/* Kyoungdeok order-app - cross-device work sync API (Google Apps Script web app)
   ---------------------------------------------------------------------------
   Deploy: script.google.com -> New project -> paste this file ->
           Deploy -> New deployment -> type "Web app", execute as "Me",
           access "Anyone" -> copy the /exec URL into OD_SYNC_URL in
           documents/order-app/index.html

   The server stores ciphertext only.
   - Work data (stores, items, past orders, carts) is encrypted in the browser
     with AES-256-GCM; only { iv, ct } (base64) is uploaded. No plaintext item
     names, barcodes, store names or quantities exist in the sheet.
   - A Google Sheets cell holds at most 50,000 characters, so one ciphertext is
     split into 45,000-character pieces. The header row keeps the piece count.
   - Per-account "key wrap" rows are AES-256-GCM ciphertext as well (opened only
     with a key derived from that account password).
   - The sheet is created by this script on first call (id kept in script props).

   actions
     info / ping                            connection check
     get    {slot}                          ciphertext + rev for that slot
     put    {slot, baseRev, by, n, iv, ct}  store new ciphertext (conflict if baseRev != rev)
     key_get {id}                           key wrap for that account
     key_put {id, iv, ct}                   store key wrap
     drop   {slot}                          delete a slot (test cleanup)
     log                                    recent activity (no ciphertext)
*/

var PROP_SHEET = 'OD_SYNC_SHEET_ID';
var SS_NAME = 'kd-order-sync (encrypted)';
var T_DATA = 'data';
var T_LOG = 'log';
var LOCK_MS = 25000;
var CHUNK = 45000;
var MAX_TOTAL = 2000000;
var MAX_LOG = 300;

function doGet(e) {
  var p = (e && e.parameter) || {};
  return handle_(p, p);
}

function doPost(e) {
  var body = {};
  try { body = JSON.parse((e && e.postData && e.postData.contents) || '{}') || {}; } catch (err) { body = {}; }
  return handle_(body, (e && e.parameter) || {});
}

function handle_(body, p) {
  body = body || {}; p = p || {};
  var action = String(body.action || p.action || 'get').trim();
  var out = { ok: false, error: 'unknown_action', action: action };
  var lock = LockService.getScriptLock();
  try {
    lock.waitLock(LOCK_MS);
    var ss = ss_();
    if (action === 'info' || action === 'ping') {
      out = { ok: true, app: 'kd-order-sync', v: 2, sheet: ss.getUrl(), time: Date.now() };
    } else if (action === 'get') {
      out = get_(ss, slotOf_(body, p));
    } else if (action === 'put') {
      out = put_(ss, slotOf_(body, p), body);
    } else if (action === 'key_get') {
      out = keyGet_(ss, body, p);
    } else if (action === 'key_put') {
      out = keyPut_(ss, body);
    } else if (action === 'drop') {
      out = drop_(ss, slotOf_(body, p));
    } else if (action === 'log') {
      out = readLog_(ss);
    }
  } catch (err) {
    out = { ok: false, error: String((err && err.message) || err) };
  } finally {
    try { lock.releaseLock(); } catch (e2) {}
  }
  out.action = action;
  out.serverTime = Date.now();
  return ContentService.createTextOutput(JSON.stringify(out)).setMimeType(ContentService.MimeType.JSON);
}

function ss_() {
  var active = null;
  try { active = SpreadsheetApp.getActiveSpreadsheet(); } catch (e0) { active = null; }
  if (active) { return active; }
  var props = PropertiesService.getScriptProperties();
  var id = props.getProperty(PROP_SHEET);
  if (id) {
    try { return SpreadsheetApp.openById(id); } catch (err) {}
  }
  var ss = SpreadsheetApp.create(SS_NAME);
  props.setProperty(PROP_SHEET, ss.getId());
  return ss;
}

function tab_(ss, name, head) {
  var sh = ss.getSheetByName(name);
  if (!sh) { sh = ss.insertSheet(name); }
  if (sh.getLastRow() < 1) {
    sh.getRange(1, 1, 1, head.length).setValues([head]);
    sh.setFrozenRows(1);
    sh.getRange('A:C').setNumberFormat('@');
  }
  return sh;
}

function slotOf_(body, p) {
  var s = String(body.slot || p.slot || '').trim().toLowerCase();
  if (!/^[a-z0-9._:\-]{1,90}$/.test(s)) { throw new Error('bad_slot'); }
  return s;
}

function findRow_(sh, key) {
  var lr = sh.getLastRow();
  if (lr < 2) { return 0; }
  var col = sh.getRange(2, 1, lr - 1, 1).getValues();
  for (var i = 0; i < col.length; i++) {
    if (String(col[i][0] === null || col[i][0] === undefined ? '' : col[i][0]).trim() === key) { return i + 2; }
  }
  return 0;
}

function readJson_(sh, key) {
  var row = findRow_(sh, key);
  if (!row) { return null; }
  try { return JSON.parse(String(sh.getRange(row, 2).getValue() || '{}')) || {}; } catch (err) { return null; }
}

function writeJson_(sh, key, obj) {
  var row = findRow_(sh, key);
  var val = JSON.stringify(obj);
  if (row) { sh.getRange(row, 1, 1, 3).setValues([[key, val, String(Date.now())]]); }
  else { sh.appendRow([key, val, String(Date.now())]); }
}

function removeRow_(sh, key) {
  var row = findRow_(sh, key);
  if (row) { sh.deleteRow(row); return true; }
  return false;
}

function headerOf_(sh, slot) { return readJson_(sh, 'data:' + slot); }

function get_(ss, slot) {
  var sh = tab_(ss, T_DATA, ['slot', 'value', 'updatedAt']);
  var h = headerOf_(sh, slot);
  if (!h) { return { ok: true, slot: slot, rev: 0, at: 0, by: '', n: 0, iv: '', ct: '' }; }
  var ct = '', parts = Number(h.chunks) || 0, i, part;
  if (parts <= 1) {
    ct = String(h.ct || '');          /* 한 칸에 다 들어가는 크기 */
  } else {
    for (i = 1; i <= parts; i++) {
      part = readJson_(sh, 'data:' + slot + '#' + i);
      if (!part || typeof part.d !== 'string') {
        return { ok: false, error: 'incomplete', slot: slot, rev: Number(h.rev) || 0, part: i };
      }
      ct += part.d;
    }
  }
  return {
    ok: true, slot: slot,
    rev: Number(h.rev) || 0, at: Number(h.at) || 0, by: String(h.by || ''),
    n: Number(h.n) || 0, iv: String(h.iv || ''), ct: ct
  };
}

function put_(ss, slot, body) {
  var sh = tab_(ss, T_DATA, ['slot', 'value', 'updatedAt']);
  var cur = headerOf_(sh, slot) || { rev: 0 };
  var curRev = Number(cur.rev) || 0;
  var baseRev = body.baseRev === null || body.baseRev === undefined ? null : Number(body.baseRev);
  if (baseRev !== null && baseRev !== curRev) {
    return { ok: false, error: 'conflict', slot: slot, rev: curRev, at: Number(cur.at) || 0 };
  }
  var ct = String(body.ct || '');
  var iv = String(body.iv || '');
  if (!ct || !iv) { return { ok: false, error: 'empty' }; }
  if (ct.length > MAX_TOTAL) { return { ok: false, error: 'too_large', length: ct.length, max: MAX_TOTAL }; }
  var parts = Math.ceil(ct.length / CHUNK);
  var next = {
    rev: curRev + 1, at: Date.now(), by: String(body.by || ''),
    n: Number(body.n) || 0, iv: iv, chunks: parts, len: ct.length
  };
  if (parts <= 1) {
    next.chunks = 0;
    next.ct = ct;                       /* 한 칸에 다 들어가면 헤더 행에 그대로 */
  } else {
    for (var i = 0; i < parts; i++) {
      writeJson_(sh, 'data:' + slot + '#' + (i + 1), { d: ct.substr(i * CHUNK, CHUNK) });
    }
  }
  var old = Number(cur.chunks) || 0;
  for (var j = parts + 1; j <= old; j++) { removeRow_(sh, 'data:' + slot + '#' + j); }
  writeJson_(sh, 'data:' + slot, next);
  addLog_(ss, { at: next.at, action: 'put', slot: slot, by: next.by, n: next.n, bytes: ct.length });
  return { ok: true, slot: slot, rev: next.rev, at: next.at, chunks: parts };
}

function drop_(ss, slot) {
  var sh = tab_(ss, T_DATA, ['slot', 'value', 'updatedAt']);
  var h = headerOf_(sh, slot);
  var old = h ? (Number(h.chunks) || 0) : 0;
  for (var j = 1; j <= old; j++) { removeRow_(sh, 'data:' + slot + '#' + j); }
  var row = findRow_(sh, 'data:' + slot);
  if (row) { sh.deleteRow(row); }
  addLog_(ss, { at: Date.now(), action: 'drop', slot: slot, by: '', n: '', bytes: '' });
  return { ok: true, slot: slot, dropped: !!row };
}

function normId_(v) {
  return String(v === null || v === undefined ? '' : v).trim().toLowerCase().slice(0, 64);
}

function keyGet_(ss, body, p) {
  var id = normId_(body.id || p.id);
  if (!id) { return { ok: false, error: 'no_id' }; }
  var sh = tab_(ss, T_DATA, ['slot', 'value', 'updatedAt']);
  var o = readJson_(sh, 'key:' + id);
  if (!o) { return { ok: true, found: false, id: id }; }
  return { ok: true, found: true, id: id, at: Number(o.at) || 0, iv: String(o.iv || ''), ct: String(o.ct || '') };
}

function keyPut_(ss, body) {
  var id = normId_(body.id);
  if (!id) { return { ok: false, error: 'no_id' }; }
  var ct = String(body.ct || '');
  var iv = String(body.iv || '');
  if (!ct || !iv) { return { ok: false, error: 'empty' }; }
  if (ct.length > 20000) { return { ok: false, error: 'too_large' }; }
  var sh = tab_(ss, T_DATA, ['slot', 'value', 'updatedAt']);
  var obj = { at: Date.now(), iv: iv, ct: ct };
  writeJson_(sh, 'key:' + id, obj);
  addLog_(ss, { at: obj.at, action: 'key_put', slot: 'key:' + id, by: id, n: '', bytes: ct.length });
  return { ok: true, id: id, at: obj.at };
}

function addLog_(ss, rec) {
  var sh = ss.getSheetByName(T_LOG);
  if (!sh) {
    sh = ss.insertSheet(T_LOG);
    sh.getRange(1, 1, 1, 6).setValues([['at', 'action', 'slot', 'by', 'n', 'bytes']]);
    sh.setFrozenRows(1);
  }
  sh.appendRow([new Date(rec.at || Date.now()), rec.action || '', rec.slot || '', rec.by || '', rec.n || '', rec.bytes || '']);
  var extra = sh.getLastRow() - 1 - MAX_LOG;
  if (extra > 0) { sh.deleteRows(2, extra); }
}

function readLog_(ss) {
  var sh = ss.getSheetByName(T_LOG);
  if (!sh || sh.getLastRow() < 2) { return { ok: true, rows: [] }; }
  var lr = sh.getLastRow();
  var from = Math.max(2, lr - 19);
  var vals = sh.getRange(from, 1, lr - from + 1, 6).getValues();
  var rows = vals.map(function (r) {
    return { at: r[0] ? String(r[0]) : '', action: r[1], slot: r[2], by: r[3], n: r[4], bytes: r[5] };
  }).reverse();
  return { ok: true, rows: rows };
}
