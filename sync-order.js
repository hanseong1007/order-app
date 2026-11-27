/* 경덕농수산 발주서 — 기기 간 작업 동기화 (sync-order.js)
   ─────────────────────────────────────────────────────────────
   · 발주 작업 자료(거래처 · 품목 · 지난 발주 · 장바구니 · 발주일)를 이 기기에서 바뀐 부분만
     AES-256-GCM 으로 잠가 구글 시트(Apps Script 웹앱)에 올리고, 다른 기기에서는 열 때 최신 것을
     받아 기록 단위로 합칩니다. 시트에는 암호문만 갑니다.
   · 자료는 두 칸으로 나눠 올립니다.
       <id>:w  거래처 · 지난 발주 · 장바구니 · 발주일   (자주 바뀜 · 작음)
       <id>:c  거래처별 품목 목록                       (가끔 바뀜 · 큼)
   · 열쇠: 계정마다 한 번 만든 32바이트 짜리 ‘자료 열쇠’를, 그 계정 비밀번호에서 뽑은 열쇠(PBKDF2)로
     감싸 시트(‘열쇠 감싸개’)와 이 기기에 둡니다. 통합포털에서 로그인하면 같은 출처의 포털 열쇠
     (IndexedDB)로 감싸개를 풀어 비밀번호를 다시 묻지 않습니다.
   · 합치기: 기록마다 ‘마지막으로 바꾼 시각’을 두고 더 최근 것을 남깁니다. 지운 것은 지운 시각을
     남겨 다른 기기에서 되살아나지 않게 합니다.
*/
(function (global) {
  'use strict';

  var KEK_DB = 'kdw-portal-kek', KEK_STORE = 'kek';
  var K_TAG = 'kd.odsync.tag';           // 시험용 칸 이름 꼬리표 (없으면 '')
  var PUSH_DELAY = 1800, POLL_MS = 45000, CHECK_MS = 4000;

  var ST = {
    url: '', uid: '', tag: '', ready: false,
    keyHex: '', keyRef: null, state: 'off', err: '', last: 0,
    rev: { w: 0, c: 0 }, pushing: false, pending: false, dirty: { w: false, c: false },
    pushT: null, pollT: null, chkT: null, suspend: false, firstRun: false, visBound: false
  };
  var AD = null, HOOK = {}, META = null;

  /* ───────── 저장 도우미 ───────── */
  function lsGet(k, fb) { try { var v = localStorage.getItem(k); return v == null ? fb : JSON.parse(v); } catch (e) { return fb; } }
  function lsText(k, fb) {
    try {
      var v = localStorage.getItem(k);
      if (v == null) return fb;
      if (v.charAt(0) === '"') { try { return JSON.parse(v); } catch (e2) { return v; } }
      return v;
    } catch (e) { return fb; }
  }
  function lsSet(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); return true; } catch (e) { return false; } }
  function metaKey() { return 'kd.u.' + ST.uid + '.odsync.v1'; }
  function cartsKey() { return 'kd.u.' + ST.uid + '.carts.v1'; }
  function wrapLocalKey(id) { return 'kd.odsync.wrap.' + id; }
  function dataKeyKey(id) { return 'kd.odsync.key.' + id; }

  function blankMeta() {
    return { v: 1, revW: 0, revC: 0,
      st: { stores: {}, hist: {}, cart: {}, items: {}, date: 0 },
      del: { stores: {}, hist: {}, cart: {}, items: {} },
      base: { stores: {}, hist: {}, cart: {}, items: {}, date: '' },
      alias: {} };
  }
  function loadMeta() {
    var m = lsGet(metaKey(), null);
    if (!m || typeof m !== 'object' || !m.st) m = blankMeta();
    ['st', 'del', 'base'].forEach(function (sec) {
      if (!m[sec] || typeof m[sec] !== 'object') m[sec] = {};
      ['stores', 'hist', 'cart', 'items'].forEach(function (k) { if (!m[sec][k] || typeof m[sec][k] !== 'object') m[sec][k] = {}; });
      if (sec !== 'base' && typeof m[sec].date !== 'number') m[sec].date = 0;
      if (sec === 'base' && typeof m[sec].date !== 'string') m[sec].date = '';
    });
    if (typeof m.revW !== 'number') m.revW = 0;
    if (typeof m.revC !== 'number') m.revC = 0;
    if (!m.alias || typeof m.alias !== 'object') m.alias = {};
    return m;
  }
  function saveMeta() { lsSet(metaKey(), META); }

  /* ───────── 암호 ───────── */
  function b64(buf) {
    var u = buf instanceof Uint8Array ? buf : new Uint8Array(buf), s = '', i;
    for (i = 0; i < u.length; i += 4096) { s += String.fromCharCode.apply(null, u.subarray(i, i + 4096)); }
    return btoa(s);
  }
  function ub64(str) {
    var bin = atob(str), u = new Uint8Array(bin.length), i;
    for (i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i);
    return u;
  }
  function hexBytes(hex) {
    var u = new Uint8Array(hex.length / 2), i;
    for (i = 0; i < u.length; i++) u[i] = parseInt(hex.substr(i * 2, 2), 16);
    return u;
  }
  function randHex(n) {
    var u = crypto.getRandomValues(new Uint8Array(n)), s = '', i;
    for (i = 0; i < u.length; i++) s += ('0' + u[i].toString(16)).slice(-2);
    return s;
  }
  function hasSubtle() { return !!(global.crypto && crypto.subtle && global.TextEncoder && global.TextDecoder); }
  function hasZip() { return typeof global.CompressionStream !== 'undefined' && typeof global.DecompressionStream !== 'undefined'; }

  function zip(u8) {
    if (!hasZip()) return Promise.resolve(u8);
    try {
      return new Response(new Blob([u8]).stream().pipeThrough(new CompressionStream('gzip')))
        .arrayBuffer().then(function (b) { return new Uint8Array(b); })
        .catch(function () { return u8; });
    } catch (e) { return Promise.resolve(u8); }
  }
  function unzip(u8) {
    return new Response(new Blob([u8]).stream().pipeThrough(new DecompressionStream('gzip')))
      .arrayBuffer().then(function (b) { return new Uint8Array(b); });
  }

  function importKey(hex) {
    return crypto.subtle.importKey('raw', hexBytes(hex), { name: 'AES-GCM' }, false, ['encrypt', 'decrypt']);
  }

  /* {…} → { iv, ct } — 첫 바이트에 gzip 표시를 넣는다 */
  function seal(key, obj) {
    var raw = new TextEncoder().encode(JSON.stringify(obj));
    return zip(raw).then(function (packed) {
      var useZip = hasZip() && packed.length && packed.length < raw.length;
      var body = new Uint8Array((useZip ? packed.length : raw.length) + 1);
      body[0] = useZip ? 1 : 0;
      body.set(useZip ? packed : raw, 1);
      var iv = crypto.getRandomValues(new Uint8Array(12));
      return crypto.subtle.encrypt({ name: 'AES-GCM', iv: iv }, key, body).then(function (ct) {
        return { iv: b64(iv), ct: b64(ct) };
      });
    });
  }

  function unseal(key, box) {
    return crypto.subtle.decrypt({ name: 'AES-GCM', iv: ub64(box.iv) }, key, ub64(box.ct)).then(function (buf) {
      var body = new Uint8Array(buf);
      var z = body[0] === 1, rest = body.subarray(1);
      return z ? unzip(rest) : Promise.resolve(rest);
    }).then(function (u8) {
      return JSON.parse(new TextDecoder().decode(u8));
    });
  }

  /* ───────── 열쇠(감싸개) ───────── */
  function kekDb() {
    return new Promise(function (res, rej) {
      var rq = indexedDB.open(KEK_DB, 1);
      rq.onupgradeneeded = function () { if (!rq.result.objectStoreNames.contains(KEK_STORE)) rq.result.createObjectStore(KEK_STORE); };
      rq.onsuccess = function () { res(rq.result); };
      rq.onerror = function () { rej(rq.error); };
    });
  }
  function kekGet(id) {
    if (!global.indexedDB) return Promise.resolve(null);
    return kekDb().then(function (db) {
      return new Promise(function (res) {
        var tx = db.transaction(KEK_STORE, 'readonly'), rq = tx.objectStore(KEK_STORE).get('u:' + id);
        rq.onsuccess = function () { res(rq.result || null); };
        rq.onerror = function () { res(null); };
      });
    }).catch(function () { return null; });
  }
  function kekPut(id, key) {
    if (!global.indexedDB) return Promise.resolve(false);
    return kekDb().then(function (db) {
      return new Promise(function (res) {
        var tx = db.transaction(KEK_STORE, 'readwrite');
        tx.objectStore(KEK_STORE).put({ key: key, salt: 'kdwpm', at: Date.now() }, 'u:' + id);
        tx.oncomplete = function () { res(true); };
        tx.onerror = function () { res(false); };
      });
    }).catch(function () { return false; });
  }
  /* 포털과 같은 방식(비밀번호 + 아이디 고정 salt, PBKDF2 310,000회) */
  function kekFromPassword(id, pw) {
    if (!hasSubtle() || !pw) return Promise.resolve(null);
    var enc = new TextEncoder();
    var salt = enc.encode('kdwpm-kek|' + String(id).trim().toLowerCase());
    return crypto.subtle.importKey('raw', enc.encode(String(pw)), 'PBKDF2', false, ['deriveKey'])
      .then(function (km) {
        return crypto.subtle.deriveKey({ name: 'PBKDF2', salt: salt, iterations: 310000, hash: 'SHA-256' },
          km, { name: 'AES-GCM', length: 256 }, false, ['encrypt', 'decrypt']);
      });
  }

  function api(payload, timeoutMs) {
    if (!ST.url) return Promise.reject(new Error('no_url'));
    var body = {}, k;
    for (k in payload) { body[k] = payload[k]; }
    try {
      if (window.KDWSEC) {
        var tk = KDWSEC.token();
        if (tk) body.token = tk;
        body.ua = (navigator.userAgent || '').slice(0, 90);
      }
    } catch (e) {}
    var ms = timeoutMs || 30000;
    var ctl = typeof AbortController !== 'undefined' ? new AbortController() : null;
    var t = setTimeout(function () { if (ctl) ctl.abort(); }, ms);
    return fetch(ST.url, {
      method: 'POST', cache: 'no-store', redirect: 'follow',
      headers: { 'Content-Type': 'text/plain;charset=utf-8' },
      body: JSON.stringify(body),
      signal: ctl ? ctl.signal : undefined
    }).then(function (r) {
      if (!r.ok) throw new Error('HTTP ' + r.status);
      return r.text();
    }).then(function (txt) {
      clearTimeout(t);
      var j = null;
      try { j = JSON.parse(txt); } catch (e) { throw new Error('sync_bad_json'); }
      if (!j || j.ok !== true) throw new Error((j && (j.error || j.message)) || 'sync_fail');
      return j;
    }).catch(function (e) { clearTimeout(t); throw e; });
  }

  function mintWrap(kek, hex, id) {
    var iv = crypto.getRandomValues(new Uint8Array(12));
    var data = new TextEncoder().encode(JSON.stringify({ v: 1, k: hex, at: Date.now() }));
    return crypto.subtle.encrypt({ name: 'AES-GCM', iv: iv }, kek, data).then(function (ct) {
      var box = { iv: b64(iv), ct: b64(ct), at: Date.now() };
      lsSet(wrapLocalKey(id), box);
      return api({ action: 'key_put', id: id, iv: box.iv, ct: box.ct }).then(function () { return true; }).catch(function () { return true; });
    });
  }
  function openWrap(kek, box) {
    if (!kek || !box || !box.iv || !box.ct) return Promise.resolve(null);
    return crypto.subtle.decrypt({ name: 'AES-GCM', iv: ub64(box.iv) }, kek, ub64(box.ct))
      .then(function (buf) {
        var o = JSON.parse(new TextDecoder().decode(new Uint8Array(buf)));
        return (o && o.k) ? String(o.k) : null;
      }).catch(function () { return null; });
  }
  function wrapFromSheet(id) {
    return api({ action: 'key_get', id: id }).then(function (j) {
      if (j && j.ok && j.found && j.iv && j.ct) {
        var box = { iv: j.iv, ct: j.ct, at: j.at || 0 };
        lsSet(wrapLocalKey(id), box);
        return box;
      }
      return null;
    }).catch(function () { return null; });
  }

  /* 이 기기에 있는 자료 열쇠 → 감싸개를 열어 → 없으면 새로 만든다 */
  function resolveKey(id, kek) {
    var local = lsGet(dataKeyKey(id), '');
    if (local && /^[0-9a-f]{64}$/.test(local)) return Promise.resolve(local);
    var box = lsGet(wrapLocalKey(id), null);
    var chain = box ? Promise.resolve(box) : wrapFromSheet(id);
    return chain.then(function (b) { return b ? openWrap(kek, b) : null; }).then(function (hex) {
      if (hex) { lsSet(dataKeyKey(id), hex); return hex; }
      if (!kek) return null;
      var fresh = randHex(32);
      return mintWrap(kek, fresh, id).then(function () { lsSet(dataKeyKey(id), fresh); return fresh; });
    });
  }

  function errText(e) {
    var s = String((e && e.message) || e || '');
    if (/abort/i.test(s)) return '응답이 없습니다';
    if (/Failed to fetch|NetworkError|Load failed|network/i.test(s)) return '인터넷 연결을 확인해 주세요';
    if (/sync_bad_json/.test(s)) return '동기화 서버 응답을 읽지 못했습니다';
    if (/conflict/.test(s)) return '동시에 저장되어 다시 맞추는 중입니다';
    if (/too_large/.test(s)) return '자료가 너무 큽니다';
    return s || '동기화 오류';
  }
  function setState(k, msg) {
    ST.state = k; ST.err = msg || '';
    if (k === 'ok') { ST.last = Date.now(); }
    if (HOOK.status) { try { HOOK.status(k, msg || ''); } catch (e) {} }
  }

  /* ───────── 지금 자료 ───────── */
  function collect() {
    var d = AD.collect() || {};
    return {
      stores: Array.isArray(d.stores) ? d.stores : [],
      items: (d.items && typeof d.items === 'object') ? d.items : {},
      history: Array.isArray(d.history) ? d.history : [],
      carts: (d.carts && typeof d.carts === 'object') ? d.carts : {},
      date: typeof d.date === 'string' ? d.date : ''
    };
  }
  function fp(o) { try { return JSON.stringify(o); } catch (e) { return ''; } }
  /* 기기마다 기본 품목 id 가 달라도 같은 품목을 하나로 보기 위한 이름표 */
  function prodKey(it) { return [it.name || '', it.spec || '', it.barcode || ''].join('|'); }

  /* 다른 기기 품목 id 로 들어온 장바구니 줄을 이 기기 id 로 잇는다 */
  function aliasCarts(carts) {
    var changed = 0, out = {};
    Object.keys(carts || {}).forEach(function (sid) {
      var c = carts[sid] || {}, n = {};
      Object.keys(c).forEach(function (iid) {
        var to = META.alias[iid];
        if (!to || to === iid) { n[iid] = c[iid]; return; }
        var t = n[to], v = c[iid];
        if (!t || (v && (v.qty || 0) > (t.qty || 0))) n[to] = v;
        changed++;
      });
      out[sid] = n;
    });
    return { carts: out, changed: changed };
  }
  function fpStores(cur) { var m = {}; cur.stores.forEach(function (s) { if (s && s.id) m[s.id] = fp(s); }); return m; }
  function fpHist(cur) { var m = {}; cur.history.forEach(function (h) { if (h && h.id) m[h.id] = fp(h); }); return m; }
  function fpItems(cur) {
    var m = {};
    Object.keys(cur.items).forEach(function (sid) {
      var sub = {};
      (cur.items[sid] || []).forEach(function (it) { if (it && it.id) sub[it.id] = fp(it); });
      m[sid] = sub;
    });
    return m;
  }
  function fpCarts(cur) {
    var m = {};
    Object.keys(cur.carts).forEach(function (sid) {
      var cart = cur.carts[sid] || {}, sub = {};
      Object.keys(cart).forEach(function (iid) {
        var c = cart[iid];
        sub[iid] = (c && c.qty > 0) ? fp([c.qty, c.unit || '', c.seq || 0]) : '';
      });
      m[sid] = sub;
    });
    return m;
  }
  function fpAll() {
    var cur = collect();
    return { stores: fpStores(cur), hist: fpHist(cur), items: fpItems(cur), cart: fpCarts(cur), date: cur.date };
  }
  function resetBase(f) {
    f = f || fpAll();
    META.base.stores = f.stores; META.base.hist = f.hist; META.base.items = f.items;
    META.base.cart = f.cart; META.base.date = f.date;
  }

  /* 이 기기에서 바뀐 기록에 시각을 찍는다 */
  function stampFlat(kind, curMap, stMap, delMap, t) {
    var n = 0, base = META.base[kind] || {};
    Object.keys(curMap).forEach(function (id) {
      if (base[id] !== curMap[id]) { stMap[id] = t; n++; delete delMap[id]; }
    });
    Object.keys(base).forEach(function (id) {
      if (!(id in curMap)) { stMap[id] = t; delMap[id] = t; n++; }
    });
    return n;
  }
  function stampDeep(kind, curMap, stMap, delMap, t) {
    var n = 0, base = META.base[kind] || {};
    Object.keys(curMap).forEach(function (sid) {
      var cur = curMap[sid] || {}, bs = base[sid] || {};
      if (!stMap[sid]) stMap[sid] = {};
      if (!delMap[sid]) delMap[sid] = {};
      Object.keys(cur).forEach(function (iid) {
        if (bs[iid] !== cur[iid]) { stMap[sid][iid] = t; n++; delete delMap[sid][iid]; }
      });
      Object.keys(bs).forEach(function (iid) {
        if (!(iid in cur)) { stMap[sid][iid] = t; delMap[sid][iid] = t; n++; }
      });
    });
    Object.keys(base).forEach(function (sid) {
      if (curMap[sid]) return;
      var bs = base[sid] || {};
      if (!stMap[sid]) stMap[sid] = {};
      if (!delMap[sid]) delMap[sid] = {};
      Object.keys(bs).forEach(function (iid) { stMap[sid][iid] = t; delMap[sid][iid] = t; n++; });
    });
    return n;
  }

  function hasAnyStamp() {
    var s = META.st, d = META.del;
    return !!(Object.keys(s.stores).length || Object.keys(s.hist).length || Object.keys(s.items).length ||
      Object.keys(s.cart).length || Object.keys(d.stores).length || Object.keys(d.hist).length ||
      Object.keys(d.items).length || Object.keys(d.cart).length || s.date > 0);
  }

  function touch() {
    if (!ST.ready || !AD || ST.suspend) return false;
    var cur = collect();
    var t = ST.firstRun ? 1 : Date.now();
    var nw = 0, nc = 0;
    nw += stampFlat('stores', fpStores(cur), META.st.stores, META.del.stores, t);
    META.base.stores = fpStores(cur);
    nw += stampFlat('hist', fpHist(cur), META.st.hist, META.del.hist, t);
    META.base.hist = fpHist(cur);
    nc += stampDeep('items', fpItems(cur), META.st.items, META.del.items, t);
    META.base.items = fpItems(cur);
    nw += stampDeep('cart', fpCarts(cur), META.st.cart, META.del.cart, t);
    META.base.cart = fpCarts(cur);
    if (META.base.date !== cur.date) { META.st.date = t; META.base.date = cur.date; nw++; }
    ST.firstRun = false;
    if (nw || nc) {
      if (nw) ST.dirty.w = true;
      if (nc) ST.dirty.c = true;
      saveMeta();
      queuePush();
      return true;
    }
    return false;
  }

  /* ───────── 올리기 ───────── */
  function buildDocW() {
    var cur = collect();
    return {
      v: 1, at: Date.now(), dev: ST.uid, n: cur.stores.length + cur.history.length,
      stores: cur.stores, history: cur.history.slice(0, 120), carts: cur.carts, date: cur.date,
      st: { stores: META.st.stores, hist: META.st.hist, cart: META.st.cart, date: META.st.date },
      del: { stores: META.del.stores, hist: META.del.hist, cart: META.del.cart }
    };
  }
  function buildDocC() {
    var cur = collect(), n = 0;
    Object.keys(cur.items).forEach(function (sid) { n += (cur.items[sid] || []).length; });
    return { v: 1, at: Date.now(), dev: ST.uid, n: n, items: cur.items, st: { items: META.st.items }, del: { items: META.del.items } };
  }
  function odSlot(kind) { return ST.uid + (ST.tag ? ':' + ST.tag : '') + ':' + kind; }

  function pushKind(kind, attempt) {
    var doc = kind === 'w' ? buildDocW() : buildDocC();
    var rev = kind === 'w' ? META.revW : META.revC;
    return seal(ST.keyRef, doc).then(function (box) {
      return api({ action: 'put', slot: odSlot(kind), baseRev: rev, by: ST.uid, n: doc.n || 0, iv: box.iv, ct: box.ct });
    }).then(function (j) {
      if (kind === 'w') META.revW = Number(j.rev) || (rev + 1); else META.revC = Number(j.rev) || (rev + 1);
      ST.dirty[kind] = false;
      saveMeta();
      return true;
    }).catch(function (e) {
      if (String(e && e.message) === 'conflict' && (attempt || 0) < 3) {
        return pull(kind, true).then(function () { return pushKind(kind, (attempt || 0) + 1); });
      }
      throw e;
    });
  }

  function pushAll() {
    if (!ST.ready) return Promise.resolve(false);
    if (ST.pushing) { ST.pending = true; return Promise.resolve(false); }
    if (!ST.dirty.w && !ST.dirty.c) { ST.pending = false; setState('ok'); return Promise.resolve(true); }
    ST.pushing = true;
    setState('saving');
    var chain = Promise.resolve(true);
    if (ST.dirty.w) chain = chain.then(function () { return pushKind('w', 0); });
    if (ST.dirty.c) chain = chain.then(function () { return pushKind('c', 0); });
    return chain.then(function () {
      ST.pending = false;
      setState('ok');
      return true;
    }).catch(function (e) {
      ST.pending = true;
      setState('error', errText(e));
      return false;
    }).then(function (r) { ST.pushing = false; return r; });
  }

  function queuePush() {
    if (!ST.ready) return;
    ST.pending = true;
    if (ST.pushT) clearTimeout(ST.pushT);
    ST.pushT = setTimeout(function () { ST.pushT = null; pushAll(); }, PUSH_DELAY);
    setState('saving');
  }

  /* ───────── 받아 합치기 ───────── */
  function num(v) { return Number(v) || 0; }

  /* 기록 하나 단위로 더 최근 것을 남긴다 */
  function mergeFlat(kind, localMap, remoteMap, rSt, rDel, outMap, deepKey) {
    var changed = 0;
    var lst = deepKey ? (META.st[kind][deepKey] || (META.st[kind][deepKey] = {})) : META.st[kind];
    var ldel = deepKey ? (META.del[kind][deepKey] || (META.del[kind][deepKey] = {})) : META.del[kind];
    var ids = {}, id;
    Object.keys(localMap).forEach(function (k) { ids[k] = 1; });
    Object.keys(remoteMap || {}).forEach(function (k) { ids[k] = 1; });
    for (id in ids) {
      if (!Object.prototype.hasOwnProperty.call(ids, id)) continue;
      var rt = num((rSt || {})[id]), rd = num((rDel || {})[id]);
      var lt = Math.max(num(lst[id]), num(ldel[id]));
      var rs = Math.max(rt, rd);
      var inRemote = !!(remoteMap && Object.prototype.hasOwnProperty.call(remoteMap, id));
      var inLocal = Object.prototype.hasOwnProperty.call(localMap, id);
      var take = false;
      if (rs > lt) take = true;
      else if (rs > 0 && rs === lt && inRemote && inLocal && fp(remoteMap[id]) !== fp(localMap[id]) && fp(remoteMap[id]) > fp(localMap[id])) take = true;
      if (!take) continue;
      if (rd > 0) { delete localMap[id]; delete lst[id]; ldel[id] = rd; changed++; }
      else if (inRemote) {
        if (fp(remoteMap[id]) !== fp(localMap[id])) changed++;
        localMap[id] = remoteMap[id]; lst[id] = rt; delete ldel[id];
      }
    }
    Object.keys(rDel || {}).forEach(function (k) { if (num(rDel[k]) > num(ldel[k])) ldel[k] = num(rDel[k]); });
    Object.keys(rSt || {}).forEach(function (k) { if (num(rSt[k]) > num(lst[k])) lst[k] = num(rSt[k]); });
    Object.keys(localMap).forEach(function (k) { outMap[k] = localMap[k]; });
    return changed;
  }

  function applyDocW(doc) {
    if (!doc || !doc.st) return 0;
    var changed = 0;
    var cur = collect();
    var lStores = {}, lHist = {}, lCarts = {};
    cur.stores.forEach(function (s) { if (s && s.id) lStores[s.id] = s; });
    cur.history.forEach(function (h) { if (h && h.id) lHist[h.id] = h; });
    Object.keys(cur.carts).forEach(function (sid) { lCarts[sid] = cur.carts[sid]; });

    var rStores = {}, rHist = {}, rCarts = {};
    (doc.stores || []).forEach(function (s) { if (s && s.id) rStores[s.id] = s; });
    (doc.history || []).forEach(function (h) { if (h && h.id) rHist[h.id] = h; });
    Object.keys(doc.carts || {}).forEach(function (sid) { rCarts[sid] = doc.carts[sid]; });

    var oStores = {}, oHist = {};
    changed += mergeFlat('stores', lStores, rStores, doc.st.stores, doc.del.stores, oStores);
    changed += mergeFlat('hist', lHist, rHist, doc.st.hist, doc.del.hist, oHist);

    var sids = {};
    Object.keys(lCarts).forEach(function (s) { sids[s] = 1; });
    Object.keys(rCarts).forEach(function (s) { sids[s] = 1; });
    var oCarts = {};
    Object.keys(sids).forEach(function (sid) {
      var loc = {}, rem = {};
      Object.keys(lCarts[sid] || {}).forEach(function (iid) { loc[iid] = lCarts[sid][iid]; });
      Object.keys(rCarts[sid] || {}).forEach(function (iid) { rem[iid] = rCarts[sid][iid]; });
      var o = {};
      changed += mergeFlat('cart', loc, rem, (doc.st.cart || {})[sid] || {}, (doc.del.cart || {})[sid] || {}, o, sid);
      oCarts[sid] = o;
    });

    var aliased = aliasCarts(oCarts);
    if (aliased.changed) { oCarts = aliased.carts; changed += aliased.changed; }

    var dateOut = cur.date;
    var rdt = num(doc.st.date), ldt = num(META.st.date);
    if (rdt > ldt) { dateOut = String(doc.date || ''); META.st.date = rdt; changed++; }

    if (changed) {
      ST.suspend = true;
      try {
        AD.apply('stores', Object.keys(oStores).map(function (id) { return oStores[id]; }));
        AD.apply('history', Object.keys(oHist).map(function (id) { return oHist[id]; })
          .sort(function (a, b) { return num(b.createdAt) - num(a.createdAt); }));
        AD.apply('carts', oCarts);
        if (dateOut) AD.apply('date', dateOut);
      } catch (e) {}
      ST.suspend = false;
      resetBase();
      saveMeta();
    }
    return changed;
  }

  function applyDocC(doc) {
    if (!doc || !doc.st) return 0;
    var cur = collect();
    var changed = 0, out = {}, sids = {};

    /* 같은 품목(이름·규격·바코드)인데 기기마다 id 가 다르면: 이 기기 id 를 남기고 저쪽 id 를 별칭으로 기억한다 */
    var localByKey = {}, localIds = {}, sid, arr, it, k;
    for (sid in cur.items) {
      localByKey[sid] = {}; localIds[sid] = {};
      arr = cur.items[sid] || [];
      for (var q = 0; q < arr.length; q++) {
        it = arr[q];
        if (!it || !it.id) continue;
        localIds[sid][it.id] = 1;
        localByKey[sid][prodKey(it)] = it.id;
      }
    }
    var pruned = {}, newAlias = 0;
    for (sid in (doc.items || {})) {
      arr = doc.items[sid] || [];
      var keep = [];
      for (var r = 0; r < arr.length; r++) {
        it = arr[r];
        if (!it || !it.id) continue;
        k = prodKey(it);
        var lid = localByKey[sid] ? localByKey[sid][k] : null;
        if (lid && lid !== it.id && !(localIds[sid] && localIds[sid][it.id])) {
          if (!META.alias[it.id]) { META.alias[it.id] = lid; newAlias = (newAlias || 0) + 1; }
          continue;                        /* 이미 이 기기에 같은 품목이 있다 */
        }
        keep.push(it);
      }
      pruned[sid] = keep;
    }
    doc = { v: doc.v, at: doc.at, dev: doc.dev, n: doc.n, items: pruned, st: doc.st, del: doc.del };

    Object.keys(cur.items).forEach(function (s) { sids[s] = 1; });
    Object.keys(doc.items || {}).forEach(function (s) { sids[s] = 1; });
    Object.keys(sids).forEach(function (sid) {
      var loc = {}, rem = {};
      (cur.items[sid] || []).forEach(function (it) { if (it && it.id) loc[it.id] = it; });
      (doc.items[sid] || []).forEach(function (it) { if (it && it.id) rem[it.id] = it; });
      var o = {};
      changed += mergeFlat('items', loc, rem, (doc.st.items || {})[sid] || {}, (doc.del.items || {})[sid] || {}, o, sid);
      out[sid] = Object.keys(o).map(function (id) { return o[id]; });
    });
    if (changed) {
      ST.suspend = true;
      try { AD.apply('items', out); } catch (e) {}
      ST.suspend = false;
    }
    /* 새로 알게 된 별칭으로 장바구니 줄을 다시 잇는다 */
    var c2 = collect(), al = aliasCarts(c2.carts);
    if (al.changed) {
      ST.suspend = true;
      try { AD.apply('carts', al.carts); } catch (e) {}
      ST.suspend = false;
      changed += al.changed;
    }
    resetBase();
    saveMeta();
    /* 이 기기 품목 id 를 저쪽도 알도록 목록을 한 번 올린다 (그래야 저쪽이 이 기기 장바구니 줄을 찾는다) */
    if (newAlias > 0) { ST.dirty.c = true; queuePush(); }
    return changed;
  }

  function pull(kind, force) {
    if (!ST.ready) return Promise.resolve(0);
    var rev = kind === 'w' ? META.revW : META.revC;
    return api({ action: 'get', slot: odSlot(kind) }).then(function (j) {
      var srev = num(j.rev);
      if (!j.iv) { if (kind === 'w') META.revW = srev; else META.revC = srev; saveMeta(); return 0; }
      if (!force && srev === rev) return 0;
      return unseal(ST.keyRef, { iv: j.iv, ct: j.ct }).then(function (doc) {
        var n = kind === 'w' ? applyDocW(doc) : applyDocC(doc);
        if (kind === 'w') META.revW = srev; else META.revC = srev;
        saveMeta();
        if (n > 0 && HOOK.changed) { try { HOOK.changed(n); } catch (e) {} }
        return n;
      });
    }).catch(function (e) {
      setState('error', errText(e));
      return 0;
    });
  }

  function pullBoth(force) {
    return pull('w', force).then(function () { return pull('c', force); });
  }

  /* ───────── 시작 / 멈춤 ───────── */
  function start() {
    if (!ST.url || !ST.uid || !hasSubtle() || !ST.keyRef) {
      setState(ST.keyRef ? 'off' : 'locked');
      return Promise.resolve(false);
    }
    ST.ready = true;
    ST.firstRun = !META.revW && !META.revC && !hasAnyStamp();
    setState('sync');
    return pullBoth(true).then(function () {
      var dirty = touch();
      return dirty ? pushAll() : null;
    }).then(function () {
      if (ST.state !== 'saving' && ST.state !== 'error') setState('ok');
      if (ST.pollT) clearInterval(ST.pollT);
      ST.pollT = setInterval(function () {
        if (document.visibilityState !== 'visible' || ST.pushing) return;
        pullBoth(false).then(function () { if (ST.pending && !ST.pushing) pushAll(); });
      }, POLL_MS);
      if (ST.chkT) clearInterval(ST.chkT);
      ST.chkT = setInterval(function () {
        if (document.visibilityState !== 'visible') return;
        if (touch()) return;
      }, CHECK_MS);
      if (!ST.visBound) {
        ST.visBound = true;
        document.addEventListener('visibilitychange', function () {
          if (document.visibilityState !== 'visible' || !ST.ready) return;
          if (ST.pending) pushAll(); else pullBoth(false);
        });
      }
      return true;
    });
  }

  function stop() {
    ST.ready = false;
    if (ST.pollT) { clearInterval(ST.pollT); ST.pollT = null; }
    if (ST.chkT) { clearInterval(ST.chkT); ST.chkT = null; }
    if (ST.pushT) { clearTimeout(ST.pushT); ST.pushT = null; }
    setState('off');
  }

  function unlock(pw) {
    if (!ST.uid || !hasSubtle()) return Promise.resolve(false);
    var local = lsGet(dataKeyKey(ST.uid), '');
    if (local && /^[0-9a-f]{64}$/.test(local)) { ST.keyHex = local; return setKey(local); }
    return kekFromPassword(ST.uid, pw).then(function (kek) {
      if (!kek) return { kek: null };
      return kekPut(ST.uid, kek).then(function () { return { kek: kek }; });
    }).then(function (r) {
      var kek = (r && r.kek) || null;
      if (!kek) return kekGet(ST.uid).then(function (k2) { return { kek: k2 }; });
      return { kek: kek };
    }).then(function (r) {
      var kek = r.kek;
      if (!kek) { setState('locked'); return false; }
      return resolveKey(ST.uid, kek).then(function (hex) {
        if (!hex) { setState('locked'); return false; }
        ST.keyHex = hex;
        return setKey(hex);
      });
    }).catch(function (e) { setState('error', errText(e)); return false; });
  }

  function unlockPortal() {
    if (!ST.uid || !hasSubtle()) return Promise.resolve(false);
    var local = lsGet(dataKeyKey(ST.uid), '');
    if (local && /^[0-9a-f]{64}$/.test(local)) { ST.keyHex = local; return setKey(local); }
    return kekGet(ST.uid).then(function (kek) {
      if (!kek) { setState('locked'); return false; }
      return resolveKey(ST.uid, kek).then(function (hex) {
        if (!hex) { setState('locked'); return false; }
        ST.keyHex = hex;
        return setKey(hex);
      });
    }).catch(function () { setState('locked'); return false; });
  }

  function rewrap(oldPw, newPw) {
    if (!ST.uid || !hasSubtle()) return Promise.resolve(false);
    var hex = ST.keyHex || lsGet(dataKeyKey(ST.uid), '');
    if (!hex || !/^[0-9a-f]{64}$/.test(hex)) return Promise.resolve(false);
    if (ST.keyRef) return kekFromPassword(ST.uid, newPw).then(function (kek) {
      if (!kek) return false;
      return mintWrap(kek, hex, ST.uid).then(function () { return kekPut(ST.uid, kek); }).then(function () { return true; });
    }).catch(function () { return false; });
    return kekFromPassword(ST.uid, newPw).then(function (kek) {
      if (!kek) return false;
      return mintWrap(kek, hex, ST.uid).then(function () { return kekPut(ST.uid, kek); }).then(function () { return true; });
    }).catch(function () { return false; });
  }

  function setKey(hex) {
    return importKey(hex).then(function (k) { ST.keyRef = k; return true; }).catch(function () { return false; });
  }

  global.ODSync = {
    init: function (opts) {
      AD = opts.adapter;
      HOOK = { status: opts.onStatus, changed: opts.onChange };
      ST.url = opts.url || '';
      ST.uid = String(opts.uid || '').trim().toLowerCase();
      ST.tag = String(opts.tag == null ? (lsText(K_TAG, '') || '') : opts.tag).trim().toLowerCase();
      ST.ready = false; ST.keyRef = null; ST.keyHex = '';
      ST.dirty = { w: false, c: false }; ST.pending = false;
      META = loadMeta();
      return global.ODSync;
    },
    unlock: unlock, unlockPortal: unlockPortal, rewrap: rewrap,
    start: start, stop: stop, touch: touch,
    push: pushAll, pull: function () { return pullBoth(true); },
    state: function () {
      return { state: ST.state, err: ST.err, last: ST.last, ready: ST.ready,
        revW: META && META.revW, revC: META && META.revC, dirty: ST.dirty, tag: ST.tag, uid: ST.uid };
    },
    cartsKey: cartsKey,
    text: function () {
      var t = ST.state;
      if (t === 'off') return '동기화 꺼짐';
      if (t === 'locked') return '동기화 열쇠 없음';
      if (t === 'sync') return '동기화 확인 중';
      if (t === 'saving') return '저장 중';
      if (t === 'error') return '동기화 오류';
      return '동기화됨';
    }
  };
})(window);
