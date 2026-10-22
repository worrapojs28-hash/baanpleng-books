// Keeps the app itself on the phone so it opens without internet.
// Shop data is kept offline separately by Firestore.
const VERSION = 'bp-2026-10-22-5';
const FB = 'https://www.gstatic.com/firebasejs/12.19.0/';
const SHELL = ['./', './index.html', './styles.css', './app.js', './firebase-config.js', './manifest.webmanifest',
  './icons/icon-192.png', './icons/icon-512.png', './icons/apple-touch-icon.png', './vendor/zxing-0.21.3.min.js'];
const LIBS = ['firebase-app.js', 'firebase-auth.js', 'firebase-firestore.js'].map(f => FB + f);

self.addEventListener('install', e => {
  e.waitUntil((async () => {
    const c = await caches.open(VERSION);
    await c.addAll(SHELL);
    await Promise.all(LIBS.map(u => c.add(new Request(u, { mode: 'cors' })).catch(() => {})));
    await self.skipWaiting();
  })());
});

self.addEventListener('activate', e => {
  e.waitUntil((async () => {
    for (const k of await caches.keys()) if (k !== VERSION) await caches.delete(k);
    await self.clients.claim();
  })());
});

const cacheable = url =>
  url.origin === self.location.origin || url.href.startsWith(FB) ||
  url.hostname === 'fonts.googleapis.com' || url.hostname === 'fonts.gstatic.com';

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (!cacheable(url)) return;
  if (url.origin === self.location.origin) {
    // the app's own files: newest copy when online, saved copy when offline
    e.respondWith((async () => {
      const c = await caches.open(VERSION);
      const key = req.mode === 'navigate' ? './index.html' : req;
      try {
        const res = await fetch(req, { cache: 'no-cache' });
        if (res && res.ok) c.put(key, res.clone());
        return res;
      } catch (err) {
        return (await c.match(key)) || (req.mode === 'navigate' ? await c.match('./') : null) || Response.error();
      }
    })());
    return;
  }
  // saved copy first, refresh in the background
  e.respondWith((async () => {
    const c = await caches.open(VERSION);
    const hit = await c.match(req);
    const net = fetch(req).then(res => { if (res && (res.ok || res.type === 'opaque')) c.put(req, res.clone()); return res; }).catch(() => null);
    if (hit) { e.waitUntil(net); return hit; }
    return (await net) || Response.error();
  })());
});
