// Service Worker — permite aplicației să funcționeze offline, odată ce a
// fost deschisă cel puțin o dată cu internet activ.
//
// La orice actualizare viitoare a fișierelor aplicației (app.js, index.html
// etc.), mărește CACHE_VERSION cu 1 mai jos, ca dispozitivele să preia
// automat versiunea nouă la următoarea vizită online (altfel ar rămâne
// blocate pe versiunea veche din cache).
const CACHE_VERSION = 'v5';
const CACHE_NAME = `tabla-cache-${CACHE_VERSION}`;

// Fișierele esențiale, precache-uite la instalare — aplicația poate porni
// offline chiar dacă utilizatorul nu a mai vizitat-o de mult.
const CORE_ASSETS = [
  './',
  './index.html',
  './app.js',
  './manifest.json',
  './icon.svg',
  './lib/tabler-icons.css',
  './lib/jspdf.min.js',
  './lib/pdf-worker.js',
  './lib/pdf.min.js',
  './lib/three.min.js',
  './lib/OrbitControls.js'
];

self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME)
      .then((cache) => Promise.all(
        CORE_ASSETS.map((url) => cache.add(url).catch(() => {
          // Dacă un fișier lipsește (ex: un font referit din CSS, cu alt nume
          // decât ne așteptăm), nu blocăm instalarea întregului cache pentru atât.
        }))
      ))
  );
  self.skipWaiting();
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((keys) => Promise.all(
      keys.filter((key) => key !== CACHE_NAME).map((key) => caches.delete(key))
    ))
  );
  self.clients.claim();
});

// Strategie: "stale-while-revalidate" — răspunde instant din cache dacă există
// (rapid + funcționează offline), și în fundal aduce versiunea de pe rețea
// (dacă e disponibilă) ca s-o pună în cache pentru vizita următoare.
self.addEventListener('fetch', (event) => {
  const req = event.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (url.origin !== self.location.origin) return; // nu interceptăm resurse externe

  event.respondWith(
    caches.match(req).then((cached) => {
      const networkFetch = fetch(req).then((networkResponse) => {
        if (networkResponse && networkResponse.status === 200) {
          const clone = networkResponse.clone();
          caches.open(CACHE_NAME).then((cache) => cache.put(req, clone));
        }
        return networkResponse;
      }).catch(() => cached);
      return cached || networkFetch;
    })
  );
});
