# Blue Tulips & Sunflowers — 3D ASCII Bouquet

Buket bunga 3D animasi berbasis ASCII di web (**13 tulip biru dominan — perpaduan biru tua & biru muda — ditambah 3 bunga matahari kuning keemasan**) lengkap dengan kertas pembungkus buket berlipit, pita biru, daun tulip, *baby's breath*, langit berbintang, dan kelopak yang berguguran.

Dibuat **100% static HTML/CSS/JS** tanpa proses *build* atau *dependency* sehingga ringan di HP maupun laptop dan siap langsung dideploy.

## Kontrol Interaktif

- **Putar 3D:** Klik & geser (laptop) atau sentuh & geser 1 jari (HP)
- **Zoom:** Scroll mouse (laptop) atau cubit 2 jari / *pinch* (HP)
- **Tombol layar:**
  - `replay` (`R`) — mengulang animasi mekarnya bunga dari `0/16`
  - `pause` / `spin` (`Space`) — menjeda atau melanjutkan rotasi otomatis
  - `hide ui` / `ui` (`H`) — menyembunyikan HUD untuk tampilan bersih

## Preview Lokal

Buka langsung `index.html` di browser, atau jalankan server statis lokal:

```bash
python -m http.server 8080
```

Lalu buka `http://localhost:8080`.

## Cara Deploy Gratis (Tanpa Build)

1. **Vercel:** Hubungkan repo ini atau jalankan `npx vercel` di folder proyek (Framework Preset: *Other*).
2. **Netlify Drop:** Drag & drop folder proyek ini langsung ke [app.netlify.com/drop](https://app.netlify.com/drop).
3. **GitHub Pages:** Push ke repository GitHub, lalu aktifkan **Settings → Pages → Deploy from branch (`main` / root)**.
