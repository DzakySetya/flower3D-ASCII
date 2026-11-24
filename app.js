(function () {
  'use strict';

  const CHAR_RAMP = ' .,:;-~=+*#%@';
  const RAMP_LEN = CHAR_RAMP.length;
  const GOLDEN_ANGLE = 2.399963229728653;

  // Directional key light and cool rim/fill light
  const L1 = normalize3(0.45, 0.72, 0.65);
  const L2 = normalize3(-0.6, 0.25, -0.55);

  // Distinct Dark Blue (Biru Tua) & Light Blue (Biru Muda) tulip palettes
  const TULIP_PALETTES = [
    // Biru Tua (Deep Midnight Cobalt)
    { name: 'biru-tua-cobalt', shadeGroup: 'dark', base: [8, 22, 108], mid: [18, 62, 208], tip: [46, 118, 252] },
    // Biru Muda (Luminous Sky Blue)
    { name: 'biru-muda-sky', shadeGroup: 'light', base: [34, 112, 205], mid: [88, 188, 255], tip: [182, 236, 255] },
    // Biru Tua (Deep Royal Sapphire)
    { name: 'biru-tua-sapphire', shadeGroup: 'dark', base: [10, 28, 122], mid: [24, 78, 226], tip: [62, 136, 255] },
    // Biru Muda (Ice Powder Blue)
    { name: 'biru-muda-ice', shadeGroup: 'light', base: [48, 132, 218], mid: [118, 206, 255], tip: [212, 246, 255] },
    // Biru Royal (Bridge Azure)
    { name: 'biru-royal', shadeGroup: 'mid', base: [16, 48, 152], mid: [42, 128, 255], tip: [118, 198, 255] }
  ];

  // Canvas & DOM elements
  const canvas = document.getElementById('ascii-canvas');
  const ctx = canvas.getContext('2d', { alpha: false });
  const hudBloomsEl = document.getElementById('hud-blooms');
  const hudPetalsEl = document.getElementById('hud-petals');
  const hudFpsEl = document.getElementById('hud-fps');
  const hintEl = document.getElementById('hint');
  const btnReplay = document.getElementById('btn-replay');
  const btnSpin = document.getElementById('btn-spin');
  const btnHud = document.getElementById('btn-hud');

  // Grid & projection state
  let dpr = 1;
  let viewW = 0;
  let viewH = 0;
  let fontSize = 11;
  let cellW = 7;
  let cellH = 13;
  let cols = 100;
  let rows = 60;
  let fovScale = 220;
  let centerYRatio = 0.5;
  const camDist = 4.3;

  // Reusable flat render buffers
  let zBuf = new Float32Array(0);
  let charBuf = new Uint8Array(0);
  let rBuf = new Uint8Array(0);
  let gBuf = new Uint8Array(0);
  let bBuf = new Uint8Array(0);
  const BUCKET_COUNT = 32768; // 5-bit RGB quantization
  const bucketHead = new Int32Array(BUCKET_COUNT);
  let bucketNext = new Int32Array(0);
  const colorStrCache = new Array(BUCKET_COUNT);

  // Camera & animation state
  let rotY = 0.22;
  let rotX = 0.38;
  let targetZoom = 1.0;
  let currentZoom = 1.0;
  let autoSpin = true;
  let bloomClock = 0;
  let animTime = 0;
  let lastTimestamp = 0;
  let isPausedHidden = false;

  // FPS & HUD tracking
  let fpsFrameCount = 0;
  let fpsAccum = 0;
  let lastBloomsText = '';
  let lastPetalsText = '';

  // Pointer / Touch interaction state
  const activePointers = new Map();
  let isDragging = false;
  let lastDragX = 0;
  let lastDragY = 0;
  let lastPinchDist = 0;
  let hintDismissed = false;

  // World data
  const flowers = [];
  const staticPoints = []; // { x, y, z, nx, ny, nz, r, g, b, kind }
  const stars = [];
  const fallingPetals = [];
  let petalSpawnTimer = 0;

  // Deterministic PRNG for consistent organic layout
  function createRng(seed) {
    let s = seed >>> 0;
    return function () {
      s = (s * 1664525 + 1013904223) >>> 0;
      return s / 4294967296;
    };
  }

  function clamp(v, lo, hi) {
    return v < lo ? lo : v > hi ? hi : v;
  }

  function lerp(a, b, t) {
    return a + (b - a) * t;
  }

  function lerpColor(c1, c2, t) {
    return [
      lerp(c1[0], c2[0], t),
      lerp(c1[1], c2[1], t),
      lerp(c1[2], c2[2], t)
    ];
  }

  function easeOutCubic(t) {
    const u = 1 - clamp(t, 0, 1);
    return 1 - u * u * u;
  }

  function normalize3(x, y, z) {
    const len = Math.hypot(x, y, z) || 1;
    return [x / len, y / len, z / len];
  }

  // Build orthonormal basis (right, up, forward) given stem direction `dir`
  function buildBasis(dir) {
    const up = normalize3(dir[0], dir[1], dir[2]);
    let refX = 0;
    let refY = 0;
    let refZ = 1;
    if (Math.abs(up[2]) > 0.92) {
      refX = 1;
      refZ = 0;
    }
    // right = normalize(cross(ref, up))
    let rx = refY * up[2] - refZ * up[1];
    let ry = refZ * up[0] - refX * up[2];
    let rz = refX * up[1] - refY * up[0];
    const rLen = Math.hypot(rx, ry, rz) || 1;
    rx /= rLen;
    ry /= rLen;
    rz /= rLen;
    // fwd = cross(up, right)
    const fx = up[1] * rz - up[2] * ry;
    const fy = up[2] * rx - up[0] * rz;
    const fz = up[0] * ry - up[1] * rx;
    return {
      right: [rx, ry, rz],
      up,
      fwd: [fx, fy, fz]
    };
  }

  // ---------------------------------------------------------------------------
  // 1. 3D Parametric Blue Tulip Generator (Water-Tight Goblet + Pointed Tepals)
  // ---------------------------------------------------------------------------
  function tulipPetalPos(u, v, phiCenter, isOuter, open) {
    const openEff = open * (isOuter ? 1.0 : 0.78);
    // Classic plump egg-goblet belly in lower half, graceful chalice curve above
    const belly = Math.sin(Math.pow(u, 0.64) * Math.PI);
    const cupFlare = Math.pow(u, 1.48) * (0.032 + 0.125 * openEff);
    const budClose = (1 - openEff * 0.84) * Math.pow(u, 1.72) * 0.095;
    const rBase = 0.022 + 0.132 * belly + cupFlare - budClose + (isOuter ? 0.015 : 0);

    const spoonCup = (1 - v * v) * 0.028 * belly;
    const tipReflex = u > 0.75 && openEff > 0.35
      ? Math.pow((u - 0.75) / 0.25, 2) * 0.026 * openEff
      : 0;
    const r = Math.max(0.01, rBase + spoonCup + tipReflex);

    // Distinct pointed tulip petal arch at tip
    const pointArch = (1 - Math.pow(Math.abs(v), 1.3)) * 0.048 * Math.pow(u, 1.35);
    const h = u * (0.37 - 0.04 * openEff) + pointArch + (isOuter ? -0.006 : 0.012 * u);

    // Broad overlapping lower cup, tapering cleanly to 6 distinct pointed tips at u=1
    const widthProfile = Math.sin(Math.pow(u, 0.60) * Math.PI);
    const halfWidthAng = (isOuter ? 0.67 : 0.62) * Math.pow(widthProfile, 0.75) + 0.05 * (1 - u);
    const phi = phiCenter + v * halfWidthAng;
    return [r * Math.cos(phi), h, r * Math.sin(phi)];
  }

  function generateTulipLocalPoints(palette, open) {
    const pts = [];
    const uSteps = 28;
    const vSteps = 15;
    const isLight = palette.shadeGroup === 'light';

    // 6 overlapping pointed tepals (3 inner, 3 outer)
    for (let k = 0; k < 6; k++) {
      const isOuter = k % 2 === 1;
      const phiCenter = (k * Math.PI) / 3;
      const du = 0.015;
      const dv = 0.045;

      for (let iu = 0; iu < uSteps; iu++) {
        const u = (iu + 0.45) / uSteps;
        let baseCol;
        if (u < 0.34) {
          baseCol = lerpColor(palette.base, palette.mid, u / 0.34);
        } else {
          baseCol = lerpColor(palette.mid, palette.tip, Math.pow((u - 0.34) / 0.66, 0.88));
        }

        for (let iv = 0; iv < vSteps; iv++) {
          const v = -1 + (2 * iv) / (vSteps - 1);
          const p = tulipPetalPos(u, v, phiCenter, isOuter, open);
          const pu = tulipPetalPos(Math.min(1, u + du), v, phiCenter, isOuter, open);
          const pv = tulipPetalPos(u, Math.min(1, v + dv), phiCenter, isOuter, open);

          const ux = pu[0] - p[0];
          const uy = pu[1] - p[1];
          const uz = pu[2] - p[2];
          const vx = pv[0] - p[0];
          const vy = pv[1] - p[1];
          const vz = pv[2] - p[2];

          let nx = vy * uz - vz * uy;
          let ny = vz * ux - vx * uz;
          let nz = vx * uy - vy * ux;
          if (nx * p[0] + nz * p[2] < 0) {
            nx = -nx;
            ny = -ny;
            nz = -nz;
          }
          const n = normalize3(nx, ny, nz);

          // Subtle edge definition so overlapping tepals read clearly
          const edgeRim = Math.pow(Math.abs(v), 2.6) * (isLight ? 18 : 22) * Math.pow(u, 0.7);
          // Keep glyph density strong on both dark-blue and light-blue tulips!
          const ao = 0.62 + 0.38 * Math.pow(u, 0.45) * (isOuter ? 1.0 : 0.93);
          const colorCurve = 0.55 + 0.45 * Math.pow(u, 0.5);
          pts.push({
            x: p[0],
            y: p[1],
            z: p[2],
            nx: n[0],
            ny: n[1],
            nz: n[2],
            r: clamp(baseCol[0] * colorCurve + edgeRim * 0.35, 0, 255),
            g: clamp(baseCol[1] * colorCurve + edgeRim * 0.85, 0, 255),
            b: clamp(baseCol[2] * colorCurve + edgeRim * 1.25, 0, 255),
            ao,
            splat: 1
          });
        }
      }
    }

    // Solid bottom cup plug so stem/background never shines up through receptacle
    for (let ir = 0; ir < 4; ir++) {
      const rad = (ir / 3) * 0.036;
      for (let ic = 0; ic < 12; ic++) {
        const ang = (ic * Math.PI * 2) / 12;
        pts.push({
          x: Math.cos(ang) * rad,
          y: 0.005,
          z: Math.sin(ang) * rad,
          nx: Math.cos(ang) * 0.4,
          ny: -0.9,
          nz: Math.sin(ang) * 0.4,
          r: palette.base[0],
          g: palette.base[1],
          b: palette.base[2],
          ao: 0.6,
          splat: 1
        });
      }
    }

    // 6 inner stamens + golden-cream anthers peeking inside open tulip chalice
    for (let s = 0; s < 6; s++) {
      const ang = (s * Math.PI) / 3 + 0.26;
      const ca = Math.cos(ang);
      const sa = Math.sin(ang);
      const rad = 0.026 + 0.015 * open;
      for (let j = 0; j < 4; j++) {
        const f = (j + 1) / 4;
        const isTip = j >= 2;
        pts.push({
          x: ca * rad * (0.65 + 0.38 * f),
          y: 0.04 + f * 0.14,
          z: sa * rad * (0.65 + 0.38 * f),
          nx: ca * 0.5,
          ny: 0.86,
          nz: sa * 0.5,
          r: isTip ? 250 : 18,
          g: isTip ? 218 : 38,
          b: isTip ? 105 : 112,
          ao: isTip ? 0.95 : 0.55,
          splat: 0
        });
      }
    }

    // Green calyx collar joining stem
    for (let c = 0; c < 14; c++) {
      const ang = (c * Math.PI * 2) / 14;
      const ca = Math.cos(ang);
      const sa = Math.sin(ang);
      pts.push({
        x: ca * 0.032,
        y: -0.012,
        z: sa * 0.032,
        nx: ca,
        ny: -0.35,
        nz: sa,
        r: 30,
        g: 148,
        b: 72,
        ao: 0.78,
        splat: 1
      });
    }

    return pts;
  }

  // ---------------------------------------------------------------------------
  // 2. 3D Parametric Sunflower Generator (Water-Tight Disk + Spiky Sun Rays)
  // ---------------------------------------------------------------------------
  function generateSunflowerLocalPoints(open) {
    const pts = [];

    // Water-tight concentric polar seed disk (~560 points -> ZERO pinholes!)
    const diskRadius = 0.145;
    const rRings = 16;
    for (let ir = 0; ir <= rRings; ir++) {
      const t = ir / rRings;
      const rad = diskRadius * t;
      const domeY = 0.048 * Math.cos(t * Math.PI * 0.46);
      const slope = 0.36 * t;
      const ringCount = Math.max(6, Math.round(10 + 48 * t));

      for (let it = 0; it < ringCount; it++) {
        const theta = (it * Math.PI * 2) / ringCount + ir * GOLDEN_ANGLE * 0.35;
        const cp = Math.cos(theta);
        const sp = Math.sin(theta);
        const n = normalize3(cp * slope, 1, sp * slope);

        // Rich roasted-espresso brown disk (solid glyph density ao ~0.68 so never transparent!)
        let col;
        let seedAo;
        if (t < 0.62) {
          col = lerpColor([72, 34, 10], [108, 52, 14], t / 0.62);
          seedAo = 0.62 + ((ir + it) % 2) * 0.10;
        } else if (t < 0.86) {
          col = lerpColor([108, 52, 14], [156, 78, 16], (t - 0.62) / 0.24);
          seedAo = 0.70 + ((ir + it) % 2) * 0.08;
        } else {
          col = lerpColor([185, 98, 14], [242, 158, 16], (t - 0.86) / 0.14);
          seedAo = 0.84;
        }

        pts.push({
          x: rad * cp,
          y: domeY,
          z: rad * sp,
          nx: n[0],
          ny: n[1],
          nz: n[2],
          r: col[0],
          g: col[1],
          b: col[2],
          ao: seedAo,
          splat: 1
        });
      }
    }

    // 16 primary pointed golden ray petals + 16 shorter inner offset petals
    // Total head radius ~ 0.145 * 0.86 + 0.185 = 0.31 (collision-free with neighbors!)
    const ringConfigs = [
      { count: 16, offset: 0, len: 0.185, width: 0.029, pitchOpen: 0.05, aoBoost: 1.0 },
      { count: 16, offset: Math.PI / 16, len: 0.145, width: 0.024, pitchOpen: 0.16, aoBoost: 0.9 }
    ];

    for (let rIdx = 0; rIdx < ringConfigs.length; rIdx++) {
      const cfg = ringConfigs[rIdx];
      const uSteps = 16;
      const vSteps = 7;

      for (let k = 0; k < cfg.count; k++) {
        const phi = (k * Math.PI * 2) / cfg.count + cfg.offset;
        const cp = Math.cos(phi);
        const sp = Math.sin(phi);
        const tx = -sp;
        const tz = cp;

        const basePitch = lerp(1.15, cfg.pitchOpen, open);

        for (let iu = 0; iu < uSteps; iu++) {
          const u = (iu + 0.4) / uSteps;
          const pitch = basePitch - 0.15 * u * open;
          const distOut = diskRadius * 0.86 + u * cfg.len * Math.cos(pitch);
          const yOff = 0.015 + u * cfg.len * Math.sin(pitch) - 0.02 * u * u * open;
          const halfW = cfg.width * Math.sin(Math.pow(u, 0.52) * Math.PI) * (1 - 0.38 * u * u);

          let col;
          if (u < 0.28) {
            col = lerpColor([238, 148, 10], [255, 212, 22], u / 0.28);
          } else {
            col = lerpColor([255, 212, 22], [255, 246, 118], (u - 0.28) / 0.72);
          }

          const n = normalize3(
            cp * Math.sin(pitch) * 0.35,
            Math.cos(pitch),
            sp * Math.sin(pitch) * 0.35
          );

          for (let iv = 0; iv < vSteps; iv++) {
            const v = -1 + (2 * iv) / (vSteps - 1);
            const x = distOut * cp + v * halfW * tx;
            const z = distOut * sp + v * halfW * tz;
            const y = yOff + (1 - Math.abs(v)) * 0.008;
            const ao = cfg.aoBoost * (0.82 + 0.18 * u);

            pts.push({
              x,
              y,
              z,
              nx: n[0],
              ny: n[1],
              nz: n[2],
              r: col[0],
              g: col[1],
              b: col[2],
              ao,
              splat: 1
            });
          }
        }
      }
    }

    // Solid green involucre backing plate + bracts underneath the seed disk
    for (let ir = 0; ir <= 8; ir++) {
      const f = ir / 8;
      const rad = f * 0.165;
      const ringN = Math.max(6, Math.round(8 + 24 * f));
      for (let b = 0; b < ringN; b++) {
        const phi = (b * Math.PI * 2) / ringN + ir * 0.2;
        const cp = Math.cos(phi);
        const sp = Math.sin(phi);
        const y = -0.018 - (1 - f) * 0.022 + f * 0.008;
        pts.push({
          x: rad * cp,
          y,
          z: rad * sp,
          nx: cp * 0.45,
          ny: -0.88,
          nz: sp * 0.45,
          r: lerp(22, 56, f),
          g: lerp(108, 174, f),
          b: lerp(44, 82, f),
          ao: 0.74,
          splat: 1
        });
      }
    }

    return pts;
  }

  // ---------------------------------------------------------------------------
  // 3. Collision-Free Bouquet Layout (13 Blue Tulips [Tua & Muda] + 3 Sunflowers = 16)
  // ---------------------------------------------------------------------------
  function initFlowers() {
    flowers.length = 0;
    const rng = createRng(20261124);
    const specs = [];

    // Curated alternating order so Biru Tua & Biru Muda sit side-by-side cleanly:
    // 0: cobalt (tua), 1: sky (muda), 2: sapphire (tua), 3: ice (muda), 4: royal (mid)
    const crownPalettes = [0, 1, 2, 3]; // Tua, Muda, Tua, Muda
    const midTulipPalettes = [4, 1, 0]; // Royal, Muda, Tua
    const outerPalettes = [1, 2, 3, 0, 1, 2]; // Muda, Tua, Muda, Tua, Muda, Tua

    // Tier 1: Upper Crown (4 Tulips at rad = 0.27 -> chord = 0.382 > 0.34!)
    for (let i = 0; i < 4; i++) {
      const theta = 0.55 + (i * Math.PI * 2) / 4;
      specs.push({
        type: 'tulip',
        paletteIdx: crownPalettes[i],
        theta,
        tilt: 0.17,
        y: 1.02 - (i % 2) * 0.02,
        rad: 0.27,
        scale: 1.0,
        startTime: 0.2 + i * 0.22
      });
    }

    // Tier 2: Middle Ring (6 blooms: 3 Sunflowers + 3 Tulips alternating 60° apart)
    let midTulipCounter = 0;
    for (let i = 0; i < 6; i++) {
      const theta = 0.32 + (i * Math.PI * 2) / 6;
      const isSunflower = i % 2 === 0;
      specs.push({
        type: isSunflower ? 'sunflower' : 'tulip',
        paletteIdx: isSunflower ? -1 : midTulipPalettes[midTulipCounter++],
        theta,
        tilt: isSunflower ? 0.48 : 0.40,
        y: isSunflower ? 0.76 : 0.68,
        rad: isSunflower ? 0.66 : 0.57,
        scale: isSunflower ? 1.02 : 1.0,
        startTime: 0.95 + i * 0.3
      });
    }

    // Tier 3: Outer Rim (6 Tulips staggered at exact +30° midpoints between Tier 2 blooms!)
    for (let i = 0; i < 6; i++) {
      const theta = 0.32 + ((i + 0.5) * Math.PI * 2) / 6;
      specs.push({
        type: 'tulip',
        paletteIdx: outerPalettes[i],
        theta,
        tilt: 0.72,
        y: 0.28 + (i % 2) * 0.02,
        rad: 0.88,
        scale: 1.0,
        startTime: 2.2 + i * 0.32
      });
    }

    for (let i = 0; i < specs.length; i++) {
      const sp = specs[i];
      const ct = Math.cos(sp.theta);
      const st = Math.sin(sp.theta);
      const pos = [sp.rad * ct, sp.y, sp.rad * st];
      const sinTilt = Math.sin(sp.tilt);
      const cosTilt = Math.cos(sp.tilt);
      const dir = normalize3(sinTilt * ct, cosTilt, sinTilt * st);
      const basis = buildBasis(dir);
      const palette = sp.type === 'tulip' ? TULIP_PALETTES[sp.paletteIdx] : null;

      flowers.push({
        id: i,
        type: sp.type,
        palette,
        pos,
        dir,
        basis,
        scale: sp.scale,
        startTime: sp.startTime,
        duration: 2.8 + rng() * 0.5,
        cachedOpen: -1,
        localPoints: []
      });
    }
  }

  // ---------------------------------------------------------------------------
  // 4. Static Bouquet Geometry (Collision-Free Stems, Outer Leaves, Wrap, Ribbon)
  // ---------------------------------------------------------------------------
  function buildStaticGeometry() {
    staticPoints.length = 0;
    const rng = createRng(88421);

    // Precompute flower head obstacle centers & clearance radii so foliage/gypsophila NEVER pierce blooms!
    const obstacles = flowers.map((fl) => {
      const headOffset = fl.type === 'tulip' ? 0.19 * fl.scale : 0.05 * fl.scale;
      return {
        cx: fl.pos[0] + fl.dir[0] * headOffset,
        cy: fl.pos[1] + fl.dir[1] * headOffset,
        cz: fl.pos[2] + fl.dir[2] * headOffset,
        clearR: fl.type === 'tulip' ? 0.21 * fl.scale : 0.34 * fl.scale
      };
    });

    function hitsAnyFlower(px, py, pz) {
      for (let m = 0; m < obstacles.length; m++) {
        const ob = obstacles[m];
        const dx = px - ob.cx;
        const dy = py - ob.cy;
        const dz = pz - ob.cz;
        if (dx * dx + dy * dy + dz * dz < ob.clearR * ob.clearR) return true;
      }
      return false;
    }

    // A. Curved Green Stems ending strictly below each flower receptacle
    const waistY = -0.50;
    for (let i = 0; i < flowers.length; i++) {
      const fl = flowers[i];
      // Terminate stem 0.025 below flower base so stem never pokes into cup/disk
      const top = [
        fl.pos[0] - fl.dir[0] * 0.025,
        fl.pos[1] - fl.dir[1] * 0.025,
        fl.pos[2] - fl.dir[2] * 0.025
      ];
      const theta = Math.atan2(top[2], top[0]);
      const waistRad = 0.065 * (0.4 + 0.6 * rng());
      const mid = [
        waistRad * Math.cos(theta + 0.15),
        waistY,
        waistRad * Math.sin(theta + 0.15)
      ];
      const botRad = 0.15 + 0.09 * rng();
      const bot = [
        botRad * Math.cos(theta + 0.25),
        -1.18 - rng() * 0.05,
        botRad * Math.sin(theta + 0.25)
      ];

      // Curve stem inward underneath the canopy so inner stems never slice outer flowers!
      const ctrlTop = [
        top[0] * 0.38 + mid[0] * 0.62,
        lerp(top[1], mid[1], 0.48),
        top[2] * 0.38 + mid[2] * 0.62
      ];
      for (let s = 0; s <= 28; s++) {
        const t = s / 28;
        const omt = 1 - t;
        const cx = omt * omt * top[0] + 2 * omt * t * ctrlTop[0] + t * t * mid[0];
        const cy = omt * omt * top[1] + 2 * omt * t * ctrlTop[1] + t * t * mid[1];
        const cz = omt * omt * top[2] + 2 * omt * t * ctrlTop[2] + t * t * mid[2];
        const rad = fl.type === 'sunflower' ? 0.019 : 0.015;
        for (let k = 0; k < 4; k++) {
          const ang = (k * Math.PI) / 2 + t * 0.7;
          const ca = Math.cos(ang);
          const sa = Math.sin(ang);
          staticPoints.push({
            x: cx + rad * ca,
            y: cy,
            z: cz + rad * sa,
            nx: ca,
            ny: 0.15,
            nz: sa,
            r: lerp(38, 22, t),
            g: lerp(158, 112, t),
            b: lerp(80, 56, t),
            ao: 0.72,
            splat: 0
          });
        }
      }

      for (let s = 1; s <= 18; s++) {
        const t = s / 18;
        const cx = lerp(mid[0], bot[0], t);
        const cy = lerp(mid[1], bot[1], t);
        const cz = lerp(mid[2], bot[2], t);
        for (let k = 0; k < 3; k++) {
          const ang = (k * Math.PI * 2) / 3;
          const ca = Math.cos(ang);
          const sa = Math.sin(ang);
          staticPoints.push({
            x: cx + 0.013 * ca,
            y: cy,
            z: cz + 0.013 * sa,
            nx: ca,
            ny: -0.1,
            nz: sa,
            r: 24,
            g: 112,
            b: 58,
            ao: 0.65,
            splat: 0
          });
        }
      }
    }

    // B. 12 Broad Pointed Tulip Leaves placed strictly in the outer perimeter gaps
    for (let i = 0; i < 12; i++) {
      const phi = 0.32 + (i * Math.PI * 2) / 12;
      const cp = Math.cos(phi);
      const sp = Math.sin(phi);
      const tx = -sp;
      const tz = cp;
      const leafLen = 0.62 + (i % 2) * 0.10;
      const maxWidth = 0.088;
      const startY = -0.46;
      const startRad = 0.16;
      const archOut = 0.92 + (i % 2) * 0.08;

      for (let iu = 0; iu < 22; iu++) {
        const u = iu / 21;
        const rad = startRad + archOut * Math.pow(u, 0.92);
        const y = startY + leafLen * (u * 0.98 - 0.24 * u * u);
        const w = maxWidth * Math.sin(Math.pow(u, 0.65) * Math.PI) * (1 - 0.25 * u * u);
        const col = lerpColor([16, 92, 46], [68, 212, 122], Math.pow(u, 0.85));

        for (let iv = 0; iv < 5; iv++) {
          const v = -1 + (2 * iv) / 4;
          const trough = Math.abs(v) * 0.022 * Math.sin(u * Math.PI);
          const px = rad * cp + v * w * tx;
          const pz = rad * sp + v * w * tz;
          const py = y + trough;
          if (hitsAnyFlower(px, py, pz)) continue;

          const n = normalize3(cp * 0.7 + tx * v * 0.4, 0.6, sp * 0.7 + tz * v * 0.4);
          staticPoints.push({
            x: px,
            y: py,
            z: pz,
            nx: n[0],
            ny: n[1],
            nz: n[2],
            r: col[0],
            g: col[1],
            b: col[2],
            ao: 0.62 + 0.38 * u,
            splat: 1
          });
        }
      }
    }

    // C. Delicate Baby's Breath florets strictly in open gaps (NEVER inside flowers!)
    let gypPlaced = 0;
    let gypAttempts = 0;
    while (gypPlaced < 28 && gypAttempts < 240) {
      gypAttempts++;
      const phi = rng() * Math.PI * 2;
      const rad = 0.38 + rng() * 0.56;
      const y = 0.26 + rng() * 0.66;
      const cx = rad * Math.cos(phi);
      const cz = rad * Math.sin(phi);
      if (hitsAnyFlower(cx, y, cz)) continue;
      gypPlaced++;
      staticPoints.push({
        x: cx,
        y,
        z: cz,
        nx: Math.cos(phi) * 0.5,
        ny: 0.86,
        nz: Math.sin(phi) * 0.5,
        r: 226,
        g: 242,
        b: 255,
        ao: 0.92,
        splat: 0
      });
    }

    // D. 360°-Symmetric Scalloped Wrapping Paper staying strictly BELOW Tier 3 blooms (topY <= 0.16!)
    const uLayers = [
      { radScale: 1.0, phase: 0.0, yShift: 0.0, tint: [118, 138, 174] },
      { radScale: 1.07, phase: 0.52, yShift: -0.04, tint: [96, 114, 150] }
    ];

    for (let l = 0; l < uLayers.length; l++) {
      const layer = uLayers[l];
      const uSteps = 16;
      const tSteps = 64;
      for (let iu = 0; iu < uSteps; iu++) {
        const u = iu / (uSteps - 1);
        for (let it = 0; it < tSteps; it++) {
          const theta = (it / tSteps) * Math.PI * 2;
          const scallop = 0.055 * Math.cos(theta * 7 + layer.phase * 2);
          const topY = 0.11 + scallop + layer.yShift;
          const pleatWave = Math.sin(theta * 14 + layer.phase);
          const pleat = 0.042 * pleatWave * Math.pow(u, 0.85);
          const rad = (0.18 + 0.86 * Math.pow(u, 0.88) + pleat) * layer.radScale;
          const y = lerp(waistY, topY, u);

          const isRim = iu === uSteps - 1;
          const col = isRim
            ? [204, 222, 248]
            : lerpColor(
                [layer.tint[0] - 18, layer.tint[1] - 16, layer.tint[2] - 10],
                [176, 196, 226],
                u * 0.85 + Math.max(0, pleatWave) * 0.15
              );
          const n = normalize3(
            Math.cos(theta) + pleatWave * 0.3 * Math.sin(theta),
            -0.35,
            Math.sin(theta) - pleatWave * 0.3 * Math.cos(theta)
          );
          staticPoints.push({
            x: rad * Math.cos(theta),
            y,
            z: rad * Math.sin(theta),
            nx: n[0],
            ny: n[1],
            nz: n[2],
            r: col[0],
            g: col[1],
            b: col[2],
            ao: isRim ? 0.88 : 0.48 + 0.25 * u,
            splat: 0
          });
        }
      }
    }

    // Lower flared paper skirt from waist down to bottom
    const lowUSteps = 12;
    const lowTSteps = 42;
    for (let iu = 0; iu < lowUSteps; iu++) {
      const u = iu / (lowUSteps - 1);
      for (let it = 0; it < lowTSteps; it++) {
        const theta = (it / lowTSteps) * Math.PI * 2;
        const pleatWave = Math.sin(theta * 8 + 0.2);
        const pleat = 0.036 * pleatWave * u;
        const rad = 0.18 + 0.29 * Math.pow(u, 0.9) + pleat;
        const y = lerp(waistY, -1.18, u);
        const ridgeLift = pleatWave * 14 * u;
        const baseCol = lerpColor([152, 170, 202], [108, 126, 158], u);
        const n = normalize3(Math.cos(theta), 0.25, Math.sin(theta));
        staticPoints.push({
          x: rad * Math.cos(theta),
          y,
          z: rad * Math.sin(theta),
          nx: n[0],
          ny: n[1],
          nz: n[2],
          r: clamp(baseCol[0] + ridgeLift, 0, 255),
          g: clamp(baseCol[1] + ridgeLift, 0, 255),
          b: clamp(baseCol[2] + ridgeLift * 0.85, 0, 255),
          ao: 0.55,
          splat: 0
        });
      }
    }

    // E. Royal Blue Satin Ribbon Band & Bow at Waist (y = -0.44)
    for (let iy = 0; iy < 4; iy++) {
      const y = waistY - 0.03 + (iy / 3) * 0.06;
      for (let it = 0; it < 44; it++) {
        const theta = (it / 44) * Math.PI * 2;
        const rad = 0.228;
        staticPoints.push({
          x: rad * Math.cos(theta),
          y,
          z: rad * Math.sin(theta),
          nx: Math.cos(theta),
          ny: iy === 0 ? -0.4 : iy === 3 ? 0.4 : 0,
          nz: Math.sin(theta),
          r: 36,
          g: 130,
          b: 255
        });
      }
    }

    // Two sculpted 3D bow loops on the front (+Z) side
    for (const side of [-1, 1]) {
      for (let iu = 0; iu < 18; iu++) {
        const t = (iu / 17) * Math.PI * 2;
        const loopR = 0.095 * Math.sin(t * 0.5);
        const lx = side * (0.045 + 0.18 * Math.sin(t * 0.5));
        const ly = waistY + 0.065 * Math.sin(t);
        const lz = 0.24 + loopR * 0.65;
        for (let w = -1; w <= 1; w++) {
          staticPoints.push({
            x: lx,
            y: ly + w * 0.017,
            z: lz + w * 0.008,
            nx: side * 0.45,
            ny: Math.sin(t) * 0.4,
            nz: 0.85,
            r: lerp(36, 135, Math.abs(Math.sin(t)) * 0.65),
            g: lerp(130, 215, Math.abs(Math.sin(t)) * 0.65),
            b: 255
          });
        }
      }
    }

    // Two flowing ribbon tails
    for (const side of [-1, 1]) {
      for (let s = 0; s < 16; s++) {
        const f = s / 15;
        const tx = side * (0.028 + 0.14 * f + 0.025 * Math.sin(f * 4));
        const ty = waistY - 0.02 - 0.36 * f;
        const tz = 0.24 + 0.05 * f + 0.02 * Math.sin(f * 3);
        for (let w = -1; w <= 1; w++) {
          staticPoints.push({
            x: tx + w * 0.013,
            y: ty,
            z: tz,
            nx: side * 0.25,
            ny: 0.15,
            nz: 0.95,
            r: lerp(36, 135, 1 - f),
            g: lerp(130, 215, 1 - f),
            b: 255
          });
        }
      }
    }

    // Warm golden-amber center knot highlight (ties in the sunflower accent)
    for (let ky = -1; ky <= 1; ky++) {
      for (let kx = -1; kx <= 1; kx++) {
        staticPoints.push({
          x: kx * 0.016,
          y: waistY + ky * 0.015,
          z: 0.258,
          nx: kx * 0.3,
          ny: ky * 0.3,
          nz: 0.95,
          r: 252,
          g: 204,
          b: 24
        });
      }
    }
  }

  // ---------------------------------------------------------------------------
  // 5. Starfield & Falling Petals
  // ---------------------------------------------------------------------------
  function initStars() {
    stars.length = 0;
    const rng = createRng(7719);
    const count = 340;
    for (let i = 0; i < count; i++) {
      const isFlare = i < 14;
      const tint = rng();
      let r = 215;
      let g = 228;
      let b = 255;
      if (tint < 0.28) {
        r = 155;
        g = 198;
        b = 255;
      } else if (tint > 0.88) {
        r = 255;
        g = 236;
        b = 185;
      }
      stars.push({
        nx: rng(),
        ny: rng(),
        phase: rng() * Math.PI * 2,
        speed: 0.8 + rng() * 2.1,
        baseLum: isFlare ? 0.85 : 0.25 + rng() * 0.55,
        isFlare,
        ch: isFlare ? '+' : rng() < 0.55 ? '.' : rng() < 0.82 ? '*' : '·',
        r,
        g,
        b
      });
    }
  }

  function spawnFallingPetal() {
    const openFlowers = [];
    for (let i = 0; i < flowers.length; i++) {
      if (flowers[i].cachedOpen >= 0.78) {
        openFlowers.push(flowers[i]);
      }
    }
    if (openFlowers.length === 0) return;

    const src = openFlowers[(Math.random() * openFlowers.length) | 0];
    const isSunflower = src.type === 'sunflower';
    const angle = Math.random() * Math.PI * 2;
    const offsetR = 0.08 + Math.random() * 0.1;

    fallingPetals.push({
      x: src.pos[0] + Math.cos(angle) * offsetR,
      y: src.pos[1] + 0.05,
      z: src.pos[2] + Math.sin(angle) * offsetR,
      vx: (Math.random() - 0.5) * 0.08,
      vy: -(0.16 + Math.random() * 0.12),
      vz: (Math.random() - 0.5) * 0.08,
      spinX: Math.random() * Math.PI * 2,
      spinY: Math.random() * Math.PI * 2,
      spinVx: (Math.random() - 0.5) * 2.2,
      spinVy: (Math.random() - 0.5) * 2.6,
      swayPhase: Math.random() * Math.PI * 2,
      age: 0,
      maxAge: 6.5 + Math.random() * 2.5,
      col: isSunflower ? [252, 206, 28] : [78, 162, 255]
    });
  }

  // ---------------------------------------------------------------------------
  // 6. Responsive Resize & Buffer Allocation
  // ---------------------------------------------------------------------------
  function handleResize() {
    dpr = Math.min(window.devicePixelRatio || 1, 2);
    viewW = window.innerWidth;
    viewH = window.innerHeight;

    canvas.width = Math.max(1, Math.floor(viewW * dpr));
    canvas.height = Math.max(1, Math.floor(viewH * dpr));
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);

    const isMobile = viewW < 600;
    const targetCols = isMobile ? clamp(Math.round(viewW / 3.6), 94, 128) : clamp(Math.round(viewW / 5.4), 165, 240);
    fontSize = clamp(viewW / (targetCols * 0.6), isMobile ? 5.6 : 7.2, isMobile ? 7.8 : 9.6);

    ctx.font = `400 ${fontSize}px "JetBrains Mono", ui-monospace, SFMono-Regular, Menlo, Consolas, monospace`;
    ctx.textBaseline = 'top';

    const measured = ctx.measureText('M').width;
    cellW = Math.max(3.8, measured);
    cellH = Math.max(6.8, fontSize * 1.15);

    cols = Math.max(20, Math.floor(viewW / cellW));
    rows = Math.max(20, Math.floor(viewH / cellH));

    const total = cols * rows;
    zBuf = new Float32Array(total);
    charBuf = new Uint8Array(total);
    rBuf = new Uint8Array(total);
    gBuf = new Uint8Array(total);
    bBuf = new Uint8Array(total);
    bucketNext = new Int32Array(total);

    centerYRatio = isMobile ? 0.50 : 0.54;
    // Generous framing with clean top starry headroom (~2.64 tall x 2.38 wide)
    const usableH = viewH * (isMobile ? 0.78 : 0.82);
    const usableW = viewW * (isMobile ? 0.92 : 0.86);
    fovScale = Math.min(usableH / 2.64, usableW / 2.38);
  }

  // ---------------------------------------------------------------------------
  // 7. Projection & Water-Tight Shading Pipeline (Sub-cell Z-Splatting)
  // ---------------------------------------------------------------------------
  function writeCell(col, row, zVal, charIdx, rr, gg, bb) {
    if (col < 0 || col >= cols || row < 0 || row >= rows) return;
    const idx = row * cols + col;
    if (zVal <= zBuf[idx]) return;
    zBuf[idx] = zVal;
    charBuf[idx] = charIdx;
    rBuf[idx] = rr;
    gBuf[idx] = gg;
    bBuf[idx] = bb;
  }

  function projectPoint(wx, wy, wz, wnx, wny, wnz, cr, cg, cb, ao, splat, sinY, cosY, sinX, cosX, swaySin, zoomScale, cxPx, cyPx) {
    const swayAmt = Math.max(0, wy + 0.50) * 0.025 * swaySin;
    const sx = wx + swayAmt;

    // Rotate around Y then X
    const x1 = sx * cosY + wz * sinY;
    const z1 = -sx * sinY + wz * cosY;
    const y2 = wy * cosX - z1 * sinX;
    const z2 = wy * sinX + z1 * cosX;

    const depth = camDist - z2;
    if (depth <= 0.45) return;

    const persp = (camDist / depth) * zoomScale;
    const fx = (cxPx + x1 * persp * fovScale) / cellW;
    const fy = (cyPx - y2 * persp * fovScale) / cellH;

    const col = fx | 0;
    const row = fy | 0;
    if (col < 0 || col >= cols || row < 0 || row >= rows) return;

    // Rotate normal
    const nx1 = wnx * cosY + wnz * sinY;
    const nz1 = -wnx * sinY + wnz * cosY;
    const ny2 = wny * cosX - nz1 * sinX;
    const nz2 = wny * sinX + nz1 * cosX;

    const isFront = nz2 >= -0.06;
    const dot1 = nx1 * L1[0] + ny2 * L1[1] + nz2 * L1[2];
    const diff1 = isFront
      ? Math.max(0, dot1) * 0.85 + 0.15
      : 0.22 + Math.max(0, -dot1) * 0.16;
    const dot2 = isFront ? Math.max(0, nx1 * L2[0] + ny2 * L2[1] + nz2 * L2[2]) : 0;
    const rim = isFront ? Math.pow(1 - Math.min(1, Math.abs(nz2)), 2.2) * 0.26 : 0.04;
    const depthBoost = clamp((z2 + 0.8) * 0.08, -0.06, 0.12);

    const aoFactor = ao !== undefined ? ao : 0.8;
    const rawShade = (0.16 + 0.68 * diff1 + 0.16 * dot2 + rim + depthBoost) * (0.48 + 0.52 * aoFactor);
    const shade = clamp(rawShade, 0.12, 1.0);
    let charIdx = Math.round(shade * (RAMP_LEN - 1));
    if (charIdx < 1) charIdx = 1;

    const lum = isFront ? 0.34 + 0.78 * shade : 0.20 + 0.36 * shade;
    const sheen = isFront && shade > 0.90 ? (shade - 0.90) * 48 : 0;
    const rr = clamp(cr * lum + sheen, 0, 255);
    const gg = clamp(cg * lum + sheen, 0, 255);
    const bb = clamp(cb * lum + sheen, 0, 255);

    // Primary cell
    writeCell(col, row, z2, charIdx, rr, gg, bb);

    // Sub-cell gap-closing splat on solid petals/disks so background NEVER bleeds through pinholes!
    if (splat) {
      const fracX = fx - col;
      const fracY = fy - row;
      const zBias = z2 - 0.022;
      if (fracX > 0.56) writeCell(col + 1, row, zBias, charIdx, rr, gg, bb);
      else if (fracX < 0.44) writeCell(col - 1, row, zBias, charIdx, rr, gg, bb);
      if (fracY > 0.58) writeCell(col, row + 1, zBias, charIdx, rr, gg, bb);
      else if (fracY < 0.42) writeCell(col, row - 1, zBias, charIdx, rr, gg, bb);
    }
  }

  function renderFrame(dt) {
    bloomClock += dt;
    animTime += dt;
    currentZoom = lerp(currentZoom, targetZoom, Math.min(1, dt * 10));
    if (autoSpin && !isDragging) {
      rotY += dt * 0.36;
    }

    // Clear Z-buffer & char buffer
    zBuf.fill(-1e9);
    charBuf.fill(0);

    const sinY = Math.sin(rotY);
    const cosY = Math.cos(rotY);
    const sinX = Math.sin(rotX);
    const cosX = Math.cos(rotX);
    const swaySin = Math.sin(animTime * 0.95);
    const cxPx = viewW * 0.5;
    const cyPx = viewH * centerYRatio;

    // 1. Project static geometry (stems, leaves, baby's breath, wrap, ribbon)
    for (let i = 0, n = staticPoints.length; i < n; i++) {
      const p = staticPoints[i];
      projectPoint(
        p.x, p.y, p.z,
        p.nx, p.ny, p.nz,
        p.r, p.g, p.b, p.ao, p.splat,
        sinY, cosY, sinX, cosX, swaySin, currentZoom, cxPx, cyPx
      );
    }

    // 2. Update & project all 16 flowers
    let openCount = 0;
    for (let f = 0; f < flowers.length; f++) {
      const fl = flowers[f];
      const rawT = (bloomClock - fl.startTime) / fl.duration;
      const open = easeOutCubic(rawT);
      if (open >= 0.82) openCount++;

      if (Math.abs(open - fl.cachedOpen) >= 0.012 || fl.localPoints.length === 0) {
        fl.cachedOpen = open;
        fl.localPoints = fl.type === 'tulip'
          ? generateTulipLocalPoints(fl.palette, open)
          : generateSunflowerLocalPoints(open);
      }

      const R = fl.basis.right;
      const U = fl.basis.up;
      const F = fl.basis.fwd;
      const ox = fl.pos[0];
      const oy = fl.pos[1];
      const oz = fl.pos[2];
      const sc = fl.scale;
      const lpts = fl.localPoints;

      for (let j = 0, m = lpts.length; j < m; j++) {
        const lp = lpts[j];
        const wx = ox + (lp.x * R[0] + lp.y * U[0] + lp.z * F[0]) * sc;
        const wy = oy + (lp.x * R[1] + lp.y * U[1] + lp.z * F[1]) * sc;
        const wz = oz + (lp.x * R[2] + lp.y * U[2] + lp.z * F[2]) * sc;

        const wnx = lp.nx * R[0] + lp.ny * U[0] + lp.nz * F[0];
        const wny = lp.nx * R[1] + lp.ny * U[1] + lp.nz * F[1];
        const wnz = lp.nx * R[2] + lp.ny * U[2] + lp.nz * F[2];

        projectPoint(
          wx, wy, wz,
          wnx, wny, wnz,
          lp.r, lp.g, lp.b, lp.ao, lp.splat,
          sinY, cosY, sinX, cosX, swaySin, currentZoom, cxPx, cyPx
        );
      }
    }

    // 3. Update & project falling petals
    if (openCount > 0) {
      petalSpawnTimer += dt;
      if (petalSpawnTimer >= 0.52 && fallingPetals.length < 16) {
        petalSpawnTimer = 0;
        spawnFallingPetal();
      }
    }

    for (let i = fallingPetals.length - 1; i >= 0; i--) {
      const fp = fallingPetals[i];
      fp.age += dt;
      if (fp.age >= fp.maxAge || fp.y < -1.45) {
        fallingPetals.splice(i, 1);
        continue;
      }
      fp.x += (fp.vx + Math.sin(animTime * 1.6 + fp.swayPhase) * 0.08) * dt;
      fp.y += fp.vy * dt;
      fp.z += (fp.vz + Math.cos(animTime * 1.3 + fp.swayPhase) * 0.07) * dt;
      fp.spinX += fp.spinVx * dt;
      fp.spinY += fp.spinVy * dt;

      const fade = fp.age > fp.maxAge - 1.2 ? Math.max(0, (fp.maxAge - fp.age) / 1.2) : 1;
      const cxp = Math.cos(fp.spinX);
      const sxp = Math.sin(fp.spinX);
      const cyp = Math.cos(fp.spinY);
      const syp = Math.sin(fp.spinY);

      // 5-point mini petal patch
      const patch = [
        [0, 0, 0],
        [0.022, 0.008, 0],
        [-0.022, 0.008, 0],
        [0, 0.02, 0.015],
        [0, -0.018, 0.01]
      ];
      for (let k = 0; k < patch.length; k++) {
        const px0 = patch[k][0];
        const py0 = patch[k][1];
        const pz0 = patch[k][2];
        const rx = px0 * cyp + pz0 * syp;
        const rz1 = -px0 * syp + pz0 * cyp;
        const ry = py0 * cxp - rz1 * sxp;
        const rz = py0 * sxp + rz1 * cxp;
        projectPoint(
          fp.x + rx, fp.y + ry, fp.z + rz,
          0.3, 0.8, 0.5,
          fp.col[0] * fade, fp.col[1] * fade, fp.col[2] * fade, 0.9, 0,
          sinY, cosY, sinX, cosX, 0, currentZoom, cxPx, cyPx
        );
      }
    }

    // 4. Draw background
    ctx.fillStyle = '#03050a';
    ctx.fillRect(0, 0, viewW, viewH);

    // 5. Draw twinkling starfield onto empty cells
    const starLimit = viewW < 600 ? 200 : stars.length;
    for (let i = 0; i < starLimit; i++) {
      const st = stars[i];
      const sc = Math.floor(st.nx * cols);
      const sr = Math.floor(st.ny * rows);
      if (sc < 0 || sc >= cols || sr < 0 || sr >= rows) continue;
      const idx = sr * cols + sc;
      if (charBuf[idx] !== 0) continue;

      const tw = 0.55 + 0.45 * Math.sin(animTime * st.speed + st.phase);
      const lum = st.baseLum * tw;
      if (lum < 0.12) continue;

      ctx.fillStyle = `rgb(${(st.r * lum) | 0},${(st.g * lum) | 0},${(st.b * lum) | 0})`;
      ctx.fillText(st.ch, sc * cellW, sr * cellH);

      if (st.isFlare && tw > 0.72) {
        const armLum = lum * 0.48;
        ctx.fillStyle = `rgb(${(st.r * armLum) | 0},${(st.g * armLum) | 0},${(st.b * armLum) | 0})`;
        if (sc > 0 && charBuf[idx - 1] === 0) ctx.fillText('-', (sc - 1) * cellW, sr * cellH);
        if (sc + 1 < cols && charBuf[idx + 1] === 0) ctx.fillText('-', (sc + 1) * cellW, sr * cellH);
        if (sr > 0 && charBuf[idx - cols] === 0) ctx.fillText('|', sc * cellW, (sr - 1) * cellH);
        if (sr + 1 < rows && charBuf[idx + cols] === 0) ctx.fillText('|', sc * cellW, (sr + 1) * cellH);
      }
    }

    // 6. Bucketed ASCII character render (minimizes ctx.fillStyle changes)
    bucketHead.fill(-1);
    const totalCells = cols * rows;
    for (let idx = 0; idx < totalCells; idx++) {
      if (charBuf[idx] === 0) continue;
      const key = ((rBuf[idx] >> 3) << 10) | ((gBuf[idx] >> 3) << 5) | (bBuf[idx] >> 3);
      bucketNext[idx] = bucketHead[key];
      bucketHead[key] = idx;
    }

    for (let key = 0; key < BUCKET_COUNT; key++) {
      let idx = bucketHead[key];
      if (idx === -1) continue;

      let cssCol = colorStrCache[key];
      if (!cssCol) {
        const rr = ((key >> 10) & 31) * 8 + 4;
        const gg = ((key >> 5) & 31) * 8 + 4;
        const bb = (key & 31) * 8 + 4;
        cssCol = `rgb(${rr},${gg},${bb})`;
        colorStrCache[key] = cssCol;
      }
      ctx.fillStyle = cssCol;

      while (idx !== -1) {
        const r = (idx / cols) | 0;
        const c = idx - r * cols;
        ctx.fillText(CHAR_RAMP[charBuf[idx]], c * cellW, r * cellH);
        idx = bucketNext[idx];
      }
    }

    // 7. Update HUD text cleanly only when values change
    const bloomsText = `blooms open ${openCount}/${flowers.length}`;
    if (bloomsText !== lastBloomsText) {
      lastBloomsText = bloomsText;
      hudBloomsEl.textContent = bloomsText;
    }
    const petalsText = `petals falling ${fallingPetals.length}`;
    if (petalsText !== lastPetalsText) {
      lastPetalsText = petalsText;
      hudPetalsEl.textContent = petalsText;
    }
  }

  // ---------------------------------------------------------------------------
  // 8. Animation Loop & Controls
  // ---------------------------------------------------------------------------
  function loop(timestamp) {
    if (isPausedHidden) return;
    if (!lastTimestamp) lastTimestamp = timestamp;
    const rawDt = (timestamp - lastTimestamp) / 1000;
    lastTimestamp = timestamp;
    const dt = Math.min(rawDt, 0.08);

    renderFrame(dt);

    fpsFrameCount++;
    fpsAccum += rawDt;
    if (fpsAccum >= 0.5) {
      const fps = Math.round(fpsFrameCount / fpsAccum);
      hudFpsEl.textContent = `~${fps} fps`;
      fpsFrameCount = 0;
      fpsAccum = 0;
    }

    requestAnimationFrame(loop);
  }

  function replayBloom() {
    bloomClock = 0;
    fallingPetals.length = 0;
    petalSpawnTimer = 0;
    for (let i = 0; i < flowers.length; i++) {
      flowers[i].cachedOpen = -1;
    }
  }

  function toggleAutoSpin() {
    autoSpin = !autoSpin;
    btnSpin.textContent = autoSpin ? 'pause' : 'spin';
    btnSpin.classList.toggle('is-active', !autoSpin);
  }

  function toggleHud() {
    const hidden = document.body.classList.toggle('ui-hidden');
    btnHud.textContent = hidden ? 'ui' : 'hide ui';
  }

  function dismissHint() {
    if (hintDismissed) return;
    hintDismissed = true;
    hintEl.classList.add('fade-out');
  }

  function getPinchDistance() {
    const pts = Array.from(activePointers.values());
    if (pts.length < 2) return 0;
    return Math.hypot(pts[0].x - pts[1].x, pts[0].y - pts[1].y);
  }

  canvas.addEventListener('pointerdown', (e) => {
    canvas.setPointerCapture(e.pointerId);
    activePointers.set(e.pointerId, { x: e.clientX, y: e.clientY });
    dismissHint();

    if (activePointers.size === 1) {
      isDragging = true;
      lastDragX = e.clientX;
      lastDragY = e.clientY;
      canvas.classList.add('dragging');
    } else if (activePointers.size === 2) {
      isDragging = false;
      lastPinchDist = getPinchDistance();
    }
  });

  canvas.addEventListener('pointermove', (e) => {
    if (!activePointers.has(e.pointerId)) return;
    activePointers.set(e.pointerId, { x: e.clientX, y: e.clientY });

    if (activePointers.size === 1 && isDragging) {
      const dx = e.clientX - lastDragX;
      const dy = e.clientY - lastDragY;
      lastDragX = e.clientX;
      lastDragY = e.clientY;
      rotY += dx * 0.008;
      rotX = clamp(rotX + dy * 0.006, -0.85, 1.05);
    } else if (activePointers.size === 2) {
      const dist = getPinchDistance();
      if (lastPinchDist > 0 && dist > 0) {
        targetZoom = clamp(targetZoom * (dist / lastPinchDist), 0.65, 1.75);
      }
      lastPinchDist = dist;
    }
  });

  function endPointer(e) {
    activePointers.delete(e.pointerId);
    if (activePointers.size === 0) {
      isDragging = false;
      lastPinchDist = 0;
      canvas.classList.remove('dragging');
    } else if (activePointers.size === 1) {
      const remaining = Array.from(activePointers.values())[0];
      isDragging = true;
      lastDragX = remaining.x;
      lastDragY = remaining.y;
      lastPinchDist = 0;
    }
  }

  canvas.addEventListener('pointerup', endPointer);
  canvas.addEventListener('pointercancel', endPointer);

  canvas.addEventListener('wheel', (e) => {
    e.preventDefault();
    dismissHint();
    const factor = e.deltaY > 0 ? 0.92 : 1.08;
    targetZoom = clamp(targetZoom * factor, 0.65, 1.75);
  }, { passive: false });

  btnReplay.addEventListener('click', replayBloom);
  btnSpin.addEventListener('click', toggleAutoSpin);
  btnHud.addEventListener('click', toggleHud);

  window.addEventListener('keydown', (e) => {
    if (e.code === 'Space') {
      e.preventDefault();
      toggleAutoSpin();
    } else if (e.key === 'r' || e.key === 'R') {
      replayBloom();
    } else if (e.key === 'h' || e.key === 'H') {
      toggleHud();
    }
  });

  document.addEventListener('visibilitychange', () => {
    if (document.hidden) {
      isPausedHidden = true;
    } else {
      isPausedHidden = false;
      lastTimestamp = 0;
      requestAnimationFrame(loop);
    }
  });

  window.addEventListener('resize', handleResize);

  // Initialize everything
  initFlowers();
  buildStaticGeometry();
  initStars();
  handleResize();

  // Optional ?t= and ?ry= preview params for deterministic inspection
  const urlParams = new URLSearchParams(window.location.search);
  const previewRyParam = urlParams.get('ry');
  if (previewRyParam !== null && Number.isFinite(parseFloat(previewRyParam))) {
    rotY = parseFloat(previewRyParam);
  }
  const previewTParam = urlParams.get('t');
  if (previewTParam !== null) {
    const parsedT = parseFloat(previewTParam);
    if (Number.isFinite(parsedT) && parsedT >= 0) {
      bloomClock = parsedT;
      if (bloomClock >= 8) {
        for (let i = 0; i < flowers.length; i++) {
          const fl = flowers[i];
          const open = easeOutCubic((bloomClock - fl.startTime) / fl.duration);
          fl.cachedOpen = open;
          fl.localPoints = fl.type === 'tulip'
            ? generateTulipLocalPoints(fl.palette, open)
            : generateSunflowerLocalPoints(open);
        }
        for (let p = 0; p < 5; p++) {
          spawnFallingPetal();
          const fp = fallingPetals[fallingPetals.length - 1];
          if (fp) {
            fp.y -= 0.22 + p * 0.22;
            fp.age = 0.8 + p * 0.6;
          }
        }
      }
    }
  }

  setTimeout(dismissHint, 4500);
  requestAnimationFrame(loop);
})();
