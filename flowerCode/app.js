(function () {
  'use strict';

  const CHAR_RAMP = ' .,:;-~=+*#%@';
  const RAMP_LEN = CHAR_RAMP.length;
  const GOLDEN_ANGLE = 2.399963229728653;

  // Directional key light and cool rim/fill light
  const L1 = normalize3(0.45, 0.72, 0.65);
  const L2 = normalize3(-0.6, 0.25, -0.55);

  // Dominant blue tulip palettes (vivid saturated blues)
  const TULIP_PALETTES = [
    { name: 'deep-cobalt', base: [8, 26, 132], mid: [20, 76, 238], tip: [68, 152, 255] },
    { name: 'royal-sapphire', base: [10, 36, 158], mid: [26, 100, 252], tip: [90, 182, 255] },
    { name: 'luminous-azure', base: [12, 52, 178], mid: [32, 132, 255], tip: [115, 206, 255] },
    { name: 'electric-cerulean', base: [14, 68, 188], mid: [40, 154, 255], tip: [138, 220, 255] },
    { name: 'twilight-indigo', base: [20, 32, 152], mid: [52, 86, 245], tip: [108, 166, 255] }
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
  let rotY = 0.25;
  let rotX = 0.34;
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
  // 1. 3D Parametric Blue Tulip Generator
  // ---------------------------------------------------------------------------
  function tulipPetalPos(u, v, phiCenter, isOuter, open) {
    const openEff = open * (isOuter ? 1.0 : 0.82);
    const belly = Math.sin(Math.pow(u, 0.72) * Math.PI);
    const cupFlare = Math.pow(u, 1.32) * (0.05 + 0.165 * openEff);
    const budTaper = (1 - openEff * 0.8) * Math.pow(u, 1.65) * 0.088;
    const rBase = 0.022 + 0.125 * belly + cupFlare - budTaper + (isOuter ? 0.014 : 0);
    const spoonBulge = (1 - v * v) * 0.022 * belly;
    const tipCurl = u > 0.74 && openEff > 0.35
      ? Math.pow((u - 0.74) / 0.26, 2) * 0.03 * openEff
      : 0;
    const r = Math.max(0.008, rBase + spoonBulge + tipCurl);
    const h = u * (0.35 - 0.045 * openEff) + (isOuter ? 0 : 0.01 * u);
    const halfWidthAng = (0.58 - 0.15 * Math.pow(u, 1.45)) * (0.55 + 0.55 * belly);
    const phi = phiCenter + v * halfWidthAng;
    return [r * Math.cos(phi), h, r * Math.sin(phi)];
  }

  function generateTulipLocalPoints(palette, open) {
    const pts = [];
    const uSteps = 18;
    const vSteps = 9;

    // 6 overlapping tepals (3 inner, 3 outer)
    for (let k = 0; k < 6; k++) {
      const isOuter = k % 2 === 1;
      const phiCenter = (k * Math.PI) / 3;
      const du = 0.02;
      const dv = 0.06;

      for (let iu = 0; iu < uSteps; iu++) {
        const u = (iu + 0.5) / uSteps;
        let baseCol;
        if (u < 0.28) {
          baseCol = lerpColor(palette.base, palette.mid, u / 0.28);
        } else {
          baseCol = lerpColor(palette.mid, palette.tip, (u - 0.28) / 0.72);
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

          // Cross product oriented outward from tulip axis
          let nx = vy * uz - vz * uy;
          let ny = vz * ux - vx * uz;
          let nz = vx * uy - vy * ux;
          if (nx * p[0] + nz * p[2] < 0) {
            nx = -nx;
            ny = -ny;
            nz = -nz;
          }
          const n = normalize3(nx, ny, nz);

          // Subtle blue-tinted luminance on petal margins
          const marginGlow = Math.abs(v) * 16 * u;
          pts.push({
            x: p[0],
            y: p[1],
            z: p[2],
            nx: n[0],
            ny: n[1],
            nz: n[2],
            r: clamp(baseCol[0] + marginGlow * 0.25, 0, 255),
            g: clamp(baseCol[1] + marginGlow * 0.85, 0, 255),
            b: clamp(baseCol[2] + marginGlow * 1.4, 0, 255)
          });
        }
      }
    }

    // 6 inner stamens (subtle deep navy filaments with pale-gold pollen tips)
    for (let s = 0; s < 6; s++) {
      const ang = (s * Math.PI) / 3 + 0.26;
      const ca = Math.cos(ang);
      const sa = Math.sin(ang);
      const rad = 0.025 + 0.012 * open;
      for (let j = 0; j < 3; j++) {
        const f = (j + 1) / 3;
        const isTip = j === 2;
        pts.push({
          x: ca * rad * (0.7 + 0.4 * f),
          y: 0.04 + f * 0.11,
          z: sa * rad * (0.7 + 0.4 * f),
          nx: ca * 0.6,
          ny: 0.8,
          nz: sa * 0.6,
          r: isTip ? 245 : 35,
          g: isTip ? 215 : 65,
          b: isTip ? 115 : 155
        });
      }
    }

    // Tiny green calyx base joining stem
    for (let c = 0; c < 10; c++) {
      const ang = (c * Math.PI * 2) / 10;
      const ca = Math.cos(ang);
      const sa = Math.sin(ang);
      pts.push({
        x: ca * 0.024,
        y: -0.008,
        z: sa * 0.024,
        nx: ca,
        ny: -0.35,
        nz: sa,
        r: 36,
        g: 145,
        b: 76
      });
    }

    return pts;
  }

  // ---------------------------------------------------------------------------
  // 2. 3D Parametric Sunflower Generator
  // ---------------------------------------------------------------------------
  function generateSunflowerLocalPoints(open) {
    const pts = [];

    // Domed Fibonacci spiral seed disk (190 seeds)
    const numSeeds = 190;
    const diskRadius = 0.162;
    for (let i = 0; i < numSeeds; i++) {
      const t = (i + 0.5) / numSeeds;
      const rad = diskRadius * Math.sqrt(t);
      const theta = i * GOLDEN_ANGLE;
      const domeY = 0.055 * Math.cos(t * Math.PI * 0.45);
      const x = rad * Math.cos(theta);
      const z = rad * Math.sin(theta);

      // Dome surface normal
      const slope = 0.35 * Math.sqrt(t);
      const n = normalize3(Math.cos(theta) * slope, 1, Math.sin(theta) * slope);

      let col;
      if (t < 0.45) {
        col = lerpColor([62, 28, 8], [116, 56, 14], t / 0.45);
      } else if (t < 0.78) {
        col = lerpColor([116, 56, 14], [198, 124, 16], (t - 0.45) / 0.33);
      } else {
        col = lerpColor([198, 124, 16], [248, 188, 22], (t - 0.78) / 0.22);
      }

      pts.push({
        x,
        y: domeY,
        z,
        nx: n[0],
        ny: n[1],
        nz: n[2],
        r: col[0],
        g: col[1],
        b: col[2]
      });
    }

    // Double ring of 28 radiating golden ray petals
    const totalPetals = 28;
    const uSteps = 9;
    const vSteps = 4;

    for (let k = 0; k < totalPetals; k++) {
      const isOuter = k % 2 === 1;
      const phi = (k * Math.PI * 2) / totalPetals;
      const cp = Math.cos(phi);
      const sp = Math.sin(phi);
      // Tangent vector perpendicular to radial direction in XZ plane
      const tx = -sp;
      const tz = cp;

      const petalLen = isOuter ? 0.23 : 0.21;
      // Pitch goes from cupped upward bud (1.18 rad) to radiant open disk (~0.08 rad)
      const basePitch = lerp(1.18, isOuter ? 0.02 : 0.14, open);

      for (let iu = 0; iu < uSteps; iu++) {
        const u = (iu + 0.45) / uSteps;
        const pitch = basePitch - 0.16 * u * open;
        const distOut = diskRadius * 0.88 + u * petalLen * Math.cos(pitch);
        const yOff = 0.015 + u * petalLen * Math.sin(pitch) - 0.025 * u * u * open;
        const halfW = 0.038 * Math.sin(Math.pow(u, 0.65) * Math.PI);

        let col;
        if (u < 0.35) {
          col = lerpColor([228, 124, 10], [252, 198, 20], u / 0.35);
        } else {
          col = lerpColor([252, 198, 20], [255, 244, 162], (u - 0.35) / 0.65);
        }

        const n = normalize3(
          cp * Math.sin(pitch) * 0.4,
          Math.cos(pitch),
          sp * Math.sin(pitch) * 0.4
        );

        for (let iv = 0; iv < vSteps; iv++) {
          const v = -1 + (2 * iv) / (vSteps - 1);
          const x = distOut * cp + v * halfW * tx;
          const z = distOut * sp + v * halfW * tz;
          const y = yOff + (1 - Math.abs(v)) * 0.008;

          pts.push({
            x,
            y,
            z,
            nx: n[0],
            ny: n[1],
            nz: n[2],
            r: col[0],
            g: col[1],
            b: col[2]
          });
        }
      }
    }

    // 12 green involucre bracts tucked underneath the seed disk
    for (let b = 0; b < 12; b++) {
      const phi = (b * Math.PI * 2) / 12 + 0.12;
      const cp = Math.cos(phi);
      const sp = Math.sin(phi);
      for (let j = 0; j < 4; j++) {
        const f = (j + 1) / 4;
        const rad = 0.055 + f * 0.115;
        const y = -0.025 - (1 - f) * 0.025 + f * 0.012;
        pts.push({
          x: rad * cp,
          y,
          z: rad * sp,
          nx: cp * 0.5,
          ny: -0.85,
          nz: sp * 0.5,
          r: lerp(24, 58, f),
          g: lerp(110, 175, f),
          b: lerp(48, 86, f)
        });
      }
    }

    return pts;
  }

  // ---------------------------------------------------------------------------
  // 3. Bouquet Layout (16 Blue Tulips + 3 Sunflowers = 19 Flowers)
  // ---------------------------------------------------------------------------
  function initFlowers() {
    flowers.length = 0;
    const rng = createRng(20261124);

    // Build 19 flower specifications in 3 tiers
    const specs = [];

    // Tier 1: Crown (3 flowers: 1 sunflower front-left + 2 blue tulips)
    specs.push({
      type: 'sunflower',
      theta: -0.55,
      tilt: 0.16,
      y: 0.9,
      rad: 0.17,
      scale: 1.02,
      startTime: 0.75
    });
    specs.push({
      type: 'tulip',
      theta: 1.65,
      tilt: 0.22,
      y: 0.95,
      rad: 0.18,
      scale: 1.06,
      startTime: 0.25
    });
    specs.push({
      type: 'tulip',
      theta: 3.75,
      tilt: 0.22,
      y: 0.91,
      rad: 0.18,
      scale: 1.03,
      startTime: 0.5
    });

    // Tier 2: Middle ring (7 flowers: 5 blue tulips + 2 sunflowers)
    for (let i = 0; i < 7; i++) {
      const baseTheta = 0.28 + (i * Math.PI * 2) / 7;
      const isSunflower = i === 1 || i === 4;
      specs.push({
        type: isSunflower ? 'sunflower' : 'tulip',
        theta: baseTheta + (rng() - 0.5) * 0.14,
        tilt: 0.36 + rng() * 0.14,
        y: 0.62 + rng() * 0.12,
        rad: 0.42 + rng() * 0.06,
        scale: isSunflower ? 0.98 : 0.96 + rng() * 0.1,
        startTime: 1.1 + i * 0.36 + rng() * 0.2
      });
    }

    // Tier 3: Outer rim (9 blue tulips forming lush royal/sky blue halo)
    for (let i = 0; i < 9; i++) {
      const baseTheta = (i * Math.PI * 2) / 9 + 0.16;
      specs.push({
        type: 'tulip',
        theta: baseTheta + (rng() - 0.5) * 0.12,
        tilt: 0.6 + rng() * 0.16,
        y: 0.35 + rng() * 0.13,
        rad: 0.66 + rng() * 0.09,
        scale: 0.95 + rng() * 0.11,
        startTime: 2.3 + i * 0.3 + rng() * 0.25
      });
    }

    let tulipIdx = 0;
    for (let i = 0; i < specs.length; i++) {
      const sp = specs[i];
      const ct = Math.cos(sp.theta);
      const st = Math.sin(sp.theta);
      const pos = [sp.rad * ct, sp.y, sp.rad * st];
      // Stem points upward and flares outward according to tilt
      const sinTilt = Math.sin(sp.tilt);
      const cosTilt = Math.cos(sp.tilt);
      const dir = normalize3(sinTilt * ct, cosTilt, sinTilt * st);
      const basis = buildBasis(dir);

      const palette = sp.type === 'tulip'
        ? TULIP_PALETTES[tulipIdx % TULIP_PALETTES.length]
        : null;
      if (sp.type === 'tulip') tulipIdx++;

      flowers.push({
        id: i,
        type: sp.type,
        palette,
        pos,
        dir,
        basis,
        scale: sp.scale,
        startTime: sp.startTime,
        duration: 2.85 + rng() * 0.55,
        cachedOpen: -1,
        localPoints: []
      });
    }
  }

  // ---------------------------------------------------------------------------
  // 4. Static Bouquet Geometry (Stems, Leaves, Baby's Breath, Paper Wrap, Ribbon)
  // ---------------------------------------------------------------------------
  function buildStaticGeometry() {
    staticPoints.length = 0;
    const rng = createRng(88421);

    // A. Curved Green Stems passing through pinched waist (0, -0.44, 0)
    const waistY = -0.44;
    for (let i = 0; i < flowers.length; i++) {
      const fl = flowers[i];
      const top = fl.pos;
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
        -1.14 - rng() * 0.06,
        botRad * Math.sin(theta + 0.25)
      ];

      // Upper stem segment: quadratic Bezier from top -> mid
      const ctrlTop = [
        top[0] * 0.52 + mid[0] * 0.48,
        lerp(top[1], mid[1], 0.55),
        top[2] * 0.52 + mid[2] * 0.48
      ];
      for (let s = 0; s <= 26; s++) {
        const t = s / 26;
        const omt = 1 - t;
        const cx = omt * omt * top[0] + 2 * omt * t * ctrlTop[0] + t * t * mid[0];
        const cy = omt * omt * top[1] + 2 * omt * t * ctrlTop[1] + t * t * mid[1];
        const cz = omt * omt * top[2] + 2 * omt * t * ctrlTop[2] + t * t * mid[2];
        const rad = fl.type === 'sunflower' ? 0.018 : 0.015;
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
            g: lerp(155, 112, t),
            b: lerp(82, 58, t)
          });
        }
      }

      // Lower stem tail: mid -> bot
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
            b: 58
          });
        }
      }
    }

    // B. 16 Broad Sweeping Tulip Leaves around the bouquet
    for (let i = 0; i < 16; i++) {
      const phi = (i * Math.PI * 2) / 16 + (rng() - 0.5) * 0.18;
      const cp = Math.cos(phi);
      const sp = Math.sin(phi);
      const tx = -sp;
      const tz = cp;
      const leafLen = 0.72 + rng() * 0.22;
      const maxWidth = 0.082 + rng() * 0.022;
      const startY = -0.34 + rng() * 0.16;
      const startRad = 0.16 + rng() * 0.05;
      const archOut = 0.56 + rng() * 0.16;

      for (let iu = 0; iu < 20; iu++) {
        const u = iu / 19;
        const rad = startRad + archOut * Math.pow(u, 1.15);
        const y = startY + leafLen * (u * 0.92 - 0.28 * u * u);
        const w = maxWidth * Math.sin(Math.pow(u, 0.72) * Math.PI);
        const col = lerpColor([22, 102, 54], [74, 212, 130], u * 0.9);

        for (let iv = 0; iv < 5; iv++) {
          const v = -1 + (2 * iv) / 4;
          // V-shaped trough characteristic of tulip leaves
          const trough = Math.abs(v) * 0.022 * Math.sin(u * Math.PI);
          const px = rad * cp + v * w * tx;
          const pz = rad * sp + v * w * tz;
          const py = y + trough;
          const n = normalize3(cp * 0.75 + tx * v * 0.4, 0.55, sp * 0.75 + tz * v * 0.4);
          staticPoints.push({
            x: px,
            y: py,
            z: pz,
            nx: n[0],
            ny: n[1],
            nz: n[2],
            r: col[0],
            g: col[1],
            b: col[2]
          });
        }
      }
    }

    // C. ~52 Tiny Baby's Breath (Gypsophila) Clusters
    for (let i = 0; i < 52; i++) {
      const phi = rng() * Math.PI * 2;
      const rad = 0.36 + rng() * 0.34;
      const y = 0.24 + rng() * 0.68;
      const cx = rad * Math.cos(phi);
      const cz = rad * Math.sin(phi);
      for (let d = 0; d < 3; d++) {
        staticPoints.push({
          x: cx + (rng() - 0.5) * 0.045,
          y: y + (rng() - 0.5) * 0.045,
          z: cz + (rng() - 0.5) * 0.045,
          nx: Math.cos(phi) * 0.6,
          ny: 0.8,
          nz: Math.sin(phi) * 0.6,
          r: 228,
          g: 242,
          b: 255
        });
      }
    }

    // D. Layered Frosted White/Silver-Blue Wrapping Paper
    // Upper flared cone: high behind flowers (sin(theta) < 0 -> z < 0), dipped in front (z > 0)
    const uLayers = [
      { radScale: 1.0, phase: 0.0, yShift: 0.0, tint: [165, 182, 210] },
      { radScale: 1.06, phase: 0.42, yShift: -0.04, tint: [142, 160, 192] }
    ];

    for (let l = 0; l < uLayers.length; l++) {
      const layer = uLayers[l];
      const uSteps = 22;
      const tSteps = 64;
      for (let iu = 0; iu < uSteps; iu++) {
        const u = iu / (uSteps - 1);
        for (let it = 0; it < tSteps; it++) {
          const theta = (it / tSteps) * Math.PI * 2;
          // Front of bouquet faces +Z (theta around +PI/2). Back is -Z (theta around -PI/2).
          const backFactor = 0.5 - 0.5 * Math.sin(theta); // 1 at back (-Z), 0 at front (+Z)
          const topY = lerp(0.06, 1.08, backFactor) + layer.yShift;
          const pleat = 0.058 * Math.sin(theta * 7 + layer.phase) * Math.pow(u, 0.8);
          const rad = (0.20 + 0.78 * Math.pow(u, 0.86) + pleat) * layer.radScale;
          const y = lerp(waistY, topY, u) + 0.03 * Math.sin(theta * 7 + layer.phase) * u;

          // Leave tiny organic seam gap in front on outer layer for folded florist wrap look
          if (l === 1 && Math.sin(theta) > 0.88 && u > 0.25) continue;

          const col = lerpColor(
            [layer.tint[0] - 24, layer.tint[1] - 22, layer.tint[2] - 14],
            [224, 234, 248],
            u * 0.78 + 0.15 * backFactor
          );
          const pleatDeriv = 0.058 * 7 * Math.cos(theta * 7 + layer.phase);
          const n = normalize3(
            Math.cos(theta) + pleatDeriv * Math.sin(theta) * 0.45,
            -0.38,
            Math.sin(theta) - pleatDeriv * Math.cos(theta) * 0.45
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
            b: col[2]
          });
        }
      }
    }

    // Lower flared paper skirt from waist down to bottom
    const lowUSteps = 11;
    const lowTSteps = 38;
    for (let iu = 0; iu < lowUSteps; iu++) {
      const u = iu / (lowUSteps - 1);
      for (let it = 0; it < lowTSteps; it++) {
        const theta = (it / lowTSteps) * Math.PI * 2;
        const pleatWave = Math.sin(theta * 7 + 0.2);
        const pleat = 0.038 * pleatWave * u;
        const rad = 0.19 + 0.25 * Math.pow(u, 0.9) + pleat;
        const y = lerp(waistY, -1.16, u);
        const ridgeLift = pleatWave * 16 * u;
        const baseCol = lerpColor([205, 220, 242], [156, 174, 204], u);
        const n = normalize3(Math.cos(theta), 0.28, Math.sin(theta));
        staticPoints.push({
          x: rad * Math.cos(theta),
          y,
          z: rad * Math.sin(theta),
          nx: n[0],
          ny: n[1],
          nz: n[2],
          r: clamp(baseCol[0] + ridgeLift, 0, 255),
          g: clamp(baseCol[1] + ridgeLift, 0, 255),
          b: clamp(baseCol[2] + ridgeLift * 0.85, 0, 255)
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
    const targetCols = isMobile ? clamp(Math.round(viewW / 4.2), 82, 108) : clamp(Math.round(viewW / 6.8), 145, 210);
    fontSize = clamp(viewW / (targetCols * 0.6), isMobile ? 6.2 : 8.2, isMobile ? 8.8 : 11.2);

    ctx.font = `400 ${fontSize}px "JetBrains Mono", ui-monospace, SFMono-Regular, Menlo, Consolas, monospace`;
    ctx.textBaseline = 'top';

    const measured = ctx.measureText('M').width;
    cellW = Math.max(4.5, measured);
    cellH = Math.max(8, fontSize * 1.16);

    cols = Math.max(20, Math.floor(viewW / cellW));
    rows = Math.max(20, Math.floor(viewH / cellH));

    const total = cols * rows;
    zBuf = new Float32Array(total);
    charBuf = new Uint8Array(total);
    rBuf = new Uint8Array(total);
    gBuf = new Uint8Array(total);
    bBuf = new Uint8Array(total);
    bucketNext = new Int32Array(total);

    centerYRatio = isMobile ? 0.47 : 0.5;
    // Fit world height (~2.55 units) and width (~2.15 units) comfortably
    const usableH = viewH * (isMobile ? 0.74 : 0.82);
    const usableW = viewW * (isMobile ? 0.88 : 0.78);
    fovScale = Math.min(usableH / 2.55, usableW / 2.15);
  }

  // ---------------------------------------------------------------------------
  // 7. Projection & Shading Pipeline
  // ---------------------------------------------------------------------------
  function projectPoint(wx, wy, wz, wnx, wny, wnz, cr, cg, cb, sinY, cosY, sinX, cosX, swaySin, zoomScale, cxPx, cyPx) {
    // Gentle organic wind sway proportional to height above waist
    const swayAmt = Math.max(0, wy + 0.45) * 0.025 * swaySin;
    const sx = wx + swayAmt;

    // Rotate around Y then X
    const x1 = sx * cosY + wz * sinY;
    const z1 = -sx * sinY + wz * cosY;
    const y2 = wy * cosX - z1 * sinX;
    const z2 = wy * sinX + z1 * cosX;

    const depth = camDist - z2;
    if (depth <= 0.45) return;

    const persp = (camDist / depth) * zoomScale;
    const px = cxPx + x1 * persp * fovScale;
    const py = cyPx - y2 * persp * fovScale;

    const col = (px / cellW) | 0;
    const row = (py / cellH) | 0;
    if (col < 0 || col >= cols || row < 0 || row >= rows) return;

    const idx = row * cols + col;
    if (z2 <= zBuf[idx]) return;
    zBuf[idx] = z2;

    // Rotate normal
    const nx1 = wnx * cosY + wnz * sinY;
    const nz1 = -wnx * sinY + wnz * cosY;
    const ny2 = wny * cosX - nz1 * sinX;
    const nz2 = wny * sinX + nz1 * cosX;

    const dot1 = nx1 * L1[0] + ny2 * L1[1] + nz2 * L1[2];
    const diff1 = Math.max(0, dot1) * 0.76 + Math.abs(dot1) * 0.24;
    const dot2 = Math.max(0, nx1 * L2[0] + ny2 * L2[1] + nz2 * L2[2]);
    const rim = Math.pow(1 - Math.min(1, Math.abs(nz2)), 2) * 0.22;
    const depthBoost = clamp((z2 + 1.0) * 0.08, -0.06, 0.12);

    const shade = clamp(0.24 + 0.64 * diff1 + 0.16 * dot2 + rim + depthBoost, 0.12, 1.0);
    let charIdx = Math.round(shade * (RAMP_LEN - 1));
    if (charIdx < 1) charIdx = 1;
    charBuf[idx] = charIdx;

    const lum = 0.34 + 0.72 * shade;
    const sheen = shade > 0.88 ? (shade - 0.88) * 55 : 0;
    rBuf[idx] = clamp(cr * lum + sheen, 0, 255);
    gBuf[idx] = clamp(cg * lum + sheen, 0, 255);
    bBuf[idx] = clamp(cb * lum + sheen, 0, 255);
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
        p.r, p.g, p.b,
        sinY, cosY, sinX, cosX, swaySin, currentZoom, cxPx, cyPx
      );
    }

    // 2. Update & project all 19 flowers
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
          lp.r, lp.g, lp.b,
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
          fp.col[0] * fade, fp.col[1] * fade, fp.col[2] * fade,
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

  // Optional ?t= preview param for deterministic full-bloom inspection
  const previewTParam = new URLSearchParams(window.location.search).get('t');
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
