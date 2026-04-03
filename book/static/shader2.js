const DEFAULTS = {
  webglUnsupportedTextColor: "#fff",
  coreColor: "#a6ccff",
  midColor: "#5973f2",
  edgeColor: "#8c40d9",
  farColor: "#FFF",
  starColor: "#b3ccff",
  backgroundColor: "#f2eee9",
  viewScale: 2.5,
  tiltYOffset: 0.0,
  tiltYScale: 1,
  armCount: 3,
  rotationSpeed: 1.4,
  showStars: false,
  hoverRadius: 0.2,
  hoverInnerRadius: 0.01,
  hoverRainbowSpeed: 0.1,
  hoverStrength: 0.95,
  hoverMode: 0,
  hoverModeBlendIn: 0.28,
  hoverModeBlendOut: 0.96,
  hoverColors: [
    "#ff26cc",
    "#ff4040",
    "#ffa626",
    "#fff233",
    "#a6f240",
    "#33d973",
    "#33ccff",
    "#6673ff",
  ],
  mobileBreakpoint: 900,
  desktop: {
    dprCap: 2,
    fbScale: 1,
    fbmOctaves: 6,
    asciiCell: { width: 8, height: 12 },
    timeScale: 1,
  },
  mobile: {
    dprCap: 1,
    fbScale: 0.6,
    fbmOctaves: 4,
    asciiCell: { width: 8, height: 12 },
    timeScale: 0.2,
  },
};

function hexToVec3(hex) {
  const normalized = hex.replace("#", "");
  const value =
    normalized.length === 3
      ? normalized
          .split("")
          .map((char) => char + char)
          .join("")
      : normalized;

  const channels = [0, 2, 4].map((index) =>
    (parseInt(value.slice(index, index + 2), 16) / 255).toFixed(3),
  );

  return `vec3(${channels.join(", ")})`;
}

function getQualityProfile(cfg) {
  const isTouch = "ontouchstart" in window || navigator.maxTouchPoints > 0;
  const isMobileViewport = window.innerWidth <= cfg.mobileBreakpoint;
  const mobile = isTouch || isMobileViewport;
  const p = mobile ? cfg.mobile : cfg.desktop;

  return {
    key: mobile ? "mobile" : "desktop",
    dprCap: p.dprCap,
    framebufferScale: p.fbScale,
    fbmOctaves: p.fbmOctaves,
    asciiCell: p.asciiCell,
    timeScale: p.timeScale,
    hoverEnabled: !mobile,
  };
}

function createGalaxyFs(quality, cfg) {
  const hc = cfg.hoverColors;
  return `#version 300 es
precision highp float;
in vec2 vUv;
out vec4 fragColor;
uniform float uTime;
uniform vec2 uRes;
uniform vec2 uMouse;

vec3 hsv2rgb(vec3 c) {
  vec3 p = abs(fract(c.xxx + vec3(0.0, 2.0/3.0, 1.0/3.0)) * 6.0 - 3.0);
  return c.z * mix(vec3(1.0), clamp(p - 1.0, 0.0, 1.0), c.y);
}

vec3 hoverRainbow(float t) {
  t = fract(t);
  vec3 c0 = ${hexToVec3(hc[0])};
  vec3 c1 = ${hexToVec3(hc[1])};
  vec3 c2 = ${hexToVec3(hc[2])};
  vec3 c3 = ${hexToVec3(hc[3])};
  vec3 c4 = ${hexToVec3(hc[4])};
  vec3 c5 = ${hexToVec3(hc[5])};
  vec3 c6 = ${hexToVec3(hc[6])};
  vec3 c7 = ${hexToVec3(hc[7])};

  if (t < 0.14) return mix(c0, c1, smoothstep(0.0, 0.14, t));
  if (t < 0.26) return mix(c1, c2, smoothstep(0.14, 0.26, t));
  if (t < 0.42) return mix(c2, c3, smoothstep(0.26, 0.42, t));
  if (t < 0.6) return mix(c3, c4, smoothstep(0.42, 0.6, t));
  if (t < 0.76) return mix(c4, c5, smoothstep(0.6, 0.76, t));
  if (t < 0.88) return mix(c5, c6, smoothstep(0.76, 0.88, t));
  return mix(c6, c7, smoothstep(0.88, 1.0, t));
}

vec3 mod289(vec3 x) { return x - floor(x * (1.0/289.0)) * 289.0; }
vec2 mod289(vec2 x) { return x - floor(x * (1.0/289.0)) * 289.0; }
vec3 permute(vec3 x) { return mod289(((x*34.0)+1.0)*x); }

float snoise(vec2 v) {
  const vec4 C = vec4(0.211324865405187, 0.366025403784439,
                     -0.577350269189626, 0.024390243902439);
  vec2 i = floor(v + dot(v, C.yy));
  vec2 x0 = v - i + dot(i, C.xx);
  vec2 i1 = (x0.x > x0.y) ? vec2(1.0, 0.0) : vec2(0.0, 1.0);
  vec4 x12 = x0.xyxy + C.xxzz;
  x12.xy -= i1;
  i = mod289(i);
  vec3 p = permute(permute(i.y + vec3(0.0, i1.y, 1.0)) + i.x + vec3(0.0, i1.x, 1.0));
  vec3 m = max(0.5 - vec3(dot(x0,x0), dot(x12.xy,x12.xy), dot(x12.zw,x12.zw)), 0.0);
  m = m*m; m = m*m;
  vec3 x = 2.0 * fract(p * C.www) - 1.0;
  vec3 h = abs(x) - 0.5;
  vec3 ox = floor(x + 0.5);
  vec3 a0 = x - ox;
  m *= 1.79284291400159 - 0.85373472095314 * (a0*a0 + h*h);
  vec3 g;
  g.x = a0.x * x0.x + h.x * x0.y;
  g.yz = a0.yz * x12.xz + h.yz * x12.yw;
  return 130.0 * dot(m, g);
}

float fbm(vec2 p) {
  float f = 0.0, a = 0.5;
  for (int i = 0; i < ${quality.fbmOctaves}; i++) {
    f += a * snoise(p);
    p *= 2.1; a *= 0.48;
  }
  return f;
}

void main() {
  vec2 uv = (gl_FragCoord.xy - 0.5 * uRes) / min(uRes.x, uRes.y);
  float t = uTime * ${quality.timeScale.toFixed(3)} * 0.08;

  vec2 viewUv = uv;
  viewUv *= ${cfg.viewScale.toFixed(3)};
  viewUv.y =
    (viewUv.y + ${cfg.tiltYOffset.toFixed(3)}) * ${cfg.tiltYScale.toFixed(3)};

  float angle = t * ${cfg.rotationSpeed.toFixed(3)};
  float ca = cos(angle), sa = sin(angle);
  viewUv = mat2(ca, -sa, sa, ca) * viewUv;

  float r = length(viewUv);
  float theta = atan(viewUv.y, viewUv.x);

  float armFreq = ${Math.max(0.5, cfg.armCount / 2).toFixed(1)};
  float spiral1 = sin(theta * armFreq - r * 8.0 + t * 0.5);
  float spiral2 = sin(theta * armFreq - r * 8.0 + t * 0.5 + 3.14159);
  float arms = max(spiral1, spiral2);
  arms = smoothstep(0.0, 1.0, arms);

  vec2 p1 = viewUv * 3.0 + vec2(t * 0.1, t * 0.07);
  vec2 p2 = viewUv * 5.0 - vec2(t * 0.05, t * 0.12);
  float n1 = fbm(p1);
  float n2 = fbm(p2 + n1 * 0.5);
  float nebula = n1 * 0.6 + n2 * 0.4;

  float core = exp(-r * r * 12.0);
  float disk = exp(-r * r * 2.5);
  float glow = core * 0.85 + disk * arms * 0.7 + nebula * disk * 0.5;

  float pulse = 1.0 + 0.15 * sin(t * 1.2) + 0.1 * sin(t * 0.7 + 1.5);
  glow *= pulse;

  float stars = 0.0;
  ${
    cfg.showStars
      ? `for (int i = 0; i < 3; i++) {
    vec2 sp = uv * (15.0 + float(i) * 20.0);
    vec2 id = floor(sp);
    vec2 f = fract(sp) - 0.5;
    float h = fract(sin(dot(id, vec2(127.1, 311.7))) * 43758.5453);
    float h2 = fract(sin(dot(id, vec2(269.5, 183.3))) * 43758.5453);
    vec2 off = vec2(h, h2) - 0.5;
    float d = length(f - off * 0.6);
    float brightness = h * h * h;
    float twinkle = 0.7 + 0.3 * sin(t * 3.0 * h + h2 * 6.28);
    stars += smoothstep(0.08, 0.0, d) * brightness * twinkle * 0.4;
  }`
      : ""
  }

  vec3 colCore = ${hexToVec3(cfg.coreColor)};
  vec3 colMid = ${hexToVec3(cfg.midColor)};
  vec3 colEdge = ${hexToVec3(cfg.edgeColor)};
  vec3 colFar = ${hexToVec3(cfg.farColor)};

  vec3 col = mix(colFar, colEdge, smoothstep(0.8, 0.4, r));
  col = mix(col, colMid, smoothstep(0.5, 0.15, r));
  col = mix(col, colCore, smoothstep(0.2, 0.0, r));
  col *= glow;
  col += stars * ${hexToVec3(cfg.starColor)};

  ${
    quality.hoverEnabled
      ? `vec2 mouseNorm = (uMouse - 0.5 * uRes) / min(uRes.x, uRes.y);
  float mouseDist = length(uv - mouseNorm);
  float hoverRadius = ${cfg.hoverRadius.toFixed(3)};
  float hoverMask = 1.0 - smoothstep(${cfg.hoverInnerRadius.toFixed(3)}, hoverRadius, mouseDist);
  if (uMouse.x >= 0.0) {
    vec2 hoverDelta = uv - mouseNorm;
    float diagonal = dot(hoverDelta, normalize(vec2(0.86, 0.5)));
    float gradient = diagonal * 0.16 + 0.035 * sin(diagonal * 6.0 + uTime * 0.7);
    float hue = fract(uTime * ${cfg.hoverRainbowSpeed.toFixed(3)} + gradient);
    vec3 rainbow = hoverRainbow(hue);
    float brightness = dot(col, vec3(0.299, 0.587, 0.114));
    float galaxyMask = smoothstep(0.04, 0.8, brightness);
    vec3 tinted = mix(col, rainbow, ${cfg.hoverStrength.toFixed(3)});
    col = mix(col, tinted, hoverMask * galaxyMask);
  }`
      : ""
  }

  fragColor = vec4(col, 1.0);
}`;
}

function createAsciiFs(quality, cfg) {
  const hc = cfg.hoverColors;
  return `#version 300 es
precision highp float;
in vec2 vUv;
out vec4 fragColor;
uniform sampler2D uTex;
uniform vec2 uRes;
uniform float uTime;
uniform int uCharMode;
uniform vec2 uMouse;

vec3 hsv2rgb(vec3 c) {
  vec3 p = abs(fract(c.xxx + vec3(0.0, 2.0/3.0, 1.0/3.0)) * 6.0 - 3.0);
  return c.z * mix(vec3(1.0), clamp(p - 1.0, 0.0, 1.0), c.y);
}

vec3 hoverRainbow(float t) {
  t = fract(t);
  vec3 c0 = ${hexToVec3(hc[0])};
  vec3 c1 = ${hexToVec3(hc[1])};
  vec3 c2 = ${hexToVec3(hc[2])};
  vec3 c3 = ${hexToVec3(hc[3])};
  vec3 c4 = ${hexToVec3(hc[4])};
  vec3 c5 = ${hexToVec3(hc[5])};
  vec3 c6 = ${hexToVec3(hc[6])};
  vec3 c7 = ${hexToVec3(hc[7])};

  if (t < 0.14) return mix(c0, c1, smoothstep(0.0, 0.14, t));
  if (t < 0.26) return mix(c1, c2, smoothstep(0.14, 0.26, t));
  if (t < 0.42) return mix(c2, c3, smoothstep(0.26, 0.42, t));
  if (t < 0.6) return mix(c3, c4, smoothstep(0.42, 0.6, t));
  if (t < 0.76) return mix(c4, c5, smoothstep(0.6, 0.76, t));
  if (t < 0.88) return mix(c5, c6, smoothstep(0.76, 0.88, t));
  return mix(c6, c7, smoothstep(0.88, 1.0, t));
}

float getCharPixel(int mode, int charIdx, int px, int py) {
  if (mode == 0) {
    if (charIdx == 0) return 0.0;
    if (charIdx == 1) return ((px + py) % 5 == 0) ? 1.0 : 0.0;
    if (charIdx == 2) return ((px + py) % 4 <= 1) ? 1.0 : 0.0;
    if (charIdx == 3) return ((px + py) % 3 <= 1) ? 1.0 : 0.0;
    return 1.0;
  }
  if (mode == 1) {
    if (charIdx == 0) return 0.0;
    if (charIdx == 1) return (px == 2 && py == 5) ? 1.0 : 0.0;
    if (charIdx == 2) return ((px == 2 && py == 2) || (px == 2 && py == 4)) ? 1.0 : 0.0;
    if (charIdx == 3) return (py == 3 && px >= 1 && px <= 3) ? 1.0 : 0.0;
    if (charIdx == 4) return ((py == 2 || py == 4) && px >= 1 && px <= 3) ? 1.0 : 0.0;
    if (charIdx == 5) return ((px == 2 && py >= 1 && py <= 5) || (py == 3 && px >= 1 && px <= 3)) ? 1.0 : 0.0;
    if (charIdx == 6) {
      if (px == 2 && py >= 1 && py <= 5) return 1.0;
      if (py == 3 && px >= 1 && px <= 3) return 1.0;
      if (abs(px - 2) == abs(py - 3) && abs(px - 2) <= 1) return 1.0;
      return 0.0;
    }
    if (charIdx == 7) return ((px == 1 || px == 3) || (py == 2 || py == 4)) ? 1.0 : 0.0;
    return ((px + py) % 2 == 0 || px == 0 || px == 4 || py == 0 || py == 6) ? 1.0 : 0.0;
  }
  if (mode == 2) {
    if (charIdx == 0) return 0.0;
    if (charIdx == 1) return (px == 2 && py == 3) ? 1.0 : 0.0;
    if (charIdx == 2) return (abs(px - 2) + abs(py - 3) <= 1) ? 1.0 : 0.0;
    float dx = float(px) - 2.0, dy = float(py) - 3.0;
    return (dx*dx + dy*dy <= 2.5) ? 1.0 : 0.0;
  }
  if (mode == 3) {
    if (charIdx == 0) return 0.0;
    if (charIdx == 1) return (px == 2 && py == 3) ? 1.0 : 0.0;
    if (charIdx == 2) return (py == 3 && px >= 1 && px <= 3) ? 1.0 : 0.0;
    if (charIdx == 3) {
      int ex = py * 4 / 6;
      return (px == ex) ? 1.0 : 0.0;
    }
    if (charIdx == 4) return (px == 2) ? 1.0 : 0.0;
    if (charIdx == 5) {
      int ex = 4 - py * 4 / 6;
      return (px == ex) ? 1.0 : 0.0;
    }
    if (charIdx == 6) {
      if (py <= 4) {
        int left = py * 2 / 5;
        int right = 4 - py * 2 / 5;
        return (px == left || px == right) ? 1.0 : 0.0;
      }
      return (px == 2) ? 1.0 : 0.0;
    }
    return ((px + py) % 2 == 0) ? 1.0 : 0.0;
  }
  return 0.0;
}

int getCharIndex(int mode, float b) {
  if (mode == 0) {
    if (b < 0.04) return 0;
    if (b < 0.15) return 1;
    if (b < 0.35) return 2;
    if (b < 0.6) return 3;
    return 4;
  }
  if (mode == 1) {
    if (b < 0.03) return 0;
    if (b < 0.08) return 1;
    if (b < 0.15) return 2;
    if (b < 0.22) return 3;
    if (b < 0.35) return 4;
    if (b < 0.5) return 5;
    if (b < 0.65) return 6;
    if (b < 0.8) return 7;
    return 8;
  }
  if (mode == 2) {
    if (b < 0.1) return 0;
    if (b < 0.3) return 1;
    if (b < 0.55) return 2;
    return 3;
  }
  if (b < 0.03) return 0;
  if (b < 0.08) return 1;
  if (b < 0.18) return 2;
  if (b < 0.3) return 3;
  if (b < 0.45) return 4;
  if (b < 0.6) return 5;
  if (b < 0.75) return 6;
  return 7;
}

void main() {
  float cellW = ${quality.asciiCell.width.toFixed(1)};
  float cellH = ${quality.asciiCell.height.toFixed(1)};
  vec2 pixel = vUv * uRes;
  vec2 cell = floor(pixel / vec2(cellW, cellH));
  vec2 cellFract = fract(pixel / vec2(cellW, cellH));

  int px = int(cellFract.x * 5.0);
  int py = int(cellFract.y * 7.0);

  vec2 sampleUv = (cell * vec2(cellW, cellH) + vec2(cellW, cellH) * 0.5) / uRes;
  vec4 color = texture(uTex, sampleUv);
  float brightness = dot(color.rgb, vec3(0.299, 0.587, 0.114));

  int activeMode = uCharMode;
  float slashBlend = 0.0;
  if (uMouse.x >= 0.0 && uCharMode == 0) {
    vec2 uv = (pixel - 0.5 * uRes) / min(uRes.x, uRes.y);
    vec2 mouseNorm = (uMouse - 0.5 * uRes) / min(uRes.x, uRes.y);
    float mouseDist = length(uv - mouseNorm);
    float hoverMask = 1.0 - smoothstep(${cfg.hoverInnerRadius.toFixed(3)}, ${cfg.hoverRadius.toFixed(3)}, mouseDist);
    slashBlend = smoothstep(${cfg.hoverModeBlendIn.toFixed(3)}, ${cfg.hoverModeBlendOut.toFixed(3)}, hoverMask);
    slashBlend *= slashBlend;
  }

  int charIdx = getCharIndex(activeMode, brightness);
  float on = getCharPixel(activeMode, charIdx, px, py);
  if (uCharMode == 0 && slashBlend > 0.0) {
    int slashCharIdx = getCharIndex(${cfg.hoverMode}, brightness);
    float slashOn = getCharPixel(${cfg.hoverMode}, slashCharIdx, px, py);
    on = mix(on, slashOn, slashBlend);
  }

  vec3 colCore = ${hexToVec3(cfg.coreColor)};
  vec3 colMid = ${hexToVec3(cfg.midColor)};
  vec3 colEdge = ${hexToVec3(cfg.edgeColor)};
  vec3 colFar = ${hexToVec3(cfg.farColor)};
  vec3 paletteTint = mix(colFar, colEdge, smoothstep(0.01, 0.16, brightness));
  paletteTint = mix(paletteTint, colMid, smoothstep(0.12, 0.42, brightness));
  paletteTint = mix(paletteTint, colCore, smoothstep(0.4, 0.85, brightness));
  float intensity = pow(smoothstep(0.01, 0.8, brightness), 0.75);
  float outerBoost = 1.0 - smoothstep(0.18, 0.45, brightness);
  vec3 lowEndTint = mix(colFar, colEdge, smoothstep(0.0, 0.12, brightness));
  vec3 tint = mix(lowEndTint, paletteTint, smoothstep(0.06, 0.3, brightness));
  tint *= 0.5 + intensity * 1.0 + outerBoost * 0.2;
  if (uMouse.x >= 0.0) {
    vec2 uv = (pixel - 0.5 * uRes) / min(uRes.x, uRes.y);
    vec2 mouseNorm = (uMouse - 0.5 * uRes) / min(uRes.x, uRes.y);
    float mouseDist = length(uv - mouseNorm);
    float hoverMask = 1.0 - smoothstep(${cfg.hoverInnerRadius.toFixed(3)}, ${cfg.hoverRadius.toFixed(3)}, mouseDist);
    vec2 hoverDelta = uv - mouseNorm;
    float diagonal = dot(hoverDelta, normalize(vec2(0.86, 0.5)));
    float gradient = diagonal * 0.18 + 0.04 * sin(diagonal * 6.5 + uTime * 0.8);
    float hue = fract(uTime * ${cfg.hoverRainbowSpeed.toFixed(3)} + gradient);
    vec3 rainbow = hoverRainbow(hue);
    float hoverStrength = hoverMask * (0.45 + 0.55 * on);
    tint = mix(tint, rainbow, hoverStrength);
  }
  vec3 result = tint * on;

  result *= 0.92 + 0.08 * sin(pixel.y * 1.5);

  fragColor = vec4(result, on);
}`;
}

export function initGalaxy(canvas, opts = {}) {
  const cfg = {
    ...DEFAULTS,
    ...opts,
    desktop: { ...DEFAULTS.desktop, ...opts.desktop },
    mobile: { ...DEFAULTS.mobile, ...opts.mobile },
    hoverColors: opts.hoverColors || DEFAULTS.hoverColors,
  };
  const gl = canvas.getContext("webgl2", { antialias: false, alpha: true });
  if (!gl) {
    canvas.parentElement.innerHTML = `<p style="color:${cfg.webglUnsupportedTextColor};padding:2em">WebGL 2 not supported</p>`;
    return;
  }
  canvas.style.background = cfg.backgroundColor;

  let charMode = cfg.initMode || 0;
  let quality = getQualityProfile(cfg);
  let galaxyProg;
  let asciiProg;
  let gTimeLoc;
  let gResLoc;
  let gMouseLoc;
  let aTexLoc;
  let aTimeLoc;
  let aResLoc;
  let aModeLoc;
  let aMouseLoc;
  let fbWidth = 0;
  let fbHeight = 0;

  function resize() {
    quality = getQualityProfile(cfg);
    const dpr = Math.min(window.devicePixelRatio || 1, quality.dprCap);
    canvas.width = canvas.clientWidth * dpr;
    canvas.height = canvas.clientHeight * dpr;
    fbWidth = Math.max(1, Math.round(canvas.width * quality.framebufferScale));
    fbHeight = Math.max(
      1,
      Math.round(canvas.height * quality.framebufferScale),
    );
  }

  function createShader(src, type) {
    const s = gl.createShader(type);
    gl.shaderSource(s, src);
    gl.compileShader(s);
    if (!gl.getShaderParameter(s, gl.COMPILE_STATUS))
      console.error(gl.getShaderInfoLog(s));
    return s;
  }
  function createProgram(vs, fs) {
    const p = gl.createProgram();
    gl.attachShader(p, createShader(vs, gl.VERTEX_SHADER));
    gl.attachShader(p, createShader(fs, gl.FRAGMENT_SHADER));
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS))
      console.error(gl.getProgramInfoLog(p));
    return p;
  }

  function rebuildPrograms() {
    if (galaxyProg) gl.deleteProgram(galaxyProg);
    if (asciiProg) gl.deleteProgram(asciiProg);

    galaxyProg = createProgram(quadVs, createGalaxyFs(quality, cfg));
    gTimeLoc = gl.getUniformLocation(galaxyProg, "uTime");
    gResLoc = gl.getUniformLocation(galaxyProg, "uRes");
    gMouseLoc = gl.getUniformLocation(galaxyProg, "uMouse");

    asciiProg = createProgram(quadVs, createAsciiFs(quality, cfg));
    aTexLoc = gl.getUniformLocation(asciiProg, "uTex");
    aTimeLoc = gl.getUniformLocation(asciiProg, "uTime");
    aResLoc = gl.getUniformLocation(asciiProg, "uRes");
    aModeLoc = gl.getUniformLocation(asciiProg, "uCharMode");
    aMouseLoc = gl.getUniformLocation(asciiProg, "uMouse");
  }

  const quadVs = `#version 300 es
in vec2 pos;
out vec2 vUv;
void main() {
  vUv = pos * 0.5 + 0.5;
  gl_Position = vec4(pos, 0.0, 1.0);
}`;

  const quadBuf = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, quadBuf);
  gl.bufferData(
    gl.ARRAY_BUFFER,
    new Float32Array([-1, -1, 1, -1, -1, 1, 1, 1]),
    gl.STATIC_DRAW,
  );

  let mouseNormX = -1,
    mouseNormY = -1;
  canvas.addEventListener("mousemove", (e) => {
    const rect = canvas.getBoundingClientRect();
    mouseNormX = (e.clientX - rect.left) / rect.width;
    mouseNormY = (rect.bottom - e.clientY) / rect.height;
  });
  canvas.addEventListener("mouseleave", () => {
    mouseNormX = -1;
    mouseNormY = -1;
  });

  let fb, fbTex;
  function createFB() {
    if (fb) {
      gl.deleteFramebuffer(fb);
      gl.deleteTexture(fbTex);
    }
    fb = gl.createFramebuffer();
    fbTex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, fbTex);
    gl.texImage2D(
      gl.TEXTURE_2D,
      0,
      gl.RGBA8,
      fbWidth,
      fbHeight,
      0,
      gl.RGBA,
      gl.UNSIGNED_BYTE,
      null,
    );
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    gl.bindFramebuffer(gl.FRAMEBUFFER, fb);
    gl.framebufferTexture2D(
      gl.FRAMEBUFFER,
      gl.COLOR_ATTACHMENT0,
      gl.TEXTURE_2D,
      fbTex,
      0,
    );
    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
  }

  function bindQuad(prog) {
    const loc = gl.getAttribLocation(prog, "pos");
    gl.bindBuffer(gl.ARRAY_BUFFER, quadBuf);
    gl.enableVertexAttribArray(loc);
    gl.vertexAttribPointer(loc, 2, gl.FLOAT, false, 0, 0);
  }

  resize();
  rebuildPrograms();
  createFB();
  window.addEventListener("resize", () => {
    const prevKey = quality.key;
    resize();
    if (quality.key !== prevKey) rebuildPrograms();
    createFB();
  });

  function render(t) {
    t *= 0.001;

    gl.bindFramebuffer(gl.FRAMEBUFFER, fb);
    gl.viewport(0, 0, fbWidth, fbHeight);
    gl.useProgram(galaxyProg);
    bindQuad(galaxyProg);
    gl.uniform1f(gTimeLoc, t);
    gl.uniform2f(gResLoc, fbWidth, fbHeight);
    gl.uniform2f(
      gMouseLoc,
      mouseNormX >= 0 ? mouseNormX * fbWidth : -1,
      mouseNormY >= 0 ? mouseNormY * fbHeight : -1,
    );
    gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);

    gl.bindFramebuffer(gl.FRAMEBUFFER, null);
    gl.viewport(0, 0, canvas.width, canvas.height);
    gl.useProgram(asciiProg);
    bindQuad(asciiProg);
    gl.activeTexture(gl.TEXTURE0);
    gl.bindTexture(gl.TEXTURE_2D, fbTex);
    gl.uniform1i(aTexLoc, 0);
    gl.uniform1f(aTimeLoc, t);
    gl.uniform2f(aResLoc, canvas.width, canvas.height);
    gl.uniform1i(aModeLoc, charMode);
    gl.uniform2f(
      aMouseLoc,
      mouseNormX >= 0 ? mouseNormX * canvas.width : -1,
      mouseNormY >= 0 ? mouseNormY * canvas.height : -1,
    );
    gl.drawArrays(gl.TRIANGLE_STRIP, 0, 4);

    requestAnimationFrame(render);
  }
  requestAnimationFrame(render);

  return {
    setMode(m) {
      charMode = m;
    },
  };
}
