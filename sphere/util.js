const angleCount = 24;
const proceedCount = 4;
const projective = false;

let scrW = 0, scrH = 0;
let refresh = _=>_;
let compile = _=>_;
let setBounds = _=>_;
let draw = _=>_;
let collide = _=>_;
let collideBound = _=>_;
let mouseContact = _=>_;
let drawObject = _=>_;
let passObject = _=>_;

let boundary = _=>_;
let boundGradient = _=>_;

function polygonNormal(a,b,c){
  const d1x = c.wx-a.wx;
  const d1y = c.wy-a.wy;
  const d1z = c.wz-a.wz;
  const d2x = c.wx-b.wx;
  const d2y = c.wy-b.wy;
  const d2z = c.wz-b.wz;
  const rx = d1y*d2z-d2y*d1z;
  const ry = d1z*d2x-d2z*d1x;
  const rz = d1x*d2y-d2x*d1y;
  const rl = Math.sqrt(rx*rx+ry*ry+rz*rz);
  return {
    x:rx/rl,
    y:ry/rl,
    z:rz/rl
  };
}
function lineDistRatio(l0,l1,l2,p){
  const d1x = l0.wx-l1.wx;
  const d1y = l0.wy-l1.wy;
  const d1z = l0.wz-l1.wz;
  const d2x = l2.wx-l1.wx;
  const d2y = l2.wy-l1.wy;
  const d2z = l2.wz-l1.wz;
  const d  = d1x*d2x+d1y*d2y+d1z*d2z;
  const dl = d2x*d2x+d2y*d2y+d2z*d2z;
  const t = d / dl;
  const nx = l1.wx+t*d2x-l0.wx;
  const ny = l1.wy+t*d2y-l0.wy;
  const nz = l1.wz+t*d2z-l0.wz;
  const oDist =
    (l0.wx-l1.wx)*nx +
    (l0.wy-l1.wy)*ny +
    (l0.wz-l1.wz)*nz;
  const pDist =
    (p.x-l1.wx)*nx +
    (p.y-l1.wy)*ny +
    (p.z-l1.wz)*nz;
  return pDist / oDist;
}
function lineDist(l1,l2,p){
  const d1x = p.wx-l1.wx;
  const d1y = p.wy-l1.wy;
  const d1z = p.wz-l1.wz;
  const d2x = l2.wx-l1.wx;
  const d2y = l2.wy-l1.wy;
  const d2z = l2.wz-l1.wz;
  const d = d1x*d2x+d1y*d2y+d1z*d2z;
  const dl = d2x*d2x+d2y*d2y+d2z*d2z;
  const t = d / dl;
  const hx = l1.wx+t*d2x;
  const hy = l1.wy+t*d2y;
  const hz = l1.wz+t*d2z;
  const nx = hx-p.wx;
  const ny = hy-p.wy;
  const nz = hz-p.wz;
  const nl = Math.sqrt(nx*nx+ny*ny+nz*nz);
  const pDist =
    (p.wx-l1.wx)*nx +
    (p.wy-l1.wy)*ny +
    (p.wz-l1.wz)*nz;
  return {
    d:-pDist / nl,
    wx:hx,
    wy:hy,
    wz:hz,
    lx:l1.lx+t*(l2.lx-l1.lx),
    ly:l1.ly+t*(l2.ly-l1.ly),
    dx:l1.dx+t*(l2.dx-l1.dx),
    dy:l1.dy+t*(l2.dy-l1.dy),
    dz:l1.dz+t*(l2.dz-l1.dz)
  };
}
function inPolygon(o,s){
  const wp1 = s[0];
  const wp2 = s[1];
  const wp3 = s[2];
  const n = polygonNormal(wp1,wp2,wp3);
  const dp =
    (o.wx-wp1.wx)*n.x +
    (o.wy-wp1.wy)*n.y +
    (o.wz-wp1.wz)*n.z;
  if(Math.abs(dp) >= 0.1)return false;
  const p = {
    x:o.wx - n.x*dp,
    y:o.wy - n.y*dp,
    z:o.wz - n.z*dp
  };
  const d1 = lineDistRatio(wp1,wp2,wp3,p);
  const d2 = lineDistRatio(wp2,wp3,wp1,p);
  const d3 = lineDistRatio(wp3,wp1,wp2,p);
  if(d1<0 || d2<0 || d3<0 || isNaN(d1) || isNaN(d2) || isNaN(d3))return false;
  const lx =
    wp1.lx*d1 +
    wp2.lx*d2 +
    wp3.lx*d3;
  const ly =
    wp1.ly*d1 +
    wp2.ly*d2 +
    wp3.ly*d3;
  const dlx = lx - o.lx;
  const dly = ly - o.ly;
  if(dlx*dlx + dly*dly < 0.001)return false; // same point
  return true;
}

window.addEventListener("load",_=>{
  const cvs = document.getElementById("canvas");
  scrW = cvs.width;
  scrH = cvs.height;

  const gl = cvs.getContext("webgl");
  const extFloat = gl.getExtension('OES_texture_float');
  if(extFloat == null){
    console.err(":P (float tex)");
    return;
  }
  gl.disable(gl.BLEND);
  gl.disable(gl.DEPTH_TEST);
  gl.disable(gl.CULL_FACE);
  gl.viewport(0,0,scrW,scrH);
  gl.clearColor(0,0,0.5,1);

  const frameBuffer = gl.createFramebuffer();
  gl.bindFramebuffer(gl.FRAMEBUFFER,frameBuffer);
  const worldTexture = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D,worldTexture);
  gl.texImage2D(gl.TEXTURE_2D,0,gl.RGBA,scrW,scrH,0,gl.RGBA,gl.FLOAT,null);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MAG_FILTER,gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_MIN_FILTER,gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_S,gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D,gl.TEXTURE_WRAP_T,gl.CLAMP_TO_EDGE);
  gl.framebufferTexture2D(gl.FRAMEBUFFER,gl.COLOR_ATTACHMENT0,gl.TEXTURE_2D,worldTexture,0);
  gl.bindFramebuffer(gl.FRAMEBUFFER,null);

  const verts = [-1,-1,-1,1,1,-1,1,1];
  const vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
  gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(verts),gl.STATIC_DRAW);

  const tverts = new Float32Array(angleCount*(2*proceedCount-1)*3*6);
  const tvbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER,tvbo);
  gl.bufferData(gl.ARRAY_BUFFER,tverts,gl.DYNAMIC_DRAW);

  const vsSource = `
    precision mediump float;
    attribute vec2 position;
    varying vec2 coord;
    uniform vec2 resolution;

    void main(void){
      coord = position * resolution;
      gl_Position = vec4(position,0.,1.);
    }
  `;
  const fsSource = (f,g,b)=>`
    precision mediump float;
    const float pi = 3.1415926535;
    varying vec2 coord;
    uniform vec2 resolution;
    uniform vec3 camera;
    uniform mat3 transform;
    uniform float fov;

    float field(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      return max(` + f + `, ` + b + `);
    }
    vec3 gradient(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      return ` + g + `;
    }
    void main(void){
      vec2 uv = coord/resolution.y;

      vec3 cur = camera;
      vec3 dir = normalize(vec3(uv.x,uv.y,1./tan(fov*pi/180.)));
      dir = transform * dir;

      // Raymarch
      vec3 pos, nrm;
      float d = 0.;
      int maxIter = -1;
      for(int i=0;i<100;i++){
        pos = cur+dir*d;
        nrm = gradient(pos);
        float f = field(pos)/length(nrm);
        if(abs(f)<0.01){
          maxIter = i;
          break;
        }
        d += f;
      }
      // Discontinuity reduction
      for(int i=0;i<5;i++){
        nrm = gradient(pos);
        d += field(pos)/length(nrm) - 0.001*d;
        pos = cur+dir*d;
      }
      pos = cur+dir*d;

      float err = length(field(pos))/length(gradient(pos));
      if(abs(err) < 0.01) gl_FragColor = vec4(pos,d);
      else gl_FragColor = vec4(-1);
    }
  `;

  const bgvsSource = `
    precision mediump float;
    attribute vec2 position;
    varying vec2 coord;
    void main(void){
      coord = position * 0.5 + 0.5;
      gl_Position = vec4(position,0.,1.);
    }
  `;
  const bgfsSource = (f,g)=>`
    precision mediump float;
    varying vec2 coord;
    uniform sampler2D worldTex;

    float field(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      return ` + f + `;
    }
    vec3 gradient(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      return ` + g + `;
    }
    void main(void){
      vec4 tex = texture2D(worldTex,coord);
      vec3 pos = tex.xyz;
      float depth = tex.w;
      vec3 n = normalize(gradient(pos));
      vec3 color;
      if(depth == -1.){
        color = vec3(1);
      }else{
        color = pos*0.2+0.8;
      }
      gl_FragColor = vec4(color,1);
    }
  `;

  const tvsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    attribute vec3 position;
    attribute float axisRatio;
    attribute float axisLen;
    attribute float anglePos;
    varying vec3 coord;
    varying vec3 screen;
    varying vec2 borderCoord;
    varying vec2 localCoord;
    uniform vec3 camera;
    uniform mat3 transform;
    uniform float fov;
    uniform float projFactor;
    void main(void){
      coord = position * projFactor;
      vec3 p = transform * (coord - camera);
      p.x *= 3./4.;
      p.xy /= tan(fov*pi/180.);
      screen = p;
      borderCoord = axisRatio * vec2(cos(anglePos),sin(anglePos));
      localCoord = axisLen * borderCoord;
      gl_Position = vec4(p,p.z);
    }
  `;
  const tfsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    varying vec3 coord;
    varying vec3 screen;
    varying vec2 borderCoord;
    varying vec2 localCoord;
    uniform vec3 camera;
    uniform float hue;
    uniform sampler2D worldTex;
    void main(void){
      vec2 texCoord = screen.xy / screen.z * 0.5 + 0.5;
      float depth = texture2D(worldTex,texCoord).w;
      float surfaceDepth = length(coord - camera);
      if(depth < surfaceDepth - 0.1)discard;
      vec3 color = cos(vec3(1,0,-1)*pi*2./3. + hue*pi*2.) * 0.5 + 0.5;
      color += coord * 0.4;
      float factor = 1.;
      if(length(borderCoord) > 0.9) factor = 0.5;
      if(abs(localCoord.x) < 0.01 && localCoord.y < 0.01) factor = 0.5;
      gl_FragColor = vec4(color*factor,1);
    }
  `;

  let program, tprogram, bgprogram;
  let resLocation;
  let camLocation, transLocation, fovLocation;
  let tcamLocation, ttransLocation, tfovLocation, thueLocation, tprojFactorLocation;
  let bgworldTexLocation, tworldTexLocation;

  let origin = [0,0,0];
  let adir = 0.8, rdir = 0, cameraDist = 6;
  let adirTo = adir, rdirTo = rdir;
  let camera = [0,0,0];
  let transform = [1,0,0,0,1,0,0,0,1];
  let transformI = [1,0,0,0,1,0,0,0,1];
  let fov = 20/2;

  let fieldMap = new Float32Array(4 * scrW * scrH);
  let objects = {};

  let grabWorld = false, grabObject = null, grabFlipped = false;
  let prevMouseX = null, prevMouseY;
  cvs.addEventListener("mousedown",e=>{
    prevMouseX = e.offsetX;
    prevMouseY = e.offsetY;
    gl.bindFramebuffer(gl.FRAMEBUFFER,frameBuffer);
    gl.readPixels(0,0,scrW,scrH,gl.RGBA,gl.FLOAT,fieldMap,0);
    gl.bindFramebuffer(gl.FRAMEBUFFER,null);
    const vp = e.offsetX + (scrH - e.offsetY - 1) * scrW;
    const x = fieldMap[vp*4+0];
    const y = fieldMap[vp*4+1];
    const z = fieldMap[vp*4+2];
    const d = fieldMap[vp*4+3];
    if(d != -1){
      // collide to the world
      const m = {wx:x,wy:y,wz:z,lx:100,ly:100};
      const mf = {wx:-x,wy:-y,wz:-z,lx:100,ly:100};
      const a = Object.keys(objects);
      let collide = null;
      for(let i=0;i<a.length;i++){
        const ix = a[i];
        const o = objects[ix];
        for(let j=0;j<o.polygon.length;j++){
          const p = o.polygon[j];
          if(inPolygon(m,p)){
            collide = {
              ix:parseInt(ix),
              wx:x,wy:y,wz:z,
              flip:false
            };
            break;
          }
          if(projective){
            if(inPolygon(mf,p)){
              collide = {
                ix:parseInt(ix),
                wx:x,wy:y,wz:z,
                flip:true
              };
              break;
            }
          }
        }
        if(collide)break;
      }
      if(collide){
        grabObject = collide;
        console.log(grabObject.ix);
      }else{
        grabWorld = true;
      }
    }else{
      grabWorld = true;
    }
  });
  cvs.addEventListener("mousemove",e=>{
    let dx = e.offsetX - prevMouseX;
    let dy = e.offsetY - prevMouseY;
    if(grabWorld){
      rdirTo -= dx/80;
      adirTo += dy/80;
      if(adirTo < -Math.PI/2)adirTo = -Math.PI/2;
      if(adirTo >  Math.PI/2)adirTo =  Math.PI/2;
    }
    if(grabObject){
      gl.bindFramebuffer(gl.FRAMEBUFFER,frameBuffer);
      gl.readPixels(0,0,scrW,scrH,gl.RGBA,gl.FLOAT,fieldMap,0);
      gl.bindFramebuffer(gl.FRAMEBUFFER,null);
      const vp = e.offsetX + (scrH - e.offsetY - 1) * scrW;
      const x = fieldMap[vp*4+0];
      const y = fieldMap[vp*4+1];
      const z = fieldMap[vp*4+2];
      const d = fieldMap[vp*4+3];
      if(d != -1){
        grabObject.wx = x;
        grabObject.wy = y;
        grabObject.wz = z;
      }
    }
    prevMouseX = e.offsetX;
    prevMouseY = e.offsetY;
  });
  cvs.addEventListener("mouseup",e=>{
    grabWorld = false;
    grabObject = null;
  });

  refresh = _=>{
    gl.clear(gl.COLOR_BUFFER_BIT);
  };
  compile = (field,grad,bound)=>{
    function makeShader(type,source){
      const s = gl.createShader(type);
      gl.shaderSource(s,source);
      gl.compileShader(s);
      if(!gl.getShaderParameter(s,gl.COMPILE_STATUS)){
        console.error(gl.getShaderInfoLog(s));
        return null;
      }
      return s;
    }
    function makeProgram(vs,fs){
      const pr = gl.createProgram();
      gl.attachShader(pr,vs);
      gl.attachShader(pr,fs);
      gl.linkProgram(pr);
      if(!gl.getProgramParameter(pr,gl.LINK_STATUS)){
        console.error(gl.getProgramInfoLog(pr));
        return null;
      }
      return pr;
    }
    // Field rendering (to framebuffer)
    const vs = makeShader(gl.VERTEX_SHADER,vsSource);
    const fs = makeShader(gl.FRAGMENT_SHADER,fsSource(field,grad,bound));
    if(!vs || !fs)return;
    program = makeProgram(vs,fs);
    if(!program)return;
    gl.useProgram(program);

    resLocation = gl.getUniformLocation(program,"resolution");
    camLocation = gl.getUniformLocation(program,"camera");
    transLocation = gl.getUniformLocation(program,"transform");
    fovLocation = gl.getUniformLocation(program,"fov");

    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bindAttribLocation(program,0,"position");
    gl.enableVertexAttribArray(0);

    // World rendering
    const bgvs = makeShader(gl.VERTEX_SHADER,bgvsSource);
    const bgfs = makeShader(gl.FRAGMENT_SHADER,bgfsSource(field,grad));
    if(!bgvs || !bgfs)return;
    bgprogram = makeProgram(bgvs,bgfs);
    if(!bgprogram)return;
    gl.useProgram(bgprogram);

    gl.bindTexture(gl.TEXTURE_2D,worldTexture);
    gl.activeTexture(gl.TEXTURE0);
    bgworldTexLocation = gl.getUniformLocation(bgprogram,"worldTex");
    gl.uniform1i(bgworldTexLocation,0);

    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bindAttribLocation(bgprogram,0,"position");
    gl.enableVertexAttribArray(0);

    // Triangle rendering
    const tvs = makeShader(gl.VERTEX_SHADER,tvsSource);
    const tfs = makeShader(gl.FRAGMENT_SHADER,tfsSource);
    if(!tvs || !tfs)return;
    tprogram = makeProgram(tvs,tfs);
    if(!tprogram)return;
    gl.useProgram(tprogram);

    tcamLocation = gl.getUniformLocation(tprogram,"camera");
    ttransLocation = gl.getUniformLocation(tprogram,"transform");
    tfovLocation = gl.getUniformLocation(tprogram,"fov");
    tworldTexLocation = gl.getUniformLocation(tprogram,"worldTex");
    thueLocation = gl.getUniformLocation(tprogram,"hue");
    tprojFactorLocation = gl.getUniformLocation(tprogram,"projFactor");
    gl.uniform1i(tworldTexLocation,0);

    gl.bindBuffer(gl.ARRAY_BUFFER,tvbo);
    const lc3 = gl.getAttribLocation(tprogram,"anglePos");
    if(lc3 != 3){
      console.err("Deficient attributes");
      return;
    }
    gl.bindAttribLocation(tprogram,0,"position");
    gl.bindAttribLocation(tprogram,1,"axisRatio");
    gl.bindAttribLocation(tprogram,2,"axisLen");
    gl.bindAttribLocation(tprogram,3,"anglePos");
    gl.enableVertexAttribArray(0);
    gl.enableVertexAttribArray(1);
    gl.enableVertexAttribArray(2);
    gl.enableVertexAttribArray(3);
  };
  setBounds = (b,g)=>{
    boundary = p=>{
      let x = p.wx;
      let y = p.wy;
      let z = p.wz;
      return eval(b);
    };
    boundGradient = p=>{
      let x = p.wx;
      let y = p.wy;
      let z = p.wz;
      return eval(g);
    };
  };
  function matMult(a,b){
    let c = [];
    for(let i=0;i<9;i++){
      let s = 0;
      for(let j=0;j<3;j++){
        s += a[Math.floor(i/3)*3+j]*b[i%3+j*3];
      }
      c.push(s);
    }
    return c;
  }
  function setCamera(){
    rdir += (rdirTo - rdir) / 2;
    adir += (adirTo - adir) / 2;
    let xRot = [1,0,0,0,Math.cos(adir),Math.sin(adir),0,-Math.sin(adir),Math.cos(adir)];
    let yRot = [Math.cos(rdir),0,Math.sin(rdir),0,1,0,-Math.sin(rdir),0,Math.cos(rdir)];
    let xRotI = [1,0,0,0,Math.cos(adir),-Math.sin(adir),0,Math.sin(adir),Math.cos(adir)];
    let yRotI = [Math.cos(rdir),0,-Math.sin(rdir),0,1,0,Math.sin(rdir),0,Math.cos(rdir)];
    transform = matMult(xRot,yRot);
    transformI = matMult(yRotI,xRotI);
    camera = [
      -transformI[2]*cameraDist + origin[0],
      -transformI[5]*cameraDist + origin[1],
      -transformI[8]*cameraDist + origin[2]
    ];
  }
  draw = _=>{
    if(!program)return;
    setCamera();
    gl.bindFramebuffer(gl.FRAMEBUFFER,frameBuffer);
    gl.useProgram(program);
    gl.uniform2f(resLocation,scrW,scrH);
    gl.uniform3f(camLocation,camera[0],camera[1],camera[2]);
    gl.uniformMatrix3fv(transLocation,false,transform);
    gl.uniform1f(fovLocation,fov);
    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.vertexAttribPointer(0,2,gl.FLOAT,false,8,0);
    gl.enableVertexAttribArray(0);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);
    gl.bindFramebuffer(gl.FRAMEBUFFER,null);

    gl.useProgram(bgprogram);
    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.vertexAttribPointer(0,2,gl.FLOAT,false,8,0);
    gl.enableVertexAttribArray(0);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);
  };
  collide = (o1,o2)=>{
    let form = _=>_; // identity or flipper
    let identity = p=>p;
    let flipper = p=>({
      wx:-p.wx, wy:-p.wy, wz:-p.wz,
      lx:p.lx, ly:p.ly,
      dx:-p.dx, dy:-p.dy, dz:-p.dz
    });
    let flip = false;
    function intersect(os,ss){
      const res = [];
      os.forEach(o=>{
        let fo = form(o);
        for(let i=0;i<ss.length;i++){
          if(inPolygon(fo,ss[i]))res.push(fo);
        }
      });
      return res;
    }
    function maxDistance(vs,os){
      if(vs.length == 0)return null;
      let shortest = 0;
      let pair = null;
      for(let i=0;i<os.length;i++){
        const o1 = os[i];
        const o2 = os[(i+1)%os.length];
        let longest = 0;
        let cand = null;
        vs.forEach(v=>{
          const d = lineDist(o1,o2,v);
          if(longest < d.d){
            longest = d.d;
            cand = {
              d:d.d,
              p1:v,
              p2:d
            };
          }
        });
        if(cand){
          if(shortest == 0 || shortest > cand.d){
            shortest = cand.d;
            pair = cand;
          }
        }
      }
      return pair;
    }
    function getContactPoint(){
      form = flip ? flipper : identity;
      const ddx = flip ? - o1.x - o2.x : o1.x - o2.x;
      const ddy = flip ? - o1.y - o2.y : o1.y - o2.y;
      const ddz = flip ? - o1.z - o2.z : o1.z - o2.z;
      const ddr = o1.enclose + o2.enclose;
      if(ddx*ddx+ddy*ddy+ddz*ddz >= ddr*ddr)return [];
      const sect1 = maxDistance(intersect(o1.outline,o2.polygon),o2.outline);
      const sect2 = maxDistance(intersect(o2.outline,o1.polygon),o1.outline);
      let sel = 0;
      if(sect1 && sect2){
        if(sect1.d < sect2.d)sel = 1;
        else sel = 2;
      }else if(sect1)sel = 1;
      else if(sect2)sel = 2;
      if(sel==0)return [];

      let p1, p2;
      let flipped1 = false, flipped2 = false;
      if(sel==1){
        p1 = sect1.p1;
        p2 = sect1.p2;
        if(flip)flipped1 = true;
      }else{
        p1 = sect2.p2;
        p2 = sect2.p1;
        if(flip)flipped2 = true;
      }
      return [{
        w1x:p1.wx, w1y:p1.wy, w1z:p1.wz,
        w2x:p2.wx, w2y:p2.wy, w2z:p2.wz,
        c1x:p1.lx, c1y:p1.ly,
        c2x:p2.lx, c2y:p2.ly,
        d1x:p1.dx, d1y:p1.dy, d1z:p1.dz,
        d2x:p2.dx, d2y:p2.dy, d2z:p2.dz,
        flipped1:flipped1, flipped2:flipped2
      }];
    }
    flip = false;
    const cps1 = getContactPoint();
    if(!projective)return cps1;
    flip = true;
    const cps2 = getContactPoint();
    return [].concat(cps1,cps2);
  };
  collideBound = (o1)=>{
    const res = [];
    o1.outline.forEach(o=>{
      let bdf = boundary(o);
      let bdn = boundGradient(o);
      let bdl = Math.sqrt(bdn.x*bdn.x+bdn.y*bdn.y+bdn.z*bdn.z);
      if(bdl < 0.001)return;
      let bd = bdf / bdl;
      if(bd >= 0){
        let p1 = o;
        let p2 = {
          wx: o.wx - bdn.x * bd,
          wy: o.wy - bdn.y * bd,
          wz: o.wz - bdn.z * bd,
          lx: 0, ly: 0, dx: 1, dy: 0, dz: 0
        };
        res.push({
          w1x:p1.wx, w1y:p1.wy, w1z:p1.wz,
          w2x:p2.wx, w2y:p2.wy, w2z:p2.wz,
          c1x:p1.lx, c1y:p1.ly,
          c2x:p2.lx, c2y:p2.ly,
          d1x:p1.dx, d1y:p1.dy, d1z:p1.dz,
          d2x:p2.dx, d2y:p2.dy, d2z:p2.dz,
          flipped1:false, flipped2:false
        });
      }
    });
    return res;
  };
  mouseContact = (i)=>{
    if(!grabObject)return [];
    if(grabObject.ix != i)return [];
    let f = grabObject.flip ? -1 : 1;
    let x = grabObject.wx * f;
    let y = grabObject.wy * f;
    let z = grabObject.wz * f;
    return [{
      w1x:0, w1y:0, w1z:0,
      w2x:x, w2y:y, w2z:z,
      c1x:0, c1y:0, c2x:0, c2y:0,
      d1x:0, d1y:0, d1z:0,
      d2x:0, d2y:0, d2z:0,
      flipped1:false, flipped2:false
    }];
  };
  passObject = (ix,o)=>{
    objects[ix] = o;
  };
  drawObjects = _=>{
    let tIndex = 0;
    function vertex(x,y,z,a,w,r){
      tverts[tIndex+0] = x;
      tverts[tIndex+1] = y;
      tverts[tIndex+2] = z;
      tverts[tIndex+3] = a;
      tverts[tIndex+4] = w;
      tverts[tIndex+5] = r;
      tIndex += 6;
    }
    function drawTriangles(hue,projFactor){
      if(!tprogram)return;
      gl.useProgram(tprogram);
      gl.uniform3f(tcamLocation,camera[0],camera[1],camera[2]);
      gl.uniformMatrix3fv(ttransLocation,false,transformI);
      gl.uniform1f(tfovLocation,fov);
      gl.uniform1f(thueLocation,hue);
      gl.uniform1f(tprojFactorLocation,projFactor);
      gl.bindBuffer(gl.ARRAY_BUFFER,tvbo);
      gl.vertexAttribPointer(0,3,gl.FLOAT,false,24,0);
      gl.vertexAttribPointer(1,1,gl.FLOAT,false,24,12);
      gl.vertexAttribPointer(2,1,gl.FLOAT,false,24,16);
      gl.vertexAttribPointer(3,1,gl.FLOAT,false,24,20);
      gl.bufferSubData(gl.ARRAY_BUFFER,0,tverts);
      gl.drawArrays(gl.TRIANGLES,0,angleCount*(2*proceedCount-1)*3);
    };
    let indices = Object.keys(objects);
    indices.forEach(ix=>{
      const o = objects[ix];
      const hue = ix / indices.length;
      o.polygon.forEach(p=>{
        p.forEach(v=>{
          vertex(v.wx,v.wy,v.wz,v.r,v.a,v.t);
        });
      });
      drawTriangles(hue,1);
      if(projective)drawTriangles(hue,-1);
      tIndex = 0;
    });
  };
});
