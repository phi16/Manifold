const angleCount = 24;
const proceedCount = 4;

let scrW = 0, scrH = 0;
let refresh = _=>_;
let compile = _=>_;
let draw = _=>_;
let collide = _=>_;
let drawObject = _=>_;

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
  const fsSource = (f,g)=>`
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
      return ` + f + `;
    }
    vec3 gradient(vec3 p){
      float x = p.x;
      float y = p.y;
      float z = p.z;
      return ` + g + `;
    }
    mat3 lookAt(vec3 look, vec3 up){
      vec3 z = normalize(look);
      vec3 x = normalize(cross(up,z));
      vec3 y = cross(z,x);
      return mat3(x,y,z);
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
      nrm = gradient(pos);

      // Coloring
      vec3 color;
      if(maxIter == -1){
        color = vec3(1);
      }else{
        color = pos*0.2+0.8;
      }
      gl_FragColor = vec4(color,d);
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
  const bgfsSource = `
    precision mediump float;
    varying vec2 coord;
    uniform sampler2D worldTex;
    void main(void){
      gl_FragColor = texture2D(worldTex,coord);
      gl_FragColor.w = 1.;
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
    void main(void){
      coord = position;
      vec3 p = transform * (position - camera);
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
    uniform sampler2D worldTex;
    void main(void){
      vec2 texCoord = screen.xy / screen.z * 0.5 + 0.5;
      float depth = texture2D(worldTex,texCoord).w;
      float surfaceDepth = length(coord - camera);
      if(depth < surfaceDepth - 0.2)discard;
      vec3 color = coord * 0.5 + 0.5;
      float factor = 1.;
      if(length(borderCoord) > 0.9) factor = 0.5;
      if(abs(localCoord.x) < 0.01 && localCoord.y < 0.01) factor = 0.5;
      gl_FragColor = vec4(color*factor,1);
    }
  `;

  let program, tprogram, bgprogram;
  let resLocation;
  let camLocation, transLocation, fovLocation;
  let tcamLocation, ttransLocation, tfovLocation;
  let bgworldTexLocation, tworldTexLocation;

  let camera = [0,4,-4];
  let adir = 0.8;
  let transform = [1,0,0,0,Math.cos(adir),Math.sin(adir),0,-Math.sin(adir),Math.cos(adir)];
  let transformI = [1,0,0,0,Math.cos(adir),-Math.sin(adir),0,Math.sin(adir),Math.cos(adir)];
  let fov = 30/2;

  refresh = _=>{
    gl.clear(gl.COLOR_BUFFER_BIT);
  };
  compile = (field,grad)=>{
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
    const fs = makeShader(gl.FRAGMENT_SHADER,fsSource(field,grad));
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
    const bgfs = makeShader(gl.FRAGMENT_SHADER,bgfsSource);
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
  draw = _=>{
    if(!program)return;
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
    function lineDist(l0,l1,l2,p){
      const d1x = p.x;
      const d1y = p.y;
      const d1z = p.z;
      const d2x = l2.wx-l1.wx;
      const d2y = l2.wy-l1.wy;
      const d2z = l2.wz-l1.wz;
      const nx = d1y*d2z-d2y*d1z;
      const ny = d1z*d2x-d2z*d1x;
      const nz = d1x*d2y-d2x*d1y;
      const pDist =
        (p.x-l1.wx)*nx +
        (p.y-l1.wy)*ny +
        (p.z-l1.wz)*nz;
      const oDist =
        (l0.wx-l1.wx)*nx +
        (l0.wy-l1.wy)*ny +
        (l0.wz-l1.wz)*nz;
      return pDist / oDist;
    }
    function intersect(os,ss){
      const res = [];
      os.forEach(o=>{
        for(let i=0;i<ss.length;i++){
          const s = ss[i];
          const wp1 = s[0];
          const wp2 = s[1];
          const wp3 = s[2];
          const n = polygonNormal(wp1,wp2,wp3);
          const dp =
            (o.wx-wp1.wx)*n.x +
            (o.wy-wp1.wy)*n.y +
            (o.wz-wp1.wz)*n.z;
          if(Math.abs(dp) >= 0.1)continue;
          const p = {
            x:o.wx - n.x*dp,
            y:o.wy - n.y*dp,
            z:o.wz - n.z*dp
          };
          const d1 = lineDist(wp1,wp2,wp3,p);
          const d2 = lineDist(wp2,wp3,wp1,p);
          const d3 = lineDist(wp3,wp1,wp2,p);
          if(d1<0 || d2<0 || d3<0)continue;
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
          if(dlx*dlx + dly*dly < 0.001)continue; // same point
          res.push({
            wx: o.wx,
            wy: o.wy,
            wz: o.wz,
            lx: lx,
            ly: ly
          });
        }
      });
      return res;
    }
    const sect1 = intersect(o1.outline,o2.polygon);
    const sect2 = intersect(o2.outline,o1.polygon);
    return [];
  };
  drawObject = o=>{
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
    function drawTriangles(){
      if(!tprogram)return;
      gl.useProgram(tprogram);
      gl.uniform3f(tcamLocation,camera[0],camera[1],camera[2]);
      gl.uniformMatrix3fv(ttransLocation,false,transformI);
      gl.uniform1f(tfovLocation,fov);
      gl.bindBuffer(gl.ARRAY_BUFFER,tvbo);
      gl.vertexAttribPointer(0,3,gl.FLOAT,false,24,0);
      gl.vertexAttribPointer(1,1,gl.FLOAT,false,24,12);
      gl.vertexAttribPointer(2,1,gl.FLOAT,false,24,16);
      gl.vertexAttribPointer(3,1,gl.FLOAT,false,24,20);
      gl.bufferSubData(gl.ARRAY_BUFFER,0,tverts);
      gl.drawArrays(gl.TRIANGLES,0,angleCount*(2*proceedCount-1)*3);
    };
    o.polygon.forEach(p=>{
      p.forEach(v=>{
        vertex(v.wx, v.wy, v.wz, v.r, v.a, v.t);
      });
    });
    drawTriangles();
  };
});
