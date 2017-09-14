let scrW = 0, scrH = 0;
let refresh = _=>_, compile = _=>_, draw = _=>_, triangle = _=>_;
window.addEventListener("load",_=>{
  const cvs = document.getElementById("canvas");
  scrW = cvs.width;
  scrH = cvs.height;

  const gl = cvs.getContext("webgl");
  gl.disable(gl.BLEND);
  gl.disable(gl.DEPTH_TEST);
  gl.disable(gl.CULL_FACE);
  gl.viewport(0,0,scrW,scrH);
  gl.clearColor(0,0,0.5,1);

  const verts = [-1,-1,-1,1,1,-1,1,1];
  const vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
  gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(verts),gl.STATIC_DRAW);

  const tverts = new Float32Array(24*(2*6-1)*3*3);
  const tvbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER,tvbo);
  gl.bufferData(gl.ARRAY_BUFFER,tverts,gl.DYNAMIC_DRAW);
  let tIndex = 0;

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
    uniform vec3 circle;
    uniform vec3 rotAxis;
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

      vec3 cur = vec3(0,4,-4.);
      vec3 dir = normalize(vec3(uv.x,uv.y,4));

      float t = 0.8;
      dir.yz *= mat2(cos(t),-sin(t),sin(t),cos(t));
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

      // sphere
      //float theta = coord.x/resolution.x*pi;
      //float phi = coord.y/resolution.y*pi/2.;
      //pos = vec3(cos(phi)*cos(theta),sin(phi),cos(phi)*sin(theta));

      // torus
      //float theta = coord.x/resolution.x*pi;
      //float phi = coord.y/resolution.y*pi;
      //pos = vec3((0.8+0.5*cos(phi))*cos(theta),0.5*sin(phi),(0.8+0.5*cos(phi))*sin(theta));

      // Coloring
      vec3 color;
      if(maxIter == -1){
        color = vec3(1);
      }else{
        color = pos*0.2+0.8;
      }
      vec3 ax = rotAxis;
      vec3 ay = cross(rotAxis,normalize(gradient(circle)));
      for(int d=0;d<24;d++){
        vec3 po = circle;
        float a = float(d)/24.*pi*2.;
        vec3 di = ax*cos(a) + ay*sin(a);
        for(int i=0;i<6;i++){
          if(length(pos-po) < 0.01) color = vec3(0,0.5,0.5);
          po += di * 0.055 * (1. + 1./float(i+1));
          vec3 nr = gradient(po);
          float nd = length(nr);
          float dp = field(po) / nd;
          po -= dp * (nr/nd);

          vec3 gr = gradient(po);
          float adj = -dot(di,gr);
          di += gr * adj;
          di = normalize(di);
        }
      }
      gl_FragColor = vec4(color,1.);
    }
  `;

  const tvsSource = `
    precision mediump float;
    attribute vec3 position;
    varying vec3 coord;
    void main(void){
      coord = position;
      gl_Position = vec4(position.xy,0,1);
    }
  `;
  const tfsSource = `
    precision mediump float;
    const float pi = 3.1415926535;
    varying vec3 coord;
    void main(void){
      gl_FragColor = vec4(coord*0.5+0.5,1);
    }
  `;

  let program, tprogram;
  let resLocation, circleLocation, rotAxisLocation;

  refresh = _=>{
    gl.clear(gl.COLOR_BUFFER_BIT);
    tIndex = 0;
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
    // Field rendering
    const vs = makeShader(gl.VERTEX_SHADER,vsSource);
    const fs = makeShader(gl.FRAGMENT_SHADER,fsSource(field,grad));
    if(!vs || !fs)return;
    program = makeProgram(vs,fs);
    if(!program)return;
    gl.useProgram(program);

    resLocation = gl.getUniformLocation(program,"resolution");
    circleLocation = gl.getUniformLocation(program,"circle");
    rotAxisLocation = gl.getUniformLocation(program,"rotAxis");

    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.bindAttribLocation(program,0,"position");
    gl.enableVertexAttribArray(0);

    // Triangle rendering
    const tvs = makeShader(gl.VERTEX_SHADER,tvsSource);
    const tfs = makeShader(gl.FRAGMENT_SHADER,tfsSource);
    if(!tvs || !tfs)return;
    tprogram = makeProgram(tvs,tfs);
    if(!tprogram)return;
    gl.useProgram(tprogram);

    gl.bindBuffer(gl.ARRAY_BUFFER,tvbo);
    gl.bindAttribLocation(tprogram,0,"position");
    gl.enableVertexAttribArray(0);
  };
  draw = (x,y,z,rx,ry,rz)=>{
    if(!program)return;
    gl.useProgram(program);
    gl.uniform2f(resLocation,scrW,scrH);
    gl.uniform3f(circleLocation,x,y,z);
    gl.uniform3f(rotAxisLocation,rx,ry,rz);
    gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
    gl.vertexAttribPointer(0,2,gl.FLOAT,false,0,0);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);
  };
  triangle = (x1,y1,z1,x2,y2,z2,x3,y3,z3)=>{
    tverts[tIndex+0] = x1;
    tverts[tIndex+1] = y1;
    tverts[tIndex+2] = z1;
    tverts[tIndex+3] = x2;
    tverts[tIndex+4] = y2;
    tverts[tIndex+5] = z2;
    tverts[tIndex+6] = x3;
    tverts[tIndex+7] = y3;
    tverts[tIndex+8] = z3;
    tIndex += 9;
  };
  drawTriangles = _=>{
    if(!tprogram)return;
    gl.useProgram(tprogram);
    gl.bindBuffer(gl.ARRAY_BUFFER,tvbo);
    gl.vertexAttribPointer(0,3,gl.FLOAT,false,0,0);
    gl.bufferSubData(gl.ARRAY_BUFFER,0,tverts);
    gl.drawArrays(gl.TRIANGLES,0,24*(2*6-1)*3);
  };
});
