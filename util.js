let scrW = 0, scrH = 0;
let refresh = _=>_, compile = _=>_, draw = _=>_;
window.addEventListener("load",_=>{
  const cvs = document.getElementById("canvas");
  scrW = cvs.width;
  scrH = cvs.height;

  const gl = cvs.getContext("webgl");
  const verts = [-1,-1,-1,1,1,-1,1,1];
  const vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER,vbo);
  gl.bufferData(gl.ARRAY_BUFFER,new Float32Array(verts),gl.STATIC_DRAW);
  gl.disable(gl.BLEND);
  gl.disable(gl.DEPTH_TEST);
  gl.viewport(0,0,scrW,scrH);
  gl.clearColor(0,0,0,1);

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
      vec3 dir = normalize(vec3(uv.x,uv.y,6));

      vec3 lookDir = -normalize(gradient(circle));
      cur = circle - lookDir * 10.;
      dir = lookAt(lookDir,rotAxis)*dir;

      //float t = 0.8;
      //dir.yz *= mat2(cos(t),-sin(t),sin(t),cos(t));
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
      for(int i=0;i<1;i++){
        nrm = gradient(pos);
        d += field(pos)/length(nrm) - 0.01*d;
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
        nrm = normalize(nrm);
        //nrm.yz *= mat2(cos(-t),-sin(-t),sin(-t),cos(-t));
        //color = vec3(-nrm.z*0.5+0.5);
        color = vec3(1);
        color *= pos*0.2+0.8;
      }
      if(length(pos-circle) < 0.2){
        color *= vec3(0.8);
        vec3 factor = vec3(1);
        if(length(pos-circle) > 0.18){
          factor = vec3(0.5);
        }
        if(abs(dot(pos-circle,cross(nrm,rotAxis))) < 0.006 && dot(pos-circle,rotAxis) < 0.008){
          factor = vec3(0.5);
        }
        color *= factor;
      }
      gl_FragColor = vec4(color,1.);
    }
  `;

  let program;
  let resLocation, posLocation;
  let circleLocation, rotAxisLocation;

  refresh = _=>{
    gl.clear(gl.COLOR_BUFFER_BIT);
    gl.uniform2f(resLocation,scrW,scrH);
  };
  draw = (x,y,z,rx,ry,rz)=>{
    if(!program)return;
    gl.uniform3f(circleLocation,x,y,z);
    gl.uniform3f(rotAxisLocation,rx,ry,rz);
    gl.drawArrays(gl.TRIANGLE_STRIP,0,4);
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
    const vs = makeShader(gl.VERTEX_SHADER,vsSource);
    const fs = makeShader(gl.FRAGMENT_SHADER,fsSource(field,grad));
    if(!vs || !fs)return;
    program = makeProgram(vs,fs);
    gl.useProgram(program);
    if(!program)return;

    resLocation = gl.getUniformLocation(program,"resolution");
    circleLocation = gl.getUniformLocation(program,"circle");
    rotAxisLocation = gl.getUniformLocation(program,"rotAxis");

    posLocation = gl.getAttribLocation(program,"position");
    gl.enableVertexAttribArray(posLocation);
    gl.vertexAttribPointer(posLocation,2,gl.FLOAT,false,0,0);
  };
});
