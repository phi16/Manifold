const leftList = [
  {path:"plane",name:"Plane"},
  {path:"hemi",name:"Hemisphere"},
  {path:"sphere",name:"Sphere"},
  {path:"torus",name:"Torus"},
  {path:"horn",name:"Horn"}
];
const rightList = [
  {path:"disc",name:"Disc"},
  {path:"proj",name:"Projective Plane"},
  {path:"projtorus",name:"Projective Torus"},
  {path:"tori",name:"Torus in 3D / Embedded 4D Torus"}
];
window.addEventListener("load",_=>{
  const frame = document.getElementById("frame");
  const name = document.getElementById("name");
  function addContent(target,list){
    list.forEach(l=>{
      const img = document.createElement("img");
      img.src="/Manifold/" + l.path + "/" + l.path + ".png";
      img.addEventListener("click",_=>{
        frame.src = "/Manifold/" + l.path + "/index.html";
        name.textContent = l.name;
      });
      target.appendChild(img);
    });
  }
  const left = document.getElementById("left");
  addContent(left,leftList);
  const right = document.getElementById("right");
  addContent(right,rightList);
});
