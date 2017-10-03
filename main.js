const list1 = [
  {path:"plane",name:"Plane"},
  {path:"disc",name:"Disc"},
  {path:"hemi",name:"Hemisphere"},
  {path:"sphere",name:"Sphere"},
  {path:"torus",name:"Torus"},
  {path:"horn",name:"Horn"}
];
const list2 = [
  {path:"plane1",name:"Plane"},
  {path:"disc1",name:"Disc"},
  {path:"hemi1",name:"Hemisphere"},
  {path:"sphere1",name:"Sphere"},
  {path:"torus1",name:"Torus"},
  {path:"horn1",name:"Horn"}
];
const list3 = [
  {path:"proj",name:"Projective Plane"},
  {path:"projtorus",name:"Projective Torus"}
];
const list4 = [
  {path:"tori",name:"Torus in 3D / Embedded 4D Torus"}
];
window.addEventListener("load",_=>{
  const frame = document.getElementById("frame");
  const name = document.getElementById("name");
  function addContent(target,list){
    list.forEach(l=>{
      const img = document.createElement("img");
      img.src="/" + l.path + "/" + l.path + ".png";
      img.addEventListener("click",_=>{
        frame.src = "/" + l.path + "/index.html";
        name.textContent = l.name;
      });
      target.appendChild(img);
    });
  }
  function po(n,p){
    const e = document.getElementById(n);
    addContent(e,p);
  }
  po("list1",list1);
  po("list2",list2);
  po("list3",list3);
  po("list4",list4);
});
