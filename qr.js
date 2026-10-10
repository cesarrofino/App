/* ===== Motor de código QR (gerar e ler) - sem dependências, funciona offline ===== */
const QR=(()=>{
'use strict';
const EXP=new Uint8Array(512),LOG=new Uint8Array(256);
{let x=1;for(let i=0;i<255;i++){EXP[i]=x;LOG[x]=i;x<<=1;if(x&256)x^=0x11d}for(let i=255;i<512;i++)EXP[i]=EXP[i-255]}
const mul=(a,b)=>a&&b?EXP[LOG[a]+LOG[b]]:0;
const inv=a=>EXP[255-LOG[a]];
/* [total codewords, ecc por bloco, blocos grupo1, dados grupo1, blocos grupo2, dados grupo2] versões 1..10 */
const TBL={
L:[null,[26,7,1,19,0,0],[44,10,1,34,0,0],[70,15,1,55,0,0],[100,20,1,80,0,0],[134,26,1,108,0,0],[172,18,2,68,0,0],[196,20,2,78,0,0],[242,24,2,97,0,0],[292,30,2,116,0,0],[346,18,2,68,2,69]],
M:[null,[26,10,1,16,0,0],[44,16,1,28,0,0],[70,26,1,44,0,0],[100,18,2,32,0,0],[134,24,2,43,0,0],[172,16,4,27,0,0],[196,18,4,31,0,0],[242,22,2,38,2,39],[292,22,3,36,2,37],[346,26,4,43,1,44]]};
const FMT={L:1,M:0};
const ALIGN=[null,[],[6,18],[6,22],[6,26],[6,30],[6,34],[6,22,38],[6,24,42],[6,26,46],[6,28,50]];
const MAXV=10;
const bit=(v,i)=>(v>>>i)&1;

/* ---------- Reed-Solomon ---------- */
function rsGen(n){let p=[1];for(let i=0;i<n;i++){const q=new Array(p.length+1).fill(0);for(let j=0;j<p.length;j++){q[j]^=p[j];q[j+1]^=mul(p[j],EXP[i])}p=q}return p}
function rsEnc(data,n){const g=rsGen(n),r=new Array(n).fill(0);for(const d of data){const f=d^r.shift();r.push(0);if(f)for(let i=0;i<n;i++)r[i]^=mul(g[i+1],f)}return r}
function polyEval(p,x){let r=0;for(let i=p.length-1;i>=0;i--)r=mul(r,x)^p[i];return r}
function rsDec(msg,nsym){
 const len=msg.length,syn=[];let bad=false;
 for(let j=0;j<nsym;j++){let s=0;for(let i=0;i<len;i++)s=mul(s,EXP[j])^msg[i];syn.push(s);if(s)bad=true}
 if(!bad)return msg;
 let C=[1],B=[1],L=0,m=1,b=1;
 for(let n=0;n<nsym;n++){
  let d=syn[n];for(let i=1;i<=L;i++)d^=mul(C[i]||0,syn[n-i]);
  if(d===0){m++;continue}
  const T=C.slice(),coef=mul(d,inv(b));
  while(C.length<B.length+m)C.push(0);
  for(let i=0;i<B.length;i++)C[i+m]^=mul(coef,B[i]);
  if(2*L<=n){L=n+1-L;B=T;b=d;m=1}else m++;
 }
 while(C.length&&C[C.length-1]===0)C.pop();
 if(C.length-1!==L||L>nsym/2)return null;
 const pos=[];
 for(let p=0;p<len;p++){const xi=EXP[(255-((len-1-p)%255))%255];if(polyEval(C,xi)===0)pos.push(p)}
 if(pos.length!==L)return null;
 // omega = (S(x)*C(x)) mod x^nsym
 const om=new Array(nsym).fill(0);
 for(let i=0;i<nsym;i++)for(let j=0;j<C.length&&i+j<nsym;j++)om[i+j]^=mul(syn[i],C[j]);
 const dC=[];for(let i=1;i<C.length;i+=2)dC[i-1]=C[i];
 const out=msg.slice();
 for(const p of pos){
  const e=(len-1-p)%255,X=EXP[e],Xi=EXP[(255-e)%255];
  const lam=polyEval(dC.map(v=>v||0),Xi);if(!lam)return null;
  const num=polyEval(om,Xi);
  out[p]=msg[p]^mul(mul(X,num),inv(lam));
 }
 // confirmar
 for(let j=0;j<nsym;j++){let s=0;for(let i=0;i<len;i++)s=mul(s,EXP[j])^out[i];if(s)return null}
 return out;
}

/* ---------- Estrutura da matriz ---------- */
function mkBase(v){
 const size=17+4*v,mods=[],fn=[];
 for(let i=0;i<size;i++){mods.push(new Uint8Array(size));fn.push(new Uint8Array(size))}
 const set=(x,y,c)=>{mods[y][x]=c?1:0;fn[y][x]=1};
 for(let i=0;i<size;i++){set(6,i,i%2===0);set(i,6,i%2===0)}
 const finder=(cx,cy)=>{for(let dy=-4;dy<=4;dy++)for(let dx=-4;dx<=4;dx++){const d=Math.max(Math.abs(dx),Math.abs(dy)),x=cx+dx,y=cy+dy;if(x>=0&&x<size&&y>=0&&y<size)set(x,y,d!==2&&d!==4)}};
 finder(3,3);finder(size-4,3);finder(3,size-4);
 const al=ALIGN[v];
 for(let i=0;i<al.length;i++)for(let j=0;j<al.length;j++){
  if((i===0&&j===0)||(i===0&&j===al.length-1)||(i===al.length-1&&j===0))continue;
  for(let dy=-2;dy<=2;dy++)for(let dx=-2;dx<=2;dx++)set(al[i]+dx,al[j]+dy,Math.max(Math.abs(dx),Math.abs(dy))!==1)}
 // reservar zonas de formato e versão
 for(let i=0;i<9;i++){fn[8][i]=1;fn[i][8]=1}
 for(let i=0;i<8;i++){fn[8][size-1-i]=1;fn[size-1-i][8]=1}
 set(8,size-8,true);
 if(v>=7){const ver=v;let rem=ver;for(let i=0;i<12;i++)rem=(rem<<1)^((rem>>>11)*0x1F25);const bits=(ver<<12)|rem;
  for(let i=0;i<18;i++){const c=bit(bits,i),a=size-11+i%3,b=Math.floor(i/3);set(a,b,c);set(b,a,c)}}
 return {size,mods,fn};
}
function fmtBits(ecl,mask){const data=(FMT[ecl]<<3)|mask;let rem=data;for(let i=0;i<10;i++)rem=(rem<<1)^((rem>>>9)*0x537);return((data<<10)|rem)^0x5412}
function drawFmt(o,ecl,mask){
 const {size,mods,fn}=o,b=fmtBits(ecl,mask),set=(x,y,c)=>{mods[y][x]=c?1:0;fn[y][x]=1};
 for(let i=0;i<=5;i++)set(8,i,bit(b,i));set(8,7,bit(b,6));set(8,8,bit(b,7));set(7,8,bit(b,8));for(let i=9;i<15;i++)set(14-i,8,bit(b,i));
 for(let i=0;i<8;i++)set(size-1-i,8,bit(b,i));for(let i=8;i<15;i++)set(8,size-15+i,bit(b,i));set(8,size-8,true);
}
const MASKS=[(x,y)=>(x+y)%2===0,(x,y)=>y%2===0,(x,y)=>x%3===0,(x,y)=>(x+y)%3===0,(x,y)=>(Math.floor(x/3)+Math.floor(y/2))%2===0,(x,y)=>x*y%2+x*y%3===0,(x,y)=>(x*y%2+x*y%3)%2===0,(x,y)=>((x+y)%2+x*y%3)%2===0];
function zigzag(size,fn,cb){let i=0;for(let right=size-1;right>=1;right-=2){if(right===6)right=5;for(let vert=0;vert<size;vert++)for(let j=0;j<2;j++){const x=right-j,up=((right+1)&2)===0,y=up?size-1-vert:vert;if(!fn[y][x])cb(x,y,i++)}}}

function penalty(o){
 const {size,mods}=o;let p=0;
 const P1=[1,0,1,1,1,0,1,0,0,0,0],P2=[0,0,0,0,1,0,1,1,1,0,1];
 const scan=line=>{ // regra 1 (sequências) e regra 3 (falsos cantos)
  let q=0,run=1;
  for(let i=1;i<=line.length;i++){if(i<line.length&&line[i]===line[i-1])run++;else{if(run>=5)q+=3+run-5;run=1}}
  for(let i=0;i+11<=line.length;i++){let a=true,b=true;for(let j=0;j<11;j++){if(line[i+j]!==P1[j])a=false;if(line[i+j]!==P2[j])b=false;if(!a&&!b)break}if(a)q+=40;if(b)q+=40}
  return q};
 for(let y=0;y<size;y++)p+=scan(Array.from(mods[y]));
 for(let x=0;x<size;x++){const col=[];for(let y=0;y<size;y++)col.push(mods[y][x]);p+=scan(col)}
 for(let y=0;y<size-1;y++)for(let x=0;x<size-1;x++){const c=mods[y][x];if(c===mods[y][x+1]&&c===mods[y+1][x]&&c===mods[y+1][x+1])p+=3}
 let dark=0;for(let y=0;y<size;y++)for(let x=0;x<size;x++)dark+=mods[y][x];
 const tot=size*size;p+=(Math.ceil(Math.abs(dark*20-tot*10)/tot)-1)*10;
 return p;
}

/* ---------- Gerar ---------- */
function utf8(s){return Array.from(new TextEncoder().encode(s))}
function make(text,pref,fm){
 const bytes=utf8(text);let ecl=pref||'M',v=0;
 const tryEcl=e=>{for(let k=1;k<=MAXV;k++){const t=TBL[e][k],dcw=t[2]*t[3]+t[4]*t[5],cap=dcw*8-4-(k<10?8:16);if(bytes.length*8<=cap)return k}return 0};
 v=tryEcl(ecl);if(!v&&ecl==='M'){ecl='L';v=tryEcl('L')}
 if(!v)return null;
 const t=TBL[ecl][v],dcw=t[2]*t[3]+t[4]*t[5];
 const bits=[];const push=(val,n)=>{for(let i=n-1;i>=0;i--)bits.push((val>>>i)&1)};
 push(4,4);push(bytes.length,v<10?8:16);bytes.forEach(b=>push(b,8));
 push(0,Math.min(4,dcw*8-bits.length));while(bits.length%8)bits.push(0);
 const cw=[];for(let i=0;i<bits.length;i+=8){let b=0;for(let j=0;j<8;j++)b=(b<<1)|bits[i+j];cw.push(b)}
 for(let pad=0xEC;cw.length<dcw;pad^=0xEC^0x11)cw.push(pad);
 const blocks=[],eccs=[];let pos=0;
 for(let g=0;g<2;g++){const nb=g?t[4]:t[2],ln=g?t[5]:t[3];for(let i=0;i<nb;i++){const d=cw.slice(pos,pos+ln);pos+=ln;blocks.push(d);eccs.push(rsEnc(d,t[1]))}}
 const out=[],maxd=Math.max(...blocks.map(b=>b.length));
 for(let i=0;i<maxd;i++)blocks.forEach(b=>{if(i<b.length)out.push(b[i])});
 for(let i=0;i<t[1];i++)eccs.forEach(e=>out.push(e[i]));
 let best=null,bp=1e9;
 for(let m=0;m<8;m++){
  if(fm!=null&&m!==fm)continue;
  const o=mkBase(v);zigzag(o.size,o.fn,(x,y,i)=>{if(i<out.length*8)o.mods[y][x]=bit(out[i>>>3],7-(i&7))});
  for(let y=0;y<o.size;y++)for(let x=0;x<o.size;x++)if(!o.fn[y][x]&&MASKS[m](x,y))o.mods[y][x]^=1;
  drawFmt(o,ecl,m);const p=penalty(o);if(p<bp){bp=p;best=o}
 }
 return {size:best.size,mods:best.mods,version:v,ecl};
}
function svg(q,px,fg,bg){
 const quiet=4,n=q.size+quiet*2;let d='';
 for(let y=0;y<q.size;y++){let x=0;while(x<q.size){if(q.mods[y][x]){let s=x;while(x<q.size&&q.mods[y][x])x++;d+='M'+(s+quiet)+' '+(y+quiet)+'h'+(x-s)+'v1h-'+(x-s)+'z'}else x++}}
 return '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 '+n+' '+n+'" width="'+(px||n)+'" height="'+(px||n)+'" shape-rendering="crispEdges"><rect width="'+n+'" height="'+n+'" fill="'+(bg||'#fff')+'"/><path d="'+d+'" fill="'+(fg||'#000')+'"/></svg>';
}
function canvas(q,scale){
 const quiet=4,n=(q.size+quiet*2)*scale,c=document.createElement('canvas');c.width=c.height=n;const g=c.getContext('2d');
 g.fillStyle='#fff';g.fillRect(0,0,n,n);g.fillStyle='#000';
 for(let y=0;y<q.size;y++)for(let x=0;x<q.size;x++)if(q.mods[y][x])g.fillRect((x+quiet)*scale,(y+quiet)*scale,scale,scale);
 return c;
}

/* ---------- Ler ---------- */
function solve(A,b){ // eliminação de Gauss 8x8
 const n=b.length;for(let i=0;i<n;i++){let m=i;for(let r=i+1;r<n;r++)if(Math.abs(A[r][i])>Math.abs(A[m][i]))m=r;[A[i],A[m]]=[A[m],A[i]];[b[i],b[m]]=[b[m],b[i]];
  if(Math.abs(A[i][i])<1e-12)return null;
  for(let r=i+1;r<n;r++){const f=A[r][i]/A[i][i];for(let c=i;c<n;c++)A[r][c]-=f*A[i][c];b[r]-=f*b[i]}}
 const x=new Array(n);for(let i=n-1;i>=0;i--){let s=b[i];for(let c=i+1;c<n;c++)s-=A[i][c]*x[c];x[i]=s/A[i][i]}return x;
}
function homog(src,dst){
 const A=[],b=[];
 for(let i=0;i<4;i++){const [u,v]=src[i],[x,y]=dst[i];
  A.push([u,v,1,0,0,0,-u*x,-v*x]);b.push(x);
  A.push([0,0,0,u,v,1,-u*y,-v*y]);b.push(y)}
 const h=solve(A,b);if(!h)return null;
 return (u,v)=>{const w=h[6]*u+h[7]*v+1;return [(h[0]*u+h[1]*v+h[2])/w,(h[3]*u+h[4]*v+h[5])/w]};
}
function binarize(rgba,w,h){
 const g=new Uint8Array(w*h),hist=new Array(256).fill(0);
 for(let i=0,j=0;i<w*h;i++,j+=4){const v=(rgba[j]*77+rgba[j+1]*150+rgba[j+2]*29)>>8;g[i]=v;hist[v]++}
 // limiar global (Otsu)
 let sum=0;for(let i=0;i<256;i++)sum+=i*hist[i];let sb=0,wb=0,mx=-1,T=128;const tot=w*h;
 for(let t=0;t<256;t++){wb+=hist[t];if(!wb)continue;const wf=tot-wb;if(!wf)break;sb+=t*hist[t];const mb=sb/wb,mf=(sum-sb)/wf,v=wb*wf*(mb-mf)*(mb-mf);if(v>mx){mx=v;T=t}}
 const ii=new Float64Array((w+1)*(h+1));
 for(let y=0;y<h;y++){let row=0;for(let x=0;x<w;x++){row+=g[y*w+x];ii[(y+1)*(w+1)+x+1]=ii[y*(w+1)+x+1]+row}}
 const bs=Math.max(25,(Math.floor(Math.min(w,h)/6)|1)),r=bs>>1,bin=new Uint8Array(w*h);
 for(let y=0;y<h;y++){const y0=Math.max(0,y-r),y1=Math.min(h,y+r+1);for(let x=0;x<w;x++){const x0=Math.max(0,x-r),x1=Math.min(w,x+r+1),s=ii[y1*(w+1)+x1]-ii[y0*(w+1)+x1]-ii[y1*(w+1)+x0]+ii[y0*(w+1)+x0],mean=s/((x1-x0)*(y1-y0)),v=g[y*w+x];
   bin[y*w+x]=(v<mean*0.9-2||(Math.abs(v-mean)<=6&&v<=T))?1:0}}
 return bin;
}
function findCenters(B,w,h,pat,tolS,minHits){
 // procura padrões de execução (pat = proporções) por linhas e verifica na vertical
 const cands=[];
 const np=pat.length,total=pat.reduce((a,b)=>a+b,0);
 const at=(x,y)=>x>=0&&y>=0&&x<w&&y<h?B[y*w+x]:0;
 const okRuns=(r,tol)=>{const s=r.reduce((a,b)=>a+b,0),m=s/total;if(m<1)return 0;for(let i=0;i<np;i++)if(Math.abs(r[i]-pat[i]*m)>Math.max(pat[i]*m*tol,m*0.75))return 0;return m};
 const vert=(x,y)=>{
  const r=new Array(np).fill(0),mid=(np-1)>>1;let yy=y,cur=at(x,y);
  // para trás
  let idx=mid;
  while(yy>=0&&idx>=0){if(at(x,yy)===cur){r[idx]++;yy--}else{idx--;cur=1-cur}}
  if(idx>=0)return null;
  const back=r[mid];
  yy=y+1;cur=at(x,y);idx=mid;
  while(yy<h&&idx<np){if(at(x,yy)===cur){r[idx]++;yy++}else{idx++;cur=1-cur}}
  if(idx<np)return null;
  const m=okRuns(r,tolS);if(!m)return null;
  let before=0;for(let i=0;i<mid;i++)before+=r[i];
  return {m,c:y-back-before+total/2*m+0-0};
 };
 for(let y=0;y<h;y+=1){
  let x=0;const runs=[],starts=[];
  let cur=at(0,y),s=0;
  for(x=1;x<=w;x++){const c=x<w?at(x,y):1-cur;if(c!==cur||x===w){runs.push(x-s);starts.push(s);s=x;cur=c}}
  // runs alternam; a cor da primeira run
  let col=at(0,y);
  for(let i=0;i+np<=runs.length;i++){
   const runCol=(col+i)%2;if(runCol!==1)continue; // começa por escuro
   const r=runs.slice(i,i+np),m=okRuns(r,tolS);if(!m)continue;
   const cx=starts[i]+r.reduce((a,b)=>a+b,0)/2;
   const v=vert(Math.round(cx),y);if(!v)continue;
   if(Math.abs(v.m-m)>m*0.6)continue;
   cands.push({x:cx,y:v.c,m:(m+v.m)/2,n:1});
  }
 }
 // agrupar
 const cl=[];
 for(const c of cands){let f=null;for(const k of cl)if(Math.hypot(k.x-c.x,k.y-c.y)<Math.max(c.m,k.m)*2.2){f=k;break}
  if(f){f.x=(f.x*f.n+c.x)/(f.n+1);f.y=(f.y*f.n+c.y)/(f.n+1);f.m=(f.m*f.n+c.m)/(f.n+1);f.n++}else cl.push({...c})}
 return cl.filter(k=>k.n>=minHits).sort((a,b)=>b.n-a.n);
}
function pickTriple(c){
 let best=null,bs=1e9;
 const n=Math.min(c.length,8);
 for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)for(let k=j+1;k<n;k++){
  const P=[c[i],c[j],c[k]],d=[Math.hypot(P[1].x-P[2].x,P[1].y-P[2].y),Math.hypot(P[0].x-P[2].x,P[0].y-P[2].y),Math.hypot(P[0].x-P[1].x,P[0].y-P[1].y)];
  // vértice do ângulo reto = oposto ao lado maior
  const mx=d.indexOf(Math.max(...d)),o=[0,1,2].filter(t=>t!==mx),a=d[o[0]],b=d[o[1]],h=d[mx];
  const sc=Math.abs(a-b)/Math.max(a,b)+Math.abs(h-Math.SQRT2*(a+b)/2)/h;
  const ms=P.map(p=>p.m),mr=Math.max(...ms)/Math.min(...ms);
  if(mr>1.8)continue;
  if(sc<bs&&sc<0.4){bs=sc;best={tl:P[mx],p:[P[o[0]],P[o[1]]]}}
 }
 if(!best)return null;
 const {tl,p}=best,cr=(p[0].x-tl.x)*(p[1].y-tl.y)-(p[0].y-tl.y)*(p[1].x-tl.x);
 return cr>0?{tl,tr:p[0],bl:p[1]}:{tl,tr:p[1],bl:p[0]};
}
function readMatrix(B,w,h,f,ver,useAlign){
 const dim=17+4*ver,sc=dim-7,ms=(Math.hypot(f.tr.x-f.tl.x,f.tr.y-f.tl.y)+Math.hypot(f.bl.x-f.tl.x,f.bl.y-f.tl.y))/2/sc;
 const aff=(u,v)=>[f.tl.x+(u-3.5)*(f.tr.x-f.tl.x)/sc+(v-3.5)*(f.bl.x-f.tl.x)/sc,f.tl.y+(u-3.5)*(f.tr.y-f.tl.y)/sc+(v-3.5)*(f.bl.y-f.tl.y)/sc];
 let map=aff;
 if(ver>=2&&useAlign){
  const [ex,ey]=aff(dim-6.5,dim-6.5),R=Math.round(ms*5),x0=Math.max(0,Math.round(ex-R)),y0=Math.max(0,Math.round(ey-R)),x1=Math.min(w,Math.round(ex+R)),y1=Math.min(h,Math.round(ey+R));
  if(x1-x0>8&&y1-y0>8){
   const sub=new Uint8Array((x1-x0)*(y1-y0));for(let y=y0;y<y1;y++)for(let x=x0;x<x1;x++)sub[(y-y0)*(x1-x0)+(x-x0)]=B[y*w+x];
   const al=findCenters(sub,x1-x0,y1-y0,[1,1,1,1,1],0.7,1);
   if(al.length){al.sort((a,b)=>Math.hypot(a.x+x0-ex,a.y+y0-ey)-Math.hypot(b.x+x0-ex,b.y+y0-ey));
    const a=al[0],ax=a.x+x0,ay=a.y+y0;
    if(Math.hypot(ax-ex,ay-ey)<ms*4){const H=homog([[3.5,3.5],[dim-3.5,3.5],[3.5,dim-3.5],[dim-6.5,dim-6.5]],[[f.tl.x,f.tl.y],[f.tr.x,f.tr.y],[f.bl.x,f.bl.y],[ax,ay]]);if(H)map=H}}}
 }
 const o=mkBase(ver),mods=[];
 const samp=(u,v)=>{let s=0;const d=0.22,pts=[[0,0],[d,0],[-d,0],[0,d],[0,-d]];for(const [a,b] of pts){const [x,y]=map(u+a,v+b),xi=Math.round(x),yi=Math.round(y);if(xi>=0&&yi>=0&&xi<w&&yi<h)s+=B[yi*w+xi]}return s>=3?1:0};
 for(let y=0;y<dim;y++){mods.push(new Uint8Array(dim));for(let x=0;x<dim;x++)mods[y][x]=samp(x+0.5,y+0.5)}
 return {mods,fn:o.fn,dim};
}
function decodeMatrix(mods,fn,dim,ver){
 // formato
 const f1=[];for(let i=0;i<=5;i++)f1.push(mods[i][8]);f1.push(mods[7][8],mods[8][8],mods[8][7]);for(let i=9;i<15;i++)f1.push(mods[8][14-i]);
 const f2=[];for(let i=0;i<8;i++)f2.push(mods[8][dim-1-i]);for(let i=8;i<15;i++)f2.push(mods[dim-15+i][8]);
 const toN=a=>a.reduce((s,b,i)=>s|(b<<i),0),r1=toN(f1),r2=toN(f2);
 let best=null,bd=99;const pc=x=>{let c=0;while(x){c+=x&1;x>>>=1}return c};
 for(const e of ['L','M'])for(let m=0;m<8;m++){const w=fmtBits(e,m),d=Math.min(pc(w^r1),pc(w^r2));if(d<bd){bd=d;best={e,m}}}
 if(!best||bd>3)return {err:'format'};
 const m2=mods.map(r=>Uint8Array.from(r));
 for(let y=0;y<dim;y++)for(let x=0;x<dim;x++)if(!fn[y][x]&&MASKS[best.m](x,y))m2[y][x]^=1;
 const t=TBL[best.e][ver],out=new Uint8Array(t[0]);
 zigzag(dim,fn,(x,y,i)=>{if(i<out.length*8&&m2[y][x])out[i>>>3]|=0x80>>>(i&7)});
 const nb=t[2]+t[4],dl=[];for(let i=0;i<nb;i++)dl.push(i<t[2]?t[3]:t[5]);
 const dB=dl.map(l=>new Array(l)),eB=[];for(let i=0;i<nb;i++)eB.push(new Array(t[1]));
 let p=0;const maxd=Math.max(...dl);
 for(let i=0;i<maxd;i++)for(let b=0;b<nb;b++)if(i<dl[b])dB[b][i]=out[p++];
 for(let i=0;i<t[1];i++)for(let b=0;b<nb;b++)eB[b][i]=out[p++];
 const data=[];
 for(let b=0;b<nb;b++){const r=rsDec(dB[b].concat(eB[b]),t[1]);if(!r)return {err:'rs'};for(let i=0;i<dl[b];i++)data.push(r[i])}
 return {data,ver};
}
const ALNUM='0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ $%*+-./:';
function parseData(data,ver){
 const bits=[];data.forEach(b=>{for(let i=7;i>=0;i--)bits.push((b>>i)&1)});
 let p=0;const rd=n=>{let v=0;for(let i=0;i<n;i++)v=(v<<1)|(bits[p++]||0);return v};
 const bytes=[];let txt='';
 const cc=ver<10?{1:10,2:9,4:8}:{1:12,2:11,4:16};
 while(p+4<=bits.length){
  const mode=rd(4);if(mode===0)break;
  if(mode===7){const f=rd(8);p+=f<128?0:f<192?8:16;continue}
  if(!cc[mode])return null;
  const n=rd(cc[mode]);
  if(mode===4){for(let i=0;i<n;i++)bytes.push(rd(8))}
  else if(mode===2){let s='';for(let i=0;i<n>>1;i++){const v=rd(11);s+=ALNUM[Math.floor(v/45)]+ALNUM[v%45]}if(n&1)s+=ALNUM[rd(6)];bytes.push(...utf8(s))}
  else if(mode===1){let s='';let k=n;while(k>=3){s+=String(rd(10)).padStart(3,'0');k-=3}if(k===2)s+=String(rd(7)).padStart(2,'0');else if(k===1)s+=String(rd(4));bytes.push(...utf8(s))}
 }
 try{return new TextDecoder('utf-8',{fatal:true}).decode(new Uint8Array(bytes))}catch(e){return String.fromCharCode(...bytes)}
}
function tryDecode(B,w,h){
 const c=findCenters(B,w,h,[1,1,3,1,1],0.5,2);
 if(c.length<3)return null;
 const f=pickTriple(c);if(!f)return null;
 const dist=(Math.hypot(f.tr.x-f.tl.x,f.tr.y-f.tl.y)+Math.hypot(f.bl.x-f.tl.x,f.bl.y-f.tl.y))/2;
 const ms=Math.min(f.tl.m,f.tr.m,f.bl.m),est=dist/ms+7;
 const vs=[];for(let v=1;v<=MAXV;v++)vs.push(v);
 vs.sort((a,b)=>Math.abs(17+4*a-est)-Math.abs(17+4*b-est));
 for(const v of vs)for(const al of v>=2?[false,true]:[false]){
  const r=readMatrix(B,w,h,f,v,al),d=decodeMatrix(r.mods,r.fn,r.dim,v);
  if(d&&d.data){const t=parseData(d.data,v);if(t!==null)return t}
 }
 return null;
}
function decode(rgba,w,h){
 const B=binarize(rgba,w,h);
 let t=tryDecode(B,w,h);if(t!==null)return t;
 const I=new Uint8Array(B.length);for(let i=0;i<B.length;i++)I[i]=1-B[i];
 return tryDecode(I,w,h);
}
return {make,svg,canvas,decode,MAXV};
})();
