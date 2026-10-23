import { initializeApp } from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-app.js';
import { initializeAuth, indexedDBLocalPersistence, browserLocalPersistence, browserPopupRedirectResolver, onAuthStateChanged,
  signInWithEmailAndPassword, createUserWithEmailAndPassword, sendPasswordResetEmail, sendEmailVerification,
  GoogleAuthProvider, signInWithPopup, signOut } from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-auth.js';
import { initializeFirestore, persistentLocalCache, persistentMultipleTabManager, doc, collection, setDoc, getDoc, getDocs,
  deleteDoc, onSnapshot, writeBatch, serverTimestamp, query, orderBy, limit, where, increment } from 'https://www.gstatic.com/firebasejs/12.19.0/firebase-firestore.js';
import { firebaseConfig } from './firebase-config.js';


const pad=n=>String(n).padStart(2,'0');
const keyOf=d=>`${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())}`;
const todayKey=()=>keyOf(new Date());
const monthOf=k=>String(k||'').slice(0,7);
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const num=v=>{const n=parseFloat(String(v??'').replace(/[,\s฿]/g,''));return isFinite(n)?Math.round(n*100)/100:NaN};
const r2=n=>Math.round(n*100)/100;
const money=n=>(n<-0.004?'−':'')+Math.abs(r2(n)).toLocaleString('th-TH',{minimumFractionDigits:0,maximumFractionDigits:2});
const thDay=k=>new Date(k+'T00:00:00').toLocaleDateString('th-TH',{weekday:'short',day:'numeric',month:'short'});
const thShort=k=>new Date(k+'T00:00:00').toLocaleDateString('th-TH',{day:'numeric',month:'short',year:'2-digit'});
const thMonth=mk=>new Date(mk+'-01T00:00:00').toLocaleDateString('th-TH',{month:'long',year:'numeric'});
const addMonth=(mk,d)=>{const[y,m]=mk.split('-').map(Number);const dt=new Date(y,m-1+d,1);return `${dt.getFullYear()}-${pad(dt.getMonth()+1)}`};
const rid=()=>Date.now().toString(36)+Math.random().toString(36).slice(2,8);
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const isObj=v=>v!==null&&typeof v==='object'&&!Array.isArray(v);
function deepMerge(a,b){const out=isObj(a)?{...a}:{};for(const[k,v]of Object.entries(b||{})){out[k]=isObj(v)?deepMerge(out[k],v):v}return out}
const LS={get(k,d){try{const v=localStorage.getItem(k);return v?JSON.parse(v):d}catch(e){return d}},set(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}}};
const byId=id=>document.getElementById(id);

const TYPE={in:'รายรับ',out:'รายจ่าย',draw:'ถอนเงินเจ้าของ',move:'ย้ายเงิน'};
const DEFAULTS={shop:'ขนมบ้านเพลง-พระแท่น',open:{},
  accs:[{id:'cash',n:'เงินสด'},{id:'scb',n:'SCB'},{id:'ktb',n:'KTB'}],
  cats:{
  in:[{n:'ขายหน้าร้าน'},{n:'ขายออนไลน์/เดลิเวอรี'},{n:'ออเดอร์จัดเลี้ยง/งานบุญ'},{n:'ขายส่ง'},{n:'รายได้อื่น'},{n:'เจ้าของลงเงินเพิ่ม',pl:false}],
  out:[{n:'วัตถุดิบ',g:'cogs'},{n:'บรรจุภัณฑ์',g:'cogs'},{n:'เทียน',g:'cogs'},{n:'เมล็ดกาแฟ',g:'cogs'},{n:'ค่าน้ำแข็ง',g:'cogs'},{n:'ค่าแรง'},{n:'ค่าแก๊ส'},{n:'ซ่อมบำรุง'},{n:'ค่าเช่า'},{n:'ค่าน้ำ-ค่าไฟ'},{n:'อื่น ๆ'}]}};
const accName=id=>(M&&M.s.accs.find(a=>a.id===id)?.n)||({cash:'เงินสด',bank:'บัญชีธนาคาร'}[id])||id||'';
const visAccs=()=>M.s.accs.filter(a=>!a.h);

let ui=Object.assign({tab:'home',filter:'all',side:'in',smode:'in',sq:''},LS.get('bp_ui',{}));
ui.month=monthOf(todayKey());
let cache={days:{},contacts:{},settings:null,stock:{},stockcost:{},count:null};
let fb=null,user=null,role=null,canWrite=false,M=null,unsubs=[],memberUnsub=null,pending=false,fromCache=true,loaded=false,gateMode='';
let es=null,ps=null,ss=null;
const isOwner=()=>role==='owner';
// staff permissions (owners can do everything). Staff without a perms map can only take stock out.
let perms=null;
const PERMS={stockUse:'เบิกใช้วัตถุดิบ',stockIn:'รับของเข้าสต็อก',stockCount:'นับสต็อกประจำเดือน',acct:'บันทึกรายรับ-รายจ่ายและค้างชำระ'};
const PERM_SHORT={stockUse:'เบิกใช้',stockIn:'รับเข้า',stockCount:'นับสต็อก',acct:'บัญชี'};
const DEFAULT_PERMS={stockUse:true};
const can=p=>isOwner()||!!(perms&&perms[p]);
const MODE_PERM={in:'stockIn',use:'stockUse',count:'stockCount'};
const canMode=m=>can(MODE_PERM[m]);
const stockModes=()=>['in','use','count'].filter(canMode);
const anyStock=()=>stockModes().length>0;
const allowedTabs=()=>isOwner()?['home','list','stock','debt','report']:[...(can('acct')?['home','list']:[]),...(anyStock()?['stock']:[]),...(can('acct')?['debt']:[])];
const cleanPerms=o=>{const r={};for(const k of Object.keys(PERMS))if(o&&o[k])r[k]=true;return r};

/* ---------- model ---------- */
function build(){
  const days=cache.days,contacts=cache.contacts,settings=cache.settings||{};
  let accs=Array.isArray(settings.accs)&&settings.accs.length?settings.accs.filter(a=>a&&a.id):DEFAULTS.accs;
  if(!accs.some(a=>a.id==='cash'))accs=[{id:'cash',n:'เงินสด'},...accs];
  accs=accs.map(a=>a.id==='cash'?{...a,h:false}:a);
  const s={shop:settings.shop||DEFAULTS.shop,open:{...(settings.open||{})},accs,openDate:settings.openDate||'',
    closed:Array.isArray(settings.closed)?settings.closed.filter(x=>typeof x==='string'):[],
    cats:{in:Array.isArray(settings.cats?.in)?settings.cats.in:DEFAULTS.cats.in,out:Array.isArray(settings.cats?.out)?settings.cats.out:DEFAULTS.cats.out}};
  const entries=[];
  for(const[d,doc_]of Object.entries(days)){
    for(const[id,e]of Object.entries(doc_?.entries||{})){
      if(!e||e.del||!e.t)continue;
      entries.push({...e,id,d,amt:+e.amt||0});
    }
  }
  entries.sort((a,b)=>b.d.localeCompare(a.d)||(b.at||0)-(a.at||0));
  const cs={};for(const[id,c]of Object.entries(contacts)){if(c&&!c.del&&c.name)cs[id]={...c,id}}
  M={entries,contacts:cs,s,configured:!!cache.settings};
}
const catInfo=(t,n)=>(M.s.cats[t]||[]).find(c=>c.n===n)||{n};
const visCats=t=>(M.s.cats[t]||[]).filter(c=>!c.h);
const hasCat=t=>t==='in'||t==='out';
const isClosed=d=>!!d&&M.s.closed.includes(monthOf(d));
const closedMsg=d=>`${thMonth(monthOf(d))} ปิดงวดแล้ว เปิดงวดได้ในหน้าตั้งค่า`;
const defTo=from=>(visAccs().find(a=>a.id!==from)||{}).id||'cash';
const paid=e=>Object.values(e.pays||{}).reduce((s,p)=>s+(p?(+p.amt||0):0),0);
const due=e=>e.credit&&(e.t==='in'||e.t==='out')?Math.max(0,r2(e.amt-paid(e))):0;
function flows(){
  const f=[];
  for(const e of M.entries){
    if(e.imp)continue;
    if(e.t==='move'){f.push({date:e.d,acc:e.acc,amt:-e.amt},{date:e.d,acc:e.to,amt:e.amt});continue}
    if(e.t==='draw'){f.push({date:e.d,acc:e.acc||'cash',amt:-e.amt,draw:true});continue}
    const sg=e.t==='in'?1:-1;
    if(!e.credit)f.push({date:e.d,acc:e.acc||'cash',amt:sg*e.amt});
    else for(const p of Object.values(e.pays||{}))if(p)f.push({date:p.date,acc:p.acc||'cash',amt:sg*(+p.amt||0)});
  }
  return f;
}
function balances(){const b={};for(const a of M.s.accs)b[a.id]=+M.s.open[a.id]||0;for(const x of flows())b[x.acc]=(b[x.acc]||0)+x.amt;return b}
function shownAccs(b){return M.s.accs.filter(a=>!a.h||Math.abs(b[a.id]||0)>0.004)}
function pnl(from,to){
  const r={inc:{},cogs:{},opex:{},owner:{in:0,out:0},I:0,C:0,O:0,draw:0,drawBy:{}};
  for(const e of M.entries){
    if(e.t==='move'||e.d<from||e.d>to)continue;
    if(e.t==='draw'){r.draw+=e.amt;if(!e.imp)r.drawBy[e.acc]=(r.drawBy[e.acc]||0)+e.amt;continue}
    const c=catInfo(e.t,e.cat);
    if(c.pl===false){r.owner[e.t]+=e.amt;continue}
    if(e.t==='in'){r.inc[e.cat]=(r.inc[e.cat]||0)+e.amt;r.I+=e.amt}
    else if(c.g==='cogs'){r.cogs[e.cat]=(r.cogs[e.cat]||0)+e.amt;r.C+=e.amt}
    else{r.opex[e.cat]=(r.opex[e.cat]||0)+e.amt;r.O+=e.amt}
  }
  r.G=r.I-r.C;r.N=r.G-r.O;return r;
}
const mRange=mk=>[mk+'-01',mk+'-31'];

/* ---------- views ---------- */
let renderQueued=false;
function render(){
  if(!role)return;
  build();renderStatus();
  byId('shopName').textContent=M.s.shop;
  const tabs=allowedTabs();if(!tabs.includes(ui.tab))ui.tab=tabs[0]||'none';
  const ae=document.activeElement,aid=ae&&ae.id&&byId('view').contains(ae)?ae.id:null,sel=aid?[ae.selectionStart,ae.selectionEnd]:null;
  byId('view').innerHTML=!loaded&&ui.tab!=='none'?`<div class="empty"><b>กำลังโหลดบัญชี</b><p>ครั้งแรกต้องต่ออินเทอร์เน็ต หลังจากนั้นเปิดได้แม้ไม่มีเน็ต</p></div>`
    :ui.tab==='none'?`<div class="empty"><b>ยังไม่ได้รับมอบหน้าที่</b><p>ให้เจ้าของร้านเปิดสิทธิ์ให้ในหน้าตั้งค่า → ผู้ใช้งานและสิทธิ์</p></div>`
    :({home:isOwner()?vHome:vStaffHome,list:vList,stock:vStock,debt:vDebt,report:vReport}[ui.tab]||vHome)();
  if(aid){const n=byId(aid);if(n){n.focus();try{if(sel&&sel[0]!=null)n.setSelectionRange(sel[0],sel[1])}catch(e){}}}
  document.querySelectorAll('.tab').forEach(t=>{t.setAttribute('aria-current',t.dataset.tab===ui.tab?'page':'false');t.hidden=!tabs.includes(t.dataset.tab)});
  byId('tabgrid').style.gridTemplateColumns=`repeat(${Math.max(1,tabs.length)},1fr)`;byId('app').querySelector('.tabbar').hidden=tabs.length<2;
  const fab=byId('fab');fab.hidden=!canWrite||(ui.tab==='stock'?!anyStock():!can('acct'));
  if(ui.tab==='stock'){if(fab.dataset.act!=='st-scan'){fab.dataset.act='st-scan';fab.innerHTML=ICON_SCAN;fab.setAttribute('aria-label','สแกนบาร์โค้ด')}}
  else if(fab.dataset.act!=='add'){fab.dataset.act='add';fab.textContent='+';fab.setAttribute('aria-label','บันทึกรายการใหม่')}
}
function schedule(){if(renderQueued)return;renderQueued=true;requestAnimationFrame(()=>{renderQueued=false;render()})}
function renderStatus(){
  const el=byId('sync');let cls='ok',txt='ซิงก์แล้ว';
  if(navigator.onLine===false){cls='warn';txt=pending?'ออฟไลน์ · รอส่ง':'ออฟไลน์'}
  else if(pending){cls='warn';txt='กำลังส่งข้อมูล'}
  else if(fromCache){cls='mute';txt='กำลังเชื่อมต่อ'}
  el.className='pill '+cls;el.textContent=txt;
}
function vStaffHome(){
  const t=todayKey(),mine=M.entries.filter(e=>e.d===t);
  return `<section class="hero"><span class="eyebrow">วันนี้ · ${esc(thDay(t))}</span>
    <span class="big">${mine.length}<span class="unit">รายการ</span></span><span class="hero-sub">บันทึกแล้ววันนี้ กดปุ่ม + เพื่อเพิ่มรายการ</span></section>
  <section class="day"><div class="row-head"><h2>รายการวันนี้</h2></div>
    ${mine.length?`<div class="list">${mine.map(rowHtml).join('')}</div>`:emptyStart()}</section>`;
}
function rowHtml(e){
  const title=e.t==='move'?`${accName(e.acc)} → ${accName(e.to)}`:e.t==='draw'?'ถอนเงินเจ้าของ':e.cat;
  const who=e.cid&&M.contacts[e.cid]?M.contacts[e.cid].name:'';
  const d=due(e);
  const tag=e.imp?'<span class="chip warn">ยอดยกมา</span>':e.credit&&(e.t==='in'||e.t==='out')?(d>0?`<span class="chip warn">ค้าง ${money(d)}</span>`:`<span class="chip ok">ชำระครบ</span>`):'';
  const where=e.t==='move'?'ย้ายเงิน':e.t==='draw'?'จาก '+accName(e.acc):e.credit?'เงินเชื่อ':accName(e.acc);
  const sub=[who,e.note].filter(Boolean).join(' · ')||where;
  const sign=e.t==='in'?'+':e.t==='move'?'':'−';
  return `<button class="row" data-act="edit" data-id="${esc(e.id)}" data-d="${esc(e.d)}">
    <span class="dot ${e.t}"></span>
    <span class="main"><span class="t">${esc(title)}</span><span class="s"><span>${esc(sub)}</span>${tag}</span></span>
    <span class="amt ${e.t}">${sign}${money(e.amt)}</span></button>`;
}
function chart(mk){
  const[y,m]=mk.split('-').map(Number);const n=new Date(y,m,0).getDate();
  const I=Array(n).fill(0),E=Array(n).fill(0);
  for(const e of M.entries){
    if((e.t!=='in'&&e.t!=='out')||monthOf(e.d)!==mk||catInfo(e.t,e.cat).pl===false)continue;
    const i=+e.d.slice(8)-1;(e.t==='in'?I:E)[i]+=e.amt;
  }
  const max=Math.max(1,...I,...E),W=n*12,H=80,t=todayKey(),ti=monthOf(t)===mk?+t.slice(8)-1:-1;
  let bars='';
  for(let i=0;i<n;i++){const hi=I[i]/max*H,he=E[i]/max*H;
    bars+=`<rect class="b-in" x="${i*12+1.5}" y="${(H-hi).toFixed(1)}" width="4.5" height="${hi.toFixed(1)}"/><rect class="b-out" x="${i*12+6}" y="${(H-he).toFixed(1)}" width="4.5" height="${he.toFixed(1)}"/>`}
  return `<div class="chart"><svg viewBox="0 0 ${W} ${H+1}" preserveAspectRatio="none" role="img" aria-label="รายรับและรายจ่ายรายวันของ${esc(thMonth(mk))}">
    ${ti>=0?`<rect class="b-today" x="${ti*12}" y="0" width="12" height="${H}"/>`:''}${bars}
    <line class="b-base" x1="0" x2="${W}" y1="${H+.5}" y2="${H+.5}"/></svg>
    <div class="axis"><span>1</span><span>${Math.ceil(n/2)}</span><span>${n}</span></div>
    <div class="legend"><span><i class="k in"></i>รายรับ</span><span><i class="k out"></i>รายจ่าย</span>${ti>=0?'<span>แถบเทา = วันนี้</span>':''}</div></div>`;
}
function emptyStart(){
  return `<div class="empty"><b>ยังไม่มีรายการ</b><p>กดปุ่ม + มุมขวาล่าง เพื่อบันทึกยอดขายหรือค่าใช้จ่ายแรกของร้าน</p></div>`;
}
function compareHtml(t){
  const mk=monthOf(t),pk=addMonth(mk,-1),day=+t.slice(8);
  const[py,pmn]=pk.split('-').map(Number),plen=new Date(py,pmn,0).getDate(),pd=Math.min(day,plen);
  const cur=pnl(mk+'-01',t),prev=pnl(pk+'-01',`${pk}-${pad(pd)}`);
  if(!prev.I&&!prev.C&&!prev.O&&!prev.draw)return '';
  const rows=[['รายรับ',cur.I,prev.I,1],['รายจ่าย',cur.C+cur.O,prev.C+prev.O,-1],['กำไร',cur.N,prev.N,1],['ถอนเงินเจ้าของ',cur.draw,prev.draw,0]];
  const chg=(c,p,good)=>{if(!p)return '<span class="muted">–</span>';const x=Math.round((c-p)/Math.abs(p)*1000)/10;
    const cls=good===0||x===0?'muted':(x>0)===(good>0)?'in':'out';return `<span class="${cls}">${x>0?'+':''}${x}%</span>`};
  return `<div><div class="grp">เทียบช่วงเดียวกันเดือนก่อน (1–${pd} ${esc(new Date(pk+'-01T00:00:00').toLocaleDateString('th-TH',{month:'short'}))})</div>
    <div style="overflow-x:auto"><table class="tbl"><thead><tr><th></th><th>เดือนนี้</th><th>เดือนก่อน</th><th>เปลี่ยน</th></tr></thead><tbody>
    ${rows.map(([l,c,p,g])=>`<tr><td>${l}</td><td>${money(c)}</td><td class="muted">${money(p)}</td><td>${chg(c,p,g)}</td></tr>`).join('')}
    </tbody></table></div>
    ${M.s.openDate&&M.s.openDate>=pk+'-01'&&M.s.openDate<`${pk}-${pad(pd)}`?`<span class="hint">ข้อมูลเดือนก่อนเริ่มบันทึกหลังวันที่ ${esc(thShort(M.s.openDate))} จึงยังเทียบได้ไม่เต็มช่วง</span>`:''}</div>`;
}
function vHome(){
  const t=todayKey(),mk=monthOf(t),b=balances(),pt=pnl(t,t),pm=pnl(...mRange(mk));
  const ar=M.entries.filter(e=>e.t==='in').reduce((s,e)=>s+due(e),0);
  const ap=M.entries.filter(e=>e.t==='out').reduce((s,e)=>s+due(e),0);
  return `
  ${!M.configured&&canWrite?`<section class="card start"><h2>เริ่มต้นใช้งาน</h2><p>ใส่ยอดเงินสดในลิ้นชักและเงินในบัญชีที่มีอยู่ตอนนี้ เพื่อให้ยอดคงเหลือตรงกับของจริง</p><div><button class="btn sm" data-act="settings">ตั้งยอดเงินตั้งต้น</button></div></section>`:''}
  <section class="hero">
    <span class="eyebrow">วันนี้ · ${esc(thDay(t))}</span>
    <span class="big">${money(pt.N)}<span class="unit">บาท</span></span>
    <span class="hero-sub">กำไรวันนี้ (รายรับ หัก รายจ่าย)</span>
    <div class="pair"><div><span class="lbl">รายรับ</span><span class="v">${money(pt.I)}</span></div><div><span class="lbl">รายจ่าย</span><span class="v">${money(pt.C+pt.O)}</span></div></div>
  </section>
  <section class="card tight">
    <div class="row-head"><h2>เงินคงเหลือ</h2><span class="v">${money(Object.values(b).reduce((s,x)=>s+x,0))}</span></div>
    ${shownAccs(b).map(a=>`<div class="ln"><span>${esc(a.n)}</span><span class="${(b[a.id]||0)<0?'neg':''}">${money(b[a.id]||0)}</span></div>`).join('')}
  </section>
  ${(ar>0||ap>0)?`<section class="grid2">
    <button class="tile tap" data-act="debt" data-side="in"><span class="lbl">ลูกค้าค้างจ่ายร้าน</span><span class="v in">${money(ar)}</span><span class="go">ดูรายชื่อ</span></button>
    <button class="tile tap" data-act="debt" data-side="out"><span class="lbl">ร้านค้างจ่าย</span><span class="v out">${money(ap)}</span><span class="go">ดูรายชื่อ</span></button></section>`:''}
  <section class="card">
    <div class="row-head"><h2>${esc(thMonth(mk))}</h2><button class="link" data-act="tab" data-tab="report">ดูงบกำไรขาดทุน</button></div>
    <div class="pair3"><div><span class="lbl">รายรับ</span><b class="in">${money(pm.I)}</b></div><div><span class="lbl">รายจ่าย</span><b class="out">${money(pm.C+pm.O)}</b></div><div><span class="lbl">กำไร</span><b class="${pm.N<0?'neg':''}">${money(pm.N)}</b></div></div>
    ${pm.draw?`<div class="ln"><span class="draw">ถอนเงินเจ้าของเดือนนี้</span><span class="draw">${money(pm.draw)}</span></div>`:''}
    ${compareHtml(t)}
    ${chart(mk)}
  </section>
  <section class="day">
    <div class="row-head"><h2>รายการล่าสุด</h2>${M.entries.length?`<button class="link" data-act="tab" data-tab="list">ดูทั้งหมด</button>`:''}</div>
    ${M.entries.length?`<div class="list">${M.entries.slice(0,6).map(rowHtml).join('')}</div>`:emptyStart()}
  </section>`;
}
function monthNav(){
  return `<div class="mnav"><button data-act="month" data-d="-1" aria-label="เดือนก่อน">‹</button><b>${esc(thMonth(ui.month))}</b><button data-act="month" data-d="1" aria-label="เดือนถัดไป">›</button></div>`;
}
function vList(){
  const mk=ui.month,p=pnl(...mRange(mk));
  const es_=M.entries.filter(e=>monthOf(e.d)===mk&&(ui.filter==='all'||e.t===ui.filter)&&(isOwner()||e.t!=='draw'));
  const groups={};for(const e of es_)(groups[e.d]=groups[e.d]||[]).push(e);
  const days=Object.entries(groups);
  return `${monthNav()}
  <div class="seg wrap">${[['all','ทั้งหมด'],['in','รายรับ'],['out','รายจ่าย'],['draw','ถอนเงิน'],['move','ย้ายเงิน']].filter(([k])=>isOwner()||k!=='draw').map(([k,l])=>`<button data-act="filter" data-v="${k}" aria-pressed="${ui.filter===k}">${l}</button>`).join('')}</div>
  ${isOwner()?`<div class="sum3"><div><span class="lbl">รายรับ</span><b class="in">${money(p.I)}</b></div><div><span class="lbl">รายจ่าย</span><b class="out">${money(p.C+p.O)}</b></div><div><span class="lbl">กำไร</span><b class="${p.N<0?'neg':''}">${money(p.N)}</b></div></div>
  ${p.draw?`<div class="note">ถอนเงินเจ้าของเดือนนี้ ${money(p.draw)} บาท (ไม่นับเป็นรายจ่าย)</div>`:''}`:''}
  ${days.length?days.map(([d,arr])=>{
    const di=arr.filter(e=>e.t==='in').reduce((s,e)=>s+e.amt,0),dout=arr.filter(e=>e.t==='out').reduce((s,e)=>s+e.amt,0);
    return `<section class="day"><div class="day-head"><span>${esc(thDay(d))}</span>${isOwner()?`<span><span class="in">+${money(di)}</span> <span class="out">−${money(dout)}</span></span>`:''}</div><div class="list">${arr.map(rowHtml).join('')}</div></section>`;
  }).join(''):`<div class="empty"><b>ไม่มีรายการ</b><p>ยังไม่มี${ui.filter==='all'?'รายการ':TYPE[ui.filter]}ใน${esc(thMonth(mk))}</p></div>`}`;
}
function vDebt(){
  const s=ui.side,today=todayKey();
  const open=M.entries.filter(e=>e.t===s&&due(e)>0);
  const total=open.reduce((a,e)=>a+due(e),0);
  const by={};for(const e of open){const k=e.cid&&M.contacts[e.cid]?e.cid:'_';(by[k]=by[k]||[]).push(e)}
  const sum=arr=>arr.reduce((x,e)=>x+due(e),0);
  const keys=Object.keys(by).sort((a,b)=>sum(by[b])-sum(by[a]));
  return `
  <div class="seg">${[['in','ลูกค้าค้างจ่ายร้าน'],['out','ร้านค้างจ่าย']].map(([k,l])=>`<button data-act="side" data-v="${k}" aria-pressed="${s===k}">${l}</button>`).join('')}</div>
  <section class="card tight"><span class="lbl">${s==='in'?'ยอดที่ร้านรอรับ (ลูกหนี้)':'ยอดที่ร้านต้องจ่าย (เจ้าหนี้)'}</span><span class="big ${s}" style="font-size:30px">${money(total)}<span class="unit">บาท</span></span></section>
  ${keys.length?keys.map(k=>{
    const c=M.contacts[k],arr=by[k];
    return `<section class="day"><div class="day-head"><span>${esc(c?c.name:'ไม่ระบุชื่อ')}${c?.phone?` <span class="muted">· ${esc(c.phone)}</span>`:''}</span><span class="${s}">${money(sum(arr))}</span></div>
    <div class="list">${arr.map(e=>{const late=e.due&&e.due<today,pd=paid(e);
      return `<div class="drow"><div class="main"><span class="t">${esc(e.cat)} · ${money(e.amt)}</span>
      <span class="s"><span>${esc(thShort(e.d))}${e.due?` · ครบกำหนด ${esc(thShort(e.due))}`:''}${pd?` · จ่ายแล้ว ${money(pd)}`:''}</span>${late?'<span class="chip bad">เลยกำหนด</span>':''}</span></div>
      <div class="rem"><b class="${s}">${money(due(e))}</b>${canWrite?`<button class="btn sm" data-act="pay" data-id="${esc(e.id)}" data-d="${esc(e.d)}">${s==='in'?'รับเงิน':'จ่ายเงิน'}</button>`:''}</div></div>`}).join('')}</div></section>`;
  }).join(''):`<div class="empty"><b>ไม่มียอดค้าง</b><p>${s==='in'?'ถ้าลูกค้าซื้อเชื่อ ให้บันทึกรายรับแล้วเลือก "ลูกค้าค้าง"':'ถ้าซื้อวัตถุดิบแบบเครดิต ให้บันทึกรายจ่ายแล้วเลือก "ค้างจ่าย"'}</p></div>`}`;
}
function vReport(){
  const mk=ui.month,p=pnl(...mRange(mk));
  const lines=obj=>Object.entries(obj).sort((a,b)=>b[1]-a[1]).map(([k,v])=>`<div class="ln"><span>${esc(k)}</span><span>${money(v)}</span></div>`).join('')||'<div class="ln muted"><span>ไม่มีรายการ</span><span>0</span></div>';
  const pct=x=>p.I?(Math.round(x/p.I*1000)/10)+'%':'–';
  const cin={},cout={};
  for(const x of flows()){if(monthOf(x.date)!==mk)continue;if(x.amt>=0)cin[x.acc]=(cin[x.acc]||0)+x.amt;else cout[x.acc]=(cout[x.acc]||0)-x.amt}
  const tAccs=M.s.accs.filter(a=>!a.h||cin[a.id]||cout[a.id]);
  const sumv=o=>Object.values(o).reduce((s,x)=>s+x,0);
  const y=mk.slice(0,4),py=pnl(y+'-01-01',y+'-12-31'),TH=1800000,prog=Math.min(100,py.I/TH*100),flat=py.I*0.6,real=py.C+py.O;
  return `${monthNav()}
  <section class="card"><div><h2>งบกำไรขาดทุน</h2><span class="muted small">${esc(thMonth(mk))} · บันทึกตามวันที่ขายหรือซื้อ</span></div>
    <div><div class="grp">รายได้จากการขาย</div>${lines(p.inc)}<div class="ln tot"><span>รวมรายได้</span><span>${money(p.I)}</span></div>
    <div class="grp">ต้นทุนขาย</div>${lines(p.cogs)}<div class="ln tot"><span>กำไรขั้นต้น</span><span>${money(p.G)}</span></div>
    <div class="grp">ค่าใช้จ่ายดำเนินงาน</div>${lines(p.opex)}<div class="ln tot"><span>รวมค่าใช้จ่าย</span><span>${money(p.O)}</span></div>
    <div class="ln net ${p.N<0?'neg':''}"><span>กำไรสุทธิ</span><span>${money(p.N)}</span></div>
    ${p.draw?`<div class="ln draw"><span>หัก ถอนเงินเจ้าของ</span><span>(${money(p.draw)})</span></div>
    <div class="ln tot"><span>กำไรที่เหลือไว้ในร้าน</span><span class="${p.N-p.draw<0?'neg':''}">${money(p.N-p.draw)}</span></div>`:''}</div>
    <span class="muted small">ต้นทุนขายคิดเป็น ${pct(p.C)} ของรายได้ · กำไรสุทธิ ${pct(p.N)}</span>
    ${(p.owner.in||p.owner.out)?`<div class="note">ไม่นับในกำไร: รายรับ ${money(p.owner.in)} บาท (เช่น เจ้าของลงเงินเพิ่ม) · รายจ่าย ${money(p.owner.out)} บาท</div>`:''}
  </section>
  <section class="card"><div><h2>เงินเข้า-ออกจริง</h2><span class="muted small">นับตามวันที่ได้รับหรือจ่ายเงินจริง รวมการรับชำระหนี้ ไม่รวมยอดยกมาจากบัญชีเก่า</span></div>
    <div style="overflow-x:auto"><table class="tbl"><thead><tr><th>ช่องทาง</th><th>เข้า</th><th>ออก</th><th>สุทธิ</th></tr></thead><tbody>
    ${tAccs.map(a=>{const i=cin[a.id]||0,o=cout[a.id]||0;return `<tr><td>${esc(a.n)}</td><td class="in">${money(i)}</td><td class="out">${money(o)}</td><td>${money(i-o)}</td></tr>`}).join('')}
    <tr><td><b>รวม</b></td><td class="in"><b>${money(sumv(cin))}</b></td><td class="out"><b>${money(sumv(cout))}</b></td><td><b>${money(sumv(cin)-sumv(cout))}</b></td></tr>
    </tbody></table></div>
    ${p.draw?`<span class="muted small">เงินออกรวมการถอนเงินเจ้าของ ${Object.entries(p.drawBy).map(([k,v])=>`${esc(accName(k))} ${money(v)}`).join(' · ')}</span>`:''}</section>
  <section class="card"><h2>สรุปปี ${+y+543}</h2>
    <div class="ln"><span>รายได้สะสมทั้งปี</span><span>${money(py.I)} บาท</span></div>
    <div class="meter" role="img" aria-label="รายได้เทียบเกณฑ์ VAT ${prog.toFixed(1)}%"><div style="width:${prog}%"></div></div>
    <span class="muted small">รายได้เกิน 1,800,000 บาทต่อปีต้องจดทะเบียน VAT · ตอนนี้ ${prog.toFixed(1)}% ของเกณฑ์</span>
    <div><div class="grp">เทียบวิธีหักค่าใช้จ่าย (ภาษีเงินได้บุคคลธรรมดา)</div>
    <div class="ln"><span>หักตามจริง (ค่าใช้จ่ายที่บันทึก)</span><span>${money(real)}</span></div>
    <div class="ln"><span>หักเหมา 60% ของรายได้</span><span>${money(flat)}</span></div></div>
    <span class="muted small">${py.I?`ปีนี้แบบ${real>flat?'หักตามจริง':'หักเหมา'}หักได้มากกว่า `:''}การหักตามจริงต้องมีใบเสร็จหรือหลักฐานครบ ควรให้นักบัญชีตรวจก่อนยื่น ภ.ง.ด.94 และ ภ.ง.ด.90</span>
  </section>
  ${isOwner()?`<section class="card"><div><h2>ส่งออกข้อมูล</h2><span class="muted small">ไฟล์ CSV เปิดได้ด้วย Excel หรือ Google Sheets ส่งให้สำนักงานบัญชีได้เลย</span></div>
    <div class="btns"><button class="btn" data-act="csv" data-scope="m">${esc(thMonth(mk))}</button><button class="btn" data-act="csv" data-scope="y">ทั้งปี ${+y+543}</button></div></section>`:''}`;
}

/* ---------- sheets ---------- */
function showSheet(html,keep){
  const p=byId('panel'),st=p.scrollTop,ae=document.activeElement,aid=keep&&ae&&ae.id&&p.contains(ae)?ae.id:null,sel=aid?[ae.selectionStart,ae.selectionEnd]:null;
  p.innerHTML=html;byId('sheet').hidden=false;document.body.classList.add('locked');
  p.scrollTop=keep?st:0;
  if(aid){const n=byId(aid);if(n){n.focus({preventScroll:true});try{if(sel&&sel[0]!=null)n.setSelectionRange(sel[0],sel[1])}catch(e){}}}
}
function closeSheet(){stopScan();sa=null;si=null;byId('sheet').hidden=true;byId('panel').innerHTML='';document.body.classList.remove('locked');es=ps=ss=null}

function openEntry(id,d){
  if(id){
    const e=M.entries.find(x=>x.id===id&&x.d===d);if(!e)return;
    es={mode:'edit',id,origDate:d,t:e.t,amt:String(e.amt),cat:e.cat||'',acc:e.acc||'cash',to:e.to||defTo(e.acc||'cash'),date:d,note:e.note||'',credit:!!e.credit,cid:e.cid||'',due:e.due||'',newC:false,cName:'',cPhone:'',confirmDel:false,hasPays:paid(e)>0,ref:e.ref||'',att:e.att||'',rno:e.rno||'',rc:e.rc||'',rcData:'',rcDrop:false,ro:false,roMsg:''};
  }else{
    es={mode:'new',ro:false,roMsg:'',rc:'',rcData:'',rcDrop:false,t:'in',amt:'',cat:'',acc:'cash',to:defTo('cash'),date:todayKey(),note:'',credit:false,cid:'',due:'',newC:false,cName:'',cPhone:'',confirmDel:false};
  }
  if(hasCat(es.t)&&!es.cat)es.cat=visCats(es.t)[0]?.n||'';
  if(es.mode==='edit'){const e0=M.entries.find(x=>x.id===id&&x.d===d);
    if(isClosed(d)){es.ro=true;es.roMsg=closedMsg(d)+' รายการนี้ดูได้อย่างเดียว'}
    else if(!isOwner()&&e0?.by!==user.uid){es.ro=true;es.roMsg='รายการนี้คนอื่นบันทึก พนักงานแก้ไขได้เฉพาะรายการของตัวเอง'}}
  showSheet(entryHtml());
  if(!id)setTimeout(()=>{try{byId('f-amt').focus()}catch(e){}},60);
}
function readEntry(){
  const g=id=>byId(id);
  if(g('f-amt'))es.amt=g('f-amt').value;if(g('f-date'))es.date=g('f-date').value;if(g('f-note'))es.note=g('f-note').value;
  if(g('f-cid'))es.cid=g('f-cid').value;if(g('f-due'))es.due=g('f-due').value;
  if(g('f-cname'))es.cName=g('f-cname').value;if(g('f-cphone'))es.cPhone=g('f-cphone').value;
}
function entryHtml(err={}){
  const t=es.t,kind=t==='in'?'cus':'sup';
  let cats=hasCat(t)?visCats(t):[];
  if(hasCat(t)&&es.cat&&!cats.some(c=>c.n===es.cat))cats=[...cats,{n:es.cat}];
  let accs=visAccs();
  for(const id of [es.acc,es.to])if(id&&!accs.some(a=>a.id===id)&&M.s.accs.some(a=>a.id===id))accs=[...accs,M.s.accs.find(a=>a.id===id)];
  const accBtns=(act,sel,off)=>accs.map(a=>`<button data-act="${act}" data-v="${esc(a.id)}" aria-pressed="${!off&&sel===a.id}">${esc(a.n)}</button>`).join('');
  const cons=Object.values(M.contacts).filter(c=>c.kind===kind).sort((a,b)=>a.name.localeCompare(b.name,'th'));
  const credit=es.credit&&hasCat(t)?`<div class="credit">
    <div class="fld"><span>${t==='in'?'ชื่อลูกค้า':'ชื่อร้านค้าหรือซัพพลายเออร์'}</span>
    ${es.newC||!cons.length?`<input id="f-cname" placeholder="ชื่อ" value="${esc(es.cName)}" maxlength="60" autocomplete="off"><input id="f-cphone" inputmode="tel" placeholder="เบอร์โทร (ไม่ใส่ก็ได้)" value="${esc(es.cPhone)}" maxlength="20">${cons.length?`<button class="link" data-act="e-newc" data-v="0">เลือกจากรายชื่อเดิม</button>`:''}`
    :`<select id="f-cid"><option value="">เลือกชื่อ</option>${cons.map(c=>`<option value="${esc(c.id)}" ${es.cid===c.id?'selected':''}>${esc(c.name)}</option>`).join('')}</select><button class="link" data-act="e-newc" data-v="1">+ เพิ่มชื่อใหม่</button>`}
    </div>${err.c?`<div class="err">${err.c}</div>`:''}
    <label class="fld"><span>กำหนดชำระ (ถ้ามี)</span><input id="f-due" type="date" value="${esc(es.due)}"></label>
    ${es.hasPays?'<span class="small" style="color:var(--sugar)">รายการนี้มีการชำระบางส่วนแล้ว ดูได้ที่หน้า ค้างชำระ</span>':''}</div>`:'';
  return `<div class="sh-head"><h2>${es.mode==='new'?'บันทึกรายการ':'แก้ไขรายการ'}</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
  <div class="seg big3">${[['in','รายรับ'],['out','รายจ่าย'],['draw','ถอนเงิน'],['move','ย้ายเงิน']].filter(([k])=>isOwner()||k!=='draw'||t==='draw').map(([k,l])=>`<button data-act="e-type" data-v="${k}" aria-pressed="${t===k}" class="t-${k}">${l}</button>`).join('')}</div>
  <label class="fld"><span>จำนวนเงิน (บาท)</span><input id="f-amt" class="amt-in t-${t}" inputmode="decimal" autocomplete="off" placeholder="0" value="${esc(es.amt)}"></label>
  ${err.amt?`<div class="err">${err.amt}</div>`:''}
  ${hasCat(t)?`<div class="fld"><span>หมวด</span><div class="chips">${cats.map(c=>`<button data-act="e-cat" data-v="${esc(c.n)}" aria-pressed="${es.cat===c.n}">${esc(c.n)}</button>`).join('')}</div></div>${err.cat?`<div class="err">${err.cat}</div>`:''}`:''}
  ${t==='move'?`<div class="fld"><span>ย้ายจาก</span><div class="seg wrap">${accBtns('e-acc',es.acc)}</div></div>
    <div class="fld"><span>ไปที่</span><div class="seg wrap">${accBtns('e-to',es.to)}</div><span class="hint">เช่น เอาเงินสดไปฝาก SCB หรือโอนจาก KTB ไป SCB ไม่นับเป็นรายรับหรือรายจ่าย</span></div>
    ${err.acc?`<div class="err">${err.acc}</div>`:''}`
  :t==='draw'?`<div class="fld"><span>ถอนจาก</span><div class="seg wrap">${accBtns('e-acc',es.acc)}</div>
    <span class="hint">เงินที่เจ้าของเอาไปใช้ส่วนตัว ยอดเงินในบัญชีจะลดลง แต่ไม่นับเป็นค่าใช้จ่าย กำไรของร้านจึงไม่ลด</span></div>`
  :`<div class="fld"><span>${t==='in'?'รับเงินทาง':'จ่ายเงินทาง'}</span><div class="seg wrap">${accBtns('e-acc',es.acc,es.credit)}<button data-act="e-credit" aria-pressed="${es.credit}">${t==='in'?'ลูกค้าค้าง':'ค้างจ่าย'}</button></div></div>`}
  ${credit}
  <label class="fld"><span>วันที่</span><input id="f-date" type="date" value="${esc(es.date)}"></label>
  ${err.date?`<div class="err">${err.date}</div>`:''}
  <label class="fld"><span>หมายเหตุ</span><input id="f-note" value="${esc(es.note)}" placeholder="${t==='in'?'เช่น ขนมชั้น 20 กล่อง':t==='out'?'เช่น แป้งข้าวเจ้า 5 กก.':t==='draw'?'เช่น ใช้จ่ายในบ้าน':'เช่น ฝากเงินสดเข้าบัญชี'}" maxlength="120" autocomplete="off"></label>
  ${t!=='move'?`<div class="fld"><span>รูปใบเสร็จ</span>
    ${es.rcData?`<div class="rc-row"><img class="thumb" src="${es.rcData}" alt="รูปใบเสร็จที่เลือก">${es.ro?'':'<button class="btn sm" data-act="rc-remove">เอาออก</button>'}</div>`
    :es.rc?`<div class="btns"><button class="btn sm" data-act="rc-view" data-v="${esc(es.rc)}">ดูใบเสร็จ</button>${es.ro?'':'<button class="btn sm" data-act="rc-remove">เอาออก</button>'}</div>`
    :es.ro?'<span class="hint">ไม่มีรูป</span>':`<label class="btn sm filebtn">ถ่ายหรือเลือกรูป<input type="file" id="f-rc" class="vh" accept="image/*"></label>`}</div>`:''}
  ${es.att||es.rno||es.ref?`<div class="hint">${es.rno?`เลขใบเสร็จ ${esc(es.rno)} · `:''}${es.ref?`รหัสเดิม ${esc(es.ref)}`:''}${es.att&&/^https:\/\//.test(es.att)?` · <a href="${esc(es.att)}" target="_blank" rel="noopener">ดูรูปใบเสร็จ</a>`:''}</div>`:''}
  ${es.ro?`<div class="note">${esc(es.roMsg)}</div>`:''}
  <div class="sh-foot">${es.ro?'':es.mode==='edit'?(es.confirmDel?`<button class="btn danger" data-act="e-del-yes">ยืนยันลบ</button><button class="btn ghost" data-act="e-del-no">ไม่ลบ</button>`:`<button class="btn ghost danger-t" data-act="e-del">ลบ</button>`):''}${es.ro?'<button class="btn primary" data-act="close">ปิด</button>':`<button class="btn primary t-${t}" data-act="e-save">บันทึก</button>`}</div>`;
}
function saveEntry(){
  readEntry();
  const err={},amt=num(es.amt);
  if(!(amt>0))err.amt='ใส่จำนวนเงินที่มากกว่า 0';
  if(hasCat(es.t)&&!es.cat)err.cat='เลือกหมวดก่อนบันทึก';
  if(es.t==='move'&&es.acc===es.to)err.acc='เลือกบัญชีต้นทางและปลายทางที่ไม่ซ้ำกัน';
  if(!/^\d{4}-\d{2}-\d{2}$/.test(es.date||''))err.date='เลือกวันที่';
  else if(isClosed(es.date))err.date=closedMsg(es.date);
  if(es.ro)err.date=es.roMsg;
  const kind=es.t==='in'?'cus':'sup',hasCons=Object.values(M.contacts).some(c=>c.kind===kind);
  const useNew=es.newC||!hasCons;
  if(es.credit&&hasCat(es.t)){if(useNew){if(!es.cName.trim())err.c='ใส่ชื่อคนที่ค้างเงิน'}else if(!es.cid)err.c='เลือกชื่อ หรือกดเพิ่มชื่อใหม่'}
  if(Object.keys(err).length){showSheet(entryHtml(err),true);return}
  let cid=es.cid;
  if(es.credit&&hasCat(es.t)&&useNew){cid='c'+rid();enqueue({k:'contact',id:cid,patch:{name:es.cName.trim(),phone:es.cPhone.trim(),kind,at:Date.now()}},false)}
  const now=Date.now();
  const e={t:es.t,amt,note:es.note.trim(),by:user.uid,at:now};
  if(es.t==='move'){e.acc=es.acc;e.to=es.to;e.cat='';e.credit=false;e.cid='';e.due=''}
  else if(es.t==='draw'){e.acc=es.acc;e.to='';e.cat='';e.credit=false;e.cid='';e.due=''}
  else{e.cat=es.cat;e.acc=es.acc;e.credit=!!es.credit;e.cid=es.credit?cid:'';e.due=es.credit?(es.due||''):''}
  if(es.rcData){const rcid='r'+rid();fire(setDoc(doc(fb.db,'receipts',rcid),{data:es.rcData,d:es.date,by:user.uid,at:Date.now()}),'receipt');e.rc=rcid}
  else e.rc=es.rcDrop?'':(es.rc||'');
  if(es.mode==='edit'){
    const o=M.entries.find(x=>x.id===es.id&&x.d===es.origDate);
    e.at=o?.at||now;e.by=o?.by||e.by;e.ed=now;
    for(const k of ['ref','att','rno'])if(o?.[k])e[k]=o[k];
    if(es.origDate===es.date)dayOp(es.date,{[es.id]:e});
    else{if(o?.pays)e.pays=o.pays;if(o?.imp)e.imp=true;dayOp(es.date,{['e'+rid()]:e},false);dayOp(es.origDate,{[es.id]:{del:true,ed:now}})}
    closeSheet();toast('แก้ไขแล้ว');
  }else{
    dayOp(es.date,{['e'+rid()]:e});
    const msg=`บันทึก${TYPE[e.t]} ${money(amt)} บาทแล้ว`;closeSheet();toast(msg);
  }
}

function openPay(id,d){
  const e=M.entries.find(x=>x.id===id&&x.d===d);if(!e)return;
  ps={id,d,amt:String(due(e)),date:todayKey(),acc:'cash',delPid:null};showSheet(payHtml());
}
function readPay(){if(byId('p-amt'))ps.amt=byId('p-amt').value;if(byId('p-date'))ps.date=byId('p-date').value}
function payHtml(err){
  const e=M.entries.find(x=>x.id===ps.id&&x.d===ps.d);
  if(!e)return `<div class="sh-head"><h2>ไม่พบรายการ</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>`;
  const rem=due(e),c=M.contacts[e.cid],verb=e.t==='in'?'รับ':'จ่าย';
  const pays=Object.entries(e.pays||{}).filter(([,p])=>p).sort((a,b)=>String(a[1].date).localeCompare(String(b[1].date)));
  return `<div class="sh-head"><h2>${e.t==='in'?'รับชำระจากลูกค้า':'จ่ายชำระหนี้'}</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
  <section class="card tight">
    <div class="ln"><span><b>${esc(c?.name||'ไม่ระบุชื่อ')}</b></span><span class="muted small">${esc(thShort(e.d))}</span></div>
    <div class="ln"><span>${esc(e.cat)}${e.note?` · <span class="muted">${esc(e.note)}</span>`:''}</span><span>${money(e.amt)}</span></div>
    ${pays.map(([pid,p])=>`<div class="ln small muted"><span>${verb}แล้ว ${esc(thShort(p.date))} · ${esc(accName(p.acc))}</span><span>${money(+p.amt||0)} ${canWrite?(ps.delPid===pid?`<button class="link danger-t" data-act="p-del-yes" data-v="${esc(pid)}">ยืนยันลบ</button>`:`<button class="link" data-act="p-del" data-v="${esc(pid)}">ลบ</button>`):''}</span></div>`).join('')}
    <div class="ln tot"><span>คงค้าง</span><span class="${e.t}">${money(rem)}</span></div>
  </section>
  ${rem>0?`<label class="fld"><span>จำนวนที่${verb}ครั้งนี้ (บาท)</span><input id="p-amt" class="amt-in t-${e.t}" inputmode="decimal" autocomplete="off" value="${esc(ps.amt)}"></label>${err?`<div class="err">${err}</div>`:''}
  <div class="fld"><span>${verb}เงินทาง</span><div class="seg wrap">${visAccs().map(a=>`<button data-act="p-acc" data-v="${esc(a.id)}" aria-pressed="${ps.acc===a.id}">${esc(a.n)}</button>`).join('')}</div></div>
  <label class="fld"><span>วันที่${verb}เงิน</span><input id="p-date" type="date" value="${esc(ps.date)}"></label>
  <div class="sh-foot"><button class="btn ghost" data-act="p-edit">แก้ไขรายการ</button><button class="btn primary t-${e.t}" data-act="p-save">บันทึกการ${verb}เงิน</button></div>`
  :`<div class="sh-foot"><button class="btn ghost" data-act="p-edit">แก้ไขรายการ</button><button class="btn primary" data-act="close">ปิด</button></div>`}`;
}
function savePay(){
  readPay();
  const e=M.entries.find(x=>x.id===ps.id&&x.d===ps.d);if(!e)return closeSheet();
  const rem=due(e),amt=num(ps.amt);
  if(!(amt>0))return showSheet(payHtml('ใส่จำนวนเงินที่มากกว่า 0'),true);
  if(amt>rem+0.001)return showSheet(payHtml(`ยอดค้างเหลือ ${money(rem)} บาท ใส่ไม่เกินนี้`),true);
  if(!/^\d{4}-\d{2}-\d{2}$/.test(ps.date||''))return showSheet(payHtml('เลือกวันที่'),true);
  if(isClosed(ps.date))return showSheet(payHtml(closedMsg(ps.date)),true);
  dayOp(ps.d,{[ps.id]:{pays:{['p'+rid()]:{amt,date:ps.date,acc:ps.acc,by:user.uid,at:Date.now()}}}});
  closeSheet();toast(`บันทึกการ${e.t==='in'?'รับ':'จ่าย'}เงิน ${money(amt)} บาทแล้ว`);
}

function openSettings(){
  ss={shop:M.s.shop,accs:M.s.accs.map(a=>({id:a.id,n:a.n,h:!!a.h,open:String(+M.s.open[a.id]||0)})),
    cats:JSON.parse(JSON.stringify(M.s.cats)),newIn:'',newOut:'',newG:'opex',newAcc:'',cdel:null,
    members:null,invites:null,founder:'',inviteRole:'staff',inviteEmail:'',inviteErr:'',peopleErr:'',rmUid:null,importData:null,importing:''};
  showSheet(setHtml());
  if(isOwner())loadPeople();
}
function accountSection(){
  return `<div class="fld"><span>บัญชีของฉัน</span>
    <div class="list"><div class="drow"><div class="main"><span class="t">${esc(user?.email||'')}</span><span class="s">${isOwner()?'เจ้าของร้าน':'พนักงาน'}</span></div>
    <button class="btn sm" data-act="signout">ออกจากระบบ</button></div></div></div>`;
}
function staffSettingsHtml(){
  return `<div class="sh-head"><h2>ตั้งค่า</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
  ${accountSection()}
  <div class="fld"><span>หน้าที่ของคุณ</span><div class="note">${Object.keys(PERMS).filter(k=>can(k)).map(k=>PERMS[k]).join('<br>')||'ยังไม่ได้รับมอบหน้าที่'}</div></div>
  <span class="hint">เจ้าของร้านเป็นผู้กำหนดหน้าที่ ถ้าต้องทำอย่างอื่นเพิ่ม ให้แจ้งเจ้าของร้าน</span>
  <div class="sh-foot"><button class="btn primary" data-act="close">ปิด</button></div>`;
}
const ROLE={owner:'เจ้าของร้าน',staff:'พนักงาน'};
function peopleSection(){
  if(ss.members===null)return `<div class="fld"><span>ผู้ใช้งานและสิทธิ์</span><span class="hint">กำลังโหลดรายชื่อ…</span></div>`;
  const ms=(ss.members||[]).slice().sort((a,b)=>(a.id===ss.founder?-1:b.id===ss.founder?1:0)||(a.role===b.role?0:a.role==='owner'?-1:1)),
    inv=(ss.invites||[]).filter(i=>!ms.some(m=>(m.email||'')===i.id));
  const row=m=>{
    const locked=m.id===user.uid||m.id===ss.founder;
    const note=m.id===ss.founder?'เจ้าของร้านหลัก':'';
    const mp=m.perms&&typeof m.perms==='object'?m.perms:DEFAULT_PERMS;
    return `<div class="drow wrap-row"><div class="main"><span class="t">${esc(m.email||'ไม่มีอีเมล')}</span>
      <span class="s">${locked?`<span class="chip ${m.role==='owner'?'ok':'warn'}">${ROLE[m.role]||m.role}</span>`:''}${[note,m.id===user.uid?'คุณ':''].filter(Boolean).map(esc).join(' · ')}</span>
      ${m.role==='staff'&&!locked?`<span class="pchips" role="group" aria-label="หน้าที่ของ ${esc(m.email||'')}">${Object.keys(PERMS).map(k=>`<button class="pchip" data-act="p-perm" data-uid="${esc(m.id)}" data-v="${k}" aria-pressed="${!!mp[k]}">${PERM_SHORT[k]}</button>`).join('')}</span>`:''}</div>
      ${locked?'':`<select id="s-role-${esc(m.id)}" data-uid="${esc(m.id)}" aria-label="สิทธิ์ของ ${esc(m.email||'')}">${['owner','staff'].map(r=>`<option value="${r}" ${m.role===r?'selected':''}>${ROLE[r]}</option>`).join('')}</select>
        ${ss.rmUid===m.id?`<button class="btn sm danger" data-act="p-rm-yes" data-v="${esc(m.id)}">ยืนยันเอาออก</button>`:`<button class="btn sm" data-act="p-rm" data-v="${esc(m.id)}">เอาออก</button>`}`}</div>`;
  };
  return `<div class="fld"><span>ผู้ใช้งานและสิทธิ์</span>
    ${ss.peopleErr?`<span class="hint">${esc(ss.peopleErr)}</span>`:''}
    <div class="list">${ms.map(row).join('')}
    ${inv.map(i=>`<div class="drow"><div class="main"><span class="t">${esc(i.id)}</span><span class="s"><span class="chip warn">รอเข้าใช้งาน</span><span>${ROLE[i.role]||'พนักงาน'}${i.role!=='owner'?' · '+(Object.keys(i.perms||DEFAULT_PERMS).filter(k=>(i.perms||DEFAULT_PERMS)[k]).map(k=>PERM_SHORT[k]).join(', ')||'ไม่มีหน้าที่'):''}</span></span></div><button class="btn sm" data-act="p-uninvite" data-v="${esc(i.id)}">ยกเลิก</button></div>`).join('')}</div>
    <div class="addrow"><input id="s-invite" type="email" inputmode="email" autocomplete="off" placeholder="อีเมลที่จะเชิญ" value="${esc(ss.inviteEmail||'')}">
      <select id="s-invite-role" aria-label="สิทธิ์ของคนที่เชิญ">${['staff','owner'].map(r=>`<option value="${r}" ${(ss.inviteRole||'staff')===r?'selected':''}>${ROLE[r]}</option>`).join('')}</select>
      <button class="btn sm" data-act="p-invite">เชิญ</button></div>
    ${(ss.inviteRole||'staff')==='staff'?`<div class="fld"><span class="small">หน้าที่ของคนที่เชิญ</span><span class="pchips">${Object.keys(PERMS).map(k=>`<button class="pchip" data-act="p-iperm" data-v="${k}" aria-pressed="${!!(ss.invitePerms||DEFAULT_PERMS)[k]}">${PERM_SHORT[k]}</button>`).join('')}</span></div>`:''}
    ${ss.inviteErr?`<div class="err" style="margin-top:0">${esc(ss.inviteErr)}</div>`:''}
    <div class="note"><b>เจ้าของร้าน</b> เห็นทุกอย่าง ทั้งยอดเงิน กำไร รายงาน ตั้งค่า และจัดการผู้ใช้<br><b>พนักงาน</b> ทำได้เฉพาะหน้าที่ที่ติ๊กไว้ ค่าเริ่มต้นคือเบิกใช้วัตถุดิบอย่างเดียว · ไม่เห็นยอดเงินคงเหลือ กำไร รายงาน ราคาวัตถุดิบ และการถอนเงินเจ้าของ
      <br><span class="small">เบิกใช้ = หยิบวัตถุดิบไปใช้ · รับเข้า = รับของที่ซื้อมา · นับสต็อก = นับประจำเดือน · บัญชี = บันทึกรายรับรายจ่ายและค้างชำระ</span></div>
    <span class="hint">คนที่ได้รับเชิญเปิดแอป สมัครด้วยอีเมลนี้ และกดยืนยันอีเมล ก็เข้าใช้งานได้ · เปลี่ยนสิทธิ์มีผลทันที · เจ้าของร้านหลักเปลี่ยนสิทธิ์หรือเอาออกไม่ได้</span></div>`;
}
function dataSection(){
  const d=ss.importData;
  return `<div class="fld"><span>ข้อมูลและไฟล์สำรอง</span>
    <div class="btns"><button class="btn sm" data-act="audit">ดูประวัติการแก้ไข</button><button class="btn sm" data-act="backup">ดาวน์โหลดไฟล์สำรอง</button>
    <label class="btn sm filebtn">นำเข้าจากไฟล์สำรอง<input type="file" id="s-import" class="vh" accept=".json,application/json"></label></div>
    ${ss.importing?`<div class="note">${esc(ss.importing)}</div>`:d?`<div class="credit"><b>พร้อมนำเข้า: ${Object.keys(d.days||{}).length} วัน · ${Object.values(d.days||{}).reduce((s,x)=>s+Object.keys(x.entries||{}).length,0)} รายการ</b>
      <span class="small">ข้อมูลวันที่ตรงกันจะถูกแทนที่ด้วยข้อมูลจากไฟล์ และการตั้งค่าร้านจะใช้ตามไฟล์</span>
      <div class="btns"><button class="btn sm danger" data-act="import-yes">ยืนยันนำเข้า</button><button class="btn sm" data-act="import-no">ยกเลิก</button></div></div>`:''}
    <span class="hint">ควรดาวน์โหลดไฟล์สำรองเก็บไว้ทุกสิ้นเดือน</span></div>`;
}
function recentMonths(){
  const set=new Set(M.s.closed);const now=monthOf(todayKey());
  for(let i=0;i<4;i++)set.add(addMonth(now,-i));
  for(const e of M.entries)set.add(monthOf(e.d));
  return [...set].filter(m=>/^\d{4}-\d{2}$/.test(m)).sort().reverse().slice(0,6);
}
const catKind=(t,c)=>c.pl===false?'own':t==='in'?'inc':c.g==='cogs'?'cogs':'opex';
function readSet(){
  const g=id=>byId(id);
  if(g('s-shop'))ss.shop=g('s-shop').value;
  ss.accs.forEach((a,i)=>{if(g('s-an-'+i))a.n=g('s-an-'+i).value;if(g('s-ao-'+i))a.open=g('s-ao-'+i).value});
  for(const t of ['in','out'])ss.cats[t].forEach((c,i)=>{const el=g(`s-g-${t}-${i}`);if(!el)return;delete c.pl;delete c.g;if(el.value==='own')c.pl=false;else if(el.value==='cogs')c.g='cogs'});
  if(g('s-newin'))ss.newIn=g('s-newin').value;if(g('s-newout'))ss.newOut=g('s-newout').value;if(g('s-newg'))ss.newG=g('s-newg').value;
  if(g('s-newacc'))ss.newAcc=g('s-newacc').value;
  if(g('s-invite'))ss.inviteEmail=g('s-invite').value;
  if(g('s-invite-role'))ss.inviteRole=g('s-invite-role').value;
}
function setHtml(err){
  if(!isOwner())return staffSettingsHtml();
  const ro=!canWrite,dis=ro?'disabled':'';
  const opts={in:[['inc','รายได้'],['own','ไม่นับกำไร']],out:[['cogs','ต้นทุนขาย'],['opex','ค่าใช้จ่าย'],['own','ไม่นับกำไร']]};
  const block=t=>`<div class="list">${ss.cats[t].map((c,i)=>`<div class="drow ${c.h?'dim':''}"><div class="main"><span class="t">${esc(c.n)}</span></div>
    <select id="s-g-${t}-${i}" aria-label="ประเภทของหมวด ${esc(c.n)}" ${dis}>${opts[t].map(([v,l])=>`<option value="${v}" ${catKind(t,c)===v?'selected':''}>${l}</option>`).join('')}</select>
    ${ro?'':`<button class="btn sm" data-act="s-cat" data-t="${t}" data-i="${i}">${c.h?'ใช้':'ซ่อน'}</button>`}</div>`).join('')}</div>`;
  const cons=Object.values(M.contacts).sort((a,b)=>a.name.localeCompare(b.name,'th'));
  return `<div class="sh-head"><h2>ตั้งค่าร้าน</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
  <label class="fld"><span>ชื่อร้าน</span><input id="s-shop" value="${esc(ss.shop)}" maxlength="60" ${dis}></label>
  <div class="fld"><span>บัญชีเงินของร้าน และยอดเงินตั้งต้น</span>
    <div class="acc-row hint"><span>ชื่อบัญชี</span><span>ยอดตั้งต้น (บาท)</span><span></span></div>
    ${ss.accs.map((a,i)=>`<div class="acc-row"><input id="s-an-${i}" value="${esc(a.n)}" maxlength="30" aria-label="ชื่อบัญชี" ${a.id==='cash'||ro?'disabled':''} style="${a.h?'opacity:.5':''}">
      <input id="s-ao-${i}" inputmode="decimal" value="${esc(a.open)}" aria-label="ยอดตั้งต้นของ ${esc(a.n)}" ${dis}>
      ${a.id==='cash'||ro?'<span></span>':`<button class="btn sm" data-act="s-acc-h" data-i="${i}">${a.h?'ใช้':'ซ่อน'}</button>`}</div>`).join('')}
    ${ro?'':`<div class="addrow"><input id="s-newacc" placeholder="เพิ่มบัญชี เช่น กสิกร" value="${esc(ss.newAcc)}" maxlength="30"><button class="btn sm" data-act="s-acc-add">เพิ่ม</button></div>`}
    <span class="hint">ยอดตั้งต้นคือเงินที่มีอยู่จริงในแต่ละบัญชี ณ วันที่เริ่มใช้แอป</span></div>
  ${err?`<div class="err">${err}</div>`:''}
  <div class="fld"><span>หมวดรายรับ</span>${block('in')}
    ${ro?'':`<div class="addrow"><input id="s-newin" placeholder="ชื่อหมวดรายรับใหม่" value="${esc(ss.newIn)}" maxlength="40"><button class="btn sm" data-act="s-add" data-t="in">เพิ่ม</button></div>`}</div>
  <div class="fld"><span>หมวดรายจ่าย</span>${block('out')}
    ${ro?'':`<div class="addrow"><input id="s-newout" placeholder="ชื่อหมวดรายจ่ายใหม่" value="${esc(ss.newOut)}" maxlength="40"><select id="s-newg" aria-label="ประเภทหมวดใหม่"><option value="cogs" ${ss.newG==='cogs'?'selected':''}>ต้นทุนขาย</option><option value="opex" ${ss.newG==='opex'?'selected':''}>ค่าใช้จ่าย</option><option value="own" ${ss.newG==='own'?'selected':''}>ไม่นับกำไร</option></select><button class="btn sm" data-act="s-add" data-t="out">เพิ่ม</button></div>`}
    <span class="hint">"ต้นทุนขาย" คือของที่กลายเป็นสินค้า เช่น วัตถุดิบ บรรจุภัณฑ์ เทียนอบขนม เมล็ดกาแฟ · หมวดที่ซ่อนจะไม่ขึ้นตอนบันทึก แต่รายการเก่ายังอยู่ครบ</span></div>
  <div class="fld"><span>ปิดงวดบัญชี</span>
    <div class="list">${recentMonths().map(mk=>{const c=M.s.closed.includes(mk);return `<div class="drow"><div class="main"><span class="t">${esc(thMonth(mk))}</span><span class="s">${c?'<span class="chip ok">ปิดงวดแล้ว</span>':'<span>เปิดอยู่ แก้ไขได้</span>'}</span></div>${ro?'':`<button class="btn sm" data-act="s-period" data-v="${mk}">${c?'เปิดงวด':'ปิดงวด'}</button>`}</div>`}).join('')}</div>
    <span class="hint">เดือนที่ปิดงวดแล้วจะเพิ่ม แก้ไข หรือลบรายการไม่ได้ กันตัวเลขที่ส่งนักบัญชีไปแล้วเปลี่ยน · ปุ่มนี้มีผลทันที</span></div>
  <div class="fld"><span>รายชื่อลูกค้าและเจ้าหนี้</span>
    ${cons.length?`<div class="list">${cons.map(c=>`<div class="drow"><div class="main"><span class="t">${esc(c.name)}</span><span class="s">${c.kind==='cus'?'ลูกค้า':'เจ้าหนี้'}${c.phone?' · '+esc(c.phone):''}</span></div>${ro?'':(ss.cdel===c.id?`<button class="btn sm danger" data-act="s-cdel-yes" data-v="${esc(c.id)}">ยืนยันลบ</button>`:`<button class="btn sm" data-act="s-cdel" data-v="${esc(c.id)}">ลบ</button>`)}</div>`).join('')}</div>`
    :'<span class="hint">ยังไม่มีรายชื่อ ระบบจะเพิ่มให้เองเมื่อบันทึกรายการเงินเชื่อ</span>'}</div>
  ${peopleSection()}${dataSection()}${accountSection()}
  <div class="sh-foot"><button class="btn ghost" data-act="close">ปิด</button>${ro?'':'<button class="btn primary" data-act="s-save">บันทึกการตั้งค่า</button>'}</div>`;
}
function saveSettings(){
  readSet();
  const open={};
  for(const a of ss.accs){const v=num(String(a.open).trim()===''?'0':a.open);if(!isFinite(v))return showSheet(setHtml(`ยอดตั้งต้นของ ${a.n||'บัญชี'} ต้องเป็นตัวเลข`),true);open[a.id]=v}
  const accs=ss.accs.map(a=>{const o={id:a.id,n:(a.n||'').trim()||(a.id==='cash'?'เงินสด':'บัญชี')};if(a.h&&a.id!=='cash')o.h=true;return o});
  enqueue({k:'settings',id:'settings',patch:{shop:ss.shop.trim()||DEFAULTS.shop,accs,open,cats:ss.cats,at:Date.now()}});
  closeSheet();toast('บันทึกการตั้งค่าแล้ว');
}

/* ---------- writes (Firestore keeps them on the phone until it is back online) ---------- */
const plain=o=>o==null?null:JSON.parse(JSON.stringify(o));
function fire(p,what){
  return p.catch(e=>{console.error(what||'write',e);
    toast(e?.code==='permission-denied'?'บันทึกไม่สำเร็จ: ไม่มีสิทธิ์ หรือเดือนนี้ปิดงวดแล้ว':'บันทึกไม่สำเร็จ ลองใหม่อีกครั้ง')});
}
function audit(act,d,eid,before,after){
  if(!fb||!user)return;
  fire(setDoc(doc(collection(fb.db,'audit')),{ts:Date.now(),at:serverTimestamp(),uid:user.uid,email:(user.email||'').toLowerCase(),act,d:d||'',eid:eid||'',before:plain(before),after:plain(after)}),'audit');
}
function dayOp(date,entries,go=true){
  for(const[eid,val]of Object.entries(entries)){
    const cur=cache.days[date]?.entries?.[eid];
    const act=!cur||cur.del?'add':val?.del?'delete':val?.pays&&Object.keys(val).length===1?'pay':'edit';
    audit(act,date,eid,cur||null,val);
  }
  fire(setDoc(doc(fb.db,'days',date),{d:date,y:+date.slice(0,4),m:date.slice(0,7),entries:plain(entries)},{merge:true}),'day');
  if(go)render();
}
function enqueue(op,go=true){
  const ref=op.k==='contact'?doc(fb.db,'contacts',op.id):doc(fb.db,'meta','settings');
  if(op.k==='settings')audit('settings','','',null,op.patch);
  fire(setDoc(ref,plain(op.patch),{merge:true}),op.k);
  if(go)render();
}
let subRetry=0;
function subscribe(){
  unsubs.forEach(u=>{try{u()}catch(e){}});unsubs=[];
  const meta={};
  const upd=(k,m)=>{meta[k]=m;pending=Object.values(meta).some(x=>x.hasPendingWrites);fromCache=Object.values(meta).some(x=>x.fromCache)};
  const onErr=e=>{console.error(e);
    if(e?.code==='permission-denied'&&role){
      // membership may still be saving on the server: try again a few times before giving up
      subRetry++;if(subRetry<=5){setTimeout(()=>{if(role)subscribe()},1500*subRetry);return}
      toast('บัญชีนี้ไม่มีสิทธิ์อ่านข้อมูลร้าน');return}
    if(e?.code==='unavailable'&&role)setTimeout(()=>{if(role)subscribe()},5000)};
  if(can('acct')){
  unsubs.push(onSnapshot(collection(fb.db,'days'),{includeMetadataChanges:true},snap=>{
    for(const ch of snap.docChanges()){if(ch.type==='removed')delete cache.days[ch.doc.id];else cache.days[ch.doc.id]=ch.doc.data()}
    upd('days',snap.metadata);if(!snap.metadata.fromCache||snap.size)loaded=true;if(!snap.metadata.fromCache)subRetry=0;schedule();
  },onErr));
  unsubs.push(onSnapshot(collection(fb.db,'contacts'),{includeMetadataChanges:true},snap=>{
    for(const ch of snap.docChanges()){if(ch.type==='removed')delete cache.contacts[ch.doc.id];else cache.contacts[ch.doc.id]=ch.doc.data()}
    upd('contacts',snap.metadata);schedule();
  },onErr));
  unsubs.push(onSnapshot(doc(fb.db,'meta','settings'),{includeMetadataChanges:true},s=>{
    cache.settings=s.exists()?s.data():null;upd('settings',s.metadata);schedule();
  },onErr));
  }
  unsubs.push(onSnapshot(collection(fb.db,'stock'),{includeMetadataChanges:true},snap=>{
    for(const ch of snap.docChanges()){if(ch.type==='removed')delete cache.stock[ch.doc.id];else cache.stock[ch.doc.id]=ch.doc.data()}
    upd('stock',snap.metadata);if(!can('acct')&&(!snap.metadata.fromCache||snap.size))loaded=true;schedule();
  },onErr));
  unsubs.push(onSnapshot(doc(fb.db,'stockcounts',monthOf(todayKey())),{includeMetadataChanges:true},s=>{
    cache.count=s.exists()?s.data():null;upd('count',s.metadata);schedule();
  },onErr));
  cache.stockcost={};
  if(isOwner())unsubs.push(onSnapshot(collection(fb.db,'stockcost'),snap=>{
    for(const ch of snap.docChanges()){if(ch.type==='removed')delete cache.stockcost[ch.doc.id];else cache.stockcost[ch.doc.id]=ch.doc.data()}
    schedule();
  },onErr));
}
function stopData(){unsubs.forEach(u=>{try{u()}catch(e){}});unsubs=[];cache={days:{},contacts:{},settings:null,stock:{},stockcost:{},count:null};loaded=false}

/* ---------- receipts (photo stored compressed in Firestore) ---------- */
async function compressImage(file){
  const url=URL.createObjectURL(file);
  try{
    const img=await new Promise((res,rej)=>{const i=new Image();i.onload=()=>res(i);i.onerror=rej;i.src=url});
    let max=1400,q=.72,out='';
    for(let k=0;k<6;k++){
      const s=Math.min(1,max/Math.max(img.naturalWidth,img.naturalHeight));
      const c=document.createElement('canvas');c.width=Math.max(1,Math.round(img.naturalWidth*s));c.height=Math.max(1,Math.round(img.naturalHeight*s));
      const g=c.getContext('2d');g.fillStyle='#fff';g.fillRect(0,0,c.width,c.height);g.drawImage(img,0,0,c.width,c.height);
      out=c.toDataURL('image/jpeg',q);
      if(out.length<650000)return out;
      max=Math.round(max*.8);q=Math.max(.5,q-.06);
    }
    return out.length<900000?out:null;
  }finally{URL.revokeObjectURL(url)}
}
async function viewReceipt(id){
  showSheet(`<div class="sh-head"><h2>ใบเสร็จ</h2><button class="icon" data-act="rc-back" aria-label="กลับ">×</button></div><div class="empty"><b>กำลังโหลดรูป</b></div>`);
  try{
    const s=await getDoc(doc(fb.db,'receipts',id));
    const data=s.exists()?s.data().data:'';
    if(!es&&!ps)return;
    showSheet(`<div class="sh-head"><h2>ใบเสร็จ</h2><button class="icon" data-act="rc-back" aria-label="กลับ">×</button></div>
      ${/^data:image\//.test(data||'')?`<img class="receipt" src="${data}" alt="รูปใบเสร็จ">`:'<div class="empty"><b>ไม่พบรูป</b><p>รูปอาจยังไม่ได้ส่งขึ้นระบบจากเครื่องที่ถ่าย</p></div>'}
      <div class="sh-foot"><button class="btn primary" data-act="rc-back">กลับ</button></div>`);
  }catch(e){showSheet(`<div class="sh-head"><h2>ใบเสร็จ</h2><button class="icon" data-act="rc-back" aria-label="กลับ">×</button></div><div class="empty"><b>เปิดรูปไม่ได้</b><p>ต้องต่ออินเทอร์เน็ตเพื่อดูรูปที่ยังไม่เคยเปิดในเครื่องนี้</p></div>`)}
}

/* ---------- files: CSV for the accountant, JSON backup ---------- */
function saveFile(name,text,type){
  const blob=new Blob([text],{type});const a=document.createElement('a');
  a.href=URL.createObjectURL(blob);a.download=name;document.body.appendChild(a);a.click();
  setTimeout(()=>{URL.revokeObjectURL(a.href);a.remove()},1500);
}
function exportCsv(scope){
  const mk=ui.month,y=mk.slice(0,4);
  const list=M.entries.filter(e=>scope==='m'?monthOf(e.d)===mk:e.d.startsWith(y)).slice().reverse();
  const cell=v=>{if(typeof v==='number')return String(v);let s=String(v??'');if(/^[=+\-@]/.test(s))s="'"+s;return /[",\r\n]/.test(s)?'"'+s.replace(/"/g,'""')+'"':s};
  const head=['วันที่','ประเภท','หมวด','จำนวนเงิน','ช่องทาง','สถานะ','ชำระแล้ว','คงค้าง','ชื่อลูกค้า/เจ้าหนี้','หมายเหตุ','มีใบเสร็จ'];
  const rows=list.map(e=>[e.d,TYPE[e.t],e.t==='move'?`${accName(e.acc)} → ${accName(e.to)}`:e.t==='draw'?'ถอนเงินเจ้าของ':e.cat,e.amt,e.imp?'ยอดยกมา':e.credit?'เงินเชื่อ':accName(e.acc),
    e.credit?(due(e)>0?'ค้างชำระ':'ชำระครบ'):'ชำระแล้ว',e.credit?r2(paid(e)):e.amt,due(e),e.cid&&M.contacts[e.cid]?M.contacts[e.cid].name:'',e.note||'',e.rc||e.att?'มี':'']);
  const csv='﻿'+[head,...rows].map(r=>r.map(cell).join(',')).join('\r\n');
  saveFile(scope==='m'?`บัญชีร้าน-${mk}.csv`:`บัญชีร้าน-ปี${+y+543}.csv`,csv,'text/csv;charset=utf-8');
}
function exportBackup(){
  const out={format:'baanpleng-books',version:1,exportedAt:new Date().toISOString(),settings:cache.settings||{},contacts:cache.contacts,days:cache.days,stock:cache.stock,stockcost:cache.stockcost};
  saveFile(`baanpleng-backup-${todayKey()}.json`,JSON.stringify(out),'application/json');
  toast('ดาวน์โหลดไฟล์สำรองแล้ว');
}
async function runImport(data){
  if(navigator.onLine===false){toast('ต้องต่ออินเทอร์เน็ตก่อนนำเข้าข้อมูล');return}
  ss.importing='กำลังนำเข้า…';rerS();
  try{
    const settings=plain(data.settings||{}),closed=Array.isArray(settings.closed)?settings.closed:[];
    await setDoc(doc(fb.db,'meta','settings'),{...settings,closed:[]});
    const days=Object.entries(data.days||{}).filter(([d,v])=>/^\d{4}-\d{2}-\d{2}$/.test(d)&&v&&typeof v==='object');
    for(let i=0;i<days.length;i+=300){
      const b=writeBatch(fb.db);
      for(const[d,v]of days.slice(i,i+300))b.set(doc(fb.db,'days',d),{...plain(v),d,y:+d.slice(0,4),m:d.slice(0,7)});
      await b.commit();ss.importing=`นำเข้าแล้ว ${Math.min(i+300,days.length)} / ${days.length} วัน`;rerS();
    }
    const cs=Object.entries(data.contacts||{});
    for(let i=0;i<cs.length;i+=300){const b=writeBatch(fb.db);for(const[id,v]of cs.slice(i,i+300))b.set(doc(fb.db,'contacts',id),plain(v));await b.commit()}
    for(const[col,obj]of [['stock',data.stock],['stockcost',data.stockcost]]){
      const rows=Object.entries(obj||{}).filter(([,v])=>v&&typeof v==='object');
      for(let i=0;i<rows.length;i+=300){const b=writeBatch(fb.db);for(const[id,v]of rows.slice(i,i+300))b.set(doc(fb.db,col,id),plain(v));await b.commit()}
    }
    await setDoc(doc(fb.db,'meta','settings'),{closed},{merge:true});
    audit('import','','',null,{days:days.length,contacts:cs.length});
    ss.importing='';ss.importData=null;rerS();toast(`นำเข้าเรียบร้อย ${days.length} วัน`);
  }catch(e){console.error(e);ss.importing='';rerS();toast(e?.code==='permission-denied'?'นำเข้าไม่ได้: ต้องเป็นเจ้าของร้าน':'นำเข้าไม่สำเร็จ ลองใหม่อีกครั้ง')}
}

/* ---------- people and history (owner) ---------- */
async function loadPeople(){
  try{
    const[m,i,o]=await Promise.all([getDocs(collection(fb.db,'members')),getDocs(collection(fb.db,'invites')),getDoc(doc(fb.db,'meta','owner'))]);
    if(!ss)return;
    ss.founder=o.exists()?o.data().uid:'';
    ss.members=m.docs.map(d=>({id:d.id,...d.data()}));ss.invites=i.docs.map(d=>({id:d.id,...d.data()}));rerS();
  }catch(e){if(ss){ss.members=[];ss.invites=[];ss.peopleErr='โหลดรายชื่อไม่ได้ ต้องต่ออินเทอร์เน็ต';rerS()}}
}
const ACT={perms:'เปลี่ยนหน้าที่',add:'เพิ่ม',edit:'แก้ไข',delete:'ลบ',pay:'ชำระหนี้',settings:'ตั้งค่า',import:'นำเข้าข้อมูล',role:'เปลี่ยนสิทธิ์',invite:'เชิญผู้ใช้',remove:'เอาผู้ใช้ออก'};
async function openAudit(){
  showSheet(`<div class="sh-head"><h2>ประวัติการแก้ไข</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div><div class="empty"><b>กำลังโหลด</b></div>`);
  try{
    const s=await getDocs(query(collection(fb.db,'audit'),orderBy('ts','desc'),limit(150)));
    const rows=s.docs.map(d=>d.data());
    const desc=a=>{if(a.act==='perms')return `${a.after?.email||''} → ${Object.keys(a.after?.perms||{}).map(k=>PERM_SHORT[k]).join(', ')||'ไม่มีสิทธิ์'}`;
      if(a.act==='role'||a.act==='invite'||a.act==='remove')return [a.after?.email||a.before?.email,a.after?.role?ROLE[a.after.role]:''].filter(Boolean).join(' → ');
      const v=a.after&&!a.after.del&&a.after.t?a.after:a.before||{};
      return [v.t?TYPE[v.t]:'',v.t==='move'?`${accName(v.acc)} → ${accName(v.to)}`:v.cat,v.amt!=null?money(+v.amt)+' บาท':'',v.note].filter(Boolean).join(' · ')};
    showSheet(`<div class="sh-head"><h2>ประวัติการแก้ไข</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
      <span class="hint">150 รายการล่าสุด ทุกการเพิ่ม แก้ไข และลบ ถูกบันทึกไว้และแก้ย้อนหลังไม่ได้</span>
      ${rows.length?`<div class="list">${rows.map(a=>`<div class="drow"><div class="main"><span class="t">${esc(ACT[a.act]||a.act)}${a.d?' · รายการวันที่ '+esc(thShort(a.d)):''}</span>
        <span class="s"><span>${esc(desc(a))}</span></span><span class="s"><span>${esc(new Date(a.ts).toLocaleString('th-TH',{dateStyle:'short',timeStyle:'short'}))} · ${esc(a.email||'')}</span></span></div></div>`).join('')}</div>`
      :'<div class="empty"><b>ยังไม่มีประวัติ</b></div>'}
      <div class="sh-foot"><button class="btn primary" data-act="close">ปิด</button></div>`);
  }catch(e){showSheet(`<div class="sh-head"><h2>ประวัติการแก้ไข</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div><div class="empty"><b>โหลดไม่ได้</b><p>ต้องต่ออินเทอร์เน็ต</p></div>`)}
}

/* ---------- ui glue ---------- */
let toastTimer=null;
function toast(msg){const t=byId('toast');t.textContent=msg;t.hidden=false;clearTimeout(toastTimer);toastTimer=setTimeout(()=>{t.hidden=true},2600)}
function setUi(p,scroll){Object.assign(ui,p);LS.set('bp_ui',{tab:ui.tab,filter:ui.filter,side:ui.side});render();if(scroll)window.scrollTo(0,0)}
const rerE=()=>showSheet(entryHtml(),true),rerP=()=>showSheet(payHtml(),true),rerS=()=>showSheet(setHtml(),true);

byId('sheet').addEventListener('click',ev=>{if(ev.target.id==='sheet')closeSheet()});
document.addEventListener('keydown',ev=>{if(ev.key==='Escape'&&!byId('sheet').hidden)closeSheet()});
document.addEventListener('click',ev=>{
  const b=ev.target.closest('[data-act]');if(!b||b.disabled)return;
  const a=b.dataset.act,v=b.dataset.v;
  switch(a){
    case 'tab':setUi({tab:b.dataset.tab},true);break;
    case 'filter':setUi({filter:v});break;
    case 'month':setUi({month:addMonth(ui.month,+b.dataset.d)});break;
    case 'side':setUi({side:v});break;
    case 'debt':setUi({tab:'debt',side:b.dataset.side},true);break;
    case 'add':if(canWrite)openEntry();break;
    case 'edit':if(canWrite)openEntry(b.dataset.id,b.dataset.d);break;
    case 'pay':if(canWrite)openPay(b.dataset.id,b.dataset.d);break;
    case 'settings':openSettings();break;
    case 'close':closeSheet();break;
    case 'csv':exportCsv(b.dataset.scope);break;
    case 'sync-info':toast(navigator.onLine===false?'ไม่มีอินเทอร์เน็ต บันทึกต่อได้ตามปกติ ข้อมูลจะส่งขึ้นเองเมื่อต่อเน็ต':pending?'กำลังส่งข้อมูลขึ้นระบบ':'ข้อมูลทุกเครื่องตรงกันแล้ว');break;
    case 'g-mode':case 'g-google':case 'g-reset':case 'g-claim':case 'g-resend':case 'g-verified':case 'g-retry':gateAction(a,v);break;
    case 'signout':closeSheet();signOut(fb.auth);break;
    case 'rc-view':readEntry();viewReceipt(v);break;
    case 'rc-back':if(es)rerE();else closeSheet();break;
    case 'rc-remove':readEntry();es.rcData='';es.rc='';es.rcDrop=true;rerE();break;
    case 'p-invite':{readSet();const em=(ss.inviteEmail||'').trim().toLowerCase(),irole=ss.inviteRole==='owner'?'owner':'staff';
      if(!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(em)){ss.inviteErr='ใส่อีเมลให้ถูกต้อง';rerS();break}
      if((ss.members||[]).some(m=>m.email===em)){ss.inviteErr='อีเมลนี้เป็นผู้ใช้งานอยู่แล้ว';rerS();break}
      const ip=irole==='staff'?cleanPerms(ss.invitePerms||DEFAULT_PERMS):null,idoc={role:irole,by:user.uid,at:serverTimestamp()};if(ip)idoc.perms=ip;
      ss.inviteErr='';ss.inviteEmail='';ss.invites=[...(ss.invites||[]).filter(i=>i.id!==em),{id:em,role:irole,perms:ip||undefined}];
      fire(setDoc(doc(fb.db,'invites',em),idoc),'invite');audit('invite','','',null,{email:em,role:irole});
      rerS();toast(`เชิญ ${em} เป็น${ROLE[irole]}แล้ว`);break}
    case 'p-perm':{readSet();const m=(ss.members||[]).find(x=>x.id===b.dataset.uid);if(!m)break;
      const cur={...(m.perms&&typeof m.perms==='object'?m.perms:DEFAULT_PERMS)};cur[v]=!cur[v];const np=cleanPerms(cur);
      fire(setDoc(doc(fb.db,'members',m.id),{perms:np,roleAt:serverTimestamp(),roleBy:user.uid},{mergeFields:['perms','roleAt','roleBy']}),'perms');
      audit('perms','','',{email:m.email||'',perms:m.perms||DEFAULT_PERMS},{email:m.email||'',perms:np});m.perms=np;rerS();break}
    case 'p-iperm':{readSet();const c={...(ss.invitePerms||DEFAULT_PERMS)};c[v]=!c[v];ss.invitePerms=cleanPerms(c);rerS();break}
    case 'p-uninvite':readSet();fire(deleteDoc(doc(fb.db,'invites',v)),'uninvite');ss.invites=(ss.invites||[]).filter(i=>i.id!==v);rerS();break;
    case 'p-rm':readSet();ss.rmUid=v;rerS();break;
    case 'p-rm-yes':{readSet();const m=(ss.members||[]).find(x=>x.id===v);fire(deleteDoc(doc(fb.db,'members',v)),'rm');audit('remove','','',{email:m?.email||'',role:m?.role||''},null);
      if(m?.email)fire(deleteDoc(doc(fb.db,'invites',m.email)),'rm-inv');ss.members=(ss.members||[]).filter(x=>x.id!==v);ss.rmUid=null;rerS();toast('เอาผู้ใช้ออกแล้ว');break}
    case 'audit':openAudit();break;
    case 'backup':exportBackup();break;
    case 'import-yes':if(ss?.importData&&!ss.importing)runImport(ss.importData);break;
    case 'import-no':readSet();ss.importData=null;rerS();break;
    case 'st-mode':setUi({smode:v});break;
    case 'st-scan':closeSheet();openScanner('op');break;
    case 'st-scan-close':stopScan();if(scanTarget==='item'&&si)showSheet(itemFormHtml());else closeSheet();break;
    case 'st-item':openStockOp(b.dataset.id,ui.smode||'in');break;
    case 'st-new':openItemForm(null);break;
    case 'st-edit':{const id=sa?.id;sa=null;if(id)openItemForm(id);break}
    case 'st-close':ui.stClose=true;render();break;
    case 'st-close-no':ui.stClose=false;render();break;
    case 'st-close-yes':closeCount();break;
    case 'st-reopen':fire(setDoc(doc(fb.db,'stockcounts',curMonth()),{m:curMonth(),status:'open'},{merge:true}),'count');audit('stock-reopen','','',null,{m:curMonth()});toast('เปิดการนับอีกครั้งแล้ว');break;
    case 'st-history':openStockHistory();break;
    case 'st-csv':exportStockCsv();break;
    case 'so-mode':if(!canMode(v))break;readOp();if(v==='count'&&sa.mode!=='count')sa.qty='';else if(v!=='count'&&sa.mode==='count'&&sa.qty==='')sa.qty='1';sa.mode=v;sa.err='';if(v==='in'&&!sa.price)prefillPrice();showSheet(stockOpHtml(),true);break;
    case 'so-pack':readOp();sa.k=v;sa.err='';prefillPrice();showSheet(stockOpHtml(),true);break;
    case 'so-inc':case 'so-dec':{readOp();const n=numx(sa.qty===''?'0':sa.qty)||0;sa.qty=String(Math.max(0,r2((n+(a==='so-inc'?1:-1))*1000)/1000));sa.err='';showSheet(stockOpHtml(),true);break}
    case 'si-convert':convertItem();break;
    case 'so-save':saveOp(v==='scan');break;
    case 'si-addcode':readItem();si.codes.push({c:'',pack:'1',label:''});showSheet(itemFormHtml(),true);break;
    case 'si-rmcode':readItem();si.codes.splice(+v,1);showSheet(itemFormHtml(),true);break;
    case 'si-scancode':readItem();openScanner('item');break;
    case 'si-save':saveItem();break;
    case 'si-off':readItem();si.confirmOff=true;showSheet(itemFormHtml(),true);break;
    case 'si-off-yes':{const n=stockItem(si.id)?.name||'';fire(setDoc(doc(fb.db,'stock',si.id),{off:true,upd:Date.now()},{merge:true}),'item');audit('stock-off','','',null,{name:n});closeSheet();toast(`เลิกใช้ ${n} แล้ว`);break}
    case 'e-type':readEntry();if(es.t!==v){es.t=v;es.cat=hasCat(v)?(visCats(v)[0]?.n||''):'';es.cid='';es.newC=false;if(!hasCat(v))es.credit=false;if(v==='move'&&es.to===es.acc)es.to=defTo(es.acc)}rerE();break;
    case 'e-cat':readEntry();es.cat=v;rerE();break;
    case 'e-acc':readEntry();es.acc=v;es.credit=false;if(es.t==='move'&&es.to===v)es.to=defTo(v);rerE();break;
    case 'e-credit':readEntry();es.credit=true;rerE();break;
    case 'e-to':readEntry();es.to=v;rerE();break;
    case 'e-newc':readEntry();es.newC=v==='1';rerE();break;
    case 'e-save':saveEntry();break;
    case 'e-del':readEntry();es.confirmDel=true;rerE();break;
    case 'e-del-no':readEntry();es.confirmDel=false;rerE();break;
    case 'e-del-yes':if(es.ro){toast(es.roMsg);break}dayOp(es.origDate,{[es.id]:{del:true,ed:Date.now()}});closeSheet();toast('ลบรายการแล้ว');break;
    case 'p-acc':readPay();ps.acc=v;rerP();break;
    case 'p-save':savePay();break;
    case 'p-del':readPay();ps.delPid=v;rerP();break;
    case 'p-del-yes':readPay();{const pp=M.entries.find(x=>x.id===ps.id&&x.d===ps.d)?.pays?.[v];if(pp&&isClosed(pp.date)){toast(closedMsg(pp.date));break}}dayOp(ps.d,{[ps.id]:{pays:{[v]:null}}});ps.delPid=null;{const e=M.entries.find(x=>x.id===ps.id&&x.d===ps.d);if(e)ps.amt=String(due(e))}rerP();toast('ลบการชำระแล้ว');break;
    case 'p-edit':{const id=ps.id,d=ps.d;closeSheet();openEntry(id,d);break}
    case 's-cat':readSet();{const c=ss.cats[b.dataset.t][+b.dataset.i];if(c)c.h=!c.h}rerS();break;
    case 's-add':{readSet();const t=b.dataset.t,n=(t==='in'?ss.newIn:ss.newOut).trim();if(!n)break;
      const ex=ss.cats[t].find(c=>c.n===n);
      if(ex)ex.h=false;else ss.cats[t].push(t==='in'?{n}:ss.newG==='cogs'?{n,g:'cogs'}:ss.newG==='own'?{n,pl:false}:{n});
      if(t==='in')ss.newIn='';else ss.newOut='';rerS();break}
    case 's-acc-h':readSet();{const a=ss.accs[+b.dataset.i];if(a&&a.id!=='cash')a.h=!a.h}rerS();break;
    case 's-acc-add':{readSet();const n=ss.newAcc.trim();if(!n)break;const ex=ss.accs.find(a=>a.n===n);
      if(ex)ex.h=false;else ss.accs.push({id:'a'+rid(),n,h:false,open:'0'});ss.newAcc='';rerS();break}
    case 's-period':{readSet();const c=M.s.closed.includes(v);const next=c?M.s.closed.filter(m=>m!==v):[...M.s.closed,v].sort();
      enqueue({k:'settings',id:'settings',patch:{closed:next,at:Date.now()}});rerS();toast(c?`เปิดงวด${thMonth(v)}แล้ว`:`ปิดงวด${thMonth(v)}แล้ว`);break}
    case 's-cdel':readSet();ss.cdel=v;rerS();break;
    case 's-cdel-yes':readSet();enqueue({k:'contact',id:v,patch:{del:true,at:Date.now()}});ss.cdel=null;rerS();break;
    case 's-save':saveSettings();break;
  }
});
document.addEventListener('change',async ev=>{
  const t=ev.target;
  if(t.id==='f-rc'&&t.files?.[0]&&es){
    readEntry();const f=t.files[0];toast('กำลังย่อรูป…');
    try{const d=await compressImage(f);if(!d){toast('รูปใหญ่เกินไป ลองถ่ายใหม่');return}if(!es)return;es.rcData=d;es.rcDrop=false;rerE()}
    catch(e){toast('เปิดรูปไม่ได้ ลองเลือกรูปอื่น')}
  }
  if(t.dataset?.uid&&ss&&t.id.startsWith('s-role-')){
    readSet();const uid=t.dataset.uid,r=t.value==='owner'?'owner':'staff',m=(ss.members||[]).find(x=>x.id===uid);
    if(!m||m.role===r)return;
    fire(setDoc(doc(fb.db,'members',uid),{role:r,roleAt:serverTimestamp(),roleBy:user.uid},{merge:true}),'role');
    audit('role','','',{email:m.email||'',role:m.role},{email:m.email||'',role:r});
    m.role=r;rerS();toast(`เปลี่ยน ${m.email||'ผู้ใช้'} เป็น${ROLE[r]}แล้ว`);return;
  }
  if(t.id==='s-invite-role'&&ss){readSet();return}
  if((t.id==='si-unit'||t.id==='si-link'||t.id==='si-cunit')&&si){readItem();showSheet(itemFormHtml(),true);return}
  if(t.id==='s-import'&&t.files?.[0]&&ss){
    readSet();
    try{const data=JSON.parse(await t.files[0].text());if(data?.format!=='baanpleng-books'||!data.days)throw 0;ss.importData=data;rerS()}
    catch(e){toast('ไฟล์นี้ไม่ใช่ไฟล์สำรองของแอปนี้')}
  }
});
document.addEventListener('submit',ev=>{if(ev.target.id==='authform'){ev.preventDefault();submitAuth()}
  if(ev.target.id==='scan-form'){ev.preventDefault();const c=(byId('scan-code')?.value||'').trim();if(c)gotCode(c)}});
document.addEventListener('input',ev=>{const t=ev.target;
  if(t.id==='st-q'){ui.sq=t.value;render();return}
  if(sa&&(t.id==='so-qty'||t.id==='so-price')){readOp();showSheet(stockOpHtml(),true)}
  if(si&&/^si-[pr]-\d+$/.test(t.id)){readItem();showSheet(itemFormHtml(),true)}});
document.addEventListener('visibilitychange',()=>{if(document.hidden)stopScan()});

/* ---------- stock: items, barcodes, receive / use / monthly count ---------- */
const SUNITS=['กล่อง','ถุง','ขวด','แพ็ก','กระป๋อง','ก้อน','ชิ้น','ฟอง','แผง','ใบ','ม้วน','กรัม','กก.','มล.','ลิตร'];
const SCATS=['วัตถุดิบ','นม เนย ไข่','กาแฟและเครื่องดื่ม','บรรจุภัณฑ์','อื่น ๆ'];
const SMODE={in:'รับเข้า',use:'เบิกใช้',count:'นับสต็อก'};
const SMOVE={in:'รับเข้า',use:'เบิกใช้',adj:'ปรับจากการนับ',init:'ยอดเริ่มต้น',conv:'เปลี่ยนหน่วยนับ'};
let sa=null,si=null,scanner=null,zxP=null;
// stock numbers keep more precision than money (price per gram, 0.5 egg)
const numx=v=>{const n=parseFloat(String(v??'').replace(/[,\s฿]/g,''));return isFinite(n)?Math.round(n*1e6)/1e6:NaN};
const pfmt=n=>(+n||0).toLocaleString('th-TH',{minimumFractionDigits:2,maximumFractionDigits:4});
const r4=n=>Math.round((+n||0)*10000)/10000;
const qfmt=n=>(+n||0).toLocaleString('th-TH',{maximumFractionDigits:3});
const codeKey=c=>'b'+String(c).replace(/[^A-Za-z0-9_-]/g,ch=>'_'+ch.charCodeAt(0));
const stockItems=()=>Object.entries(cache.stock).filter(([,v])=>v&&!v.off&&v.name).map(([id,v])=>({...v,id,qty:+v.qty||0})).sort((a,b)=>a.name.localeCompare(b.name,'th'));
const stockItem=id=>{const v=cache.stock[id];return v?{...v,id,qty:+v.qty||0}:null};
const packsOf=it=>Object.entries(it?.codes||{}).filter(([,p])=>p&&p.c).map(([k,p])=>({k,c:p.c,pack:+p.pack||1,label:p.label||''}));
function findByCode(code){
  for(const[id,v]of Object.entries(cache.stock)){if(!v||v.off)continue;for(const[k,p]of Object.entries(v.codes||{}))if(p&&p.c===code)return{item:stockItem(id),k}}
  return null;
}
const avgOf=id=>+(cache.stockcost[id]?.avg)||0;
const isLow=it=>(+it.min||0)>0&&it.qty<=+it.min;
const curMonth=()=>monthOf(todayKey());
const countOpen=()=>!cache.count||cache.count.status!=='done';
// brand name per barcode: its label, or the last 4 digits; repeated labels also get the digits
function packNames(it){const ps=packsOf(it),cnt={};ps.forEach(p=>{if(p.label)cnt[p.label]=(cnt[p.label]||0)+1});
  const o={};ps.forEach(p=>{o[p.k]=!p.label?`บาร์โค้ด …${p.c.slice(-4)}`:cnt[p.label]>1?`${p.label} …${p.c.slice(-4)}`:p.label});return o}

function vStock(){
  const items=stockItems(),q=(ui.sq||'').trim().toLowerCase();
  const shown=q?items.filter(it=>it.name.toLowerCase().includes(q)||packsOf(it).some(p=>p.c.includes(q))):items;
  const modes=stockModes();if(!modes.includes(ui.smode))ui.smode=modes[0]||'use';
  const low=items.filter(isLow),mode=ui.smode;
  const lines=cache.count?.lines||{},counted=items.filter(it=>lines[it.id]).length,done=cache.count?.status==='done';
  const total=items.reduce((s,it)=>s+Math.max(0,it.qty)*avgOf(it.id),0);
  return `
  ${isOwner()?`<section class="card tight"><div class="row-head"><h2>มูลค่าสต็อก</h2><span class="v">${money(total)} บาท</span></div>
    <span class="muted small">${items.length} รายการ${low.length?` · ใกล้หมด ${low.length} รายการ`:''} · คิดจากราคาเฉลี่ยที่ซื้อ</span></section>`:''}
  ${isOwner()||canMode('count')?`<section class="card tight">
    <div class="row-head"><h2>นับสต็อก ${esc(thMonth(curMonth()))}</h2>${done?'<span class="chip ok">ปิดการนับแล้ว</span>':`<span class="muted small">${counted}/${items.length}</span>`}</div>
    ${items.length?`<div class="meter" role="img" aria-label="นับแล้ว ${counted} จาก ${items.length}"><div style="width:${items.length?counted/items.length*100:0}%;background:var(--pandan)"></div></div>`:''}
    <span class="muted small">${done?`เจ้าของร้านปิดการนับเดือนนี้แล้ว${isOwner()?'':' ถ้าต้องนับเพิ่ม ให้เจ้าของร้านเปิดอีกครั้ง'}`:'นับเดือนละครั้ง เลือกโหมด "นับสต็อก" แล้วสแกนหรือแตะทีละรายการ'}</span>
    ${isOwner()?`<div class="btns">${done?'<button class="btn sm" data-act="st-reopen">เปิดการนับอีกครั้ง</button>':`<button class="btn sm" data-act="st-close">ปิดการนับเดือนนี้</button>`}<button class="btn sm" data-act="st-history">มูลค่าย้อนหลัง</button><button class="btn sm" data-act="st-csv">ดาวน์โหลด CSV</button></div>`:''}
    ${ui.stClose&&!done?`<div class="credit"><b>ปิดการนับ ${esc(thMonth(curMonth()))}?</b><span class="small">${items.length-counted?`ยังไม่ได้นับ ${items.length-counted} รายการ ระบบจะใช้ยอดในระบบแทน `:''}ระบบจะบันทึกมูลค่าสต็อกสิ้นเดือนไว้ และพนักงานจะนับเพิ่มไม่ได้</span>
      <div class="btns"><button class="btn sm danger" data-act="st-close-yes">ยืนยันปิดการนับ</button><button class="btn sm" data-act="st-close-no">ยกเลิก</button></div></div>`:''}
  </section>`:''}
  ${modes.length>1?`<div class="seg">${modes.map(k=>`<button data-act="st-mode" data-v="${k}" aria-pressed="${mode===k}">${SMODE[k]}</button>`).join('')}</div>`
    :`<div class="note">หน้าที่ของคุณ: <b>${SMODE[mode]}</b> สแกนบาร์โค้ดหรือแตะรายการที่หยิบไปใช้</div>`}
  <div class="st-actions"><button class="btn primary" data-act="st-scan">${ICON_SCAN} สแกนบาร์โค้ด</button>${isOwner()?'<button class="btn" data-act="st-new">+ เพิ่มวัตถุดิบ</button>':''}</div>
  <input id="st-q" type="search" placeholder="ค้นหาชื่อหรือรหัสบาร์โค้ด" value="${esc(ui.sq||'')}" autocomplete="off" aria-label="ค้นหาวัตถุดิบ">
  ${low.length&&!q?`<section class="day"><div class="row-head"><h2>ต้องซื้อ</h2><span class="muted small">ต่ำกว่าขั้นต่ำที่ตั้งไว้</span></div>
    <div class="chips">${low.map(it=>`<button data-act="st-item" data-id="${esc(it.id)}">${esc(it.name)} · เหลือ ${qfmt(it.qty)} ${esc(it.unit)}</button>`).join('')}</div></section>`:''}
  <section class="day"><div class="row-head"><h2>วัตถุดิบ</h2><span class="muted small">แตะเพื่อ${SMODE[mode]}</span></div>
  <div id="st-list">${stockListHtml(shown,lines)}</div></section>`;
}
function stockListHtml(shown,lines){
  if(!stockItems().length)return `<div class="empty"><b>ยังไม่มีวัตถุดิบ</b><p>${isOwner()?'กด "สแกนบาร์โค้ด" ที่ห่อวัตถุดิบ หรือ "+ เพิ่มวัตถุดิบ" สำหรับของที่ไม่มีบาร์โค้ด':'ให้เจ้าของร้านเพิ่มรายการวัตถุดิบก่อน'}</p></div>`;
  if(!shown.length)return `<div class="empty"><b>ไม่พบ</b><p>ไม่มีวัตถุดิบที่ตรงกับคำค้น</p></div>`;
  const mode=ui.smode||'in';
  return `<div class="list">${shown.map(it=>{const v=Math.max(0,it.qty)*avgOf(it.id),ln=lines[it.id];
    return `<button class="row" data-act="st-item" data-id="${esc(it.id)}"><span class="dot ${isLow(it)?'out':'in'}"></span>
      <span class="main"><span class="t">${esc(it.name)}</span><span class="s"><span>${esc(it.cat||'')}${packsOf(it).length?'':' · ไม่มีบาร์โค้ด'}</span>
      ${isLow(it)?'<span class="chip bad">ใกล้หมด</span>':''}${mode==='count'?(ln?'<span class="chip ok">นับแล้ว</span>':'<span class="chip warn">ยังไม่นับ</span>'):''}</span></span>
      <span class="rem"><b class="${it.qty<0?'neg':''}">${qfmt(it.qty)} ${esc(it.unit)}</b>${isOwner()&&v?`<span class="muted small">${money(v)} บาท</span>`:''}</span></button>`}).join('')}</div>`;
}
const ICON_SCAN='<svg class="ic" viewBox="0 0 24 24" aria-hidden="true"><path d="M4 7V5a1 1 0 0 1 1-1h2M17 4h2a1 1 0 0 1 1 1v2M20 17v2a1 1 0 0 1-1 1h-2M7 20H5a1 1 0 0 1-1-1v-2M7 8v8M10 8v8M13 8v8M16 8v8"/></svg>';

/* operation sheet: receive / use / count one item. Every barcode = 1 unit of the item. */
const legacyPacks=it=>packsOf(it).filter(p=>p.pack!==1);
function openStockOp(id,mode,k){
  const it=stockItem(id);if(!it)return;
  const ps=packsOf(it);
  const modes=stockModes();if(!modes.length)return;mode=mode||ui.smode;if(!modes.includes(mode))mode=modes[0];
  sa={id,mode,k:k||(ps[0]?.k||''),scanned:!!k,qty:mode==='count'?'':'1',price:'',note:'',err:'',moves:null};
  prefillPrice();
  showSheet(stockOpHtml());
  loadMoves(id);
}
function prefillPrice(){
  if(!sa||sa.mode!=='in'||!isOwner())return;
  const it=stockItem(sa.id),p=packsOf(it).find(x=>x.k===sa.k);
  const lp=p&&p.pack===1?lastPrice(sa.id,p.k):'';
  sa.price=lp||(avgOf(sa.id)&&!legacyPacks(it).length?String(r2(avgOf(sa.id)*100)/100):'');
}
function readOp(){const g=x=>byId(x);if(!sa)return;if(g('so-qty'))sa.qty=g('so-qty').value;if(g('so-price'))sa.price=g('so-price').value;if(g('so-note'))sa.note=g('so-note').value}
function opTotal(){const n=numx(sa.qty===''?'0':sa.qty);return isFinite(n)?r2(n*1000)/1000:NaN}
function brandName(it,k){const nm=packNames(it);return nm[k]||''}
function stockOpHtml(){
  const it=stockItem(sa.id);if(!it)return `<div class="sh-head"><h2>ไม่พบรายการ</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>`;
  const ps=packsOf(it),p=ps.find(x=>x.k===sa.k),u=esc(it.unit),tot=opTotal(),avg=avgOf(it.id),legacy=legacyPacks(it).length>0;
  const locked=sa.mode==='count'&&!countOpen();
  const verb={in:'รับเข้า',use:'เบิกใช้',count:'นับได้'}[sa.mode];
  const diff=sa.mode==='count'&&isFinite(tot)&&sa.qty!==''?r2((tot-it.qty)*1000)/1000:null;
  const unitPrice=numx(sa.price)>0?numx(sa.price):0;
  const brands=ps.filter(x=>x.label).length>0||ps.length>1;
  return `<div class="sh-head"><h2>${esc(it.name)}</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
  <div class="card tight"><div class="ln"><span>คงเหลือ</span><b class="${it.qty<0?'neg':''}">${qfmt(it.qty)} ${u}</b></div>
    ${isOwner()?`<div class="ln"><span>ราคาเฉลี่ย</span><span>${avg?pfmt(avg)+' บาท / '+u:'ยังไม่มีราคา'}</span></div><div class="ln"><span>มูลค่า</span><span>${money(Math.max(0,it.qty)*avg)} บาท</span></div>`:''}
    ${+it.min?`<div class="ln"><span>ขั้นต่ำ</span><span>${qfmt(it.min)} ${u}</span></div>`:''}
    ${sa.scanned&&p&&brands?`<div class="ln"><span>สแกนได้</span><span>${esc(brandName(it,p.k))}</span></div>`:''}
    ${cache.count?.lines?.[it.id]?`<div class="ln small muted"><span>นับเดือนนี้แล้ว</span><span>${qfmt(cache.count.lines[it.id].c)} ${u}</span></div>`:''}</div>
  ${legacy&&isOwner()?`<div class="note">รายการนี้ยังตั้งแบบเดิม (1 ห่อ = ${legacyPacks(it).map(x=>qfmt(x.pack)).join(' / ')} ${u}) กด "แก้ไข" เพื่อเปลี่ยนเป็นนับเป็นกล่องหรือถุง</div>`:''}
  ${stockModes().length>1?`<div class="seg big3">${stockModes().map(k=>`<button data-act="so-mode" data-v="${k}" aria-pressed="${sa.mode===k}" class="t-${k==='in'?'in':k==='use'?'out':'move'}">${SMODE[k]}</button>`).join('')}</div>`:''}
  ${locked?`<div class="note">${esc(thMonth(curMonth()))} ปิดการนับแล้ว${isOwner()?' กด "เปิดการนับอีกครั้ง" ในหน้าสต็อกถ้าต้องนับใหม่':''}</div>`:`
  <label class="fld"><span>${verb} (${u})</span>
    <div class="qty-row"><button class="btn qbtn" data-act="so-dec" aria-label="ลด">−</button><input id="so-qty" class="amt-in t-${sa.mode==='in'?'in':sa.mode==='use'?'out':'move'}" inputmode="decimal" value="${esc(sa.qty)}" placeholder="0" autocomplete="off"><button class="btn qbtn" data-act="so-inc" aria-label="เพิ่ม">+</button></div></label>
  ${diff!==null?`<div class="ln"><span>ต่างจากในระบบ</span><b class="${diff<0?'out':diff>0?'in':''}">${diff>0?'+':''}${qfmt(diff)} ${u}${isOwner()&&avg&&diff?` (${diff>0?'+':'−'}${money(Math.abs(diff)*avg)} บาท)`:''}</b></div>`:''}
  ${sa.mode==='in'&&isOwner()?`${ps.length>1?`<div class="fld"><span>ยี่ห้อ</span><div class="chips">${ps.map(x=>`<button data-act="so-pack" data-v="${esc(x.k)}" aria-pressed="${sa.k===x.k}">${esc(brandName(it,x.k))}</button>`).join('')}</div></div>`:''}
    <label class="fld"><span>ราคาต่อ${u} (บาท) ไม่ใส่ก็ได้</span><input id="so-price" inputmode="decimal" value="${esc(sa.price)}" placeholder="ใช้คำนวณมูลค่าสต็อก" autocomplete="off"></label>
    ${unitPrice&&isFinite(tot)&&tot>0?`<span class="hint">รวม ${money(unitPrice*tot)} บาท · ราคาเฉลี่ยใหม่ ≈ ${pfmt(newAvg(it,tot,unitPrice))} บาท / ${u}</span>`:''}`:''}
  ${sa.mode!=='count'?`<label class="fld"><span>หมายเหตุ</span><input id="so-note" value="${esc(sa.note)}" maxlength="80" autocomplete="off" placeholder="${sa.mode==='in'?'เช่น Makro':'เช่น ทำบราวนี่'}"></label>`:''}
  ${sa.err?`<div class="err" style="margin-top:0">${esc(sa.err)}</div>`:''}`}
  <div class="sh-foot">${isOwner()?'<button class="btn ghost" data-act="st-edit">แก้ไข</button>':''}${locked?'<button class="btn primary" data-act="close">ปิด</button>':`<button class="btn" data-act="so-save" data-v="scan">บันทึก+สแกนต่อ</button><button class="btn primary" data-act="so-save">บันทึก</button>`}</div>
  <div class="fld"><span>ประวัติล่าสุด</span>${movesHtml(it)}</div>`;
}
function newAvg(it,q,unitPrice){const q0=Math.max(0,it.qty),a0=avgOf(it.id);return q0+q>0?(q0*a0+q*unitPrice)/(q0+q):unitPrice}
function movesHtml(it){
  if(!sa||sa.moves===null)return '<span class="hint">กำลังโหลด…</span>';
  if(sa.moves==='err')return '<span class="hint">โหลดประวัติไม่ได้ ต้องต่ออินเทอร์เน็ต</span>';
  if(!sa.moves.length)return '<span class="hint">ยังไม่มีประวัติ</span>';
  return `<div class="list">${sa.moves.slice(0,12).map(m=>`<div class="drow"><div class="main"><span class="t">${esc(SMOVE[m.t]||m.t)} ${m.q>0?'+':''}${qfmt(m.q)} ${esc(it.unit)}</span>
    <span class="s"><span>${esc(new Date(m.ts).toLocaleString('th-TH',{dateStyle:'short',timeStyle:'short'}))} · ${esc(m.email||'')}${m.note?' · '+esc(m.note):''}</span></span></div></div>`).join('')}</div>`;
}
async function loadMoves(id){
  try{const s=await getDocs(query(collection(fb.db,'stockmoves'),where('item','==',id)));
    if(!sa||sa.id!==id)return;sa.moves=s.docs.map(d=>d.data()).sort((a,b)=>(b.ts||0)-(a.ts||0));}
  catch(e){if(!sa||sa.id!==id)return;sa.moves='err'}
  readOp();showSheet(stockOpHtml(),true);
}
function stockMove(id,t,delta,extra){
  fire(setDoc(doc(fb.db,'stock',id),{qty:increment(delta),upd:Date.now()},{merge:true}),'stock');
  fire(setDoc(doc(collection(fb.db,'stockmoves')),{item:id,t,q:delta,ts:Date.now(),at:serverTimestamp(),by:user.uid,email:(user.email||'').toLowerCase(),m:curMonth(),...extra}),'stockmove');
}
function saveOp(again){
  readOp();const it=stockItem(sa.id);if(!it)return closeSheet();
  if(!canMode(sa.mode)){sa.err='คุณไม่มีสิทธิ์ทำรายการนี้';return showSheet(stockOpHtml(),true)}
  if(sa.mode==='count'&&!countOpen()){sa.err='เดือนนี้ปิดการนับแล้ว';return showSheet(stockOpHtml(),true)}
  const tot=opTotal();
  if(!isFinite(tot)||tot<0){sa.err='ใส่จำนวนเป็นตัวเลข';return showSheet(stockOpHtml(),true)}
  if(sa.mode!=='count'&&!(tot>0)){sa.err='ใส่จำนวนที่มากกว่า 0';return showSheet(stockOpHtml(),true)}
  if(sa.mode==='count'&&sa.qty===''){sa.err='ใส่จำนวนที่นับได้ ถ้าหมดแล้วใส่ 0';return showSheet(stockOpHtml(),true)}
  const note=(sa.note||'').trim();let msg='';
  if(sa.mode==='in'){
    const p=packsOf(it).find(x=>x.k===sa.k),price=numx(sa.price);
    if(isOwner()&&sa.price!==''){
      if(!(price>=0)){sa.err='ราคาต้องเป็นตัวเลข';return showSheet(stockOpHtml(),true)}
      const patch={avg:r4(newAvg(it,tot,price)),upd:Date.now()};if(p&&p.pack===1)patch.last={[p.k]:price};
      fire(setDoc(doc(fb.db,'stockcost',it.id),patch,{merge:true}),'stockcost');
    }
    stockMove(it.id,'in',tot,{note});msg=`รับเข้า ${it.name} ${qfmt(tot)} ${it.unit}`;
  }else if(sa.mode==='use'){
    stockMove(it.id,'use',-tot,{note});msg=`เบิกใช้ ${it.name} ${qfmt(tot)} ${it.unit}`;
  }else{
    const m=curMonth(),diff=r2((tot-it.qty)*1000)/1000;
    if(diff)stockMove(it.id,'adj',diff,{count:m,counted:tot});
    fire(setDoc(doc(fb.db,'stockcounts',m),{m,status:'open',lines:{[it.id]:{c:tot,e:it.qty,by:user.uid,email:(user.email||'').toLowerCase(),ts:Date.now()}}},{merge:true}),'count');
    msg=`นับ ${it.name} ได้ ${qfmt(tot)} ${it.unit}${diff?` (${diff>0?'+':''}${qfmt(diff)})`:''}`;
  }
  const mode=sa.mode;sa=null;closeSheet();toast(msg);
  if(again){ui.smode=mode;openScanner()}
}

/* item form (owner): add / edit. Each barcode = 1 unit; several barcodes = several brands of the same thing */
function openItemForm(id,opt={}){
  const it=id?stockItem(id):null;
  si={id,name:it?.name||'',unit:it?.unit||'กล่อง',cat:it?.cat||SCATS[0],min:it?String(it.min||''):'',
    codes:it?packsOf(it).map(p=>({c:p.c,pack:p.pack,label:p.label,price:p.pack===1?lastPrice(id,p.k):''})):(opt.code?[{c:opt.code,pack:1,label:'',price:''}]:[]),
    qty0:'',cost:id&&avgOf(id)?String(r4(avgOf(id))):'',err:'',link:opt.code&&!id?'':null,scanCode:opt.code||'',confirmOff:false,
    cunit:'กล่อง'};
  si.cost0=si.cost;
  showSheet(itemFormHtml());
}
const lastPrice=(id,k)=>{const v=cache.stockcost[id]?.last?.[k];return v!=null&&v!==''?String(v):''};
function readItem(){const g=x=>byId(x);if(!si)return;
  for(const k of ['name','min','qty0','cost'])if(g('si-'+k))si[k]=g('si-'+k).value;
  if(g('si-unit'))si.unit=g('si-unit').value;if(g('si-cat'))si.cat=g('si-cat').value;if(g('si-link'))si.link=g('si-link').value;if(g('si-cunit'))si.cunit=g('si-cunit').value;
  si.codes.forEach((c,i)=>{if(g('si-c-'+i))c.c=g('si-c-'+i).value.trim();if(g('si-l-'+i))c.label=g('si-l-'+i).value;if(g('si-r-'+i))c.price=g('si-r-'+i).value});
}
function convertHtml(){
  const it=si.id&&stockItem(si.id);if(!it)return '';
  const lp=legacyPacks(it);if(!lp.length)return '';
  const sizes=[...new Set(packsOf(it).map(p=>p.pack))];
  if(sizes.length>1)return `<div class="credit"><b>รายการนี้มีหลายขนาดปนกัน</b><span class="small">ตอนนี้นับเป็น${esc(it.unit)} และบาร์โค้ดแต่ละอันมีขนาดต่างกัน (${sizes.map(qfmt).join(' / ')} ${esc(it.unit)}) ควรแยกแต่ละขนาดเป็นคนละรายการ: กด "เอาออก" ที่บาร์โค้ดขนาดอื่นแล้วบันทึก จากนั้นสแกนบาร์โค้ดนั้นเพื่อเพิ่มเป็นรายการใหม่ แล้วค่อยกลับมาเปลี่ยนรายการนี้เป็นนับเป็นกล่อง</span></div>`;
  const P=sizes[0];
  return `<div class="credit"><b>เปลี่ยนเป็นนับตามที่หยิบใช้</b><span class="small">ตอนนี้นับเป็น${esc(it.unit)} โดย 1 ${esc(si.cunit)} = ${qfmt(P)} ${esc(it.unit)} ระบบจะแปลงยอดคงเหลือ ${qfmt(it.qty)} ${esc(it.unit)} เป็น ${qfmt(it.qty/P)} ${esc(si.cunit)} พร้อมปรับขั้นต่ำและราคาเฉลี่ยให้ ราคาต่อ${esc(si.cunit)}ที่บันทึกไว้ยังใช้ได้เหมือนเดิม</span>
    <div class="addrow"><select id="si-cunit" aria-label="หน่วยใหม่">${SUNITS.filter(x=>x!==it.unit).map(x=>`<option ${si.cunit===x?'selected':''}>${x}</option>`).join('')}</select><button class="btn sm danger" data-act="si-convert">เปลี่ยนเป็นนับเป็น${esc(si.cunit)}</button></div></div>`;
}
function itemFormHtml(){
  const others=stockItems().filter(x=>x.id!==si.id),u=esc(si.unit);
  return `<div class="sh-head"><h2>${si.id?'แก้ไขวัตถุดิบ':'เพิ่มวัตถุดิบ'}</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
  ${si.scanCode&&!si.id?`<div class="note">บาร์โค้ด <b>${esc(si.scanCode)}</b> ยังไม่มีในระบบ</div>
    ${others.length?`<div class="fld"><span>เป็นของชนิดเดียวกับที่มีอยู่แล้ว แต่คนละยี่ห้อ?</span><div class="addrow"><select id="si-link" aria-label="ผูกกับรายการที่มีอยู่"><option value="">ไม่ใช่ เพิ่มเป็นรายการใหม่</option>${others.map(o=>`<option value="${esc(o.id)}" ${si.link===o.id?'selected':''}>${esc(o.name)}</option>`).join('')}</select></div></div>`:''}`:''}
  ${si.link?(()=>{const t=stockItem(si.link);return `<div class="two"><label class="fld"><span class="small">ยี่ห้อ (ไม่ใส่ก็ได้)</span><input id="si-l-0" value="${esc(si.codes[0]?.label||'')}" placeholder="เช่น Aroma"></label>
      <label class="fld"><span class="small">ราคาต่อ${esc(t?.unit||'')} (บาท)</span><input id="si-r-0" inputmode="decimal" value="${esc(si.codes[0]?.price||'')}" placeholder="ไม่ใส่ก็ได้"></label></div>
      <span class="hint">สแกนบาร์โค้ดนี้ 1 ครั้ง = 1 ${esc(t?.unit||'')} ของ ${esc(t?.name||'')}</span>`})():`
  ${convertHtml()}
  <label class="fld"><span>ชื่อวัตถุดิบ</span><input id="si-name" value="${esc(si.name)}" maxlength="60" placeholder="เช่น ครีมเหลว 1 ลิตร, กะทิ 250 มล." autocomplete="off"></label>
  <div class="two"><label class="fld"><span>นับเป็น</span><select id="si-unit">${(SUNITS.includes(si.unit)?SUNITS:[si.unit,...SUNITS]).map(x=>`<option ${si.unit===x?'selected':''}>${x}</option>`).join('')}</select></label>
    <label class="fld"><span>หมวด</span><select id="si-cat">${SCATS.map(c=>`<option ${si.cat===c?'selected':''}>${c}</option>`).join('')}</select></label></div>
  <span class="hint">นับตามที่หยิบใช้จริง เช่น กล่อง ถุง ขวด สแกน 1 ครั้ง = 1 ${u} ถ้ามีหลายขนาด เช่น กะทิ 150 มล. กับ 250 มล. ให้เพิ่มเป็นคนละรายการ</span>
  <div class="fld"><span>บาร์โค้ด</span>
    ${si.codes.length?si.codes.map((c,i)=>`<div class="codebox"><div class="addrow"><input id="si-c-${i}" value="${esc(c.c)}" inputmode="numeric" placeholder="รหัสบาร์โค้ด" aria-label="รหัสบาร์โค้ด"><button class="btn sm" data-act="si-rmcode" data-v="${i}">เอาออก</button></div>
      <div class="two"><label class="fld"><span class="small">ยี่ห้อ (ไม่ใส่ก็ได้)</span><input id="si-l-${i}" value="${esc(c.label)}" placeholder="เช่น Aroma"></label>
        ${c.pack===1?`<label class="fld"><span class="small">ราคาต่อ${u} (บาท)</span><input id="si-r-${i}" inputmode="decimal" value="${esc(c.price||'')}" placeholder="ไม่ใส่ก็ได้"></label>`:`<span class="hint">1 ห่อ = ${qfmt(c.pack)} ${u} (แบบเดิม)</span>`}</div></div>`).join('')
      :'<span class="hint">ไม่มีบาร์โค้ด แตะเลือกจากรายการแทนได้</span>'}
    <div class="btns"><button class="btn sm" data-act="si-addcode">+ เพิ่มบาร์โค้ด</button><button class="btn sm" data-act="si-scancode">${ICON_SCAN} สแกนเพิ่ม</button></div>
    ${si.codes.length>1?'<span class="hint">หลายบาร์โค้ดในรายการเดียว = ของเดียวกันคนละยี่ห้อ สแกนยี่ห้อไหนก็นับรวมกัน</span>':''}</div>
  <div class="two"><label class="fld"><span>ขั้นต่ำก่อนต้องซื้อ (${u})</span><input id="si-min" inputmode="decimal" value="${esc(si.min)}" placeholder="0 = ไม่เตือน"></label>
    <label class="fld"><span>ราคาเฉลี่ยต่อ${u} (บาท)</span><input id="si-cost" inputmode="decimal" value="${esc(si.cost)}" placeholder="คิดจากราคาด้านบนให้"></label></div>
  ${si.id?'':`<label class="fld"><span>มีอยู่ตอนนี้ (${u})</span><input id="si-qty0" inputmode="decimal" value="${esc(si.qty0)}" placeholder="0"></label>`}`}
  ${si.err?`<div class="err" style="margin-top:0">${esc(si.err)}</div>`:''}
  <div class="sh-foot">${si.id?(si.confirmOff?'<button class="btn danger" data-act="si-off-yes">ยืนยันเลิกใช้</button>':'<button class="btn ghost danger-t" data-act="si-off">เลิกใช้รายการนี้</button>'):''}<button class="btn primary" data-act="si-save">บันทึก</button></div>`;
}
function convertItem(){
  readItem();const it=stockItem(si.id);if(!it)return;
  const sizes=[...new Set(packsOf(it).map(p=>p.pack))];if(sizes.length!==1||sizes[0]===1)return;
  const P=sizes[0],nu=si.cunit,codes={};
  for(const p of packsOf(it))codes[p.k]={c:p.c,pack:1,label:p.label||''};
  const qty=r2(it.qty/P*1000)/1000,min=r2((+it.min||0)/P*1000)/1000;
  fire(setDoc(doc(fb.db,'stock',it.id),{unit:nu,min,codes,qty,upd:Date.now()},{mergeFields:['unit','min','codes','qty','upd']}),'convert');
  const a=avgOf(it.id);if(a)fire(setDoc(doc(fb.db,'stockcost',it.id),{avg:r4(a*P),upd:Date.now()},{merge:true}),'convert-cost');
  const ln=cache.count?.lines?.[it.id];
  if(ln&&countOpen())fire(setDoc(doc(fb.db,'stockcounts',curMonth()),{m:curMonth(),status:'open',lines:{[it.id]:{...ln,c:r2(ln.c/P*1000)/1000,e:r2(ln.e/P*1000)/1000}}},{merge:true}),'convert-count');
  fire(setDoc(doc(collection(fb.db,'stockmoves')),{item:it.id,t:'conv',q:0,ts:Date.now(),at:serverTimestamp(),by:user.uid,email:(user.email||'').toLowerCase(),m:curMonth(),note:`เปลี่ยนจาก${it.unit}เป็น${nu} (1 ${nu} = ${qfmt(P)} ${it.unit})`}),'stockmove');
  audit('stock-edit','','',{name:it.name,unit:it.unit,qty:it.qty},{name:it.name,unit:nu,qty});
  cache.stock[it.id]={...cache.stock[it.id],unit:nu,min,codes,qty};
  closeSheet();toast(`${it.name}: นับเป็น${nu}แล้ว เหลือ ${qfmt(qty)} ${nu}`);
}
function saveItem(){
  readItem();
  const used=c=>{const f=findByCode(c);return f&&f.item.id!==(si.link||si.id)?f.item.name:''};
  if(si.link){
    const tgt=stockItem(si.link);
    const pr=si.codes[0]?.price||'',price=pr===''?null:numx(pr);
    if(price!==null&&!(price>=0)){si.err='ราคาต้องเป็นตัวเลข';return showSheet(itemFormHtml(),true)}
    const k=codeKey(si.scanCode),entry={c:si.scanCode,pack:1,label:(si.codes[0]?.label||'').trim()};
    if(price!==null){const patch={last:{[k]:price},upd:Date.now()};if(!avgOf(si.link))patch.avg=price;
      fire(setDoc(doc(fb.db,'stockcost',si.link),patch,{merge:true}),'stockcost');
      cache.stockcost[si.link]={...(cache.stockcost[si.link]||{}),...patch,last:{...(cache.stockcost[si.link]?.last||{}),[k]:price}}}
    fire(setDoc(doc(fb.db,'stock',si.link),{codes:{[k]:entry},upd:Date.now()},{merge:true}),'item');
    if(cache.stock[si.link])cache.stock[si.link]={...cache.stock[si.link],codes:{...(cache.stock[si.link].codes||{}),[k]:entry}};
    const id=si.link;si=null;closeSheet();toast(`เพิ่มบาร์โค้ดให้ ${tgt?.name||''} แล้ว`);openStockOp(id,ui.smode,k);return;
  }
  const name=si.name.trim();if(!name){si.err='ใส่ชื่อวัตถุดิบ';return showSheet(itemFormHtml(),true)}
  const codes={},last={},prices=[],seen=new Set();
  for(const c of si.codes){if(!c.c)continue;
    if(seen.has(c.c)){si.err=`บาร์โค้ด ${c.c} ซ้ำกัน`;return showSheet(itemFormHtml(),true)}seen.add(c.c);
    const u=used(c.c);if(u){si.err=`บาร์โค้ด ${c.c} ใช้กับ "${u}" อยู่แล้ว`;return showSheet(itemFormHtml(),true)}
    const pack=+c.pack||1,k=codeKey(c.c);
    if(pack===1&&c.price!==''&&c.price!=null){const pr=numx(c.price);if(!(pr>=0)){si.err=`ราคาของ ${c.c} ต้องเป็นตัวเลข`;return showSheet(itemFormHtml(),true)}last[k]=pr;prices.push(pr)}
    codes[k]={c:c.c,pack,label:(c.label||'').trim()}}
  const min=si.min===''?0:numx(si.min),cost=si.cost===''?null:numx(si.cost),q0=si.qty0===''?0:numx(si.qty0);
  if(!(min>=0)||(cost!==null&&!(cost>=0))||!(q0>=0)){si.err='ขั้นต่ำ ราคา และจำนวนต้องเป็นตัวเลข';return showSheet(itemFormHtml(),true)}
  const isNew=!si.id,id=si.id||('s'+rid());
  const data={name,unit:si.unit,cat:si.cat,min,codes,upd:Date.now()};
  if(isNew){data.qty=q0;data.at=Date.now();data.by=user.uid}
  // on edit, replace these fields whole (so removed barcodes disappear) and leave qty alone
  fire(isNew?setDoc(doc(fb.db,'stock',id),data):setDoc(doc(fb.db,'stock',id),data,{mergeFields:['name','unit','cat','min','codes','upd']}),'item');
  // average cost: typed value wins; otherwise start from the barcode prices if there is no average yet
  let avg=null;
  if(cost!==null&&si.cost!==si.cost0)avg=cost;
  else if(!avgOf(id)&&prices.length)avg=r4(prices.reduce((a,b)=>a+b,0)/prices.length);
  else if(isNew&&cost!==null)avg=cost;
  const cpatch={upd:Date.now()};if(avg!==null)cpatch.avg=avg;if(Object.keys(last).length)cpatch.last=last;
  if(avg!==null||cpatch.last)fire(setDoc(doc(fb.db,'stockcost',id),cpatch,{merge:true}),'stockcost');
  if(isNew&&q0)fire(setDoc(doc(collection(fb.db,'stockmoves')),{item:id,t:'init',q:q0,ts:Date.now(),at:serverTimestamp(),by:user.uid,email:(user.email||'').toLowerCase(),m:curMonth(),note:''}),'stockmove');
  audit(isNew?'stock-add':'stock-edit','','',null,{name,unit:si.unit});
  si=null;closeSheet();toast(isNew?`เพิ่ม ${name} แล้ว`:'บันทึกแล้ว');
}

/* camera scanner: native BarcodeDetector (Android Chrome) or ZXing (iPhone and others) */
function loadZXing(){return zxP||(zxP=new Promise((res,rej)=>{const s=document.createElement('script');s.src='vendor/zxing-0.21.3.min.js';s.onload=res;s.onerror=()=>{zxP=null;rej(new Error('zxing'))};document.head.appendChild(s)}))}
let scanTarget='op';
function openScanner(target){
  scanTarget=target||'op';
  showSheet(`<div class="sh-head"><h2>สแกนบาร์โค้ด${scanTarget==='op'?' · '+SMODE[ui.smode||'in']:''}</h2><button class="icon" data-act="st-scan-close" aria-label="ปิด">×</button></div>
    <div class="scanbox"><video id="scan-v" playsinline muted autoplay></video><div class="scanline"></div></div>
    <div id="scan-msg" class="hint">กำลังเปิดกล้อง… เล็งให้เส้นแดงพาดผ่านบาร์โค้ด</div>
    <form id="scan-form" class="addrow"><input id="scan-code" inputmode="numeric" autocomplete="off" placeholder="หรือพิมพ์รหัส / ใช้เครื่องยิงบาร์โค้ด" aria-label="รหัสบาร์โค้ด"><button class="btn sm" type="submit">ตกลง</button></form>
    <div class="sh-foot"><button class="btn primary" data-act="st-scan-close">ปิดกล้อง</button></div>`);
  startScan();
}
async function startScan(){
  stopScan();const v=byId('scan-v'),msg=()=>byId('scan-msg');
  if(!v)return;
  if(!navigator.mediaDevices?.getUserMedia){msg().textContent='เครื่องนี้เปิดกล้องจากแอปไม่ได้ พิมพ์รหัสบาร์โค้ดแทน';return}
  const s={on:true,stop(){this.on=false;try{this.reader?.reset()}catch(e){}this.stream?.getTracks().forEach(t=>t.stop())}};scanner=s;
  const cons={video:{facingMode:{ideal:'environment'},width:{ideal:1280},height:{ideal:720}},audio:false};
  try{
    if('BarcodeDetector' in window){
      const fm=await BarcodeDetector.getSupportedFormats().catch(()=>[]);
      const want=['ean_13','ean_8','upc_a','upc_e','code_128','code_39','itf','qr_code'].filter(f=>fm.includes(f));
      if(want.length){
        s.stream=await navigator.mediaDevices.getUserMedia(cons);if(!s.on){s.stop();return}
        v.srcObject=s.stream;await v.play().catch(()=>{});
        const det=new BarcodeDetector({formats:want});msg().textContent='เล็งให้เส้นแดงพาดผ่านบาร์โค้ด';
        const tick=async()=>{if(!s.on)return;try{const r=await det.detect(v);if(r.length&&s.on){gotCode(r[0].rawValue);return}}catch(e){}setTimeout(tick,150)};tick();return;
      }
    }
    await loadZXing();if(!s.on)return;
    // no decode hints: passing TRY_HARDER stops this ZXing build from reading 1D barcodes
    s.reader=new ZXing.BrowserMultiFormatReader(undefined,250);
    msg().textContent='เล็งให้เส้นแดงพาดผ่านบาร์โค้ด';
    await s.reader.decodeFromConstraints(cons,v,res=>{if(res&&s.on)gotCode(res.getText())});
  }catch(e){
    console.warn('scan',e);if(scanner===s)s.stop();
    const m=msg();if(m)m.textContent=e?.name==='NotAllowedError'?'แอปยังไม่ได้รับอนุญาตให้ใช้กล้อง ไปที่การตั้งค่าของมือถือ แล้วอนุญาตกล้องให้เบราว์เซอร์ หรือพิมพ์รหัสแทน'
      :e?.message==='zxing'?'โหลดตัวอ่านบาร์โค้ดไม่ได้ ต่ออินเทอร์เน็ตครั้งแรกก่อน หรือพิมพ์รหัสแทน':'เปิดกล้องไม่ได้ พิมพ์รหัสบาร์โค้ดแทน';
  }
}
function stopScan(){if(scanner){const s=scanner;scanner=null;s.stop()}}
function gotCode(code){stopScan();try{navigator.vibrate&&navigator.vibrate(60)}catch(e){}handleCode(String(code||'').trim())}
function handleCode(code){
  if(!code)return;
  if(scanTarget==='item'&&si){si.codes.push({c:code,pack:'1',label:''});showSheet(itemFormHtml());return}
  const f=findByCode(code);
  if(f){openStockOp(f.item.id,ui.smode||'in',f.k);return}
  if(isOwner()){openItemForm(null,{code});return}
  showSheet(`<div class="sh-head"><h2>ไม่พบบาร์โค้ดนี้</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
    <p>รหัส <b>${esc(code)}</b> ยังไม่มีในระบบ ให้เจ้าของร้านสแกนเพิ่มเป็นวัตถุดิบก่อน หรือแตะเลือกจากรายการแทน</p>
    <div class="sh-foot"><button class="btn" data-act="close">ปิด</button><button class="btn primary" data-act="st-scan">สแกนใหม่</button></div>`);
}

/* owner: close the monthly count and keep a value snapshot */
function closeCount(){
  const m=curMonth(),items=stockItems(),lines=cache.count?.lines||{};
  let total=0,diffVal=0;const snap={};
  for(const it of items){const a=avgOf(it.id),val=Math.max(0,it.qty)*a;total+=val;
    const ln=lines[it.id];if(ln)diffVal+=(+ln.c-(+ln.e))*a;
    snap[it.id]={n:it.name,u:it.unit,q:it.qty,avg:a,val:r2(val),counted:!!ln}}
  fire(setDoc(doc(fb.db,'stockvals',m),{m,ts:Date.now(),by:user.uid,total:r2(total),diffVal:r2(diffVal),counted:Object.keys(lines).length,items:snap}),'stockvals');
  fire(setDoc(doc(fb.db,'stockcounts',m),{m,status:'done',doneBy:user.uid,doneTs:Date.now()},{merge:true}),'count');
  audit('stock-close','','',null,{m,total:r2(total)});
  cache.stockvals=null;ui.stClose=false;toast(`ปิดการนับ ${thMonth(m)} · มูลค่าสต็อก ${money(total)} บาท`);render();
}
async function openStockHistory(){
  showSheet(`<div class="sh-head"><h2>มูลค่าสต็อกสิ้นเดือน</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div><div class="empty"><b>กำลังโหลด</b></div>`);
  try{
    const s=await getDocs(collection(fb.db,'stockvals'));const rows=s.docs.map(d=>d.data()).sort((a,b)=>String(b.m).localeCompare(String(a.m)));
    showSheet(`<div class="sh-head"><h2>มูลค่าสต็อกสิ้นเดือน</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div>
      ${rows.length?`<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>เดือน</th><th>มูลค่า</th><th>ขาด/เกินจากการนับ</th></tr></thead><tbody>
      ${rows.map(r=>`<tr><td>${esc(thMonth(r.m))}</td><td>${money(r.total||0)}</td><td class="${(r.diffVal||0)<0?'out':(r.diffVal||0)>0?'in':''}">${(r.diffVal||0)>0?'+':''}${money(r.diffVal||0)}</td></tr>`).join('')}</tbody></table></div>
      <span class="hint">บันทึกตอนกด "ปิดการนับ" ของแต่ละเดือน · ติดลบ = ของในระบบมากกว่าที่นับได้จริง (ใช้ไปโดยไม่ได้เบิก เสีย หรือหาย)</span>`
      :'<div class="empty"><b>ยังไม่มีข้อมูล</b><p>จะเริ่มมีเมื่อปิดการนับสต็อกเดือนแรก</p></div>'}
      <div class="sh-foot"><button class="btn primary" data-act="close">ปิด</button></div>`);
  }catch(e){showSheet(`<div class="sh-head"><h2>มูลค่าสต็อกสิ้นเดือน</h2><button class="icon" data-act="close" aria-label="ปิด">×</button></div><div class="empty"><b>โหลดไม่ได้</b><p>ต้องต่ออินเทอร์เน็ต</p></div>`)}
}
function exportStockCsv(){
  const cell=v=>{if(typeof v==='number')return String(v);let s=String(v??'');if(/^[=+\-@]/.test(s))s="'"+s;return /[",\r\n]/.test(s)?'"'+s.replace(/"/g,'""')+'"':s};
  const lines=cache.count?.lines||{};
  const rows=stockItems().map(it=>{const a=avgOf(it.id);return [it.name,it.cat||'',it.qty,it.unit,r4(a),r2(Math.max(0,it.qty)*a),+it.min||0,lines[it.id]?'นับแล้ว':'',packsOf(it).map(p=>p.c).join(' ')]});
  const csv='﻿'+[['วัตถุดิบ','หมวด','คงเหลือ','หน่วย','ราคาเฉลี่ยต่อหน่วย','มูลค่า','ขั้นต่ำ',`นับ ${curMonth()}`,'บาร์โค้ด'],...rows].map(r=>r.map(cell).join(',')).join('\r\n');
  saveFile(`สต็อก-${todayKey()}.csv`,csv,'text/csv;charset=utf-8');
}

/* ---------- sign-in and access ---------- */
const AUTH_ERR={'auth/invalid-credential':'อีเมลหรือรหัสผ่านไม่ถูกต้อง','auth/wrong-password':'อีเมลหรือรหัสผ่านไม่ถูกต้อง','auth/user-not-found':'ไม่พบบัญชีนี้ ลองกด "สมัครใช้งาน"',
  'auth/email-already-in-use':'อีเมลนี้สมัครแล้ว ให้กด "เข้าสู่ระบบ" แทน','auth/weak-password':'รหัสผ่านต้องยาวอย่างน้อย 6 ตัวอักษร','auth/invalid-email':'รูปแบบอีเมลไม่ถูกต้อง',
  'auth/missing-password':'ใส่รหัสผ่าน','auth/too-many-requests':'ลองหลายครั้งเกินไป รอสักครู่แล้วลองใหม่','auth/network-request-failed':'ต่ออินเทอร์เน็ตไม่ได้',
  'auth/popup-closed-by-user':'ปิดหน้าต่างก่อนเข้าสู่ระบบเสร็จ','auth/popup-blocked':'เบราว์เซอร์บล็อกหน้าต่าง ให้ใช้อีเมลและรหัสผ่านแทน',
  'auth/operation-not-allowed':'ยังไม่ได้เปิดวิธีเข้าสู่ระบบนี้ใน Firebase','auth/unauthorized-domain':'ยังไม่ได้เพิ่มโดเมนเว็บนี้ใน Firebase (Authorized domains)'};
let gate={mode:'signin',email:'',err:'',busy:false,info:''};
function showGate(mode,extra){
  gateMode=mode;if(extra)Object.assign(gate,extra);
  byId('app').hidden=true;byId('fab').hidden=true;byId('gate').hidden=false;closeSheet();
  const brand=`<div class="g-brand"><img src="icons/icon-192.png" alt="โลโก้ขนมบ้านเพลง" width="96" height="96"><div><b>บัญชีขนมบ้านเพลง</b><span>บัญชีรายรับ-รายจ่ายของร้าน</span></div></div>`;
  const out=`<button class="link" data-act="signout">ออกจากระบบ</button>`;
  let body='';
  if(mode==='setup')body=`<h2>ยังไม่ได้เชื่อม Firebase</h2><p>ใส่ค่าใน firebase-config.js ก่อนใช้งาน</p>`;
  else if(mode==='loading')body=`<p class="muted">กำลังเปิดบัญชี…</p>`;
  else if(mode==='signin'||mode==='signup')body=`
    <form id="authform" class="gform" novalidate>
      <h2>${mode==='signin'?'เข้าสู่ระบบ':'สมัครใช้งาน'}</h2>
      <label class="fld"><span>อีเมล</span><input id="g-email" type="email" inputmode="email" autocomplete="username" value="${esc(gate.email)}" required></label>
      <label class="fld"><span>รหัสผ่าน${mode==='signup'?' (อย่างน้อย 6 ตัว)':''}</span><input id="g-pass" type="password" autocomplete="${mode==='signin'?'current-password':'new-password'}" required></label>
      ${gate.err?`<div class="err" style="margin-top:0">${esc(gate.err)}</div>`:''}${gate.info?`<div class="note">${esc(gate.info)}</div>`:''}
      <button class="btn primary" type="submit" ${gate.busy?'disabled':''}>${gate.busy?'กำลังดำเนินการ…':mode==='signin'?'เข้าสู่ระบบ':'สมัครใช้งาน'}</button>
      <button class="btn" type="button" data-act="g-google" ${gate.busy?'disabled':''}>เข้าด้วยบัญชี Google</button>
      <div class="g-links">${mode==='signin'?`<button class="link" type="button" data-act="g-mode" data-v="signup">สมัครใช้งานใหม่</button><button class="link" type="button" data-act="g-reset">ลืมรหัสผ่าน</button>`
        :`<button class="link" type="button" data-act="g-mode" data-v="signin">มีบัญชีแล้ว เข้าสู่ระบบ</button>`}</div>
    </form>`;
  else if(mode==='claim')body=`<h2>ตั้งค่าเจ้าของร้าน</h2><p>ยังไม่มีเจ้าของร้านในระบบ บัญชีแรกที่กดปุ่มนี้จะเป็นเจ้าของร้าน ดูรายงานและตั้งค่าได้ทั้งหมด</p>
    <p class="muted small">${esc(user?.email||'')}</p>${gate.err?`<div class="err" style="margin-top:0">${esc(gate.err)}</div>`:''}
    <button class="btn primary" data-act="g-claim" ${gate.busy?'disabled':''}>ฉันคือเจ้าของร้าน</button>${out}`;
  else if(mode==='verify')body=`<h2>ยืนยันอีเมลก่อน</h2><p>เจ้าของร้านเชิญอีเมล <b>${esc(user?.email||'')}</b> แล้ว ระบบส่งลิงก์ยืนยันไปที่อีเมลนี้ กดลิงก์ในอีเมล แล้วกลับมากดปุ่มด้านล่าง</p>
    ${gate.err?`<div class="err" style="margin-top:0">${esc(gate.err)}</div>`:''}${gate.info?`<div class="note">${esc(gate.info)}</div>`:''}
    <button class="btn primary" data-act="g-verified" ${gate.busy?'disabled':''}>ยืนยันอีเมลแล้ว</button><button class="btn" data-act="g-resend">ส่งลิงก์อีกครั้ง</button>${out}`;
  else if(mode==='denied')body=`<h2>บัญชีนี้ยังไม่ได้รับอนุญาต</h2><p>ให้เจ้าของร้านเพิ่มอีเมล <b>${esc(user?.email||'')}</b> ในหน้าตั้งค่า → ผู้ใช้งาน แล้วกดปุ่มด้านล่าง</p>
    <button class="btn primary" data-act="g-retry">ลองอีกครั้ง</button>${out}`;
  else if(mode==='offline')body=`<h2>ต้องต่ออินเทอร์เน็ตครั้งแรก</h2><p>เครื่องนี้ยังไม่เคยโหลดข้อมูลร้าน ต่อเน็ตแล้วกดลองอีกครั้ง หลังจากนั้นเปิดได้แม้ไม่มีเน็ต</p><button class="btn primary" data-act="g-retry">ลองอีกครั้ง</button>${out}`;
  else body=`<h2>เกิดข้อผิดพลาด</h2><p>${esc(gate.err||'เปิดบัญชีไม่ได้')}</p><button class="btn primary" data-act="g-retry">ลองอีกครั้ง</button>${out}`;
  byId('gate').innerHTML=`<div class="gcard">${brand}${body}</div>`;
}
function showApp(){byId('gate').hidden=true;byId('app').hidden=false;gateMode=''}
function stopAll(){if(memberUnsub){memberUnsub();memberUnsub=null}stopData();role=null;perms=null;canWrite=false;byId('view').innerHTML='';byId('panel').innerHTML=''}
function watchMember(){
  if(memberUnsub)memberUnsub();
  showGate('loading');
  memberUnsub=onSnapshot(doc(fb.db,'members',user.uid),{includeMetadataChanges:true},snap=>{
    if(snap.exists()){
      if(snap.metadata.hasPendingWrites)return; // wait until the server has saved the membership
      const d=snap.data(),first=!role,prevKey=role+JSON.stringify(perms);
      role=d.role==='owner'?'owner':'staff';perms=role==='staff'?(d.perms&&typeof d.perms==='object'?d.perms:DEFAULT_PERMS):null;canWrite=true;
      if(first){showApp();subscribe()}else if(prevKey!==role+JSON.stringify(perms)){closeSheet();subscribe()}render();return;
    }
    if(snap.metadata.fromCache){if(navigator.onLine===false)showGate('offline');return}
    const had=!!role;role=null;canWrite=false;if(had)stopData();
    resolveAccess();
  },e=>{console.error(e);showGate('error',{err:e?.code==='permission-denied'?'ยังไม่ได้ตั้งกฎความปลอดภัยใน Firestore':'เชื่อมต่อฐานข้อมูลไม่ได้'})});
}
async function resolveAccess(){
  try{
    const o=await getDoc(doc(fb.db,'meta','owner'));
    if(!o.exists()){showGate('claim',{err:'',busy:false});return}
    const em=(user.email||'').toLowerCase();
    const inv=em?await getDoc(doc(fb.db,'invites',em)):null;
    if(inv&&inv.exists()){
      if(!user.emailVerified){showGate('verify',{err:'',info:'',busy:false});return}
      const r=inv.data().role==='owner'?'owner':'staff';
      const ip=inv.data().perms,mdoc={role:r,email:em,at:serverTimestamp()};if(ip&&typeof ip==='object')mdoc.perms=ip;
      await setDoc(doc(fb.db,'members',user.uid),mdoc);
      return;
    }
    showGate('denied');
  }catch(e){console.error(e);showGate(navigator.onLine===false?'offline':'error',{err:e?.code==='permission-denied'?'ยังไม่ได้ตั้งกฎความปลอดภัยใน Firestore หรือกฎไม่ถูกต้อง':'เชื่อมต่อฐานข้อมูลไม่ได้'})}
}
async function gateAction(a,v){
  const auth=fb.auth;
  try{
    if(a==='g-mode'){gate.err='';gate.info='';showGate(v);return}
    if(a==='g-google'){gate.busy=true;gate.err='';showGate(gateMode);await signInWithPopup(auth,new GoogleAuthProvider());return}
    if(a==='g-reset'){
      const em=(byId('g-email')?.value||'').trim();gate.email=em;
      if(!em){gate.err='ใส่อีเมลก่อน แล้วกด "ลืมรหัสผ่าน" อีกครั้ง';showGate(gateMode);return}
      await sendPasswordResetEmail(auth,em);gate.err='';gate.info=`ส่งลิงก์ตั้งรหัสผ่านใหม่ไปที่ ${em} แล้ว`;showGate(gateMode);return;
    }
    if(a==='g-claim'){
      gate.busy=true;showGate('claim');
      const b=writeBatch(fb.db);
      b.set(doc(fb.db,'meta','owner'),{uid:user.uid,at:serverTimestamp()});
      b.set(doc(fb.db,'members',user.uid),{role:'owner',email:(user.email||'').toLowerCase(),at:serverTimestamp()});
      await b.commit();gate.busy=false;return;
    }
    if(a==='g-resend'){await sendEmailVerification(user);gate.info='ส่งลิงก์ยืนยันอีกครั้งแล้ว ดูในกล่องจดหมายหรือจดหมายขยะ';gate.err='';showGate('verify');return}
    if(a==='g-verified'){
      gate.busy=true;showGate('verify');await user.reload();await user.getIdToken(true);gate.busy=false;
      if(!user.emailVerified){gate.err='ยังไม่พบการยืนยัน กดลิงก์ในอีเมลก่อน';showGate('verify');return}
      showGate('loading');await resolveAccess();return;
    }
    if(a==='g-retry'){if(user){showGate('loading');watchMember()}else showGate('signin');return}
  }catch(e){console.error(e);gate.busy=false;gate.err=AUTH_ERR[e?.code]||(e?.code==='permission-denied'?'มีเจ้าของร้านแล้ว หรือกฎความปลอดภัยไม่ถูกต้อง':'ทำรายการไม่สำเร็จ ลองใหม่อีกครั้ง');showGate(gateMode||'signin')}
}
async function submitAuth(){
  const em=(byId('g-email').value||'').trim(),pw=byId('g-pass').value||'';gate.email=em;
  if(!em||!pw){gate.err='ใส่อีเมลและรหัสผ่าน';showGate(gateMode);return}
  gate.busy=true;gate.err='';gate.info='';showGate(gateMode);
  try{
    if(gateMode==='signup'){const c=await createUserWithEmailAndPassword(fb.auth,em,pw);try{await sendEmailVerification(c.user)}catch(e){}}
    else await signInWithEmailAndPassword(fb.auth,em,pw);
    gate.busy=false;
  }catch(e){gate.busy=false;gate.err=AUTH_ERR[e?.code]||'เข้าสู่ระบบไม่สำเร็จ';showGate(gateMode)}
}

function boot(){
  if('serviceWorker' in navigator)navigator.serviceWorker.register('./sw.js').catch(e=>console.warn('sw',e));
  if(!firebaseConfig||!firebaseConfig.projectId){showGate('setup');return}
  const app=initializeApp(firebaseConfig);
  const auth=initializeAuth(app,{persistence:[indexedDBLocalPersistence,browserLocalPersistence],popupRedirectResolver:browserPopupRedirectResolver});
  let db;
  try{db=initializeFirestore(app,{localCache:persistentLocalCache({tabManager:persistentMultipleTabManager()}),ignoreUndefinedProperties:true})}
  catch(e){console.warn('offline cache unavailable',e);db=initializeFirestore(app,{ignoreUndefinedProperties:true})}
  fb={app,auth,db};
  showGate('loading');
  onAuthStateChanged(auth,u=>{
    const same=u&&user&&u.uid===user.uid;user=u;
    if(same)return;
    stopAll();
    if(!u){gate={mode:'signin',email:gate.email||'',err:'',busy:false,info:''};showGate('signin');return}
    watchMember();
  });
  window.addEventListener('online',()=>{renderStatus();if(gateMode==='offline'&&user)watchMember()});
  window.addEventListener('offline',renderStatus);
}
boot();
