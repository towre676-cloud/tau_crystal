(async () => {
  const metaEl = document.getElementById('meta');
  const tbody  = document.querySelector('#t tbody');
  const m = await (await fetch('./_manifest.json')).json();
  metaEl.textContent = JSON.stringify(m, null, 2);
  const text = await (await fetch('./data/atlas.jsonl')).text();
  for (const L of text.trim().split(/\n/).slice(-200)) {
    let o={}; try{o=JSON.parse(L);}catch{continue;}
    const tr=document.createElement('tr');
    const extra=('mirror_ok'in o)?`mirror_ok=${o.mirror_ok}`:('agree'in o)?`agree=${o.agree}`:'';
    tr.innerHTML=`<td>${o.type||''}</td><td>${o.label||''}</td><td>${o.ts||''}</td><td>${extra}</td>`;
    tbody.appendChild(tr);
  }
})();
