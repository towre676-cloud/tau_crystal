import json,sys,os
def fix(path_in, path_out=None):
    if not os.path.exists(path_in): return False
    d=json.load(open(path_in,encoding='utf-8'))
    node=d.get('confirm', d)
    zeros=node.get('critical_line_zeros_gl2') or []
    hits=node.get('sym2_outside_hits') or []
    node['critical_line_zeros_gl2']=list(zeros)
    node['sym2_outside_hits']=list(hits)
    node['flag']=bool(zeros) and bool(hits)
    t=node.get('turing_count_0T', None)
    try: node['turing_count_0T']=float(t) if t is not None else None
    except Exception: node['turing_count_0T']=None
    if 'confirm' in d: d['confirm']=node
    p=path_out or path_in
    json.dump(d, open(p,'w',encoding='utf-8'), ensure_ascii=False, separators=(',',':'))
    print('[fixed]', p)
    return True
if __name__=='__main__':
    cands=['.tau_ledger/discovery/confirm_double_zero_stable.json','.tau_ledger/discovery/confirm_double_zero.json']
    for p in cands:
        if fix(p): break
