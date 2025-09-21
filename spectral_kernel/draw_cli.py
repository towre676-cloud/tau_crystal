import sys, json, os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import networkx as nx

inp = sys.argv[1] if len(sys.argv) > 1 else "trace.json"
data = json.load(open(inp, "r", encoding="utf-8"))

G = nx.Graph()
for n in data.get("nodes", []):
    lab = n.get("label","?")
    mas = int(n.get("maslov", 0) or 0)
    tam = int(n.get("tamagawa", 0) or 0)
    G.add_node(lab, maslov=mas, tam=tam)
for e in data.get("edges", []):
    s = e.get("from"); t = e.get("to"); w = int(e.get("int",1) or 1)
    if s is not None and t is not None: G.add_edge(s,t,weight=w)

if len(G)==0:
    print("empty graph; nothing to draw")
    sys.exit(0)

pos = nx.spring_layout(G, seed=1)
colors = ["green" if G.nodes[v]["maslov"]==1 else "red" for v in G]
labels = {v: f"{v}\n{G.nodes[v]['tam']}" for v in G}

plt.figure(figsize=(6,4), dpi=140)
nx.draw(G, pos, node_color=colors, with_labels=False)
nx.draw_networkx_labels(G, pos, labels=labels, font_size=7)
plt.title("Kervaire–Maslov plumbing graph")
out = os.path.splitext(os.path.basename(inp))[0] + ".png"
plt.savefig(out, bbox_inches="tight")
print(f"[ok] wrote {out}")
