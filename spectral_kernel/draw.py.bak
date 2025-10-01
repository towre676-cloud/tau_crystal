import sys, json
import networkx as nx
import matplotlib.pyplot as plt
path = sys.argv[1] if len(sys.argv) > 1 else "trace.json"
data = json.load(open(path, "r", encoding="utf-8"))
G = nx.Graph()
for n in data.get("nodes", []):
    G.add_node(n["label"], maslov=n.get("maslov",0), tam=n.get("tamagawa",0))
for e in data.get("edges", []):
    G.add_edge(e["from"], e["to"], weight=e.get("int",1))
pos = nx.spring_layout(G)
labels = {v: f"{v}\\n{G.nodes[v][\x27tam\x27]}" for v in G}
colors = ["green" if G.nodes[v]["maslov"] == 1 else "red" for v in G]
nx.draw(G, pos, node_color=colors, with_labels=False)
nx.draw_networkx_labels(G, pos, labels=labels, font_size=8)
plt.title("Kervaire–Maslov plumbing graph")
plt.show()
