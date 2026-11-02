#!/usr/bin/env python3
"""Values of F(G), the number of connected subgraphs (V', E') of a connected graph G,
up to a limit LIM (default 89).

F(G) = |V(G)| + c(L(G)), where L(G) is the line graph and c counts connected induced
subgraphs: a nonempty edge set E' spans a connected subgraph exactly when E' induces a
connected subgraph of L(G).

Completeness of the search.  F(G) >= c(G) >= n(n+1)/2, so F(G) <= 89 forces n <= 12.
F strictly increases when an edge is added (the new edge alone is a new connected
subgraph), and F(T) = c(T) for a tree T.  A connected G with F(G) <= LIM contains a
spanning tree T, and adding the edges of G - E(T) one at a time gives connected graphs
with F <= F(G) <= LIM.  So the search below, which starts from all trees with
c(T) <= LIM and adds one edge at a time while F <= LIM, finds every connected graph
with F <= LIM, up to isomorphism.

F is computed in two independent ways: (1) by enumerating the connected vertex sets of
L(G) (ESU scheme, Wernicke 2006), stopping once the count exceeds LIM; (2) for every
graph kept, by testing all nonempty edge subsets with union-find.

Requires networkx (tested with Python 3.13 and NetworkX 3.7).
Usage (from the directory code):  python3 f_values.py 89 > ../data/f_values_output.txt
Writes ../data/f_graphs_le_LIM.csv: every connected graph with F <= LIM up to isomorphism, with
F, the numbers of vertices and edges, c, and the edge list.
"""
import os
import sys
import networkx as nx

LIM = int(sys.argv[1]) if len(sys.argv) > 1 else 89
# Exceptions of Czabarka, Szekely and Wagner (2009): the positive integers that are not
# the number of subtrees of any tree.
CSW = [2, 4, 5, 7, 8, 9, 12, 13, 14, 16, 18, 19, 22, 23, 26, 27, 29, 31, 33, 35,
       38, 39, 42, 43, 46, 50, 52, 54, 60, 65, 68, 72, 77, 89]


def line_adj(G):
    E = list(G.edges())
    nb = [set() for _ in E]
    for i in range(len(E)):
        for j in range(i + 1, len(E)):
            if set(E[i]) & set(E[j]):
                nb[i].add(j)
                nb[j].add(i)
    return nb


def count_connected_sets(nb, cap):
    """Number of connected vertex sets of the graph with adjacency sets nb (ESU),
    or cap + 1 as soon as the count exceeds cap."""
    count = 0

    def extend(sub, ext, v, excl):
        nonlocal count
        count += 1
        if count > cap:
            return
        ext = set(ext)
        while ext:
            w = ext.pop()
            new = {u for u in nb[w] if u > v and u not in excl}
            extend(sub | {w}, ext | new, v, excl | new)
            if count > cap:
                return

    for v in range(len(nb)):
        nbr = {u for u in nb[v] if u > v}
        extend({v}, nbr, v, nbr | {v})
        if count > cap:
            return cap + 1
    return count


def F_esu(G, cap=LIM):
    n = G.number_of_nodes()
    if n > cap:
        return cap + 1
    return n + count_connected_sets(line_adj(G), cap - n)


def F_unionfind(G):
    n = G.number_of_nodes()
    E = list(G.edges())
    m = len(E)
    total = n
    for mask in range(1, 1 << m):
        par = {}

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for i in range(m):
            if mask >> i & 1:
                for x in E[i]:
                    par.setdefault(x, x)
                a, b = find(E[i][0]), find(E[i][1])
                if a != b:
                    par[a] = b
        total += len({find(x) for x in par}) == 1
    return total


def c_vertex(G):
    nodes = list(G.nodes())
    idx = {v: i for i, v in enumerate(nodes)}
    nb = [set() for _ in nodes]
    for u, v in G.edges():
        nb[idx[u]].add(idx[v])
        nb[idx[v]].add(idx[u])
    return count_connected_sets(nb, 10 ** 9)


seen = {}


def is_new(G):
    h = nx.weisfeiler_lehman_graph_hash(G, iterations=4)
    for H in seen.get(h, []):
        if nx.is_isomorphic(G, H):
            return False
    seen.setdefault(h, []).append(G)
    return True


def main():
    found = []
    level = []
    n = 1
    trees_kept = {}
    while n * (n + 1) // 2 <= LIM:
        trees = [nx.empty_graph(1)] if n == 1 else \
            [nx.convert_node_labels_to_integers(t) for t in nx.nonisomorphic_trees(n)]
        for t in trees:
            f = F_esu(t)
            assert f > LIM or f == c_vertex(t)          # F(T) = c(T) for trees
            if f <= LIM and is_new(t):
                level.append((t, f))
                trees_kept[n] = trees_kept.get(n, 0) + 1
        n += 1
    found += level
    print(f"trees with F = c <= {LIM}, by order: {dict(sorted(trees_kept.items()))}"
          f" (total {len(level)})")
    rnd = 0
    while level:
        rnd += 1
        nxt = []
        for G, _ in level:
            nodes = sorted(G.nodes())
            for i, u in enumerate(nodes):
                for v in nodes[i + 1:]:
                    if not G.has_edge(u, v):
                        H = G.copy()
                        H.add_edge(u, v)
                        f = F_esu(H)
                        if f <= LIM and is_new(H):
                            nxt.append((H, f))
        found += nxt
        level = nxt
        print(f"round {rnd} (one more edge): {len(nxt)} new graphs with F <= {LIM}")
    bad = sum(F_unionfind(G) != f for G, f in found)
    # machine-readable list of every connected graph with F <= LIM, up to isomorphism
    data = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data")
    with open(os.path.join(data, f"f_graphs_le_{LIM}.csv"), "w") as out:
        out.write("F,n,m,c,edges\n")
        for G, f in sorted(found, key=lambda p: (p[1], p[0].number_of_nodes(),
                                                  p[0].number_of_edges(), sorted(p[0].edges()))):
            out.write(f"{f},{G.number_of_nodes()},{G.number_of_edges()},{c_vertex(G)},"
                      + " ".join(f"{u}-{v}" for u, v in sorted(G.edges())) + "\n")
    values = sorted({f for _, f in found})
    missing = sorted(set(range(1, LIM + 1)) - set(values))
    print(f"connected graphs with F <= {LIM}, up to isomorphism: {len(found)}")
    print(f"disagreements between the two methods: {bad}")
    print(f"values of F in [1,{LIM}] not attained: {missing}")
    print("subtree exceptions of CSW that are values of F:",
          [k for k in CSW if k in values])
    print("witnesses (n, edges) of least order, then least size:")
    for k in CSW:
        if k in values:
            G = min((G for G, f in found if f == k),
                    key=lambda G: (G.number_of_nodes(), G.number_of_edges(), sorted(G.edges())))
            print(f"  F = {k}: n = {G.number_of_nodes()}, edges {sorted(G.edges())}")


if __name__ == "__main__":
    main()
