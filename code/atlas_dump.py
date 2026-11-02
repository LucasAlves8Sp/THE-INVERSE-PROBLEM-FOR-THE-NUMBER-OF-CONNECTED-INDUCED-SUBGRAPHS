#!/usr/bin/env python3
"""Write the connected graphs with at most seven vertices of the Read-Wilson atlas (as
distributed with NetworkX) to atlas_connected_le7.txt, one graph per line:
    n m u1 v1 u2 v2 ... um vm
This is the input of f_edge_subsets.c, which recomputes c by vertex subsets and F by edge
subsets.  Usage (from the directory code):
    python3 atlas_dump.py
    gcc -O2 -o f_edge_subsets f_edge_subsets.c
    ./f_edge_subsets < atlas_connected_le7.txt
Requires networkx.
"""
import networkx as nx

with open('atlas_connected_le7.txt', 'w') as f:
    for G in nx.graph_atlas_g()[1:]:
        if not nx.is_connected(G):
            continue
        f.write(f"{G.number_of_nodes()} {G.number_of_edges()} "
                + " ".join(f"{u} {v}" for u, v in G.edges()) + "\n")
