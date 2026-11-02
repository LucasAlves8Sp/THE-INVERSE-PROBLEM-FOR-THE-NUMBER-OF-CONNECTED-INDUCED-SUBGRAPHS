#!/usr/bin/env python3
"""Check the witness table of Appendix A of the paper directly from the LaTeX source.

For every row (k, n, graph6) of the table, decode the graph6 string with the decoder below
(no external library), and check that the graph has n vertices, is connected, and has exactly
k connected sets, counted by testing all 2^n - 1 nonempty vertex sets.

graph6 (for n <= 62): the first character is chr(n + 63); then the entries x(i,j), i < j, of the
adjacency matrix are listed column by column, (0,1), (0,2), (1,2), (0,3), (1,3), (2,3), ...,
padded with zeros to a multiple of six bits, and each group of six bits b is written as chr(b + 63).

Usage (from the directory code):  python3 check_witnesses.py > ../data/check_witnesses_output.txt
(optional argument: the path of the .tex file; default ../paper/connected-induced-subgraphs-inverse-problem.tex)
"""
import re
import sys

import os

TEX = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "..", "paper",
    "connected-induced-subgraphs-inverse-problem.tex")


def decode_graph6(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits.extend((v >> (5 - i)) & 1 for i in range(6))
    edges, p = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                edges.append((i, j))
            p += 1
    return n, edges


def count_connected_sets(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    count = 0
    for S in range(1, 1 << n):
        seen = S & -S
        frontier = seen
        while frontier:
            i = (frontier & -frontier).bit_length() - 1
            frontier &= frontier - 1
            new = adj[i] & S & ~seen
            seen |= new
            frontier |= new
        count += seen == S
    return count


def main():
    tex = open(TEX, encoding="utf-8").read()
    table = tex[tex.index(r"\begin{longtable}"):tex.index(r"\end{longtable}")]
    rows = re.findall(r"(\d+) & (\d+) & \\verb!([^!]+)!", table)
    bad = 0
    for k, n, g6 in rows:
        k, n = int(k), int(n)
        m, edges = decode_graph6(g6)
        c = count_connected_sets(m, edges)
        connected = _is_connected(m, edges)
        if m != n or c != k or not connected:
            bad += 1
            print("MISMATCH", k, n, g6, m, c, connected)
    ks = sorted(int(k) for k, _, _ in rows)
    print(f"rows checked: {len(rows)}; values: {ks[0]}..{ks[-1]}; complete range: "
          f"{ks == list(range(17, 128))}; mismatches: {bad}")


def _is_connected(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    seen, stack = {0}, [0]
    while stack:
        x = stack.pop()
        for y in adj[x] - seen:
            seen.add(y)
            stack.append(y)
    return len(seen) == n


if __name__ == "__main__":
    main()
