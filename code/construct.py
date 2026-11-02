"""
construct.py -- the computer-free construction of Section 5 of the note,
implemented literally, so that it can be tested.
(In "The inverse problem for the number of connected induced subgraphs" this construction is
Section 4 -- Lemmas 4.2-4.4, Remark 4.5, Theorem 4.6 -- and Remark 5.1.  Copied unchanged otherwise
from the companion repository.  Usage (from the repository root): python3 code/construct.py
writes data/base_certificate.txt and prints the gaps of Remark 4.5, as in data/construct_output.txt.)

Notation.  For a finite simple graph K (connected or not), c(K) is the number
of nonempty vertex sets inducing a connected subgraph.
  Lambda_m = { c(K) : K a graph on exactly m vertices }
  V_m      = { c(G) : G a connected graph on exactly m vertices }

Rules (each is a lemma of the note, proved by direct counting):
  (U) disjoint union   c(K + K') = c(K) + c(K')
  (C) cone             c(K * w)  = 2^|K| + c(K)                       (connected)
  (N) near-cone        for d >= 1 and any graph R on r >= 0 vertices, the graph
                       N(d, R) on m = d + r + 2 vertices -- a star with centre u
                       and leaves l_1..l_d, plus R, plus a vertex w adjacent to
                       every vertex except u -- is connected and
                       c(N(d,R)) = 2^(m-1) - 2^r + 2^d + d + c(R).
Sporadic graphs (S1)-(S7) are listed below with their counts.

Base (m <= 7): the closure of {single vertex} under (U), (C), (N) and the
sporadic graphs; every value receives a derivation (a backpointer), which is
written to ../data/base_certificate.txt.

Induction (m >= 8): for v in [m, 2^m - 1] a graph on exactly m vertices with
c = v, connected when v >= 2^(m-1):
  * v <  2^(m-1):                 (graph for v-1 on m-1 vertices) + isolated vertex
  * v >= 2^(m-1) + m - 1:         cone over (graph for v - 2^(m-1) on m-1 vertices)
  * v = 2^(m-1) + j, 0<=j<=m-2:   N(d, R) with (d, r) chosen as in the note:
        m = 8 : (2,4) for j <= 5, (3,3) for j = 6
        m = 9 : (2,5) for j <= 5, (3,4) for j = 6,7
        m = 10: (3,5) for j != 4, (2,6) for j = 4
        m = 11: (3,6)
        m >= 12: d = least d >= 1 with 2^d + d >= m-1, r = m-2-d
      and R a graph on r vertices with c(R) = 2^r - 2^d - d + j.
For k >= 17: k in V_m with m = bit length of k, except k in [17,31] (base),
and k = 25 (sporadic spider on 6 vertices).
"""

import functools
import os
import sys

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data")

# ------------------------------------------------------------ graph helpers
# A graph is (n, edges) with vertices 0..n-1 and edges a tuple of pairs.

def disjoint_union(G, H):
    n, e = G
    m, f = H
    return (n + m, tuple(e) + tuple((a + n, b + n) for a, b in f))


def add_isolated(G):
    return (G[0] + 1, G[1])


def cone(K):
    n, e = K
    return (n + 1, tuple(e) + tuple((v, n) for v in range(n)))


def near_cone(d, R):
    """N(d,R): R on 0..r-1, u = r, leaves r+1..r+d, w = r+d+1."""
    r, e = R
    u = r
    leaves = list(range(r + 1, r + 1 + d))
    w = r + d + 1
    edges = list(e)
    edges += [(u, l) for l in leaves]
    edges += [(l, w) for l in leaves]
    edges += [(v, w) for v in range(r)]
    return (r + d + 2, tuple(edges))


def near_cone_value(d, r, cR):
    m = d + r + 2
    return 2 ** (m - 1) - 2 ** r + 2 ** d + d + cR


# ----------------------------------------------------------- sporadic graphs

SPORADIC = {
    # value: (order, edges, description, hand count)
    19: (5, ((0, 1), (0, 2), (1, 2), (0, 3), (1, 4)),
         "triangle xyz with one pendant vertex at x and one at y",
         "(1+2)(1+2)(1+1) - 1 + 2 = 19"),
    25: (6, ((0, 1), (0, 2), (2, 3), (0, 4), (4, 5)),
         "spider with legs of lengths 1, 2, 2",
         "2*3*3 + T(1) + T(2) + T(2) = 18 + 1 + 3 + 3 = 25"),
    32: (6, ((0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (1, 5)),
         "triangle xyz with two pendant vertices at x and one at y",
         "(1+4)(1+2)(1+1) - 1 + 3 = 32"),
    35: (6, ((0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 4), (2, 5)),
         "K4 minus an edge ab, with a pendant vertex at a and one at a vertex c of degree 3",
         "sum over the 14 connected subsets Q of K4-ab of 2^{|Q cap {a,c}|} = 33, plus 2 = 35"),
    57: (6, tuple((a, b) for a in range(6) for b in range(a + 1, 6)
                  if (a, b) not in ((0, 1), (0, 2), (3, 4), (3, 5))),
         "K6 minus two vertex-disjoint paths of length 2",
         "63 - 2*(2^2 - 1) = 57"),
    67: (7, ((0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (4, 5), (4, 6)),
         "K_{2,3} with two pendant vertices at a vertex x of the 3-side",
         "c_x(K23)*4 + c(C4) + 2 = 13*4 + 13 + 2 = 67"),
    90: (7, tuple([(a, b) for a in range(6) for b in range(a + 1, 6)
                   if (a, b) not in ((0, 1), (0, 2))] + [(0, 6)]),
         "K6 minus two edges va, vb, with a pendant vertex at v",
         "c(K6 - va - vb) + 1 + c_v = (63-3) + 1 + (32-3) = 90"),
}


# ------------------------------------------------------------- base closure

@functools.lru_cache(maxsize=None)
def base_tables():
    """Closure for m <= 7.  Returns (Vder, Lder): dicts m -> {value: derivation}.

    Derivations:
      ('single',)                    the one-vertex graph
      ('sporadic', value)
      ('cone', x)                    x in Lambda_{m-1}
      ('near', d, r, x)              x in Lambda_r
      ('conn',)                      value already in V_m
      ('union', a, x, y)             x in V_a, y in Lambda_{m-a}
    """
    Vder = {1: {1: ("single",)}}
    Lder = {0: {0: ("empty",)}, 1: {1: ("conn",)}}
    for m in range(2, 8):
        v = {}
        for x in sorted(Lder[m - 1]):
            v.setdefault(2 ** (m - 1) + x, ("cone", x))
        for d in range(1, m - 1):
            r = m - 2 - d
            for x in sorted(Lder[r]):
                v.setdefault(near_cone_value(d, r, x), ("near", d, r, x))
        for val, (order, *_rest) in SPORADIC.items():
            if order == m:
                v.setdefault(val, ("sporadic", val))
        Vder[m] = v
        lam = {val: ("conn",) for val in v}
        for a in range(1, m):
            for x in sorted(Vder[a]):
                for y in sorted(Lder[m - a]):
                    lam.setdefault(x + y, ("union", a, x, y))
        Lder[m] = lam
    return Vder, Lder


def rule_gaps(m):
    """Values in [2^(m-1), 2^m - 1] (m >= 5; for m = 5 the interval [17, 31])
    that rules (C) and (N) do not produce on m vertices from the sets
    Lambda_r (r < m) of the base closure, i.e. with every sporadic graph of
    order < m available but none of order m."""
    Vder, Lder = base_tables()
    v = set()
    for x in Lder[m - 1]:
        v.add(2 ** (m - 1) + x)
    for d in range(1, m - 1):
        r = m - 2 - d
        for x in Lder[r]:
            v.add(near_cone_value(d, r, x))
    lo = 17 if m == 5 else 2 ** (m - 1)
    return sorted(set(range(lo, 2 ** m)) - v)


def build_base(m, val, connected):
    Vder, Lder = base_tables()
    if connected:
        der = Vder[m][val]
    else:
        der = Lder[m][val]
        if der[0] == "conn":
            return build_base(m, val, True)
    kind = der[0]
    if kind == "single":
        return (1, ())
    if kind == "empty":
        return (0, ())
    if kind == "sporadic":
        n, edges, _, _ = SPORADIC[val]
        return (n, edges)
    if kind == "cone":
        return cone(build_base(m - 1, der[1], False))
    if kind == "near":
        _, d, r, x = der
        return near_cone(d, build_base(r, x, False))
    if kind == "union":
        _, a, x, y = der
        return disjoint_union(build_base(a, x, True), build_base(m - a, y, False))
    raise ValueError(der)


# ---------------------------------------------------------------- induction

def near_params(m, j):
    if m == 8:
        return (2, 4) if j <= 5 else (3, 3)
    if m == 9:
        return (2, 5) if j <= 5 else (3, 4)
    if m == 10:
        return (2, 6) if j == 4 else (3, 5)
    if m == 11:
        return (3, 6)
    d = 1
    while 2 ** d + d < m - 1:
        d += 1
    return (d, m - 2 - d)


def graph_lambda(m, v):
    """A graph on exactly m vertices with c = v (m >= 1, v in Lambda_m)."""
    if m <= 7:
        return build_base(m, v, False)
    if not (m <= v <= 2 ** m - 1):
        raise ValueError((m, v))
    if v < 2 ** (m - 1):
        return add_isolated(graph_lambda(m - 1, v - 1))
    return graph_V(m, v)


def graph_V(m, v):
    """A connected graph on exactly m vertices with c = v, for 2^(m-1) <= v <= 2^m - 1 (m >= 6)."""
    if m <= 7:
        return build_base(m, v, True)
    if v >= 2 ** (m - 1) + m - 1:
        return cone(graph_lambda(m - 1, v - 2 ** (m - 1)))
    j = v - 2 ** (m - 1)
    assert 0 <= j <= m - 2
    d, r = near_params(m, j)
    cR = 2 ** r - 2 ** d - d + j
    assert near_cone_value(d, r, cR) == v
    return near_cone(d, graph_lambda(r, cR))


def realize(k):
    """A connected graph G with c(G) = k, for every k >= 17 (and the values
    1,3,6,7,10..15 via the base)."""
    if k < 17:
        for m in range(1, 5):
            Vder, _ = base_tables()
            if k in Vder[m]:
                return build_base(m, k, True)
        raise ValueError(f"{k} is not a value of c")
    if k == 25:
        n, e, _, _ = SPORADIC[25]
        return (n, e)
    m = k.bit_length()
    if m == 5:
        return build_base(5, k, True)
    return graph_V(m, k)


def certificate():
    Vder, Lder = base_tables()
    lines = ["# Base certificate: derivations of the values of V_m and Lambda_m for m <= 7",
             "# from the single vertex by the rules (U) union, (C) cone, (N) near-cone,",
             "# and the sporadic graphs (S).  Each line: m, set, value, derivation.",
             "#   C x        : value = 2^(m-1) + x, with x in Lambda_(m-1)",
             "#   N d r x    : value = 2^(m-1) - 2^r + 2^d + d + x, m = d+r+2, x in Lambda_r",
             "#   S          : sporadic graph (see the note, Table of sporadic graphs)",
             "#   V          : value in V_m (a connected graph)",
             "#   U a x y    : value = x + y with x in V_a and y in Lambda_(m-a)",
             ""]
    for m in range(1, 8):
        for val in sorted(Vder[m]):
            der = Vder[m][val]
            if der[0] == "single":
                tag = "single vertex"
            elif der[0] == "sporadic":
                tag = "S"
            elif der[0] == "cone":
                tag = f"C {der[1]}"
            else:
                tag = f"N {der[1]} {der[2]} {der[3]}"
            lines.append(f"m={m} V {val}: {tag}")
        for val in sorted(Lder[m]):
            der = Lder[m][val]
            tag = "V" if der[0] == "conn" else f"U {der[1]} {der[2]} {der[3]}"
            lines.append(f"m={m} L {val}: {tag}")
        lines.append("")
    return "\n".join(lines)


if __name__ == "__main__":
    os.makedirs(DATA, exist_ok=True)
    with open(os.path.join(DATA, "base_certificate.txt"), "w") as f:
        f.write(certificate())
    Vder, Lder = base_tables()
    for m in range(1, 8):
        print(m, "V misses in [2^(m-1),2^m-1]:", [x for x in range(2 ** (m - 1), 2 ** m) if x not in Vder[m]],
              "| Lambda misses in [m,2^m-1]:", [x for x in range(m, 2 ** m) if x not in Lder[m]])
    for m in (5, 6, 7):
        print(f"m={m}: values left by (C) and (N) without the sporadic graphs of order {m}:", rule_gaps(m))
