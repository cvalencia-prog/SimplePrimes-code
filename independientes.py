# -*- coding: utf-8 -*-
# independientes.py -- comprueba el Lema 3.27.  Para una gráfica simple H con vértices 1..n y al menos una arista, y todo
# L ⊆ V(H), las cubiertas maximales de G_{H,L} (aristas x_v x_w de H y lazos x_v^2, v ∈ L) con soporte completo son
# exactamente los vectores c^W (2 en W, 1 fuera), con W un conjunto independiente maximal de H contenido en L.  Además: si
# L = V, toda cubierta maximal tiene soporte completo y mu(m) es el número de conjuntos independientes maximales.
# Instancias: n = 2..5, todas las gráficas etiquetadas con al menos una arista y todo L; n = 6, una gráfica por clase de
# isomorfismo y todo L (la afirmación no cambia al renombrar los vértices de H y de L a la vez).
# Método, independiente de cubiertas.py y del Lema 2.4: las cubiertas se calculan por la definición en la rejilla
# {1..b_j} ∪ {∞} (b_j, el mayor exponente en j); una cubierta de la rejilla es maximal si y solo si ninguna c' que sube una sola
# entrada al siguiente valor de la rejilla es cubierta.  Para n <= 4 se compara además con la maximalidad por pares.
# Controles negativos (deben fallar en alguna instancia): (N1) predecir con todos los independientes maximales de H, sin pedir
# W ⊆ L; (N2) predecir con todos los independientes W ⊆ L, maximales o no.
# Uso: python3 independientes.py   (termina en EXITO o FALLA).
import itertools

INF = 10**9

def antichain(n, edges, L):
    G = []
    for (v, w) in edges:
        g = [0]*n; g[v] = 1; g[w] = 1; G.append(tuple(g))
    for v in L:
        g = [0]*n; g[v] = 2; G.append(tuple(g))
    return G

def grid(n, G):
    b = [max(g[j] for g in G) for j in range(n)]
    vals = [list(range(1, b[j]+1)) + [INF] for j in range(n)]
    return b, vals

def covers(c, G):
    for g in G:
        if not any(c[j] != INF and c[j] <= g[j] for j in range(len(c))):
            return False
    return True

def maximal_covers(n, G, pairwise=False):
    b, vals = grid(n, G)
    C = [c for c in itertools.product(*vals) if covers(c, G)]
    Cset = set(C)
    if pairwise:
        res = []
        for c in C:
            if not any(d != c and all(d[j] >= c[j] for j in range(n)) for d in C):
                res.append(c)
        return set(res)
    res = []
    for c in C:
        ok = True
        for u in range(n):
            if c[u] == INF:
                continue
            nxt = c[u]+1 if c[u] < b[u] else INF
            c2 = c[:u] + (nxt,) + c[u+1:]
            if c2 in Cset:
                ok = False; break
        if ok:
            res.append(c)
    return set(res)

def independent(W, adj):
    return all(w2 not in adj[w1] for w1 in W for w2 in W)

def maximal_independent_sets(n, adj):
    res = []
    for r in range(n+1):
        for W in itertools.combinations(range(n), r):
            W = set(W)
            if independent(W, adj) and all(v in W or any(w in W for w in adj[v]) for v in range(n)):
                res.append(frozenset(W))
    return res

def independent_sets(n, adj):
    return [frozenset(W) for r in range(n+1) for W in itertools.combinations(range(n), r) if independent(set(W), adj)]

def cW(n, W):
    return tuple(2 if v in W else 1 for v in range(n))

def graphs(n, iso):
    pairs = list(itertools.combinations(range(n), 2))
    idx = {e: i for i, e in enumerate(pairs)}
    perms = list(itertools.permutations(range(n))) if iso else []
    emaps = [[idx[tuple(sorted((p[v], p[w])))] for (v, w) in pairs] for p in perms]
    seen = set()
    for mask in range(1, 2**len(pairs)):
        if iso:
            if mask in seen:
                continue
            for em in emaps:
                m2 = 0
                for i in range(len(pairs)):
                    if mask >> i & 1:
                        m2 |= 1 << em[i]
                seen.add(m2)
        yield [pairs[i] for i in range(len(pairs)) if mask >> i & 1]

fallas = 0; inst = 0; n1 = 0; n2 = 0; inst_por_n = {}
for n in range(2, 7):
    iso = (n == 6)
    cnt = 0
    for edges in graphs(n, iso):
        adj = {v: set() for v in range(n)}
        for (v, w) in edges:
            adj[v].add(w); adj[w].add(v)
        mis = maximal_independent_sets(n, adj)
        ind = independent_sets(n, adj)
        for r in range(n+1):
            for L in itertools.combinations(range(n), r):
                L = set(L)
                G = antichain(n, edges, L)
                M = maximal_covers(n, G)
                if n <= 4:
                    if M != maximal_covers(n, G, pairwise=True):
                        print("FALLA maximalidad por pares", n, edges, L); fallas += 1
                full = {c for c in M if all(x != INF for x in c)}
                pred = {cW(n, W) for W in mis if W <= L}
                if full != pred:
                    print("FALLA: Lema 3.27", n, edges, sorted(L), full, pred); fallas += 1
                if r == n:
                    if full != M:
                        print("FALLA: con L = V hay una componente sin radical m", n, edges); fallas += 1
                    if len(full) != len(mis):
                        print("FALLA mu(m) != #MIS", n, edges); fallas += 1
                if {cW(n, W) for W in mis} != full:
                    n1 += 1
                if {cW(n, W) for W in ind if W <= L} != full:
                    n2 += 1
                inst += 1; cnt += 1
    inst_por_n[n] = cnt
print("instancias (H, L) por n:", inst_por_n, "total", inst)
print("control N1 (sin W ⊆ L) falla en", n1, "instancias; control N2 (sin maximalidad) falla en", n2)
if n1 == 0 or n2 == 0:
    print("FALLA: un control negativo no detectó nada"); fallas += 1
print("EXITO" if fallas == 0 else "FALLA (%d)" % fallas)
