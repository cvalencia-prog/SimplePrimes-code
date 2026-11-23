# -*- coding: utf-8 -*-
# cubiertas.py -- biblioteca y autotest del banco de cómputo de SimplePrimes (T1, 2026-11-19).
# Calcula las ∞-cubiertas maximales de una anticadena G ⊂ N^n (= componentes de la descomposición irreducible irredundante de
# I_G), decide si I_G es simple (no hay dos cubiertas maximales con el mismo soporte), lista los generadores dominados y los
# pares de cubiertas maximales con el mismo soporte, y coteja con irreducibleDecomposition de Macaulay2.
# Definiciones (las del encargo de la sesión orquestadora, 2026-11-19):
#   ∞-cubierta: c ∈ (N_{>0} ∪ {∞})^n tal que todo g ∈ G tiene un j con c_j finito y c_j ≤ g_j; orden entrada a entrada, ∞ arriba.
#   simple: no hay dos cubiertas maximales con el mismo soporte (conjunto de entradas finitas).
#   dominado: g está dominado si para cada u ∈ supp(g) hay f ∈ G con f_u > g_u.  Con supp(g) = {p,q} es la definición de
#     SimplePrimes (f_p > g_p, h_q > g_q), extendida a aristas múltiples (f, h pueden estar sobre el mismo par).  Para un lazo
#     g = x_p^a la misma definición pide f con f_p > a, y entonces x_p^a divide a x^f: en una anticadena un lazo nunca está dominado.
# Dos algoritmos independientes para las cubiertas maximales (se cotejan en el autotest):
#   (A) incremental: cubiertas({g}) = ↓{a e_j + ∞ en lo demás : j ∈ supp g}; cubiertas(G ∪ H) = ↓{c ∧ d}; se quitan las no maximales.
#   (B) fuerza bruta: toda cubierta maximal tiene c_j ∈ {g_j > 0 : g ∈ G} ∪ {∞} (si c_j no es un exponente, c + e_j sigue siendo
#       cubierta); se recorre ese producto y se comprueba la maximalidad por definición (c + e_u no es cubierta para u ∈ supp c).
# Uso: /opt/homebrew/bin/python3 -B cubiertas.py --autotest     (termina en «EXITO»; control negativo incluido)
import itertools, os, random, re, shutil, subprocess, sys, tempfile

INF = 10 ** 6
M2 = shutil.which('M2') or '/opt/homebrew/bin/M2'          # Macaulay2 en el PATH


# ---------------------------------------------------------------------------------------------------------------- utilidades
def parse_monomios(texto, n=None):
    """'x_1^2*x_3, x2x4^3' -> lista de vectores; n = número de variables (por defecto, el índice mayor)."""
    mons = []
    for m in re.split(r'[,;]', texto):
        m = m.strip()
        if not m:
            continue
        v = {}
        for i, e in re.findall(r'x_?(\d+)(?:\^(\d+))?', m):
            v[int(i)] = v.get(int(i), 0) + int(e or 1)
        mons.append(v)
    n = n or max(max(v) for v in mons)
    return [tuple(v.get(i + 1, 0) for i in range(n)) for v in mons], n


def minimalizar(G):
    """Los generadores minimales (la anticadena) de la familia G."""
    G = sorted(set(G))
    return [g for g in G if not any(h != g and all(a <= b for a, b in zip(h, g)) for h in G)]


def es_anticadena(G):
    return len(set(G)) == len(G) and minimalizar(G) == sorted(set(G))


def soporte(v):
    return frozenset(i for i, a in enumerate(v) if 0 < a < INF)


def monomio(g):
    s = []
    for i, a in enumerate(g):
        if a:
            s.append('x%d' % (i + 1) + ('^%d' % a if a > 1 else ''))
    return ''.join(s) or '1'


def componente(c):
    """∞-cubierta -> ideal irreducible m^c en texto."""
    return '<' + ','.join('x%d' % (i + 1) + ('^%d' % a if a > 1 else '') for i, a in enumerate(c) if a < INF) + '>'


def vec(c):
    return '(' + ','.join('∞' if a >= INF else str(a) for a in c) + ')'


# ---------------------------------------------------------------------------------------------------------------- cubiertas
def es_cubierta(c, G):
    return all(any(c[j] < INF and 0 < g[j] and c[j] <= g[j] for j in range(len(c))) for g in G)


def maximales(S):
    S = list(set(S))
    return sorted(c for c in S if not any(d != c and all(a <= b for a, b in zip(c, d)) for d in S))


def cubiertas_maximales(G, n):
    """Algoritmo (A), incremental."""
    actuales = [tuple([INF] * n)]
    for g in G:
        simples = [tuple(g[j] if k == j else INF for k in range(n)) for j in range(n) if g[j] > 0]
        actuales = maximales({tuple(min(a, b) for a, b in zip(c, s)) for c in actuales for s in simples})
    return actuales


def cubiertas_maximales_fb(G, n):
    """Algoritmo (B), fuerza bruta sobre los candidatos, maximalidad por definición."""
    cand = [sorted({g[j] for g in G if g[j] > 0}) + [INF] for j in range(n)]
    res = []
    for c in itertools.product(*cand):
        if not es_cubierta(c, G):
            continue
        if all(not es_cubierta(c[:u] + (c[u] + 1,) + c[u + 1:], G) for u in range(n) if c[u] < INF):
            res.append(c)
    return sorted(res)


def critica(c, G):
    """Lema `key` de SimplePrimes: para cada u ∈ supp(c) hay g con g_u = c_u y g_v < c_v para v ∈ supp(c) \\ u."""
    s = soporte(c)
    return all(any(g[u] == c[u] and all(g[v] < c[v] for v in s if v != u) for g in G) for u in s)


# ---------------------------------------------------------------------------------------------------------------- análisis
def dominados(G):
    """Generadores dominados, con un testigo (f_u) para cada u de su soporte."""
    res = []
    for g in G:
        s = soporte(g)
        if all(any(f[u] > g[u] for f in G) for u in s):
            res.append(g)
    return res


def pares_mismo_soporte(C):
    """Pares de cubiertas maximales con el mismo soporte, con el conjunto de coordenadas en que difieren."""
    por = {}
    for c in C:
        por.setdefault(soporte(c), []).append(c)
    pares = []
    for s, L in por.items():
        for c, d in itertools.combinations(L, 2):
            pares.append((c, d, frozenset(i for i in s if c[i] != d[i])))
    return pares


def criticos(c, G):
    """Para cada u ∈ supp(c), los generadores críticos de c en u."""
    s = soporte(c)
    return {u: [g for g in G if g[u] == c[u] and all(g[v] < c[v] for v in s if v != u)] for u in s}


def analizar(G, n):
    G = minimalizar(G)
    C = cubiertas_maximales(G, n)
    pares = pares_mismo_soporte(C)
    dom = dominados(G)
    # generadores dominados «efectivos»: los que son críticos de c en u ∈ U = {c < d} para un par (c, d) con el mismo soporte
    efectivos = set()
    for c, d, D in pares:
        for x, y in ((c, d), (d, c)):
            cr = criticos(x, G)
            for u in D:
                if x[u] < y[u]:
                    efectivos.update(cr[u])
    return {
        'G': G, 'n': n, 'cubiertas': C, 'simple': not pares, 'pares': pares, 'dominados': dom,
        'efectivos': sorted(efectivos),
        'soporte_grafica': all(len(soporte(g)) <= 2 for g in G),
        'H1': (not pares) or any(len(D) == 2 for _, _, D in pares),
    }


# ---------------------------------------------------------------------------------------------------------------- Macaulay2
def m2_descomposiciones(ideales, tmpdir=None):
    """ideales: lista de (G, n). Devuelve, para cada uno, la lista ordenada de ∞-vectores de irreducibleDecomposition."""
    lineas = []
    for k, (G, n) in enumerate(ideales):
        gens = ', '.join('*'.join('x_%d^%d' % (i + 1, a) for i, a in enumerate(g) if a) for g in G)
        lineas.append('R = QQ[x_1..x_%d]; I = monomialIdeal(%s); '
                      'print("R%d " | toString apply(irreducibleDecomposition I, J -> apply(flatten entries gens J, '
                      'm -> flatten exponents m)));' % (n, gens, k))
    d = tempfile.mkdtemp(dir=tmpdir)
    f = os.path.join(d, 'cotejo.m2')
    open(f, 'w').write('\n'.join(lineas) + '\nprint "FIN";\n')
    r = subprocess.run([M2, '--script', f], capture_output=True, text=True)
    if r.returncode != 0 or 'FIN' not in r.stdout:
        raise RuntimeError('M2 falló (código %d): %s' % (r.returncode, r.stderr[-500:]))
    res = {}
    for linea in r.stdout.splitlines():
        m = re.match(r'R(\d+) (.*)$', linea)
        if not m:
            continue
        k = int(m.group(1))
        n = ideales[k][1]
        comps = []
        for comp in re.findall(r'\{((?:\{[^{}]*\},?\s*)*)\}', m.group(2)[1:-1]):
            c = [INF] * n
            for e in re.findall(r'\{([^{}]*)\}', comp):
                v = [int(x) for x in e.split(',')]
                nz = [i for i, a in enumerate(v) if a]
                if len(nz) != 1:
                    raise RuntimeError('componente no irreducible en M2: %s' % e)
                c[nz[0]] = v[nz[0]]
            comps.append(tuple(c))
        res[k] = sorted(comps)
    return [res[k] for k in range(len(ideales))]


# ---------------------------------------------------------------------------------------------------------------- autotest
def autotest():
    rnd = random.Random(20261119)
    # 1. los dos algoritmos coinciden, y el lema de criticidad caracteriza las maximales entre las cubiertas
    for _ in range(400):
        n = rnd.randint(2, 4)
        G = minimalizar([tuple(rnd.randint(0, 3) for _ in range(n)) for _ in range(rnd.randint(1, 5))])
        G = [g for g in G if any(g)]
        if not G:
            continue
        A, B = cubiertas_maximales(G, n), cubiertas_maximales_fb(G, n)
        assert A == B, ('los algoritmos difieren', G, A, B)
        cand = [sorted({g[j] for g in G if g[j] > 0}) + [INF] for j in range(n)]
        for c in itertools.product(*cand):
            if es_cubierta(c, G):
                assert critica(c, G) == (c in A), ('lema key', G, c)
    # 2. ejemplos conocidos
    G, n = parse_monomios('x1^2, x1x2, x2^2')
    a = analizar(G, n)
    assert a['cubiertas'] == [(1, 2), (2, 1)] and not a['simple'], a
    G, n = parse_monomios('x1x2, x1x3, x2^2x3, x1^2x4')        # contraejemplo al primer `main` (sesión orquestadora)
    a = analizar(G, n)
    assert a['simple'] and (1, 1, 0, 0) in a['dominados'], a
    # 3. control negativo: un cálculo de cubiertas equivocado (sin quitar las no maximales) debe detectarse
    G, n = parse_monomios('x1x2, x2x3')
    malo = sorted({tuple(min(a, b) for a, b in zip(c, s))
                   for c in [(1, INF, INF), (INF, 1, INF)] for s in [(INF, 1, INF), (INF, INF, 1)]})
    assert malo != cubiertas_maximales(G, n), 'el control negativo no distingue un cálculo sin maximalizar'
    assert cubiertas_maximales(G, n) == [(1, INF, 1), (INF, 1, INF)]
    assert not critica((1, 1, INF), G), 'el lema de criticidad aceptó una cubierta no maximal'
    # 4. M2 sobre unos ejemplos (incluye un control: una lista alterada no debe coincidir)
    muestra = [parse_monomios(t) for t in ('x1^2, x1x2, x2^2', 'x1x2, x1x3, x2^2x3, x1^2x4', 'x1x2^2, x2x3^5, x3x4^7')]
    m2 = m2_descomposiciones(muestra, os.environ.get('TMPDIR'))
    for (G, n), comps in zip(muestra, m2):
        assert comps == cubiertas_maximales(minimalizar(G), n), ('M2 difiere', G, comps)
    assert m2[0] != m2[1], 'control negativo de M2'
    print('Autotest: (A) = (B) en 400 anticadenas al azar; lema de criticidad comprobado en todas sus cubiertas; '
          'ejemplos conocidos; control negativo; 3 ideales cotejados con Macaulay2.')
    print('EXITO')


if __name__ == '__main__':
    if '--autotest' in sys.argv:
        autotest()
    else:
        print(__doc__ or 'uso: cubiertas.py --autotest')
