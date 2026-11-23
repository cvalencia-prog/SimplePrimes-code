# -*- coding: utf-8 -*-
# t2_caracterizacion.py -- T2 (2026-11-19): comprueba contra la enumeración de soporte gráfica los enunciados de
# Contexto/Exploracion-T2-2026-11-19/Pruebas.tex y decide el segundo teorema `main` de SimplePrimes bajo sus lecturas.
# Usa cubiertas.py (cubiertas maximales) y las familias B(n,w), M(n,w) de enumeracion.py.
#
# CRITERIO DE PODA (R-20), fijado antes de lanzar: el de enumeracion.py (P1: gráficas conexas, una por clase de isomorfismo con
#   sus lazos; P2: exponentes apretados por vértice).  Vale aquí por la misma razón: todos los enunciados que se prueban solo
#   dependen de las comparaciones entre exponentes de una misma coordenada y se deciden por componentes conexas.
#   Los vectores M se recorren en  prod_j ({exponentes que aparecen en j} ∪ {∞}): sin pérdida, porque (TB) toma M = c ∨ d con
#   c, d maximales (entradas entre los exponentes) y la Definición `dominated` del manuscrito pide g_u = M_u en su inciso (iii).
#
# Qué comprueba en cada anticadena G (soporte gráfica, con aristas múltiples y lazos):
#  (TA) Anatomía de un par: para todo par c ≠ d de cubiertas maximales con el mismo soporte S, U = {c<d}, V = {d<c},
#       m = c∧d, M = c∨d (en S):  U, V ≠ ∅;  H = {g : g_j < M_j ∀ j ∈ S} es no vacío y todo g ∈ H es x_u^e x_v^f con u ∈ U,
#       v ∈ V, m_u ≤ e < M_u, m_v ≤ f < M_v;  cada u ∈ U (v ∈ V) es extremo de un g ∈ H con e = m_u (f = m_v);  los críticos de c
#       en u ∈ U y de d en v ∈ V están en H;  todo g ∈ H está dominado;  hay al menos max(|U|,|V|) dominados.
#       En particular: sin generador dominado ⇒ simple (Teorema A).
#  (TB) Caracterización: G no es simple  ⇔  hay M ∈ (N_{>0} ∪ ∞)^n tal que H(M) = {g no cubiertos por M} es no vacío, cada
#       h ∈ H(M) tiene soporte {u,v} ⊂ supp(M) con u ∈ U, v ∈ V para una bipartición (U,V) de la gráfica de soportes de H(M), y
#       M^U, M^V son cubiertas maximales (M^X = M con las coordenadas de X bajadas a min{h_x : h ∈ H(M)}).  Se comprueba además:
#       M^U y M^V siempre son cubiertas, M^U es crítica en U y M^V en V (lo «automático»), y que el conjunto de pares
#       {M^U, M^V} obtenidos es EXACTAMENTE el de pares de cubiertas maximales con el mismo soporte.
#  (MS) Segundo `main` de SimplePrimes (Respaldo-2026-11-19-antes-de-T0.tex, l.513-557): «G tiene cubiertas maximales con el
#       mismo soporte ⇔ G está dominada por algún M», bajo 8 lecturas de la Definición `dominated`:
#         eje A (inciso (i), «sin vértices aislados»):  A1 = todo vértice de supp(M) toca a H;  A0 = sin esa exigencia;
#         eje B (inciso (ii), G_U):  Bo = se quitan los g cubiertos por (m_U, M_{resto}) (l.537-546; es el «o» de l.518-522);
#                                    By = se quitan los g con (g_v ≥ M_v, algún v ∉ U) Y (g_u ≥ m_u, algún u ∈ U) (l.518-522 literal);
#         eje C (inciso (iii), el vector «c» sin definir):  Ca = c es la cubierta común a;  Cn = sin condición fuera de supp(M).
#       Para cada lectura se cuentan las anticadenas donde falla cada dirección, con las menores.
# Control negativo: (TB) sin exigir que M^U, M^V sean maximales («TB-débil») debe fallar en alguna anticadena simple; y la
#   anatomía (TA) con «H ⊂ aristas U–U» debe fallar.  Además, ejemplos conocidos (CE-1 simple, CE-2 no simple).
# Uso: /opt/homebrew/bin/python3 -B t2_caracterizacion.py FAMILIA N W [--max-aristas K] [--salida ARCHIVO]
#      /opt/homebrew/bin/python3 -B t2_caracterizacion.py --autotest
# Termina en «EXITO» o «FALLA».
import collections, itertools, multiprocessing, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cubiertas as cb
import enumeracion as en

INF = cb.INF


def sop(v):
    return frozenset(i for i, a in enumerate(v) if 0 < a < INF)


def candidatos_M(G, n):
    cols = [sorted({g[j] for g in G if g[j] > 0}) + [INF] for j in range(n)]
    for M in itertools.product(*cols):
        if any(a < INF for a in M):
            yield M


def biparticiones(H, S):
    """Biparticiones (U,V) de la gráfica de soportes de H (todos de tamaño 2, dentro de S); None si no es bipartita."""
    ady = collections.defaultdict(set)
    for h in H:
        s = sorted(sop(h))
        if len(s) != 2 or not set(s) <= S:
            return None
        ady[s[0]].add(s[1])
        ady[s[1]].add(s[0])
    comps, color = [], {}
    for v in sorted(ady):
        if v in color:
            continue
        color[v] = 0
        comp, pila = [v], [v]
        while pila:
            x = pila.pop()
            for y in ady[x]:
                if y not in color:
                    color[y] = 1 - color[x]
                    comp.append(y)
                    pila.append(y)
                elif color[y] == color[x]:
                    return None
        comps.append(comp)
    res = []
    for flips in itertools.product((0, 1), repeat=len(comps)):
        U = frozenset(v for comp, f in zip(comps, flips) for v in comp if color[v] ^ f == 0)
        V = frozenset(v for comp, f in zip(comps, flips) for v in comp if color[v] ^ f == 1)
        res.append((U, V))
    return res


def bajar(M, X, m):
    return tuple(m[j] if j in X else M[j] for j in range(len(M)))


def critica_en(c, G, u):
    s = sop(c)
    return any(g[u] == c[u] and all(g[v] < c[v] for v in s if v != u) for g in G)


# ------------------------------------------------------------------------------------------------------------------ (TA)
def anatomia(G, n, C, pares, dom):
    domset = set(dom)
    for c, d, D in pares:
        S = sop(c)
        U = frozenset(i for i in D if c[i] < d[i])
        V = frozenset(i for i in D if d[i] < c[i])
        if not U or not V:
            return 'U o V vacío'
        M = tuple(max(a, b) if a < INF else INF for a, b in zip(c, d))
        m = tuple(min(a, b) for a, b in zip(c, d))
        H = [g for g in G if all(g[j] < M[j] for j in S)]
        if not H:
            return 'H vacío'
        for g in H:
            s = sop(g)
            if len(s) != 2 or len(s & U) != 1 or len(s & V) != 1:
                return 'H no es U-V'
            if any(not (m[j] <= g[j] < M[j]) for j in s):
                return 'H fuera de la caja'
            if g not in domset:
                return 'g de H no dominado'
        for u in U:
            if not any(g[u] == m[u] for g in H):
                return 'u sin esquina'
            cr = [g for g in G if g[u] == c[u] and all(g[v] < c[v] for v in S if v != u)]
            if not cr or any(g not in H for g in cr):
                return 'crítico de c en U fuera de H'
        for v in V:
            if not any(g[v] == m[v] for g in H):
                return 'v sin esquina'
            cr = [g for g in G if g[v] == d[v] and all(g[w] < d[w] for w in S if w != v)]
            if not cr or any(g not in H for g in cr):
                return 'crítico de d en V fuera de H'
        if len(H) < max(len(U), len(V)):
            return 'menos de max(|U|,|V|) en H'
    if pares and not dom:
        return 'no simple sin dominado'
    return None


def anatomia_mala(G, n, pares):
    """Control negativo: «todo g ∈ H tiene sus dos extremos en U» (falso)."""
    for c, d, D in pares:
        S = sop(c)
        U = frozenset(i for i in D if c[i] < d[i])
        M = tuple(max(a, b) if a < INF else INF for a, b in zip(c, d))
        for g in G:
            if all(g[j] < M[j] for j in S) and not sop(g) <= U:
                return True
    return False


# ------------------------------------------------------------------------------------------------------------------ (TB)
def teorema_B(G, n, Cset):
    """Devuelve (pares obtenidos, error de lo «automático» o None, pares de la versión débil)."""
    obtenidos, debiles = set(), set()
    for M in candidatos_M(G, n):
        S = sop(M)
        H = [g for g in G if all(g[j] < M[j] for j in S)]
        if not H:
            continue
        bip = biparticiones(H, S)
        if bip is None:
            continue
        W = set().union(*[sop(h) for h in H])
        m = {w: min(h[w] for h in H if h[w] > 0) for w in W}
        for U, V in bip:
            MU, MV = bajar(M, U, m), bajar(M, V, m)
            if not (cb.es_cubierta(MU, G) and cb.es_cubierta(MV, G)):
                return obtenidos, 'M^U o M^V no es cubierta', debiles
            if not all(critica_en(MU, G, u) for u in U) or not all(critica_en(MV, G, v) for v in V):
                return obtenidos, 'M^U no es crítica en U', debiles
            debiles.add(frozenset((MU, MV)))
            if MU in Cset and MV in Cset:
                if cb.critica(MU, G) is False or cb.critica(MV, G) is False:
                    return obtenidos, 'maximal sin ser crítica', debiles
                obtenidos.add(frozenset((MU, MV)))
            # la maximalidad equivale a la criticidad en los vértices NO bajados
            maxU = all(critica_en(MU, G, j) for j in S - U)
            maxV = all(critica_en(MV, G, j) for j in S - V)
            if maxU != (MU in Cset) or maxV != (MV in Cset):
                return obtenidos, 'criticidad en S-U no equivale a maximal', debiles
    return obtenidos, None, debiles


# ------------------------------------------------------------------------------------------------------------------ (MS)
def proyectar(Gs, T, n):
    """Pone x_u = 1 para u ∈ T; devuelve None si aparece el generador 1, y si no la anticadena minimal."""
    out = []
    for g in Gs:
        h = tuple(0 if j in T else g[j] for j in range(n))
        if not any(h):
            return None
        out.append(h)
    return cb.minimalizar(out)


def cubiertas_de(Gs, n, cache):
    if Gs is None:
        return frozenset()
    k = tuple(Gs)
    if k not in cache:
        cache[k] = frozenset(cb.cubiertas_maximales(Gs, n)) if Gs else frozenset([tuple([INF] * n)])
    return cache[k]


def G_U(G, n, M, T, U, m, lectura_B):
    resto = T - U
    if lectura_B == 'o':
        q = [g for g in G if not (any(g[v] >= M[v] for v in resto) or any(g[u] >= m[u] for u in U))]
    else:
        q = [g for g in G if not (any(g[v] >= M[v] for v in resto) and any(g[u] >= m[u] for u in U))]
    return proyectar(q, T, n)


LECTURAS = [(A, B, C) for A in (1, 0) for B in ('o', 'y') for C in ('a', 'n')]


def dominada_manuscrito(G, n):
    """Para cada lectura, ¿hay M dominante?  Devuelve dict lectura -> bool."""
    res = {L: False for L in LECTURAS}
    cache = {}
    for M in candidatos_M(G, n):
        T = sop(M)
        H = [g for g in G if sop(g) <= T and all(g[j] < M[j] for j in T)]
        if not H:
            continue
        bip = biparticiones(H, T)
        if bip is None:
            continue
        W = set().union(*[sop(h) for h in H])
        m = {w: min(h[w] for h in H if h[w] > 0) for w in W}
        mm = {j: m.get(j, M[j]) for j in T}      # en un vértice aislado (solo con A0) no hay mínimo: no se baja
        aislados = sorted(T - W)
        for A in (1, 0):
            if A == 1 and aislados:
                continue
            if A == 0 and not aislados:
                continue                               # sin aislados las dos lecturas del eje A coinciden: se copia abajo
            repartos = [frozenset(x for x, f in zip(aislados, fl) if f) for fl in itertools.product((0, 1), repeat=len(aislados))]
            for Bl in ('o', 'y'):
                for P0, Q0 in bip:
                    for extra in repartos:
                        P, Q = P0 | extra, Q0 | (frozenset(aislados) - extra)
                        CP = cubiertas_de(G_U(G, n, M, T, P, mm, Bl), n, cache)
                        CQ = cubiertas_de(G_U(G, n, M, T, Q, mm, Bl), n, cache)
                        for a in CP & CQ:
                            for Cl in ('a', 'n'):
                                ok = True
                                for u in T:
                                    if not any(g[u] == M[u] and all(g[v] < mm[v] for v in T if v != u) and
                                               (Cl == 'n' or all(g[v] < a[v] for v in range(n) if v not in T))
                                               for g in G):
                                        ok = False
                                        break
                                if ok:
                                    res[(0, Bl, Cl)] = True
                                    if A == 1:
                                        res[(1, Bl, Cl)] = True
        if all(res.values()):
            break
    return res


# ------------------------------------------------------------------------------------------------------------------ corrida
def trabajo(G):
    n = len(G[0])
    G = sorted(G)
    C = cb.cubiertas_maximales(G, n)
    pares = cb.pares_mismo_soporte(C)
    dom = cb.dominados(G)
    r = {'nosimple': bool(pares), 'TA': anatomia(G, n, C, pares, dom), 'ctrlA': anatomia_mala(G, n, pares)}
    obt, err, deb = teorema_B(G, n, set(C))
    reales = {frozenset((c, d)) for c, d, _ in pares}
    r['TB'] = err or (None if obt == reales else 'pares de TB ≠ pares reales')
    r['TBdebil'] = bool(deb) != bool(pares)          # control: la versión débil debería fallar a veces
    ms = dominada_manuscrito(G, n)
    r['MS'] = {L: ms[L] for L in LECTURAS}
    return G, r


def clave(G):
    return (len(G[0]) - sum(1 for j in range(len(G[0])) if not any(g[j] for g in G)), len(G), sum(map(sum, G)))


def correr(familia, n, w, max_aristas=None, procesos=None):
    gen = en.instancias_B(n, w, max_aristas) if familia == 'B' else en.instancias_M(n, w, max_aristas)
    cont = collections.Counter()
    ej = collections.defaultdict(list)
    t0 = time.time()

    def guarda(tipo, G):
        L = ej[tipo]
        L.append((clave(G), G))
        L.sort()
        del L[6:]

    with multiprocessing.Pool(procesos) as pool:
        for G, r in pool.imap_unordered(trabajo, gen, chunksize=200):
            cont['total'] += 1
            cont['no simple'] += r['nosimple']
            if r['TA']:
                cont['TA falla'] += 1
                guarda('TA: ' + r['TA'], G)
            if r['TB']:
                cont['TB falla'] += 1
                guarda('TB: ' + r['TB'], G)
            cont['ctrl TA-mala detecta'] += r['ctrlA']
            cont['ctrl TB-débil falla'] += r['TBdebil']
            if r['TBdebil']:
                guarda('ctrl TB-débil', G)
            for L in LECTURAS:
                nom = 'A%d-B%s-C%s' % L
                if r['nosimple'] and not r['MS'][L]:
                    cont['MS %s: no simple sin M (falla ⇒)' % nom] += 1
                    guarda('MS %s falla ⇒' % nom, G)
                if not r['nosimple'] and r['MS'][L]:
                    cont['MS %s: simple con M (falla ⇐)' % nom] += 1
                    guarda('MS %s falla ⇐' % nom, G)
    return cont, ej, time.time() - t0


def informe(familia, n, w, max_aristas, cont, ej, seg):
    out = ['# t2_caracterizacion.py %s(%d,%d)%s -- %d anticadenas, %d no simples, %.0f s' % (
        familia, n, w, '' if max_aristas is None else ' con ≤ %d pares' % max_aristas, cont['total'], cont['no simple'], seg)]
    out.append('TA (anatomía de un par; implica «sin dominado ⇒ simple»): %d fallas' % cont['TA falla'])
    out.append('TB (caracterización por M): %d fallas' % cont['TB falla'])
    out.append('Control negativo: TA-mala detectada en %d no simples; TB-débil falla en %d anticadenas' % (
        cont['ctrl TA-mala detecta'], cont['ctrl TB-débil falla']))
    out.append('Segundo `main` de SimplePrimes, por lectura (A: sin aislados 1/0; B: G_U «o»/«y»; C: c = a / nada):')
    for L in LECTURAS:
        nom = 'A%d-B%s-C%s' % L
        out.append('  %s: falla ⇒ en %d (no simples sin M dominante); falla ⇐ en %d (simples con M dominante)' % (
            nom, cont['MS %s: no simple sin M (falla ⇒)' % nom], cont['MS %s: simple con M (falla ⇐)' % nom]))
    out.append('Ejemplos menores de cada tipo:')
    for tipo in sorted(ej):
        out.append('  [%s]' % tipo)
        for _, G in ej[tipo]:
            out.append('    ' + ', '.join(cb.monomio(g) for g in G))
    return '\n'.join(out)


def autotest():
    # ejemplos conocidos
    G, n = cb.parse_monomios('x1x2, x1x3, x2^2x3, x1^2x4')                 # CE-1: simple con dominado
    _, r = trabajo(G)
    assert not r['nosimple'] and r['TA'] is None and r['TB'] is None, r
    G, n = cb.parse_monomios('x1^2, x2^2, x3^2, x1x2, x1x3')                # CE-2: no simple, par (1,2,2),(2,1,1)
    _, r = trabajo(G)
    assert r['nosimple'] and r['TA'] is None and r['TB'] is None and r['ctrlA'], r
    G, n = cb.parse_monomios('x1^2, x1x2, x2^2')
    obt, err, deb = teorema_B(sorted(G), n, set(cb.cubiertas_maximales(G, n)))
    assert err is None and obt == {frozenset(((1, 2), (2, 1)))}, (obt, err)
    # control negativo de TB: en CE-1 hay un M con H bipartita cuyas reparaciones no son maximales
    G, n = cb.parse_monomios('x1x2, x1x3, x2^2x3, x1^2x4')
    obt, err, deb = teorema_B(sorted(G), n, set(cb.cubiertas_maximales(G, n)))
    assert err is None and not obt and deb, 'el control negativo de TB no distingue'
    print('Autotest: CE-1, CE-2 y <x1^2,x1x2,x2^2>; control negativo de TB (versión débil) y de TA (H en U-U).')
    print('EXITO')


if __name__ == '__main__':
    if '--autotest' in sys.argv:
        autotest()
        sys.exit(0)
    fam, n, w = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    ma = int(sys.argv[sys.argv.index('--max-aristas') + 1]) if '--max-aristas' in sys.argv else None
    cont, ej, seg = correr(fam, n, w, ma)
    texto = informe(fam, n, w, ma, cont, ej, seg)
    ok = cont['TA falla'] == 0 and cont['TB falla'] == 0 and (cont['no simple'] == 0 or cont['ctrl TA-mala detecta'] > 0)
    texto += '\n' + ('EXITO' if ok else 'FALLA')
    print(texto)
    if '--salida' in sys.argv:
        open(sys.argv[sys.argv.index('--salida') + 1], 'w').write(texto + '\n')
    sys.exit(0 if ok else 1)
