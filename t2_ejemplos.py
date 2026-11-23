# -*- coding: utf-8 -*-
# t2_ejemplos.py -- T2 (2026-11-19): comprueba, uno por uno, los ejemplos y las cifras de
# Contexto/Exploracion-T2-2026-11-19/Pruebas.tex y los contraejemplos CE-4 y CE-5 de Contraejemplos/Contraejemplos.tex.
# Cada ejemplo: cubiertas maximales por los dos algoritmos de cubiertas.py y por irreducibleDecomposition de Macaulay2,
# «simple / no simple», generadores dominados y, donde el texto lo afirma, el conjunto H_M, las reparaciones M^U, M^V,
# las cubiertas fuertes de una gráfica orientada con pesos y las familias (estrella, biparticiones).
# Sin búsqueda: no hay criterio de poda (R-20 no aplica); la única familia es la estrella S_k, k = 1..6, fijada de antemano.
# Control negativo: una descomposición alterada, un «simple» alterado y una reparación no maximal deben detectarse.
# Uso: /opt/homebrew/bin/python3 -B t2_ejemplos.py     (termina en «EXITO» o «FALLA»)
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cubiertas as cb
import t2_caracterizacion as t2

INF = cb.INF
I = INF
LINEAS = []


def di(s):
    LINEAS.append(s)
    print(s)


def datos(texto, n=None):
    G, n = cb.parse_monomios(texto, n)
    G = sorted(G)
    assert cb.es_anticadena(G), ('no es anticadena', texto)
    A, B = cb.cubiertas_maximales(G, n), cb.cubiertas_maximales_fb(G, n)
    assert A == B, ('los algoritmos difieren', texto)
    return G, n, A


EJEMPLOS = []      # (nombre, texto, cubiertas esperadas, simple, dominados esperados)


def ej(nombre, texto, cubiertas, simple, dominados, n=None):
    EJEMPLOS.append((nombre, texto, None if cubiertas is None else sorted(cubiertas), simple, dominados, n))


# --- Sección 1 (lema de criticidad)
ej('ex:critical', 'x1^2, x1x2, x2^2', [(1, 2), (2, 1)], False, ['x1x2'])
# --- Sección 2 (anatomía y Teorema A)
ej('ex:star (k=2) = CE-2', 'x1^2, x2^2, x3^2, x1x2, x1x3', [(1, 2, 2), (2, 1, 1)], False, ['x1x2', 'x1x3'])
ej('ex:nodominated', 'x1x2, x1x3, x2^2x3^2', [(1, 2, I), (1, I, 2), (I, 1, 1)], True, [])
ej('rem:converse = CE-1', 'x1x2, x1x3, x2^2x3, x1^2x4',
   [(1, 2, I, I), (1, I, 1, I), (2, 1, 1, I), (I, 1, 1, 1)], True, ['x1x2'])
# --- Sección 3 (gráficas orientadas con pesos)
ej('ex:prt-path', 'x1x2^2, x2x3^3', [(I, 1, I), (I, 2, 3), (1, I, 3)], True, [])
ej('rem:beyond (lazo)', 'x1^2, x1x2, x1x3', [(1, I, I), (2, 1, 1)], True, [])
ej('rem:beyond (arista múltiple)', 'x1x2, x1x3^2, x1^2x3', [(1, I, I), (2, 1, 2), (I, 1, 1)], True, [])
ej('rem:beyond (tres exponentes)', 'x1x2, x1^2x3, x1^3x4', [(1, I, I, I), (2, 1, I, I), (3, 1, 1, I), (I, 1, 1, 1)], True, [])
# --- Sección 4 (caracterización)
ej('ex:dominating = CE-4', 'x1^2, x2^2, x1x2, x1x3^2, x2x3', [(1, 1, I), (1, 2, 1), (2, 1, 2)], False, ['x1x2', 'x2x3'])
# --- Sección 5 (complementos)
ej('ex:nonlocal G1', 'x1x2, x1^2x3, x2^2x4', [(1, 2, I, I), (2, 1, I, I), (1, I, I, 1), (I, 1, 1, I)], False, ['x1x2'])
ej('ex:nonlocal G2', 'x1x2, x1^2x3, x2^2x4, x3x4', [(1, 2, 1, I), (2, 1, I, 1), (1, I, I, 1), (I, 1, 1, I)], True, ['x1x2'])
ej('ex:multiple = CE-3', 'x1^3, x2^3, x1x2^2, x1^2x2', [(1, 3), (2, 2), (3, 1)], False, ['x1x2^2', 'x1^2x2'])
ej('ex:bipartitions = CE-5', 'x1^2, x3^2, x4^2, x1x3, x2x4, x1x2^2', None, False, None)
ej('árbol simple con dominado', 'x1x3, x1x2, x1^2x4, x2^2x5', None, True, ['x1x2'])
ej('ex:partial-converse', 'x1x2, x2^2x3, x3^2x4^2, x1^2x4',
   [(1, 2, 2, I), (2, 1, 2, I), (1, 2, I, 2), (2, 1, I, 2), (1, I, 1, I), (I, 1, I, 1)], False, ['x1x2'])


def cubiertas_fuertes(n, E, w):
    """Cubiertas fuertes de Pitones-Reyes-Toledo (Def. 2.3 y 2.6 de arXiv:1710.03785v1) y su vector c(C)."""
    res = []
    for k in range(n + 1):
        for C in itertools.combinations(range(n), k):
            C = set(C)
            if any(a not in C and b not in C for a, b in E):
                continue
            L1 = {x for x in C if any(a == x and b not in C for a, b in E)}
            L2 = {x for x in C if x not in L1 and any(b == x and a not in C for a, b in E)}
            L3 = C - L1 - L2
            if all(any(b == x and a in (L2 | L3) and w[a] != 1 for a, b in E) for x in L3):
                res.append(tuple(INF if x not in C else (1 if x in L1 else w[x]) for x in range(n)))
    return sorted(res)


def principal():
    ok = True
    m2 = cb.m2_descomposiciones([(datos(t, n)[0], datos(t, n)[1]) for _, t, _, _, _, n in EJEMPLOS], os.environ.get('TMPDIR'))
    di('## Ejemplos de Pruebas.tex (cubiertas maximales: algoritmos A = B = Macaulay2)')
    for (nombre, texto, esperadas, simple, dominados, n0), comps in zip(EJEMPLOS, m2):
        G, n, C = datos(texto, n0)
        a = cb.analizar(G, n)
        fallas = []
        if comps != C:
            fallas.append('M2 difiere')
        if esperadas is not None and C != esperadas:
            fallas.append('cubiertas ≠ esperadas')
        if a['simple'] != simple:
            fallas.append('simple ≠ esperado')
        dom = sorted(cb.monomio(g) for g in a['dominados'])
        if dominados is not None and dom != sorted(cb.monomio(cb.parse_monomios(d, n)[0][0]) for d in dominados):
            fallas.append('dominados ≠ esperados')
        ok &= not fallas
        di('- %s: <%s> = %s | %s | dominados: %s | pares: %s%s' % (
            nombre, texto, ' ∩ '.join(cb.componente(c) for c in C), 'simple' if a['simple'] else 'NO simple',
            ', '.join(dom) or 'ninguno', '; '.join(cb.vec(c) + '~' + cb.vec(d) for c, d, _ in a['pares']) or 'ninguno',
            ('  **FALLA: ' + ', '.join(fallas) + '**') if fallas else ''))

    di('## Afirmaciones puntuales')
    # ex:critical: (1,1) es cubierta y no es maximal ni crítica en 1
    G, n, C = datos('x1^2, x1x2, x2^2')
    t = cb.es_cubierta((1, 1), G) and (1, 1) not in C and not t2.critica_en((1, 1), G, 0)
    ok &= t
    di('- ex:critical: (1,1) es cubierta, no maximal, sin generador crítico en 1: %s' % t)
    # ex:star: M = (2,2,2), H_M = {x1x2, x1x3}, U = {1}, V = {2,3}
    G, n, C = datos('x1^2, x2^2, x3^2, x1x2, x1x3')
    H = sorted(cb.monomio(g) for g in G if all(g[j] < 2 for j in range(3)))
    t = H == ['x1x2', 'x1x3']
    ok &= t
    di('- ex:star: H_M con M = (2,2,2) es {x1x2, x1x3}: %s' % t)
    # familia estrella S_k: {x0^2, xi^2, x0xi}: exactamente dos cubiertas maximales, (1,2,...,2) y (2,1,...,1)
    for k in range(1, 7):
        n = k + 1
        G = [tuple(2 if j == i else 0 for j in range(n)) for i in range(n)] + \
            [tuple(1 if j in (0, i) else 0 for j in range(n)) for i in range(1, n)]
        C = cb.cubiertas_maximales(sorted(G), n)
        t = C == sorted([(1,) + (2,) * k, (2,) + (1,) * k]) and len(cb.dominados(G)) == k
        ok &= t
        di('- estrella S_%d: cubiertas maximales = {(1,2,...,2), (2,1,...,1)}, %d dominados: %s' % (k, k, t))
    # ex:prt-path: las cubiertas fuertes dan las cubiertas maximales
    G, n, C = datos('x1x2^2, x2x3^3')
    F = cubiertas_fuertes(3, [(0, 1), (1, 2)], [1, 2, 3])
    t = F == C
    ok &= t
    di('- ex:prt-path: c(C), C fuerte = %s = cubiertas maximales: %s' % (' '.join(cb.vec(c) for c in F), t))
    # ex:dominating (CE-4): M = (2,2,2), H_M = {x1x2, x2x3}, U = {1,3}, V = {2}; M^U = (1,2,1), M^V = (2,1,2) maximales;
    # el inciso (iii) de la Definición `dominated` del manuscrito falla en u = 3 (no hay g con g_3 = 2, g_1 < 1, g_2 < 1)
    G, n, C = datos('x1^2, x2^2, x1x2, x1x3^2, x2x3')
    M = (2, 2, 2)
    H = [g for g in G if all(g[j] < M[j] for j in range(3))]
    m = {w: min(h[w] for h in H if h[w]) for w in range(3)}
    MU, MV = t2.bajar(M, {0, 2}, m), t2.bajar(M, {1}, m)
    t = sorted(cb.monomio(h) for h in H) == ['x1x2', 'x2x3'] and MU == (1, 2, 1) and MV == (2, 1, 2) and MU in C and MV in C
    t &= not any(g[2] == 2 and g[0] < 1 and g[1] < 1 for g in G)
    ms = t2.dominada_manuscrito(G, n)
    t &= not any(ms.values())
    ok &= t
    di('- ex:dominating (CE-4): H_M, M^U, M^V como en el texto; (iii) del manuscrito falla en u = 3; ningún M dominante '
       'bajo ninguna de las 8 lecturas: %s' % t)
    # CE-1: M = (2,2,1,∞): H_M = {x1x2}; M^U = (1,2,1,∞) es cubierta y no es maximal (no crítica en 2)
    G, n, C = datos('x1x2, x1x3, x2^2x3, x1^2x4')
    M = (2, 2, 1, INF)
    H = [g for g in G if all(g[j] < M[j] for j in range(3))]
    MU = (1, 2, 1, INF)
    t = [cb.monomio(h) for h in H] == ['x1x2'] and cb.es_cubierta(MU, G) and MU not in C and not t2.critica_en(MU, G, 1)
    ok &= t
    di('- CE-1 con M = (2,2,1,∞): H_M = {x1x2}, M^U = (1,2,1,∞) cubierta no crítica en 2: %s' % t)
    # ex:bipartitions (CE-5): M = (2,2,2,2), H_M = {x1x3, x2x4}; ({1,2},{3,4}) da par; ({1,4},{2,3}) no
    G, n, C = datos('x1^2, x3^2, x4^2, x1x3, x2x4, x1x2^2')
    M = (2, 2, 2, 2)
    H = [g for g in G if all(g[j] < 2 for j in range(4))]
    m = {w: 1 for w in range(4)}
    par1 = (t2.bajar(M, {0, 1}, m), t2.bajar(M, {2, 3}, m))
    par2 = (t2.bajar(M, {0, 3}, m), t2.bajar(M, {1, 2}, m))
    t = sorted(cb.monomio(h) for h in H) == ['x1x3', 'x2x4'] and all(c in C for c in par1) and \
        par2[0] not in C and par2[1] in C and not t2.critica_en(par2[0], G, 1)
    ok &= t
    di('- ex:bipartitions (CE-5): cubiertas %s; ({1,2},{3,4}) da el par %s, %s; con ({1,4},{2,3}), %s no es maximal '
       '(no crítica en 2) y %s sí: %s' % (' '.join(cb.vec(c) for c in C), cb.vec(par1[0]), cb.vec(par1[1]),
                                          cb.vec(par2[0]), cb.vec(par2[1]), t))
    # prop:selections: para cada par (c, d) de cada ejemplo, las selecciones J, J' del texto dan G_J = c y G_J' = d
    t, npares = True, 0
    for _, texto, _, _, _, n0 in EJEMPLOS:
        G, n, C = datos(texto, n0)
        for c, d, D in cb.pares_mismo_soporte(C):
            npares += 1
            S = cb.soporte(c)
            M = tuple(max(a, b) if a < INF else INF for a, b in zip(c, d))
            U = {j for j in D if c[j] < d[j]}
            GJ, GJ2 = [INF] * n, [INF] * n
            for g in G:
                if all(g[j] < M[j] for j in S):
                    u = [j for j in cb.soporte(g) if j in U][0]
                    v = [j for j in cb.soporte(g) if j not in U][0]
                else:
                    u = v = [j for j in S if g[j] >= M[j]][0]
                GJ[u], GJ2[v] = min(GJ[u], g[u]), min(GJ2[v], g[v])
            t &= tuple(GJ) == c and tuple(GJ2) == d
    ok &= t and npares > 0
    di('- prop:selections: en los %d pares de los ejemplos, G_J = c y G_J\' = d: %s' % (npares, t))
    # lem:monotone: con phi_j(e) = e^2 + j (estrictamente creciente) las cubiertas maximales se corresponden; y con una phi
    # NO creciente (que intercambia los dos exponentes menores de x1) la correspondencia debe romperse en algún ejemplo
    t, rompe = True, False
    for _, texto, _, _, _, n0 in EJEMPLOS:
        G, n, C = datos(texto, n0)
        phi = lambda e, j: e * e + j
        G2 = sorted(tuple(phi(a, j) if a else 0 for j, a in enumerate(g)) for g in G)
        C2 = sorted(tuple(phi(a, j) if a < INF else INF for j, a in enumerate(c)) for c in C)
        t &= cb.es_anticadena(G2) and cb.cubiertas_maximales(G2, n) == C2
        E0 = sorted({g[0] for g in G if g[0]})
        if len(E0) >= 2:
            mal = lambda e, j: (E0[1] if e == E0[0] else E0[0] if e == E0[1] else e) if j == 0 else e
            G3 = cb.minimalizar([tuple(mal(a, j) if a else 0 for j, a in enumerate(g)) for g in G])
            C3 = sorted(tuple(mal(a, j) if a < INF else INF for j, a in enumerate(c)) for c in C)
            rompe |= cb.cubiertas_maximales(G3, n) != C3
    ok &= t and rompe
    di('- lem:monotone: phi_j(e) = e^2 + j conserva anticadena y cubiertas maximales en todos los ejemplos: %s; '
       'control negativo (phi no creciente rompe la correspondencia): %s' % (t, rompe))
    # biparticiones (CE-5): en B(4,2), M(4,2) y B(4,3) (familias de enumeracion.py, mismo criterio de poda), vectores M con
    # H_M bipartita y disconexa en los que alguna bipartición da un par de cubiertas maximales: ¿lo dan todas?
    import enumeracion as en
    con_par = todas = 0
    for fam, n, w in (('B', 4, 2), ('M', 4, 2), ('B', 4, 3)):
        for G in (en.instancias_B(n, w) if fam == 'B' else en.instancias_M(n, w)):
            G = sorted(G)
            Cs = set(cb.cubiertas_maximales(G, n))
            for M in t2.candidatos_M(G, n):
                S = t2.sop(M)
                H = [g for g in G if all(g[j] < M[j] for j in S)]
                bip = t2.biparticiones(H, S) if H else None
                if bip is None or len(bip) < 4:
                    continue
                m = {x: min(h[x] for h in H if h[x]) for x in set().union(*[t2.sop(h) for h in H])}
                dan = [t2.bajar(M, U, m) in Cs and t2.bajar(M, V, m) in Cs for U, V in bip]
                con_par += any(dan)
                todas += all(dan)
    t = con_par > todas > 0
    ok &= t
    di('- biparticiones en B(4,2), M(4,2), B(4,3): %d vectores M con gráfica disconexa y algún par; en %d de ellos todas las '
       'biparticiones dan par: %s' % (con_par, todas, t))
    # rem:bijection: sin soporte gráfica, thm:main (a) falla (ejemplo del verificador V1, I2)
    G = sorted([(3, 0, 0), (2, 1, 1), (1, 2, 1), (0, 2, 2)])
    C = cb.cubiertas_maximales(G, 3)
    assert C == cb.cubiertas_maximales_fb(G, 3) and cb.es_anticadena(G)
    c, d, M = (3, INF, 1), (1, INF, 2), (3, INF, 2)
    H = sorted(g for g in G if g[0] < 3 and g[2] < 2)
    t = c in C and d in C and H == [(1, 2, 1), (2, 1, 1)] and cb.m2_descomposiciones([(G, 3)], os.environ.get('TMPDIR'))[0] == C
    ok &= t
    di('- rem:bijection (sin soporte gráfica): <x1^3, x1^2x2x3, x1x2^2x3, x2^2x3^2> tiene las maximales (3,∞,1) y (1,∞,2), y '
       'los no cubiertos por (3,∞,2) son los dos generadores de tres variables: %s' % t)
    # controles negativos
    G, n, C = datos('x1^2, x1x2, x2^2')
    t = cb.m2_descomposiciones([(G, n)], os.environ.get('TMPDIR'))[0] != [(1, 2), (2, 2)] and cb.analizar(G, n)['simple'] is False
    ok &= t
    di('- control negativo: una descomposición alterada y un «simple» alterado se detectan: %s' % t)
    di('EXITO' if ok else 'FALLA')
    return ok


if __name__ == '__main__':
    bien = principal()
    if '--salida' in sys.argv:
        open(sys.argv[sys.argv.index('--salida') + 1], 'w').write('\n'.join(LINEAS) + '\n')
    sys.exit(0 if bien else 1)
