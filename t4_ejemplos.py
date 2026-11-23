# -*- coding: utf-8 -*-
# t4_ejemplos.py -- T4 (2026-11-19): comprueba, uno por uno, los ejemplos y las cifras de SimplePrimes.tex reescrito en T4
# (las etiquetas del manuscrito van entre paréntesis en cada caso).
# Cada ideal: cubiertas maximales por los dos algoritmos de cubiertas.py y por irreducibleDecomposition de Macaulay2,
# descomposición afirmada en el texto, «simple / no simple», generadores dominados y, donde el texto lo afirma, los pares con el
# mismo soporte y sus conjuntos R, U, V, el vector M = c ∨ d, el conjunto G_{<M}, las reparaciones M^U, M^V (maximales o no),
# los generadores críticos que se nombran, las cubiertas fuertes del camino orientado y la familia estrella S_k (k = 1..6).
# Sin búsqueda: no hay criterio de poda (R-20 no aplica); la única familia es S_k, fijada de antemano.
# Control negativo: una descomposición alterada, un «simple» alterado, un dominado de más, una reparación no maximal declarada
# maximal y un crítico falso deben detectarse.
# Uso: /opt/homebrew/bin/python3 -B t4_ejemplos.py     (termina en «EXITO» o «FALLA»; salida en Salidas/2026-11-19-t4_ejemplos.txt)
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cubiertas as cb
from t2_ejemplos import cubiertas_fuertes

I = cb.INF
LINEAS = []
FALLAS = []
SILENCIO = [False]   # durante el control negativo no se imprime nada


def di(s):
    if SILENCIO[0]:
        return
    LINEAS.append(s)
    print(s)


def exige(cond, msg):
    if not cond:
        FALLAS.append(msg)
        di('  FALLA: ' + msg)


def G_de(texto, n=None):
    G, n = cb.parse_monomios(texto, n)
    G = sorted(G)
    assert cb.es_anticadena(G), ('no es anticadena', texto)
    return G, n


def mon(texto, n):
    return cb.parse_monomios(texto, n)[0][0]


def cubiertas(G, n):
    A, B = cb.cubiertas_maximales(G, n), cb.cubiertas_maximales_fb(G, n)
    assert A == B, 'los dos algoritmos difieren'
    return A


def no_cubiertos(G, M):
    """G_{<M}: los generadores que M no cubre."""
    return sorted(g for g in G if all(g[j] < M[j] for j in range(len(M)) if M[j] < I))


def reparacion(G, M, X):
    """M^X: M con las entradas de X bajadas a m_j = mín de los exponentes de G_{<M} en j."""
    H = no_cubiertos(G, M)
    c = list(M)
    for j in X:
        c[j] = min(h[j] for h in H if h[j] > 0)
    return tuple(c)


def es_maximal(c, G):
    return cb.es_cubierta(c, G) and cb.critica(c, G)


def es_critico(g, c, u):
    s = cb.soporte(c)
    return g[u] == c[u] and all(g[v] < c[v] for v in s if v != u)


CASOS = []   # (etiqueta, texto, n, componentes afirmadas o None, simple, dominados afirmados o None)


def caso(etiqueta, texto, comps, simple, dominados, n=None):
    CASOS.append((etiqueta, texto, n, comps, simple, dominados))


# --- §1 y §2
caso('intro y ex:critical', 'x1^2, x1x2, x2^2', [(1, 2), (2, 1)], False, ['x1x2'])
# --- §3
G1 = 'x1x2, x2^2x3, x3^2x4^2, x1^2x4'
G2 = 'x1x2, x2x3^2, x3^2x4^2, x1^2x4'
caso('ex:cycles G1 / ex:cycles-pairs', G1,
     [(1, I, 1, I), (I, 1, I, 1), (1, 2, 2, I), (2, 1, 2, I), (1, 2, I, 2), (2, 1, I, 2)], False, ['x1x2'])
caso('ex:cycles G2 / ex:cycles-simple', G2, [(1, I, 2, I), (I, 1, I, 1), (2, 1, 2, I), (2, 1, I, 2)], True, [])
caso('ex:star', 'x1^2, x2^2, x3^2, x1x2, x1x3', [(1, 2, 2), (2, 1, 1)], False, ['x1x2', 'x1x3'])
caso('rem:converse = CE-1', 'x1x2, x1x3, x2^2x3, x1^2x4', [(1, 2, I, I), (1, I, 1, I), (2, 1, 1, I), (I, 1, 1, 1)], True, ['x1x2'])
# --- §4
caso('ex:prt-path', 'x1x2^2, x2x3^3', [(I, 1, I), (1, I, 3), (I, 2, 3)], True, [])
caso('rem:beyond (a) lazo', 'x1^2, x1x2, x1x3', [(1, I, I), (2, 1, 1)], True, [])
caso('rem:beyond (a) arista doble', 'x1x2, x1x3^2, x1^2x3', [(1, I, I), (2, 1, 2), (I, 1, 1)], True, [])
caso('rem:beyond (c)', 'x1x2, x1x3, x2^2x3^2', [(1, 2, I), (1, I, 2), (I, 1, 1)], True, [])
caso('rem:beyond (d)', 'x1x2, x1^2x3, x1^3x4', [(1, I, I, I), (2, 1, I, I), (3, 1, 1, I), (I, 1, 1, 1)], True, [])
caso('ex:triangle', 'x1x2, x2^2x3^2, x1^3x3^3', [(1, 2, I), (1, I, 2), (3, 1, I), (I, 1, 3)], False, ['x1x2'])
# --- §5
caso('ex:dominating = CE-4', 'x1^2, x2^2, x1x2, x1x3^2, x2x3', [(1, 1, I), (1, 2, 1), (2, 1, 2)], False, ['x1x2', 'x2x3'])
caso('ex:bipartitions = CE-5', 'x1^2, x3^2, x4^2, x1x3, x2x4, x1x2^2', None, False, None)
caso('rem:hypothesis (sin soporte gráfica)', 'x1^3, x1^2x2x3, x1x2^2x3, x2^2x3^2', None, False, None)
caso('rem:hypothesis (VA-1: sin dominados y no simple, sin soporte gráfica)', 'x2^2, x3^2, x1x2x3', [(1, 2, 2), (I, 1, 2), (I, 2, 1)], False, [])
# --- §6
caso('ex:nonlocal G3', 'x1x2, x1^2x3, x2^2x4', [(1, 2, I, I), (2, 1, I, I), (1, I, I, 1), (I, 1, 1, I)], False, ['x1x2'])
caso('ex:nonlocal G4', 'x1x2, x1^2x3, x2^2x4, x3x4', [(1, 2, 1, I), (2, 1, I, 1), (1, I, I, 1), (I, 1, 1, I)], True, ['x1x2'])


def comprobar_casos(casos, alterar=False):
    """Devuelve el número de discrepancias; con alterar=True, siembra errores (control negativo) y no las imprime."""
    fallas0 = len(FALLAS)
    ideales = []
    for etq, texto, n, comps, simple, dom in casos:
        G, n = G_de(texto, n)
        ideales.append((G, n))
    m2 = cb.m2_descomposiciones(ideales)
    for (etq, texto, n, comps, simple, dom), (G, n), m2c in zip(casos, ideales, m2):
        C = cubiertas(G, n)
        if alterar and comps:
            comps = comps[:-1] + [tuple(a + 1 if a < I else a for a in comps[-1])]
            simple = not simple
            dom = (dom or []) + ['x1']
        di('%s: I = <%s>' % (etq, texto))
        di('  = ' + ' ∩ '.join(cb.componente(c) for c in C))
        exige(C == m2c, '%s: Macaulay2 da otra descomposición' % etq)
        if comps is not None:
            exige(sorted(comps) == C, '%s: la descomposición del texto no es la calculada' % etq)
        es_simple = not cb.pares_mismo_soporte(C)
        di('  simple: %s; dominados: %s' % (es_simple, [cb.monomio(g) for g in cb.dominados(G)]))
        exige(es_simple == simple, '%s: «simple» del texto no coincide' % etq)
        if dom is not None:
            exige(sorted(cb.monomio(g) for g in cb.dominados(G)) == sorted(dom), '%s: dominados del texto no coinciden' % etq)
    return len(FALLAS) - fallas0


def particulares():
    # ex:cycles-pairs: los dos pares de G1, con R, U, V, M, H y los críticos que nombra el texto
    G, n = G_de(G1)
    pares = sorted((c, d) for c, d, _ in cb.pares_mismo_soporte(cubiertas(G, n)))
    di('ex:cycles-pairs: pares con el mismo soporte: %s' % [(cb.vec(c), cb.vec(d)) for c, d in pares])
    esperados = {((1, 2, 2, I), (2, 1, 2, I)): {2}, ((1, 2, I, 2), (2, 1, I, 2)): {3}}
    hallados = {}
    for c, d in pares:
        if c[0] > d[0]:
            c, d = d, c
        T = cb.soporte(c)
        R = {j for j in T if c[j] == d[j]}
        U = {j for j in T if c[j] < d[j]}
        V = {j for j in T if d[j] < c[j]}
        M = tuple(max(a, b) for a, b in zip(c, d))
        H = no_cubiertos(G, M)
        hallados[(c, d)] = R
        exige(U == {0} and V == {1}, 'ex:cycles-pairs: U, V')
        exige([cb.monomio(h) for h in H] == ['x1x2'], 'ex:cycles-pairs: H')
    exige(hallados == esperados, 'ex:cycles-pairs: los pares o sus R')
    c, d = (1, 2, 2, I), (2, 1, 2, I)
    exige(es_critico(mon('x1x2', 4), c, 0) and es_critico(mon('x1x2', 4), d, 1), 'ex:cycles-pairs: x1x2 crítico')
    exige(es_critico(mon('x1^2x4', 4), d, 0), 'ex:cycles-pairs: x1^2x4 d-crítico en 1')
    exige(es_critico(mon('x2^2x3', 4), c, 1), 'ex:cycles-pairs: x2^2x3 c-crítico en 2')
    exige(no_cubiertos(G, (2, 2, 2, I)) == [mon('x1x2', 4)], 'ex:dominating (G1): M = (2,2,2,∞)')

    # ex:star: R, U, V, H y la familia S_k
    G, n = G_de('x1^2, x2^2, x3^2, x1x2, x1x3')
    exige([cb.monomio(h) for h in no_cubiertos(G, (2, 2, 2))] == ['x1x3', 'x1x2'] or
          sorted(cb.monomio(h) for h in no_cubiertos(G, (2, 2, 2))) == ['x1x2', 'x1x3'], 'ex:star: H')
    for k in range(1, 7):
        texto = ', '.join(['x1^2'] + ['x%d^2' % (i + 2) for i in range(k)] + ['x1x%d' % (i + 2) for i in range(k)])
        G, n = G_de(texto)
        C = cubiertas(G, n)
        esperado = sorted([tuple([1] + [2] * k), tuple([2] + [1] * k)])
        exige(C == esperado, 'ex:star: S_%d' % k)
    di('ex:star: la familia S_k (k = 1..6, con x_0 = x1) tiene exactamente las dos cubiertas del texto')

    # ex:prt-path: cubiertas fuertes = cubiertas maximales
    F = cubiertas_fuertes(3, [(0, 1), (1, 2)], [1, 2, 3])
    G, n = G_de('x1x2^2, x2x3^3')
    exige(sorted(F) == cubiertas(G, n), 'ex:prt-path: cubiertas fuertes')
    di('ex:prt-path: cubiertas fuertes %s' % [cb.vec(c) for c in sorted(F)])

    # ex:dominating = CE-4
    G, n = G_de('x1^2, x2^2, x1x2, x1x3^2, x2x3')
    M = (2, 2, 2)
    exige(sorted(cb.monomio(h) for h in no_cubiertos(G, M)) == ['x1x2', 'x2x3'], 'ex:dominating: H')
    MU, MV = reparacion(G, M, [0, 2]), reparacion(G, M, [1])
    exige(MU == (1, 2, 1) and MV == (2, 1, 2), 'ex:dominating: M^U, M^V')
    exige(es_maximal(MU, G) and es_maximal(MV, G), 'ex:dominating: M^U, M^V maximales')
    exige(es_critico(mon('x2^2', 3), MU, 1) and es_critico(mon('x1^2', 3), MV, 0) and es_critico(mon('x1x3^2', 3), MV, 2),
          'ex:dominating: críticos nombrados')

    # ex:not-dominating (CE-1)
    G, n = G_de('x1x2, x1x3, x2^2x3, x1^2x4')
    exige(sorted(cb.monomio(h) for h in no_cubiertos(G, (2, 2, I, I))) == ['x1x2', 'x1x3'], 'ex:not-dominating: M1')
    M = (2, 2, 1, I)
    exige([cb.monomio(h) for h in no_cubiertos(G, M)] == ['x1x2'], 'ex:not-dominating: M2, H')
    MU = reparacion(G, M, [0])
    exige(MU == (1, 2, 1, I) and cb.es_cubierta(MU, G) and not es_maximal(MU, G), 'ex:not-dominating: M^U no maximal')

    # ex:bipartitions = CE-5
    G, n = G_de('x1^2, x3^2, x4^2, x1x3, x2x4, x1x2^2')
    M = (2, 2, 2, 2)
    exige(sorted(cb.monomio(h) for h in no_cubiertos(G, M)) == ['x1x3', 'x2x4'], 'ex:bipartitions: H')
    a, b = reparacion(G, M, [0, 1]), reparacion(G, M, [2, 3])
    exige(a == (1, 1, 2, 2) and b == (2, 2, 1, 1) and es_maximal(a, G) and es_maximal(b, G), 'ex:bipartitions: U={1,2}')
    a, b = reparacion(G, M, [0, 3]), reparacion(G, M, [1, 2])
    exige(a == (1, 2, 2, 1) and not es_maximal(a, G) and b == (2, 1, 1, 2) and es_maximal(b, G), 'ex:bipartitions: U={1,4}')
    C = cubiertas(G, n)
    tres = [c for c in C if cb.soporte(c) == frozenset(range(4))]
    exige(sorted(tres) == sorted([(1, 1, 2, 2), (2, 2, 1, 1), (2, 1, 1, 2)]), 'ex:bipartitions: tres con el mismo radical')
    di('ex:bipartitions: cubiertas con soporte {1,2,3,4}: %s' % [cb.vec(c) for c in sorted(tres)])

    # rem:hypothesis: c = (3,∞,1), d = (1,∞,2) maximales; G_{<c∨d} con tres variables
    G, n = G_de('x1^3, x1^2x2x3, x1x2^2x3, x2^2x3^2')
    C = cubiertas(G, n)
    exige((3, I, 1) in C and (1, I, 2) in C, 'rem:hypothesis: c, d')
    exige(sorted(cb.monomio(h) for h in no_cubiertos(G, (3, I, 2))) == ['x1^2x2x3', 'x1x2^2x3'], 'rem:hypothesis: G_<M')

    # ex:partial-converse con G1: G'' = {x3^2x4^2}, sus cubiertas y el par que predice cada una
    G, n = G_de(G1)
    Gpp = [g for g in G if g[0] == 0 and g[1] == 0]
    Cpp = cb.cubiertas_maximales(Gpp, n)
    exige(sorted(Cpp) == [(I, I, 2, I), (I, I, I, 2)], 'ex:partial-converse: cubiertas de G\'\'')
    C = cubiertas(G, n)
    for ap in Cpp:
        c = (1, 2) + ap[2:]
        d = (2, 1) + ap[2:]
        exige(c in C and d in C, 'ex:partial-converse: el par de %s' % cb.vec(ap))
    # ex:nonlocal G3: M = (2,2,∞,∞) domina
    G, n = G_de('x1x2, x1^2x3, x2^2x4')
    M = (2, 2, I, I)
    exige([cb.monomio(h) for h in no_cubiertos(G, M)] == ['x1x2'], 'ex:nonlocal: H de G3')
    exige(es_maximal(reparacion(G, M, [0]), G) and es_maximal(reparacion(G, M, [1]), G), 'ex:nonlocal: M^{1}, M^{2}')


def control_negativo():
    """Errores sembrados: deben detectarse."""
    global FALLAS
    guardadas = FALLAS
    FALLAS = []
    SILENCIO[0] = True
    n_alt = comprobar_casos([c for c in CASOS if c[3] is not None][:3], alterar=True)
    G, n = G_de('x1x2, x1x3, x2^2x3, x1^2x4')
    no_max = reparacion(G, (2, 2, 1, I), [0])
    falso_max = es_maximal(no_max, G)
    falso_critico = es_critico(mon('x2^2x3', 4), no_max, 1)
    FALLAS = guardadas
    SILENCIO[0] = False
    return n_alt >= 3 * 3 and not falso_max and not falso_critico


def principal():
    di('t4_ejemplos.py -- ejemplos de SimplePrimes.tex (T4, 2026-11-19)')
    comprobar_casos(CASOS)
    particulares()
    ok_neg = control_negativo()
    di('Control negativo: %s (descomposición, «simple» y dominados alterados; reparación no maximal; crítico falso)'
       % ('detectado' if ok_neg else 'NO detectado'))
    salida = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'Salidas', '2026-11-19-t4_ejemplos.txt')
    if FALLAS or not ok_neg:
        di('FALLA: %d discrepancias' % len(FALLAS))
        open(salida, 'w', encoding='utf-8').write('\n'.join(LINEAS) + '\n')
        sys.exit(1)
    di('%d ideales, todos con dos algoritmos y Macaulay2; cifras particulares comprobadas' % len(CASOS))
    di('EXITO')
    open(salida, 'w', encoding='utf-8').write('\n'.join(LINEAS) + '\n')


if __name__ == '__main__':
    principal()
