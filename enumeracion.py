# -*- coding: utf-8 -*-
# enumeracion.py -- la Tabla 1: enumeración exhaustiva de anticadenas de soporte gráfica en gráficas conexas chicas.
# Familias:
#   B(n,w): gráfica simple conexa con n vértices y un generador x_p^a x_q^b en cada arista, con exponentes 1..w.
#   M(n,w): gráfica conexa con n vértices; en cada arista {p,q}, una anticadena no vacía de generadores x_p^a x_q^b con
#           1 <= a,b <= w (aristas múltiples), y en algunos vértices un lazo x_p^e con 2 <= e <= w; el total debe ser una
#           anticadena (a < e en cada arista de un vértice con lazo).
#   Con --max-aristas K se toman solo las gráficas con a lo más K aristas.
# Se toma una gráfica por clase de isomorfismo (con su conjunto de lazos), y en cada variable los exponentes positivos que
# aparecen son 1, 2, ..., k (Lema 4.4); no se identifican las anticadenas que intercambian los automorfismos.
# Para cada anticadena se cuentan: si es simple y si tiene un generador dominado.  Se comprueba el Teorema 3.6: toda
# anticadena sin generador dominado es simple; si alguna no lo es, se imprime y el guion termina en FALLA.
# Autotest y control negativo (--autotest): ejemplos conocidos caen donde deben, y los números de gráficas conexas, de
# anticadenas en la rejilla y de tuplas apretadas son los correctos.
# Uso: python3 enumeracion.py B 5 2 [--max-aristas K]     python3 enumeracion.py --autotest
import collections, itertools, multiprocessing, sys, time
import cubiertas as cb

INF = cb.INF


def canon_grafica(n, E, L=frozenset()):
    best = None
    for p in itertools.permutations(range(n)):
        k = (tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in E)), tuple(sorted(p[v] for v in L)))
        if best is None or k < best:
            best = k
    return best


def conexa(n, E):
    ady = collections.defaultdict(set)
    for a, b in E:
        ady[a].add(b)
        ady[b].add(a)
    vistos, pila = {0}, [0]
    while pila:
        v = pila.pop()
        for u in ady[v]:
            if u not in vistos:
                vistos.add(u)
                pila.append(u)
    return len(vistos) == n


def graficas(n, max_aristas=None):
    pares = list(itertools.combinations(range(n), 2))
    vistas, res = set(), []
    for k in range(n - 1, len(pares) + 1):
        if max_aristas is not None and k > max_aristas:
            break
        for E in itertools.combinations(pares, k):
            if conexa(n, E):
                c = canon_grafica(n, E)
                if c not in vistas:
                    vistas.add(c)
                    res.append(list(c[0]))
    return res


def apretadas(d, w):
    """Tuplas de longitud d en 1..w cuyo conjunto de valores es {1,...,k}."""
    return [t for t in itertools.product(range(1, w + 1), repeat=d) if set(t) == set(range(1, max(t) + 1))]


def apretada(G, n):
    for j in range(n):
        s = {g[j] for g in G if g[j] > 0}
        if s and s != set(range(1, max(s) + 1)):
            return False
    return True


def instancias_B(n, w, max_aristas=None):
    for E in graficas(n, max_aristas):
        inc = [[(i, 0 if e[0] == v else 1) for i, e in enumerate(E) if v in e] for v in range(n)]
        for asig in itertools.product(*[apretadas(len(inc[v]), w) for v in range(n)]):
            pesos = [[0, 0] for _ in E]
            for v in range(n):
                for (i, lado), a in zip(inc[v], asig[v]):
                    pesos[i][lado] = a
            G = []
            for (p, q), (a, b) in zip(E, pesos):
                g = [0] * n
                g[p], g[q] = a, b
                G.append(tuple(g))
            yield G


def anticadenas_par(w):
    pts = [(a, b) for a in range(1, w + 1) for b in range(1, w + 1)]
    res = []
    for k in range(1, len(pts) + 1):
        for S in itertools.combinations(pts, k):
            if all(not (x[0] <= y[0] and x[1] <= y[1]) for x in S for y in S if x != y):
                res.append(S)
    return res


def instancias_M(n, w, max_aristas=None):
    AP = anticadenas_par(w)
    vistas = set()
    formas = []
    for E in graficas(n, max_aristas):
        for k in range(n + 1):
            for L in itertools.combinations(range(n), k):
                c = canon_grafica(n, E, L)
                if c not in vistas:
                    vistas.add(c)
                    formas.append((list(c[0]), list(c[1])))
    for E, L in formas:
        for lazos in itertools.product(range(2, w + 1), repeat=len(L)):
            tope = [INF] * n
            for v, e in zip(L, lazos):
                tope[v] = e
            opciones = [[S for S in AP if all(a < tope[p] and b < tope[q] for a, b in S)] for (p, q) in E]
            for elec in itertools.product(*opciones):
                G = []
                for v, e in zip(L, lazos):
                    g = [0] * n
                    g[v] = e
                    G.append(tuple(g))
                for (p, q), S in zip(E, elec):
                    for a, b in S:
                        g = [0] * n
                        g[p], g[q] = a, b
                        G.append(tuple(g))
                if apretada(G, n):
                    yield G


def clave(G):
    n = len(G[0])
    usados = sum(1 for j in range(n) if any(g[j] for g in G))
    return (len(G), usados, sum(map(sum, G)), max(max(g) for g in G))



def trabajo(G):
    a = cb.analizar(G, len(G[0]))
    assert len(a['G']) == len(G), 'no es anticadena'
    return G, a['simple'], bool(a['dominados'])


def correr(familia, n, w, max_aristas=None):
    gen = instancias_B(n, w, max_aristas) if familia == 'B' else instancias_M(n, w, max_aristas)
    cont = collections.Counter()
    contraejemplos = []
    t0 = time.time()
    with multiprocessing.Pool() as pool:
        for G, simple, dom in pool.imap_unordered(trabajo, gen, chunksize=500):
            cont['anticadenas'] += 1
            cont['simples' if simple else 'no simples'] += 1
            if not dom:
                cont['sin generador dominado'] += 1
                if not simple:
                    contraejemplos.append(G)
    return cont, contraejemplos, time.time() - t0


def autotest():
    a = cb.analizar(*cb.parse_monomios('x1x2, x1x3, x2^2x3, x1^2x4'))     # Observación 3.8: simple con un dominado
    assert a['simple'] and a['dominados']
    a = cb.analizar(*cb.parse_monomios('x1x3, x2x3, x1^2x4, x2^2x5, x3^2x6'))
    assert not a['simple'] and a['dominados']
    a = cb.analizar(*cb.parse_monomios('x1^2, x1x2, x2^2'))
    assert not a['simple'] and a['dominados']
    assert len(graficas(3)) == 2 and len(graficas(4)) == 6 and len(graficas(5)) == 21, 'número de gráficas conexas'
    assert len(anticadenas_par(2)) == 5 and len(anticadenas_par(3)) == 19, 'anticadenas en la rejilla'
    assert len(apretadas(4, 3)) == 51 and len(apretadas(2, 2)) == 3, 'tuplas apretadas'
    # M(2,2) a mano: una arista con una anticadena apretada, y lazos de exponente 2, que piden a = 1 o b = 1
    # (el lazo solo en x2 es isomorfo al lazo solo en x1 y no se repite)
    esperado = {((1, 1),), ((1, 2), (2, 1)), ((1, 1), (2, 0)), ((1, 1), (2, 0), (0, 2))}
    obtenido = {tuple(sorted(G)) for G in instancias_M(2, 2)}
    assert {tuple(sorted(x)) for x in esperado} == obtenido, ('M(2,2)', obtenido)
    # control negativo: la cuenta detecta una anticadena sin dominado y no simple (la de la Observación 3.18, cuyo soporte
    # no es una gráfica)
    _, simple, dom = trabajo(cb.parse_monomios('x2^2, x3^2, x1x2x3')[0])
    assert not simple and not dom, 'el control negativo no detectó la anticadena'
    print('Autotest: ejemplos conocidos; 2/6/21 gráficas conexas; 5/19 anticadenas en la rejilla; 51 tuplas apretadas; '
          'M(2,2) completa.')
    print('EXITO')


def main():
    if '--autotest' in sys.argv:
        return autotest()
    familia, n, w = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    max_aristas = int(sys.argv[sys.argv.index('--max-aristas') + 1]) if '--max-aristas' in sys.argv else None
    cont, contraejemplos, seg = correr(familia, n, w, max_aristas)
    print('%s(%d,%d)%s: %.1f s' % (familia, n, w, '' if max_aristas is None else ', a lo más %d aristas' % max_aristas, seg))
    for k in ('anticadenas', 'no simples', 'simples', 'sin generador dominado'):
        print('  %-25s %d' % (k, cont[k]))
    if contraejemplos:
        for G in contraejemplos[:10]:
            print('  sin dominado y no simple: %s' % ', '.join(cb.monomio(g) for g in G))
        print('FALLA')
        sys.exit(1)
    print('EXITO')


if __name__ == '__main__':
    main()
