# -*- coding: utf-8 -*-
# enumeracion.py -- T1.3 (2026-11-19): enumeración exhaustiva de anticadenas de soporte gráfica, como evidencia para el
# explorador de T2 (no prueba nada).  Usa cubiertas.py.
# Familias:
#   B(n,w): subfamilia de cómputo «gráfica simple con un generador por arista»: gráfica simple conexa con n vértices, un
#           generador x_p^a x_q^b por arista, exponentes 1..w (la letra B es heredada; el marco es el de soporte gráfica, D5).
#   M(n,w): soporte gráfica general: por cada par {p,q} de una gráfica conexa con n vértices, una anticadena no vacía de
#           generadores x_p^a x_q^b con 1 ≤ a,b ≤ w (aristas múltiples), y en un subconjunto de vértices un lazo x_p^e,
#           2 ≤ e ≤ w (e = 1 haría redundantes las aristas de p); se exige que el total sea una anticadena (a < e en cada arista
#           de un vértice con lazo).
# CRITERIO DE PODA (R-20), nombrado antes de lanzar:
#   (P1) Gráficas conexas y sin vértices aislados, una por clase de isomorfismo (con su conjunto de lazos).  Justificación: las
#        cubiertas maximales de una unión disjunta de soportes son las concatenaciones de las de cada parte, así que I_G es simple
#        si y solo si cada componente lo es; un generador dominado lo es dentro de su componente; y un par de cubiertas maximales
#        con el mismo soporte que difiere en k coordenadas da, restringido a la componente donde difieren, otro par (si difieren
#        en dos componentes, cada restricción difiere en un solo lado y serían comparables).  Así (a), (b), (c) se deciden por
#        componentes.
#   (P2) Exponentes «apretados» por vértice: en cada coordenada j, los exponentes positivos que aparecen forman {1,...,k}.
#        Justificación: cubierta, maximalidad, soporte y dominación solo dependen de las comparaciones entre exponentes de una
#        misma coordenada (las cubiertas maximales tienen sus entradas entre esos exponentes); un cambio monótono de los valores
#        de cada coordenada da una biyección entre cubiertas maximales que conserva soportes y coordenadas en que difieren
#        (es la invariancia por signatura de Ibarguen-Moran-Valencia-Villarreal).
#   No se quitan las simetrías de los pesos dentro de una misma gráfica: hay repeticiones, que no cambian las conclusiones.
# Qué se mide en cada anticadena (cubiertas.analizar):
#   (a) contraejemplos a «sin generador dominado ⇒ simple»;
#   (b) contraejemplos a «generador dominado ⇒ no simple» (la dirección falsa del primer `main`), con los minimales;
#   (c) H1: «no simple ⇔ hay dos cubiertas maximales con el mismo soporte que difieren en exactamente dos coordenadas»;
#   H3: si c, d son maximales con el mismo soporte y difieren solo en p, q (c_p < d_p, d_q < c_q), entonces x_p^{c_p} x_q^{d_q} ∈ G;
#   E: en una anticadena no simple, ¿todo generador dominado es «efectivo» (crítico de c en u ∈ {c < d} para algún par)?
#   y la distribución de (|U|, |V|) en el par de cada anticadena no simple que difiere en menos coordenadas.
# Uso: /opt/homebrew/bin/python3 -B enumeracion.py FAMILIA N W [--max-aristas K] [--salida ARCHIVO]
#      /opt/homebrew/bin/python3 -B enumeracion.py --autotest
# Termina en «EXITO» (con control negativo: una anticadena conocida de cada tipo debe caer donde debe).
import collections, itertools, multiprocessing, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
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


def resumen_una(G):
    n = len(G[0])
    a = cb.analizar(G, n)
    assert len(a['G']) == len(G), 'no es anticadena'
    r = {'simple': a['simple'], 'dom': bool(a['dominados']), 'H1': a['H1'], 'H3': True, 'E': True, 'UV': None, 'kmin': None}
    if a['pares']:
        kmin = min(len(D) for _, _, D in a['pares'])
        r['kmin'] = kmin
        c, d, D = min(a['pares'], key=lambda t: len(t[2]))
        U = sum(1 for i in D if c[i] < d[i])
        r['UV'] = tuple(sorted((U, len(D) - U)))
        for c, d, D in a['pares']:
            if len(D) == 2:
                p, q = sorted(D)
                if c[p] > d[p]:
                    c, d = d, c
                g = [0] * n
                g[p], g[q] = c[p], d[q]
                if tuple(g) not in a['G']:
                    r['H3'] = False
        r['E'] = set(a['dominados']) <= set(a['efectivos'])
    return r


def clave(G):
    n = len(G[0])
    usados = sum(1 for j in range(n) if any(g[j] for g in G))
    return (len(G), usados, sum(map(sum, G)), max(max(g) for g in G))


def canon_G(G):
    n = len(G[0])
    return min(tuple(sorted(tuple(g[p[j]] for j in range(n)) for g in G)) for p in itertools.permutations(range(n)))


def trabajo(G):
    return G, resumen_una(G)


def correr(familia, n, w, max_aristas=None, procesos=None):
    gen = instancias_B(n, w, max_aristas) if familia == 'B' else instancias_M(n, w, max_aristas)
    cont = collections.Counter()
    ejemplos = collections.defaultdict(dict)        # tipo -> canon -> G (los de clave mínima se eligen al final)
    t0 = time.time()
    with multiprocessing.Pool(procesos) as pool:
        for G, r in pool.imap_unordered(trabajo, gen, chunksize=500):
            cont['total'] += 1
            cont['no simple' if not r['simple'] else 'simple'] += 1
            cont['con dominado'] += r['dom']
            tipos = []
            if r['simple'] and not r['dom']:
                pass
            if not r['simple'] and not r['dom']:
                tipos.append('a: no simple sin dominado')
            if r['simple'] and r['dom']:
                tipos.append('b: simple con dominado')
            if not r['H1']:
                tipos.append('c: H1 falla')
            if not r['H3']:
                tipos.append('H3 falla')
            if not r['simple'] and not r['E']:
                tipos.append('E: dominado no efectivo en no simple')
            if not r['simple']:
                cont['kmin=%d' % r['kmin']] += 1
                cont['(|U|,|V|)=%s' % (r['UV'],)] += 1
            for t in tipos:
                cont[t] += 1
                k = clave(G)
                d = ejemplos[t]
                if len(d) < 400 or k < max(d.values(), key=lambda x: x[0])[0]:
                    d[canon_G(G)] = (k, G)
                    if len(d) > 400:
                        del d[max(d, key=lambda x: d[x][0])]
    return cont, ejemplos, time.time() - t0


def informe(familia, n, w, max_aristas, cont, ejemplos, segundos):
    out = ['# enumeracion.py %s n=%d w=%d%s (2026-11-19)' % (familia, n, w, '' if max_aristas is None else ' max-aristas=%d' % max_aristas),
           'Alcance: %s con exactamente %d vértices (todos usados), pesos/exponentes 1..%d, poda P1 (conexa, por isomorfismo) y '
           'P2 (exponentes apretados por vértice)%s; %.1f s.' % (
               'gráficas simples con un generador por arista' if familia == 'B' else 'anticadenas de soporte gráfica con aristas múltiples y lazos',
               n, w, '' if max_aristas is None else ', a lo más %d pares con generadores' % max_aristas, segundos), '']
    for k in sorted(cont):
        out.append('%-45s %d' % (k, cont[k]))
    for t in sorted(ejemplos):
        L = sorted(ejemplos[t].values())
        out += ['', '## %s: %d clases distintas guardadas; las 12 menores (generadores, vértices, grado total, exponente máx.):' % (t, len(L))]
        for k, G in L[:12]:
            a = cb.analizar(G, len(G[0]))
            out.append('  %s   | %s | pares: %s' % (
                ', '.join(cb.monomio(g) for g in G), ' ∩ '.join(cb.componente(c) for c in a['cubiertas']),
                '; '.join('%s/%s' % (cb.vec(c), cb.vec(d)) for c, d, _ in a['pares']) or '—'))
    return '\n'.join(out) + '\n'


def autotest():
    # control negativo: anticadenas conocidas caen en su tipo
    r = resumen_una(cb.parse_monomios('x1x2, x1x3, x2^2x3, x1^2x4')[0])
    assert r['simple'] and r['dom'], 'el contraejemplo al primer main no salió como «b»'
    r = resumen_una(cb.parse_monomios('x1x3, x2x3, x1^2x4, x2^2x5, x3^2x6')[0])
    assert not r['simple'] and not r['H1'] and r['kmin'] == 3, 'C-19 no salió como fallo de H1'
    r = resumen_una(cb.parse_monomios('x1^2, x1x2, x2^2')[0])
    assert not r['simple'] and r['H1'] and r['H3'], 'ejemplo-1'
    # la enumeración pequeña es completa: B(3,2) y M(2,2) a mano
    assert len(graficas(3)) == 2 and len(graficas(4)) == 6 and len(graficas(5)) == 21, 'número de gráficas conexas'
    assert len(anticadenas_par(2)) == 5 and len(anticadenas_par(3)) == 19, 'anticadenas en la rejilla'
    assert len(apretadas(4, 3)) == 51 and len(apretadas(2, 2)) == 3, 'tuplas apretadas'
    M22 = list(instancias_M(2, 2))
    # n=2, w=2: un par con anticadena no vacía apretada, y lazos con exponente 2 que exigen a=1 o b=1
    # (el lazo en x2 solo es isomorfo al lazo en x1 y no se repite)
    esperado = {((1, 1),), ((1, 2), (2, 1)), ((1, 1), (2, 0)), ((1, 1), (2, 0), (0, 2))}
    obtenido = {tuple(sorted(G)) for G in M22}
    assert {tuple(sorted(x)) for x in esperado} == obtenido, ('M(2,2)', obtenido)
    print('Autotest: tipos de los ejemplos conocidos, 2/6/21 gráficas conexas, 5/19 anticadenas en la rejilla, '
          '51 tuplas apretadas, M(2,2) contiene sus casos.')
    print('EXITO')


def main():
    if '--autotest' in sys.argv:
        return autotest()
    familia, n, w = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    max_aristas = int(sys.argv[sys.argv.index('--max-aristas') + 1]) if '--max-aristas' in sys.argv else None
    salida = sys.argv[sys.argv.index('--salida') + 1] if '--salida' in sys.argv else None
    cont, ejemplos, seg = correr(familia, n, w, max_aristas)
    texto = informe(familia, n, w, max_aristas, cont, ejemplos, seg)
    if salida:
        open(salida, 'w', encoding='utf-8').write(texto)
    print(texto)
    if cont['a: no simple sin dominado']:
        print('AVISO: hay contraejemplos a «sin dominado ⇒ simple»')
    print('EXITO')


if __name__ == '__main__':
    main()
