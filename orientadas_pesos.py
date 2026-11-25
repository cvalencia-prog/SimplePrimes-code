# -*- coding: utf-8 -*-
# orientadas_pesos.py -- comprueba los enunciados de la sección 4 sobre las gráficas orientadas con pesos.
# D = (V, E, w), E ⊆ V×V sin aristas en los dos sentidos, w: V -> N_{>0} con w(x) = 1 si x es una fuente;
# I(D) = <x_i x_j^{w(x_j)} : (x_i, x_j) ∈ E>.
#   (a) Corolario 4.1: toda I(D) es de soporte gráfica, sin generador dominado y simple.
#   (b) Teorema 4.2: C ↦ c(C) (c_i = 1 en L1(C), w(x_i) en L2(C) ∪ L3(C), ∞ fuera de C) lleva las cubiertas fuertes
#       de D a las cubiertas maximales de I(D).
#   (d) Observación 4.5: en I(D) cada variable tiene a lo más dos exponentes positivos, 1 (colas) y w (cabezas); la versión
#       apretada de I(D) (los exponentes positivos de cada variable -> 1, 2, ...) es otra I(D') con los mismos arcos y pesos
#       en {1, 2}, y coincide con la signatura salvo cuando una variable divide a todos los generadores.
#   (c) Observación 4.6: ideales de soporte gráfica simples que no son I(D) para ninguna D, ni siquiera después de un cambio
#       monótono de los exponentes de cada variable (Lema 4.4), clasificados por la razón: lazos, aristas múltiples,
#       un generador dominado, un generador sin el exponente mínimo de ninguno de sus dos vértices, o un vértice con tres
#       exponentes distintos.
# Instancias: para (a), (b) y (d), las gráficas subyacentes conexas con 2 a N vértices (una por clase de isomorfismo), todas
# las orientaciones y pesos 1..3; para (c), las anticadenas de enumeracion.py en B(4,3), M(3,3) y M(4,2).
# Controles negativos: (b) con una regla de cubierta fuerte alterada (sin la condición w(y) ≠ 1) debe fallar; un ideal con
# lazo no debe reconocerse como I(D).
# Uso: python3 orientadas_pesos.py [--n-max N]   (por omisión, N = 5; termina en EXITO o FALLA).
import collections, itertools, multiprocessing, sys
import cubiertas as cb
import enumeracion as en

INF = cb.INF


def ideal_D(n, arcos, w):
    G = []
    for i, j in arcos:
        g = [0] * n
        g[i], g[j] = 1, w[j]
        G.append(tuple(g))
    return G


def cubiertas_fuertes(n, arcos, w, exigir_peso=True):
    """Vectores c(C) de las cubiertas fuertes de D (sección 4)."""
    sal = collections.defaultdict(set)
    ent = collections.defaultdict(set)
    for i, j in arcos:
        sal[i].add(j)
        ent[j].add(i)
    res = set()
    for k in range(1, n + 1):
        for C in itertools.combinations(range(n), k):
            C = set(C)
            if not all(i in C or j in C for i, j in arcos):
                continue
            L1 = {x for x in C if sal[x] - C}
            L2 = {x for x in C if x not in L1 and ent[x] - C}
            L3 = C - L1 - L2
            if all(any(y in L2 | L3 and (w[y] != 1 or not exigir_peso) for y in ent[x]) for x in L3):
                res.add(tuple(1 if i in L1 else (w[i] if i in C else INF) for i in range(n)))
    return sorted(res)


def instancias(n_max, w_max=3):
    for n in range(2, n_max + 1):
        for E in en.graficas(n):
            for sentidos in itertools.product((0, 1), repeat=len(E)):
                arcos = [(a, b) if s == 0 else (b, a) for (a, b), s in zip(E, sentidos)]
                cabezas = sorted({j for _, j in arcos})
                for pesos in itertools.product(range(1, w_max + 1), repeat=len(cabezas)):
                    w = [1] * n
                    for j, p in zip(cabezas, pesos):
                        w[j] = p
                    yield n, arcos, tuple(w)


def apretar(G):
    n = len(G[0])
    pos = [{e: k + 1 for k, e in enumerate(sorted({g[j] for g in G if g[j]}))} for j in range(n)]
    return sorted(tuple(pos[j][g[j]] if g[j] else 0 for j in range(n)) for g in G)


def signatura(G):
    """La signatura: en cada variable, cada exponente -> su posición entre los distintos (el menor, también el 0, -> 0)."""
    n = len(G[0])
    pos = [{e: k for k, e in enumerate(sorted({g[j] for g in G}))} for j in range(n)]
    return sorted(tuple(pos[j][g[j]] for j in range(n)) for g in G)


def revisar(args):
    n, arcos, w = args
    G = ideal_D(n, arcos, w)
    a = cb.analizar(G, n)
    fuertes = cubiertas_fuertes(n, arcos, w)
    A = apretar(G)
    reduce_ok = es_ID(A, n) and max(map(max, A)) <= 2
    estrella = any(all(g[j] for g in G) for j in range(n))
    sigma_ok = estrella or signatura(G) == A
    return {
        'reduce': reduce_ok, 'sigma': sigma_ok, 'estrella': estrella,
        'grafica': a['soporte_grafica'] and len(a['G']) == len(G),
        'sin_dominado': not a['dominados'], 'simple': a['simple'],
        'b': fuertes == a['cubiertas'],
    }


# ------------------------------------------------------------------------------------------------ (c) reconocer I(D)
def es_ID(G, n):
    """¿Hay D con I(D) = <x^G>?  Sin lazos, un generador por par, y una orientación con exponente 1 en la cola y el mismo
    exponente en todas las llegadas a cada vértice."""
    pares = collections.Counter()
    for g in G:
        s = [i for i in range(n) if g[i]]
        if len(s) != 2:
            return False
        pares[tuple(s)] += 1
    if max(pares.values()) > 1:
        return False
    gens = [tuple(i for i in range(n) if g[i]) + (g,) for g in G]
    peso = {}

    def bt(k):
        if k == len(gens):
            return True
        p, q, g = gens[k]
        for cola, cabeza in ((p, q), (q, p)):
            if g[cola] != 1:
                continue
            previo = peso.get(cabeza)
            if previo is None or previo == g[cabeza]:
                peso[cabeza] = g[cabeza]
                if bt(k + 1):
                    return True
                if previo is None:
                    del peso[cabeza]
        return False
    return bt(0)


def es_ID_hasta_signatura(G, n):
    """¿Algún cambio monótono de los exponentes de cada variable lleva G a un I(D)?  Basta probar, para cada vértice, que sus
    exponentes {e} vayan a {1} o {2}, y {e1 < e2} a {1, 2}; con tres o más exponentes distintos no hay D."""
    vals = [sorted({g[j] for g in G if g[j]}) for j in range(n)]
    if any(len(v) > 2 for v in vals):
        return False
    opciones = []
    for v in vals:
        if len(v) == 0:
            opciones.append([{}])
        elif len(v) == 1:
            opciones.append([{v[0]: 1}, {v[0]: 2}])
        else:
            opciones.append([{v[0]: 1, v[1]: 2}])
    for elec in itertools.product(*opciones):
        H = [tuple(elec[j][g[j]] if g[j] else 0 for j in range(n)) for g in G]
        if es_ID(H, n):
            return True
    return False


def razones(G, n, a):
    r = []
    sop = [frozenset(i for i in range(n) if g[i]) for g in G]
    if any(len(s) == 1 for s in sop):
        r.append('lazo')
    if len(set(s for s in sop if len(s) == 2)) < sum(1 for s in sop if len(s) == 2):
        r.append('arista múltiple')
    if a['dominados']:
        r.append('generador dominado')
    mins = [min((g[j] for g in G if g[j]), default=0) for j in range(n)]
    if any(len(s) == 2 and all(g[i] > mins[i] for i in s) for g, s in zip(G, sop)):
        r.append('generador sin exponente mínimo en sus dos vértices')
    if any(len({g[j] for g in G if g[j]}) > 2 for j in range(n)):
        r.append('vértice con tres exponentes distintos')
    return r or ['otra (orientación imposible)']


def parte_c():
    por_razon = collections.defaultdict(list)
    cont = collections.Counter()
    for f, n, w in (('B', 4, 3), ('M', 3, 3), ('M', 4, 2)):
        gen = en.instancias_B(n, w) if f == 'B' else en.instancias_M(n, w)
        for G in gen:
            a = cb.analizar(G, n)
            if not a['simple']:
                continue
            cont['%s(%d,%d) simples' % (f, n, w)] += 1
            assert es_ID_hasta_signatura(G, n) == es_ID(apretar(G), n), ('(d) en (c)', G)
            if es_ID_hasta_signatura(G, n):
                cont['%s(%d,%d) simples que son I(D) salvo signatura' % (f, n, w)] += 1
                continue
            cont['%s(%d,%d) simples que no son I(D) salvo signatura' % (f, n, w)] += 1
            for r in razones(G, n, a):
                por_razon[r].append((en.clave(G), G))
    return cont, por_razon


def autotest():
    # el ideal de la Observación 3.8 es simple, tiene un dominado y no es I(D) de ninguna D
    G, n = cb.parse_monomios('x1x2, x1x3, x2^2x3, x1^2x4')
    assert not es_ID_hasta_signatura(G, n)
    # una I(D): x1x2^2, x2x3^5, con arcos (1,2), (2,3) y pesos w2 = 2, w3 = 5
    G, n = cb.parse_monomios('x1x2^2, x2x3^5')
    assert es_ID(G, n)
    assert cubiertas_fuertes(3, [(0, 1), (1, 2)], (1, 2, 5)) == cb.cubiertas_maximales(G, n)
    # controles negativos
    assert not es_ID(cb.parse_monomios('x1^2, x1x2')[0], 2), 'un lazo no es I(D)'
    malo = cubiertas_fuertes(3, [(0, 1), (1, 2)], (1, 1, 1), exigir_peso=False)
    assert malo != cb.cubiertas_maximales(ideal_D(3, [(0, 1), (1, 2)], (1, 1, 1)), 3), 'sin w(y) ≠ 1 debe fallar (b)'
    # (d) en un ejemplo: x1x2^3, x2x3^3, x3x4 (pesos 3, 3, 1) se aprieta a x1x2^2, x2x3^2, x3x4 (pesos 2, 2, 1), que es su signatura;
    # en la estrella x1x2^3, x2x3^3 (x2 divide a los dos) la signatura manda x2 a exponente 0 y difiere; un lazo no se vuelve I(D)
    P = cb.parse_monomios('x1x2^3, x2x3^3, x3x4')[0]
    assert apretar(P) == signatura(P) == sorted(cb.parse_monomios('x1x2^2, x2x3^2, x3x4')[0]) and es_ID(apretar(P), 4)
    E = cb.parse_monomios('x1x2^3, x2x3^3')[0]
    assert apretar(E) == sorted(cb.parse_monomios('x1x2^2, x2x3')[0]) and signatura(E) != apretar(E)
    assert not es_ID(apretar(cb.parse_monomios('x1^3, x1x2')[0]), 2)
    print('Autotest: reconocimiento de I(D), correspondencia en un ejemplo, controles negativos.')


def main():
    n_max = int(sys.argv[sys.argv.index('--n-max') + 1]) if '--n-max' in sys.argv else 5
    autotest()
    cont = collections.Counter()
    malos = collections.defaultdict(list)
    with multiprocessing.Pool() as pool:
        for r in pool.imap_unordered(revisar, instancias(n_max), chunksize=200):
            cont['total'] += 1
            cont['estrella'] += r['estrella']
            for k in ('grafica', 'sin_dominado', 'simple', 'b', 'reduce', 'sigma'):
                if not r[k]:
                    malos[k].append(r)
    print('(a), (b): %d gráficas orientadas con pesos (conexas, 2..%d vértices, todas las orientaciones, pesos 1..3, '
          'fuentes con peso 1).' % (cont['total'], n_max))
    for k, nombre in (('grafica', 'no es anticadena de soporte gráfica'), ('sin_dominado', 'tiene generador dominado'),
                      ('simple', 'no es simple'), ('b', 'cubiertas fuertes ≠ cubiertas maximales')):
        print('  %-45s %d' % (nombre, len(malos[k])))
    print('  (d) la versión apretada de I(D) no es una I(D\') con pesos en {1, 2}: %d' % len(malos['reduce']))
    print('  (d) signatura ≠ versión apretada, sin variable que divida a todos los generadores: %d (estrellas, excluidas: %d)' % (
        len(malos['sigma']), cont['estrella']))
    c, por_razon = parte_c()
    print('\n(c) Ideales de soporte gráfica simples que no son I(D) de ninguna gráfica orientada con pesos, ni después de cambiar '
          'monótonamente los exponentes de cada variable:')
    for k in sorted(c):
        print('  %-55s %d' % (k, c[k]))
    muestra = []
    for r in sorted(por_razon):
        L = sorted(por_razon[r])
        print('  -- %s: %d; los 4 menores:' % (r, len(L)))
        for _, G in L[:4]:
            n = len(G[0])
            a = cb.analizar(G, n)
            muestra.append((G, n))
            print('     %s   | %s' % (', '.join(cb.monomio(g) for g in G), ' ∩ '.join(cb.componente(x) for x in a['cubiertas'])))
    m2 = cb.m2_descomposiciones(muestra)
    dif = sum(1 for (G, n), d in zip(muestra, m2) if d != cb.cubiertas_maximales(G, n))
    print('  Los %d ejemplos listados, cotejados con Macaulay2: %d diferencias.' % (len(muestra), dif))
    if any(malos[k] for k in ('grafica', 'sin_dominado', 'simple', 'b', 'reduce', 'sigma')) or dif:
        print('FALLA')
        sys.exit(1)
    print('EXITO')


if __name__ == '__main__':
    main()
