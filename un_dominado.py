# -*- coding: utf-8 -*-
# un_dominado.py -- comprueba la Observación 3.26 (la reducción con un solo generador dominado) para
#   G^1_Phi = {x_u^2x_a, x_ux_{v_i}^2, x_{v_i}^2x_l (l en C_i), x_{y_j}x_{ybar_j}, x_w^2x_b, x_ux_w}:
#   A1: es una anticadena; su soporte es una gráfica simple sin lazos, con un generador por arista y exponentes <= 2.
#   A2: el único generador dominado es x_ux_w.
#   A3: I no es simple  <=>  Phi es satisfacible, también con m = 0.
#   Además: si Phi es satisfacible, el par (c, d) de la demostración son cubiertas maximales con el mismo soporte; y en todo
#   par de cubiertas maximales con el mismo soporte, c y d difieren exactamente en {u, w}.
# Las componentes se calculan con un algoritmo propio, independiente de cubiertas.py: la descomposición irreducible por
#   división I = (I + x_j^a) ∩ (I + m'), con g = x_j^a m'; las componentes irredundantes son los vectores maximales.  Se coteja
#   con los dos algoritmos de cubiertas.py donde el tamaño lo permite.
# Instancias: todas las de k = 0, 1, 2 variables y 0 <= m <= 3 cláusulas, y las de k = 3 y 0 <= m <= 2, con cláusulas que son
#   subconjuntos arbitrarios de literales (vacías, tautológicas y repetidas incluidas), en orden; más 600 instancias al azar
#   (semilla fija) con 1 <= k <= 5, 1 <= m <= 4 y cláusulas de 0 a 3 literales.
# Controles negativos: (N1) sin x_w^2x_b; (N2) con x_ux_{v_i} en vez de x_ux_{v_i}^2; (N3) un oráculo de satisfacibilidad
#   que miente en las instancias con k = 1, m = 1.  Cada uno debe romper A2 o A3 en alguna instancia.
# Uso: python3 un_dominado.py   (termina en EXITO o FALLA).
import itertools, random, time
from functools import lru_cache

import cubiertas as CB  # solo para cotejar con los algoritmos (A) y (B)

INF = CB.INF


# ------------------------------------------------------------------ construcción
def indices(k, m):
    idx = {'u': 0, 'a': 1, 'w': 2, 'b': 3}
    for i in range(m):
        idx[('v', i)] = 4 + i
    for j in range(k):
        idx[('y', j, 0)] = 4 + m + 2 * j      # y_j
        idx[('y', j, 1)] = 4 + m + 2 * j + 1  # ybar_j
    return idx, 4 + m + 2 * k


def construir(k, clausulas, variante='G1'):
    m = len(clausulas)
    idx, n = indices(k, m)

    def v(d):
        x = [0] * n
        for key, e in d:
            x[idx[key]] += e
        return tuple(x)
    G = [v([('u', 2), ('a', 1)])]
    for i, C in enumerate(clausulas):
        G.append(v([('u', 1), (('v', i), 1 if variante == 'N2' else 2)]))
        for (j, s) in C:
            G.append(v([(('v', i), 2), (('y', j, s), 1)]))
    for j in range(k):
        G.append(v([(('y', j, 0), 1), (('y', j, 1), 1)]))
    if variante != 'N1':
        G.append(v([('w', 2), ('b', 1)]))
    G.append(v([('u', 1), ('w', 1)]))
    return G, n, idx


# ------------------------------------------------------------------ definiciones
def soporte(x):
    return frozenset(i for i, a in enumerate(x) if 0 < a < INF)


def es_anticadena(G):
    if len(set(G)) != len(G):
        return False
    return not any(g != h and all(a <= b for a, b in zip(g, h)) for g in G for h in G)


def dominados(G):
    return [g for g in G if all(any(f[t] > g[t] for f in G) for t in soporte(g))]


def minimales(gens):
    gens = set(gens)
    return frozenset(g for g in gens if not any(h != g and all(a <= b for a, b in zip(h, g)) for h in gens))


@lru_cache(maxsize=None)
def irreducibles(gens):
    """Componentes irreducibles (no necesariamente irredundantes) de <x^g : g en gens>, por división."""
    for g in sorted(gens):
        s = [t for t in range(len(g)) if g[t] > 0]
        if len(s) >= 2:
            j = s[0]
            pura = tuple(g[t] if t == j else 0 for t in range(len(g)))
            resto = tuple(0 if t == j else g[t] for t in range(len(g)))
            return irreducibles(minimales(gens | {pura})) | irreducibles(minimales(gens | {resto}))
    n = len(next(iter(gens)))
    c = [INF] * n
    for g in gens:
        (t,) = [t for t in range(n) if g[t] > 0]
        c[t] = min(c[t], g[t])
    return frozenset([tuple(c)])


def cubiertas_maximales(G):
    irreducibles.cache_clear()
    C = irreducibles(minimales(G))
    return sorted(c for c in C if not any(d != c and all(a <= b for a, b in zip(c, d)) for d in C))


def es_cubierta(c, G):
    return all(any(c[j] < INF and 0 < g[j] and c[j] <= g[j] for j in range(len(c))) for g in G)


def es_maximal_def(c, G):
    """Por definición: c es cubierta y c + e_t no lo es para ningún t del soporte."""
    return es_cubierta(c, G) and all(not es_cubierta(c[:t] + (c[t] + 1,) + c[t + 1:], G) for t in soporte(c))


def pares_mismo_soporte(C):
    por = {}
    for c in C:
        por.setdefault(soporte(c), []).append(c)
    return [(c, d) for L in por.values() for c, d in itertools.combinations(L, 2)]


def satisfacible(k, clausulas):
    for t in itertools.product((False, True), repeat=k):
        if all(any(t[j] == (s == 0) for (j, s) in C) for C in clausulas):
            return True
    return False


def par_de_la_prueba(k, clausulas, idx, n):
    """El par (c, d) de la demostración de la Observación 3.26, para la primera asignación que satisface Phi."""
    for t in itertools.product((False, True), repeat=k):
        if all(any(t[j] == (s == 0) for (j, s) in C) for C in clausulas):
            c = [INF] * n
            for j in range(k):
                falso = 1 if t[j] else 0   # el literal falso: ybar_j si y_j es verdadera
                c[idx[('y', j, falso)]] = 1
            for i in range(len(clausulas)):
                c[idx[('v', i)]] = 2
            d = list(c)
            c[idx['u']], c[idx['w']] = 1, 2
            d[idx['u']], d[idx['w']] = 2, 1
            return tuple(c), tuple(d)
    return None


# ------------------------------------------------------------------ comprobación de una instancia
def literales(k):
    return [(j, s) for j in range(k) for s in (0, 1)]


def comprobar(k, clausulas, variante='G1', cotejo=False, oraculo=None):
    """Devuelve lista de fallas (vacía si A1-A3 y lo demás se cumplen)."""
    fallas = []
    G, n, idx = construir(k, clausulas, variante)
    m = len(clausulas)
    # A1
    sops = [soporte(g) for g in G]
    if not es_anticadena(G):
        fallas.append('A1: no es anticadena')
    if any(len(s) != 2 for s in sops) or len(set(sops)) != len(sops) or any(max(g) > 2 for g in G):
        fallas.append('A1: soporte/exponentes')
    # A2
    uw = tuple(1 if t in (idx['u'], idx['w']) else 0 for t in range(n))
    if dominados(G) != [uw]:
        fallas.append('A2: dominados = %s' % [CB.monomio(g) for g in dominados(G)])
    # A3
    C = cubiertas_maximales(G)
    if cotejo:
        A = CB.cubiertas_maximales(G, n)
        if sorted(A) != C:
            fallas.append('cotejo: algoritmo (A) de cubiertas.py difiere')
        if n <= 9:
            B = CB.cubiertas_maximales_fb(G, n)
            if sorted(B) != C:
                fallas.append('cotejo: algoritmo (B) difiere')
        if not all(es_maximal_def(c, G) for c in C):
            fallas.append('cotejo: una componente no es cubierta maximal por definición')
    pares = pares_mismo_soporte(C)
    sat = satisfacible(k, clausulas) if oraculo is None else oraculo(k, clausulas)
    if bool(pares) != sat:
        fallas.append('A3: no simple=%s, satisfacible=%s' % (bool(pares), sat))
    # forma de los pares: difieren exactamente en {u, w}
    for c, d in pares:
        D = {t for t in range(n) if c[t] != d[t]}
        if D != {idx['u'], idx['w']}:
            fallas.append('forma: un par difiere en %s' % sorted(D))
            break
    # el par de la prueba
    if sat and variante == 'G1' and oraculo is None:
        cd = par_de_la_prueba(k, clausulas, idx, n)
        if not (cd[0] in C and cd[1] in C and soporte(cd[0]) == soporte(cd[1]) and cd[0] != cd[1]):
            fallas.append('prueba: el par (c, d) construido no es un par de cubiertas maximales con el mismo soporte')
        if not (es_maximal_def(cd[0], G) and es_maximal_def(cd[1], G)):
            fallas.append('prueba: (c, d) no maximales por definición')
    return fallas


def instancias_exhaustivas():
    rango = [(0, m) for m in range(4)] + [(1, m) for m in range(4)] + [(2, m) for m in range(4)] + \
            [(3, m) for m in range(3)]
    for k, m in rango:
        subs = [tuple(S) for r in range(2 * k + 1) for S in itertools.combinations(literales(k), r)]
        for cl in itertools.product(subs, repeat=m):
            yield k, list(cl)


def main():
    t0 = time.time()
    ok = True
    # parte exhaustiva
    cuenta, sat_cuenta, nosimple, fallas_tot = 0, 0, 0, []
    por_km = {}
    for k, cl in instancias_exhaustivas():
        cot = (len(cl) <= 2 and k <= 2) or cuenta % 50 == 0
        f = comprobar(k, cl, cotejo=cot)
        cuenta += 1
        s = satisfacible(k, cl)
        sat_cuenta += s
        por_km.setdefault((k, len(cl)), [0, 0])
        por_km[(k, len(cl))][0] += 1
        por_km[(k, len(cl))][1] += s
        if f:
            fallas_tot.append((k, cl, f))
    print('Parte exhaustiva: %d instancias (%d satisfacibles), %.1f s' % (cuenta, sat_cuenta, time.time() - t0))
    for km in sorted(por_km):
        print('  k=%d m=%d: %d instancias, %d satisfacibles' % (km[0], km[1], *por_km[km]))
    print('  fallas: %d' % len(fallas_tot))
    for x in fallas_tot[:10]:
        print('   ', x)
    ok &= not fallas_tot
    # casos de borde nombrados
    bordes = {
        'm=1, cláusula vacía': (1, [()]),
        'k=0, m=1, cláusula vacía': (0, [()]),
        'tautológica {y, ybar}': (1, [((0, 0), (0, 1))]),
        'repetida {y},{y}': (1, [((0, 0),), ((0, 0),)]),
        'literal que no aparece (k=2, {y1})': (2, [((0, 0),)]),
        'm=1, {y}': (1, [((0, 0),)]),
        '{y},{ybar} (insatisfacible)': (1, [((0, 0),), ((0, 1),)]),
        'm=0, k=1': (1, []),
        'm=0, k=0': (0, []),
    }
    for nombre, (k, cl) in bordes.items():
        f = comprobar(k, cl, cotejo=True)
        G, n, idx = construir(k, cl)
        C = cubiertas_maximales(G)
        print('Borde %-36s sat=%-5s pares=%d  componentes=%d  fallas=%s' % (
            nombre, satisfacible(k, cl), len(pares_mismo_soporte(C)), len(C), f))
        ok &= not f
    # parte al azar
    rnd = random.Random(20261121)
    t1 = time.time()
    fallas_az, nsat = [], 0
    for _ in range(600):
        k = rnd.randint(1, 5)
        m = rnd.randint(1, 4)
        cl = [tuple(rnd.sample(literales(k), rnd.randint(0, min(3, 2 * k)))) for _ in range(m)]
        nsat += satisfacible(k, cl)
        f = comprobar(k, cl, cotejo=(_ % 20 == 0))
        if f:
            fallas_az.append((k, cl, f))
    print('Parte al azar: 600 instancias (%d satisfacibles), %.1f s, fallas: %d' % (nsat, time.time() - t1, len(fallas_az)))
    ok &= not fallas_az
    # controles negativos
    rompe = {}
    for var in ('N1', 'N2'):
        r = []
        for k, cl in instancias_exhaustivas():
            if k <= 2 and len(cl) <= 2:
                f = comprobar(k, cl, variante=var)
                if any(x.startswith('A2') or x.startswith('A3') for x in f):
                    r.append((k, cl, [x for x in f if x[:2] in ('A2', 'A3')]))
        rompe[var] = r
        a3 = sum(1 for x in r if any(y.startswith('A3') for y in x[2]))
        print('Control %s: rompe A2 o A3 en %d instancias (A3 en %d); ejemplo: %s' % (var, len(r), a3, r[0] if r else None))
    def oraculo_malo(k, cl):
        s = satisfacible(k, cl)
        return (not s) if (k == 1 and len(cl) == 1) else s
    r3 = [1 for k, cl in instancias_exhaustivas() if k == 1 and len(cl) == 1
          and any(x.startswith('A3') for x in comprobar(k, cl, oraculo=oraculo_malo))]
    print('Control N3 (oráculo corrompido): rompe A3 en %d instancias' % len(r3))
    neg_ok = bool(rompe['N1']) and bool(rompe['N2']) and bool(r3)
    print('Controles negativos detectados: %s' % neg_ok)
    ok &= neg_ok
    print('Tiempo total: %.1f s' % (time.time() - t0))
    print('EXITO' if ok else 'FALLA')


if __name__ == '__main__':
    main()
