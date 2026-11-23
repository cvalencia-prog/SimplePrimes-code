# -*- coding: utf-8 -*-
# t3_multiplicidad.py -- SimplePrimes, T3 y T4 (a) (2026-11-21): comprueba lo que afirman def:simple, rem:multiplicity y
# rem:complexity.
#   (1) Las cifras de rem:multiplicity y de la introducción: para <x1^2,x1x2,x2^2> y p=<x1,x2>, longitud 3 y mu=2; para
#       <x1^2,x2>, longitud 2 y mu=1.
#   (2) mu_G(p) (número de cubiertas maximales con soporte T, p=<x_j : j en T>) es la dimensión del zócalo de (S/I_G)_p, el
#       número de Bass mu_0(p,S/I_G); y es 0 exactamente cuando p no es asociado.  El zócalo se calcula sin cubiertas:
#       localizar en p es poner x_j=1 fuera de T; el zócalo de la localización es (J:m)/J para el ideal monomial J así obtenido
#       en k[x_T], con base los monomios w fuera de J con x_i w en J para todo i en T, y w_i < (mayor exponente de x_i en J).
#   (3) rem:complexity: el criterio de dominado en O(n|G|) (máximo de cada columna) coincide con la definición
#       (cubiertas.dominados), y el certificado de no simple (dos cubiertas maximales con el mismo soporte, comprobadas con
#       lem:key) existe exactamente cuando I_G no es simple.
# Criterio de poda (R-20): anticadenas al azar con n <= 4 variables, exponentes <= 3 y hasta 6 generadores, sin la hipótesis de
# gráfica (rem:multiplicity y la parte NP de rem:complexity valen para toda anticadena), más las de soporte gráfica de la misma
# caja; semilla fija.  Controles negativos: la longitud no es mu en el ejemplo (1); un zócalo que olvida una variable falla en
# algún caso; un criterio de dominado con «>=» falla en algún caso.
# Uso: TMPDIR=<temporal> /opt/homebrew/bin/python3 -B t3_multiplicidad.py [N] [semilla]   (termina en EXITO o FALLA)
import itertools, os, random, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cubiertas as cb
assert os.path.dirname(os.path.abspath(cb.__file__)) == os.path.dirname(os.path.abspath(__file__)), 'cubiertas.py equivocado'
INF = cb.INF


def falla(msg):
    print('FALLA: ' + msg)
    sys.exit(1)


def restringir(G, T):
    """Generadores del ideal J de k[x_T] que se obtiene poniendo x_j=1 fuera de T (la localización en p_T)."""
    return cb.minimalizar([tuple(g[j] for j in T) for g in G])


def en(w, J):
    return any(all(a <= b for a, b in zip(h, w)) for h in J)


def zocalo(G, T, olvida=None):
    J = restringir(G, T)
    if any(sum(h) == 0 for h in J):              # J = (1): p no contiene a I_G
        return 0
    tope = [max(h[i] for h in J) for i in range(len(T))]
    var = [i for i in range(len(T)) if i != olvida]
    cuenta = 0
    for w in itertools.product(*[range(t) for t in tope]):
        if en(w, J):
            continue
        if all(en(w[:i] + (w[i] + 1,) + w[i + 1:], J) for i in var):
            cuenta += 1
    return cuenta


def longitud_m_primario(G):
    """Longitud de S/I para I m-primario: número de monomios estándar."""
    tope = [max(g[i] for g in G) for i in range(len(G[0]))]
    return sum(1 for w in itertools.product(*[range(t) for t in tope]) if not en(w, G))


def mu(C, T):
    return sum(1 for c in C if set(i for i, a in enumerate(c) if a < INF) == set(T))


def dominados_rapido(G, n, estricto=True):
    mx = [max(g[j] for g in G) for j in range(n)]
    return sorted(g for g in G if all((g[u] < mx[u]) if estricto else (g[u] <= mx[u]) for u in range(n) if g[u] > 0))


def es_maximal_por_lem_key(c, G):
    if not cb.es_cubierta(c, G):
        return False
    return all(any(g[u] == c[u] and all(g[v] < c[v] for v in range(len(c)) if v != u and c[v] < INF) for g in G)
               for u in range(len(c)) if c[u] < INF)


def anticadena_al_azar(rnd, n, e, k, grafica):
    G = []
    for _ in range(k):
        s = rnd.sample(range(n), rnd.randint(1, 2 if grafica else n))
        G.append(tuple(rnd.randint(1, e) if j in s else 0 for j in range(n)))
    return cb.minimalizar(G)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    semilla = int(sys.argv[2]) if len(sys.argv) > 2 else 20261121
    rnd = random.Random(semilla)
    # (1) las cifras
    G1, G2 = [(2, 0), (1, 1), (0, 2)], [(2, 0), (0, 1)]
    for G, lon, m in ((G1, 3, 2), (G2, 2, 1)):
        C = cb.cubiertas_maximales(G, 2)
        if (longitud_m_primario(G), mu(C, (0, 1)), zocalo(G, (0, 1))) != (lon, m, m):
            falla('cifras de %s: longitud %d, mu %d, zócalo %d' % (G, longitud_m_primario(G), mu(C, (0, 1)), zocalo(G, (0, 1))))
    if longitud_m_primario(G1) == mu(cb.cubiertas_maximales(G1, 2), (0, 1)):
        falla('control negativo: la longitud coincide con mu en el ejemplo')
    print('(1) <x1^2,x1x2,x2^2>: longitud 3, mu 2; <x1^2,x2>: longitud 2, mu 1 (y el zócalo da mu).')
    # (2) y (3)
    casos = primos = asociados = neg_zocalo = neg_dom = no_simples = 0
    for k in range(N):
        n = rnd.randint(2, 4)
        G = anticadena_al_azar(rnd, n, 3, rnd.randint(1, 6), grafica=(k % 2 == 0))
        C = cb.cubiertas_maximales(G, n)
        if C != cb.cubiertas_maximales_fb(G, n):
            falla('los dos algoritmos de cubiertas no coinciden en %s' % G)
        casos += 1
        for r in range(1, n + 1):
            for T in itertools.combinations(range(n), r):
                primos += 1
                z, m = zocalo(G, T), mu(C, T)
                if z != m:
                    falla('zócalo %d != mu %d en G=%s, T=%s' % (z, m, G, T))
                asociados += m > 0
                if m > 0 and zocalo(G, T, olvida=0) != m:
                    neg_zocalo += 1
        if dominados_rapido(G, n) != sorted(cb.dominados(G)):
            falla('criterio de dominado O(n|G|) != definición en %s' % G)
        if dominados_rapido(G, n, estricto=False) != sorted(cb.dominados(G)):
            neg_dom += 1
        if not all(es_maximal_por_lem_key(c, G) for c in C):
            falla('lem:key no reconoce una cubierta maximal en %s' % G)
        cert = [(c, d) for c, d in itertools.combinations(C, 2) if cb.soporte(c) == cb.soporte(d)]
        simple = len({cb.soporte(c) for c in C}) == len(C)
        if bool(cert) == simple:
            falla('el certificado no corresponde a la simplicidad en %s' % G)
        no_simples += not simple
    if neg_zocalo == 0 or neg_dom == 0:
        falla('los controles negativos no detectaron nada (zócalo %d, dominado %d)' % (neg_zocalo, neg_dom))
    print('(2) %d anticadenas (la mitad de soporte gráfica), %d primos monomiales, %d asociados: zócalo = mu en todos.' % (casos, primos, asociados))
    print('(3) dominado en O(n|G|) = definición; certificado de no simple <-> no simple (%d no simples).' % no_simples)
    print('Controles negativos: zócalo sin x_1 falla en %d primos; dominado con «<=» falla en %d anticadenas.' % (neg_zocalo, neg_dom))
    print('EXITO')


if __name__ == '__main__':
    main()
