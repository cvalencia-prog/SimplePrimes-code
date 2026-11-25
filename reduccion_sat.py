# -*- coding: utf-8 -*-
# reduccion_sat.py -- comprueba en instancias chicas de satisfacibilidad las dos reducciones de la sección 3.5.
#   (A) Teorema 3.24: para una instancia Phi con variables y_1..y_k y cláusulas C_1..C_m (m >= 1), la anticadena G_Phi de la
#       Definición 3.23,  { x_u^2 x_a,  x_u x_{v_i},  x_{v_i}^2 x_l (l en C_i),  x_y x_{no y} },  NO es simple  <=>  Phi es
#       satisfacible.  También con el lazo x_u^2 en lugar de x_u^2 x_a, como dice la demostración.
#   (B) Teorema 3.29, segunda demostración: para la anticadena G'_Phi de la Definición 3.28,
#       { x_l^2 (l literal),  x_y x_{no y},  x_{v_i} x_l (l en C_i) },  el número de cubiertas maximales de soporte total
#       (= mu de <todas las variables>) es el número de asignaciones que satisfacen Phi (m >= 0).
#   El caso m = 0 de (A), excluido por el Teorema 3.24: G_Phi es simple aunque Phi sea satisfacible.
# Instancias: a lo más 4 variables y 5 cláusulas.
#   R1: k=1, todas las colecciones de 1..3 cláusulas distintas entre los 4 subconjuntos de literales (incluida la vacía);
#   R2: k=2, todas las colecciones de 1..3 cláusulas distintas entre los 16 subconjuntos de literales;
#   R3: k=3, todas las colecciones de 1..2 cláusulas distintas entre los 64 subconjuntos de literales;
#   R4: NAZAR instancias al azar (semilla fija) con k en {3,4}, m en {3,4,5}, cláusulas de 1 a 3 literales.
# La simplicidad se calcula con los dos algoritmos de cubiertas.py; el (B) se omite solo si el producto de candidatos pasa de
# TOPE_B (se dice cuántas veces).  La satisfacibilidad, por fuerza bruta sobre las 2^k asignaciones.
# Controles negativos: (N1) sin el generador x_u^2 x_a la equivalencia (A) debe fallar en alguna instancia satisfacible;
# (N2) sin las aristas x_y x_{no y} debe fallar en alguna instancia insatisfacible; (N3) en (B), sin los lazos, debe fallar.
# Uso: python3 reduccion_sat.py [NAZAR]   (por omisión, NAZAR = 150; termina en EXITO o FALLA).
import itertools, random, sys, time
import cubiertas as cb

NAZAR = int(sys.argv[1]) if len(sys.argv) > 1 else 150
TOPE_B = 400000
INICIO = time.time()


def di(s):
    print(s)


def satisfacen(k, clausulas):
    """Número de asignaciones de las k variables que satisfacen todas las cláusulas; literal = (j, signo)."""
    return sum(1 for t in itertools.product((False, True), repeat=k)
               if all(any(t[j] == s for j, s in c) for c in clausulas))


def anticadena_A(k, clausulas, variante='hoja', sin_u2=False, sin_pares=False):
    """G_Phi.  Vértices: u=0, a=1, v_i=2+i, literal (j,True)=2+m+2j, (j,False)=2+m+2j+1."""
    m = len(clausulas)
    n = 2 + m + 2 * k
    lit = lambda j, s: 2 + m + 2 * j + (0 if s else 1)

    def mon(d):
        v = [0] * n
        for i, e in d.items():
            v[i] = e
        return tuple(v)
    G = []
    if not sin_u2:
        G.append(mon({0: 2, 1: 1}) if variante == 'hoja' else mon({0: 2}))
    for i, c in enumerate(clausulas):
        G.append(mon({0: 1, 2 + i: 1}))
        for j, s in c:
            G.append(mon({2 + i: 2, lit(j, s): 1}))
    if not sin_pares:
        for j in range(k):
            G.append(mon({lit(j, True): 1, lit(j, False): 1}))
    assert cb.es_anticadena(G), G
    assert all(len([e for e in g if e]) <= 2 and max(g) <= 2 for g in G)
    return G, n


def anticadena_B(k, clausulas, sin_lazos=False):
    """G'_Phi.  Vértices: v_i=i, literal (j,True)=m+2j, (j,False)=m+2j+1."""
    m = len(clausulas)
    n = m + 2 * k
    lit = lambda j, s: m + 2 * j + (0 if s else 1)

    def mon(d):
        v = [0] * n
        for i, e in d.items():
            v[i] = e
        return tuple(v)
    G = []
    for j in range(k):
        if not sin_lazos:
            G += [mon({lit(j, True): 2}), mon({lit(j, False): 2})]
        G.append(mon({lit(j, True): 1, lit(j, False): 1}))
    for i, c in enumerate(clausulas):
        for j, s in c:
            G.append(mon({i: 1, lit(j, s): 1}))
    assert cb.es_anticadena(G), G
    return G, n


cuenta_B_omitido = 0


def maximales_dos(G, n):
    """Cubiertas maximales con los dos algoritmos; se exige que coincidan."""
    global cuenta_B_omitido
    C = cb.cubiertas_maximales(G, n)
    prod = 1
    for j in range(n):
        prod *= len({g[j] for g in G if g[j] > 0}) + 1
    if prod <= TOPE_B:
        C2 = cb.cubiertas_maximales_fb(G, n)
        if sorted(C) != sorted(C2):
            di('FALLA: los dos algoritmos de cubiertas.py difieren en %r' % (G,))
            sys.exit(1)
    else:
        cuenta_B_omitido += 1
    return C


def simple(C):
    sop = [cb.soporte(c) for c in C]
    return len(set(sop)) == len(sop)


def instancias():
    for k, mmax in ((1, 3), (2, 3), (3, 2)):
        lits = [(j, s) for j in range(k) for s in (True, False)]
        todas = [frozenset(c) for r in range(len(lits) + 1) for c in itertools.combinations(lits, r)]
        for m in range(1, mmax + 1):
            for col in itertools.combinations(todas, m):
                yield 'R%d' % k, k, list(col)
    rnd = random.Random(20261121)
    for _ in range(NAZAR):
        k = rnd.choice((3, 4))
        m = rnd.choice((3, 4, 5))
        lits = [(j, s) for j in range(k) for s in (True, False)]
        col = [frozenset(rnd.sample(lits, rnd.choice((1, 1, 2, 2, 3)))) for _ in range(m)]
        yield 'R4', k, col


res = {}
neg1 = neg2 = neg3 = 0
for rango, k, col in instancias():
    ns = satisfacen(k, col)
    sat = ns > 0
    r = res.setdefault(rango, [0, 0, 0])   # instancias, satisfacibles, max n
    r[0] += 1
    r[1] += sat
    for variante in ('hoja', 'lazo'):
        G, n = anticadena_A(k, col, variante)
        r[2] = max(r[2], n)
        C = maximales_dos(G, n)
        if (not simple(C)) != sat:
            di('FALLA (A, %s): k=%d cláusulas=%r sat=%s simple=%s' % (variante, k, col, sat, simple(C)))
            di('FALLA')
            sys.exit(1)
    Gb, nb = anticadena_B(k, col)
    Cb = maximales_dos(Gb, nb)
    mu = sum(1 for c in Cb if len(cb.soporte(c)) == nb)
    if mu != ns:
        di('FALLA (B): k=%d cláusulas=%r #SAT=%d mu=%d' % (k, col, ns, mu))
        di('FALLA')
        sys.exit(1)
    if rango != 'R4':   # controles negativos solo en lo exhaustivo (baratos)
        G1, n1 = anticadena_A(k, col, 'hoja', sin_u2=True)
        neg1 += (not simple(cb.cubiertas_maximales(G1, n1))) != sat
        G2, n2 = anticadena_A(k, col, 'hoja', sin_pares=True)
        neg2 += (not simple(cb.cubiertas_maximales(G2, n2))) != sat
        G3, n3 = anticadena_B(k, col, sin_lazos=True)
        neg3 += sum(1 for c in cb.cubiertas_maximales(G3, n3) if len(cb.soporte(c)) == n3) != ns

# caso m = 0: Phi sin cláusulas es satisfacible y G_Phi es simple (por eso el Teorema 3.24 pide m >= 1); en (B), mu = 2^k.
for k in (1, 2, 3):
    G, n = anticadena_A(k, [], 'hoja')
    assert simple(maximales_dos(G, n)), 'm = 0: G_Phi debía ser simple'
    Gb, nb = anticadena_B(k, [])
    assert sum(1 for c in maximales_dos(Gb, nb) if len(cb.soporte(c)) == nb) == 2 ** k
di('m = 0 (k = 1, 2, 3): G_Phi es simple aunque Phi sin cláusulas es satisfacible; en (B), mu = 2^k.')

for rango in sorted(res):
    di('%s: %d instancias (%d satisfacibles, %d no), n <= %d: (A) no simple <=> satisfacible, variantes hoja y lazo; '
       '(B) mu(m) = #SAT.' % (rango, res[rango][0], res[rango][1], res[rango][0] - res[rango][1], res[rango][2]))
di('Algoritmo (B) omitido por tamaño en %d anticadenas (TOPE_B=%d); en las demás A y B coinciden.'
   % (cuenta_B_omitido, TOPE_B))
di('Controles negativos (R1-R3): N1 sin x_u^2x_a falla en %d; N2 sin x_yx_{no y} falla en %d; N3 (B) sin lazos falla en %d.'
   % (neg1, neg2, neg3))
di('Tiempo: %.1f s' % (time.time() - INICIO))
ok = neg1 > 0 and neg2 > 0 and neg3 > 0
di('EXITO' if ok else 'FALLA')
sys.exit(0 if ok else 1)
