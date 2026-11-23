# -*- coding: utf-8 -*-
# amc_algoritmos.py -- SimplePrimesAMC (2026-11-22): los dos algoritmos de la sección «Algorithms and computations» y sus cómputos.
# Afirmaciones que se comprueban (SimplePrimesAMC):
#   alg:dominating / prop:algorithm: el algoritmo por vectores dominantes (thm:main, lem:repairs (3), rem:bijection) decide la
#     simplicidad; se coteja con el cálculo de todas las cubiertas maximales (cubiertas.py, algoritmo (A)).
#   thm:forest: la programación dinámica por firmas decide la simplicidad cuando la gráfica soporte sin lazos ni aristas
#     múltiples es un bosque; implementación propia (no la de la exploración E1), cotejada con (A).
#   tab:timings: tiempos en bosques al azar: la programación dinámica, el algoritmo (A) y irreducibleDecomposition de Macaulay2.
# Clase y criterio de poda (R-20, fijado antes de calcular): cotejos en anticadenas al azar de soporte gráfica con n <= 6 y
# exponentes <= 3 (con lazos y aristas múltiples), y en bosques al azar con n <= 9; tiempos en bosques al azar con un generador
# por arista, exponentes en {1,2,3} y lazos x_v^4 en la mitad de los vértices, n en NS; un método se deja de correr en cuanto
# una instancia pasa de LIM segundos (límite real: el algoritmo (A) se interrumpe y Macaulay2 corre con timeout).  Semilla fija.
# Control negativo: el algoritmo por vectores dominantes sin la comprobación de maximalidad, y la programación dinámica sin la
# criticidad que un hijo recibe de la arista a su padre, deben fallar en alguna instancia.
# Uso: /opt/homebrew/bin/python3 -B amc_algoritmos.py [--rapido]  -> termina en «EXITO»; salida cruda en Salidas/.
import itertools, os, random, re, subprocess, sys, tempfile, time

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import cubiertas as cb
assert os.path.dirname(os.path.abspath(cb.__file__)) == AQUI
sys.setrecursionlimit(100000)
INF = cb.INF
RAPIDO = '--rapido' in sys.argv
NS = [8, 12, 16, 24, 32, 64, 128, 256, 512] if not RAPIDO else [8, 12, 16]
LIM = 60.0
lineas = []


class Agotado(Exception):
    pass


def di(s):
    print(s, flush=True)
    lineas.append(s)


def soporte(g):
    return [j for j, a in enumerate(g) if a > 0]


# ------------------------------------------------------------------------------------------ algoritmo por vectores dominantes
def critico(g, c, u):
    return g[u] == c[u] and all(g[j] < c[j] for j in range(len(c)) if j != u and c[j] < INF)


def no_simple_dominantes(G, n, sin_maximalidad=False, limite=None):
    """True si algún M domina a G (thm:main): se recorren los M con entradas finitas entre los exponentes (rem:bijection)."""
    E = [sorted({g[j] for g in G if g[j] > 0}) + [INF] for j in range(n)]
    t0 = time.time()
    for M in itertools.product(*E):
        if limite is not None and time.time() - t0 > limite:
            raise Agotado()
        H = [g for g in G if all(g[j] < M[j] for j in range(n) if M[j] < INF)]
        if not H:
            continue
        if any(len(soporte(h)) != 2 or any(M[j] == INF for j in soporte(h)) for h in H):
            continue
        ady = {}
        for h in H:
            a, b = soporte(h)
            ady.setdefault(a, set()).add(b)
            ady.setdefault(b, set()).add(a)
        lado, comps, bip = {}, [], True
        for s in ady:
            if s in lado:
                continue
            lado[s] = 0
            comp, pila = [s], [s]
            while pila:
                x = pila.pop()
                for y in ady[x]:
                    if y not in lado:
                        lado[y] = 1 - lado[x]
                        comp.append(y)
                        pila.append(y)
                    elif lado[y] == lado[x]:
                        bip = False
            comps.append(comp)
        if not bip:
            continue
        m = {j: min(h[j] for h in H if h[j] > 0) for j in ady}
        for giro in itertools.product((0, 1), repeat=len(comps) - 1):
            U = set()
            for k, comp in enumerate(comps):
                t = giro[k - 1] if k > 0 else 0
                U |= {x for x in comp if lado[x] == t}
            V = set(ady) - U
            MU = tuple(m[j] if j in U else M[j] for j in range(n))
            MV = tuple(m[j] if j in V else M[j] for j in range(n))
            if sin_maximalidad:
                return True
            if all(any(critico(g, MU, j) for g in G) for j in range(n) if M[j] < INF and j not in U) and \
               all(any(critico(g, MV, j) for g in G) for j in range(n) if M[j] < INF and j not in V):
                return True
    return False


# ------------------------------------------------------------------------------------------ programación dinámica en bosques
def no_simple_bosque(G, n, roto=False):
    """thm:forest: True si hay dos cubiertas maximales distintas con el mismo soporte; requiere que F sea un bosque."""
    lazo, arista = {}, {}
    for g in G:
        s = soporte(g)
        if len(s) == 1:
            lazo[s[0]] = g[s[0]]
        else:
            arista.setdefault(frozenset(s), []).append(g)
    ady = {v: set() for v in range(n)}
    for e in arista:
        a, b = tuple(e)
        ady[a].add(b)
        ady[b].add(a)
    E = [sorted({g[v] for g in G if g[v] > 0}) + [INF] for v in range(n)]
    orden, padre, visto = [], {}, set()
    for r in range(n):
        if r in visto:
            continue
        pila = [r]
        padre[r] = None
        visto.add(r)
        while pila:
            v = pila.pop()
            orden.append(v)
            for w in ady[v]:
                if w not in visto:
                    visto.add(w)
                    padre[w] = v
                    pila.append(w)
                elif w != padre[v]:
                    raise ValueError('el soporte no es un bosque')
    sig = {}
    for v in reversed(orden):
        A = set()
        for al in E[v]:
            for be in E[v]:
                if (al == INF) != (be == INF):
                    continue
                if v in lazo and (al > lazo[v] or be > lazo[v]):
                    continue
                A.add((al, be, al == INF or lazo.get(v) == al, be == INF or lazo.get(v) == be, al != be))
        for w in ady[v]:
            if w == padre[v]:
                continue
            gens = arista[frozenset((v, w))]
            B = set()
            for (al, be, sc, sd, de) in A:
                for (al2, be2, sc2, sd2, de2) in sig[w]:
                    if not all(al <= g[v] or al2 <= g[w] for g in gens):
                        continue
                    if not all(be <= g[v] or be2 <= g[w] for g in gens):
                        continue
                    if not roto:
                        if not (sc2 or any(g[w] == al2 and g[v] < al for g in gens)):
                            continue
                        if not (sd2 or any(g[w] == be2 and g[v] < be for g in gens)):
                            continue
                    kc = any(g[v] == al and g[w] < al2 for g in gens)
                    kd = any(g[v] == be and g[w] < be2 for g in gens)
                    B.add((al, be, sc or kc, sd or kd, de or de2))
            A = B
            del sig[w]
        sig[v] = A
        if padre[v] is None and any(sc and sd and de for (_, _, sc, sd, de) in A):
            return True
    return False


def cubiertas_con_limite(G, n, limite):
    """El algoritmo (A) de cubiertas.py, con un límite de tiempo: se detiene (Agotado) si pasa de `limite` segundos."""
    t0 = time.time()
    actuales = [tuple([INF] * n)]
    for g in G:
        simples = [tuple(g[j] if k == j else INF for k in range(n)) for j in range(n) if g[j] > 0]
        cand = {tuple(min(a, b) for a, b in zip(c, s)) for c in actuales for s in simples}
        if len(cand) > 30000:                      # la eliminación de no maximales es cuadrática: no cabe en el límite
            raise Agotado()
        actuales = cb.maximales(cand)
        if time.time() - t0 > limite:
            raise Agotado()
    return actuales


def no_simple_cubiertas(G, n, limite=None):
    C = cb.cubiertas_maximales(G, n) if limite is None else cubiertas_con_limite(G, n, limite)
    sop = [tuple(j for j in range(n) if c[j] < INF) for c in C]
    return len(set(sop)) != len(sop), len(C)


# ------------------------------------------------------------------------------------------ instancias
def antichain_grafica(rng, n, w, ngen):
    G = set()
    for _ in range(ngen):
        if rng.random() < 0.25:
            v = rng.randrange(n)
            g = [0] * n
            g[v] = rng.randint(2, w)
        else:
            a, b = rng.sample(range(n), 2)
            g = [0] * n
            g[a], g[b] = rng.randint(1, w), rng.randint(1, w)
        G.add(tuple(g))
    return cb.minimalizar(sorted(G))


def bosque(rng, n, w, multi=False, lazos=0.5, exp_lazo=None):
    G = set()
    for v in range(1, n):
        if rng.random() < 0.15 and multi:
            continue
        u = rng.randrange(v)
        for _ in range(rng.choice((1, 2)) if multi else 1):
            g = [0] * n
            g[u], g[v] = rng.randint(1, w), rng.randint(1, w)
            G.add(tuple(g))
    for v in range(n):
        if rng.random() < lazos:
            g = [0] * n
            g[v] = exp_lazo or rng.randint(2, w)
            G.add(tuple(g))
    return cb.minimalizar(sorted(G))


def m2_tiempo(G, n, limite):
    gens = ', '.join('*'.join('x_%d^%d' % (i + 1, a) for i, a in enumerate(g) if a) for g in G)
    d = tempfile.mkdtemp(dir=os.environ.get('TMPDIR'))
    f = os.path.join(d, 't.m2')
    open(f, 'w').write('R = QQ[x_1..x_%d]; I = monomialIdeal(%s);\nt0 = cpuTime(); L = irreducibleDecomposition I; t1 = cpuTime();\n'
                       'print("COMP " | toString(#L) | " T " | toString(t1-t0));\n' % (n, gens))
    try:
        r = subprocess.run([cb.M2, '--script', f], capture_output=True, text=True, timeout=limite)
    except subprocess.TimeoutExpired:
        return None, None
    m = re.search(r'COMP (\d+) T ([0-9.e-]+)', r.stdout)
    return (int(m.group(1)), float(m.group(2))) if m else (None, None)


def frobby_tiempo(G, n, limite):
    """Número de componentes y tiempo (s, de reloj) de `frobby irrdecom`; (None, None) si pasa del límite."""
    txt = 'vars %s;\n[\n%s\n];\n' % (', '.join('x%d' % (i + 1) for i in range(n)),
                                       ',\n'.join('*'.join('x%d^%d' % (i + 1, a) for i, a in enumerate(g) if a) for g in G))
    t = time.time()
    try:
        r = subprocess.run([__import__('shutil').which('frobby') or '/opt/homebrew/bin/frobby', 'irrdecom', '-oformat', 'count'], input=txt, capture_output=True,
                           text=True, timeout=limite)
    except subprocess.TimeoutExpired:
        return None, None
    dt = time.time() - t
    lin = [l for l in r.stdout.split('\n') if l.strip()]          # con -oformat count, una línea por componente
    return (len(lin), dt) if r.returncode == 0 and all(l.strip().isdigit() for l in lin) else (None, None)


def main():
    t0 = time.time()
    rng = random.Random(20261122)
    # 1. Cotejo del algoritmo por vectores dominantes con las cubiertas maximales.
    N1 = 600 if not RAPIDO else 120
    nosimples = 0
    for k in range(N1):
        n = rng.randint(2, 6)
        G = antichain_grafica(rng, n, 3, rng.randint(1, 2 * n))
        a = no_simple_dominantes(G, n)
        b, _ = no_simple_cubiertas(G, n)
        if a != b:
            di('FALLA: vectores dominantes y cubiertas difieren en %r' % (G,))
            sys.exit(1)
        nosimples += b
    di('[1] algoritmo por vectores dominantes = cubiertas maximales en %d anticadenas al azar (n <= 6, exponentes <= 3); '
       'no simples: %d' % (N1, nosimples))
    # 2. Cotejo de la programación dinámica en bosques.
    N2 = 1500 if not RAPIDO else 200
    nosimples = 0
    for k in range(N2):
        n = rng.randint(1, 9)
        G = bosque(rng, n, 3, multi=True)
        a = no_simple_bosque(G, n)
        b, _ = no_simple_cubiertas(G, n)
        if a != b:
            di('FALLA: la programación dinámica y las cubiertas difieren en %r' % (G,))
            sys.exit(1)
        nosimples += b
    di('[2] programación dinámica = cubiertas maximales en %d bosques al azar (n <= 9, exponentes <= 3, lazos y aristas '
       'múltiples); no simples: %d' % (N2, nosimples))
    # 3. Controles negativos.
    malo1 = malo2 = 0
    r2 = random.Random(7)
    for k in range(400):
        n = r2.randint(2, 6)
        G = antichain_grafica(r2, n, 3, r2.randint(1, 2 * n))
        malo1 += no_simple_dominantes(G, n, sin_maximalidad=True) != no_simple_cubiertas(G, n)[0]
        n = r2.randint(2, 9)
        G = bosque(r2, n, 3, multi=True)
        malo2 += no_simple_bosque(G, n, roto=True) != no_simple_cubiertas(G, n)[0]
    di('[3] controles negativos: sin maximalidad falla en %d de 400; sin la criticidad del hijo falla en %d de 400' % (malo1, malo2))
    if malo1 == 0 or malo2 == 0:
        di('FALLA: un control negativo no detectó nada')
        sys.exit(1)
    # 4. Tiempos en bosques al azar: R árboles por cada n; mediana de los que terminan; un método deja de correrse en cuanto
    #    una instancia pasa de LIM segundos.  Máquina y versiones, en la salida.
    R = 5 if not RAPIDO else 2
    maquina = subprocess.run(['sysctl', '-n', 'machdep.cpu.brand_string'], capture_output=True, text=True).stdout.strip()
    di('[4] tiempos (s, mediana de %d árboles al azar por n): un generador por arista, exponentes en {1,2,3}, lazo x_v^4 en la '
       'mitad de los vértices; límite %d s por instancia; %s, Python %s, Macaulay2 1.26.06, Frobby (irrdecom)'
       % (R, LIM, maquina, sys.version.split()[0]))
    di('  n | generadores | componentes | no simples | DP | vectores dominantes | cubiertas (A) | Macaulay2 (cpuTime) | Frobby')
    vivo = {'D': True, 'A': True, 'M2': True, 'F': True}
    r3 = random.Random(20261123)

    def med(xs):
        xs = sorted(xs)
        return xs[len(xs) // 2]

    for n in NS:
        filas = {k: [] for k in ('dp', 'D', 'A', 'M2', 'F')}
        corrio = dict(vivo)                       # los métodos que se intentan con este n
        gens, comps, nosimp = [], [], 0
        for _ in range(R):
            G = bosque(r3, n, 3, multi=False, lazos=0.5, exp_lazo=4)
            gens.append(len(G))
            t = time.time()
            dp = no_simple_bosque(G, n)
            filas['dp'].append(time.time() - t)
            nosimp += dp
            nc_ref = None
            if vivo['D']:
                t = time.time()
                try:
                    if no_simple_dominantes(G, n, limite=LIM) != dp:
                        di('FALLA: vectores dominantes y DP difieren en n=%d' % n)
                        sys.exit(1)
                    filas['D'].append(time.time() - t)
                except Agotado:
                    vivo['D'] = False
            if vivo['A']:
                t = time.time()
                try:
                    ns, nc = no_simple_cubiertas(G, n, LIM)
                    filas['A'].append(time.time() - t)
                    if ns != dp:
                        di('FALLA: DP y (A) difieren en n=%d' % n)
                        sys.exit(1)
                    nc_ref = nc
                except Agotado:
                    vivo['A'] = False
            if vivo['M2']:
                nc, tm = m2_tiempo(G, n, LIM)
                if nc is None or tm > LIM:
                    vivo['M2'] = False
                else:
                    filas['M2'].append(tm)
                    if nc_ref is not None and nc != nc_ref:
                        di('FALLA: Macaulay2 y (A) difieren en n=%d' % n)
                        sys.exit(1)
                    nc_ref = nc
            if vivo['F']:
                nc, tf = frobby_tiempo(G, n, LIM)
                if nc is None:
                    vivo['F'] = False
                else:
                    filas['F'].append(tf)
                    if nc_ref is not None and nc != nc_ref:
                        di('FALLA: Frobby y las demás difieren en n=%d' % n)
                        sys.exit(1)
                    nc_ref = nc
            if nc_ref is not None:
                comps.append(nc_ref)

        cel = {}
        for k in ('D', 'A', 'M2', 'F'):
            cel[k] = '%.3f' % med(filas[k]) if len(filas[k]) == R else ('> %d' % LIM if corrio[k] else '-')
        di('  %d | %d | %s | %d/%d | %.4f | %s | %s | %s | %s' % (
            n, med(gens), str(med(comps)) if len(comps) == R else '-', nosimp, R, med(filas['dp']),
            cel['D'], cel['A'], cel['M2'], cel['F']))
        for k in ('D', 'A', 'M2', 'F'):
            if len(filas[k]) < R:
                vivo[k] = False
    di('Tiempo total: %.0f s' % (time.time() - t0))
    di('EXITO')
    sal = os.path.join(AQUI, 'Salidas', '2026-11-22-amc_algoritmos%s.txt' % ('-rapido' if RAPIDO else ''))
    open(sal, 'w', encoding='utf-8').write('\n'.join(lineas) + '\n')


if __name__ == '__main__':
    main()
