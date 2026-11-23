# -*- coding: utf-8 -*-
# m2_complejidad.py -- revisión automática de SimplePrimes (2026-11-21), hallazgo F1 del lector del flujo: la introducción dice
# que todo ejemplo se comprobó con dos algoritmos independientes y con Macaulay2, y los ejemplos de la subsección de
# complejidad (ex:reduction, sus dos ideales, y ex:ass) solo habían pasado por los dos algoritmos (ejemplo.py).
# Afirmación que se comprueba: para cada uno de los tres ideales, irreducibleDecomposition de Macaulay2, el algoritmo (A)
# (cubiertas_maximales), el (B) (cubiertas_maximales_fb) y las componentes impresas en el manuscrito (MD5 7ff05a7a) coinciden;
# además, los conteos del texto: 7 componentes y simple; no simple con el par c, d; mu(m) = 3.
# Clase: tres anticadenas fijas; sin búsqueda.  Control negativo: una lista impresa alterada (sin su primera componente, y con
# un exponente cambiado) debe salir distinta de la de Macaulay2.
# Uso: TMPDIR=<temporal> /opt/homebrew/bin/python3 -B m2_complejidad.py   -> EXITO o FALLA; salida en ../Salidas/ (R-18).
import os, sys
AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import cubiertas as cb

I = cb.INF
# (nombre, generadores, n, componentes como ∞-vectores, tal como las imprime el manuscrito)
CASOS = [
    ('ex:reduction, Phi = (y) y (no y)', 'x1^2x2, x1x3, x1x4, x3^2x5, x4^2x6, x5x6', 6,
     [(1, I, 2, I, I, 1), (1, I, I, 2, 1, I), (1, I, I, I, 1, 1), (2, I, 1, 1, 1, I),
      (2, I, 1, 1, I, 1), (I, 1, 1, 1, 1, I), (I, 1, 1, 1, I, 1)]),
    ('ex:reduction, Phi = (y)', 'x1^2x2, x1x3, x3^2x5, x5x6', 6,
     [(1, I, 2, I, I, 1), (2, I, 1, I, I, 1), (1, I, I, I, 1, I), (2, I, 1, I, 1, I),
      (I, 1, 1, I, 1, I), (I, 1, 1, I, I, 1)]),
    ('ex:ass, Phi = (y1 o y2)', 'x2^2, x3^2, x4^2, x5^2, x2x3, x4x5, x1x2, x1x4', 5,
     [(1, 1, 2, 2, 1), (1, 2, 1, 1, 2), (1, 2, 1, 2, 1), (I, 1, 2, 1, 2)]),
]
L = []


def di(s):
    print(s)
    L.append(s)


def main():
    ideales = []
    for nombre, txt, n, _ in CASOS:
        G, n = cb.parse_monomios(txt, n)
        assert cb.es_anticadena(G)
        ideales.append((G, n))
    m2 = cb.m2_descomposiciones(ideales, os.environ.get('TMPDIR'))
    ok = True
    for (nombre, txt, n, impresas), (G, n), dm2 in zip(CASOS, ideales, m2):
        a = sorted(cb.cubiertas_maximales(G, n))
        b = sorted(cb.cubiertas_maximales_fb(G, n))
        imp = sorted(impresas)
        iguales = (sorted(dm2) == a == b == imp)
        sop = [cb.soporte(c) for c in a]
        simple = len(set(sop)) == len(sop)
        di('%s: G = {%s}' % (nombre, txt))
        di('  Macaulay2: %s' % ' ∩ '.join(cb.componente(c) for c in sorted(dm2)))
        di('  M2 = (A) = (B) = impresas: %s; %d componentes; simple: %s' % (iguales, len(a), simple))
        ok &= iguales
    ok &= len(m2[0]) == 7 and cb.analizar(ideales[0][0], 6)['simple']
    ok &= (not cb.analizar(ideales[1][0], 6)['simple']) and (1, I, 2, I, I, 1) in m2[1] and (2, I, 1, I, I, 1) in m2[1]
    mu = [c for c in m2[2] if len(cb.soporte(c)) == 5]
    di('ex:ass: componentes con radical m según Macaulay2: %d (el texto dice mu = 3)' % len(mu))
    ok &= len(mu) == 3
    # control negativo
    alt1 = sorted(CASOS[0][3][1:])
    alt2 = sorted([(1, 2, 1, 1, 2), (1, 2, 1, 2, 1), (I, 1, 2, 1, 2), (1, 1, 2, 2, 2)])
    neg = alt1 != sorted(m2[0]) and alt2 != sorted(m2[2])
    di('Control negativo (listas impresas alteradas difieren de Macaulay2): %s' % neg)
    di('EXITO' if ok and neg else 'FALLA')
    open(os.path.join(AQUI, 'Salidas', '2026-11-21-m2_complejidad.txt'), 'w', encoding='utf-8').write('\n'.join(L) + '\n')
    sys.exit(0 if ok and neg else 1)


if __name__ == '__main__':
    main()
