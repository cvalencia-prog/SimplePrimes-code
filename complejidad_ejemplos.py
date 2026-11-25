# -*- coding: utf-8 -*-
# complejidad_ejemplos.py -- comprueba con Macaulay2 los ejemplos de la sección 3.5: los dos ideales del
# Ejemplo 3.25 y el del Ejemplo 3.30.
# Para cada uno, irreducibleDecomposition de Macaulay2, los algoritmos (A) y (B) de cubiertas.py y las componentes impresas en
# el artículo coinciden; además, las cifras del texto: 7 componentes y simple; no simple con el par c, d; mu(m) = 3.
# Control negativo: una lista impresa alterada (sin su primera componente, o con un exponente cambiado) debe salir distinta de
# la de Macaulay2.
# Uso: python3 complejidad_ejemplos.py   (termina en EXITO o FALLA).
import sys
import cubiertas as cb

I = cb.INF
# (nombre, generadores, n, componentes como ∞-vectores, tal como las imprime el artículo)
CASOS = [
    ('Ejemplo 3.25, Phi = (y) y (no y)', 'x1^2x2, x1x3, x1x4, x3^2x5, x4^2x6, x5x6', 6,
     [(1, I, 2, I, I, 1), (1, I, I, 2, 1, I), (1, I, I, I, 1, 1), (2, I, 1, 1, 1, I),
      (2, I, 1, 1, I, 1), (I, 1, 1, 1, 1, I), (I, 1, 1, 1, I, 1)]),
    ('Ejemplo 3.25, Phi = (y)', 'x1^2x2, x1x3, x3^2x5, x5x6', 6,
     [(1, I, 2, I, I, 1), (2, I, 1, I, I, 1), (1, I, I, I, 1, I), (2, I, 1, I, 1, I),
      (I, 1, 1, I, 1, I), (I, 1, 1, I, I, 1)]),
    ('Ejemplo 3.30, Phi = (y1 o y2)', 'x2^2, x3^2, x4^2, x5^2, x2x3, x4x5, x1x2, x1x4', 5,
     [(1, 1, 2, 2, 1), (1, 2, 1, 1, 2), (1, 2, 1, 2, 1), (I, 1, 2, 1, 2)]),
]

def di(s):
    print(s)


def main():
    ideales = []
    for nombre, txt, n, _ in CASOS:
        G, n = cb.parse_monomios(txt, n)
        assert cb.es_anticadena(G)
        ideales.append((G, n))
    m2 = cb.m2_descomposiciones(ideales)
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
    di('Ejemplo 3.30: componentes con radical m según Macaulay2: %d (el texto dice mu = 3)' % len(mu))
    ok &= len(mu) == 3
    # control negativo
    alt1 = sorted(CASOS[0][3][1:])
    alt2 = sorted([(1, 2, 1, 1, 2), (1, 2, 1, 2, 1), (I, 1, 2, 1, 2), (1, 1, 2, 2, 2)])
    neg = alt1 != sorted(m2[0]) and alt2 != sorted(m2[2])
    di('Control negativo (listas impresas alteradas difieren de Macaulay2): %s' % neg)
    di('EXITO' if ok and neg else 'FALLA')
    sys.exit(0 if ok and neg else 1)


if __name__ == '__main__':
    main()
