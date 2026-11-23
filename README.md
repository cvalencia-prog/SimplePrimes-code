# SimplePrimes-code

Code for the article *Simple associated primes of monomial ideals supported by a graph*, by O. Garcia and C. E. Valencia.

A monomial ideal $I$ is *simple* if the components of its irredundant irreducible decomposition have pairwise different radicals.
These scripts compute the maximal $\infty$-covers of an antichain of exponent vectors (that is, the irreducible components of $I$), decide simplicity, and check every example and every computational claim of the article.

## Requirements

- Python 3.8 or later (standard library only).
- [Macaulay2](https://macaulay2.com) (`M2` in the `PATH`), for the comparisons with `irreducibleDecomposition`.
- [Frobby](https://github.com/Macaulay2/frobby) (`frobby` in the `PATH`), only for the timings of Section 5.

Every script ends with the line `EXITO` (success) or `FALLA` (failure), and writes its raw output to `Salidas/`.
Comments in the code are in Spanish.

## What each script checks

| Script | Article | How to run |
|---|---|---|
| `cubiertas.py` | Library: maximal covers by two independent algorithms (incremental and exhaustive), simplicity, dominated generators, comparison with Macaulay2 | `python3 cubiertas.py --autotest` |
| `t4_ejemplos.py` (uses `t2_ejemplos.py`, `t2_caracterizacion.py`) | Every decomposition and claim in the examples of Sections 2–4 | `python3 t4_ejemplos.py` |
| `m2_complejidad.py` | The examples of the complexity section, with Macaulay2 | `python3 m2_complejidad.py` |
| `red_sat.py` | Theorem 3.24 and the second proof of Theorem 3.29 (reductions from satisfiability) on random instances | `python3 red_sat.py 120` |
| `v4_un_dominado.py` | Remark 3.26 (a single dominated generator) | `python3 v4_un_dominado.py` |
| `v5_lem_mis.py` | Lemma 3.27 (maximal covers and maximal independent sets) | `python3 v5_lem_mis.py` |
| `t3_multiplicidad.py` | Definition 2.2 and Remark 2.3 (multiplicity) | `python3 t3_multiplicidad.py` |
| `orientadas_pesos.py` | Section 4 (weighted oriented graphs) | `python3 orientadas_pesos.py` |
| `enumeracion.py` | Table 1 (exhaustive enumeration) | `python3 enumeracion.py B 5 2` (family, vertices, largest exponent) |
| `amc_algoritmos.py` | Section 5: Proposition 5.2 and Theorem 5.4 against the maximal covers, with negative controls, and Table 2 (timings) | `python3 amc_algoritmos.py` (about 8 minutes; `--rapido` for a short run) |

The numbering of statements is that of the version submitted to *Applied Mathematics and Computation*.

## Authors

Omar Garcia and Carlos E. Valencia (Departamento de Matemáticas, Cinvestav-IPN, Mexico City).
