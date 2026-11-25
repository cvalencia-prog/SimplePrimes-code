# SimplePrimes-code

Code for the article *Simple associated primes of monomial ideals supported by a graph*, by O. Garcia and C. E. Valencia.

A monomial ideal $I$ is *simple* if the components of its irredundant irreducible decomposition have pairwise different radicals.
These scripts compute the maximal $\infty$-covers of an antichain of exponent vectors (that is, the irreducible components of $I$), decide simplicity, and check the examples and the computational claims of the article.

## Requirements

- Python 3.8 or later (standard library only).
- [Macaulay2](https://macaulay2.com) (`M2` in the `PATH`), for the comparisons with `irreducibleDecomposition`.
- [Frobby](https://github.com/Macaulay2/frobby) (`frobby` in the `PATH`), only for the timings of Table 2.

Run the scripts from this folder.
Each one prints its results and ends with the line `EXITO` (success) or `FALLA` (failure).
Comments and messages in the code are in Spanish.

## What each script checks

| Script | Article | How to run |
|---|---|---|
| `cubiertas.py` | Library used by the other scripts: maximal covers by two independent algorithms (incremental and exhaustive), simplicity, dominated generators, comparison with Macaulay2 | `python3 cubiertas.py --autotest` |
| `ejemplos.py` | The examples of Sections 1–4 | `python3 ejemplos.py` |
| `multiplicidad.py` | Definition 2.2, Section 2.1 and Remark 3.22 | `python3 multiplicidad.py` |
| `complejidad_ejemplos.py` | Example 3.25 and Example 3.30, with Macaulay2 | `python3 complejidad_ejemplos.py` |
| `reduccion_sat.py` | Theorem 3.24 and the second proof of Theorem 3.29, on small instances of satisfiability | `python3 reduccion_sat.py` |
| `un_dominado.py` | Remark 3.26 | `python3 un_dominado.py` |
| `independientes.py` | Lemma 3.27 | `python3 independientes.py` |
| `orientadas_pesos.py` | Section 4 (weighted oriented graphs) | `python3 orientadas_pesos.py` |
| `enumeracion.py` | Table 1 | `python3 enumeracion.py B 5 2` (family, vertices, largest exponent; `--max-aristas K` bounds the number of edges) |
| `algoritmos.py` | Proposition 5.2, Theorem 5.4 and Table 2 | `python3 algoritmos.py` (about 8 minutes; `--rapido` for a short run) |

## Authors

Omar Garcia and Carlos E. Valencia (Departamento de Matemáticas, Cinvestav-IPN, Mexico City).
