# EK-LogConcave-Chromatic

[![Lean build](https://github.com/sajadcosmos/EK-LogConcave-Chromatic./actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/sajadcosmos/EK-LogConcave-Chromatic./actions/workflows/lean_action_ci.yml)

Lean 4 formal verification and computational scripts accompanying the article

> **Sajad A. Sheikh**, *Log-concavity meets Eneström–Kakeya: inner radii for the roots of chromatic and matroid characteristic polynomials.*
> Department of Mathematics, University of Kashmir, South Campus, Anantnag, 192101, Jammu and Kashmir, India.

## About the mathematics

The Eneström–Kakeya theorem confines the zeros of a polynomial with positive coefficients to an annulus whose radii are the extreme ratios of consecutive coefficients. For **log-concave** coefficients these radii are the first and the last ratio, and the annulus is **rigid**: no zero lies on its boundary unless the coefficients are geometric.

By the theorem of Adiprasito, Huh and Katz this applies to the characteristic polynomial `χ_M` of every matroid. Its inner radius is `1/h(M)`, where `h(M) = w_{r-1}/w_r` is the ratio of the last two Whitney numbers of the first kind, and `1 ≤ h(M) ≤ r`. Consequences:

* every root of `χ_M` satisfies `|λ| > 1/h(M) ≥ 1/r`;
* every root `λ ≠ 1` satisfies `|λ| > 1/(r_i − 1)`, where `r_i` is the rank of a connected component;
* every nonzero chromatic root of a graph with `n` vertices and `c` components satisfies `|q| > 1/(n − c)`;
* every chromatic root outside `{0, 1}` satisfies `|q| > 1/(β − 2)`, where `β` is the order of the largest 2-connected block;
* for the cycle `C_n` the smallest nonzero chromatic root has modulus exactly `2 sin(π/(n − 1))`, so the order `1/n` is optimal.

## Repository layout

| Path | Contents |
|------|----------|
| `EKLogConcave.lean` | The complete formal development (single file, ~990 lines, 60 theorems and lemmas, namespace `EKLC`). |
| `Check.lean` | Prints the axioms used by every main theorem (`#print axioms`). |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Lake project pinned to Lean `v4.34.1` and Mathlib `v4.34.1`. |
| `computations/` | Python scripts for the exhaustive computations and figures of the article. |
| `.github/workflows/` | Continuous integration: builds the project and prints the axioms. |

## What is verified

The formalisation checks the arguments of the article, not the classical theory on which they rest. Mathlib contains matroids but not their lattices of flats, Whitney numbers, Tutte activities or the Hodge theory of Adiprasito–Huh–Katz. The development therefore works with coefficient sequences, and the classical inputs enter the statements as **explicit hypotheses**:

* positivity of the Whitney numbers (Rota) and of the reduced coefficients;
* their log-concavity (Adiprasito–Huh–Katz), recorded by the structure `PosLC a N`;
* `w₀ = 1`, the root `χ_M(1) = 0`, and the identities linking `χ_M` with its reduced polynomial;
* the activity data (Tutte–Crapo), the sizes of rank-two flats, and supersolvable exponents (Stanley).

Everything else is proved from Mathlib, with no `sorry` and only Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`.

| Statement in the article | Lean theorem(s) |
|---|---|
| Lemma 2.1 (monotone ratios) | `ratio_mono`, `geometric_of_first_eq_last` |
| Theorem 3.1 (rigid ratio annulus) | `ek_core`, `ek_core_strict`, `rigid_outer`, `rigid_inner`, `rigid_annulus` |
| Corollary 3.2 (dominance) | `sum_inv_roots`, `dominance_inv`, `dominance_sum` |
| Proposition 4.2(a),(d) | `sum_inv_roots`, `L_mul`, `hpoly_mul` |
| Proposition 4.4, Lemma 2.2 (mediant) | `h_mediant`, `mediant`, `mediant_lt_max` |
| Lemma 4.5 (non-geometricity) | `nongeom_core`, `nongeom_rev` |
| Theorem 4.6 (`1 ≤ h ≤ r`) | `h_bounds_activity`, `h_gt_one` |
| Theorem 4.8 (inner radius of `χ_M`) | `mainA`, `mainA_rank` |
| Theorem 4.9 (reduced polynomial) | `mainB`, `mainB_rank_two`, `reduced_radius`, `reduced_rank_bound` |
| Example 4.11 (uniform matroids, projective geometries) | `alt_partial_sum`, `uniform_h`, `pg_bound` |
| Proposition 5.1(a),(b),(e) | `sum_inv_roots`, `hpoly_mul`, `hpoly_glue` |
| Proposition 5.3 (cycles, chordal graphs, edge gluing) | `cycle_coeffs`, `chordal_bounds`, `glue_half` |
| Theorem 5.6 (cycles) | `cycle_factor`, `one_sub_root_of_unity`, `cycle_roots`, `cycle_roots_attained`, `two_sin_lt_one_iff`, `cycle_ratio_tendsto` |
| Theorems 5.2, 5.4 and the flow / arrangement corollaries | instances of `mainA`, `mainA_rank`, `mainB`, `reduced_rank_bound` |
| Proposition 6.2 (supersolvable matroids) | `supersolvable_bound` |
| Uniform and projective cases of Conjecture 6.1 | `uniform_conj`, `pg_bound` |
| Proposition 6.3 (reduced broken-circuit complex) | `ridge_average` |

## Building

Install [elan](https://github.com/leanprover/elan), then:

```bash
git clone https://github.com/sajadcosmos/EK-LogConcave-Chromatic..git
cd EK-LogConcave-Chromatic.
lake exe cache get        # download the compiled Mathlib cache
lake build                # build EKLogConcave
lake env lean Check.lean  # print the axioms of the main theorems
```

The build completes without errors or warnings. Every line printed by `Check.lean` has the form

```
'EKLC.rigid_annulus' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Computations

The scripts in `computations/` reproduce the numerical evidence of Section 6 of the article (Python 3; `pip install -r computations/requirements.txt`):

| Script | Purpose |
|---|---|
| `gen_graphs.py` | All connected graphs on at most 8 vertices (graph atlas + extension with isomorph rejection via `pynauty`); writes `graphs.pkl`. |
| `chrom.py` | Exact chromatic polynomials by a subset dynamic programme over independent-set partitions. |
| `analyze.py` | Roots, `h(G)` and block data for all 12 111 graphs; writes `rows.json` (included). |
| `check.py` | Verifies the bounds and tests the conjectures on `rows.json`. |
| `more.py`, `sp.py` | The class of graphs glued from cycles along edges; edge-addition and 2-sum experiments. |
| `flows.py` | Cographic (flow-polynomial) test of Conjecture 6.1. |
| `bc.py` | Ridge statistics of the reduced broken-circuit complex. |
| `theta2.py` | Search over generalised theta graphs (writes `theta_best.json`, included). |
| `figs.py`, then `figs2.py` | Figures, written to `computations/figures/`. |

Run them from inside `computations/` in the order `gen_graphs.py`, `analyze.py`, then the others.

## Citation

If you use this code, please cite the article above and this repository; see `CITATION.cff`.

## License

Released under the MIT License (see `LICENSE`).
