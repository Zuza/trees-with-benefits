# Trees with Benefits: Lean 4 formalization

Lean 4 (`v4.27.0` / Mathlib `v4.27.0`) formal verification of the four theorems of Sections 1–5 of the paper *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion* by Arnold Filtser and Goran Zuzic: the upper bound (Theorem 1) and the three lower bounds (Theorems 2–4).

- **Specification (`250` lines):** [`Challenge.lean`](Challenge.lean) — the definitions and the four theorem statements
- **Proof (`12,108` lines, `0 sorry`):** [`Solution.lean`](Solution.lean) — standard axioms `[propext, Classical.choice, Quot.sound]` only
- **Kernel comparator spec:** [`config.json`](config.json) ([`leanprover/comparator`](https://github.com/leanprover/comparator))

## Paper ↔ Lean 4 correspondence

| Paper | Statement (`Challenge.lean`) | Main steps of the proof (`Solution.lean`) |
| :--- | :--- | :--- |
| $h$-hop distance, HST (Definition 1), stochastic hop-constrained Ramsey-type embedding (Definition 2) | `hopDist`, `HST`, `IsStochasticHCRamseyHSTEmbedding` | |
| Theorem 1 (Sections 3–4): upper bound | `thm_1_hop_constrained_ramsey_embedding` | `finite_diam_hc_ramsey_hst` (finite $h$-hop diameter), `thm1_from_finite_diam` |
| Theorem 2 (Section 5.1): hop-stretch lower bound | `thm_2_hop_stretch_lower_bound` | `thm2_from_expander` |
| Theorem 3 (Section 5.2): expected-distortion lower bound | `thm_3_expected_distortion_lower_bound` | `thm3_from_expander` |
| Theorem 4 (Section 5.3): worst-case distortion lower bound | `thm_4_worst_case_distortion_lower_bound` | `thm4_ramsey_tree_lower_bound` |

`finite_diam_hc_ramsey_hst` has the explicit parameters of the paper: hop-stretch $2k(L+1)$, worst-case distortion $8kL$, and expected distortion $2^8 L \log_2 N \cdot (1+2\delta)^{\log_2 \Phi}$, with $k$ = `hstRadiusSteps`, $L$ = `hstPhaseCount`, $\delta$ = `hstTruncDelta`. It combines `ssp_and_hse_deterministic` (deterministic properties of Algorithms 1–2, cf. Section 4.2), `hse_exclusion_prob_bound` (cf. Lemma 1), and `hse_expected_distortion_bound` (cf. Lemma 2). Theorems 2 and 3 use `exists_bounded_degree_expander`.

Notes on the statements:

- $\tilde{O}(\log n)$ in Theorem 1 is stated as $C \cdot \log_2 n \cdot (\log_2(\log_2 n + 2))^d$, with constants $C, d$ depending only on the exponent $c_0$ of the weight bound $1 \le w(e) \le n^{c_0}$.
- Distributions have finite support (`D.support.Finite`); in particular, Theorem 3 is stated for finite-support distributions.
- Sections 6–7 of the paper (applications) are not formalized.

`Solution` does not import `Challenge`: it repeats the definitions and the four statements, and the comparator checks that they agree.

## Build & verify

```bash
lake exe cache get
lake build Challenge Solution
lake env comparator config.json
```

## License

Apache License 2.0, see [`LICENSE`](LICENSE).
