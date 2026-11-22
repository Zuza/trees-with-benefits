import Mathlib

set_option maxHeartbeats 4000000

/-!
# Trees with Benefits: statements

Lean 4 statements of the four theorems of Sections 1–5 of
*Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic
Expected Distortion* by Arnold Filtser and Goran Zuzic:

* `thm_1_hop_constrained_ramsey_embedding`: Theorem 1 (Sections 3–4);
* `thm_2_hop_stretch_lower_bound`: Theorem 2 (Section 5.1);
* `thm_3_expected_distortion_lower_bound`: Theorem 3 (Section 5.2);
* `thm_4_worst_case_distortion_lower_bound`: Theorem 4 (Section 5.3).

A graph is a `G : SimpleGraph V` on a finite vertex type `V`, with edge weights
`w : Sym2 V → ℝ`. Distances that may be infinite take values in `ENNReal`.
-/

/-- Total edge weight of a walk `p` in `G` under edge-weight function `w`. -/
noncomputable def walkWeight {V : Type} {G : SimpleGraph V} (w : Sym2 V → ℝ)
    {u v : V} (p : G.Walk u v) : ℝ :=
  (p.edges.map w).sum

/-- The `H`-hop distance `d_G^{(H)}(u, v) ∈ [0, ∞]` in a weighted graph `(G, w)`:
the infimum of total edge weight over all walks (equivalently, paths when edge weights
are non-negative) in `G` from `u` to `v` of length at most `H` hops, equal to `⊤` (`∞`)
if no walk of at most `H` edges connects `u` and `v`. -/
noncomputable def hopDist {V : Type} (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (H : ℕ) (u v : V) : ENNReal :=
  ⨅ (p : G.Walk u v) (_ : p.length ≤ H), ENNReal.ofReal (walkWeight w p)

/-- The `H`-hop distance `d_G^{(H)}(u, v) ∈ [0, ∞]` in an unweighted simple graph `G`
(unit edge weights `w(e) = 1`). -/
noncomputable def unweightedHopDist {V : Type} (G : SimpleGraph V)
    (H : ℕ) (u v : V) : ENNReal :=
  hopDist G (fun _ => 1) H u v

/-- Shortest-path distance `d_G(u, v) ∈ ℝ` in a connected unweighted simple graph `G`. -/
noncomputable def graphDist {V : Type} (G : SimpleGraph V) (u v : V) : ℝ :=
  (G.dist u v : ℝ)

/-- An extended metric `dX : X → X → [0, ∞]` satisfying zero self-distance, symmetry,
and the triangle inequality (allowing `⊤` distances between points). -/
def IsExtendedMetric {X : Type} (dX : X → X → ENNReal) : Prop :=
  (∀ x : X, dX x x = 0) ∧
  (∀ x y : X, dX x y = dX y x) ∧
  (∀ x y z : X, dX x z ≤ dX x y + dX y z)

/-- A finite weighted tree `T = (V(T), E(T), w_T)`: a finite connected acyclic simple graph
equipped with non-negative edge weights on `E(T)`. -/
structure FiniteWeightedTree where
  Node : Type
  finiteNode : Finite Node
  tree : SimpleGraph Node
  isTree : tree.IsTree
  weight : Sym2 Node → ℝ
  weight_nonneg : ∀ e ∈ tree.edgeSet, 0 ≤ weight e

/-- Induced shortest-path tree distance `d_T : V(T) × V(T) → ℝ` on a finite weighted tree. -/
noncomputable def FiniteWeightedTree.dist (T : FiniteWeightedTree) (x y : T.Node) : ℝ :=
  (⨅ p : T.tree.Walk x y, ENNReal.ofReal (walkWeight T.weight p)).toReal

/-- In a rooted tree `(T, root)`, `q` is a descendant of `z` (equivalently, `z` is an ancestor
of `q`) if `z` lies on a simple path in `T` from `root` to `q`. -/
def IsDescendant {Node : Type} (T : SimpleGraph Node) (root q z : Node) : Prop :=
  ∃ p : T.Walk root q, p.IsPath ∧ z ∈ p.support

/-- A vertex `q` of a rooted tree `(T, root)` is a leaf if it has no proper descendants. -/
def IsRootedLeaf {Node : Type} (T : SimpleGraph Node) (root q : Node) : Prop :=
  ∀ w : Node, IsDescendant T root w q → w = q

/-- In a rooted tree `(T, root)`, `z` is the least common ancestor of `x` and `y` if `z` is a
common ancestor of `x` and `y` and `z` is a descendant of every common ancestor of `x` and `y`. -/
def IsLCA {Node : Type} (T : SimpleGraph Node) (root x y z : Node) : Prop :=
  IsDescendant T root x z ∧
  IsDescendant T root y z ∧
  ∀ w : Node, IsDescendant T root x w → IsDescendant T root y w → IsDescendant T root z w

/-- The least common ancestor of `x` and `y` in a rooted tree `(T, root)`. -/
noncomputable def rootedLCA {Node : Type} (T : SimpleGraph Node) (root x y : Node) : Node :=
  haveI := Classical.propDecidable
  if h : ∃ z : Node, IsLCA T root x y z then Classical.choose h else root

/-- A Hierarchically Separated Tree (HST, Definition 1) on leaf set `V`. -/
structure HST (V : Type) where
  Node : Type
  finiteNode : Finite Node
  tree : SimpleGraph Node
  isTree : tree.IsTree
  root : Node
  leafEquiv : V ≃ {q : Node // IsRootedLeaf tree root q}
  label : Node → ENNReal
  label_mono : ∀ q z : Node, IsDescendant tree root q z → label q ≤ label z
  label_eq_zero_iff : ∀ q : Node, label q = 0 ↔ IsRootedLeaf tree root q

/-- Induced HST distance `d_U(u, v) = ℓ(lca_T(u, v)) ∈ [0, ∞]` on leaf set `V`. -/
noncomputable def HST.dist {V : Type} (U : HST V) (u v : V) : ENNReal :=
  U.label (rootedLCA U.tree U.root (U.leafEquiv u).1 (U.leafEquiv v).1)

/-- HST distance restricted to the saved set `M`: `d_{U, M}(u, v) = d_U(u, v)` when
`u ∈ M ∧ v ∈ M`, and `0` otherwise (even when `d_U(u, v) = ⊤`). -/
noncomputable def savedHSTDist {V : Type} (U : HST V) (M : Set V) (u v : V) : ENNReal :=
  haveI := Classical.propDecidable
  if u ∈ M ∧ v ∈ M then U.dist u v else 0

/-- `D` is a stochastic hop-constrained Ramsey-type embedding of `(G, w)` into HSTs
(Definition 2) with hop parameter `h`, exclusion probability `ε`, hop-stretch `β`,
worst-case distortion `K`, and expected distortion `α`. -/
def IsStochasticHCRamseyHSTEmbedding {V : Type} (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (h : ℕ) (ε : ℝ) (β : ℕ) (K α : ℝ) (D : PMF (HST V × Set V)) : Prop :=
  1 ≤ β ∧ 1 ≤ K ∧ 1 ≤ α ∧
  D.support.Finite ∧
  (∀ p ∈ D.support, ∀ u v : V, hopDist G w (β * h) u v ≤ p.1.dist u v) ∧
  (∀ p ∈ D.support, ∀ u ∈ p.2, ∀ v : V,
    p.1.dist u v ≤ ENNReal.ofReal K * hopDist G w h u v) ∧
  (∀ v : V, (D.toOuterMeasure {p | v ∉ p.2}).toReal ≤ ε) ∧
  (∀ u v : V,
    (∑' p : HST V × Set V, D p * savedHSTDist p.1 p.2 u v) ≤
      ENNReal.ofReal α * hopDist G w h u v)

/-- A sample `(T, f, M)` of a stochastic Ramsey-type tree embedding of a vertex set `V`:
a finite weighted tree `T`, a map `f : V → V(T)`, and a saved subset `M ⊆ V`. -/
structure TreeEmbeddingSample (V : Type) where
  T : FiniteWeightedTree
  f : V → T.Node
  M : Set V

/-- Tree distance restricted to the saved set `M`: `d_T(f(u), f(v))` if `u ∈ M ∧ v ∈ M`,
and `0` otherwise. -/
noncomputable def savedTreeDist {V : Type} (s : TreeEmbeddingSample V) (u v : V) : ℝ :=
  haveI := Classical.propDecidable
  if u ∈ s.M ∧ v ∈ s.M then s.T.dist (s.f u) (s.f v) else 0

/-- `D` is a stochastic Ramsey-type embedding of a finite connected unweighted simple graph `G`
into finite weighted trees with exclusion probability `ε` and expected distortion `α ≥ 0`
(Section 5.2). -/
def IsStochasticRamseyTreeEmbedding {V : Type} (G : SimpleGraph V)
    (ε α : ℝ) (D : PMF (TreeEmbeddingSample V)) : Prop :=
  0 ≤ α ∧
  D.support.Finite ∧
  (∀ s ∈ D.support, ∀ u v : V, graphDist G u v ≤ s.T.dist (s.f u) (s.f v)) ∧
  (∀ v : V, (D.toOuterMeasure {s | v ∉ s.M}).toReal ≤ ε) ∧
  (∀ u v : V,
    (∑' s : TreeEmbeddingSample V, (D s).toReal * savedTreeDist s u v) ≤
      α * graphDist G u v)

/-- `f : M → V(T)` is a dominating Ramsey-type embedding of `G` on saved set `M` into a finite
weighted tree `T` with distortion `t ≥ 1` (Section 5.3). -/
def IsDominatingRamseyTreeEmbedding {V : Type} (G : SimpleGraph V)
    (M : Set V) (T : FiniteWeightedTree) (t : ℝ) (f : M → T.Node) : Prop :=
  1 ≤ t ∧
  ∀ u v : M,
    graphDist G u.1 v.1 ≤ T.dist (f u) (f v) ∧
    T.dist (f u) (f v) ≤ t * graphDist G u.1 v.1

/-- **Theorem 1** (upper bound, Sections 3–4). For every weight exponent `c₀ ≥ 1` there are
constants `C` and `d` such that every `n`-vertex graph with edge weights in `[1, n ^ c₀]`, every
hop parameter `1 ≤ h ≤ n` and every `ε ∈ (0, 1)` admit a stochastic hop-constrained Ramsey-type
embedding into HSTs with exclusion probability `ε`, with hop-stretch `β` and worst-case
distortion `K` at most `ε⁻¹ · C · log₂ n · (log₂ (log₂ n + 2)) ^ d`, and with expected
distortion `α` at most `C · log₂ n · (log₂ (log₂ n + 2)) ^ d`. -/
theorem thm_1_hop_constrained_ramsey_embedding :
    ∀ c₀ : ℝ, 1 ≤ c₀ →
      ∃ (C : ℝ) (d : ℕ), 1 ≤ C ∧
        ∀ n : ℕ, 2 ≤ n →
          ∀ (V : Type) [Fintype V], Fintype.card V = n →
            ∀ (G : SimpleGraph V) (w : Sym2 V → ℝ),
              (∀ e ∈ G.edgeSet, 1 ≤ w e ∧ w e ≤ (n : ℝ) ^ c₀) →
              ∀ h : ℕ, 1 ≤ h → h ≤ n →
                ∀ ε : ℝ, 0 < ε → ε < 1 →
                  ∃ (β : ℕ) (K α : ℝ) (D : PMF (HST V × Set V)),
                    1 ≤ β ∧ 1 ≤ K ∧ 1 ≤ α ∧
                    IsStochasticHCRamseyHSTEmbedding G w h ε β K α D ∧
                    (β : ℝ) ≤ ε⁻¹ * C * Real.logb 2 (n : ℝ) *
                      (Real.logb 2 (Real.logb 2 (n : ℝ) + 2)) ^ d ∧
                    K ≤ ε⁻¹ * C * Real.logb 2 (n : ℝ) *
                      (Real.logb 2 (Real.logb 2 (n : ℝ) + 2)) ^ d ∧
                    α ≤ C * Real.logb 2 (n : ℝ) *
                      (Real.logb 2 (Real.logb 2 (n : ℝ) + 2)) ^ d := by
  sorry

/-- **Theorem 2** (hop-stretch lower bound, Section 5.1). There are constants `c > 0` and
`ε₀ ∈ (0, 1)` such that for every `ε ∈ (0, ε₀]` there are arbitrarily large unweighted graphs
`G` on `N` vertices, `ε · N ≥ 2`, with the following property for hop parameter `h = 1`. If a
map `f` of `G` into an extended metric space has hop-stretch `β` and finite distortion `t` on
all pairs with an endpoint in a saved set `M` that misses at most `ε · N` vertices, then
`β ≥ c · ε⁻¹ · log₂ (ε · N)`. -/
theorem thm_2_hop_stretch_lower_bound :
    ∃ (c ε₀ : ℝ), 0 < c ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ N₀ : ℕ, 1 ≤ N₀ →
          ∃ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
            letI := hV
            let N := Fintype.card V
            N₀ ≤ N ∧
            2 ≤ ε * (N : ℝ) ∧
            ∀ (X : Type) (dX : X → X → ENNReal), IsExtendedMetric dX →
              ∀ (f : V → X) (M : Set V),
                ((Set.univ \ M).ncard : ℝ) ≤ ε * (N : ℝ) →
                ∀ t : ℝ, 1 ≤ t →
                  ∀ β : ℕ, 1 ≤ β →
                    (∀ u v : V, unweightedHopDist G β u v ≤ dX (f u) (f v)) →
                    (∀ u ∈ M, ∀ v : V,
                      dX (f u) (f v) ≤ ENNReal.ofReal t * unweightedHopDist G 1 u v) →
                    c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ)) ≤ (β : ℝ) := by
  sorry

/-- **Theorem 3** (expected-distortion lower bound, Section 5.2). There are constants `c > 0`
and `ε₀ ∈ (0, 1)` such that for every `ε ∈ (0, ε₀]` there are arbitrarily large connected
unweighted graphs `G` on `n` vertices for which every stochastic Ramsey-type embedding into
finite weighted trees with exclusion probability `ε` has expected distortion
`α ≥ c · log₂ n`. -/
theorem thm_3_expected_distortion_lower_bound :
    ∃ (c ε₀ : ℝ), 0 < c ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ N₀ : ℕ, 2 ≤ N₀ →
          ∃ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
            letI := hV
            let n := Fintype.card V
            G.Connected ∧
            N₀ ≤ n ∧
            ∀ α : ℝ, 0 ≤ α →
              ∀ D : PMF (TreeEmbeddingSample V),
                IsStochasticRamseyTreeEmbedding G ε α D →
                c * Real.logb 2 (n : ℝ) ≤ α := by
  sorry

/-- **Theorem 4** (worst-case distortion lower bound, Section 5.3). There are constants `c > 0`
and `ε₀ ∈ (0, 1)` such that for every `ε ∈ (0, ε₀]` there are arbitrarily large connected
unweighted graphs `G` on `N` vertices, `ε · N ≥ 2`, for which every dominating embedding into a
finite weighted tree of a saved set `M` that misses at most `ε · N` vertices has distortion
`t ≥ c · ε⁻¹ · log₂ (ε · N)`. -/
theorem thm_4_worst_case_distortion_lower_bound :
    ∃ (c ε₀ : ℝ), 0 < c ∧ 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ N₀ : ℕ, 2 ≤ N₀ →
          ∃ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
            letI := hV
            let N := Fintype.card V
            G.Connected ∧
            N₀ ≤ N ∧
            2 ≤ ε * (N : ℝ) ∧
            ∀ M : Set V, ((Set.univ \ M).ncard : ℝ) ≤ ε * (N : ℝ) →
              ∀ (T : FiniteWeightedTree) (t : ℝ), 1 ≤ t →
                ∀ f : M → T.Node,
                  IsDominatingRamseyTreeEmbedding G M T t f →
                  c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ)) ≤ t := by
  sorry
