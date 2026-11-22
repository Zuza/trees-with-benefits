import Mathlib

set_option maxHeartbeats 4000000

/-!
# Trees with Benefits: proofs

Lean 4 proofs of the four theorems of Sections 1–5 of
*Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic
Expected Distortion* by Arnold Filtser and Goran Zuzic.

The definitions up to `IsDominatingRamseyTreeEmbedding` and the four theorems at the end of the
file (`thm_1_hop_constrained_ramsey_embedding`,
`thm_2_hop_stretch_lower_bound`, `thm_3_expected_distortion_lower_bound`,
`thm_4_worst_case_distortion_lower_bound`) are those of `Challenge.lean`.
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

/-- Theorem 1 (Sections 3–4, Upper Bound). -/
def Theorem1 : Prop :=
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
                    (Real.logb 2 (Real.logb 2 (n : ℝ) + 2)) ^ d

/-- Theorem 2 (Section 5.1, Hop-Stretch Lower Bound). -/
def Theorem2 : Prop :=
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
                  c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ)) ≤ (β : ℝ)

/-- Theorem 3 (Section 5.2, Expected Distortion Lower Bound). -/
def Theorem3 : Prop :=
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
              c * Real.logb 2 (n : ℝ) ≤ α

/-- Theorem 4 (Section 5.3, Ramsey Tree Distortion Lower Bound). -/
def Theorem4 : Prop :=
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
                c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ)) ≤ t
noncomputable def hstPhaseCount (N : ℕ) : ℕ :=
  Nat.ceil (Real.logb 2 (Real.logb 2 ((N : ℝ) + 1)))


noncomputable def hstTruncDelta (N : ℕ) : ℝ :=
  ((Real.logb 2 ((N : ℝ) + 1)) ^ 2)⁻¹


noncomputable def hstRadiusSteps (N : ℕ) (Φ ε : ℝ) : ℕ :=
  let δ := hstTruncDelta N
  Nat.ceil ((4 / ε) * (1 + 2 * δ) ^ (Real.logb 2 Φ) *
    (Real.log (N : ℝ) + Real.log (2 / δ) * Real.logb 2 Φ))


def IsBoundedDegreeEdgeExpander {n : ℕ} (G : SimpleGraph (Fin n)) (D : ℕ) (φ : ℝ) : Prop :=
  (∀ v : Fin n, (G.neighborSet v).ncard ≤ D) ∧
  (∀ S : Set (Fin n), 2 * S.ncard ≤ n →
    φ * (S.ncard : ℝ) ≤
      ({p : Fin n × Fin n | p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2}.ncard : ℝ))
noncomputable def hstMu (N ℓ : ℕ) : ℕ :=
  2 ^ (2 ^ (hstPhaseCount N - ℓ))

noncomputable def hstGeomP (N : ℕ) (Φ ε : ℝ) (ℓ : ℕ) : ℝ :=
  (2 / (hstRadiusSteps N Φ ε : ℝ)) * Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N)

noncomputable def hstRadius (N : ℕ) (Δ : ℝ) : ℕ → ℝ
  | 0 => Δ / (2 : ℝ) ^ (hstPhaseCount N + 4)
  | ℓ + 1 =>
    hstRadius N Δ ℓ +
      Δ / (2 : ℝ) ^ ((hstPhaseCount N - (ℓ + 1)) + 4) +
      Δ / (8 * (hstPhaseCount N : ℝ))

noncomputable def hstStep (N : ℕ) (Φ ε Δ : ℝ) (ℓ : ℕ) : ℝ :=
  (hstRadius N Δ ℓ - hstRadius N Δ (ℓ - 1)) / (hstRadiusSteps N Φ ε : ℝ)

noncomputable def hstDepth (Φ : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 Φ) + 1

def phaseDesc : ℕ → List ℕ
  | 0 => []
  | m + 1 => (m + 1) :: phaseDesc m

noncomputable def sspSlotPhases (N : ℕ) : List ℕ :=
  (phaseDesc (hstPhaseCount N)).flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ)

noncomputable def hstTotalSlots (N : ℕ) : ℕ :=
  (sspSlotPhases N).length

noncomputable def hstBall {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (N h : ℕ) (Φ ε Δ : ℝ) (X : Finset (Fin n)) (v : Fin n) (ℓ : ℕ) (R : ℤ) : Finset (Fin n) :=
  haveI := Classical.propDecidable
  if (hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R < 0 ∨
      hstRadius N Δ (ℓ - 1) + (R : ℝ) * hstStep N Φ ε Δ ℓ < 0 then
    ∅
  else
    X.filter (fun u =>
      hopDist G w (((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R).toNat * h) v u ≤
        ENNReal.ofReal (hstRadius N Δ (ℓ - 1) + (R : ℝ) * hstStep N Φ ε Δ ℓ))

noncomputable def sspCands {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (N h : ℕ) (Φ ε Δ : ℝ) (m_init : ℕ) (X_cur : Finset (Fin n)) (ℓ : ℕ) : Finset (Fin n) :=
  haveI := Classical.propDecidable
  X_cur.filter (fun x =>
    (m_init : ℝ) / (hstMu N (ℓ - 1) : ℝ) ≤
      ((hstBall G w N h Φ ε Δ X_cur x ℓ 0).card : ℝ) ∧
    ((hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) ≤
      (m_init : ℝ) / (hstMu N ℓ : ℝ))

noncomputable def sspRunSteps {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (N h : ℕ) (Φ ε Δ : ℝ) (m_init : ℕ) (X_cur M_cur : Finset (Fin n)) :
    List (ℕ × ℕ) → List (ℕ × Finset (Fin n) × Finset (Fin n)) × Finset (Fin n) × Finset (Fin n)
  | [] => ([], X_cur, M_cur)
  | (ℓ, R) :: rest =>
    let cands := sspCands G w N h Φ ε Δ m_init X_cur ℓ
    if hc : cands.Nonempty then
      let x := cands.min' hc
      let Xj := hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ)
      let Mj := hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur
      let M_next := M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1)
      let res := sspRunSteps G w N h Φ ε Δ m_init (X_cur \ Xj) M_next rest
      ((ℓ, Xj, Mj) :: res.1, res.2.1, res.2.2)
    else
      sspRunSteps G w N h Φ ε Δ m_init X_cur M_cur rest

abbrev FinTape (N : ℕ) (Φ ε : ℝ) : Type :=
  Fin (hstTotalSlots N) → Fin (hstRadiusSteps N Φ ε)

noncomputable def sspTaggedClusters {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (N h : ℕ) (Φ ε : ℝ) (X M : Finset (Fin n)) (Δ : ℝ) (τ : FinTape N Φ ε) :
    List (ℕ × Finset (Fin n) × Finset (Fin n)) :=
  let steps := List.ofFn (fun i : Fin (hstTotalSlots N) => ((sspSlotPhases N).get i, (τ i).1))
  let res := sspRunSteps G w N h Φ ε Δ X.card X M steps
  if res.2.1.Nonempty then res.1 ++ [(0, res.2.1, res.2.2)] else res.1

noncomputable def sspClusters {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (N h : ℕ) (Φ ε : ℝ) (X M : Finset (Fin n)) (Δ : ℝ) (τ : FinTape N Φ ε) :
    List (Finset (Fin n) × Finset (Fin n)) :=
  (sspTaggedClusters G w N h Φ ε X M Δ τ).map (fun t => (t.2.1, t.2.2))

inductive RawHST (W : Type) : Type
  | leaf (X : Finset W) : RawHST W
  | node (X : Finset W) (Δ : ℝ) (children : List (RawHST W)) : RawHST W

def RawHST.cluster {W : Type} : RawHST W → Finset W
  | RawHST.leaf X => X
  | RawHST.node X _ _ => X

def RawHST.topLabel {W : Type} : RawHST W → ℝ
  | RawHST.leaf _ => 0
  | RawHST.node _ Δ _ => Δ

def RawHST.dist {W : Type} [DecidableEq W] (t : RawHST W) (u v : W) : ℝ :=
  match t with
  | RawHST.leaf _ => 0
  | RawHST.node _ Δ children =>
    if u = v then 0 else go Δ children
where
  go (Δ : ℝ) : List (RawHST W) → ℝ
    | [] => Δ
    | c :: cs =>
      if u ∈ c.cluster ∧ v ∈ c.cluster then RawHST.dist c u v else go Δ cs

def ValidRawHST {W : Type} [DecidableEq W] : RawHST W → Prop
  | RawHST.leaf X => X.card = 1
  | RawHST.node X Δ children =>
    0 < Δ ∧
    children ≠ [] ∧
    go children ∧
    (∀ c ∈ children, c.topLabel ≤ Δ ∧ c.cluster.Nonempty) ∧
    (children.map RawHST.cluster).Pairwise Disjoint ∧
    children.foldr (fun c acc => c.cluster ∪ acc) ∅ = X
where
  go : List (RawHST W) → Prop
    | [] => True
    | c :: cs => ValidRawHST c ∧ go cs

def TreeTape (N : ℕ) (Φ ε : ℝ) : ℕ → Type
  | 0 => PUnit
  | d + 1 => FinTape N Φ ε × (Fin N → TreeTape N Φ ε d)

noncomputable instance instFintypeTreeTape (N : ℕ) (Φ ε : ℝ) :
    ∀ d : ℕ, Fintype (TreeTape N Φ ε d)
  | 0 => PUnit.fintype
  | d + 1 =>
    letI := instFintypeTreeTape N Φ ε d
    instFintypeProd (FinTape N Φ ε) (Fin N → TreeTape N Φ ε d)

noncomputable def truncGeomWeight (N : ℕ) (Φ ε : ℝ) (ℓ R : ℕ) : ℝ :=
  (1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ /
    (1 - (1 - hstGeomP N Φ ε ℓ) ^ hstRadiusSteps N Φ ε)

noncomputable def finTapeProb (N : ℕ) (Φ ε : ℝ) (τ : FinTape N Φ ε) : ℝ :=
  ∏ i : Fin (hstTotalSlots N), truncGeomWeight N Φ ε ((sspSlotPhases N).get i) (τ i).1

noncomputable def treeTapeProb (N : ℕ) (Φ ε : ℝ) : ∀ d : ℕ, TreeTape N Φ ε d → ℝ
  | 0, _ => 1
  | d + 1, (τ, sub) =>
    finTapeProb N Φ ε τ * ∏ q : Fin N, treeTapeProb N Φ ε d (sub q)

noncomputable def hseRun {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (N h : ℕ) (Φ ε : ℝ) :
    ∀ d : ℕ, Finset (Fin n) → Finset (Fin n) → ℝ → TreeTape N Φ ε d →
      RawHST (Fin n) × Finset (Fin n)
  | 0, X, M, _, _ => (RawHST.leaf X, M)
  | d + 1, X, M, Δ, (τ, sub) =>
    if X.card ≤ 1 then
      (RawHST.leaf X, M)
    else
      let clus := sspClusters G w N h Φ ε X M Δ τ
      let childRes : Fin clus.length → RawHST (Fin n) × Finset (Fin n) :=
        fun idx =>
          let c := clus.get idx
          if hq : idx.1 < N then
            hseRun G w N h Φ ε d c.1 c.2 (Δ / 2) (sub ⟨idx.1, hq⟩)
          else
            (RawHST.leaf c.1, c.2)
      (RawHST.node X Δ (List.ofFn (fun idx => (childRes idx).1)),
       Finset.univ.biUnion (fun idx => (childRes idx).2))

noncomputable def savedRawDist {n : ℕ} (res : RawHST (Fin n) × Finset (Fin n))
    (u v : Fin n) : ℝ :=
  if u ∈ res.2 ∧ v ∈ res.2 then res.1.dist u v else 0

structure HSTParamSpec (N : ℕ) (Φ ε : ℝ) : Prop where
  one_le_L : 1 ≤ hstPhaseCount N
  delta_pos : 0 < hstTruncDelta N
  delta_lt_half : hstTruncDelta N < 1 / 2
  inv_one_sub_delta : (1 - hstTruncDelta N)⁻¹ ≤ 1 + 2 * hstTruncDelta N
  L_mul_delta_lt_one : (hstPhaseCount N : ℝ) * hstTruncDelta N < 1
  mu_zero_ge : N + 1 ≤ hstMu N 0
  mu_one_lt : hstMu N 1 < N + 1
  mu_L_eq : hstMu N (hstPhaseCount N) = 2
  mu_sq : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
    hstMu N (ℓ - 1) = (hstMu N ℓ) ^ 2 ∧ 2 ≤ hstMu N ℓ
  one_le_k : 1 ≤ hstRadiusSteps N Φ ε
  one_le_beta : 1 ≤ 2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1)
  one_le_K : 1 ≤ 8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)
  one_le_alpha :
    1 ≤ 256 * (hstPhaseCount N : ℝ) * Real.logb 2 (N : ℝ) *
      (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Φ)
  one_le_depth : 1 ≤ hstDepth Φ
  diam_lt_depth : Φ < 8 * (2 : ℝ) ^ (hstDepth Φ - 1)
  root_f_le_eps :
    (4 / (hstRadiusSteps N Φ ε : ℝ)) * (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Φ) *
      (Real.log (N : ℝ) + Real.log (2 / hstTruncDelta N) * Real.logb 2 Φ) ≤ ε
  slot_phases_bounds : ∀ ℓ ∈ sspSlotPhases N, 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N
  geomP_bounds : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
    0 < hstGeomP N Φ ε ℓ ∧ hstGeomP N Φ ε ℓ < 1
  trunc_norm_prod_ge :
    1 - hstTruncDelta N ≤ ∏ i : Fin (hstTotalSlots N),
      (1 - (1 - hstGeomP N Φ ε ((sspSlotPhases N).get i)) ^ hstRadiusSteps N Φ ε)
  prob_nonneg : ∀ (d : ℕ) (ω : TreeTape N Φ ε d), 0 ≤ treeTapeProb N Φ ε d ω
  prob_sum : ∀ d : ℕ, (∑ ω : TreeTape N Φ ε d, treeTapeProb N Φ ε d ω) = 1
  radius_bounds : ∀ Δ : ℝ, 0 < Δ →
    hstRadius N Δ (hstPhaseCount N) = Δ / 4 - Δ / (2 : ℝ) ^ (hstPhaseCount N + 4) ∧
    hstRadius N Δ (hstPhaseCount N) < Δ / 4 ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
      0 < hstRadius N Δ (ℓ - 1) ∧
      0 < hstStep N Φ ε Δ ℓ ∧
      Δ / hstStep N Φ ε Δ ℓ ≤ 8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ) ∧
      (Δ / (hstRadius N Δ ℓ - hstRadius N Δ (ℓ - 1))) *
        Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N) ≤
        64 * (hstPhaseCount N : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ))

structure SSPDetSpec (N n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (h : ℕ) (Φ ε : ℝ) : Prop where
  hopDist_toReal_bounds : ∀ u v : Fin n, u ≠ v →
    2 ≤ (hopDist G w h u v).toReal ∧ (hopDist G w h u v).toReal ≤ Φ
  scale_spec :
    ∀ (X M : Finset (Fin n)), 2 ≤ X.card → M ⊆ X →
      ∀ Δ : ℝ, 0 < Δ →
        (∀ u ∈ X, ∀ v ∈ X,
          hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
            ENNReal.ofReal Δ) →
        2 ≤ Δ ∧
        (∀ τ : FinTape N Φ ε,
          let tclus := sspTaggedClusters G w N h Φ ε X M Δ τ
          tclus ≠ [] ∧
          tclus.length ≤ N ∧
          (tclus.map (fun t => t.2.1)).Pairwise Disjoint ∧
          tclus.foldr (fun t acc => t.2.1 ∪ acc) ∅ = X ∧
          (∀ t ∈ tclus,
            t.2.1.Nonempty ∧
            t.2.1 ⊆ X ∧
            t.2.2 ⊆ M ∩ t.2.1 ∧
            (∀ u ∈ t.2.1, ∀ v ∈ t.2.1,
              hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
                ENNReal.ofReal (Δ / 2)) ∧
            (1 ≤ t.1 → (t.2.1.card : ℝ) ≤ (X.card : ℝ) / (hstMu N t.1 : ℝ)) ∧
            (∀ u ∈ t.2.2, ∀ v ∈ X \ t.2.1,
              ENNReal.ofReal Δ ≤
                ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
                  hopDist G w h u v) ∧
            (Δ < 8 → t.2.1.card = 1))) ∧
        (∀ X_cur : Finset (Fin n), X_cur ⊆ X →
          ∀ x ∈ X_cur, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
            x ∈ hstBall G w N h Φ ε Δ X_cur x ℓ 0 ∧
            (∀ R₁ R₂ : ℤ, R₁ ≤ R₂ →
              hstBall G w N h Φ ε Δ X_cur x ℓ R₁ ⊆ hstBall G w N h Φ ε Δ X_cur x ℓ R₂) ∧
            (∃ ρ : Fin n → ℤ,
              (∀ v ∈ X_cur, ∀ R : ℤ,
                v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ R ↔ ρ v ≤ R) ∧
              (∀ u ∈ X_cur, ∀ v ∈ X_cur, u ≠ v →
                ρ v ≤ ρ u +
                  (Nat.ceil ((hopDist G w h u v).toReal / hstStep N Φ ε Δ ℓ) : ℤ))))

structure HSERunDetSpec (N n : ℕ) (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (h : ℕ) (Φ ε : ℝ) : Prop where
  run_spec :
    ∀ (d : ℕ) (X M : Finset (Fin n)), X.Nonempty → M ⊆ X →
      ∀ Δ : ℝ, 0 < Δ →
        (∀ u ∈ X, ∀ v ∈ X,
          hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
            ENNReal.ofReal Δ) →
        (2 ≤ X.card → 1 ≤ d ∧ Δ < 8 * (2 : ℝ) ^ (d - 1)) →
        ∀ ω : TreeTape N Φ ε d,
          let res := hseRun G w N h Φ ε d X M Δ ω
          ValidRawHST res.1 ∧
          res.1.cluster = X ∧
          res.1.topLabel ≤ Δ ∧
          res.2 ⊆ M ∧
          (∀ u v : Fin n, 0 ≤ res.1.dist u v ∧ res.1.dist u v ≤ Δ) ∧
          (∀ u ∈ X, ∀ v ∈ X,
            hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
              ENNReal.ofReal (res.1.dist u v)) ∧
          (∀ u ∈ res.2, ∀ v ∈ X,
            ENNReal.ofReal (res.1.dist u v) ≤
              ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
                hopDist G w h u v)
def thm4OpenSum {α β : Type*} [Add β] (step : α → α → β) : α → List α → α → β
  | u, [], last => step u last
  | u, w :: ws, last => step u w + thm4OpenSum step w ws last

def thm4OpenRel {α : Type*} (rel : α → α → Prop) : α → List α → α → Prop
  | u, [], last => rel u last
  | u, w :: ws, last => rel u w ∧ thm4OpenRel rel w ws last
noncomputable def hseExpDistFactor (N : ℕ) (m Δ : ℝ) : ℝ :=
  256 * (hstPhaseCount N : ℝ) * Real.logb 2 m *
    (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ)

noncomputable def hseExpDistPenaltySteps {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (N h : ℕ) (Φ ε : ℝ) (m_init : ℕ) (Δ d_uv : ℝ) (u v : Fin n)
    (X_cur M_cur : Finset (Fin n)) : List (ℕ × ℕ) → ℝ
  | [] =>
    if u ∈ M_cur ∧ v ∈ M_cur then hseExpDistFactor N (m_init : ℝ) (Δ / 2) * d_uv else 0
  | (ℓ, R) :: rest =>
    let cands := sspCands G w N h Φ ε Δ m_init X_cur ℓ
    if hc : cands.Nonempty then
      let x := cands.min' hc
      let Xj := hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ)
      let Mj := hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur
      let M_next := M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1)
      if u ∈ Mj ∧ v ∈ Mj then
        hseExpDistFactor N ((m_init : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2) * d_uv
      else if (u ∈ Mj ∧ v ∈ M_next) ∨ (v ∈ Mj ∧ u ∈ M_next) then
        Δ
      else if u ∈ M_next ∧ v ∈ M_next then
        hseExpDistPenaltySteps G w N h Φ ε m_init Δ d_uv u v (X_cur \ Xj) M_next rest
      else
        0
    else
      hseExpDistPenaltySteps G w N h Φ ε m_init Δ d_uv u v X_cur M_cur rest

def hseExpDistStepsOfTape {k : ℕ} (phases : List ℕ) (τ : Fin phases.length → Fin k) :
    List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin phases.length => (phases.get i, (τ i).1))

noncomputable def hseExpDistUnnormGeom (N : ℕ) (Φ ε : ℝ) (ℓ R : ℕ) : ℝ :=
  (1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ

noncomputable def hseExpDistUnnormTape (N : ℕ) (Φ ε : ℝ) (phases : List ℕ)
    (τ : Fin phases.length → Fin (hstRadiusSteps N Φ ε)) : ℝ :=
  ∏ i : Fin phases.length, hseExpDistUnnormGeom N Φ ε (phases.get i) (τ i).1

theorem hst_param_bounds (N : ℕ) (hN : 2 ≤ N)
    (Φ : ℝ) (hΦ_ge : 2 ≤ Φ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    HSTParamSpec N Φ ε :=
by
  
  set y : ℝ := (N : ℝ) + 1
  have hN_cast : (2 : ℝ) ≤ (N : ℝ) := Nat.ofNat_le_cast.mpr hN
  have hy_ge3 : (3 : ℝ) ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  set x : ℝ := Real.logb 2 y
  have hx_gt_3_2 : 3 / 2 < x := by
    have h8 : (2 : ℝ) ^ (3 : ℝ) < y ^ (2 : ℕ) := by
      norm_num
      nlinarith
    have hlog : (3 : ℝ) < Real.logb 2 (y ^ (2 : ℕ)) :=
      (Real.lt_logb_iff_rpow_lt one_lt_two (pow_pos hy_pos 2)).mpr h8
    rw [Real.logb_pow 2 y 2] at hlog
    norm_num at hlog
    linarith
  have hx_gt1 : 1 < x := by linarith
  have hx_pos : 0 < x := by linarith
  have hlogx_pos : 0 < Real.logb 2 x := Real.logb_pos one_lt_two hx_gt1
  set L : ℕ := hstPhaseCount N
  have hone_le_L : 1 ≤ L := by
    have hpos : 0 < L := Nat.ceil_pos.mpr hlogx_pos
    omega
  have hx_sq_gt : 9 / 4 < x ^ 2 := by nlinarith
  set δ : ℝ := hstTruncDelta N
  have hdelta_eq : δ = (x ^ 2)⁻¹ := rfl
  have hdelta_pos : 0 < δ := by
    rw [hdelta_eq]
    exact inv_pos.mpr (by linarith)
  have hdelta_cancel : δ * (x ^ 2) = 1 := by
    rw [hdelta_eq]
    exact inv_mul_cancel₀ (by linarith)
  have hdelta_lt_half : δ < 1 / 2 := by nlinarith
  have hinv_one_sub_delta : (1 - δ)⁻¹ ≤ 1 + 2 * δ := by
    rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - δ)]
    nlinarith
  have hx_le_pow : x ≤ (2 : ℝ) ^ L := by
    have hceil : Real.logb 2 x ≤ (L : ℝ) := Nat.le_ceil (Real.logb 2 x)
    have hrpow : x ≤ (2 : ℝ) ^ (L : ℝ) := (Real.logb_le_iff_le_rpow one_lt_two hx_pos).mp hceil
    rwa [Real.rpow_natCast] at hrpow
  have hmu_zero_ge : N + 1 ≤ hstMu N 0 := by
    have hx_le_cast : Real.logb 2 y ≤ ((2 ^ L : ℕ) : ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hx_le_pow
    have hy_le : y ≤ (2 : ℝ) ^ (((2 ^ L : ℕ) : ℝ)) :=
      (Real.logb_le_iff_le_rpow one_lt_two hy_pos).mp hx_le_cast
    rw [Real.rpow_natCast] at hy_le
    have hy_cast : ((N + 1 : ℕ) : ℝ) ≤ ((hstMu N 0 : ℕ) : ℝ) := by
      simpa [y, hstMu] using hy_le
    exact Nat.cast_le.mp hy_cast
  have h2L1_lt_x : ((2 ^ (L - 1) : ℕ) : ℝ) < x := by
    have hceil_lt : (L : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one (le_of_lt hlogx_pos)
    have hsub_lt : ((L - 1 : ℕ) : ℝ) < Real.logb 2 x := by
      rw [Nat.cast_sub hone_le_L, Nat.cast_one]
      linarith
    have hrpow : (2 : ℝ) ^ (((L - 1 : ℕ) : ℝ)) < x :=
      (Real.lt_logb_iff_rpow_lt one_lt_two hx_pos).mp hsub_lt
    rw [Real.rpow_natCast] at hrpow
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hrpow
  have hmu_one_lt : hstMu N 1 < N + 1 := by
    have hy_gt : (2 : ℝ) ^ (((2 ^ (L - 1) : ℕ) : ℝ)) < y :=
      (Real.lt_logb_iff_rpow_lt one_lt_two hy_pos).mp h2L1_lt_x
    rw [Real.rpow_natCast] at hy_gt
    have hy_cast : ((hstMu N 1 : ℕ) : ℝ) < ((N + 1 : ℕ) : ℝ) := by
      simpa [y, hstMu, L] using hy_gt
    exact Nat.cast_lt.mp hy_cast
  have hL_mul_delta_lt_one : (L : ℝ) * δ < 1 := by
    have hL_lt_pow : L - 1 < 2 ^ (L - 1) := Nat.lt_two_pow_self
    have hL_le_pow : L ≤ 2 ^ (L - 1) := by omega
    have hL_cast_le : (L : ℝ) ≤ ((2 ^ (L - 1) : ℕ) : ℝ) := Nat.cast_le.mpr hL_le_pow
    have hL_lt_xsq : (L : ℝ) < x ^ 2 := by nlinarith
    nlinarith
  have hmu_L_eq : hstMu N L = 2 := by
    simp [hstMu, L]
  have hmu_sq : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L → hstMu N (ℓ - 1) = (hstMu N ℓ) ^ 2 ∧ 2 ≤ hstMu N ℓ := by
    intro ℓ hℓ1 hℓL
    constructor
    · simp only [hstMu]
      have hsub : L - (ℓ - 1) = (L - ℓ) + 1 := by omega
      rw [hsub]
      have hdbl : 2 ^ ((L - ℓ) + 1) = 2 ^ (L - ℓ) + 2 ^ (L - ℓ) := by ring
      rw [hdbl, pow_add, sq]
    · simp only [hstMu]
      have h1 : 1 ≤ 2 ^ (L - ℓ) := Nat.one_le_two_pow
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 ^ (L - ℓ)) := Nat.pow_le_pow_right (by norm_num) h1
  have hphaseDesc_bounds : ∀ (m a : ℕ), a ∈ phaseDesc m → 1 ≤ a ∧ a ≤ m := by
    intro m
    induction m with
    | zero =>
      intro a ha
      simp [phaseDesc] at ha
    | succ m ih =>
      intro a ha
      simp only [phaseDesc, List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · have := ih a ha
        omega
  have hslot_bounds : ∀ ℓ ∈ sspSlotPhases N, 1 ≤ ℓ ∧ ℓ ≤ L := by
    intro ℓ hℓ
    simp only [sspSlotPhases, List.mem_flatMap, List.mem_replicate] at hℓ
    rcases hℓ with ⟨a, ha, _, hℓa⟩
    rw [hℓa]
    exact hphaseDesc_bounds L a ha

  
  set P_Φ : ℝ := (1 + 2 * δ) ^ (Real.logb 2 Φ)
  set S : ℝ := Real.log (N : ℝ) + Real.log (2 / δ) * Real.logb 2 Φ
  set k : ℕ := hstRadiusSteps N Φ ε
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogbN_ge1 : 1 ≤ Real.logb 2 (N : ℝ) :=
    (Real.le_logb_iff_rpow_le one_lt_two (by linarith)).mpr (by rw [Real.rpow_one]; exact hN_cast)
  have hlogbPhi_ge1 : 1 ≤ Real.logb 2 Φ :=
    (Real.le_logb_iff_rpow_le one_lt_two (by linarith)).mpr (by norm_num; exact hΦ_ge)
  have hP_ge1 : 1 ≤ P_Φ := Real.one_le_rpow (by linarith) (by linarith)
  have h2_div_delta_gt4 : 4 < 2 / δ := (lt_div_iff₀ hdelta_pos).mpr (by linarith)
  have hlog_2delta_pos : 0 < Real.log (2 / δ) := Real.log_pos (by linarith)
  have hS_pos : 0 < S := by nlinarith
  have h4_div_eps_gt4 : 4 < 4 / ε := (lt_div_iff₀ hε_pos).mpr (by linarith)
  have hk_arg_pos : 0 < (4 / ε) * P_Φ * S := by positivity
  have hone_le_k : 1 ≤ k := by
    have hk_pos : 0 < k := Nat.ceil_pos.mpr hk_arg_pos
    omega
  have hone_le_beta : 1 ≤ 2 * k * (L + 1) := by nlinarith
  have hk_cast_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hone_le_k
  have hk_cast_pos : 0 < (k : ℝ) := by linarith
  have hL_cast_ge1 : (1 : ℝ) ≤ (L : ℝ) := Nat.one_le_cast.mpr hone_le_L
  have hL_cast_pos : 0 < (L : ℝ) := by linarith
  have hone_le_K : 1 ≤ 8 * (k : ℝ) * (L : ℝ) := by nlinarith
  have hone_le_alpha : 1 ≤ 256 * (L : ℝ) * Real.logb 2 (N : ℝ) * P_Φ := by
    have h1 : 1 ≤ 256 * (L : ℝ) * Real.logb 2 (N : ℝ) := by nlinarith
    nlinarith
  have hone_le_depth : 1 ≤ hstDepth Φ := by
    simp only [hstDepth]
    omega
  have hdiam_lt_depth : Φ < 8 * (2 : ℝ) ^ (hstDepth Φ - 1) := by
    have hd_sub : hstDepth Φ - 1 = Nat.ceil (Real.logb 2 Φ) := by
      simp only [hstDepth]
      omega
    rw [hd_sub]
    set c := Nat.ceil (Real.logb 2 Φ)
    have hc : Real.logb 2 Φ ≤ (c : ℝ) := Nat.le_ceil (Real.logb 2 Φ)
    have hΦ_le : Φ ≤ (2 : ℝ) ^ (c : ℝ) :=
      (Real.logb_le_iff_le_rpow one_lt_two (by linarith)).mp hc
    rw [Real.rpow_natCast] at hΦ_le
    have hpow_pos : 0 < (2 : ℝ) ^ c := pow_pos (by norm_num) c
    linarith
  have hk_ceil : (4 / ε) * P_Φ * S ≤ (k : ℝ) := Nat.le_ceil _
  have hroot_f_le_eps : (4 / (k : ℝ)) * P_Φ * S ≤ ε := by
    have h1 : (4 * P_Φ * S) / ε ≤ (k : ℝ) := by
      simpa only [div_mul_eq_mul_div] using hk_ceil
    have h2 : 4 * P_Φ * S ≤ (k : ℝ) * ε := (div_le_iff₀ hε_pos).mp h1
    have h3 : (4 * P_Φ * S) / (k : ℝ) ≤ ε :=
      (div_le_iff₀ hk_cast_pos).mpr (by linarith)
    simpa only [div_mul_eq_mul_div] using h3
  have hgeomP_bounds : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L →
      0 < hstGeomP N Φ ε ℓ ∧ hstGeomP N Φ ε ℓ < 1 := by
    intro ℓ hℓ1 hℓL
    have hmu_ge2 : 2 ≤ hstMu N ℓ := (hmu_sq ℓ hℓ1 hℓL).2
    have hmu_cast_ge2 : (2 : ℝ) ≤ (hstMu N ℓ : ℝ) := Nat.ofNat_le_cast.mpr hmu_ge2
    constructor
    · have hratio_gt : 1 < 2 * (hstMu N ℓ : ℝ) / δ := (lt_div_iff₀ hdelta_pos).mpr (by linarith)
      have hlog_pos : 0 < Real.log (2 * (hstMu N ℓ : ℝ) / δ) := Real.log_pos hratio_gt
      exact mul_pos (div_pos (by norm_num) hk_cast_pos) hlog_pos
    · have hsub_le : L - ℓ ≤ L - 1 := by omega
      have hpow1 : 2 ^ (L - ℓ) ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) hsub_le
      have hmu_le_mu1 : hstMu N ℓ ≤ hstMu N 1 := Nat.pow_le_pow_right (by norm_num) hpow1
      have hmu_le_N : hstMu N ℓ ≤ N := by omega
      have hmu_cast_le : (hstMu N ℓ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hmu_le_N
      have hlog_mu_le : Real.log (hstMu N ℓ : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (by linarith) hmu_cast_le
      have hsplit : 2 * (hstMu N ℓ : ℝ) / δ = (hstMu N ℓ : ℝ) * (2 / δ) := by ring
      have hlog_split : Real.log (2 * (hstMu N ℓ : ℝ) / δ) =
          Real.log (hstMu N ℓ : ℝ) + Real.log (2 / δ) := by
        rw [hsplit, Real.log_mul (by linarith) (by linarith)]
      have hlog_le_S : Real.log (2 * (hstMu N ℓ : ℝ) / δ) ≤ S := by nlinarith
      have h4P : 4 < (4 / ε) * P_Φ := by nlinarith
      have h4S_lt : 4 * S < (4 / ε) * P_Φ * S := by nlinarith
      have h2log_lt_k : 2 * Real.log (2 * (hstMu N ℓ : ℝ) / δ) < (k : ℝ) := by linarith
      simp only [hstGeomP]
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ hk_cast_pos).mpr (by linarith)

  
  let q : ℕ → ℝ := fun ℓ => (1 - hstGeomP N Φ ε ℓ) ^ k
  have hq_bounds : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L →
      0 < q ℓ ∧ q ℓ < 1 ∧ (hstMu N (ℓ - 1) : ℝ) * q ℓ ≤ δ ^ 2 / 4 := by
    intro ℓ hℓ1 hℓL
    have hp := hgeomP_bounds ℓ hℓ1 hℓL
    have hmu_ge2 : 2 ≤ hstMu N ℓ := (hmu_sq ℓ hℓ1 hℓL).2
    have hmu_cast_ge2 : (2 : ℝ) ≤ (hstMu N ℓ : ℝ) := Nat.ofNat_le_cast.mpr hmu_ge2
    have hq_pos : 0 < q ℓ := pow_pos (by linarith) k
    have hexp1 : 1 - hstGeomP N Φ ε ℓ ≤ Real.exp (-hstGeomP N Φ ε ℓ) := by
      have h := Real.add_one_le_exp (-hstGeomP N Φ ε ℓ)
      linarith
    have hq_le_exp : q ℓ ≤ Real.exp ((k : ℝ) * (-hstGeomP N Φ ε ℓ)) := by
      calc
        q ℓ ≤ (Real.exp (-hstGeomP N Φ ε ℓ)) ^ k :=
          pow_le_pow_left₀ (by linarith) hexp1 k
        _ = Real.exp ((k : ℝ) * (-hstGeomP N Φ ε ℓ)) := (Real.exp_nat_mul _ k).symm
    have hR_pos : 0 < 2 * (hstMu N ℓ : ℝ) / δ := by positivity
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
    have hk_def : hstRadiusSteps N Φ ε = k := rfl
    have hδ_def : hstTruncDelta N = δ := rfl
    have harg_eq : (k : ℝ) * (-hstGeomP N Φ ε ℓ) =
        -(((2 : ℕ) : ℝ) * Real.log (2 * (hstMu N ℓ : ℝ) / δ)) := by
      simp only [hstGeomP, hk_def, hδ_def, Nat.cast_ofNat]
      field_simp
    have hexp_eval : Real.exp ((k : ℝ) * (-hstGeomP N Φ ε ℓ)) =
        δ ^ 2 / (4 * (hstMu N ℓ : ℝ) ^ 2) := by
      rw [harg_eq, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hR_pos]
      have hmu_ne : (hstMu N ℓ : ℝ) ≠ 0 := by linarith
      have hdelta_ne : δ ≠ 0 := ne_of_gt hdelta_pos
      field_simp
      ring
    have hq_le_tail : q ℓ ≤ δ ^ 2 / (4 * (hstMu N ℓ : ℝ) ^ 2) := hq_le_exp.trans_eq hexp_eval
    have hq_lt1 : q ℓ < 1 := by
      have hden_ge : 16 ≤ 4 * (hstMu N ℓ : ℝ) ^ 2 := by nlinarith
      have hnum_lt : δ ^ 2 < 1 := by nlinarith
      have hfrac_lt1 : δ ^ 2 / (4 * (hstMu N ℓ : ℝ) ^ 2) < 1 :=
        (div_lt_iff₀ (by linarith)).mpr (by linarith)
      linarith
    have hmu_sq_cast : (hstMu N (ℓ - 1) : ℝ) = (hstMu N ℓ : ℝ) ^ 2 := by
      exact_mod_cast (hmu_sq ℓ hℓ1 hℓL).1
    have hmu_q_le : (hstMu N (ℓ - 1) : ℝ) * q ℓ ≤ δ ^ 2 / 4 := by
      rw [hmu_sq_cast]
      have hmu_sq_nonneg : 0 ≤ (hstMu N ℓ : ℝ) ^ 2 := sq_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hq_le_tail hmu_sq_nonneg
      have hmu_ne : (hstMu N ℓ : ℝ) ≠ 0 := by linarith
      have hrhs : (hstMu N ℓ : ℝ) ^ 2 * (δ ^ 2 / (4 * (hstMu N ℓ : ℝ) ^ 2)) = δ ^ 2 / 4 := by
        field_simp
      linarith
    exact ⟨hq_pos, hq_lt1, hmu_q_le⟩
  have hbernoulli : ∀ (xs : List ℝ), (∀ z ∈ xs, 0 ≤ z ∧ z ≤ 1) →
      1 - xs.sum ≤ (xs.map (fun z => 1 - z)).prod := by
    intro xs
    induction xs with
    | nil => simp
    | cons a tail ih =>
      intro hxs
      have ha : 0 ≤ a ∧ a ≤ 1 := hxs a (by simp)
      have htail : ∀ z ∈ tail, 0 ≤ z ∧ z ≤ 1 := fun z hz => hxs z (by simp [hz])
      have hih := ih htail
      have hsum_nonneg : 0 ≤ tail.sum := List.sum_nonneg (fun z hz => (htail z hz).1)
      simp only [List.sum_cons, List.map_cons, List.prod_cons]
      have hmul : (1 - a) * (1 - tail.sum) ≤ (1 - a) * (tail.map (fun z => 1 - z)).prod :=
        mul_le_mul_of_nonneg_left hih (by linarith)
      nlinarith
  have hphase_sum : ∀ m : ℕ, m ≤ L →
      ((((phaseDesc m).flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ)).map q).sum) ≤
        (m : ℝ) * (δ ^ 2 / 4) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [phaseDesc]
    | succ m ih =>
      intro hm
      have hm_le : m ≤ L := by omega
      have hih := ih hm_le
      have htail_m1 : (hstMu N m : ℝ) * q (m + 1) ≤ δ ^ 2 / 4 := by
        simpa using (hq_bounds (m + 1) (by omega) hm).2.2
      simp only [phaseDesc, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_replicate, List.sum_replicate, nsmul_eq_mul, Nat.add_sub_cancel, Nat.cast_add,
        Nat.cast_one]
      linarith
  have htrunc_norm_prod_ge :
      1 - δ ≤ ∏ i : Fin (hstTotalSlots N),
        (1 - (1 - hstGeomP N Φ ε ((sspSlotPhases N).get i)) ^ k) := by
    have hprod_eq :
        (∏ i : Fin (hstTotalSlots N),
          (1 - (1 - hstGeomP N Φ ε ((sspSlotPhases N).get i)) ^ k)) =
        (((sspSlotPhases N).map q).map (fun z => 1 - z)).prod := by
      rw [Fin.prod_univ_def]
      change ((List.finRange (sspSlotPhases N).length).map
        (((fun z => 1 - z) ∘ q) ∘ (sspSlotPhases N).get)).prod = _
      rw [← List.map_map, List.map_get_finRange, List.map_map]
    rw [hprod_eq]
    have hmem_q : ∀ z ∈ (sspSlotPhases N).map q, 0 ≤ z ∧ z ≤ 1 := by
      intro z hz
      rw [List.mem_map] at hz
      rcases hz with ⟨ℓ, hℓ, rfl⟩
      have hb := hslot_bounds ℓ hℓ
      have hqb := hq_bounds ℓ hb.1 hb.2
      exact ⟨le_of_lt hqb.1, le_of_lt hqb.2.1⟩
    have hbern := hbernoulli ((sspSlotPhases N).map q) hmem_q
    have hsum_le : ((sspSlotPhases N).map q).sum ≤ (L : ℝ) * (δ ^ 2 / 4) :=
      hphase_sum L (le_refl L)
    have hLdelta_lt : (L : ℝ) * (δ ^ 2 / 4) < δ := by nlinarith
    linarith
  have htrunc_nonneg : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L → ∀ R : ℕ,
      0 ≤ truncGeomWeight N Φ ε ℓ R := by
    intro ℓ hℓ1 hℓL R
    have hp := hgeomP_bounds ℓ hℓ1 hℓL
    have hq_lt1 : q ℓ < 1 := (hq_bounds ℓ hℓ1 hℓL).2.1
    simp only [truncGeomWeight]
    exact div_nonneg (mul_nonneg (pow_nonneg (by linarith) R) (le_of_lt hp.1)) (by linarith)
  have htrunc_sum : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L →
      (∑ r : Fin k, truncGeomWeight N Φ ε ℓ r.1) = 1 := by
    intro ℓ hℓ1 hℓL
    have hp := hgeomP_bounds ℓ hℓ1 hℓL
    have hq_lt1 : q ℓ < 1 := (hq_bounds ℓ hℓ1 hℓL).2.1
    simp only [truncGeomWeight]
    rw [Fin.sum_univ_eq_sum_range (fun R =>
      (1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ /
        (1 - (1 - hstGeomP N Φ ε ℓ) ^ k)) k]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    rw [geom_sum_eq (by linarith : 1 - hstGeomP N Φ ε ℓ ≠ 1) k]
    have hp_ne : hstGeomP N Φ ε ℓ ≠ 0 := ne_of_gt hp.1
    have hden_ne : 1 - (1 - hstGeomP N Φ ε ℓ) ^ k ≠ 0 := ne_of_gt (by linarith)
    have hsub_ne : 1 - hstGeomP N Φ ε ℓ - 1 ≠ 0 := by linarith
    field_simp
    ring
  have hfin_nonneg : ∀ τ : FinTape N Φ ε, 0 ≤ finTapeProb N Φ ε τ := by
    intro τ
    refine Finset.prod_nonneg (fun i _ => ?_)
    have hb := hslot_bounds _ (List.get_mem (sspSlotPhases N) i)
    exact htrunc_nonneg _ hb.1 hb.2 (τ i).1
  have hfin_sum : (∑ τ : FinTape N Φ ε, finTapeProb N Φ ε τ) = 1 := by
    simp only [finTapeProb]
    rw [← Fintype.prod_sum (fun (i : Fin (hstTotalSlots N)) (r : Fin k) =>
      truncGeomWeight N Φ ε ((sspSlotPhases N).get i) r.1)]
    refine Finset.prod_eq_one (fun i _ => ?_)
    have hb := hslot_bounds _ (List.get_mem (sspSlotPhases N) i)
    exact htrunc_sum _ hb.1 hb.2
  have hprob_nonneg : ∀ (d : ℕ) (ω : TreeTape N Φ ε d), 0 ≤ treeTapeProb N Φ ε d ω := by
    intro d
    induction d with
    | zero =>
      intro _
      exact zero_le_one
    | succ d ih =>
      rintro ⟨τ, sub⟩
      exact mul_nonneg (hfin_nonneg τ) (Finset.prod_nonneg (fun q _ => ih (sub q)))
  have hprob_sum : ∀ d : ℕ, (∑ ω : TreeTape N Φ ε d, treeTapeProb N Φ ε d ω) = 1 := by
    intro d
    induction d with
    | zero =>
      change (∑ _ : PUnit, (1 : ℝ)) = 1
      simp
    | succ d ih =>
      letI : Fintype (TreeTape N Φ ε d) := instFintypeTreeTape N Φ ε d
      change (∑ ω : FinTape N Φ ε × (Fin N → TreeTape N Φ ε d),
        finTapeProb N Φ ε ω.1 * ∏ q : Fin N, treeTapeProb N Φ ε d (ω.2 q)) = 1
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, ← Fintype.prod_sum, ih, Finset.prod_const_one, mul_one]
      exact hfin_sum

  
  have hradius_bounds : ∀ Δ : ℝ, 0 < Δ →
      hstRadius N Δ L = Δ / 4 - Δ / (2 : ℝ) ^ (L + 4) ∧
      hstRadius N Δ L < Δ / 4 ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ L →
        0 < hstRadius N Δ (ℓ - 1) ∧
        0 < hstStep N Φ ε Δ ℓ ∧
        Δ / hstStep N Φ ε Δ ℓ ≤ 8 * (k : ℝ) * (L : ℝ) ∧
        (Δ / (hstRadius N Δ ℓ - hstRadius N Δ (ℓ - 1))) *
          Real.log (2 * (hstMu N ℓ : ℝ) / δ) ≤
          64 * (L : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ)) := by
    intro Δ hΔ
    have hL_def : hstPhaseCount N = L := rfl
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_cast_pos
    have hrad_closed : ∀ m : ℕ, m ≤ L →
        hstRadius N Δ m =
          (m : ℝ) * Δ / (8 * (L : ℝ)) + Δ / (2 : ℝ) ^ ((L - m) + 3) -
            Δ / (2 : ℝ) ^ (L + 4) := by
      intro m
      induction m with
      | zero =>
        intro _
        simp only [hstRadius, hL_def, Nat.cast_zero, zero_mul, zero_div, zero_add, Nat.sub_zero]
        have hpow : (2 : ℝ) ^ (L + 4) = (2 : ℝ) ^ (L + 3) * 2 := by
          rw [show L + 4 = (L + 3) + 1 by omega, pow_succ]
        rw [hpow]
        field_simp
        ring
      | succ m ih =>
        intro hm
        have hm_le : m ≤ L := by omega
        rw [hstRadius, hL_def, ih hm_le]
        set e := L - (m + 1)
        have hLm : (L - m) + 3 = e + 4 := by omega
        rw [hLm]
        have hpow : (2 : ℝ) ^ (e + 4) = (2 : ℝ) ^ (e + 3) * 2 := by
          rw [show e + 4 = (e + 3) + 1 by omega, pow_succ]
        rw [hpow, Nat.cast_add, Nat.cast_one]
        field_simp
        ring
    have hrad_L_eq : hstRadius N Δ L = Δ / 4 - Δ / (2 : ℝ) ^ (L + 4) := by
      rw [hrad_closed L (le_refl L), Nat.sub_self]
      field_simp
      ring
    have hrad_L_lt : hstRadius N Δ L < Δ / 4 := by
      rw [hrad_L_eq]
      have hpos : 0 < Δ / (2 : ℝ) ^ (L + 4) := by positivity
      linarith
    have hrad_pos : ∀ m : ℕ, 0 < hstRadius N Δ m := by
      intro m
      induction m with
      | zero =>
        simp only [hstRadius]
        positivity
      | succ m ih =>
        simp only [hstRadius]
        positivity
    refine ⟨hrad_L_eq, hrad_L_lt, ?_⟩
    intro ℓ hℓ1 hℓL
    have hrad_prev_pos : 0 < hstRadius N Δ (ℓ - 1) := hrad_pos (ℓ - 1)
    have hℓ_eq : ℓ = (ℓ - 1) + 1 := by omega
    have hdiff : hstRadius N Δ ℓ - hstRadius N Δ (ℓ - 1) =
        Δ / (2 : ℝ) ^ ((L - ℓ) + 4) + Δ / (8 * (L : ℝ)) := by
      conv_lhs => rw [hℓ_eq, hstRadius]
      rw [← hℓ_eq, hL_def]
      ring
    set D : ℝ := hstRadius N Δ ℓ - hstRadius N Δ (ℓ - 1)
    have hD_gt : Δ / (8 * (L : ℝ)) < D := by
      rw [show D = Δ / (2 : ℝ) ^ ((L - ℓ) + 4) + Δ / (8 * (L : ℝ)) from hdiff]
      have h1 : 0 < Δ / (2 : ℝ) ^ ((L - ℓ) + 4) := by positivity
      linarith
    have hD_pos : 0 < D := lt_trans (by positivity) hD_gt
    have hstep_pos : 0 < hstStep N Φ ε Δ ℓ := div_pos hD_pos hk_cast_pos
    have hstep_bound : Δ / hstStep N Φ ε Δ ℓ ≤ 8 * (k : ℝ) * (L : ℝ) := by
      rw [div_le_iff₀ hstep_pos]
      simp only [hstStep]
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_cast_pos
      have hprod : 8 * (k : ℝ) * (L : ℝ) * (D / (k : ℝ)) = 8 * (L : ℝ) * D := by
        field_simp
      have hbase : 8 * (L : ℝ) * (Δ / (8 * (L : ℝ))) = Δ := by
        field_simp
      nlinarith
    have hratio_bound : (Δ / D) * Real.log (2 * (hstMu N ℓ : ℝ) / δ) ≤
        64 * (L : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ) := by
      set a : ℝ := ((2 ^ (L - ℓ) : ℕ) : ℝ)
      set b : ℝ := (L : ℝ)
      have ha_ge1 : 1 ≤ a := Nat.one_le_cast.mpr (@Nat.one_le_two_pow (L - ℓ))
      have ha_pos : 0 < a := by linarith
      have hb_ge1 : 1 ≤ b := hL_cast_ge1
      have hlogb_mu : Real.logb 2 (hstMu N ℓ : ℝ) = a := by
        have hmu_eq : (hstMu N ℓ : ℝ) = (2 : ℝ) ^ (2 ^ (L - ℓ)) := by simp [hstMu, hL_def]
        rw [hmu_eq, Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
      have hlog2_le1 : Real.log 2 ≤ 1 :=
        (Real.log_le_iff_le_exp (by norm_num)).mpr (by linarith [Real.add_one_le_exp 1])
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
      have hlog_2mu : Real.log (2 * (hstMu N ℓ : ℝ)) ≤ 2 * a := by
        have h2mu : 2 * (hstMu N ℓ : ℝ) = (2 : ℝ) ^ (2 ^ (L - ℓ) + 1) := by
          simp [hstMu, pow_succ]
          ring
        rw [h2mu, Real.log_pow, Nat.cast_add, Nat.cast_one]
        change (a + 1) * Real.log 2 ≤ 2 * a
        nlinarith
      have hlog_inv_delta : Real.log δ⁻¹ ≤ 2 * b := by
        have hlogx : Real.log x ≤ b := by
          have h1 := Real.log_le_log hx_pos hx_le_pow
          rw [Real.log_pow] at h1
          nlinarith
        have hinv : δ⁻¹ = x ^ (2 : ℕ) := by
          rw [hdelta_eq, inv_inv]
        rw [hinv, Real.log_pow, Nat.cast_ofNat]
        linarith
      have hmu_ge2 : (2 : ℝ) ≤ (hstMu N ℓ : ℝ) := Nat.ofNat_le_cast.mpr (hmu_sq ℓ hℓ1 hℓL).2
      have hLambda : Real.log (2 * (hstMu N ℓ : ℝ) / δ) ≤ 2 * a + 2 * b := by
        rw [div_eq_mul_inv, Real.log_mul (by linarith) (by positivity)]
        linarith
      have hpow4 : (2 : ℝ) ^ ((L - ℓ) + 4) = 16 * a := by
        rw [pow_add]
        norm_num [a]
        ring
      have hclear : (64 * b * a) * D = Δ * (4 * b + 8 * a) := by
        rw [show D = Δ / (2 : ℝ) ^ ((L - ℓ) + 4) + Δ / (8 * b) from hdiff, hpow4]
        field_simp
        ring
      rw [hlogb_mu, div_mul_eq_mul_div]
      refine (div_le_iff₀ hD_pos).mpr ?_
      nlinarith
    exact ⟨hrad_prev_pos, hstep_pos, hstep_bound, hratio_bound⟩

  exact {
    one_le_L := hone_le_L
    delta_pos := hdelta_pos
    delta_lt_half := hdelta_lt_half
    inv_one_sub_delta := hinv_one_sub_delta
    L_mul_delta_lt_one := hL_mul_delta_lt_one
    mu_zero_ge := hmu_zero_ge
    mu_one_lt := hmu_one_lt
    mu_L_eq := hmu_L_eq
    mu_sq := hmu_sq
    one_le_k := hone_le_k
    one_le_beta := hone_le_beta
    one_le_K := hone_le_K
    one_le_alpha := hone_le_alpha
    one_le_depth := hone_le_depth
    diam_lt_depth := hdiam_lt_depth
    root_f_le_eps := hroot_f_le_eps
    slot_phases_bounds := hslot_bounds
    geomP_bounds := hgeomP_bounds
    trunc_norm_prod_ge := htrunc_norm_prod_ge
    prob_nonneg := hprob_nonneg
    prob_sum := hprob_sum
    radius_bounds := hradius_bounds
  }

theorem exists_hst_of_valid_raw_hst (W : Type) [Fintype W] [DecidableEq W]
    (T : RawHST W) (hT : ValidRawHST T) (h_univ : T.cluster = Finset.univ) :
    ∃ U : HST W,
      U.label U.root = ENNReal.ofReal T.topLabel ∧
      ∀ u v : W, U.dist u v = ENNReal.ofReal (T.dist u v) :=
by
  
  have h_lca_iff : ∀ (N : Type) (G : SimpleGraph N), G.IsTree →
      ∀ rt x y z : N, rootedLCA G rt x y = z ↔ IsLCA G rt x y z := by
    intro N G hG rt
    classical
    let P : ∀ q : N, G.Walk rt q := fun q => Classical.choose (hG.existsUnique_path rt q)
    have hP_spec : ∀ q : N, (P q).IsPath ∧ ∀ p : G.Walk rt q, p.IsPath → p = P q :=
      fun q => Classical.choose_spec (hG.existsUnique_path rt q)
    have hP_path : ∀ q : N, (P q).IsPath := fun q => (hP_spec q).1
    have hP_uniq : ∀ (q : N) (p : G.Walk rt q), p.IsPath → p = P q := fun q => (hP_spec q).2
    have desc_iff : ∀ q z : N, IsDescendant G rt q z ↔ z ∈ (P q).support := by
      intro q z
      constructor
      · rintro ⟨p, hp, hz⟩
        rwa [hP_uniq q p hp] at hz
      · intro hz
        exact ⟨P q, hP_path q, hz⟩
    have take_eq : ∀ {q z : N} (hz : z ∈ (P q).support), (P q).takeUntil z hz = P z := by
      intro q z hz
      exact hP_uniq z _ ((hP_path q).takeUntil hz)
    have desc_refl : ∀ q : N, IsDescendant G rt q q := by
      intro q
      rw [desc_iff]
      exact SimpleGraph.Walk.end_mem_support (P q)
    have eq_of_desc_len_le : ∀ {q z : N}, IsDescendant G rt q z → (P q).length ≤ (P z).length → z = q := by
      intro q z hqz hlen
      rw [desc_iff] at hqz
      have hspec := SimpleGraph.Walk.take_spec (P q) hqz
      have hlen_eq : ((P q).takeUntil z hqz).length + ((P q).dropUntil z hqz).length = (P q).length := by
        rw [← SimpleGraph.Walk.length_append, hspec]
      rw [take_eq hqz] at hlen_eq
      have hdrop_zero : ((P q).dropUntil z hqz).length = 0 := by omega
      exact SimpleGraph.Walk.eq_of_length_eq_zero hdrop_zero
    have desc_antisymm : ∀ {z₁ z₂ : N}, IsDescendant G rt z₁ z₂ → IsDescendant G rt z₂ z₁ → z₁ = z₂ := by
      intro z₁ z₂ h₁₂ h₂₁
      have h₁₂' := (desc_iff z₁ z₂).mp h₁₂
      have hspec := SimpleGraph.Walk.take_spec (P z₁) h₁₂'
      have hlen₁ : (P z₂).length ≤ (P z₁).length := by
        have hlen_eq : ((P z₁).takeUntil z₂ h₁₂').length + ((P z₁).dropUntil z₂ h₁₂').length = (P z₁).length := by
          rw [← SimpleGraph.Walk.length_append, hspec]
        rw [take_eq h₁₂'] at hlen_eq
        omega
      exact eq_of_desc_len_le h₂₁ hlen₁
    have walk_prefix_total : ∀ {u v : N} (p : G.Walk u v) {w₁ w₂ : N}
        (h₁ : w₁ ∈ p.support) (h₂ : w₂ ∈ p.support),
        w₁ ∈ (p.takeUntil w₂ h₂).support ∨ w₂ ∈ (p.takeUntil w₁ h₁).support := by
      intro u v p
      induction p with
      | nil =>
        intro w₁ w₂ h₁ h₂
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at h₁
        subst h₁
        exact Or.inl (SimpleGraph.Walk.start_mem_support _)
      | @cons u u' v hadj p' ih =>
        intro w₁ w₂ h₁ h₂
        by_cases hw₁ : u = w₁
        · subst hw₁
          exact Or.inl (SimpleGraph.Walk.start_mem_support _)
        · by_cases hw₂ : u = w₂
          · subst hw₂
            exact Or.inr (SimpleGraph.Walk.start_mem_support _)
          · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at h₁ h₂
            have h₁' : w₁ ∈ p'.support := h₁.resolve_left (Ne.symm hw₁)
            have h₂' : w₂ ∈ p'.support := h₂.resolve_left (Ne.symm hw₂)
            rw [SimpleGraph.Walk.takeUntil_cons h₂' hw₂, SimpleGraph.Walk.takeUntil_cons h₁' hw₁]
            rcases ih h₁' h₂' with hleft | hright
            · exact Or.inl (List.mem_cons_of_mem u hleft)
            · exact Or.inr (List.mem_cons_of_mem u hright)
    have anc_total : ∀ {x w₁ w₂ : N}, IsDescendant G rt x w₁ → IsDescendant G rt x w₂ →
        IsDescendant G rt w₂ w₁ ∨ IsDescendant G rt w₁ w₂ := by
      intro x w₁ w₂ h₁ h₂
      rw [desc_iff] at h₁ h₂ ⊢
      rw [desc_iff]
      rcases walk_prefix_total (P x) h₁ h₂ with hl | hr
      · rw [take_eq h₂] at hl; exact Or.inl hl
      · rw [take_eq h₁] at hr; exact Or.inr hr
    intro x y z
    have h_ex : ∃ z₀ : N, IsLCA G rt x y z₀ := by
      let S : Finset N := (P x).support.toFinset ∩ (P y).support.toFinset
      have hrt_S : rt ∈ S := by
        simp only [S, Finset.mem_inter, List.mem_toFinset]
        exact ⟨SimpleGraph.Walk.start_mem_support _, SimpleGraph.Walk.start_mem_support _⟩
      obtain ⟨z₀, hz₀_S, hz₀_max⟩ := Finset.exists_max_image S (fun w => (P w).length) ⟨rt, hrt_S⟩
      simp only [S, Finset.mem_inter, List.mem_toFinset] at hz₀_S
      have hxz₀ : IsDescendant G rt x z₀ := (desc_iff x z₀).mpr hz₀_S.1
      have hyz₀ : IsDescendant G rt y z₀ := (desc_iff y z₀).mpr hz₀_S.2
      refine ⟨z₀, hxz₀, hyz₀, ?_⟩
      intro w hxw hyw
      have hw_S : w ∈ S := by
        simp only [S, Finset.mem_inter, List.mem_toFinset]
        exact ⟨(desc_iff x w).mp hxw, (desc_iff y w).mp hyw⟩
      have hlen_le : (P w).length ≤ (P z₀).length := hz₀_max w hw_S
      rcases anc_total hxz₀ hxw with hwz₀ | hz₀w
      · have heq : z₀ = w := eq_of_desc_len_le hwz₀ hlen_le
        subst heq
        exact desc_refl z₀
      · exact hz₀w
    have h_uniq : ∀ {z₁ z₂ : N}, IsLCA G rt x y z₁ → IsLCA G rt x y z₂ → z₁ = z₂ := by
      intro z₁ z₂ h₁ h₂
      exact desc_antisymm (h₁.2.2 z₂ h₂.1 h₂.2.1) (h₂.2.2 z₁ h₁.1 h₁.2.1)
    have h_lca_choose : IsLCA G rt x y (rootedLCA G rt x y) := by
      have h_eq : rootedLCA G rt x y = Classical.choose h_ex := by
        unfold rootedLCA
        exact dif_pos h_ex
      rw [h_eq]
      exact Classical.choose_spec h_ex
    constructor
    · rintro rfl
      exact h_lca_choose
    · intro hz
      exact h_uniq h_lca_choose hz

  
  have h_glue : ∀ (ι : Type) [Finite ι] [Nonempty ι] (V : ι → Type)
      (U : ∀ i : ι, HST (V i)) (L : ENNReal),
      L ≠ 0 → (∀ i : ι, (U i).label (U i).root ≤ L) →
      ∃ G : HST (Σ i : ι, V i),
        G.label G.root = L ∧
        (∀ (i : ι) (u v : V i), G.dist ⟨i, u⟩ ⟨i, v⟩ = (U i).dist u v) ∧
        (∀ (i j : ι) (u : V i) (v : V j), i ≠ j → G.dist ⟨i, u⟩ ⟨j, v⟩ = L) := by
    intro ι hι_fin hι_ne V U L hL_ne hL_ge
    letI : ∀ i : ι, Finite (U i).Node := fun i => (U i).finiteNode
    let Node := Option (Σ i : ι, (U i).Node)
    have hNode_fin : Finite Node := inferInstance
    let glueAdj : Node → Node → Prop := fun a b =>
      match a, b with
      | none, none => False
      | none, some ⟨i, x⟩ => x = (U i).root
      | some ⟨i, x⟩, none => x = (U i).root
      | some ⟨i, x⟩, some ⟨j, y⟩ => ∃ h : i = j, (U i).tree.Adj x (h ▸ y)
    let tree : SimpleGraph Node :=
      { Adj := glueAdj
        symm := by
          intro a b hab
          rcases a with _ | ⟨i, x⟩ <;> rcases b with _ | ⟨j, y⟩
          · exact False.elim hab
          · exact hab
          · exact hab
          · rcases hab with ⟨rfl, h⟩
            exact ⟨rfl, (U i).tree.symm h⟩
        loopless := by
          intro a ha
          rcases a with _ | ⟨i, x⟩
          · exact ha
          · rcases ha with ⟨_, h⟩
            exact (U i).tree.loopless x h }
    let emb : ∀ i : ι, (U i).tree →g tree := fun i =>
      { toFun := fun x => some ⟨i, x⟩
        map_rel' := fun h => ⟨rfl, h⟩ }
    have hemb_inj : ∀ i : ι, Function.Injective (emb i) := by
      intro i x y hxy
      change (some (⟨i, x⟩ : Σ k, (U k).Node)) = some ⟨i, y⟩ at hxy
      injection hxy with hsig
      exact eq_of_heq (Sigma.mk.inj hsig).2
    let P_child : ∀ (i : ι) (x : (U i).Node), (U i).tree.Walk (U i).root x :=
      fun i x => Classical.choose (((U i).isTree).existsUnique_path (U i).root x)
    have hP_child_spec : ∀ (i : ι) (x : (U i).Node),
        (P_child i x).IsPath ∧ ∀ p : (U i).tree.Walk (U i).root x, p.IsPath → p = P_child i x :=
      fun i x => Classical.choose_spec (((U i).isTree).existsUnique_path (U i).root x)
    let rootPath : ∀ w : Node, tree.Walk none w := fun w =>
      match w with
      | none => SimpleGraph.Walk.nil
      | some ⟨i, x⟩ =>
        SimpleGraph.Walk.cons (rfl : tree.Adj none (some ⟨i, (U i).root⟩))
          ((P_child i x).map (emb i))
    have h_rootPath_isPath : ∀ w : Node, (rootPath w).IsPath := by
      intro w
      rcases w with _ | ⟨i, x⟩
      · exact SimpleGraph.Walk.IsPath.nil
      · change (SimpleGraph.Walk.cons _ ((P_child i x).map (emb i))).IsPath
        rw [SimpleGraph.Walk.cons_isPath_iff]
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
          exact ((hP_child_spec i x).1.support_nodup).map (hemb_inj i)
        · rw [SimpleGraph.Walk.support_map]
          rintro hmem
          rcases List.mem_map.mp hmem with ⟨z, _, hz⟩
          simp [emb] at hz
    have h_conn : tree.Connected :=
      { preconnected := fun a b => ⟨(rootPath a).reverse.append (rootPath b)⟩
        nonempty := ⟨none⟩ }
    have walk_decomp : ∀ {u v : Node} (w : tree.Walk u v), 0 < w.length →
        ∃ (b : Node) (hadj : tree.Adj u b) (q : tree.Walk b v),
          w.length = q.length + 1 ∧ w.support = u :: q.support := by
      rintro u v (_ | ⟨hadj, q⟩) hlen
      · simp at hlen
      · exact ⟨_, hadj, q, rfl, rfl⟩
    have lift_walk : ∀ {u v : Node} (w : tree.Walk u v), none ∉ w.support →
        ∀ (i : ι) (x : (U i).Node), u = some ⟨i, x⟩ →
          ∃ (y : (U i).Node) (w₀ : (U i).tree.Walk x y),
            v = some ⟨i, y⟩ ∧ w.length = w₀.length ∧ w.support = w₀.support.map (emb i) := by
      intro u v w
      induction w with
      | nil =>
        intro _ i x hu
        subst hu
        exact ⟨x, SimpleGraph.Walk.nil, rfl, rfl, rfl⟩
      | @cons u u' v hadj w' ih =>
        intro h_none i x hu
        subst hu
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at h_none
        have hu'_mem : u' ∈ w'.support := SimpleGraph.Walk.start_mem_support w'
        rcases u' with _ | ⟨j, x'⟩
        · exact False.elim (h_none.2 hu'_mem)
        · rcases hadj with ⟨rfl, h₀⟩
          obtain ⟨y, w₀', hv, hlen, hsupp⟩ := ih h_none.2 i x' rfl
          refine ⟨y, SimpleGraph.Walk.cons h₀ w₀', hv, ?_, ?_⟩
          · simp [hlen]
          · simp [hsupp, emb]
    have h_acyc : tree.IsAcyclic := by
      classical
      intro a c hc
      by_cases hm : none ∈ c.support
      · let c' : tree.Walk none none := c.rotate hm
        have hc' : c'.IsCycle := hc.rotate hm
        have h3 : 3 ≤ c'.length := hc'.three_le_length
        have hnodup_c' : c'.support.tail.Nodup := hc'.support_nodup
        obtain ⟨b₁, hadj₁, q, hc'_len, hc'_supp⟩ := walk_decomp c' (by omega)
        have hq_nodup : q.support.Nodup := by
          rw [hc'_supp] at hnodup_c'
          exact hnodup_c'
        rcases b₁ with _ | ⟨i, x₁⟩
        · exact False.elim hadj₁
        · change x₁ = (U i).root at hadj₁
          subst hadj₁
          have hqr_pos : 0 < q.reverse.length := by
            rw [SimpleGraph.Walk.length_reverse]
            omega
          obtain ⟨b₂, hadj₂, p_rev, hqr_len, hqr_supp⟩ := walk_decomp q.reverse hqr_pos
          have hqr_nodup : q.reverse.support.Nodup := by
            rw [SimpleGraph.Walk.support_reverse]
            exact List.nodup_reverse.mpr hq_nodup
          rw [hqr_supp, List.nodup_cons] at hqr_nodup
          rcases b₂ with _ | ⟨j, x₂⟩
          · exact False.elim hadj₂
          · change x₂ = (U j).root at hadj₂
            subst hadj₂
            obtain ⟨y, _, h_end, _, _⟩ := lift_walk p_rev hqr_nodup.1 j (U j).root rfl
            have hij : i = j := by
              injection h_end with hsig
              exact (Sigma.mk.inj hsig).1
            subst hij
            have hp_path : p_rev.IsPath := by
              rw [SimpleGraph.Walk.isPath_def]
              exact hqr_nodup.2
            have hp_nil : p_rev = SimpleGraph.Walk.nil :=
              (SimpleGraph.Walk.isPath_iff_eq_nil p_rev).mp hp_path
            have hp_len : p_rev.length = 0 := by simp [hp_nil]
            have hq_len : q.length = 1 := by
              have := SimpleGraph.Walk.length_reverse q
              omega
            omega
      · have ha_mem : a ∈ c.support := SimpleGraph.Walk.start_mem_support c
        rcases a with _ | ⟨i, x⟩
        · exact False.elim (hm ha_mem)
        · have h3 : 3 ≤ c.length := hc.three_le_length
          have hnodup_c : c.support.tail.Nodup := hc.support_nodup
          obtain ⟨b, hadj, q, hc_len, hc_supp⟩ := walk_decomp c (by omega)
          have hq_nodup : q.support.Nodup := by
            rw [hc_supp] at hnodup_c
            exact hnodup_c
          have hq_none : none ∉ q.support := by
            intro hmem
            apply hm
            rw [hc_supp]
            exact List.mem_cons_of_mem _ hmem
          have hb_mem : b ∈ q.support := SimpleGraph.Walk.start_mem_support q
          rcases b with _ | ⟨j, z⟩
          · exact False.elim (hq_none hb_mem)
          · rcases hadj with ⟨rfl, h₀⟩
            obtain ⟨y, q₀, h_end, hlen_q, hsupp_q⟩ := lift_walk q hq_none i z rfl
            have hxy : x = y := hemb_inj i h_end
            subst hxy
            rw [hsupp_q] at hq_nodup
            have hq₀_path : q₀.IsPath := by
              rw [SimpleGraph.Walk.isPath_def]
              exact List.Nodup.of_map (emb i) hq_nodup
            let e_back : (U i).tree.Walk z x := ((U i).tree.symm h₀).toWalk
            have he_path : e_back.IsPath := SimpleGraph.Walk.IsPath.of_adj _
            have h_uniq_zx := ((U i).isTree).existsUnique_path z x
            obtain ⟨p_zx, _, hp_zx_uniq⟩ := h_uniq_zx
            have hq₀_eq : q₀ = e_back :=
              (hp_zx_uniq q₀ hq₀_path).trans (hp_zx_uniq e_back he_path).symm
            have hq₀_len : q₀.length = 1 := by simp [hq₀_eq, e_back]
            omega
    have h_isTree : tree.IsTree := (SimpleGraph.isTree_iff tree).mpr ⟨h_conn, h_acyc⟩
    have desc_tree_iff : ∀ w z : Node, IsDescendant tree none w z ↔ z ∈ (rootPath w).support := by
      intro w z
      obtain ⟨p₀, _, hp₀_uniq⟩ := h_isTree.existsUnique_path none w
      have hrp_eq : rootPath w = p₀ := hp₀_uniq (rootPath w) (h_rootPath_isPath w)
      constructor
      · rintro ⟨p, hp, hz⟩
        have hp_eq : p = rootPath w := (hp₀_uniq p hp).trans hrp_eq.symm
        rwa [hp_eq] at hz
      · intro hz
        exact ⟨rootPath w, h_rootPath_isPath w, hz⟩
    have desc_child_iff : ∀ (i : ι) (x y : (U i).Node),
        IsDescendant (U i).tree (U i).root x y ↔ y ∈ (P_child i x).support := by
      intro i x y
      constructor
      · rintro ⟨p, hp, hy⟩
        rwa [(hP_child_spec i x).2 p hp] at hy
      · intro hy
        exact ⟨P_child i x, (hP_child_spec i x).1, hy⟩
    have desc_none_iff : ∀ z : Node, IsDescendant tree none none z ↔ z = none := by
      intro z
      rw [desc_tree_iff]
      simp [rootPath]
    have desc_some_none : ∀ (i : ι) (x : (U i).Node), IsDescendant tree none (some ⟨i, x⟩) none := by
      intro i x
      rw [desc_tree_iff]
      simp [rootPath]
    have desc_some_eq_idx : ∀ {i j : ι} {x : (U i).Node} {y : (U j).Node},
        IsDescendant tree none (some ⟨i, x⟩) (some ⟨j, y⟩) → i = j := by
      intro i j x y h
      rw [desc_tree_iff] at h
      simp only [rootPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_map,
        List.mem_cons, reduceCtorEq, false_or, List.mem_map] at h
      rcases h with ⟨y', _, hy'⟩
      change (some (⟨i, y'⟩ : Σ k, (U k).Node)) = some ⟨j, y⟩ at hy'
      injection hy' with hsig
      exact (Sigma.mk.inj hsig).1
    have desc_some_same_iff : ∀ (i : ι) (x y : (U i).Node),
        IsDescendant tree none (some ⟨i, x⟩) (some ⟨i, y⟩) ↔
          IsDescendant (U i).tree (U i).root x y := by
      intro i x y
      rw [desc_tree_iff, desc_child_iff]
      simp only [rootPath, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_map,
        List.mem_cons, reduceCtorEq, false_or, List.mem_map]
      constructor
      · rintro ⟨y', hy', h_eq⟩
        have hy'y : y' = y := hemb_inj i h_eq
        rwa [← hy'y]
      · intro hy
        exact ⟨y, hy, rfl⟩
    have h_not_leaf_none : ¬ IsRootedLeaf tree none none := by
      obtain ⟨i₀⟩ := hι_ne
      intro hl
      have h_eq := hl (some ⟨i₀, (U i₀).root⟩) (desc_some_none i₀ (U i₀).root)
      simp at h_eq
    have leaf_some_iff : ∀ (i : ι) (x : (U i).Node),
        IsRootedLeaf tree none (some ⟨i, x⟩) ↔ IsRootedLeaf (U i).tree (U i).root x := by
      intro i x
      constructor
      · intro hl w hw
        have h_eq := hl (some ⟨i, w⟩) ((desc_some_same_iff i w x).mpr hw)
        exact hemb_inj i h_eq
      · intro hl w hw
        rcases w with _ | ⟨j, w₀⟩
        · have h_eq := (desc_none_iff (some ⟨i, x⟩)).mp hw
          simp at h_eq
        · have hij : j = i := desc_some_eq_idx hw
          subst hij
          have hw₀ : w₀ = x := hl w₀ ((desc_some_same_iff j w₀ x).mp hw)
          rw [hw₀]
    let leafEquiv : (Σ i : ι, V i) ≃ {q : Node // IsRootedLeaf tree none q} :=
      { toFun := fun p =>
          ⟨some ⟨p.1, ((U p.1).leafEquiv p.2).1⟩,
           (leaf_some_iff p.1 _).mpr ((U p.1).leafEquiv p.2).2⟩
        invFun := fun q =>
          match q with
          | ⟨none, hq⟩ => False.elim (h_not_leaf_none hq)
          | ⟨some ⟨i, x⟩, hq⟩ => ⟨i, (U i).leafEquiv.symm ⟨x, (leaf_some_iff i x).mp hq⟩⟩
        left_inv := by
          rintro ⟨i, u⟩
          simp
        right_inv := by
          rintro ⟨q, hq⟩
          rcases q with _ | ⟨i, x⟩
          · exact False.elim (h_not_leaf_none hq)
          · apply Subtype.ext
            simp }
    let label : Node → ENNReal := fun q =>
      match q with
      | none => L
      | some ⟨i, x⟩ => (U i).label x
    have h_label_mono : ∀ q z : Node, IsDescendant tree none q z → label q ≤ label z := by
      intro q z hqz
      rcases q with _ | ⟨i, x⟩
      · have hz := (desc_none_iff z).mp hqz
        subst hz
        exact le_rfl
      · rcases z with _ | ⟨j, y⟩
        · have h_rt : IsDescendant (U i).tree (U i).root x (U i).root := by
            rw [desc_child_iff]
            exact SimpleGraph.Walk.start_mem_support _
          exact le_trans ((U i).label_mono x (U i).root h_rt) (hL_ge i)
        · have hij : i = j := desc_some_eq_idx hqz
          subst hij
          exact (U i).label_mono x y ((desc_some_same_iff i x y).mp hqz)
    have h_label_zero : ∀ q : Node, label q = 0 ↔ IsRootedLeaf tree none q := by
      intro q
      rcases q with _ | ⟨i, x⟩
      · exact ⟨fun h => False.elim (hL_ne h), fun h => False.elim (h_not_leaf_none h)⟩
      · exact ((U i).label_eq_zero_iff x).trans (leaf_some_iff i x).symm
    let G : HST (Σ i : ι, V i) :=
      { Node := Node
        finiteNode := hNode_fin
        tree := tree
        isTree := h_isTree
        root := none
        leafEquiv := leafEquiv
        label := label
        label_mono := h_label_mono
        label_eq_zero_iff := h_label_zero }
    refine ⟨G, rfl, ?_, ?_⟩
    · intro i u v
      let q₁ := ((U i).leafEquiv u).1
      let q₂ := ((U i).leafEquiv v).1
      let z₀ := rootedLCA (U i).tree (U i).root q₁ q₂
      have hz₀ : IsLCA (U i).tree (U i).root q₁ q₂ z₀ :=
        (h_lca_iff _ _ (U i).isTree (U i).root q₁ q₂ z₀).mp rfl
      have hlca_G : IsLCA tree none (some ⟨i, q₁⟩) (some ⟨i, q₂⟩) (some ⟨i, z₀⟩) := by
        refine ⟨(desc_some_same_iff i q₁ z₀).mpr hz₀.1,
                (desc_some_same_iff i q₂ z₀).mpr hz₀.2.1, ?_⟩
        intro w hw₁ hw₂
        rcases w with _ | ⟨j, y⟩
        · exact desc_some_none i z₀
        · have hij : i = j := desc_some_eq_idx hw₁
          subst hij
          exact (desc_some_same_iff i z₀ y).mpr
            (hz₀.2.2 y ((desc_some_same_iff i q₁ y).mp hw₁) ((desc_some_same_iff i q₂ y).mp hw₂))
      have hr_eq : rootedLCA tree none (some ⟨i, q₁⟩) (some ⟨i, q₂⟩) = some ⟨i, z₀⟩ :=
        (h_lca_iff _ _ h_isTree none (some ⟨i, q₁⟩) (some ⟨i, q₂⟩) (some ⟨i, z₀⟩)).mpr hlca_G
      change G.label (rootedLCA tree none (some ⟨i, q₁⟩) (some ⟨i, q₂⟩)) = (U i).label z₀
      rw [hr_eq]
    · intro i j u v hij
      let q₁ := ((U i).leafEquiv u).1
      let q₂ := ((U j).leafEquiv v).1
      have hlca_G : IsLCA tree none (some ⟨i, q₁⟩) (some ⟨j, q₂⟩) none := by
        refine ⟨desc_some_none i q₁, desc_some_none j q₂, ?_⟩
        intro w hw₁ hw₂
        rcases w with _ | ⟨r, y⟩
        · exact (desc_none_iff none).mpr rfl
        · have hir : i = r := desc_some_eq_idx hw₁
          have hjr : j = r := desc_some_eq_idx hw₂
          exact False.elim (hij (hir.trans hjr.symm))
      have hr_eq : rootedLCA tree none (some ⟨i, q₁⟩) (some ⟨j, q₂⟩) = none :=
        (h_lca_iff _ _ h_isTree none (some ⟨i, q₁⟩) (some ⟨j, q₂⟩) none).mpr hlca_G
      change G.label (rootedLCA tree none (some ⟨i, q₁⟩) (some ⟨j, q₂⟩)) = L
      rw [hr_eq]

  
  have h_dist_diag : ∀ (t : RawHST W) (w : W), t.dist w w = 0 := by
    intro t w
    cases t with
    | leaf _ => rfl
    | node _ _ _ => simp [RawHST.dist]
  have h_valid_go : ∀ (cs : List (RawHST W)), ValidRawHST.go cs → ∀ c ∈ cs, ValidRawHST c := by
    intro cs
    induction cs with
    | nil =>
      intro _ c hc
      exact False.elim (List.not_mem_nil hc)
    | cons c cs' ih =>
      intro h c' hc'
      rcases List.mem_cons.mp hc' with rfl | hmem
      · exact h.1
      · exact ih h.2 c' hmem
  have h_foldr_mem : ∀ (cs : List (RawHST W)) (w : W),
      w ∈ cs.foldr (fun c acc => c.cluster ∪ acc) ∅ ↔ ∃ c ∈ cs, w ∈ c.cluster := by
    intro cs w
    induction cs with
    | nil => simp
    | cons c cs' ih =>
      simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]
  have h_go_same : ∀ (w₁ w₂ : W) (Δ : ℝ) (cs : List (RawHST W)),
      cs.Pairwise (fun c₁ c₂ => Disjoint c₁.cluster c₂.cluster) →
      ∀ (idx : Fin cs.length), w₁ ∈ (cs.get idx).cluster → w₂ ∈ (cs.get idx).cluster →
        RawHST.dist.go w₁ w₂ Δ cs = (cs.get idx).dist w₁ w₂ := by
    intro w₁ w₂ Δ cs
    induction cs with
    | nil =>
      intro _ idx
      exact idx.elim0
    | cons c cs' ih =>
      intro hpw idx
      obtain ⟨hd, htl⟩ := List.pairwise_cons.mp hpw
      refine Fin.cases ?_ ?_ idx
      · intro hw₁ hw₂
        change w₁ ∈ c.cluster at hw₁
        change w₂ ∈ c.cluster at hw₂
        change RawHST.dist.go w₁ w₂ Δ (c :: cs') = c.dist w₁ w₂
        simp [RawHST.dist.go, hw₁, hw₂]
      · intro k hw₁ hw₂
        change w₁ ∈ (cs'.get k).cluster at hw₁
        change w₂ ∈ (cs'.get k).cluster at hw₂
        change RawHST.dist.go w₁ w₂ Δ (c :: cs') = (cs'.get k).dist w₁ w₂
        have hk_mem : cs'.get k ∈ cs' := List.get_mem cs' k
        have hdisj : Disjoint c.cluster (cs'.get k).cluster := hd _ hk_mem
        have hw₁_not : w₁ ∉ c.cluster := Finset.disjoint_right.mp hdisj hw₁
        have h_cond : ¬ (w₁ ∈ c.cluster ∧ w₂ ∈ c.cluster) := fun h => hw₁_not h.1
        simp only [RawHST.dist.go, h_cond, ↓reduceIte]
        exact ih htl k hw₁ hw₂
  have h_go_diff : ∀ (w₁ w₂ : W) (Δ : ℝ) (cs : List (RawHST W)),
      (∀ c ∈ cs, ¬ (w₁ ∈ c.cluster ∧ w₂ ∈ c.cluster)) →
      RawHST.dist.go w₁ w₂ Δ cs = Δ := by
    intro w₁ w₂ Δ cs
    induction cs with
    | nil =>
      intro _
      rfl
    | cons c cs' ih =>
      intro hno
      have hc : ¬ (w₁ ∈ c.cluster ∧ w₂ ∈ c.cluster) := hno c List.mem_cons_self
      simp only [RawHST.dist.go, hc, ↓reduceIte]
      exact ih (fun c' hc' => hno c' (List.mem_cons_of_mem c hc'))
  have h_raw_node : ∀ (X : Finset W) (Δ : ℝ) (children : List (RawHST W)),
      ValidRawHST (RawHST.node X Δ children) →
      0 < Δ ∧ 0 < children.length ∧
      (∀ i : Fin children.length, ValidRawHST (children.get i) ∧ (children.get i).topLabel ≤ Δ) ∧
      (∃ e : (Σ i : Fin children.length, {w : W // w ∈ (children.get i).cluster}) ≃ {w : W // w ∈ X},
        ∀ (i : Fin children.length) (u : {w : W // w ∈ (children.get i).cluster}), (e ⟨i, u⟩).1 = u.1) ∧
      (∀ (i : Fin children.length) (u v : {w : W // w ∈ (children.get i).cluster}),
        (RawHST.node X Δ children).dist u.1 v.1 = (children.get i).dist u.1 v.1) ∧
      (∀ (i j : Fin children.length) (u : {w : W // w ∈ (children.get i).cluster})
        (v : {w : W // w ∈ (children.get j).cluster}),
        i ≠ j → (RawHST.node X Δ children).dist u.1 v.1 = Δ) := by
    intro X Δ children hv
    rcases hv with ⟨hΔ, hne, hvgo, hprops, hdisj_map, hunion⟩
    have hlen_pos : 0 < children.length := List.length_pos_of_ne_nil hne
    have hpw : children.Pairwise (fun c₁ c₂ => Disjoint c₁.cluster c₂.cluster) :=
      List.pairwise_map.mp hdisj_map
    have hpw_get : ∀ {i j : Fin children.length}, i ≠ j →
        Disjoint (children.get i).cluster (children.get j).cluster := by
      intro i j hij
      have h_lt := List.pairwise_iff_get.mp hpw
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact h_lt i j hlt
      · exact (h_lt j i hgt).symm
    have hchild : ∀ i : Fin children.length,
        ValidRawHST (children.get i) ∧ (children.get i).topLabel ≤ Δ := by
      intro i
      have hmem : children.get i ∈ children := List.get_mem children i
      exact ⟨h_valid_go children hvgo _ hmem, (hprops _ hmem).1⟩
    have hmem_X_iff : ∀ w : W, w ∈ X ↔ ∃ i : Fin children.length, w ∈ (children.get i).cluster := by
      intro w
      rw [← hunion, h_foldr_mem]
      constructor
      · rintro ⟨c, hc, hw⟩
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
        exact ⟨i, hw⟩
      · rintro ⟨i, hw⟩
        exact ⟨children.get i, List.get_mem children i, hw⟩
    let toX : (Σ i : Fin children.length, {w : W // w ∈ (children.get i).cluster}) → {w : W // w ∈ X} :=
      fun p => ⟨p.2.1, (hmem_X_iff p.2.1).mpr ⟨p.1, p.2.2⟩⟩
    have h_bij : Function.Bijective toX := by
      constructor
      · rintro ⟨i, ⟨w₁, hw₁⟩⟩ ⟨j, ⟨w₂, hw₂⟩⟩ h_eq
        have hw_eq : w₁ = w₂ := congrArg Subtype.val h_eq
        subst hw_eq
        have hij : i = j := by
          by_contra hne_ij
          exact Finset.disjoint_left.mp (hpw_get hne_ij) hw₁ hw₂
        subst hij
        rfl
      · rintro ⟨w, hw⟩
        obtain ⟨i, hi⟩ := (hmem_X_iff w).mp hw
        exact ⟨⟨i, ⟨w, hi⟩⟩, rfl⟩
    let e := Equiv.ofBijective toX h_bij
    refine ⟨hΔ, hlen_pos, hchild, ⟨e, fun _ _ => rfl⟩, ?_, ?_⟩
    · intro i u v
      by_cases huv : u.1 = v.1
      · rw [huv, h_dist_diag, h_dist_diag]
      · simp only [RawHST.dist, huv, ↓reduceIte]
        exact h_go_same u.1 v.1 Δ children hpw i u.2 v.2
    · intro i j u v hij
      have huv_ne : u.1 ≠ v.1 := by
        intro heq
        have hv_in : u.1 ∈ (children.get j).cluster := heq ▸ v.2
        exact Finset.disjoint_left.mp (hpw_get hij) u.2 hv_in
      simp only [RawHST.dist, huv_ne, ↓reduceIte]
      apply h_go_diff u.1 v.1 Δ children
      intro c hc ⟨hu_c, hv_c⟩
      obtain ⟨r, rfl⟩ := List.mem_iff_get.mp hc
      have hri : r = i := by
        by_contra hne_ri
        exact Finset.disjoint_left.mp (hpw_get hne_ri) hu_c u.2
      have hrj : r = j := by
        by_contra hne_rj
        exact Finset.disjoint_left.mp (hpw_get hne_rj) hv_c v.2
      exact hij (hri.symm.trans hrj)

  
  let motive₁ : RawHST W → Prop := fun t =>
    ValidRawHST t →
      ∃ U : HST {w : W // w ∈ t.cluster},
        U.label U.root = ENNReal.ofReal t.topLabel ∧
        ∀ x y : {w : W // w ∈ t.cluster}, U.dist x y = ENNReal.ofReal (t.dist x.1 y.1)
  let motive₂ : List (RawHST W) → Prop := fun cs => ∀ c ∈ cs, motive₁ c
  have h_main : motive₁ T := by
    refine @RawHST.rec W motive₁ motive₂ ?_ ?_ ?_ ?_ T
    · 
      intro X hX
      obtain ⟨w₀, rfl⟩ := Finset.card_eq_one.mp hX
      have h_bot_tree : (⊥ : SimpleGraph PUnit).IsTree := by
        rw [SimpleGraph.isTree_iff]
        refine ⟨?_, ?_⟩
        · exact { preconnected := fun a b => ⟨Subsingleton.elim a b ▸ SimpleGraph.Walk.nil⟩
                  nonempty := ⟨PUnit.unit⟩ }
        · intro a c hc
          have h3 := hc.three_le_length
          cases c with
          | nil => simp at h3
          | cons hadj _ => exact False.elim hadj
      have h_unit_leaf : IsRootedLeaf (⊥ : SimpleGraph PUnit) PUnit.unit PUnit.unit :=
        fun w _ => Subsingleton.elim w PUnit.unit
      let U_leaf : HST {w : W // w ∈ ({w₀} : Finset W)} :=
        { Node := PUnit
          finiteNode := inferInstance
          tree := ⊥
          isTree := h_bot_tree
          root := PUnit.unit
          leafEquiv :=
            { toFun := fun _ => ⟨PUnit.unit, h_unit_leaf⟩
              invFun := fun _ => ⟨w₀, Finset.mem_singleton_self w₀⟩
              left_inv := fun ⟨w, hw⟩ => Subtype.ext (Finset.mem_singleton.mp hw).symm
              right_inv := fun ⟨u, _⟩ => Subtype.ext (Subsingleton.elim PUnit.unit u) }
          label := fun _ => 0
          label_mono := fun _ _ _ => le_rfl
          label_eq_zero_iff := fun q =>
            ⟨fun _ w _ => Subsingleton.elim w q, fun _ => rfl⟩ }
      refine ⟨U_leaf, ?_, ?_⟩
      · simp [U_leaf, RawHST.topLabel]
      · intro x y
        simp [U_leaf, HST.dist, RawHST.dist]
    · 
      intro X Δ children ih_cs hv
      obtain ⟨hΔ, hlen_pos, hchild, ⟨e, he_val⟩, hsame, hdiff⟩ := h_raw_node X Δ children hv
      let ι := Fin children.length
      haveI : Nonempty ι := ⟨⟨0, hlen_pos⟩⟩
      have h_ex : ∀ i : ι, ∃ U_i : HST {w : W // w ∈ (children.get i).cluster},
          U_i.label U_i.root = ENNReal.ofReal (children.get i).topLabel ∧
          ∀ u v : {w : W // w ∈ (children.get i).cluster},
            U_i.dist u v = ENNReal.ofReal ((children.get i).dist u.1 v.1) :=
        fun i => ih_cs (children.get i) (List.get_mem children i) (hchild i).1
      let U_fam : ∀ i : ι, HST {w : W // w ∈ (children.get i).cluster} :=
        fun i => Classical.choose (h_ex i)
      have hU_fam : ∀ i : ι,
          (U_fam i).label (U_fam i).root = ENNReal.ofReal (children.get i).topLabel ∧
          ∀ u v : {w : W // w ∈ (children.get i).cluster},
            (U_fam i).dist u v = ENNReal.ofReal ((children.get i).dist u.1 v.1) :=
        fun i => Classical.choose_spec (h_ex i)
      have hL_ne : ENNReal.ofReal Δ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hΔ)
      have hL_ge : ∀ i : ι, (U_fam i).label (U_fam i).root ≤ ENNReal.ofReal Δ := by
        intro i
        rw [(hU_fam i).1]
        exact ENNReal.ofReal_le_ofReal (hchild i).2
      obtain ⟨G, hG_root, hG_same, hG_diff⟩ :=
        h_glue ι (fun i => {w : W // w ∈ (children.get i).cluster}) U_fam (ENNReal.ofReal Δ)
          hL_ne hL_ge
      let U_node : HST {w : W // w ∈ X} :=
        { G with leafEquiv := e.symm.trans G.leafEquiv }
      refine ⟨U_node, hG_root, ?_⟩
      intro x y
      change G.dist (e.symm x) (e.symm y) = ENNReal.ofReal ((RawHST.node X Δ children).dist x.1 y.1)
      rcases hx : e.symm x with ⟨i, u⟩
      rcases hy : e.symm y with ⟨j, v⟩
      have hx_val : x.1 = u.1 := by
        have h1 : e (e.symm x) = e ⟨i, u⟩ := congrArg e hx
        rw [e.apply_symm_apply] at h1
        exact (congrArg Subtype.val h1).trans (he_val i u)
      have hy_val : y.1 = v.1 := by
        have h1 : e (e.symm y) = e ⟨j, v⟩ := congrArg e hy
        rw [e.apply_symm_apply] at h1
        exact (congrArg Subtype.val h1).trans (he_val j v)
      rw [hx_val, hy_val]
      by_cases hij : i = j
      · subst hij
        rw [hG_same i u v, (hU_fam i).2 u v, hsame i u v]
      · rw [hG_diff i j u v hij, hdiff i j u v hij]
    · 
      intro c hc
      exact False.elim (List.not_mem_nil hc)
    · 
      intro c cs ih_c ih_cs c' hc'
      rcases List.mem_cons.mp hc' with rfl | hmem
      · exact ih_c
      · exact ih_cs c' hmem
  obtain ⟨U₀, hU₀_root, hU₀_dist⟩ := h_main hT
  let e_univ : W ≃ {w : W // w ∈ T.cluster} :=
    { toFun := fun w => ⟨w, h_univ ▸ Finset.mem_univ w⟩
      invFun := fun x => x.1
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  refine ⟨{ U₀ with leafEquiv := e_univ.trans U₀.leafEquiv }, hU₀_root, ?_⟩
  intro u v
  exact hU₀_dist (e_univ u) (e_univ v)

theorem ssp_and_hse_deterministic (N n : ℕ) (hn : 2 ≤ n) (hnN : n ≤ N)
    (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 2 ≤ w e)
    (h : ℕ) (hh : 1 ≤ h)
    (Φ : ℝ) (hΦ_ge : 2 ≤ Φ)
    (hΦ_diam : ∀ u v : Fin n, hopDist G w h u v ≤ ENNReal.ofReal Φ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (h_params : HSTParamSpec N Φ ε) :
    SSPDetSpec N n G w h Φ ε ∧ HSERunDetSpec N n G w h Φ ε :=
by
  have _ : 2 ≤ n ∧ 1 ≤ h := ⟨hn, hh⟩
  
  
  
  have walkWeight_nonneg : ∀ {u v : Fin n} (p : G.Walk u v), 0 ≤ walkWeight w p := by
    intro u v p
    unfold walkWeight
    refine List.sum_nonneg ?_
    intro r hr
    rcases List.mem_map.mp hr with ⟨e, he, rfl⟩
    have he_edge : e ∈ G.edgeSet := p.edges_subset_edgeSet he
    linarith [hw e he_edge]

  have hopDist_self : ∀ (H : ℕ) (u : Fin n), hopDist G w H u u = 0 := by
    intro H u
    refine le_antisymm ?_ (zero_le _)
    unfold hopDist
    refine le_trans (iInf_le_of_le SimpleGraph.Walk.nil (iInf_le_of_le (Nat.zero_le H) le_rfl)) ?_
    simp [walkWeight]

  have hopDist_comm : ∀ (H : ℕ) (u v : Fin n), hopDist G w H u v = hopDist G w H v u := by
    have h_rev : ∀ (H : ℕ) (u v : Fin n), hopDist G w H v u ≤ hopDist G w H u v := by
      intro H u v
      unfold hopDist
      refine le_iInf₂ (fun p hp => ?_)
      have hlen : p.reverse.length ≤ H := by simpa [SimpleGraph.Walk.length_reverse] using hp
      have hw_rev : walkWeight w p.reverse = walkWeight w p := by
        simp only [walkWeight, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]
      refine le_trans (iInf_le_of_le p.reverse (iInf_le_of_le hlen le_rfl)) ?_
      rw [hw_rev]
    intro H u v
    exact le_antisymm (h_rev H v u) (h_rev H u v)

  have hopDist_anti : ∀ {H₁ H₂ : ℕ}, H₁ ≤ H₂ → ∀ u v : Fin n,
      hopDist G w H₂ u v ≤ hopDist G w H₁ u v := by
    intro H₁ H₂ hH u v
    unfold hopDist
    exact le_iInf₂ (fun p hp => iInf_le_of_le p (iInf_le_of_le (le_trans hp hH) le_rfl))

  have hopDist_add_le : ∀ (H₁ H₂ : ℕ) (x y z : Fin n),
      hopDist G w (H₁ + H₂) x z ≤ hopDist G w H₁ x y + hopDist G w H₂ y z := by
    intro H₁ H₂ x y z
    rw [hopDist, hopDist, hopDist]
    rw [ENNReal.iInf_add]
    refine le_iInf (fun p => ?_)
    rw [ENNReal.iInf_add]
    refine le_iInf (fun hp => ?_)
    rw [ENNReal.add_iInf]
    refine le_iInf (fun q => ?_)
    rw [ENNReal.add_iInf]
    refine le_iInf (fun hq => ?_)
    have hlen : (p.append q).length ≤ H₁ + H₂ := by
      rw [SimpleGraph.Walk.length_append]
      exact Nat.add_le_add hp hq
    have hw_eq : walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by
      simp only [walkWeight, SimpleGraph.Walk.edges_append, List.map_append, List.sum_append]
    refine le_trans (iInf_le_of_le (p.append q) (iInf_le_of_le hlen le_rfl)) ?_
    rw [hw_eq, ENNReal.ofReal_add (walkWeight_nonneg p) (walkWeight_nonneg q)]

  have two_le_hopDist : ∀ (H : ℕ) (u v : Fin n), u ≠ v →
      ENNReal.ofReal 2 ≤ hopDist G w H u v := by
    intro H u v huv
    unfold hopDist
    refine le_iInf₂ (fun p _ => ?_)
    cases p with
    | nil => exact absurd rfl huv
    | @cons _ w_next _ hadj p' =>
      have he : s(u, w_next) ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr hadj
      have hw1 : 2 ≤ w s(u, w_next) := hw _ he
      have hw2 : 0 ≤ walkWeight w p' := walkWeight_nonneg p'
      have hsum : 2 ≤ walkWeight w (SimpleGraph.Walk.cons hadj p') := by
        change 2 ≤ w s(u, w_next) + walkWeight w p'
        linarith
      exact ENNReal.ofReal_le_ofReal hsum

  have hopDist_toReal_bounds : ∀ u v : Fin n, u ≠ v →
      2 ≤ (hopDist G w h u v).toReal ∧ (hopDist G w h u v).toReal ≤ Φ := by
    intro u v huv
    have h_lo := two_le_hopDist h u v huv
    have h_hi := hΦ_diam u v
    have h_ne_top : hopDist G w h u v ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_hi
    constructor
    · have h1 := ENNReal.toReal_mono h_ne_top h_lo
      rwa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)] at h1
    · have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_hi
      rwa [ENNReal.toReal_ofReal (by linarith : 0 ≤ Φ)] at h2

  have mem_hstBall_iff : ∀ (Δ : ℝ) (X : Finset (Fin n)) (v : Fin n) (ℓ : ℕ) (R : ℤ) (u : Fin n),
      u ∈ hstBall G w N h Φ ε Δ X v ℓ R ↔
        0 ≤ (hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R ∧
        0 ≤ hstRadius N Δ (ℓ - 1) + (R : ℝ) * hstStep N Φ ε Δ ℓ ∧
        u ∈ X ∧
        hopDist G w (((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R).toNat * h) v u ≤
          ENNReal.ofReal (hstRadius N Δ (ℓ - 1) + (R : ℝ) * hstStep N Φ ε Δ ℓ) := by
    intro Δ X v ℓ R u
    unfold hstBall
    split_ifs with h_if
    · constructor
      · simp
      · rintro ⟨h1, h2, _, _⟩
        rcases h_if with h_lt1 | h_lt2 <;> linarith
    · push_neg at h_if
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨hu, hd⟩ => ⟨h_if.1, h_if.2, hu, hd⟩, fun ⟨_, _, hu, hd⟩ => ⟨hu, hd⟩⟩

  have hstBall_subset : ∀ (Δ : ℝ) (X : Finset (Fin n)) (v : Fin n) (ℓ : ℕ) (R : ℤ),
      hstBall G w N h Φ ε Δ X v ℓ R ⊆ X := by
    intro Δ X v ℓ R u hu
    exact ((mem_hstBall_iff Δ X v ℓ R u).mp hu).2.2.1

  have hstBall_mono_set : ∀ (Δ : ℝ) {X₁ X₂ : Finset (Fin n)}, X₁ ⊆ X₂ →
      ∀ (v : Fin n) (ℓ : ℕ) (R : ℤ),
        hstBall G w N h Φ ε Δ X₁ v ℓ R ⊆ hstBall G w N h Φ ε Δ X₂ v ℓ R := by
    intro Δ X₁ X₂ hsub v ℓ R u hu
    rw [mem_hstBall_iff] at hu ⊢
    exact ⟨hu.1, hu.2.1, hsub hu.2.2.1, hu.2.2.2⟩

  have mem_sspCands_iff : ∀ (Δ : ℝ) (m_init : ℕ) (X_cur : Finset (Fin n)) (ℓ : ℕ) (x : Fin n),
      x ∈ sspCands G w N h Φ ε Δ m_init X_cur ℓ ↔
        x ∈ X_cur ∧
        (m_init : ℝ) / (hstMu N (ℓ - 1) : ℝ) ≤
          ((hstBall G w N h Φ ε Δ X_cur x ℓ 0).card : ℝ) ∧
        ((hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) ≤
          (m_init : ℝ) / (hstMu N ℓ : ℝ) := by
    intro Δ m_init X_cur ℓ x
    simp only [sspCands, Finset.mem_filter]

  have hstRadius_mono : ∀ (Δ : ℝ), 0 < Δ → ∀ {m₁ m₂ : ℕ}, m₁ ≤ m₂ →
      hstRadius N Δ m₁ ≤ hstRadius N Δ m₂ := by
    intro Δ hΔ m₁ m₂ hle
    induction hle with
    | refl => exact le_rfl
    | @step m _ ih =>
      have hL_pos : (0 : ℝ) < (hstPhaseCount N : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h_params.one_le_L)
      simp only [hstRadius]
      have h1 : 0 ≤ Δ / (2 : ℝ) ^ ((hstPhaseCount N - (m + 1)) + 4) := by positivity
      have h2 : 0 ≤ Δ / (8 * (hstPhaseCount N : ℝ)) := by positivity
      linarith

  have hstRadius_step_end : ∀ (Δ : ℝ) (ℓ : ℕ),
      hstRadius N Δ (ℓ - 1) + (hstRadiusSteps N Φ ε : ℝ) * hstStep N Φ ε Δ ℓ =
        hstRadius N Δ ℓ := by
    intro Δ ℓ
    unfold hstStep
    have hk_ne : (hstRadiusSteps N Φ ε : ℝ) ≠ 0 := by
      have hk1 : (1 : ℝ) ≤ (hstRadiusSteps N Φ ε : ℝ) := by exact_mod_cast h_params.one_le_k
      linarith
    rw [mul_div_cancel₀ _ hk_ne]
    ring

  have mem_hstBall_zero : ∀ (Δ : ℝ), 0 < Δ → ∀ (X_cur : Finset (Fin n)) (x : Fin n),
      x ∈ X_cur → ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
        x ∈ hstBall G w N h Φ ε Δ X_cur x ℓ 0 := by
    intro Δ hΔ X_cur x hx ℓ hℓ1 hℓL
    rw [mem_hstBall_iff]
    have hrad := (h_params.radius_bounds Δ hΔ).2.2 ℓ hℓ1 hℓL
    refine ⟨by positivity, ?_, hx, ?_⟩
    · simp only [Int.cast_zero, zero_mul, add_zero]
      exact le_of_lt hrad.1
    · rw [hopDist_self]
      exact zero_le _

  have hstBall_mono_R : ∀ (Δ : ℝ), 0 < Δ → ∀ (X_cur : Finset (Fin n)) (x : Fin n) (ℓ : ℕ),
      1 ≤ ℓ → ℓ ≤ hstPhaseCount N → ∀ (R₁ R₂ : ℤ), R₁ ≤ R₂ →
        hstBall G w N h Φ ε Δ X_cur x ℓ R₁ ⊆ hstBall G w N h Φ ε Δ X_cur x ℓ R₂ := by
    intro Δ hΔ X_cur x ℓ hℓ1 hℓL R₁ R₂ hR u hu
    rw [mem_hstBall_iff] at hu ⊢
    have hq_pos : 0 < hstStep N Φ ε Δ ℓ := ((h_params.radius_bounds Δ hΔ).2.2 ℓ hℓ1 hℓL).2.1
    have h1 : 0 ≤ (hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R₂ := by omega
    have hR_real : (R₁ : ℝ) ≤ (R₂ : ℝ) := by exact_mod_cast hR
    have h_rad_le : hstRadius N Δ (ℓ - 1) + (R₁ : ℝ) * hstStep N Φ ε Δ ℓ ≤
        hstRadius N Δ (ℓ - 1) + (R₂ : ℝ) * hstStep N Φ ε Δ ℓ := by nlinarith
    have h_hop_le : ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R₁).toNat * h ≤
        ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R₂).toNat * h :=
      Nat.mul_le_mul_right h (Int.toNat_le_toNat (by omega))
    refine ⟨h1, by linarith [hu.2.1], hu.2.2.1, ?_⟩
    exact le_trans (hopDist_anti h_hop_le x u)
      (le_trans hu.2.2.2 (ENNReal.ofReal_le_ofReal h_rad_le))

  have h_geom : ∀ (Δ : ℝ), 0 < Δ → ∀ (X_cur : Finset (Fin n)),
      (∀ x ∈ X_cur, ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
        x ∈ hstBall G w N h Φ ε Δ X_cur x ℓ 0 ∧
        (∀ R₁ R₂ : ℤ, R₁ ≤ R₂ →
          hstBall G w N h Φ ε Δ X_cur x ℓ R₁ ⊆ hstBall G w N h Φ ε Δ X_cur x ℓ R₂) ∧
        (∃ ρ : Fin n → ℤ,
          (∀ v ∈ X_cur, ∀ R : ℤ,
            v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ R ↔ ρ v ≤ R) ∧
          (∀ u ∈ X_cur, ∀ v ∈ X_cur, u ≠ v →
            ρ v ≤ ρ u +
              (Nat.ceil ((hopDist G w h u v).toReal / hstStep N Φ ε Δ ℓ) : ℤ)))) ∧
      (∀ (ℓ R : ℕ), 1 ≤ ℓ → ℓ ≤ hstPhaseCount N → R < hstRadiusSteps N Φ ε →
        ∀ (x u v : Fin n),
          u ∈ hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ) →
          v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ) →
          hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
            ENNReal.ofReal (Δ / 2)) ∧
      (∀ (ℓ : ℕ) (S : ℤ) (x a b : Fin n),
        1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
        a ∈ hstBall G w N h Φ ε Δ X_cur x ℓ S →
        b ∈ X_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ (S + 1) →
        ENNReal.ofReal Δ ≤
          ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
            hopDist G w h a b ∧
        ENNReal.ofReal Δ ≤
          ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
            hopDist G w h b a) ∧
      (∀ u v z : Fin n,
        z ∈ hstBall G w N h Φ ε Δ X_cur u (hstPhaseCount N) (hstRadiusSteps N Φ ε : ℤ) →
        z ∈ hstBall G w N h Φ ε Δ X_cur v (hstPhaseCount N) (hstRadiusSteps N Φ ε : ℤ) →
        hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
          ENNReal.ofReal (Δ / 2)) ∧
      (Δ < 8 → ∀ x ∈ X_cur, ∀ (ℓ : ℕ) (R : ℤ),
        1 ≤ ℓ → ℓ ≤ hstPhaseCount N → 0 ≤ R → R ≤ (hstRadiusSteps N Φ ε : ℤ) →
        (hstBall G w N h Φ ε Δ X_cur x ℓ R).card = 1) := by
    intro Δ hΔ X_cur
    have hrL_lt : hstRadius N Δ (hstPhaseCount N) < Δ / 4 :=
      (h_params.radius_bounds Δ hΔ).2.1
    have h_two_seg : ∀ {H₁ H₂ : ℕ} {B₁ B₂ : ℝ} {u z v : Fin n},
        H₁ ≤ hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h →
        H₂ ≤ hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h →
        0 ≤ B₁ → B₁ < Δ / 4 → 0 ≤ B₂ → B₂ < Δ / 4 →
        hopDist G w H₁ u z ≤ ENNReal.ofReal B₁ →
        hopDist G w H₂ z v ≤ ENNReal.ofReal B₂ →
        hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
          ENNReal.ofReal (Δ / 2) := by
      intro H₁ H₂ B₁ B₂ u z v hH1 hH2 hB1_nn hB1_lt hB2_nn hB2_lt hd1 hd2
      have hH_sum : H₁ + H₂ ≤ 2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h := by
        linarith
      refine le_trans (hopDist_anti hH_sum u v) ?_
      refine le_trans (hopDist_add_le H₁ H₂ u z v) ?_
      refine le_trans (add_le_add hd1 hd2) ?_
      rw [← ENNReal.ofReal_add hB1_nn hB2_nn]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · 
      intro x hx ℓ hℓ1 hℓL
      refine ⟨mem_hstBall_zero Δ hΔ X_cur x hx ℓ hℓ1 hℓL,
        hstBall_mono_R Δ hΔ X_cur x ℓ hℓ1 hℓL, ?_⟩
      classical
      have hrad := (h_params.radius_bounds Δ hΔ).2.2 ℓ hℓ1 hℓL
      have hr0_pos : 0 < hstRadius N Δ (ℓ - 1) := hrad.1
      have hq_pos : 0 < hstStep N Φ ε Δ ℓ := hrad.2.1
      let b : ℤ := -((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ))
      have hb : ∀ (v : Fin n) (R : ℤ),
          v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ R → b ≤ R := by
        intro v R hv
        have h1 := ((mem_hstBall_iff Δ X_cur x ℓ R v).mp hv).1
        dsimp [b]
        omega
      have hex : ∀ v ∈ X_cur, ∃ R : ℤ, v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ R := by
        intro v hv
        let c0 : ℕ := Nat.ceil (Φ / hstStep N Φ ε Δ ℓ)
        refine ⟨(c0 : ℤ), ?_⟩
        rw [mem_hstBall_iff]
        have hΦ_pos : 0 < Φ := by linarith
        have hc0_pos : 0 < c0 := Nat.ceil_pos.mpr (div_pos hΦ_pos hq_pos)
        have h_le_c0 : Φ / hstStep N Φ ε Δ ℓ ≤ (c0 : ℝ) := Nat.le_ceil _
        have hΦ_le_mul : Φ ≤ (c0 : ℝ) * hstStep N Φ ε Δ ℓ :=
          (div_le_iff₀ hq_pos).mp h_le_c0
        have hk1 : 1 ≤ hstRadiusSteps N Φ ε := h_params.one_le_k
        have h_int_pos : 1 ≤ (hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + (c0 : ℤ) := by
          have : (0 : ℤ) ≤ (hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) := by positivity
          omega
        have h_tonat_ge : 1 ≤ ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + (c0 : ℤ)).toNat := by
          omega
        have h_hops_ge : h ≤ ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + (c0 : ℤ)).toNat * h := by
          simpa using Nat.mul_le_mul_right h h_tonat_ge
        have h_rad_ge : Φ ≤ hstRadius N Δ (ℓ - 1) + ((c0 : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ := by
          rw [Int.cast_natCast]
          linarith
        refine ⟨by omega, by linarith, hv, ?_⟩
        exact le_trans (hopDist_anti h_hops_ge x v)
          (le_trans (hΦ_diam x v) (ENNReal.ofReal_le_ofReal h_rad_ge))
      let ρ : Fin n → ℤ := fun v =>
        if hv : v ∈ X_cur then (Int.leastOfBdd b (hb v) (hex v hv)).1 else 0
      refine ⟨ρ, ?_, ?_⟩
      · intro v hv R
        have h_spec := (Int.leastOfBdd b (hb v) (hex v hv)).2
        have hρ_eq : ρ v = (Int.leastOfBdd b (hb v) (hex v hv)).1 := dif_pos hv
        rw [hρ_eq]
        exact ⟨fun hmem => h_spec.2 R hmem,
          fun hle => hstBall_mono_R Δ hΔ X_cur x ℓ hℓ1 hℓL _ R hle h_spec.1⟩
      · intro u hu v hv huv
        have h_iff : ∀ w_v ∈ X_cur, ∀ R : ℤ,
            w_v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ R ↔ ρ w_v ≤ R := by
          intro w_v hw_v R
          have h_spec := (Int.leastOfBdd b (hb w_v) (hex w_v hw_v)).2
          have hρ_eq : ρ w_v = (Int.leastOfBdd b (hb w_v) (hex w_v hw_v)).1 := dif_pos hw_v
          rw [hρ_eq]
          exact ⟨fun hmem => h_spec.2 R hmem,
            fun hle => hstBall_mono_R Δ hΔ X_cur x ℓ hℓ1 hℓL _ R hle h_spec.1⟩
        have hu_mem : u ∈ hstBall G w N h Φ ε Δ X_cur x ℓ (ρ u) :=
          (h_iff u hu (ρ u)).mpr le_rfl
        rw [mem_hstBall_iff] at hu_mem
        let d_uv : ℝ := (hopDist G w h u v).toReal
        have hd_bounds := hopDist_toReal_bounds u v huv
        have hd_ge2 : 2 ≤ d_uv := hd_bounds.1
        have hd_ne_top : hopDist G w h u v ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hΦ_diam u v)
        have hd_ofReal : ENNReal.ofReal d_uv = hopDist G w h u v :=
          ENNReal.ofReal_toReal hd_ne_top
        let c : ℕ := Nat.ceil (d_uv / hstStep N Φ ε Δ ℓ)
        have hc_pos : 1 ≤ c := Nat.ceil_pos.mpr (div_pos (by linarith) hq_pos)
        have hd_le_mul : d_uv ≤ (c : ℝ) * hstStep N Φ ε Δ ℓ :=
          (div_le_iff₀ hq_pos).mp (Nat.le_ceil _)
        rw [← h_iff v hv (ρ u + (c : ℤ)), mem_hstBall_iff]
        let A : ℕ := ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + ρ u).toNat
        have hA_eq : ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + (ρ u + (c : ℤ))).toNat = A + c := by
          dsimp [A]
          omega
        have h_hops : A * h + h ≤ (A + c) * h := by
          have : A + 1 ≤ A + c := by omega
          simpa [Nat.add_mul] using Nat.mul_le_mul_right h this
        have h_rad_step :
            hstRadius N Δ (ℓ - 1) + (ρ u : ℝ) * hstStep N Φ ε Δ ℓ + d_uv ≤
            hstRadius N Δ (ℓ - 1) + ((ρ u + (c : ℤ) : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ := by
          push_cast
          linarith
        refine ⟨by omega, by linarith [hu_mem.2.1], hv, ?_⟩
        rw [hA_eq]
        refine le_trans (hopDist_anti h_hops x v) ?_
        refine le_trans (hopDist_add_le (A * h) h x u v) ?_
        refine le_trans (add_le_add hu_mem.2.2.2 (le_of_eq hd_ofReal.symm)) ?_
        rw [← ENNReal.ofReal_add hu_mem.2.1 (by linarith)]
        exact ENNReal.ofReal_le_ofReal h_rad_step
    · 
      intro ℓ R hℓ1 hℓL hR x u v hu hv
      rw [mem_hstBall_iff] at hu hv
      have hq_pos : 0 < hstStep N Φ ε Δ ℓ := ((h_params.radius_bounds Δ hΔ).2.2 ℓ hℓ1 hℓL).2.1
      have h_hop_eq : ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + (R : ℤ)).toNat =
          hstRadiusSteps N Φ ε * ℓ + R := by omega
      have hH_le : (hstRadiusSteps N Φ ε * ℓ + R) * h ≤
          hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h := by
        refine Nat.mul_le_mul_right h ?_
        have h1 : hstRadiusSteps N Φ ε * ℓ ≤ hstRadiusSteps N Φ ε * hstPhaseCount N :=
          Nat.mul_le_mul_left _ hℓL
        linarith
      have hB_lt : hstRadius N Δ (ℓ - 1) + ((R : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ < Δ / 4 := by
        have hR_le : ((R : ℤ) : ℝ) ≤ (hstRadiusSteps N Φ ε : ℝ) := by
          exact_mod_cast (le_of_lt hR)
        have h1 : hstRadius N Δ (ℓ - 1) + ((R : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ ≤
            hstRadius N Δ (ℓ - 1) + (hstRadiusSteps N Φ ε : ℝ) * hstStep N Φ ε Δ ℓ := by
          nlinarith
        rw [hstRadius_step_end Δ ℓ] at h1
        exact lt_of_le_of_lt (le_trans h1 (hstRadius_mono Δ hΔ hℓL)) hrL_lt
      have hu_d : hopDist G w ((hstRadiusSteps N Φ ε * ℓ + R) * h) u x ≤
          ENNReal.ofReal (hstRadius N Δ (ℓ - 1) + ((R : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ) := by
        rw [hopDist_comm, ← h_hop_eq]
        exact hu.2.2.2
      have hv_d : hopDist G w ((hstRadiusSteps N Φ ε * ℓ + R) * h) x v ≤
          ENNReal.ofReal (hstRadius N Δ (ℓ - 1) + ((R : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ) := by
        rw [← h_hop_eq]
        exact hv.2.2.2
      exact h_two_seg hH_le hH_le hu.2.1 hB_lt hv.2.1 hB_lt hu_d hv_d
    · 
      intro ℓ S x a b hℓ1 hℓL ha hb
      rw [Finset.mem_sdiff] at hb
      rcases hb with ⟨hb_X, hb_not⟩
      rw [mem_hstBall_iff] at ha
      have hrad := (h_params.radius_bounds Δ hΔ).2.2 ℓ hℓ1 hℓL
      have hq_pos : 0 < hstStep N Φ ε Δ ℓ := hrad.2.1
      have hK_div : Δ / hstStep N Φ ε Δ ℓ ≤
          8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ) := hrad.2.2.1
      have hq_le_ab : ENNReal.ofReal (hstStep N Φ ε Δ ℓ) ≤ hopDist G w h a b := by
        by_contra h_lt
        push_neg at h_lt
        apply hb_not
        rw [mem_hstBall_iff]
        let A : ℕ := ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + S).toNat
        have hA1 : ((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + (S + 1)).toNat = A + 1 := by
          dsimp [A]
          omega
        have h_rad_eq :
            hstRadius N Δ (ℓ - 1) + ((S + 1 : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ =
            (hstRadius N Δ (ℓ - 1) + (S : ℝ) * hstStep N Φ ε Δ ℓ) + hstStep N Φ ε Δ ℓ := by
          push_cast
          ring
        refine ⟨by omega, by linarith [ha.2.1], hb_X, ?_⟩
        rw [hA1, Nat.add_mul, one_mul, h_rad_eq,
          ENNReal.ofReal_add ha.2.1 (le_of_lt hq_pos)]
        exact le_trans (hopDist_add_le (A * h) h x a b)
          (add_le_add ha.2.2.2 (le_of_lt h_lt))
      have hΔ_le : Δ ≤ (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
          hstStep N Φ ε Δ ℓ := (div_le_iff₀ hq_pos).mp hK_div
      have hK_nn : 0 ≤ 8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ) := by
        linarith [h_params.one_le_K]
      have h_main : ENNReal.ofReal Δ ≤
          ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
            hopDist G w h a b := by
        refine le_trans (ENNReal.ofReal_le_ofReal hΔ_le) ?_
        rw [ENNReal.ofReal_mul hK_nn]
        exact mul_le_mul_right hq_le_ab _
      refine ⟨h_main, ?_⟩
      rwa [hopDist_comm h b a]
    · 
      intro u v z hzu hzv
      rw [mem_hstBall_iff] at hzu hzv
      have h_hop_eq : ((hstRadiusSteps N Φ ε : ℤ) * (hstPhaseCount N : ℤ) +
          (hstRadiusSteps N Φ ε : ℤ)).toNat =
          hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) := by
        have : (hstRadiusSteps N Φ ε : ℤ) * (hstPhaseCount N : ℤ) +
            (hstRadiusSteps N Φ ε : ℤ) =
            ((hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) : ℕ) : ℤ) := by
          push_cast; ring
        rw [this, Int.toNat_natCast]
      have h_rad_eq : hstRadius N Δ (hstPhaseCount N - 1) +
          ((hstRadiusSteps N Φ ε : ℤ) : ℝ) * hstStep N Φ ε Δ (hstPhaseCount N) =
          hstRadius N Δ (hstPhaseCount N) := by
        rw [Int.cast_natCast]
        exact hstRadius_step_end Δ (hstPhaseCount N)
      have hu_d : hopDist G w (hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u z ≤
          ENNReal.ofReal (hstRadius N Δ (hstPhaseCount N)) := by
        rw [← h_hop_eq, ← h_rad_eq]
        exact hzu.2.2.2
      have hv_d : hopDist G w (hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) z v ≤
          ENNReal.ofReal (hstRadius N Δ (hstPhaseCount N)) := by
        rw [hopDist_comm, ← h_hop_eq, ← h_rad_eq]
        exact hzv.2.2.2
      have hrL_nn : 0 ≤ hstRadius N Δ (hstPhaseCount N) := by
        rw [← h_rad_eq]
        exact hzu.2.1
      exact h_two_seg le_rfl le_rfl hrL_nn hrL_lt hrL_nn hrL_lt hu_d hv_d
    · 
      intro hΔ8 x hx ℓ R hℓ1 hℓL hR0 hRk
      have h_eq : hstBall G w N h Φ ε Δ X_cur x ℓ R = {x} := by
        ext u
        rw [Finset.mem_singleton]
        constructor
        · intro hu
          by_contra hne
          have h2_le := two_le_hopDist
            (((hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + R).toNat * h) x u (Ne.symm hne)
          rw [mem_hstBall_iff] at hu
          have hq_pos : 0 < hstStep N Φ ε Δ ℓ :=
            ((h_params.radius_bounds Δ hΔ).2.2 ℓ hℓ1 hℓL).2.1
          have hR_le : (R : ℝ) ≤ (hstRadiusSteps N Φ ε : ℝ) := by exact_mod_cast hRk
          have h_rad_lt2 : hstRadius N Δ (ℓ - 1) + (R : ℝ) * hstStep N Φ ε Δ ℓ < 2 := by
            have h1 : hstRadius N Δ (ℓ - 1) + (R : ℝ) * hstStep N Φ ε Δ ℓ ≤
                hstRadius N Δ (ℓ - 1) + (hstRadiusSteps N Φ ε : ℝ) * hstStep N Φ ε Δ ℓ := by
              nlinarith
            rw [hstRadius_step_end Δ ℓ] at h1
            have h2 := lt_of_le_of_lt (le_trans h1 (hstRadius_mono Δ hΔ hℓL)) hrL_lt
            linarith
          have h_le_enn := le_trans h2_le hu.2.2.2
          have h2_le_rad := (ENNReal.ofReal_le_ofReal_iff hu.2.1).mp h_le_enn
          linarith
        · rintro rfl
          exact hstBall_mono_R Δ hΔ X_cur u ℓ hℓ1 hℓL 0 R hR0
            (mem_hstBall_zero Δ hΔ X_cur u hx ℓ hℓ1 hℓL)
      rw [h_eq, Finset.card_singleton]

  
  
  
  have h_run_steps : ∀ (Δ : ℝ), 0 < Δ → ∀ (m_init : ℕ) (steps : List (ℕ × ℕ)),
      (∀ p ∈ steps, 1 ≤ p.1 ∧ p.1 ≤ hstPhaseCount N ∧ p.2 < hstRadiusSteps N Φ ε) →
      ∀ (X_cur M_cur : Finset (Fin n)), M_cur ⊆ X_cur →
        let res := sspRunSteps G w N h Φ ε Δ m_init X_cur M_cur steps
        res.1.length + (if res.2.1.Nonempty then 1 else 0) ≤ X_cur.card ∧
        (res.1.map (fun t => t.2.1)).Pairwise Disjoint ∧
        (∀ t ∈ res.1, Disjoint t.2.1 res.2.1) ∧
        res.1.foldr (fun t acc => t.2.1 ∪ acc) res.2.1 = X_cur ∧
        res.2.1 ⊆ X_cur ∧
        res.2.2 ⊆ M_cur ∩ res.2.1 ∧
        (∀ t ∈ res.1,
          1 ≤ t.1 ∧ t.1 ≤ hstPhaseCount N ∧
          t.2.1.Nonempty ∧
          t.2.1 ⊆ X_cur ∧
          t.2.2 ⊆ M_cur ∩ t.2.1 ∧
          (t.2.1.card : ℝ) ≤ (m_init : ℝ) / (hstMu N t.1 : ℝ) ∧
          (∃ (X_sub : Finset (Fin n)) (x : Fin n) (R : ℕ),
            X_sub ⊆ X_cur ∧ x ∈ X_sub ∧ R < hstRadiusSteps N Φ ε ∧
            t.2.1 = hstBall G w N h Φ ε Δ X_sub x t.1 (R : ℤ)) ∧
          (∀ u ∈ t.2.2, ∀ v ∈ X_cur \ t.2.1,
            ∃ (X_sub : Finset (Fin n)) (x : Fin n) (ℓ : ℕ) (S : ℤ),
              X_sub ⊆ X_cur ∧ 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N ∧
              ((u ∈ hstBall G w N h Φ ε Δ X_sub x ℓ S ∧
                v ∈ X_sub \ hstBall G w N h Φ ε Δ X_sub x ℓ (S + 1)) ∨
               (v ∈ hstBall G w N h Φ ε Δ X_sub x ℓ S ∧
                u ∈ X_sub \ hstBall G w N h Φ ε Δ X_sub x ℓ (S + 1))))) ∧
        (∀ u ∈ res.2.2, ∀ v ∈ X_cur \ res.2.1,
          ∃ (X_sub : Finset (Fin n)) (x : Fin n) (ℓ : ℕ) (S : ℤ),
            X_sub ⊆ X_cur ∧ 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N ∧
            v ∈ hstBall G w N h Φ ε Δ X_sub x ℓ S ∧
            u ∈ X_sub \ hstBall G w N h Φ ε Δ X_sub x ℓ (S + 1)) := by
    intro Δ hΔ m_init steps
    induction steps with
    | nil =>
      intro _ X_cur M_cur hM_sub
      dsimp only [sspRunSteps]
      refine ⟨?_, List.Pairwise.nil, ?_, rfl, Finset.Subset.refl _,
        Finset.subset_inter (Finset.Subset.refl _) hM_sub, ?_, ?_⟩
      · simp only [List.length_nil, zero_add]
        split_ifs with hne
        · exact Finset.Nonempty.card_pos hne
        · exact Nat.zero_le _
      · intro _ ht; exact absurd ht List.not_mem_nil
      · intro _ ht; exact absurd ht List.not_mem_nil
      · intro _ _ v hv
        simp at hv
    | cons hd rest ih =>
      rcases hd with ⟨ℓ, R⟩
      intro h_steps X_cur M_cur hM_sub
      have h_hd := h_steps (ℓ, R) List.mem_cons_self
      rcases h_hd with ⟨hℓ1, hℓL, hRk⟩
      have h_rest : ∀ p ∈ rest,
          1 ≤ p.1 ∧ p.1 ≤ hstPhaseCount N ∧ p.2 < hstRadiusSteps N Φ ε :=
        fun p hp => h_steps p (List.mem_cons_of_mem _ hp)
      dsimp only [sspRunSteps]
      by_cases hc : (sspCands G w N h Φ ε Δ m_init X_cur ℓ).Nonempty
      · rw [dif_pos hc]
        dsimp only
        obtain ⟨x, hx_def⟩ : ∃ x, (sspCands G w N h Φ ε Δ m_init X_cur ℓ).min' hc = x := ⟨_, rfl⟩
        rw [hx_def]
        obtain ⟨Xj, hXj_def⟩ : ∃ s, hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ) = s := ⟨_, rfl⟩
        obtain ⟨Mj, hMj_def⟩ :
            ∃ s, hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur = s := ⟨_, rfl⟩
        obtain ⟨M_next, hM_next_def⟩ :
            ∃ s, M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) = s := ⟨_, rfl⟩
        rw [hXj_def, hMj_def, hM_next_def]
        obtain ⟨res', h_res'⟩ :
            ∃ r, sspRunSteps G w N h Φ ε Δ m_init (X_cur \ Xj) M_next rest = r := ⟨_, rfl⟩
        rw [h_res']
        have hx_cands : x ∈ sspCands G w N h Φ ε Δ m_init X_cur ℓ := by
          rw [← hx_def]
          exact Finset.min'_mem _ hc
        rcases (mem_sspCands_iff Δ m_init X_cur ℓ x).mp hx_cands with ⟨hx_X, _, hx_hi⟩
        have hx_Xj : x ∈ Xj := by
          rw [← hXj_def]
          exact hstBall_mono_R Δ hΔ X_cur x ℓ hℓ1 hℓL 0 (R : ℤ) (by omega)
            (mem_hstBall_zero Δ hΔ X_cur x hx_X ℓ hℓ1 hℓL)
        have hXj_ne : Xj.Nonempty := ⟨x, hx_Xj⟩
        have hXj_sub : Xj ⊆ X_cur := by
          rw [← hXj_def]
          exact hstBall_subset Δ X_cur x ℓ (R : ℤ)
        have hXj_sub_R1 : Xj ⊆ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) := by
          rw [← hXj_def]
          exact hstBall_mono_R Δ hΔ X_cur x ℓ hℓ1 hℓL (R : ℤ) ((R : ℤ) + 1) (by omega)
        have hM_next_sub : M_next ⊆ X_cur \ Xj := by
          intro z hz
          rw [← hM_next_def, Finset.mem_sdiff] at hz
          rw [Finset.mem_sdiff]
          exact ⟨hM_sub hz.1, fun hz_in => hz.2 (hXj_sub_R1 hz_in)⟩
        have h_ih := ih h_rest (X_cur \ Xj) M_next hM_next_sub
        dsimp only at h_ih
        rw [h_res'] at h_ih
        rcases h_ih with ⟨h_len, h_pw, h_disj_res, h_fold, h_res_sub, h_resM_sub,
          h_t_spec, h_res_sep⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h_card_add : (X_cur \ Xj).card + Xj.card = X_cur.card :=
            Finset.card_sdiff_add_card_eq_card hXj_sub
          have hXj_pos : 1 ≤ Xj.card := Finset.Nonempty.card_pos hXj_ne
          simp only [List.length_cons]
          omega
        · simp only [List.map_cons, List.pairwise_cons]
          refine ⟨?_, h_pw⟩
          intro Y hY
          rcases List.mem_map.mp hY with ⟨t', ht'_mem, rfl⟩
          have ht'_sub : t'.2.1 ⊆ X_cur \ Xj := (h_t_spec t' ht'_mem).2.2.2.1
          exact Finset.disjoint_left.mpr (fun z hz1 hz2 =>
            (Finset.mem_sdiff.mp (ht'_sub hz2)).2 hz1)
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht'
          · exact Finset.disjoint_left.mpr (fun z hz1 hz2 =>
              (Finset.mem_sdiff.mp (h_res_sub hz2)).2 hz1)
          · exact h_disj_res t ht'
        · simp only [List.foldr_cons]
          rw [h_fold]
          exact Finset.union_sdiff_of_subset hXj_sub
        · exact Finset.Subset.trans h_res_sub Finset.sdiff_subset
        · intro z hz
          have hz' := h_resM_sub hz
          rw [Finset.mem_inter] at hz' ⊢
          rw [← hM_next_def] at hz'
          exact ⟨(Finset.mem_sdiff.mp hz'.1).1, hz'.2⟩
        · intro t ht
          rcases List.mem_cons.mp ht with rfl | ht'
          · 
            have hMj_sub : Mj ⊆ M_cur ∩ Xj := by
              intro z hz
              rw [← hMj_def, Finset.mem_inter] at hz
              rw [Finset.mem_inter, ← hXj_def]
              exact ⟨hz.2, hstBall_mono_R Δ hΔ X_cur x ℓ hℓ1 hℓL
                ((R : ℤ) - 1) (R : ℤ) (by omega) hz.1⟩
            have hXj_card : (Xj.card : ℝ) ≤ (m_init : ℝ) / (hstMu N ℓ : ℝ) := by
              have h_sub_k : Xj ⊆ hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ) := by
                rw [← hXj_def]
                exact hstBall_mono_R Δ hΔ X_cur x ℓ hℓ1 hℓL (R : ℤ) (hstRadiusSteps N Φ ε : ℤ) (by omega)
              have h_le_nat : Xj.card ≤
                  (hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card :=
                Finset.card_le_card h_sub_k
              exact le_trans (by exact_mod_cast h_le_nat) hx_hi
            refine ⟨hℓ1, hℓL, hXj_ne, hXj_sub, hMj_sub, hXj_card,
              ⟨X_cur, x, R, Finset.Subset.refl _, hx_X, hRk, hXj_def.symm⟩, ?_⟩
            intro u hu v hv
            rw [← hMj_def] at hu
            have hu_ball : u ∈ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) :=
              (Finset.mem_inter.mp hu).1
            have hv_out : v ∈ X_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ (((R : ℤ) - 1) + 1) := by
              have h_eq : ((R : ℤ) - 1) + 1 = (R : ℤ) := by ring
              rwa [h_eq, hXj_def]
            exact ⟨X_cur, x, ℓ, (R : ℤ) - 1, Finset.Subset.refl _, hℓ1, hℓL,
              Or.inl ⟨hu_ball, hv_out⟩⟩
          · 
            have ht_ih := h_t_spec t ht'
            rcases ht_ih with ⟨ht1, htL, ht_ne, ht_sub, htM_sub, ht_card,
              ⟨X_sub, x', R', hX_sub, hx', hR', ht_eq⟩, ht_sep⟩
            refine ⟨ht1, htL, ht_ne, Finset.Subset.trans ht_sub Finset.sdiff_subset, ?_,
              ht_card, ⟨X_sub, x', R', Finset.Subset.trans hX_sub Finset.sdiff_subset,
                hx', hR', ht_eq⟩, ?_⟩
            · intro z hz
              have hz' := htM_sub hz
              rw [Finset.mem_inter] at hz' ⊢
              rw [← hM_next_def] at hz'
              exact ⟨(Finset.mem_sdiff.mp hz'.1).1, hz'.2⟩
            · intro u hu v hv
              have hu_Mnext : u ∈ M_next := (Finset.mem_inter.mp (htM_sub hu)).1
              rw [← hM_next_def] at hu_Mnext
              have hu_out : u ∈ X_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) := by
                rw [Finset.mem_sdiff]
                exact ⟨hM_sub (Finset.mem_sdiff.mp hu_Mnext).1,
                  (Finset.mem_sdiff.mp hu_Mnext).2⟩
              by_cases hv_Xj : v ∈ Xj
              · rw [← hXj_def] at hv_Xj
                exact ⟨X_cur, x, ℓ, (R : ℤ), Finset.Subset.refl _, hℓ1, hℓL,
                  Or.inr ⟨hv_Xj, hu_out⟩⟩
              · have hv' : v ∈ (X_cur \ Xj) \ t.2.1 := by
                  rw [Finset.mem_sdiff, Finset.mem_sdiff]
                  exact ⟨⟨(Finset.mem_sdiff.mp hv).1, hv_Xj⟩, (Finset.mem_sdiff.mp hv).2⟩
                rcases ht_sep u hu v hv' with ⟨X_sub2, x2, ℓ2, S2, hsub2, h1_2, hL_2, hor⟩
                exact ⟨X_sub2, x2, ℓ2, S2,
                  Finset.Subset.trans hsub2 Finset.sdiff_subset, h1_2, hL_2, hor⟩
        · intro u hu v hv
          have hu_Mnext : u ∈ M_next := (Finset.mem_inter.mp (h_resM_sub hu)).1
          rw [← hM_next_def] at hu_Mnext
          have hu_out : u ∈ X_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) := by
            rw [Finset.mem_sdiff]
            exact ⟨hM_sub (Finset.mem_sdiff.mp hu_Mnext).1,
              (Finset.mem_sdiff.mp hu_Mnext).2⟩
          by_cases hv_Xj : v ∈ Xj
          · rw [← hXj_def] at hv_Xj
            exact ⟨X_cur, x, ℓ, (R : ℤ), Finset.Subset.refl _, hℓ1, hℓL, hv_Xj, hu_out⟩
          · have hv' : v ∈ (X_cur \ Xj) \ res'.2.1 := by
              rw [Finset.mem_sdiff, Finset.mem_sdiff]
              exact ⟨⟨(Finset.mem_sdiff.mp hv).1, hv_Xj⟩, (Finset.mem_sdiff.mp hv).2⟩
            rcases h_res_sep u hu v hv' with ⟨X_sub2, x2, ℓ2, S2, hsub2, h1_2, hL_2, hv_in, hu_nin⟩
            exact ⟨X_sub2, x2, ℓ2, S2,
              Finset.Subset.trans hsub2 Finset.sdiff_subset, h1_2, hL_2, hv_in, hu_nin⟩
      · rw [dif_neg hc]
        exact ih h_rest X_cur M_cur hM_sub

  
  
  
  have h_res_large : ∀ (X M : Finset (Fin n)) (Δ : ℝ), 0 < Δ → ∀ (τ : FinTape N Φ ε),
      ∀ v ∈ (sspRunSteps G w N h Φ ε Δ X.card X M
        (List.ofFn (fun i : Fin (hstTotalSlots N) => ((sspSlotPhases N).get i, (τ i).1)))).2.1,
        (X.card : ℝ) / 2 <
          ((hstBall G w N h Φ ε Δ X v (hstPhaseCount N) (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := by
    intro X M Δ hΔ τ
    have h_append : ∀ (s₁ s₂ : List (ℕ × ℕ)) (X_c M_c : Finset (Fin n)),
        (sspRunSteps G w N h Φ ε Δ X.card X_c M_c (s₁ ++ s₂)).2.1 =
          (sspRunSteps G w N h Φ ε Δ X.card
            (sspRunSteps G w N h Φ ε Δ X.card X_c M_c s₁).2.1
            (sspRunSteps G w N h Φ ε Δ X.card X_c M_c s₁).2.2 s₂).2.1 := by
      intro s₁ s₂
      induction s₁ with
      | nil => intro X_c M_c; rfl
      | cons hd tl ih =>
        rcases hd with ⟨ℓ, R⟩
        intro X_c M_c
        simp only [List.cons_append, sspRunSteps]
        split_ifs with hc <;> exact ih _ _
    have h_sub_run : ∀ (s : List (ℕ × ℕ)) (X_c M_c : Finset (Fin n)),
        (sspRunSteps G w N h Φ ε Δ X.card X_c M_c s).2.1 ⊆ X_c := by
      intro s
      induction s with
      | nil => intro X_c M_c; exact Finset.Subset.refl _
      | cons hd tl ih =>
        rcases hd with ⟨ℓ, R⟩
        intro X_c M_c
        simp only [sspRunSteps]
        split_ifs with hc
        · exact Finset.Subset.trans (ih _ _) Finset.sdiff_subset
        · exact ih _ _
    have h_noop : ∀ (ℓ : ℕ) (s : List (ℕ × ℕ)), (∀ p ∈ s, p.1 = ℓ) →
        ∀ (X_c M_c : Finset (Fin n)),
          sspCands G w N h Φ ε Δ X.card X_c ℓ = ∅ →
          (sspRunSteps G w N h Φ ε Δ X.card X_c M_c s).2.1 = X_c := by
      intro ℓ s
      induction s with
      | nil => intro _ X_c M_c _; rfl
      | cons hd tl ih =>
        rcases hd with ⟨p1, R⟩
        intro hs X_c M_c hemp
        have hp1 : p1 = ℓ := hs (p1, R) List.mem_cons_self
        subst hp1
        have htl : ∀ p ∈ tl, p.1 = p1 := fun p hp => hs p (List.mem_cons_of_mem _ hp)
        simp only [sspRunSteps]
        split_ifs with hc
        · rw [hemp] at hc
          exact absurd hc Finset.not_nonempty_empty
        · exact ih htl X_c M_c hemp
    have h_pot : ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
        ∀ (s : List (ℕ × ℕ)), (∀ p ∈ s, p.1 = ℓ) →
        ∀ (X_c M_c : Finset (Fin n)),
          sspCands G w N h Φ ε Δ X.card (sspRunSteps G w N h Φ ε Δ X.card X_c M_c s).2.1 ℓ = ∅ ∨
          (((sspRunSteps G w N h Φ ε Δ X.card X_c M_c s).2.1).card : ℝ) +
            (s.length : ℝ) * ((X.card : ℝ) / (hstMu N (ℓ - 1) : ℝ)) ≤
            (X_c.card : ℝ) := by
      intro ℓ hℓ1 hℓL s
      induction s with
      | nil =>
        intro _ X_c M_c
        right
        simp [sspRunSteps]
      | cons hd tl ih =>
        rcases hd with ⟨p1, R⟩
        intro hs X_c M_c
        have hp1 : p1 = ℓ := hs (p1, R) List.mem_cons_self
        subst hp1
        have htl : ∀ p ∈ tl, p.1 = p1 := fun p hp => hs p (List.mem_cons_of_mem _ hp)
        dsimp only [sspRunSteps]
        by_cases hc : (sspCands G w N h Φ ε Δ X.card X_c p1).Nonempty
        · rw [dif_pos hc]
          dsimp only
          obtain ⟨x, hx_def⟩ : ∃ x, (sspCands G w N h Φ ε Δ X.card X_c p1).min' hc = x := ⟨_, rfl⟩
          rw [hx_def]
          obtain ⟨Xj, hXj_def⟩ : ∃ s_j, hstBall G w N h Φ ε Δ X_c x p1 (R : ℤ) = s_j := ⟨_, rfl⟩
          obtain ⟨M_next, hMn_def⟩ :
              ∃ s_m, M_c \ hstBall G w N h Φ ε Δ X_c x p1 ((R : ℤ) + 1) = s_m := ⟨_, rfl⟩
          rw [hXj_def, hMn_def]
          have hx_cands : x ∈ sspCands G w N h Φ ε Δ X.card X_c p1 := by
            rw [← hx_def]
            exact Finset.min'_mem _ hc
          rcases (mem_sspCands_iff Δ X.card X_c p1 x).mp hx_cands with ⟨_, hx_lo, _⟩
          have h0_sub : hstBall G w N h Φ ε Δ X_c x p1 0 ⊆ Xj := by
            rw [← hXj_def]
            exact hstBall_mono_R Δ hΔ X_c x p1 hℓ1 hℓL 0 (R : ℤ) (by omega)
          have hXj_lo : (X.card : ℝ) / (hstMu N (p1 - 1) : ℝ) ≤ (Xj.card : ℝ) :=
            le_trans hx_lo (by exact_mod_cast Finset.card_le_card h0_sub)
          have hXj_sub : Xj ⊆ X_c := by
            rw [← hXj_def]
            exact hstBall_subset Δ X_c x p1 (R : ℤ)
          have h_add : (X_c \ Xj).card + Xj.card = X_c.card :=
            Finset.card_sdiff_add_card_eq_card hXj_sub
          have h_add_r : ((X_c \ Xj).card : ℝ) + (Xj.card : ℝ) = (X_c.card : ℝ) := by
            exact_mod_cast h_add
          rcases ih htl (X_c \ Xj) M_next with h_emp | h_drop
          · exact Or.inl h_emp
          · right
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            linarith
        · rw [dif_neg hc]
          have hemp : sspCands G w N h Φ ε Δ X.card X_c p1 = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hc
          left
          rw [h_noop p1 tl htl X_c M_c hemp]
          exact hemp
    have h_exhaust : ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
        ∀ (s : List (ℕ × ℕ)), s.map Prod.fst = List.replicate (hstMu N (ℓ - 1)) ℓ →
        ∀ (X_c M_c : Finset (Fin n)), X_c ⊆ X →
          sspCands G w N h Φ ε Δ X.card
            (sspRunSteps G w N h Φ ε Δ X.card X_c M_c s).2.1 ℓ = ∅ := by
      intro ℓ hℓ1 hℓL s hs_map X_c M_c hXc_sub
      have hs_all : ∀ p ∈ s, p.1 = ℓ := by
        intro p hp
        have hmem : p.1 ∈ List.replicate (hstMu N (ℓ - 1)) ℓ := by
          rw [← hs_map]
          exact List.mem_map_of_mem hp
        exact List.eq_of_mem_replicate hmem
      have hs_len : s.length = hstMu N (ℓ - 1) := by
        have h1 := congrArg List.length hs_map
        simpa [List.length_map, List.length_replicate] using h1
      rcases h_pot ℓ hℓ1 hℓL s hs_all X_c M_c with h_emp | h_bound
      · exact h_emp
      · by_contra h_ne
        obtain ⟨X_out, hXout_def⟩ :
            ∃ s_out, (sspRunSteps G w N h Φ ε Δ X.card X_c M_c s).2.1 = s_out := ⟨_, rfl⟩
        rw [hXout_def] at h_ne h_bound
        have h_cands_ne : (sspCands G w N h Φ ε Δ X.card X_out ℓ).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr h_ne
        rcases h_cands_ne with ⟨z, hz⟩
        have hz_mem : z ∈ X_out := ((mem_sspCands_iff Δ X.card X_out ℓ z).mp hz).1
        have h_pos_nat : 1 ≤ X_out.card := Finset.Nonempty.card_pos ⟨z, hz_mem⟩
        have h_pos_r : (1 : ℝ) ≤ (X_out.card : ℝ) := by exact_mod_cast h_pos_nat
        have h_mu_ne : (hstMu N (ℓ - 1) : ℝ) ≠ 0 := by
          unfold hstMu
          positivity
        rw [hs_len, mul_div_cancel₀ _ h_mu_ne] at h_bound
        have hXc_le : (X_c.card : ℝ) ≤ (X.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hXc_sub
        linarith
    have h_phase_bdry : ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ + 1 ≤ hstPhaseCount N →
        ∀ (Y : Finset (Fin n)) (v : Fin n),
          hstBall G w N h Φ ε Δ Y v ℓ (hstRadiusSteps N Φ ε : ℤ) =
          hstBall G w N h Φ ε Δ Y v (ℓ + 1) 0 := by
      intro ℓ hℓ1 hℓ1L Y v
      ext u
      rw [mem_hstBall_iff, mem_hstBall_iff]
      have h_int : (hstRadiusSteps N Φ ε : ℤ) * (ℓ : ℤ) + (hstRadiusSteps N Φ ε : ℤ) =
          (hstRadiusSteps N Φ ε : ℤ) * ((ℓ + 1 : ℕ) : ℤ) + 0 := by
        push_cast; ring
      have h_rad : hstRadius N Δ (ℓ - 1) +
          ((hstRadiusSteps N Φ ε : ℤ) : ℝ) * hstStep N Φ ε Δ ℓ =
          hstRadius N Δ ((ℓ + 1) - 1) + ((0 : ℤ) : ℝ) * hstStep N Φ ε Δ (ℓ + 1) := by
        simp only [Int.cast_natCast, Int.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel]
        exact hstRadius_step_end Δ ℓ
      rw [h_int, h_rad]
    have h_chain : ∀ (m : ℕ), 1 ≤ m → m ≤ hstPhaseCount N →
        ∀ (X_in M_in : Finset (Fin n)), X_in ⊆ X →
        ∀ (s : List (ℕ × ℕ)),
          s.map Prod.fst = (phaseDesc m).flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ) →
          ∀ v ∈ (sspRunSteps G w N h Φ ε Δ X.card X_in M_in s).2.1,
            (X.card : ℝ) / (hstMu N m : ℝ) <
              ((hstBall G w N h Φ ε Δ X_in v m (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := by
      intro m
      induction m with
      | zero => intro hm1; omega
      | succ m' ih =>
        intro _ hmL X_in M_in hXin_sub s hs_map v hv
        by_cases hm'0 : m' = 0
        · subst hm'0
          simp only [phaseDesc, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            Nat.sub_self] at hs_map
          have hemp := h_exhaust 1 le_rfl hmL s hs_map X_in M_in hXin_sub
          obtain ⟨X_out, hX_out_def⟩ :
              ∃ s_out, (sspRunSteps G w N h Φ ε Δ X.card X_in M_in s).2.1 = s_out := ⟨_, rfl⟩
          rw [hX_out_def] at hv hemp
          have hv_ball0 : v ∈ hstBall G w N h Φ ε Δ X_out v 1 0 :=
            mem_hstBall_zero Δ hΔ X_out v hv 1 le_rfl hmL
          have h1_le_b0 : (1 : ℝ) ≤ ((hstBall G w N h Φ ε Δ X_out v 1 0).card : ℝ) := by
            exact_mod_cast Finset.Nonempty.card_pos ⟨v, hv_ball0⟩
          have hX_lt_mu0 : X.card < hstMu N 0 := by
            have hX_le_n : X.card ≤ n := by
              simpa [Fintype.card_fin] using Finset.card_le_univ X
            have hmu0 := h_params.mu_zero_ge
            omega
          have hmu0_pos : (0 : ℝ) < (hstMu N 0 : ℝ) := by
            unfold hstMu; positivity
          have h_lo_ok : (X.card : ℝ) / (hstMu N (1 - 1) : ℝ) ≤
              ((hstBall G w N h Φ ε Δ X_out v 1 0).card : ℝ) := by
            simp only [Nat.sub_self]
            have h_div_lt1 : (X.card : ℝ) / (hstMu N 0 : ℝ) < 1 := by
              rw [div_lt_one hmu0_pos]
              exact_mod_cast hX_lt_mu0
            linarith
          have hv_not_cand : v ∉ sspCands G w N h Φ ε Δ X.card X_out 1 := by
            rw [hemp]; simp
          rw [mem_sspCands_iff] at hv_not_cand
          have h_gt_out : (X.card : ℝ) / (hstMu N 1 : ℝ) <
              ((hstBall G w N h Φ ε Δ X_out v 1 (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := by
            by_contra h_le
            push_neg at h_le
            exact hv_not_cand ⟨hv, h_lo_ok, h_le⟩
          have hXout_sub : X_out ⊆ X_in := by
            rw [← hX_out_def]
            exact h_sub_run s X_in M_in
          have h_mono_X : ((hstBall G w N h Φ ε Δ X_out v 1 (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) ≤
              ((hstBall G w N h Φ ε Δ X_in v 1 (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (hstBall_mono_set Δ hXout_sub v 1 _)
          linarith
        · have hm'1 : 1 ≤ m' := by omega
          simp only [phaseDesc, List.flatMap_cons, Nat.add_sub_cancel] at hs_map
          obtain ⟨len1, hlen1_def⟩ : ∃ k, hstMu N m' = k := ⟨_, rfl⟩
          rw [hlen1_def] at hs_map
          obtain ⟨s1, hs1_def⟩ : ∃ l, s.take len1 = l := ⟨_, rfl⟩
          obtain ⟨s2, hs2_def⟩ : ∃ l, s.drop len1 = l := ⟨_, rfl⟩
          have hs_split : s1 ++ s2 = s := by
            rw [← hs1_def, ← hs2_def]
            exact List.take_append_drop len1 s
          have hs1_map : s1.map Prod.fst = List.replicate len1 (m' + 1) := by
            rw [← hs1_def, List.map_take, hs_map]
            have htake : List.take (List.replicate len1 (m' + 1)).length
                (List.replicate len1 (m' + 1) ++
                  (phaseDesc m').flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ)) =
                List.replicate len1 (m' + 1) := List.take_left
            rwa [List.length_replicate] at htake
          have hs2_map : s2.map Prod.fst =
              (phaseDesc m').flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ) := by
            rw [← hs2_def, List.map_drop, hs_map]
            have hdrop : List.drop (List.replicate len1 (m' + 1)).length
                (List.replicate len1 (m' + 1) ++
                  (phaseDesc m').flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ)) =
                (phaseDesc m').flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ) := List.drop_left
            rwa [List.length_replicate] at hdrop
          rw [← hs_split, h_append s1 s2 X_in M_in] at hv
          obtain ⟨r1, hr1_def⟩ :
              ∃ r, sspRunSteps G w N h Φ ε Δ X.card X_in M_in s1 = r := ⟨_, rfl⟩
          rw [hr1_def] at hv
          obtain ⟨X_mid, hXmid_def⟩ : ∃ xm, r1.2.1 = xm := ⟨_, rfl⟩
          obtain ⟨M_mid, hMmid_def⟩ : ∃ mm, r1.2.2 = mm := ⟨_, rfl⟩
          rw [hXmid_def, hMmid_def] at hv
          have hXmid_in : X_mid ⊆ X_in := by
            rw [← hXmid_def, ← hr1_def]
            exact h_sub_run s1 X_in M_in
          have hXmid_X : X_mid ⊆ X := Finset.Subset.trans hXmid_in hXin_sub
          have hv_mid : v ∈ X_mid := h_sub_run s2 X_mid M_mid hv
          have h_ih_v := ih hm'1 (by omega) X_mid M_mid hXmid_X s2 hs2_map v hv
          rw [h_phase_bdry m' hm'1 hmL X_mid v] at h_ih_v
          have hs1_map' : s1.map Prod.fst = List.replicate (hstMu N ((m' + 1) - 1)) (m' + 1) := by
            rw [Nat.add_sub_cancel, hlen1_def]
            exact hs1_map
          have hemp1 := h_exhaust (m' + 1) (by omega) hmL s1 hs1_map' X_in M_in hXin_sub
          rw [hr1_def, hXmid_def] at hemp1
          have hv_not_cand : v ∉ sspCands G w N h Φ ε Δ X.card X_mid (m' + 1) := by
            rw [hemp1]; simp
          rw [mem_sspCands_iff] at hv_not_cand
          have h_lo_ok : (X.card : ℝ) / (hstMu N ((m' + 1) - 1) : ℝ) ≤
              ((hstBall G w N h Φ ε Δ X_mid v (m' + 1) 0).card : ℝ) := by
            rw [Nat.add_sub_cancel]
            exact le_of_lt h_ih_v
          have h_gt_mid : (X.card : ℝ) / (hstMu N (m' + 1) : ℝ) <
              ((hstBall G w N h Φ ε Δ X_mid v (m' + 1) (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := by
            by_contra h_le
            push_neg at h_le
            exact hv_not_cand ⟨hv_mid, h_lo_ok, h_le⟩
          have h_mono_X :
              ((hstBall G w N h Φ ε Δ X_mid v (m' + 1) (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) ≤
              ((hstBall G w N h Φ ε Δ X_in v (m' + 1) (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (hstBall_mono_set Δ hXmid_in v (m' + 1) _)
          linarith
    obtain ⟨steps, hsteps_def⟩ :
        ∃ s, List.ofFn (fun i : Fin (hstTotalSlots N) => ((sspSlotPhases N).get i, (τ i).1)) = s :=
      ⟨_, rfl⟩
    rw [hsteps_def]
    obtain ⟨X_res, hX_res_def⟩ :
        ∃ xr, (sspRunSteps G w N h Φ ε Δ X.card X M steps).2.1 = xr := ⟨_, rfl⟩
    rw [hX_res_def]
    intro v hv
    have hs_map : steps.map Prod.fst =
        (phaseDesc (hstPhaseCount N)).flatMap (fun ℓ => List.replicate (hstMu N (ℓ - 1)) ℓ) := by
      rw [← hsteps_def, List.map_ofFn]
      change List.ofFn (sspSlotPhases N).get = _
      rw [List.ofFn_get]
      rfl
    rw [← hX_res_def] at hv
    have h_final := h_chain (hstPhaseCount N) h_params.one_le_L le_rfl X M
      (Finset.Subset.refl X) steps hs_map v hv
    rwa [h_params.mu_L_eq, Nat.cast_ofNat] at h_final

  
  
  
  have h_ssp : SSPDetSpec N n G w h Φ ε := by
    refine ⟨hopDist_toReal_bounds, ?_⟩
    intro X M hX2 hMX Δ hΔ h_diam
    have h2_le_Δ : 2 ≤ Δ := by
      rcases Finset.one_lt_card.mp (by omega : 1 < X.card) with ⟨u, hu, v, hv, huv⟩
      have h1 := two_le_hopDist (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v huv
      have h2 := h_diam u hu v hv
      exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt hΔ)).mp (le_trans h1 h2)
    refine ⟨h2_le_Δ, ?_, ?_⟩
    · intro τ
      dsimp only
      obtain ⟨steps, hsteps_def⟩ :
          ∃ s, List.ofFn (fun i : Fin (hstTotalSlots N) => ((sspSlotPhases N).get i, (τ i).1)) = s :=
        ⟨_, rfl⟩
      have h_steps : ∀ p ∈ steps,
          1 ≤ p.1 ∧ p.1 ≤ hstPhaseCount N ∧ p.2 < hstRadiusSteps N Φ ε := by
        intro p hp
        rw [← hsteps_def] at hp
        rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
        have h_slot_mem : (sspSlotPhases N).get i ∈ sspSlotPhases N := List.get_mem _ _
        have h_bds := h_params.slot_phases_bounds _ h_slot_mem
        exact ⟨h_bds.1, h_bds.2, (τ i).isLt⟩
      obtain ⟨res, hres_def⟩ :
          ∃ r, sspRunSteps G w N h Φ ε Δ X.card X M steps = r := ⟨_, rfl⟩
      obtain ⟨X_res, hXres_def⟩ : ∃ xr, res.2.1 = xr := ⟨_, rfl⟩
      obtain ⟨M_res, hMres_def⟩ : ∃ mr, res.2.2 = mr := ⟨_, rfl⟩
      have h_run := h_run_steps Δ hΔ X.card steps h_steps X M hMX
      dsimp only at h_run
      rw [hres_def, hXres_def, hMres_def] at h_run
      rcases h_run with ⟨h_len, h_pw, h_disj_res, h_fold, h_res_sub, h_resM_sub,
        h_t_spec, h_res_sep⟩
      have h_geom_X := h_geom Δ hΔ X
      have hX_le_N : X.card ≤ N := by
        have hX_le_n : X.card ≤ n := by
          simpa [Fintype.card_fin] using Finset.card_le_univ X
        omega
      obtain ⟨tclus, htclus_raw⟩ :
          ∃ l, sspTaggedClusters G w N h Φ ε X M Δ τ = l := ⟨_, rfl⟩
      rw [htclus_raw]
      have htclus_def : tclus =
          if X_res.Nonempty then res.1 ++ [(0, X_res, M_res)] else res.1 := by
        rw [← htclus_raw]
        unfold sspTaggedClusters
        dsimp only
        rw [hsteps_def, hres_def, hXres_def, hMres_def]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · 
        rw [htclus_def]
        split_ifs with hne
        · simp
        · intro h_nil
          have hemp : X_res = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          rw [h_nil, hemp, List.foldr_nil] at h_fold
          rw [← h_fold] at hX2
          simp at hX2
      · 
        rw [htclus_def]
        split_ifs with hne
        · simp only [List.length_append, List.length_singleton]
          simp only [hne, ↓reduceIte] at h_len
          omega
        · simp only [hne, ↓reduceIte, add_zero] at h_len
          omega
      · 
        rw [htclus_def]
        split_ifs with hne
        · rw [List.map_append, List.map_singleton, List.pairwise_append]
          refine ⟨h_pw, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          rw [List.mem_singleton] at hb
          subst hb
          rcases List.mem_map.mp ha with ⟨t, ht, rfl⟩
          exact h_disj_res t ht
        · exact h_pw
      · 
        rw [htclus_def]
        split_ifs with hne
        · rw [List.foldr_append, List.foldr_cons, List.foldr_nil, Finset.union_empty]
          exact h_fold
        · have hemp : X_res = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
          rw [← hemp]
          exact h_fold
      · 
        intro t ht
        have ht_cases : t ∈ res.1 ∨ (X_res.Nonempty ∧ t = (0, X_res, M_res)) := by
          rw [htclus_def] at ht
          split_ifs at ht with hne
          · rcases List.mem_append.mp ht with ht1 | ht2
            · exact Or.inl ht1
            · exact Or.inr ⟨hne, List.mem_singleton.mp ht2⟩
          · exact Or.inl ht
        rcases ht_cases with ht_carved | ⟨hne_res, rfl⟩
        · 
          rcases h_t_spec t ht_carved with ⟨ht1, htL, ht_ne, ht_sub, htM_sub, ht_card,
            ⟨X_sub, x, R, hX_sub, hx, hRk, ht_eq⟩, ht_sep⟩
          have h_geom_sub := h_geom Δ hΔ X_sub
          refine ⟨ht_ne, ht_sub, htM_sub, ?_, fun _ => ht_card, ?_, ?_⟩
          · intro u hu v hv
            rw [ht_eq] at hu hv
            exact h_geom_sub.2.1 t.1 R ht1 htL hRk x u v hu hv
          · intro u hu v hv
            rcases ht_sep u hu v hv with ⟨X_sub2, x2, ℓ2, S2, _, h1_2, hL_2, hor⟩
            have h_ann := (h_geom Δ hΔ X_sub2).2.2.1
            rcases hor with ⟨hu_in, hv_out⟩ | ⟨hv_in, hu_out⟩
            · exact (h_ann ℓ2 S2 x2 u v h1_2 hL_2 hu_in hv_out).1
            · exact (h_ann ℓ2 S2 x2 v u h1_2 hL_2 hv_in hu_out).2
          · intro hΔ8
            rw [ht_eq]
            exact h_geom_sub.2.2.2.2 hΔ8 x hx t.1 (R : ℤ) ht1 htL (by omega) (by omega)
        · 
          dsimp only
          refine ⟨hne_res, h_res_sub, h_resM_sub, ?_, ?_, ?_, ?_⟩
          · intro u hu v hv
            have hu_raw : u ∈ (sspRunSteps G w N h Φ ε Δ X.card X M
                (List.ofFn (fun i : Fin (hstTotalSlots N) => ((sspSlotPhases N).get i, (τ i).1)))).2.1 := by
              rwa [hsteps_def, hres_def, hXres_def]
            have hv_raw : v ∈ (sspRunSteps G w N h Φ ε Δ X.card X M
                (List.ofFn (fun i : Fin (hstTotalSlots N) => ((sspSlotPhases N).get i, (τ i).1)))).2.1 := by
              rwa [hsteps_def, hres_def, hXres_def]
            obtain ⟨Bu, hBu_def⟩ :
                ∃ bu, hstBall G w N h Φ ε Δ X u (hstPhaseCount N) (hstRadiusSteps N Φ ε : ℤ) = bu :=
              ⟨_, rfl⟩
            obtain ⟨Bv, hBv_def⟩ :
                ∃ bv, hstBall G w N h Φ ε Δ X v (hstPhaseCount N) (hstRadiusSteps N Φ ε : ℤ) = bv :=
              ⟨_, rfl⟩
            have hBu_gt : (X.card : ℝ) / 2 < (Bu.card : ℝ) := by
              rw [← hBu_def]; exact h_res_large X M Δ hΔ τ u hu_raw
            have hBv_gt : (X.card : ℝ) / 2 < (Bv.card : ℝ) := by
              rw [← hBv_def]; exact h_res_large X M Δ hΔ τ v hv_raw
            have h_sum_gt_r : (X.card : ℝ) < (Bu.card : ℝ) + (Bv.card : ℝ) := by linarith
            have h_sum_gt : X.card < Bu.card + Bv.card := by exact_mod_cast h_sum_gt_r
            have hBu_sub : Bu ⊆ X := by rw [← hBu_def]; exact hstBall_subset Δ X u _ _
            have hBv_sub : Bv ⊆ X := by rw [← hBv_def]; exact hstBall_subset Δ X v _ _
            have h_union_sub : Bu ∪ Bv ⊆ X := Finset.union_subset hBu_sub hBv_sub
            have h_union_le : (Bu ∪ Bv).card ≤ X.card := Finset.card_le_card h_union_sub
            have h_eq_ui := Finset.card_union_add_card_inter Bu Bv
            have h_inter_pos : 0 < (Bu ∩ Bv).card := by omega
            rcases Finset.card_pos.mp h_inter_pos with ⟨z, hz⟩
            rw [Finset.mem_inter, ← hBu_def, ← hBv_def] at hz
            exact h_geom_X.2.2.2.1 u v z hz.1 hz.2
          · intro h10
            omega
          · intro u hu v hv
            rcases h_res_sep u hu v hv with ⟨X_sub2, x2, ℓ2, S2, _, h1_2, hL_2, hv_in, hu_out⟩
            exact ((h_geom Δ hΔ X_sub2).2.2.1 ℓ2 S2 x2 v u h1_2 hL_2 hv_in hu_out).2
          · intro hΔ8
            exfalso
            rcases hne_res with ⟨v, hv⟩
            have hv_X : v ∈ X := h_res_sub hv
            have hv_raw : v ∈ (sspRunSteps G w N h Φ ε Δ X.card X M
                (List.ofFn (fun i : Fin (hstTotalSlots N) => ((sspSlotPhases N).get i, (τ i).1)))).2.1 := by
              rwa [hsteps_def, hres_def, hXres_def]
            have hBv_gt : (X.card : ℝ) / 2 <
                ((hstBall G w N h Φ ε Δ X v (hstPhaseCount N)
                  (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := h_res_large X M Δ hΔ τ v hv_raw
            have hBv_eq1 : (hstBall G w N h Φ ε Δ X v (hstPhaseCount N)
                (hstRadiusSteps N Φ ε : ℤ)).card = 1 :=
              h_geom_X.2.2.2.2 hΔ8 v hv_X (hstPhaseCount N) (hstRadiusSteps N Φ ε : ℤ)
                h_params.one_le_L le_rfl (by positivity) le_rfl
            rw [hBv_eq1, Nat.cast_one] at hBv_gt
            have hX2_r : (2 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hX2
            linarith
    · intro X_cur _ x hx ℓ hℓ1 hℓL
      exact (h_geom Δ hΔ X_cur).1 x hx ℓ hℓ1 hℓL

  
  
  
  have h_hse : HSERunDetSpec N n G w h Φ ε := by
    have h_valid_go : ∀ (cs : List (RawHST (Fin n))),
        (∀ c ∈ cs, ValidRawHST c) → ValidRawHST.go cs := by
      intro cs
      induction cs with
      | nil => intro _; exact True.intro
      | cons c cs' ih =>
        intro h_all
        simp only [ValidRawHST.go]
        exact ⟨h_all c List.mem_cons_self, ih (fun c' hc' => h_all c' (List.mem_cons_of_mem _ hc'))⟩
    have h_dist_go_bounds : ∀ (Δ : ℝ), 0 < Δ → ∀ (cs : List (RawHST (Fin n))),
        (∀ c ∈ cs, ∀ u v : Fin n, 0 ≤ c.dist u v ∧ c.dist u v ≤ Δ) →
        ∀ u v : Fin n, 0 ≤ RawHST.dist.go u v Δ cs ∧ RawHST.dist.go u v Δ cs ≤ Δ := by
      intro Δ hΔ cs
      induction cs with
      | nil =>
        intro _ u v
        simp only [RawHST.dist.go]
        exact ⟨le_of_lt hΔ, le_rfl⟩
      | cons c cs' ih =>
        intro h_all u v
        simp only [RawHST.dist.go]
        split_ifs with h_in
        · exact h_all c List.mem_cons_self u v
        · exact ih (fun c' hc' => h_all c' (List.mem_cons_of_mem _ hc')) u v
    have h_dist_go_mem : ∀ (Δ : ℝ) (cs : List (RawHST (Fin n))),
        (cs.map RawHST.cluster).Pairwise Disjoint →
        ∀ c ∈ cs, ∀ u v : Fin n, u ∈ c.cluster → v ∈ c.cluster →
          RawHST.dist.go u v Δ cs = c.dist u v := by
      intro Δ cs
      induction cs with
      | nil => intro _ c hc; exact absurd hc List.not_mem_nil
      | cons hd tl ih =>
        intro h_pw c hc u v hu hv
        rw [List.map_cons, List.pairwise_cons] at h_pw
        simp only [RawHST.dist.go]
        rcases List.mem_cons.mp hc with rfl | h_tl
        · simp [hu, hv]
        · have h_disj : Disjoint hd.cluster c.cluster :=
            h_pw.1 c.cluster (List.mem_map_of_mem h_tl)
          have hu_not : u ∉ hd.cluster := Finset.disjoint_right.mp h_disj hu
          simp only [hu_not, false_and, ↓reduceIte]
          exact ih h_pw.2 c h_tl u v hu hv
    have h_dist_go_none : ∀ (Δ : ℝ) (cs : List (RawHST (Fin n))) (u v : Fin n),
        (∀ c ∈ cs, ¬(u ∈ c.cluster ∧ v ∈ c.cluster)) →
        RawHST.dist.go u v Δ cs = Δ := by
      intro Δ cs u v
      induction cs with
      | nil => intro _; simp [RawHST.dist.go]
      | cons hd tl ih =>
        intro h_none
        simp only [RawHST.dist.go]
        have h_hd := h_none hd List.mem_cons_self
        simp only [h_hd, ↓reduceIte]
        exact ih (fun c hc => h_none c (List.mem_cons_of_mem _ hc))
    have h_leaf_spec : ∀ (X M : Finset (Fin n)), X.card = 1 → M ⊆ X →
        ∀ Δ : ℝ, 0 < Δ →
          ValidRawHST (RawHST.leaf X) ∧
          (RawHST.leaf X).cluster = X ∧
          (RawHST.leaf X).topLabel ≤ Δ ∧
          M ⊆ M ∧
          (∀ u v : Fin n, 0 ≤ (RawHST.leaf X).dist u v ∧ (RawHST.leaf X).dist u v ≤ Δ) ∧
          (∀ u ∈ X, ∀ v ∈ X,
            hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
              ENNReal.ofReal ((RawHST.leaf X).dist u v)) ∧
          (∀ u ∈ M, ∀ v ∈ X,
            ENNReal.ofReal ((RawHST.leaf X).dist u v) ≤
              ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
                hopDist G w h u v) := by
      intro X M hX1 _ Δ hΔ
      refine ⟨hX1, rfl, le_of_lt hΔ, Finset.Subset.refl M, ?_, ?_, ?_⟩
      · intro u v
        simp only [RawHST.dist]
        exact ⟨le_rfl, le_of_lt hΔ⟩
      · intro u hu v hv
        have huv : u = v := Finset.card_le_one.mp (le_of_eq hX1) u hu v hv
        subst huv
        simp [RawHST.dist, hopDist_self]
      · intro u _ v _
        simp [RawHST.dist]
    refine ⟨?_⟩
    intro d
    induction d with
    | zero =>
      intro X M hX_ne hMX Δ hΔ _ h_depth ω
      have hX_le1 : X.card ≤ 1 := by
        by_contra h_gt
        have h2 : 2 ≤ X.card := by omega
        have h10 := (h_depth h2).1
        omega
      have hX1 : X.card = 1 := le_antisymm hX_le1 (Finset.Nonempty.card_pos hX_ne)
      simpa only [hseRun] using h_leaf_spec X M hX1 hMX Δ hΔ
    | succ d ih =>
      intro X M hX_ne hMX Δ hΔ h_diam h_depth ω
      rcases ω with ⟨τ, sub⟩
      dsimp only [hseRun]
      split_ifs with hX_le1
      · dsimp only
        have hX1 : X.card = 1 := le_antisymm hX_le1 (Finset.Nonempty.card_pos hX_ne)
        exact h_leaf_spec X M hX1 hMX Δ hΔ
      · dsimp only
        have hX2 : 2 ≤ X.card := by omega
        have hΔ_lt_pow : Δ < 8 * (2 : ℝ) ^ d := by
          simpa [Nat.add_sub_cancel] using (h_depth hX2).2
        obtain ⟨tclus, htclus_def⟩ :
            ∃ l, sspTaggedClusters G w N h Φ ε X M Δ τ = l := ⟨_, rfl⟩
        obtain ⟨clus, hclus_def⟩ :
            ∃ l, sspClusters G w N h Φ ε X M Δ τ = l := ⟨_, rfl⟩
        rw [hclus_def]
        obtain ⟨childRes, hchildRes_def⟩ :
            ∃ f : Fin clus.length → RawHST (Fin n) × Finset (Fin n),
              (fun idx : Fin clus.length =>
                if hq : idx.1 < N then
                  hseRun G w N h Φ ε d (clus.get idx).1 (clus.get idx).2 (Δ / 2) (sub ⟨idx.1, hq⟩)
                else
                  (RawHST.leaf (clus.get idx).1, (clus.get idx).2)) = f := ⟨_, rfl⟩
        have hchildRes_app : ∀ idx : Fin clus.length,
            (if hq : idx.1 < N then
              hseRun G w N h Φ ε d (clus.get idx).1 (clus.get idx).2 (Δ / 2) (sub ⟨idx.1, hq⟩)
            else
              (RawHST.leaf (clus.get idx).1, (clus.get idx).2)) = childRes idx :=
          fun idx => congrFun hchildRes_def idx
        simp_rw [hchildRes_app]
        obtain ⟨children, hchildren_def⟩ :
            ∃ l : List (RawHST (Fin n)), List.ofFn (fun idx : Fin clus.length => (childRes idx).1) = l :=
          ⟨_, rfl⟩
        obtain ⟨M_out, hM_out_def⟩ :
            ∃ s : Finset (Fin n), Finset.univ.biUnion (fun idx : Fin clus.length => (childRes idx).2) = s :=
          ⟨_, rfl⟩
        rw [hchildren_def, hM_out_def]
        have h_sc := (h_ssp.scale_spec X M hX2 hMX Δ hΔ h_diam).2.1 τ
        dsimp only at h_sc
        rw [htclus_def] at h_sc
        rcases h_sc with ⟨htclus_ne, htclus_len, htclus_pw, htclus_fold, htclus_all⟩
        have hclus_eq : clus = tclus.map (fun t => (t.2.1, t.2.2)) := by
          rw [← hclus_def, ← htclus_def]
          rfl
        have hclus_len : clus.length = tclus.length := by rw [hclus_eq, List.length_map]
        have h_child_t : ∀ idx : Fin clus.length,
            tclus.get (idx.cast hclus_len) ∈ tclus ∧
            clus.get idx =
              ((tclus.get (idx.cast hclus_len)).2.1, (tclus.get (idx.cast hclus_len)).2.2) ∧
            idx.1 < N := by
          intro idx
          refine ⟨List.get_mem _ _, ?_, ?_⟩
          · have h_some : clus[idx.1]? = (tclus.map (fun t => (t.2.1, t.2.2)))[idx.1]? :=
              congrArg (fun l => l[idx.1]?) hclus_eq
            rw [List.getElem?_eq_getElem idx.isLt, List.getElem?_map,
              List.getElem?_eq_getElem (by omega : idx.1 < tclus.length)] at h_some
            simp only [List.get_eq_getElem, Fin.val_cast, Option.map_some,
              Option.some.injEq] at h_some ⊢
            exact h_some
          · omega
        have h_child_spec : ∀ idx : Fin clus.length,
            ValidRawHST (childRes idx).1 ∧
            (childRes idx).1.cluster = (clus.get idx).1 ∧
            (childRes idx).1.topLabel ≤ Δ / 2 ∧
            (childRes idx).2 ⊆ (clus.get idx).2 ∧
            (∀ u v : Fin n, 0 ≤ (childRes idx).1.dist u v ∧ (childRes idx).1.dist u v ≤ Δ / 2) ∧
            (∀ u ∈ (clus.get idx).1, ∀ v ∈ (clus.get idx).1,
              hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
                ENNReal.ofReal ((childRes idx).1.dist u v)) ∧
            (∀ u ∈ (childRes idx).2, ∀ v ∈ (clus.get idx).1,
              ENNReal.ofReal ((childRes idx).1.dist u v) ≤
                ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
                  hopDist G w h u v) := by
          intro idx
          rcases h_child_t idx with ⟨ht_mem, hc_eq, hq⟩
          obtain ⟨t, ht_def⟩ : ∃ t_el, tclus.get (idx.cast hclus_len) = t_el := ⟨_, rfl⟩
          rw [ht_def] at ht_mem hc_eq
          have hcr_eq : childRes idx =
              hseRun G w N h Φ ε d (clus.get idx).1 (clus.get idx).2 (Δ / 2) (sub ⟨idx.1, hq⟩) := by
            rw [← hchildRes_app idx, dif_pos hq]
          rcases htclus_all t ht_mem with ⟨ht_ne, ht_subX, htM_sub, ht_diam, _, _, ht_lt8⟩
          have hc1_ne : (clus.get idx).1.Nonempty := by rw [hc_eq]; exact ht_ne
          have hc2_sub : (clus.get idx).2 ⊆ (clus.get idx).1 := by
            rw [hc_eq]
            exact Finset.Subset.trans htM_sub Finset.inter_subset_right
          have hc_diam : ∀ u ∈ (clus.get idx).1, ∀ v ∈ (clus.get idx).1,
              hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v ≤
                ENNReal.ofReal (Δ / 2) := by
            rw [hc_eq]; exact ht_diam
          have hc_depth : 2 ≤ (clus.get idx).1.card → 1 ≤ d ∧ Δ / 2 < 8 * (2 : ℝ) ^ (d - 1) := by
            intro hc2
            by_cases hd0 : d = 0
            · exfalso
              subst hd0
              simp only [pow_zero, mul_one] at hΔ_lt_pow
              have h1 := ht_lt8 hΔ_lt_pow
              rw [hc_eq] at hc2
              dsimp only at hc2
              omega
            · have hd1 : 1 ≤ d := by omega
              have h_pow : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
                conv_lhs => rw [← Nat.sub_add_cancel hd1, pow_succ]
              refine ⟨hd1, ?_⟩
              rw [h_pow] at hΔ_lt_pow
              linarith
          have h_ih_idx := ih (clus.get idx).1 (clus.get idx).2 hc1_ne hc2_sub
            (Δ / 2) (by linarith) hc_diam hc_depth (sub ⟨idx.1, hq⟩)
          dsimp only at h_ih_idx
          rwa [← hcr_eq] at h_ih_idx
        have h_clusters_eq : children.map RawHST.cluster = tclus.map (fun t => t.2.1) := by
          rw [← hchildren_def, List.map_ofFn]
          have h_fn : (RawHST.cluster ∘ fun idx : Fin clus.length => (childRes idx).1) =
              fun idx : Fin clus.length => (clus.get idx).1 := by
            funext idx
            exact (h_child_spec idx).2.1
          rw [h_fn]
          have h_map_get : List.ofFn (fun idx : Fin clus.length => (clus.get idx).1) =
              clus.map Prod.fst := by
            change List.ofFn (Prod.fst ∘ clus.get) = clus.map Prod.fst
            rw [← List.map_ofFn, List.ofFn_get]
          rw [h_map_get, hclus_eq, List.map_map]
          rfl
        have h_children_pw : (children.map RawHST.cluster).Pairwise Disjoint := by
          rw [h_clusters_eq]
          exact htclus_pw
        have h_child_disj : ∀ i j : Fin clus.length, i ≠ j →
            Disjoint (childRes i).1.cluster (childRes j).1.cluster := by
          intro i j hij
          let f_cl : Fin clus.length → Finset (Fin n) := fun k => (childRes k).1.cluster
          have hp : (List.ofFn f_cl).Pairwise Disjoint := by
            have h_eq_map : List.ofFn f_cl = children.map RawHST.cluster := by
              rw [← hchildren_def, List.map_ofFn]
              rfl
            rw [h_eq_map]
            exact h_children_pw
          have hlen_f : clus.length = (List.ofFn f_cl).length := (List.length_ofFn).symm
          let i1 : Fin (List.ofFn f_cl).length := i.cast hlen_f
          let i2 : Fin (List.ofFn f_cl).length := j.cast hlen_f
          have hi_ne : i1 ≠ i2 := by
            intro heq
            apply hij
            ext
            exact congrArg (fun k : Fin (List.ofFn f_cl).length => k.1) heq
          have h_disj : Disjoint ((List.ofFn f_cl).get i1) ((List.ofFn f_cl).get i2) := by
            rcases lt_or_gt_of_ne hi_ne with hlt | hgt
            · exact (List.pairwise_iff_get.mp hp) i1 i2 hlt
            · exact ((List.pairwise_iff_get.mp hp) i2 i1 hgt).symm
          simpa [i1, i2, f_cl] using h_disj
        have h_children_ne : children ≠ [] := by
          intro h_nil
          have h0 : children.length = 0 := by rw [h_nil]; rfl
          rw [← hchildren_def, List.length_ofFn, hclus_len] at h0
          exact htclus_ne (List.eq_nil_of_length_eq_zero h0)
        have h_children_fold :
            children.foldr (fun c acc => c.cluster ∪ acc) ∅ = X := by
          have h1 := List.foldr_map (f := RawHST.cluster)
            (g := fun (s acc : Finset (Fin n)) => s ∪ acc) (l := children) (init := ∅)
          have h2 := List.foldr_map (f := fun (t : ℕ × Finset (Fin n) × Finset (Fin n)) => t.2.1)
            (g := fun (s acc : Finset (Fin n)) => s ∪ acc) (l := tclus) (init := ∅)
          rw [← h1, h_clusters_eq, h2]
          exact htclus_fold
        refine ⟨?_, rfl, le_rfl, ?_, ?_, ?_, ?_⟩
        · 
          simp only [ValidRawHST]
          refine ⟨hΔ, h_children_ne, ?_, ?_, h_children_pw, h_children_fold⟩
          · refine h_valid_go children (fun c hc => ?_)
            rw [← hchildren_def] at hc
            rcases List.mem_ofFn.mp hc with ⟨idx, rfl⟩
            exact (h_child_spec idx).1
          · intro c hc
            rw [← hchildren_def] at hc
            rcases List.mem_ofFn.mp hc with ⟨idx, rfl⟩
            rcases h_child_t idx with ⟨ht_mem, hc_eq, _⟩
            have h_top : (childRes idx).1.topLabel ≤ Δ / 2 := (h_child_spec idx).2.2.1
            have h_cne : (childRes idx).1.cluster.Nonempty := by
              rw [(h_child_spec idx).2.1, hc_eq]
              exact (htclus_all _ ht_mem).1
            exact ⟨by linarith, h_cne⟩
        · 
          intro u hu
          rw [← hM_out_def, Finset.mem_biUnion] at hu
          rcases hu with ⟨idx, _, hu_idx⟩
          rcases h_child_t idx with ⟨ht_mem, hc_eq, _⟩
          have hu_c2 : u ∈ (clus.get idx).2 := (h_child_spec idx).2.2.2.1 hu_idx
          rw [hc_eq] at hu_c2
          exact (Finset.mem_inter.mp ((htclus_all _ ht_mem).2.2.1 hu_c2)).1
        · 
          intro u v
          simp only [RawHST.dist]
          split_ifs with huv
          · exact ⟨le_rfl, le_of_lt hΔ⟩
          · refine h_dist_go_bounds Δ hΔ children (fun c hc x y => ?_) u v
            rw [← hchildren_def] at hc
            rcases List.mem_ofFn.mp hc with ⟨idx, rfl⟩
            have hb := (h_child_spec idx).2.2.2.2.1 x y
            exact ⟨hb.1, by linarith [hb.2]⟩
        · 
          intro u hu v hv
          simp only [RawHST.dist]
          split_ifs with huv
          · subst huv
            simp [hopDist_self]
          · by_cases h_same : ∃ c ∈ children, u ∈ c.cluster ∧ v ∈ c.cluster
            · rcases h_same with ⟨c, hc_mem, hu_c, hv_c⟩
              rw [h_dist_go_mem Δ children h_children_pw c hc_mem u v hu_c hv_c]
              rw [← hchildren_def] at hc_mem
              rcases List.mem_ofFn.mp hc_mem with ⟨idx, rfl⟩
              rw [(h_child_spec idx).2.1] at hu_c hv_c
              exact (h_child_spec idx).2.2.2.2.2.1 u hu_c v hv_c
            · push_neg at h_same
              have h_none : ∀ c ∈ children, ¬(u ∈ c.cluster ∧ v ∈ c.cluster) :=
                fun c hc hboth => h_same c hc hboth.1 hboth.2
              rw [h_dist_go_none Δ children u v h_none]
              exact h_diam u hu v hv
        · 
          intro u hu v hv
          simp only [RawHST.dist]
          split_ifs with huv
          · simp
          · rw [← hM_out_def, Finset.mem_biUnion] at hu
            rcases hu with ⟨idx, _, hu_idx⟩
            rcases h_child_t idx with ⟨ht_mem, hc_eq, _⟩
            have hu_c2 : u ∈ (clus.get idx).2 := (h_child_spec idx).2.2.2.1 hu_idx
            have hu_c1 : u ∈ (clus.get idx).1 := by
              rw [hc_eq] at hu_c2 ⊢
              exact (Finset.mem_inter.mp ((htclus_all _ ht_mem).2.2.1 hu_c2)).2
            by_cases hv_c1 : v ∈ (clus.get idx).1
            · have hc_mem : (childRes idx).1 ∈ children := by
                rw [← hchildren_def]
                exact List.mem_ofFn.mpr ⟨idx, rfl⟩
              have hu_cl : u ∈ (childRes idx).1.cluster := by
                rwa [(h_child_spec idx).2.1]
              have hv_cl : v ∈ (childRes idx).1.cluster := by
                rwa [(h_child_spec idx).2.1]
              rw [h_dist_go_mem Δ children h_children_pw (childRes idx).1 hc_mem u v hu_cl hv_cl]
              exact (h_child_spec idx).2.2.2.2.2.2 u hu_idx v hv_c1
            · have h_none : ∀ c ∈ children, ¬(u ∈ c.cluster ∧ v ∈ c.cluster) := by
                intro c hc
                rw [← hchildren_def] at hc
                rcases List.mem_ofFn.mp hc with ⟨idx', rfl⟩
                by_cases h_eq_idx : idx' = idx
                · subst h_eq_idx
                  rw [(h_child_spec idx').2.1]
                  exact fun hboth => hv_c1 hboth.2
                · intro hboth
                  have h_disj := h_child_disj idx' idx h_eq_idx
                  have hu_cl : u ∈ (childRes idx).1.cluster := by
                    rwa [(h_child_spec idx).2.1]
                  exact Finset.disjoint_left.mp h_disj hboth.1 hu_cl
              rw [h_dist_go_none Δ children u v h_none]
              obtain ⟨t, ht_def⟩ : ∃ t_el, tclus.get (idx.cast hclus_len) = t_el := ⟨_, rfl⟩
              rw [ht_def] at ht_mem hc_eq
              have hu_t2 : u ∈ t.2.2 := by
                rw [hc_eq] at hu_c2
                exact hu_c2
              have hv_out : v ∈ X \ t.2.1 := by
                rw [Finset.mem_sdiff]
                rw [hc_eq] at hv_c1
                exact ⟨hv, hv_c1⟩
              exact (htclus_all t ht_mem).2.2.2.2.2.1 u hu_t2 v hv_out

  exact ⟨h_ssp, h_hse⟩

theorem hse_exclusion_prob_bound (N n : ℕ) (hn : 2 ≤ n) (hnN : n ≤ N)
    (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 2 ≤ w e)
    (h : ℕ) (hh : 1 ≤ h)
    (Φ : ℝ) (hΦ_ge : 2 ≤ Φ)
    (hΦ_diam : ∀ u v : Fin n, hopDist G w h u v ≤ ENNReal.ofReal Φ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (h_params : HSTParamSpec N Φ ε)
    (h_ssp : SSPDetSpec N n G w h Φ ε)
    (h_hse : HSERunDetSpec N n G w h Φ ε) :
    ∀ v : Fin n,
      (∑ ω : TreeTape N Φ ε (hstDepth Φ),
        treeTapeProb N Φ ε (hstDepth Φ) ω *
          (if v ∉ (hseRun G w N h Φ ε (hstDepth Φ) Finset.univ Finset.univ Φ ω).2
           then (1 : ℝ) else 0)) ≤ ε :=
by
  obtain ⟨hseExclPotential, h_pot_def⟩ :
      ∃ f : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ,
        ∀ N' Φ' ε' m_real Δ,
          f N' Φ' ε' m_real Δ =
            (4 / (hstRadiusSteps N' Φ' ε' : ℝ)) * (1 + 2 * hstTruncDelta N') ^ (Real.logb 2 Δ) *
              (Real.log m_real + Real.log (2 / hstTruncDelta N') * Real.logb 2 Δ) :=
    ⟨fun N' Φ' ε' m_real Δ =>
      (4 / (hstRadiusSteps N' Φ' ε' : ℝ)) * (1 + 2 * hstTruncDelta N') ^ (Real.logb 2 Δ) *
        (Real.log m_real + Real.log (2 / hstTruncDelta N') * Real.logb 2 Δ),
     fun _ _ _ _ _ => rfl⟩
  obtain ⟨hseExclPenalty1, h_pen_nil, h_pen_pos, h_pen_neg⟩ :
      ∃ pen : SimpleGraph (Fin n) → (Sym2 (Fin n) → ℝ) →
          ∀ (N' : ℕ), ℕ → ∀ (Φ' ε' : ℝ), ℝ → ℕ → Fin n →
          Finset (Fin n) → Finset (Fin n) →
          ∀ (phases : List ℕ), (Fin phases.length → Fin (hstRadiusSteps N' Φ' ε')) → ℝ,
        (∀ G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur radii,
          pen G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur [] radii =
            if v ∈ M_cur then hseExclPotential N' Φ' ε' (m_init : ℝ) (Δ / 2) else 1) ∧
        (∀ {G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur ℓ rest}
            (radii : Fin (ℓ :: rest).length → Fin (hstRadiusSteps N' Φ' ε'))
            (hc : (sspCands G' w' N' h' Φ' ε' Δ m_init X_cur ℓ).Nonempty),
          pen G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur (ℓ :: rest) radii =
            let x := (sspCands G' w' N' h' Φ' ε' Δ m_init X_cur ℓ).min' hc
            let R : ℕ := (radii ⟨0, Nat.succ_pos rest.length⟩).1
            let Xj := hstBall G' w' N' h' Φ' ε' Δ X_cur x ℓ (R : ℤ)
            let Mj := hstBall G' w' N' h' Φ' ε' Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur
            let M_next := M_cur \ hstBall G' w' N' h' Φ' ε' Δ X_cur x ℓ ((R : ℤ) + 1)
            if v ∈ Mj then
              hseExclPotential N' Φ' ε' ((m_init : ℝ) / (hstMu N' ℓ : ℝ)) (Δ / 2)
            else if v ∈ M_next then
              pen G' w' N' h' Φ' ε' Δ m_init v (X_cur \ Xj) M_next rest
                (fun i => radii ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
            else
              1) ∧
        (∀ {G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur ℓ rest}
            (radii : Fin (ℓ :: rest).length → Fin (hstRadiusSteps N' Φ' ε'))
            (hc : ¬ (sspCands G' w' N' h' Φ' ε' Δ m_init X_cur ℓ).Nonempty),
          pen G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur (ℓ :: rest) radii =
            pen G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur rest
              (fun i => radii ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) := by
    let penAux : SimpleGraph (Fin n) → (Sym2 (Fin n) → ℝ) →
        ∀ (N' : ℕ), ℕ → ∀ (Φ' ε' : ℝ), ℝ → ℕ → Fin n →
        ∀ (phases : List ℕ), Finset (Fin n) → Finset (Fin n) →
        (Fin phases.length → Fin (hstRadiusSteps N' Φ' ε')) → ℝ :=
      fun G' w' N' h' Φ' ε' Δ m_init v phases =>
        @List.rec ℕ
          (fun ph => Finset (Fin n) → Finset (Fin n) →
            (Fin ph.length → Fin (hstRadiusSteps N' Φ' ε')) → ℝ)
          (fun _ M_cur _ =>
            if v ∈ M_cur then hseExclPotential N' Φ' ε' (m_init : ℝ) (Δ / 2) else 1)
          (fun ℓ rest recFn X_cur M_cur radii =>
            if hc : (sspCands G' w' N' h' Φ' ε' Δ m_init X_cur ℓ).Nonempty then
              let x := (sspCands G' w' N' h' Φ' ε' Δ m_init X_cur ℓ).min' hc
              let R : ℕ := (radii ⟨0, Nat.succ_pos rest.length⟩).1
              let Xj := hstBall G' w' N' h' Φ' ε' Δ X_cur x ℓ (R : ℤ)
              let Mj := hstBall G' w' N' h' Φ' ε' Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur
              let M_next := M_cur \ hstBall G' w' N' h' Φ' ε' Δ X_cur x ℓ ((R : ℤ) + 1)
              if v ∈ Mj then
                hseExclPotential N' Φ' ε' ((m_init : ℝ) / (hstMu N' ℓ : ℝ)) (Δ / 2)
              else if v ∈ M_next then
                recFn (X_cur \ Xj) M_next (fun i => radii ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
              else
                1
            else
              recFn X_cur M_cur (fun i => radii ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))
          phases
    refine ⟨fun G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur phases radii =>
      penAux G' w' N' h' Φ' ε' Δ m_init v phases X_cur M_cur radii, ?_, ?_, ?_⟩
    · intro G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur radii
      rfl
    · intro G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur ℓ rest radii hc
      dsimp only [penAux]
      rw [dif_pos hc]
    · intro G' w' N' h' Φ' ε' Δ m_init v X_cur M_cur ℓ rest radii hc
      dsimp only [penAux]
      rw [dif_neg hc]
  have h_ana :
      (∀ (m_real Δ : ℝ), 1 ≤ m_real → 1 ≤ Δ → 0 ≤ hseExclPotential N Φ ε m_real Δ) ∧
      (∀ (m₁ m₂ Δ : ℝ), 0 < m₁ → m₁ ≤ m₂ →
        hseExclPotential N Φ ε m₁ Δ ≤ hseExclPotential N Φ ε m₂ Δ) ∧
      (∀ (m_real Δ : ℝ), 1 ≤ m_real → 2 ≤ Δ →
        hseExclPotential N Φ ε m_real (Δ / 2) ≤
          hseExclPotential N Φ ε m_real Δ / (1 + 2 * hstTruncDelta N)) ∧
      (∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
        ∀ (m_real Δ : ℝ), 1 ≤ m_real → 2 ≤ Δ → 1 ≤ m_real / (hstMu N ℓ : ℝ) →
        ∀ (ρ : ℤ) (term : ℕ → ℝ),
        (∀ R : ℕ, R < hstRadiusSteps N Φ ε → (R : ℤ) < ρ - 1 →
          term R ≤ hseExclPotential N Φ ε m_real Δ / (1 + 2 * hstTruncDelta N)) →
        (∀ R : ℕ, R < hstRadiusSteps N Φ ε → ρ - 1 ≤ (R : ℤ) → (R : ℤ) ≤ ρ → term R ≤ 1) →
        (∀ R : ℕ, R < hstRadiusSteps N Φ ε → ρ + 1 ≤ (R : ℤ) →
          term R ≤ hseExclPotential N Φ ε (m_real / (hstMu N ℓ : ℝ)) (Δ / 2)) →
        (∑ R ∈ Finset.range (hstRadiusSteps N Φ ε),
          ((1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ) * term R) ≤
          hseExclPotential N Φ ε m_real Δ / (1 + 2 * hstTruncDelta N)) := by
    clear h_pen_neg h_pen_pos h_pen_nil hseExclPenalty1
    clear h_hse h_ssp hε_lt hε_pos hΦ_diam hΦ_ge hh h hw w G hnN hn n
    have hk_one : 1 ≤ hstRadiusSteps N Φ ε := h_params.one_le_k
    have hk_pos : (0 : ℝ) < (hstRadiusSteps N Φ ε : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk_one
    have h4k_pos : (0 : ℝ) < 4 / (hstRadiusSteps N Φ ε : ℝ) := div_pos (by norm_num) hk_pos
    have hδ_pos : 0 < hstTruncDelta N := h_params.delta_pos
    have hδ_half : hstTruncDelta N < 1 / 2 := h_params.delta_lt_half
    have h12δ_pos : 0 < 1 + 2 * hstTruncDelta N := by linarith
    have h2δ_pos : 0 < 2 / hstTruncDelta N := div_pos (by norm_num) hδ_pos
    have h2δ_gt1 : 1 < 2 / hstTruncDelta N := by
      have hmul : hstTruncDelta N * (2 / hstTruncDelta N) = 2 :=
        mul_div_cancel₀ 2 (ne_of_gt hδ_pos)
      nlinarith
    have hlog_2δ_pos : 0 < Real.log (2 / hstTruncDelta N) := Real.log_pos h2δ_gt1
    have h_pot_nonneg : ∀ (m_real Δ : ℝ), 1 ≤ m_real → 1 ≤ Δ →
        0 ≤ hseExclPotential N Φ ε m_real Δ := by
      intro m_real Δ hm hΔ
      rw [h_pot_def]
      have hrpow : 0 < (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) :=
        Real.rpow_pos_of_pos h12δ_pos _
      have hlogm : 0 ≤ Real.log m_real := Real.log_nonneg hm
      have hlogb : 0 ≤ Real.logb 2 Δ := Real.logb_nonneg (by norm_num) hΔ
      exact mul_nonneg (mul_nonneg (le_of_lt h4k_pos) (le_of_lt hrpow))
        (add_nonneg hlogm (mul_nonneg (le_of_lt hlog_2δ_pos) hlogb))
    have h_geom_sum : ∀ (p : ℝ) (m : ℕ),
        (∑ R ∈ Finset.range m, (1 - p) ^ R * p) = 1 - (1 - p) ^ m := by
      intro p m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    refine ⟨h_pot_nonneg, ?_, ?_, ?_⟩
    · intro m₁ m₂ Δ hm₁ hm₁₂
      rw [h_pot_def, h_pot_def]
      have hrpow : 0 < (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) :=
        Real.rpow_pos_of_pos h12δ_pos _
      have hpref : 0 ≤ (4 / (hstRadiusSteps N Φ ε : ℝ)) *
          (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) :=
        mul_nonneg (le_of_lt h4k_pos) (le_of_lt hrpow)
      have hlog : Real.log m₁ ≤ Real.log m₂ := Real.log_le_log hm₁ hm₁₂
      exact mul_le_mul_of_nonneg_left (by linarith) hpref
    · intro m_real Δ hm hΔ
      have hlogb_half : Real.logb 2 (Δ / 2) = Real.logb 2 Δ - 1 := by
        rw [Real.logb_div (by linarith) (by norm_num), Real.logb_self_eq_one (by norm_num)]
      have hrpow_half : (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2)) =
          (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) / (1 + 2 * hstTruncDelta N) := by
        rw [hlogb_half, Real.rpow_sub h12δ_pos, Real.rpow_one]
      have hrpow_pos : 0 < (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) /
          (1 + 2 * hstTruncDelta N) :=
        div_pos (Real.rpow_pos_of_pos h12δ_pos _) h12δ_pos
      rw [h_pot_def, h_pot_def, hrpow_half, hlogb_half]
      have h_inner : Real.log m_real + Real.log (2 / hstTruncDelta N) * (Real.logb 2 Δ - 1) ≤
          Real.log m_real + Real.log (2 / hstTruncDelta N) * Real.logb 2 Δ := by linarith
      calc
        (4 / (hstRadiusSteps N Φ ε : ℝ)) *
            ((1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) / (1 + 2 * hstTruncDelta N)) *
            (Real.log m_real + Real.log (2 / hstTruncDelta N) * (Real.logb 2 Δ - 1))
          ≤ (4 / (hstRadiusSteps N Φ ε : ℝ)) *
              ((1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) / (1 + 2 * hstTruncDelta N)) *
              (Real.log m_real + Real.log (2 / hstTruncDelta N) * Real.logb 2 Δ) :=
            mul_le_mul_of_nonneg_left h_inner
              (mul_nonneg (le_of_lt h4k_pos) (le_of_lt hrpow_pos))
        _ = ((4 / (hstRadiusSteps N Φ ε : ℝ)) * (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) *
              (Real.log m_real + Real.log (2 / hstTruncDelta N) * Real.logb 2 Δ)) /
              (1 + 2 * hstTruncDelta N) := by ring
    · intro ℓ hℓ1 hℓL m_real Δ hm hΔ hm_div ρ term h_lt h_mid h_gt
      set p := hstGeomP N Φ ε ℓ
      set B₁ := hseExclPotential N Φ ε m_real Δ / (1 + 2 * hstTruncDelta N)
      set C := hseExclPotential N Φ ε (m_real / (hstMu N ℓ : ℝ)) (Δ / 2)
      obtain ⟨hp_pos, hp_lt1⟩ := h_params.geomP_bounds ℓ hℓ1 hℓL
      have hw_nonneg : ∀ R : ℕ, 0 ≤ (1 - p) ^ R * p :=
        fun R => mul_nonneg (pow_nonneg (by linarith) R) (le_of_lt hp_pos)
      have hC_nonneg : 0 ≤ C := h_pot_nonneg _ _ hm_div (by linarith)
      have hB₁_nonneg : 0 ≤ B₁ :=
        div_nonneg (h_pot_nonneg _ _ hm (by linarith)) (le_of_lt h12δ_pos)
      have h_abs : 2 * p + C ≤ B₁ := by
        have hμ_ge2 : (2 : ℝ) ≤ (hstMu N ℓ : ℝ) := by
          exact_mod_cast (h_params.mu_sq ℓ hℓ1 hℓL).2
        have hμ_pos : (0 : ℝ) < (hstMu N ℓ : ℝ) := by linarith
        have h2μδ_eq : 2 * (hstMu N ℓ : ℝ) / hstTruncDelta N =
            (2 / hstTruncDelta N) * (hstMu N ℓ : ℝ) := by ring
        have h2μδ_gt1 : 1 < 2 * (hstMu N ℓ : ℝ) / hstTruncDelta N := by
          rw [h2μδ_eq]
          nlinarith
        have hlog_2μδ_pos : 0 < Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N) :=
          Real.log_pos h2μδ_gt1
        have hrpow_ge1 : 1 ≤ (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2)) :=
          Real.one_le_rpow (by linarith) (Real.logb_nonneg (by norm_num) (by linarith))
        have h2p_eq : 2 * p =
            (4 / (hstRadiusSteps N Φ ε : ℝ)) *
              Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N) := by
          simp only [p, hstGeomP]
          ring
        have h2p_le : 2 * p ≤
            (4 / (hstRadiusSteps N Φ ε : ℝ)) *
              (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2)) *
              Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N) := by
          rw [h2p_eq]
          have hfac : 0 ≤ (4 / (hstRadiusSteps N Φ ε : ℝ)) *
              Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N) :=
            mul_nonneg (le_of_lt h4k_pos) (le_of_lt hlog_2μδ_pos)
          nlinarith
        have hlog_split1 : Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N) =
            Real.log (2 / hstTruncDelta N) + Real.log (hstMu N ℓ : ℝ) := by
          rw [h2μδ_eq, Real.log_mul (ne_of_gt h2δ_pos) (ne_of_gt hμ_pos)]
        have hlog_split2 : Real.log (m_real / (hstMu N ℓ : ℝ)) =
            Real.log m_real - Real.log (hstMu N ℓ : ℝ) :=
          Real.log_div (by linarith) (ne_of_gt hμ_pos)
        have hlogb_half : Real.logb 2 (Δ / 2) = Real.logb 2 Δ - 1 := by
          rw [Real.logb_div (by linarith) (by norm_num), Real.logb_self_eq_one (by norm_num)]
        have hrpow_half : (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2)) =
            (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) / (1 + 2 * hstTruncDelta N) := by
          rw [hlogb_half, Real.rpow_sub h12δ_pos, Real.rpow_one]
        have h_rhs_eq :
            (4 / (hstRadiusSteps N Φ ε : ℝ)) *
              (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2)) *
              Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N) + C = B₁ := by
          dsimp only [C, B₁]
          rw [h_pot_def, h_pot_def, hlog_split1, hlog_split2, hrpow_half, hlogb_half]
          ring
        linarith
      set s : ℕ := Int.toNat (max 0 (ρ - 1))
      have hs_eq : (s : ℤ) = max 0 (ρ - 1) := Int.toNat_of_nonneg (le_max_left 0 (ρ - 1))
      by_cases hks : hstRadiusSteps N Φ ε ≤ s
      · have h_sum_le :
            (∑ R ∈ Finset.range (hstRadiusSteps N Φ ε), ((1 - p) ^ R * p) * term R) ≤
            ∑ R ∈ Finset.range (hstRadiusSteps N Φ ε), ((1 - p) ^ R * p) * B₁ := by
          refine Finset.sum_le_sum (fun R hR => ?_)
          have hRk : R < hstRadiusSteps N Φ ε := Finset.mem_range.mp hR
          have hRρ : (R : ℤ) < ρ - 1 := by omega
          exact mul_le_mul_of_nonneg_left (h_lt R hRk hRρ) (hw_nonneg R)
        rw [← Finset.sum_mul, h_geom_sum] at h_sum_le
        have hpk_nonneg : 0 ≤ (1 - p) ^ (hstRadiusSteps N Φ ε) * B₁ :=
          mul_nonneg (pow_nonneg (by linarith) _) hB₁_nonneg
        linarith
      · have hsk : s < hstRadiusSteps N Φ ε := Nat.lt_of_not_ge hks
        rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt hsk)]
        have h_part1 :
            (∑ R ∈ Finset.range s, ((1 - p) ^ R * p) * term R) ≤ (1 - (1 - p) ^ s) * B₁ := by
          calc
            (∑ R ∈ Finset.range s, ((1 - p) ^ R * p) * term R)
              ≤ ∑ R ∈ Finset.range s, ((1 - p) ^ R * p) * B₁ := by
                  refine Finset.sum_le_sum (fun R hR => ?_)
                  have hRs : R < s := Finset.mem_range.mp hR
                  have hRk : R < hstRadiusSteps N Φ ε := Nat.lt_trans hRs hsk
                  have hRρ : (R : ℤ) < ρ - 1 := by omega
                  exact mul_le_mul_of_nonneg_left (h_lt R hRk hRρ) (hw_nonneg R)
            _ = (1 - (1 - p) ^ s) * B₁ := by rw [← Finset.sum_mul, h_geom_sum]
        have h_ico_geom :
            (∑ R ∈ Finset.Ico s (hstRadiusSteps N Φ ε), (1 - p) ^ R * p) =
            (1 - p) ^ s - (1 - p) ^ (hstRadiusSteps N Φ ε) := by
          have h_tot := Finset.sum_range_add_sum_Ico (fun R => (1 - p) ^ R * p) (Nat.le_of_lt hsk)
          rw [h_geom_sum, h_geom_sum] at h_tot
          linarith
        have h_part2 :
            (∑ R ∈ Finset.Ico s (hstRadiusSteps N Φ ε), ((1 - p) ^ R * p) * term R) ≤
            (1 - p) ^ s * (2 * p + C) := by
          have h_pw :
              (∑ R ∈ Finset.Ico s (hstRadiusSteps N Φ ε), ((1 - p) ^ R * p) * term R) ≤
              ∑ R ∈ Finset.Ico s (hstRadiusSteps N Φ ε),
                ((if R = s then (1 - p) ^ R * p else 0) +
                 (if R = s + 1 then (1 - p) ^ R * p else 0) +
                 ((1 - p) ^ R * p) * C) := by
            refine Finset.sum_le_sum (fun R hR => ?_)
            obtain ⟨hsR, hRk⟩ := Finset.mem_Ico.mp hR
            have hρ_le : ρ - 1 ≤ (R : ℤ) := by omega
            have ht_le : term R ≤
                (if R = s then (1 : ℝ) else 0) +
                (if R = s + 1 then (1 : ℝ) else 0) + C := by
              by_cases hRρ : (R : ℤ) ≤ ρ
              · have h_tr := h_mid R hRk hρ_le hRρ
                have h_or : R = s ∨ R = s + 1 := by omega
                rcases h_or with rfl | rfl
                · simp only [↓reduceIte]
                  have hne : s ≠ s + 1 := by omega
                  simp only [if_neg hne]
                  linarith
                · simp only [↓reduceIte]
                  have hne : s + 1 ≠ s := by omega
                  simp only [if_neg hne]
                  linarith
              · have h_tr := h_gt R hRk (by omega)
                have hi1 : (0 : ℝ) ≤ (if R = s then 1 else 0) := by split_ifs <;> norm_num
                have hi2 : (0 : ℝ) ≤ (if R = s + 1 then 1 else 0) := by split_ifs <;> norm_num
                linarith
            calc
              ((1 - p) ^ R * p) * term R
                ≤ ((1 - p) ^ R * p) *
                    ((if R = s then (1 : ℝ) else 0) +
                     (if R = s + 1 then (1 : ℝ) else 0) + C) :=
                  mul_le_mul_of_nonneg_left ht_le (hw_nonneg R)
              _ = (if R = s then (1 - p) ^ R * p else 0) +
                  (if R = s + 1 then (1 - p) ^ R * p else 0) +
                  ((1 - p) ^ R * p) * C := by
                  split_ifs <;> ring
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.sum_mul, h_ico_geom] at h_pw
          have hs1 : (if s ∈ Finset.Ico s (hstRadiusSteps N Φ ε)
              then (1 - p) ^ s * p else 0) ≤ (1 - p) ^ s * p := by
            split_ifs <;> [exact le_rfl; exact hw_nonneg s]
          have hs2 : (if s + 1 ∈ Finset.Ico s (hstRadiusSteps N Φ ε)
              then (1 - p) ^ (s + 1) * p else 0) ≤ (1 - p) ^ s * p := by
            have hw_s1 : (1 - p) ^ (s + 1) * p ≤ (1 - p) ^ s * p := by
              exact mul_le_mul_of_nonneg_right
                (pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.le_succ s))
                (le_of_lt hp_pos)
            split_ifs <;> [exact hw_s1; exact hw_nonneg s]
          have hs3 : ((1 - p) ^ s - (1 - p) ^ (hstRadiusSteps N Φ ε)) * C ≤ (1 - p) ^ s * C := by
            have hpk_nonneg : 0 ≤ (1 - p) ^ (hstRadiusSteps N Φ ε) := pow_nonneg (by linarith) _
            nlinarith
          linarith
        have hps_nonneg : 0 ≤ (1 - p) ^ s := pow_nonneg (by linarith) s
        have h_part2' : (1 - p) ^ s * (2 * p + C) ≤ (1 - p) ^ s * B₁ :=
          mul_le_mul_of_nonneg_left h_abs hps_nonneg
        linarith
  obtain ⟨h_ana_nonneg, h_ana_mono_left, h_ana_half_scale_le, h_ana_slot_step_le⟩ := h_ana
  have h_pen_le : ∀ (X M : Finset (Fin n)) (hX2 : 2 ≤ X.card) (hMX : M ⊆ X)
      (Δ : ℝ) (hΔ_pos : 0 < Δ)
      (hΔ_diam : ∀ u ∈ X, ∀ v' ∈ X,
        hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v' ≤
          ENNReal.ofReal Δ)
      (v : Fin n) (τ : FinTape N Φ ε) (Q : ℝ) (hQ1 : Q ≤ 1)
      (hQ_clus : ∀ t ∈ sspTaggedClusters G w N h Φ ε X M Δ τ, v ∈ t.2.2 →
        Q ≤ (if 1 ≤ t.1 then
               hseExclPotential N Φ ε ((X.card : ℝ) / (hstMu N t.1 : ℝ)) (Δ / 2)
             else
               hseExclPotential N Φ ε (X.card : ℝ) (Δ / 2))),
      Q ≤ hseExclPenalty1 G w N h Φ ε Δ X.card v X M (sspSlotPhases N) τ := by
    clear h_ana_slot_step_le h_ana_half_scale_le h_ana_mono_left h_ana_nonneg h_pot_def
    clear h_hse hε_lt hε_pos hΦ_diam hΦ_ge hh hw hnN hn
    intro X M hX2 hMX Δ hΔ_pos hΔ_diam v τ Q hQ1 hQ_clus
    have h_ball_spec := (h_ssp.scale_spec X M hX2 hMX Δ hΔ_pos hΔ_diam).2.2
    let outOf : ∀ (phases : List ℕ), Finset (Fin n) → Finset (Fin n) →
        (Fin phases.length → Fin (hstRadiusSteps N Φ ε)) →
        List (ℕ × Finset (Fin n) × Finset (Fin n)) :=
      fun phases X_cur M_cur radii =>
        let steps := List.ofFn (fun i : Fin phases.length => (phases.get i, (radii i).1))
        let res := sspRunSteps G w N h Φ ε Δ X.card X_cur M_cur steps
        if res.2.1.Nonempty then res.1 ++ [(0, res.2.1, res.2.2)] else res.1
    have h_ind : ∀ (phases : List ℕ),
        (∀ ℓ ∈ phases, 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N) →
        ∀ (X_cur M_cur : Finset (Fin n)), X_cur ⊆ X → M_cur ⊆ X_cur →
        ∀ (radii : Fin phases.length → Fin (hstRadiusSteps N Φ ε)),
        (∀ t ∈ outOf phases X_cur M_cur radii, v ∈ t.2.2 →
          Q ≤ (if 1 ≤ t.1 then
                 hseExclPotential N Φ ε ((X.card : ℝ) / (hstMu N t.1 : ℝ)) (Δ / 2)
               else
                 hseExclPotential N Φ ε (X.card : ℝ) (Δ / 2))) →
        Q ≤ hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur phases radii := by
      intro phases
      induction phases with
      | nil =>
        intro _ X_cur M_cur _ hM_sub radii h_out
        have h_out_nil : outOf [] X_cur M_cur radii =
            (if X_cur.Nonempty then [(0, X_cur, M_cur)] else []) := by
          simp [outOf, sspRunSteps]
        rw [h_out_nil] at h_out
        rw [h_pen_nil]
        by_cases hv : v ∈ M_cur
        · rw [if_pos hv]
          have hne : X_cur.Nonempty := ⟨v, hM_sub hv⟩
          rw [if_pos hne] at h_out
          have h0 := h_out (0, X_cur, M_cur) (by simp) hv
          simpa using h0
        · rw [if_neg hv]
          exact hQ1
      | cons ℓ rest ih =>
        intro h_ph X_cur M_cur hX_sub hM_sub radii h_out
        obtain ⟨hℓ1, hℓL⟩ := h_ph ℓ List.mem_cons_self
        have h_rest : ∀ ℓ' ∈ rest, 1 ≤ ℓ' ∧ ℓ' ≤ hstPhaseCount N :=
          fun ℓ' hmem => h_ph ℓ' (List.mem_cons_of_mem ℓ hmem)
        let R : ℕ := (radii ⟨0, Nat.succ_pos rest.length⟩).1
        let radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε) :=
          fun i => radii ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
        have h_steps_cons :
            List.ofFn (fun i : Fin (ℓ :: rest).length => ((ℓ :: rest).get i, (radii i).1)) =
              (ℓ, R) :: List.ofFn (fun i : Fin rest.length => (rest.get i, (radii' i).1)) := by
          change List.ofFn (fun i : Fin (rest.length + 1) => ((ℓ :: rest).get i, (radii i).1)) =
            (ℓ, R) :: List.ofFn (fun i : Fin rest.length => (rest.get i, (radii' i).1))
          rw [List.ofFn_succ]
          rfl
        by_cases hc : (sspCands G w N h Φ ε Δ X.card X_cur ℓ).Nonempty
        · let x := (sspCands G w N h Φ ε Δ X.card X_cur ℓ).min' hc
          let Xj := hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ)
          let Mj := hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur
          let M_next := M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1)
          have h_out_cons : outOf (ℓ :: rest) X_cur M_cur radii =
              (ℓ, Xj, Mj) :: outOf rest (X_cur \ Xj) M_next radii' := by
            dsimp only [outOf]
            rw [h_steps_cons, sspRunSteps, dif_pos hc]
            dsimp only
            split_ifs <;> rfl
          rw [h_out_cons] at h_out
          rw [h_pen_pos radii hc]
          change Q ≤
            if v ∈ Mj then
              hseExclPotential N Φ ε ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2)
            else if v ∈ M_next then
              hseExclPenalty1 G w N h Φ ε Δ X.card v (X_cur \ Xj) M_next rest radii'
            else 1
          by_cases hvj : v ∈ Mj
          · rw [if_pos hvj]
            have h_app := h_out (ℓ, Xj, Mj) List.mem_cons_self hvj
            simpa only [if_pos hℓ1] using h_app
          · rw [if_neg hvj]
            by_cases hvn : v ∈ M_next
            · rw [if_pos hvn]
              have hx_cands : x ∈ sspCands G w N h Φ ε Δ X.card X_cur ℓ :=
                Finset.min'_mem _ hc
              have hx_mem : x ∈ X_cur := by
                letI := Classical.propDecidable
                unfold sspCands at hx_cands
                rw [Finset.mem_filter] at hx_cands
                exact hx_cands.1
              have h_mono := (h_ball_spec X_cur hX_sub x hx_mem ℓ hℓ1 hℓL).2.1
                (R : ℤ) ((R : ℤ) + 1) (by omega)
              have hX'_sub : X_cur \ Xj ⊆ X := Finset.Subset.trans Finset.sdiff_subset hX_sub
              have hM'_sub : M_next ⊆ X_cur \ Xj := by
                intro u hu
                obtain ⟨huM, huB⟩ := Finset.mem_sdiff.mp hu
                exact Finset.mem_sdiff.mpr ⟨hM_sub huM, fun huXj => huB (h_mono huXj)⟩
              refine ih h_rest (X_cur \ Xj) M_next hX'_sub hM'_sub radii' ?_
              intro t ht hv_t
              exact h_out t (List.mem_cons_of_mem _ ht) hv_t
            · rw [if_neg hvn]
              exact hQ1
        · have h_out_cons : outOf (ℓ :: rest) X_cur M_cur radii =
              outOf rest X_cur M_cur radii' := by
            dsimp only [outOf]
            rw [h_steps_cons, sspRunSteps, dif_neg hc]
          rw [h_out_cons] at h_out
          rw [h_pen_neg radii hc]
          exact ih h_rest X_cur M_cur hX_sub hM_sub radii' h_out
    exact h_ind (sspSlotPhases N) h_params.slot_phases_bounds X M (Finset.Subset.refl X) hMX τ
      hQ_clus
  have h_pen_exp : ∀ (X M : Finset (Fin n)) (hX2 : 2 ≤ X.card) (hMX : M ⊆ X)
      (Δ : ℝ) (hΔ_pos : 0 < Δ)
      (hΔ_diam : ∀ u ∈ X, ∀ v' ∈ X,
        hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v' ≤
          ENNReal.ofReal Δ)
      (v : Fin n) (hvM : v ∈ M),
      (∑ τ : FinTape N Φ ε,
        finTapeProb N Φ ε τ *
          hseExclPenalty1 G w N h Φ ε Δ X.card v X M (sspSlotPhases N) τ) ≤
        hseExclPotential N Φ ε (X.card : ℝ) Δ := by
    clear h_pen_le h_ana_mono_left h_pot_def
    clear h_hse hε_lt hε_pos hΦ_diam hΦ_ge hh hw hnN hn
    intro X M hX2 hMX Δ hΔ_pos hΔ_diam v hvM
    have hδ_pos : 0 < hstTruncDelta N := h_params.delta_pos
    have hδ_half : hstTruncDelta N < 1 / 2 := h_params.delta_lt_half
    have h12δ_pos : 0 < 1 + 2 * hstTruncDelta N := by linarith
    have h_geom_sum : ∀ (p : ℝ) (m : ℕ),
        (∑ R ∈ Finset.range m, (1 - p) ^ R * p) = 1 - (1 - p) ^ m := by
      intro p m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have h_sc := h_ssp.scale_spec X M hX2 hMX Δ hΔ_pos hΔ_diam
    have hΔ2 : 2 ≤ Δ := h_sc.1
    have h_ball_spec := h_sc.2.2
    have hm1 : (1 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast (by omega : 1 ≤ X.card)
    set B₁ := hseExclPotential N Φ ε (X.card : ℝ) Δ / (1 + 2 * hstTruncDelta N)
    have hB₁_nonneg : 0 ≤ B₁ := div_nonneg (h_ana_nonneg _ _ hm1 (by linarith)) (le_of_lt h12δ_pos)
    let unnormW : ℕ → ℕ → ℝ :=
      fun ℓ R => (1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ
    let unnormProb : ∀ (phases : List ℕ),
        (Fin phases.length → Fin (hstRadiusSteps N Φ ε)) → ℝ :=
      fun phases radii => ∏ i : Fin phases.length, unnormW (phases.get i) (radii i).1
    have h_unnorm_sum_le_one : ∀ (phases : List ℕ),
        (∀ ℓ ∈ phases, 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N) →
        (∑ radii : Fin phases.length → Fin (hstRadiusSteps N Φ ε), unnormProb phases radii) ≤ 1 := by
      intro phases h_ph
      have h_fact :
          (∑ radii : Fin phases.length → Fin (hstRadiusSteps N Φ ε), unnormProb phases radii) =
          ∏ i : Fin phases.length,
            (∑ r : Fin (hstRadiusSteps N Φ ε), unnormW (phases.get i) r.1) :=
        (Fintype.prod_sum (fun (i : Fin phases.length) (r : Fin (hstRadiusSteps N Φ ε)) =>
          unnormW (phases.get i) r.1)).symm
      rw [h_fact]
      refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
      · obtain ⟨hℓ1, hℓL⟩ := h_ph (phases.get i) (List.get_mem phases i)
        obtain ⟨hp_pos, hp_lt1⟩ := h_params.geomP_bounds (phases.get i) hℓ1 hℓL
        refine Finset.sum_nonneg (fun r _ => ?_)
        exact mul_nonneg (pow_nonneg (by linarith) _) (le_of_lt hp_pos)
      · obtain ⟨hℓ1, hℓL⟩ := h_ph (phases.get i) (List.get_mem phases i)
        obtain ⟨hp_pos, hp_lt1⟩ := h_params.geomP_bounds (phases.get i) hℓ1 hℓL
        rw [Fin.sum_univ_eq_sum_range (fun R => unnormW (phases.get i) R) (hstRadiusSteps N Φ ε)]
        simp only [unnormW]
        rw [h_geom_sum]
        have hpow_nonneg : 0 ≤ (1 - hstGeomP N Φ ε (phases.get i)) ^ (hstRadiusSteps N Φ ε) :=
          pow_nonneg (by linarith) _
        linarith
    have h_s1 : ∀ (phases : List ℕ),
        (∀ ℓ ∈ phases, 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N) →
        ∀ (X_cur M_cur : Finset (Fin n)), X_cur ⊆ X → M_cur ⊆ X_cur → v ∈ M_cur →
        (∑ radii : Fin phases.length → Fin (hstRadiusSteps N Φ ε),
          unnormProb phases radii *
            hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur phases radii) ≤ B₁ := by
      intro phases
      induction phases with
      | nil =>
        intro _ X_cur M_cur _ _ hv_cur
        let r_nil : Fin ([] : List ℕ).length → Fin (hstRadiusSteps N Φ ε) := fun i => Fin.elim0 i
        have h_univ :
            (Finset.univ : Finset (Fin ([] : List ℕ).length → Fin (hstRadiusSteps N Φ ε))) =
            {r_nil} := by
          ext g
          simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
          funext i
          exact Fin.elim0 i
        rw [h_univ, Finset.sum_singleton]
        have hp0 : unnormProb [] r_nil = 1 := by simp [unnormProb]
        rw [hp0, one_mul]
        rw [h_pen_nil, if_pos hv_cur]
        exact h_ana_half_scale_le (X.card : ℝ) Δ hm1 hΔ2
      | cons ℓ rest ih =>
        intro h_ph X_cur M_cur hX_sub hM_sub hv_cur
        obtain ⟨hℓ1, hℓL⟩ := h_ph ℓ List.mem_cons_self
        have h_rest : ∀ ℓ' ∈ rest, 1 ≤ ℓ' ∧ ℓ' ≤ hstPhaseCount N :=
          fun ℓ' hmem => h_ph ℓ' (List.mem_cons_of_mem ℓ hmem)
        let e : Fin (hstRadiusSteps N Φ ε) × (Fin rest.length → Fin (hstRadiusSteps N Φ ε)) ≃
            (Fin (rest.length + 1) → Fin (hstRadiusSteps N Φ ε)) :=
          Fin.consEquiv (fun _ : Fin (rest.length + 1) => Fin (hstRadiusSteps N Φ ε))
        have h_reidx :
            (∑ radii : Fin (ℓ :: rest).length → Fin (hstRadiusSteps N Φ ε),
              unnormProb (ℓ :: rest) radii *
                hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur (ℓ :: rest) radii) =
            ∑ p : Fin (hstRadiusSteps N Φ ε) × (Fin rest.length → Fin (hstRadiusSteps N Φ ε)),
              unnormProb (ℓ :: rest) (e p) *
                hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur (ℓ :: rest) (e p) := by
          change (∑ radii : Fin (rest.length + 1) → Fin (hstRadiusSteps N Φ ε),
              unnormProb (ℓ :: rest) radii *
                hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur (ℓ :: rest) radii) = _
          refine Fintype.sum_equiv e.symm _ _ (fun radii => ?_)
          simp
        rw [h_reidx, Fintype.sum_prod_type]
        have h_e_zero : ∀ (r₀ : Fin (hstRadiusSteps N Φ ε))
            (radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε)),
            (e (r₀, radii') ⟨0, Nat.succ_pos rest.length⟩).1 = r₀.1 := by
          intro r₀ radii'
          have hz : (⟨0, Nat.succ_pos rest.length⟩ : Fin (rest.length + 1)) = 0 := rfl
          rw [hz]
          exact congrArg Fin.val (Fin.cons_zero (α := fun _ => Fin (hstRadiusSteps N Φ ε)) r₀ radii')
        have h_e_succ : ∀ (r₀ : Fin (hstRadiusSteps N Φ ε))
            (radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε)),
            (fun i : Fin rest.length => e (r₀, radii') ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) = radii' := by
          intro r₀ radii'
          funext i
          have hs : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (rest.length + 1)) = i.succ := rfl
          rw [hs]
          exact Fin.cons_succ (α := fun _ => Fin (hstRadiusSteps N Φ ε)) r₀ radii' i
        have h_prob_cons : ∀ (r₀ : Fin (hstRadiusSteps N Φ ε))
            (radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε)),
            unnormProb (ℓ :: rest) (e (r₀, radii')) =
              unnormW ℓ r₀.1 * unnormProb rest radii' := by
          intro r₀ radii'
          change (∏ i : Fin (rest.length + 1),
              unnormW ((ℓ :: rest).get i) ((e (r₀, radii') i).1)) =
            unnormW ℓ r₀.1 * unnormProb rest radii'
          rw [Fin.prod_univ_succ]
          have h0 : unnormW ((ℓ :: rest).get (0 : Fin (rest.length + 1)))
              ((e (r₀, radii') (0 : Fin (rest.length + 1))).1) = unnormW ℓ r₀.1 := by
            have hg0 : (ℓ :: rest).get (0 : Fin (rest.length + 1)) = ℓ := rfl
            rw [hg0]
            exact congrArg (unnormW ℓ) (h_e_zero r₀ radii')
          have htl : (∏ i : Fin rest.length,
              unnormW ((ℓ :: rest).get i.succ) ((e (r₀, radii') i.succ).1)) =
              unnormProb rest radii' := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            have hgs : (ℓ :: rest).get i.succ = rest.get i := rfl
            have hes : e (r₀, radii') i.succ = radii' i :=
              Fin.cons_succ (α := fun _ => Fin (hstRadiusSteps N Φ ε)) r₀ radii' i
            rw [hgs, hes]
          rw [h0, htl]
        by_cases hc : (sspCands G w N h Φ ε Δ X.card X_cur ℓ).Nonempty
        · let x := (sspCands G w N h Φ ε Δ X.card X_cur ℓ).min' hc
          have hx_cands : x ∈ sspCands G w N h Φ ε Δ X.card X_cur ℓ :=
            Finset.min'_mem _ hc
          have hx_pair : x ∈ X_cur ∧
              ((hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) ≤
                (X.card : ℝ) / (hstMu N ℓ : ℝ) := by
            letI := Classical.propDecidable
            unfold sspCands at hx_cands
            rw [Finset.mem_filter] at hx_cands
            exact ⟨hx_cands.1, hx_cands.2.2⟩
          have hx_cur : x ∈ X_cur := hx_pair.1
          have hx_upper := hx_pair.2
          have h_bs := h_ball_spec X_cur hX_sub x hx_cur ℓ hℓ1 hℓL
          have hx_in_k : x ∈ hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ) :=
            h_bs.2.1 0 (hstRadiusSteps N Φ ε : ℤ) (by omega) h_bs.1
          have h_card_k_pos :
              1 ≤ (hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card :=
            Finset.card_pos.mpr ⟨x, hx_in_k⟩
          have hm_div : 1 ≤ (X.card : ℝ) / (hstMu N ℓ : ℝ) := by
            refine le_trans ?_ hx_upper
            exact_mod_cast h_card_k_pos
          obtain ⟨ρ_map, hρ_iff, _⟩ := h_bs.2.2
          set ρ : ℤ := ρ_map v
          have hv_in_X : v ∈ X_cur := hM_sub hv_cur
          let term : ℕ → ℝ := fun R =>
            let Xj := hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ)
            let Mj := hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur
            let M_next := M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1)
            ∑ radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε),
              unnormProb rest radii' *
                (if v ∈ Mj then
                   hseExclPotential N Φ ε ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2)
                 else if v ∈ M_next then
                   hseExclPenalty1 G w N h Φ ε Δ X.card v (X_cur \ Xj) M_next rest radii'
                 else 1)
          have h_eq_range :
              (∑ r₀ : Fin (hstRadiusSteps N Φ ε),
                ∑ radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε),
                  unnormProb (ℓ :: rest) (e (r₀, radii')) *
                    hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur (ℓ :: rest)
                      (e (r₀, radii'))) =
              ∑ R ∈ Finset.range (hstRadiusSteps N Φ ε), unnormW ℓ R * term R := by
            rw [← Fin.sum_univ_eq_sum_range (fun R => unnormW ℓ R * term R) (hstRadiusSteps N Φ ε)]
            refine Finset.sum_congr rfl (fun r₀ _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun radii' _ => ?_)
            rw [h_prob_cons r₀ radii', mul_assoc]
            congr 1
            rw [h_pen_pos (e (r₀, radii')) hc]
            dsimp only
            rw [h_e_zero r₀ radii', h_e_succ r₀ radii']
          rw [h_eq_range]
          refine h_ana_slot_step_le ℓ hℓ1 hℓL (X.card : ℝ) Δ hm1 hΔ2 hm_div ρ term ?_ ?_ ?_
          · intro R _ hR_lt
            have hv_not_Mj : v ∉ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur := by
              intro hmem
              have hle := (hρ_iff v hv_in_X ((R : ℤ) - 1)).mp (Finset.mem_inter.mp hmem).1
              omega
            have hv_in_Mn : v ∈ M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) := by
              refine Finset.mem_sdiff.mpr ⟨hv_cur, fun hmem => ?_⟩
              have hle := (hρ_iff v hv_in_X ((R : ℤ) + 1)).mp hmem
              omega
            dsimp only [term]
            simp only [if_neg hv_not_Mj, if_pos hv_in_Mn]
            have h_mono := h_bs.2.1 (R : ℤ) ((R : ℤ) + 1) (by omega)
            have hX'_sub : X_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ) ⊆ X :=
              Finset.Subset.trans Finset.sdiff_subset hX_sub
            have hM'_sub : M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) ⊆
                X_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ) := by
              intro u hu
              obtain ⟨huM, huB⟩ := Finset.mem_sdiff.mp hu
              exact Finset.mem_sdiff.mpr ⟨hM_sub huM, fun huXj => huB (h_mono huXj)⟩
            exact ih h_rest _ _ hX'_sub hM'_sub hv_in_Mn
          · intro R _ hR_ge hR_le
            have hv_not_Mj : v ∉ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur := by
              intro hmem
              have hle := (hρ_iff v hv_in_X ((R : ℤ) - 1)).mp (Finset.mem_inter.mp hmem).1
              omega
            have hv_not_Mn : v ∉ M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) := by
              intro hmem
              have h_in : v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) :=
                (hρ_iff v hv_in_X ((R : ℤ) + 1)).mpr (by omega)
              exact (Finset.mem_sdiff.mp hmem).2 h_in
            dsimp only [term]
            simp only [if_neg hv_not_Mj, if_neg hv_not_Mn, mul_one]
            exact h_unnorm_sum_le_one rest h_rest
          · intro R _ hR_ge
            have hv_in_Mj : v ∈ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur := by
              refine Finset.mem_inter.mpr ⟨?_, hv_cur⟩
              exact (hρ_iff v hv_in_X ((R : ℤ) - 1)).mpr (by omega)
            dsimp only [term]
            simp only [if_pos hv_in_Mj, ← Finset.sum_mul]
            have hC_nonneg : 0 ≤ hseExclPotential N Φ ε
                ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2) :=
              h_ana_nonneg _ _ hm_div (by linarith)
            calc
              (∑ radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε), unnormProb rest radii') *
                  hseExclPotential N Φ ε ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2)
                ≤ 1 * hseExclPotential N Φ ε ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2) :=
                  mul_le_mul_of_nonneg_right (h_unnorm_sum_le_one rest h_rest) hC_nonneg
              _ = hseExclPotential N Φ ε ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2) := one_mul _
        · have h_outer :
              (∑ r₀ : Fin (hstRadiusSteps N Φ ε),
                ∑ radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε),
                  unnormProb (ℓ :: rest) (e (r₀, radii')) *
                    hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur (ℓ :: rest)
                      (e (r₀, radii'))) =
              (∑ r₀ : Fin (hstRadiusSteps N Φ ε), unnormW ℓ r₀.1) *
                (∑ radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε),
                  unnormProb rest radii' *
                    hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur rest radii') := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun r₀ _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun radii' _ => ?_)
            rw [h_prob_cons r₀ radii', mul_assoc]
            congr 1
            rw [h_pen_neg (e (r₀, radii')) hc, h_e_succ r₀ radii']
          rw [h_outer, Fin.sum_univ_eq_sum_range (fun R => unnormW ℓ R) (hstRadiusSteps N Φ ε)]
          simp only [unnormW]
          rw [h_geom_sum]
          obtain ⟨hp_pos, hp_lt1⟩ := h_params.geomP_bounds ℓ hℓ1 hℓL
          have h1p_nonneg : 0 ≤ 1 - (1 - hstGeomP N Φ ε ℓ) ^ (hstRadiusSteps N Φ ε) := by
            have hpow_le : (1 - hstGeomP N Φ ε ℓ) ^ (hstRadiusSteps N Φ ε) ≤
                (1 - hstGeomP N Φ ε ℓ) ^ 0 :=
              pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.zero_le _)
            linarith [pow_zero (1 - hstGeomP N Φ ε ℓ)]
          have h_ih := ih h_rest X_cur M_cur hX_sub hM_sub hv_cur
          calc
            (1 - (1 - hstGeomP N Φ ε ℓ) ^ (hstRadiusSteps N Φ ε)) *
                (∑ radii' : Fin rest.length → Fin (hstRadiusSteps N Φ ε),
                  unnormProb rest radii' *
                    hseExclPenalty1 G w N h Φ ε Δ X.card v X_cur M_cur rest radii')
              ≤ (1 - (1 - hstGeomP N Φ ε ℓ) ^ (hstRadiusSteps N Φ ε)) * B₁ :=
                mul_le_mul_of_nonneg_left h_ih h1p_nonneg
            _ ≤ B₁ := by
                have hpow_nonneg : 0 ≤ (1 - hstGeomP N Φ ε ℓ) ^ (hstRadiusSteps N Φ ε) * B₁ :=
                  mul_nonneg (pow_nonneg (by linarith) _) hB₁_nonneg
                linarith
    have h_s1_root := h_s1 (sspSlotPhases N) h_params.slot_phases_bounds X M
      (Finset.Subset.refl X) hMX hvM
    set Z_tot : ℝ := ∏ i : Fin (hstTotalSlots N),
      (1 - (1 - hstGeomP N Φ ε ((sspSlotPhases N).get i)) ^ hstRadiusSteps N Φ ε)
    have hZ_ge : 1 - hstTruncDelta N ≤ Z_tot := h_params.trunc_norm_prod_ge
    have h1δ_pos : 0 < 1 - hstTruncDelta N := by linarith
    have hZ_pos : 0 < Z_tot := lt_of_lt_of_le h1δ_pos hZ_ge
    have hZ_inv_nonneg : 0 ≤ Z_tot⁻¹ := inv_nonneg.mpr (le_of_lt hZ_pos)
    have hZ_inv_le : Z_tot⁻¹ ≤ 1 + 2 * hstTruncDelta N :=
      le_trans (inv_anti₀ h1δ_pos hZ_ge) h_params.inv_one_sub_delta
    have h_ft_eq : ∀ τ : FinTape N Φ ε,
        finTapeProb N Φ ε τ = unnormProb (sspSlotPhases N) τ / Z_tot := by
      intro τ
      simp only [finTapeProb, truncGeomWeight, unnormProb, unnormW, Z_tot]
      exact Finset.prod_div_distrib _ _
    have h_lhs_eq :
        (∑ τ : FinTape N Φ ε,
          finTapeProb N Φ ε τ *
            hseExclPenalty1 G w N h Φ ε Δ X.card v X M (sspSlotPhases N) τ) =
        (∑ τ : FinTape N Φ ε,
          unnormProb (sspSlotPhases N) τ *
            hseExclPenalty1 G w N h Φ ε Δ X.card v X M (sspSlotPhases N) τ) * Z_tot⁻¹ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      rw [h_ft_eq τ]
      ring
    rw [h_lhs_eq]
    calc
      (∑ τ : FinTape N Φ ε,
          unnormProb (sspSlotPhases N) τ *
            hseExclPenalty1 G w N h Φ ε Δ X.card v X M (sspSlotPhases N) τ) * Z_tot⁻¹
        ≤ B₁ * Z_tot⁻¹ := mul_le_mul_of_nonneg_right h_s1_root hZ_inv_nonneg
      _ ≤ B₁ * (1 + 2 * hstTruncDelta N) := mul_le_mul_of_nonneg_left hZ_inv_le hB₁_nonneg
      _ = hseExclPotential N Φ ε (X.card : ℝ) Δ :=
          div_mul_cancel₀ _ (ne_of_gt h12δ_pos)
  have h_sub_cond : ∀ (d : ℕ) (X M : Finset (Fin n)) (hX2 : 2 ≤ X.card) (hMX : M ⊆ X)
      (Δ : ℝ) (hΔ_pos : 0 < Δ)
      (hΔ_diam : ∀ u ∈ X, ∀ v' ∈ X,
        hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v' ≤
          ENNReal.ofReal Δ)
      (hΔ_lt : Δ < 8 * (2 : ℝ) ^ d)
      (v : Fin n) (τ : FinTape N Φ ε),
      let Q := ∑ sub : Fin N → TreeTape N Φ ε d,
        (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) *
          (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 then (1 : ℝ) else 0)
      Q ≤ 1 ∧
      (∀ t ∈ sspTaggedClusters G w N h Φ ε X M Δ τ, v ∈ t.2.2 →
        Q = ∑ ω' : TreeTape N Φ ε d,
          treeTapeProb N Φ ε d ω' *
            (if v ∉ (hseRun G w N h Φ ε d t.2.1 t.2.2 (Δ / 2) ω').2 then (1 : ℝ) else 0)) := by
    clear h_pen_exp h_pen_le h_ana_slot_step_le h_ana_half_scale_le h_ana_mono_left h_ana_nonneg
    clear h_pen_neg h_pen_pos h_pen_nil hseExclPenalty1 h_pot_def hseExclPotential
    clear hε_lt hε_pos hΦ_diam hΦ_ge hh hw hnN hn
    intro d X M hX2 hMX Δ hΔ_pos hΔ_diam hΔ_lt v τ
    dsimp only
    constructor
    · calc
        (∑ sub : Fin N → TreeTape N Φ ε d,
            (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) *
              (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 then (1 : ℝ) else 0))
          ≤ ∑ sub : Fin N → TreeTape N Φ ε d,
              (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) := by
              refine Finset.sum_le_sum (fun sub _ => ?_)
              have hp_nn : 0 ≤ ∏ q : Fin N, treeTapeProb N Φ ε d (sub q) :=
                Finset.prod_nonneg (fun q _ => h_params.prob_nonneg d (sub q))
              have hi_le : (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2
                  then (1 : ℝ) else 0) ≤ 1 := by
                split_ifs <;> norm_num
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hi_le hp_nn
        _ = ∏ _q : Fin N, (∑ ω' : TreeTape N Φ ε d, treeTapeProb N Φ ε d ω') :=
              (Fintype.prod_sum (fun (_ : Fin N) (ω' : TreeTape N Φ ε d) =>
                treeTapeProb N Φ ε d ω')).symm
        _ = 1 := by simp only [h_params.prob_sum d, Finset.prod_const_one]
    · intro t ht hvt
      have h_biUnion_mem : ∀ (clus : List (Finset (Fin n) × Finset (Fin n)))
          (h_len : clus.length ≤ N)
          (h_pw : (clus.map Prod.fst).Pairwise Disjoint)
          (h_sub1 : ∀ c ∈ clus, c.2 ⊆ c.1)
          (h_run_sub : ∀ c ∈ clus, ∀ ω' : TreeTape N Φ ε d,
            (hseRun G w N h Φ ε d c.1 c.2 (Δ / 2) ω').2 ⊆ c.2)
          (idx₀ : Fin clus.length) (hq₀ : idx₀.1 < N)
          (hv_c₀ : v ∈ (clus.get idx₀).1)
          (sub : Fin N → TreeTape N Φ ε d),
          (v ∈ Finset.univ.biUnion (fun idx : Fin clus.length =>
            (if hq : idx.1 < N then
               hseRun G w N h Φ ε d (clus.get idx).1 (clus.get idx).2 (Δ / 2) (sub ⟨idx.1, hq⟩)
             else
               (RawHST.leaf (clus.get idx).1, (clus.get idx).2)).2)) ↔
          (v ∈ (hseRun G w N h Φ ε d (clus.get idx₀).1 (clus.get idx₀).2 (Δ / 2)
            (sub ⟨idx₀.1, hq₀⟩)).2) := by
        intro clus h_len h_pw h_sub1 h_run_sub idx₀ hq₀ hv_c₀ sub
        rw [Finset.mem_biUnion]
        constructor
        · rintro ⟨idx, _, hmem⟩
          have hq : idx.1 < N := Nat.lt_of_lt_of_le idx.2 h_len
          rw [dif_pos hq] at hmem
          by_cases h_eq : idx = idx₀
          · subst h_eq
            exact hmem
          · exfalso
            have hc_mem : clus.get idx ∈ clus := List.get_mem clus idx
            have hv_c2 : v ∈ (clus.get idx).2 :=
              h_run_sub (clus.get idx) hc_mem (sub ⟨idx.1, hq⟩) hmem
            have hv_c1 : v ∈ (clus.get idx).1 := h_sub1 (clus.get idx) hc_mem hv_c2
            have h_pw_fst : clus.Pairwise (fun a b => Disjoint a.1 b.1) :=
              List.pairwise_map.mp h_pw
            have h_disj : Disjoint (clus.get idx₀).1 (clus.get idx).1 := by
              rcases lt_or_gt_of_ne h_eq with hlt | hgt
              · exact (List.pairwise_iff_get.mp h_pw_fst idx idx₀ hlt).symm
              · exact List.pairwise_iff_get.mp h_pw_fst idx₀ idx hgt
            exact Finset.disjoint_left.mp h_disj hv_c₀ hv_c1
        · intro hmem
          refine ⟨idx₀, Finset.mem_univ idx₀, ?_⟩
          rw [dif_pos hq₀]
          exact hmem
      have h_sc_τ := (h_ssp.scale_spec X M hX2 hMX Δ hΔ_pos hΔ_diam).2.1 τ
      have h_len_le : (sspClusters G w N h Φ ε X M Δ τ).length ≤ N := by
        rw [sspClusters, List.length_map]
        exact h_sc_τ.2.1
      have h_pw_clus : ((sspClusters G w N h Φ ε X M Δ τ).map Prod.fst).Pairwise Disjoint := by
        rw [sspClusters, List.map_map]
        exact h_sc_τ.2.2.1
      have h_sub1_clus : ∀ c ∈ sspClusters G w N h Φ ε X M Δ τ, c.2 ⊆ c.1 := by
        intro c hc
        rw [sspClusters, List.mem_map] at hc
        obtain ⟨s, hs_mem, rfl⟩ := hc
        exact Finset.Subset.trans (h_sc_τ.2.2.2.2 s hs_mem).2.2.1 Finset.inter_subset_right
      have h_run_sub_clus : ∀ c ∈ sspClusters G w N h Φ ε X M Δ τ, ∀ ω' : TreeTape N Φ ε d,
          (hseRun G w N h Φ ε d c.1 c.2 (Δ / 2) ω').2 ⊆ c.2 := by
        intro c hc ω'
        rw [sspClusters, List.mem_map] at hc
        obtain ⟨s, hs_mem, rfl⟩ := hc
        have hs_props := h_sc_τ.2.2.2.2 s hs_mem
        have hs_M_sub : s.2.2 ⊆ s.2.1 :=
          Finset.Subset.trans hs_props.2.2.1 Finset.inter_subset_right
        have hs_term : 2 ≤ s.2.1.card → 1 ≤ d ∧ Δ / 2 < 8 * (2 : ℝ) ^ (d - 1) := by
          intro hs2
          by_cases hd0 : d = 0
          · subst hd0
            have hΔ8 : Δ < 8 := by simpa using hΔ_lt
            have hcard1 := hs_props.2.2.2.2.2.2 hΔ8
            omega
          · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
            refine ⟨hd1, ?_⟩
            have hpow : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
              conv_lhs => rw [← Nat.sub_add_cancel hd1, pow_succ]
            linarith
        exact (h_hse.run_spec d s.2.1 s.2.2 hs_props.1 hs_M_sub (Δ / 2)
          (by linarith) hs_props.2.2.2.1 hs_term ω').2.2.2.1
      have ht_in_clus : (t.2.1, t.2.2) ∈ sspClusters G w N h Φ ε X M Δ τ := by
        rw [sspClusters, List.mem_map]
        exact ⟨t, ht, rfl⟩
      obtain ⟨idx₀, h_get₀⟩ := List.mem_iff_get.mp ht_in_clus
      have hq₀ : idx₀.1 < N := Nat.lt_of_lt_of_le idx₀.2 h_len_le
      let q₀ : Fin N := ⟨idx₀.1, hq₀⟩
      have ht_props := h_sc_τ.2.2.2.2 t ht
      have hv_in_t1 : v ∈ t.2.1 := (Finset.mem_inter.mp (ht_props.2.2.1 hvt)).2
      have hv_c₀ : v ∈ ((sspClusters G w N h Φ ε X M Δ τ).get idx₀).1 := by
        rw [h_get₀]
        exact hv_in_t1
      have hX_not1 : ¬ X.card ≤ 1 := by omega
      have h_ind_eq : ∀ sub : Fin N → TreeTape N Φ ε d,
          (v ∈ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2) ↔
            (v ∈ (hseRun G w N h Φ ε d t.2.1 t.2.2 (Δ / 2) (sub q₀)).2) := by
        intro sub
        have h_unfold : (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 =
            Finset.univ.biUnion (fun idx : Fin (sspClusters G w N h Φ ε X M Δ τ).length =>
              (if hq : idx.1 < N then
                 hseRun G w N h Φ ε d ((sspClusters G w N h Φ ε X M Δ τ).get idx).1
                   ((sspClusters G w N h Φ ε X M Δ τ).get idx).2 (Δ / 2) (sub ⟨idx.1, hq⟩)
               else
                 (RawHST.leaf ((sspClusters G w N h Φ ε X M Δ τ).get idx).1,
                  ((sspClusters G w N h Φ ε X M Δ τ).get idx).2)).2) := by
          rw [hseRun.eq_2, if_neg hX_not1]
        rw [h_unfold]
        have h_iff := h_biUnion_mem (sspClusters G w N h Φ ε X M Δ τ)
          h_len_le h_pw_clus h_sub1_clus h_run_sub_clus idx₀ hq₀ hv_c₀ sub
        rw [h_get₀] at h_iff
        exact h_iff
      let φ : TreeTape N Φ ε d → ℝ :=
        fun ω' => if v ∉ (hseRun G w N h Φ ε d t.2.1 t.2.2 (Δ / 2) ω').2 then 1 else 0
      let g : Fin N → TreeTape N Φ ε d → ℝ :=
        fun q ω' => if q = q₀ then treeTapeProb N Φ ε d ω' * φ ω' else treeTapeProb N Φ ε d ω'
      have h_rw_sub : ∀ sub : Fin N → TreeTape N Φ ε d,
          (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) *
            (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 then (1 : ℝ) else 0) =
          ∏ q : Fin N, g q (sub q) := by
        intro sub
        have h_ite : (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2
            then (1 : ℝ) else 0) = φ (sub q₀) := by
          simp only [φ, h_ind_eq sub]
        rw [h_ite, ← Finset.mul_prod_erase Finset.univ (fun q => g q (sub q)) (Finset.mem_univ q₀)]
        rw [← Finset.mul_prod_erase Finset.univ
          (fun q => treeTapeProb N Φ ε d (sub q)) (Finset.mem_univ q₀)]
        have h_er : (∏ q ∈ Finset.univ.erase q₀, g q (sub q)) =
            ∏ q ∈ Finset.univ.erase q₀, treeTapeProb N Φ ε d (sub q) := by
          refine Finset.prod_congr rfl (fun q hq => ?_)
          simp only [g, if_neg (Finset.ne_of_mem_erase hq)]
        simp only [g, ↓reduceIte, h_er]
        ring
      calc
        (∑ sub : Fin N → TreeTape N Φ ε d,
            (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) *
              (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 then (1 : ℝ) else 0))
          = ∑ sub : Fin N → TreeTape N Φ ε d, ∏ q : Fin N, g q (sub q) :=
              Finset.sum_congr rfl (fun sub _ => h_rw_sub sub)
        _ = ∏ q : Fin N, ∑ ω', g q ω' := (Fintype.prod_sum g).symm
        _ = (∑ ω', g q₀ ω') * ∏ q ∈ Finset.univ.erase q₀, ∑ ω', g q ω' :=
              (Finset.mul_prod_erase Finset.univ (fun q => ∑ ω', g q ω') (Finset.mem_univ q₀)).symm
        _ = ∑ ω' : TreeTape N Φ ε d,
              treeTapeProb N Φ ε d ω' *
                (if v ∉ (hseRun G w N h Φ ε d t.2.1 t.2.2 (Δ / 2) ω').2 then (1 : ℝ) else 0) := by
            have h_er_one : (∏ q ∈ Finset.univ.erase q₀, ∑ ω', g q ω') = 1 := by
              refine Finset.prod_eq_one (fun q hq => ?_)
              have hne : q ≠ q₀ := Finset.ne_of_mem_erase hq
              simp only [g, if_neg hne]
              exact h_params.prob_sum d
            simp only [g, ↓reduceIte, h_er_one, mul_one, φ]
  have h_ft_nonneg : ∀ τ : FinTape N Φ ε, 0 ≤ finTapeProb N Φ ε τ := by
    intro τ
    simpa [treeTapeProb] using h_params.prob_nonneg 1 (τ, fun _ => PUnit.unit)
  have h_depth_ind : ∀ (d : ℕ) (X M : Finset (Fin n)), X.Nonempty → M ⊆ X →
      ∀ Δ : ℝ, 1 ≤ Δ →
      (∀ u ∈ X, ∀ v' ∈ X,
        hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v' ≤
          ENNReal.ofReal Δ) →
      (2 ≤ X.card → 1 ≤ d ∧ Δ < 8 * (2 : ℝ) ^ (d - 1)) →
      ∀ v ∈ M,
      (∑ ω : TreeTape N Φ ε d,
        treeTapeProb N Φ ε d ω *
          (if v ∉ (hseRun G w N h Φ ε d X M Δ ω).2 then (1 : ℝ) else 0)) ≤
        hseExclPotential N Φ ε (X.card : ℝ) Δ := by
    intro d
    induction d with
    | zero =>
      intro X M hX_ne _ Δ hΔ1 _ _ v hvM
      have hm1 : (1 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hX_ne
      have h_zero : (∑ ω : TreeTape N Φ ε 0,
          treeTapeProb N Φ ε 0 ω *
            (if v ∉ (hseRun G w N h Φ ε 0 X M Δ ω).2 then (1 : ℝ) else 0)) = 0 := by
        refine Finset.sum_eq_zero (fun ω _ => ?_)
        have h_snd : (hseRun G w N h Φ ε 0 X M Δ ω).2 = M := rfl
        rw [h_snd, if_neg (not_not.mpr hvM), mul_zero]
      rw [h_zero]
      exact h_ana_nonneg (X.card : ℝ) Δ hm1 hΔ1
    | succ d ih =>
      intro X M hX_ne hMX Δ hΔ1 hΔ_diam h_term v hvM
      have hm1 : (1 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hX_ne
      by_cases hX1 : X.card ≤ 1
      · have h_zero : (∑ ω : TreeTape N Φ ε (d + 1),
            treeTapeProb N Φ ε (d + 1) ω *
              (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ ω).2 then (1 : ℝ) else 0)) = 0 := by
          refine Finset.sum_eq_zero (fun ω _ => ?_)
          rcases ω with ⟨τ, sub⟩
          have h_snd : (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 = M := by
            unfold hseRun
            rw [if_pos hX1]
          rw [h_snd, if_neg (not_not.mpr hvM), mul_zero]
        rw [h_zero]
        exact h_ana_nonneg (X.card : ℝ) Δ hm1 hΔ1
      · have hX2 : 2 ≤ X.card := by omega
        have hΔ_pos : 0 < Δ := by linarith
        have hΔ2 : 2 ≤ Δ := (h_ssp.scale_spec X M hX2 hMX Δ hΔ_pos hΔ_diam).1
        have hΔ_lt : Δ < 8 * (2 : ℝ) ^ d := by
          simpa using (h_term hX2).2
        let Q : FinTape N Φ ε → ℝ := fun τ =>
          ∑ sub : Fin N → TreeTape N Φ ε d,
            (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) *
              (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 then (1 : ℝ) else 0)
        have h_split :
            (∑ ω : TreeTape N Φ ε (d + 1),
              treeTapeProb N Φ ε (d + 1) ω *
                (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ ω).2 then (1 : ℝ) else 0)) =
            ∑ τ : FinTape N Φ ε, finTapeProb N Φ ε τ * Q τ := by
          change (∑ ω : FinTape N Φ ε × (Fin N → TreeTape N Φ ε d),
              treeTapeProb N Φ ε (d + 1) ω *
                (if v ∉ (hseRun G w N h Φ ε (d + 1) X M Δ ω).2 then (1 : ℝ) else 0)) =
            ∑ τ : FinTape N Φ ε, finTapeProb N Φ ε τ * Q τ
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun τ _ => ?_)
          simp only [Q, treeTapeProb, Finset.mul_sum, mul_assoc]
        rw [h_split]
        refine le_trans ?_ (h_pen_exp X M hX2 hMX Δ hΔ_pos hΔ_diam v hvM)
        refine Finset.sum_le_sum (fun τ _ => ?_)
        refine mul_le_mul_of_nonneg_left ?_ (h_ft_nonneg τ)
        obtain ⟨hQ1, hQ_eq⟩ := h_sub_cond d X M hX2 hMX Δ hΔ_pos hΔ_diam hΔ_lt v τ
        refine h_pen_le X M hX2 hMX Δ hΔ_pos hΔ_diam v τ (Q τ) hQ1 ?_
        intro t ht hvt
        dsimp only [Q]
        rw [hQ_eq t ht hvt]
        have ht_props := (h_ssp.scale_spec X M hX2 hMX Δ hΔ_pos hΔ_diam).2.1 τ |>.2.2.2.2 t ht
        have ht_M_sub : t.2.2 ⊆ t.2.1 :=
          Finset.Subset.trans ht_props.2.2.1 Finset.inter_subset_right
        have ht_term : 2 ≤ t.2.1.card → 1 ≤ d ∧ Δ / 2 < 8 * (2 : ℝ) ^ (d - 1) := by
          intro ht2
          by_cases hd0 : d = 0
          · subst hd0
            have hΔ8 : Δ < 8 := by simpa using hΔ_lt
            have hcard1 := ht_props.2.2.2.2.2.2 hΔ8
            omega
          · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
            refine ⟨hd1, ?_⟩
            have hpow : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - 1) * 2 := by
              conv_lhs => rw [← Nat.sub_add_cancel hd1, pow_succ]
            linarith
        have h_ih_t := ih t.2.1 t.2.2 ht_props.1 ht_M_sub (Δ / 2) (by linarith)
          ht_props.2.2.2.1 ht_term v hvt
        refine le_trans h_ih_t ?_
        have ht_card_pos : (0 : ℝ) < (t.2.1.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr ht_props.1
        by_cases ht1 : 1 ≤ t.1
        · rw [if_pos ht1]
          exact h_ana_mono_left _ _ (Δ / 2) ht_card_pos (ht_props.2.2.2.2.1 ht1)
        · rw [if_neg ht1]
          have h_sub_card : (t.2.1.card : ℝ) ≤ (X.card : ℝ) := by
            exact_mod_cast Finset.card_le_card ht_props.2.1
          exact h_ana_mono_left _ _ (Δ / 2) ht_card_pos h_sub_card
  intro v
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hβ_diam : ∀ u ∈ (Finset.univ : Finset (Fin n)), ∀ v' ∈ (Finset.univ : Finset (Fin n)),
      hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v' ≤
        ENNReal.ofReal Φ := by
    intro u _ v' _
    have h_mono : hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) u v' ≤
        hopDist G w h u v' := by
      simp only [hopDist]
      refine le_iInf₂ (fun p hp_len => ?_)
      have h_beta_pos : 0 < 2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one h_params.one_le_beta
      have h_le : h ≤ 2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h :=
        Nat.le_mul_of_pos_left h h_beta_pos
      exact iInf_le_of_le p (iInf_le_of_le (le_trans hp_len h_le) le_rfl)
    exact le_trans h_mono (hΦ_diam u v')
  have h_root := h_depth_ind (hstDepth Φ) Finset.univ Finset.univ huniv_ne
    (Finset.Subset.refl _) Φ (by linarith) hβ_diam
    (fun _ => ⟨h_params.one_le_depth, h_params.diam_lt_depth⟩) v (Finset.mem_univ v)
  have h_card_univ : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
  rw [h_card_univ] at h_root
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnN_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have h_mono_N := h_ana_mono_left (n : ℝ) (N : ℝ) Φ hn_pos hnN_real
  have h_eps : hseExclPotential N Φ ε (N : ℝ) Φ ≤ ε := by
    rw [h_pot_def]
    exact h_params.root_f_le_eps
  linarith

theorem hse_expected_distortion_bound (N n : ℕ) (hn : 2 ≤ n) (hnN : n ≤ N)
    (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 2 ≤ w e)
    (h : ℕ) (hh : 1 ≤ h)
    (Φ : ℝ) (hΦ_ge : 2 ≤ Φ)
    (hΦ_diam : ∀ u v : Fin n, hopDist G w h u v ≤ ENNReal.ofReal Φ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (h_params : HSTParamSpec N Φ ε)
    (h_ssp : SSPDetSpec N n G w h Φ ε)
    (h_hse : HSERunDetSpec N n G w h Φ ε) :
    ∀ u v : Fin n,
      (∑ ω : TreeTape N Φ ε (hstDepth Φ),
        treeTapeProb N Φ ε (hstDepth Φ) ω *
          savedRawDist (hseRun G w N h Φ ε (hstDepth Φ) Finset.univ Finset.univ Φ ω) u v) ≤
      (256 * (hstPhaseCount N : ℝ) * Real.logb 2 (N : ℝ) *
        (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Φ)) * (hopDist G w h u v).toReal :=
by
  
  have h_exp_mono : ∀ (m₁ m₂ : ℝ), 1 ≤ m₁ → m₁ ≤ m₂ → ∀ (y : ℝ),
      0 ≤ hseExpDistFactor N m₁ y ∧ hseExpDistFactor N m₁ y ≤ hseExpDistFactor N m₂ y := by
    intro m₁ m₂ hm₁ hm₁₂ y
    have hδ_pos : 0 < hstTruncDelta N := h_params.delta_pos
    have h12δ_nonneg : 0 ≤ 1 + 2 * hstTruncDelta N := by linarith
    have hrpow_nonneg : 0 ≤ (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 y) :=
      Real.rpow_nonneg h12δ_nonneg _
    have hlog_nonneg : 0 ≤ Real.logb 2 m₁ := Real.logb_nonneg (by norm_num) hm₁
    have hlog_le : Real.logb 2 m₁ ≤ Real.logb 2 m₂ :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hm₁₂
    have hL_nonneg : 0 ≤ 256 * (hstPhaseCount N : ℝ) := by positivity
    refine ⟨?_, ?_⟩
    · unfold hseExpDistFactor
      exact mul_nonneg (mul_nonneg hL_nonneg hlog_nonneg) hrpow_nonneg
    · unfold hseExpDistFactor
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_le hL_nonneg) hrpow_nonneg

  
  have h_slot_contraction : ∀ (m Δ d_uv : ℝ), 2 ≤ m → 2 ≤ Δ → 0 ≤ d_uv →
      ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ hstPhaseCount N →
        hseExpDistFactor N (m / (hstMu N ℓ : ℝ)) (Δ / 2) * d_uv +
          (d_uv / hstStep N Φ ε Δ ℓ) * hstGeomP N Φ ε ℓ * Δ ≤
          hseExpDistFactor N m (Δ / 2) * d_uv := by
    intro m Δ d_uv hm2 hΔ2 hd_nonneg ℓ hℓ1 hℓL
    have hμ2 : 2 ≤ hstMu N ℓ := (h_params.mu_sq ℓ hℓ1 hℓL).2
    have hμ_real2 : (2 : ℝ) ≤ (hstMu N ℓ : ℝ) := by exact_mod_cast hμ2
    have hk1 : 1 ≤ hstRadiusSteps N Φ ε := h_params.one_le_k
    have hk_pos : (0 : ℝ) < (hstRadiusSteps N Φ ε : ℝ) := by exact_mod_cast hk1
    have hk_ne : (hstRadiusSteps N Φ ε : ℝ) ≠ 0 := ne_of_gt hk_pos
    have hrad := (h_params.radius_bounds Δ (by linarith)).2.2 ℓ hℓ1 hℓL
    have hq_pos : 0 < hstStep N Φ ε Δ ℓ := hrad.2.1
    have hrad_ineq := hrad.2.2.2
    set δr : ℝ := hstRadius N Δ ℓ - hstRadius N Δ (ℓ - 1)
    have hq_def : hstStep N Φ ε Δ ℓ = δr / (hstRadiusSteps N Φ ε : ℝ) := rfl
    have hδr_pos : 0 < δr := by
      have hδr_eq : δr = hstStep N Φ ε Δ ℓ * (hstRadiusSteps N Φ ε : ℝ) := by
        rw [hq_def, div_mul_cancel₀ _ hk_ne]
      rw [hδr_eq]
      exact mul_pos hq_pos hk_pos
    have hδr_ne : δr ≠ 0 := ne_of_gt hδr_pos
    have h_sep_eq :
        (d_uv / hstStep N Φ ε Δ ℓ) * hstGeomP N Φ ε ℓ * Δ =
        2 * ((Δ / δr) * Real.log (2 * (hstMu N ℓ : ℝ) / hstTruncDelta N)) * d_uv := by
      rw [hq_def]
      unfold hstGeomP
      field_simp [hk_ne, hδr_ne]
    have h_sep_le1 :
        (d_uv / hstStep N Φ ε Δ ℓ) * hstGeomP N Φ ε ℓ * Δ ≤
        128 * (hstPhaseCount N : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ) * d_uv := by
      rw [h_sep_eq]
      nlinarith [hrad_ineq, hd_nonneg]
    set E : ℝ := (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2))
    have hδ_pos : 0 < hstTruncDelta N := h_params.delta_pos
    have hE_ge1 : 1 ≤ E :=
      Real.one_le_rpow (by linarith) (Real.logb_nonneg (by norm_num) (by linarith))
    have hlogμ_nonneg : 0 ≤ Real.logb 2 (hstMu N ℓ : ℝ) :=
      Real.logb_nonneg (by norm_num) (by linarith)
    have hL_nonneg : (0 : ℝ) ≤ (hstPhaseCount N : ℝ) := by positivity
    have h_prod_nonneg : 0 ≤ (hstPhaseCount N : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ) * d_uv :=
      mul_nonneg (mul_nonneg hL_nonneg hlogμ_nonneg) hd_nonneg
    have h_sep_le2 :
        (d_uv / hstStep N Φ ε Δ ℓ) * hstGeomP N Φ ε ℓ * Δ ≤
        256 * (hstPhaseCount N : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ) * E * d_uv := by
      nlinarith [h_sep_le1, hE_ge1, h_prod_nonneg]
    have hlog_div :
        Real.logb 2 (m / (hstMu N ℓ : ℝ)) = Real.logb 2 m - Real.logb 2 (hstMu N ℓ : ℝ) :=
      Real.logb_div (by linarith) (by linarith)
    have h_id :
        hseExpDistFactor N (m / (hstMu N ℓ : ℝ)) (Δ / 2) * d_uv +
          256 * (hstPhaseCount N : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ) * E * d_uv =
        hseExpDistFactor N m (Δ / 2) * d_uv := by
      unfold hseExpDistFactor
      change 256 * (hstPhaseCount N : ℝ) * Real.logb 2 (m / (hstMu N ℓ : ℝ)) * E * d_uv +
          256 * (hstPhaseCount N : ℝ) * Real.logb 2 (hstMu N ℓ : ℝ) * E * d_uv =
        256 * (hstPhaseCount N : ℝ) * Real.logb 2 m * E * d_uv
      rw [hlog_div]
      ring
    linarith

  
  have h_norm_rescale : ∀ (m Δ d_uv S : ℝ), 1 ≤ m → 0 < Δ → 0 ≤ d_uv →
      S ≤ hseExpDistFactor N m (Δ / 2) * d_uv →
      S / (∏ i : Fin (hstTotalSlots N),
        (1 - (1 - hstGeomP N Φ ε ((sspSlotPhases N).get i)) ^ hstRadiusSteps N Φ ε)) ≤
        hseExpDistFactor N m Δ * d_uv := by
    intro m Δ d_uv S hm1 hΔ_pos hd_nonneg hS
    set B₂ : ℝ := hseExpDistFactor N m (Δ / 2) * d_uv
    set Z_tot : ℝ := ∏ i : Fin (hstTotalSlots N),
      (1 - (1 - hstGeomP N Φ ε ((sspSlotPhases N).get i)) ^ hstRadiusSteps N Φ ε)
    have hB₂_nonneg : 0 ≤ B₂ :=
      mul_nonneg (h_exp_mono m m hm1 le_rfl (Δ / 2)).1 hd_nonneg
    have h1δ_pos : 0 < 1 - hstTruncDelta N := by linarith [h_params.delta_lt_half]
    have hZ_ge : 1 - hstTruncDelta N ≤ Z_tot := h_params.trunc_norm_prod_ge
    have hZ_pos : 0 < Z_tot := lt_of_lt_of_le h1δ_pos hZ_ge
    have h1 : S / Z_tot ≤ B₂ / Z_tot := div_le_div_of_nonneg_right hS (le_of_lt hZ_pos)
    have h2 : B₂ / Z_tot ≤ B₂ / (1 - hstTruncDelta N) :=
      div_le_div_of_nonneg_left hB₂_nonneg h1δ_pos hZ_ge
    have h3 : B₂ / (1 - hstTruncDelta N) ≤ (1 + 2 * hstTruncDelta N) * B₂ := by
      rw [div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right h_params.inv_one_sub_delta hB₂_nonneg
    have h12δ_pos : 0 < 1 + 2 * hstTruncDelta N := by linarith [h_params.delta_pos]
    have h12δ_ne : 1 + 2 * hstTruncDelta N ≠ 0 := ne_of_gt h12δ_pos
    have hlog_half : Real.logb 2 (Δ / 2) = Real.logb 2 Δ - 1 := by
      rw [Real.logb_div (ne_of_gt hΔ_pos) (by norm_num), Real.logb_self_eq_one (by norm_num)]
    have hrpow_half :
        (1 + 2 * hstTruncDelta N) * (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2)) =
        (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) := by
      rw [hlog_half, Real.rpow_sub h12δ_pos, Real.rpow_one, mul_div_cancel₀ _ h12δ_ne]
    have h4 : (1 + 2 * hstTruncDelta N) * B₂ = hseExpDistFactor N m Δ * d_uv := by
      dsimp [B₂, hseExpDistFactor]
      calc
        (1 + 2 * hstTruncDelta N) *
            (256 * (hstPhaseCount N : ℝ) * Real.logb 2 m *
              (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2)) * d_uv)
          = 256 * (hstPhaseCount N : ℝ) * Real.logb 2 m *
              ((1 + 2 * hstTruncDelta N) *
                (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 (Δ / 2))) * d_uv := by ring
        _ = 256 * (hstPhaseCount N : ℝ) * Real.logb 2 m *
              (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Δ) * d_uv := by rw [hrpow_half]
    linarith

  
  have h_single_slot :
      ∀ (k : ℕ), 1 ≤ k →
        ∀ (p d_uv q Δ G_child B : ℝ),
          0 < p → p < 1 → 0 < d_uv → 0 < q → 0 ≤ Δ → 0 ≤ G_child →
          G_child + (d_uv / q) * p * Δ ≤ B →
          ∀ (ρ_u ρ_v : ℤ),
            ρ_u ≤ ρ_v →
            ρ_v ≤ ρ_u + (Nat.ceil (d_uv / q) : ℤ) →
            ∀ (val : ℕ → ℝ),
              (∀ R < k, (R : ℤ) < ρ_u - 1 → val R ≤ B) →
              (∀ R < k, ρ_v + 1 ≤ (R : ℤ) → val R ≤ G_child) →
              (∀ R < k, ρ_u + 1 ≤ (R : ℤ) → (R : ℤ) ≤ ρ_v - 2 → val R ≤ Δ) →
              (∀ R < k, ((R : ℤ) = ρ_u - 1 ∨ (R : ℤ) = ρ_u ∨
                         (R : ℤ) = ρ_v - 1 ∨ (R : ℤ) = ρ_v) → val R ≤ 0) →
              (∑ R ∈ Finset.range k, ((1 - p) ^ R * p) * val R) ≤ B := by
    intro k _ p d_uv q Δ G_child B hp_pos hp_lt1 hd_pos hq_pos hΔ_nn hG_nn hB_bound
      ρ_u ρ_v hρ_le hρ_lip val h_lt h_gt h_mid h_pad
    have h1p_nn : 0 ≤ 1 - p := by linarith
    have h1p_le1 : 1 - p ≤ 1 := by linarith
    have h_sep_nn : 0 ≤ (d_uv / q) * p * Δ := by positivity
    have hB_nn : 0 ≤ B := by linarith
    have hw_nn : ∀ R : ℕ, 0 ≤ (1 - p) ^ R * p :=
      fun R => mul_nonneg (pow_nonneg h1p_nn R) (le_of_lt hp_pos)
    have hw_sum : ∀ m : ℕ, (∑ R ∈ Finset.range m, (1 - p) ^ R * p) = 1 - (1 - p) ^ m := by
      intro m
      calc
        (∑ R ∈ Finset.range m, (1 - p) ^ R * p)
          = (∑ R ∈ Finset.range m, (1 - p) ^ R) * (1 - (1 - p)) := by
              rw [← Finset.sum_mul]; ring
        _ = 1 - (1 - p) ^ m := geom_sum_mul_neg (1 - p) m
    set s : ℕ := Int.toNat (max 0 (ρ_u - 1))
    have hs_int : (s : ℤ) = max 0 (ρ_u - 1) := Int.toNat_of_nonneg (le_max_left 0 _)
    by_cases hks : k ≤ s
    · calc
        (∑ R ∈ Finset.range k, ((1 - p) ^ R * p) * val R)
          ≤ ∑ R ∈ Finset.range k, ((1 - p) ^ R * p) * B := by
              refine Finset.sum_le_sum (fun R hR => ?_)
              rw [Finset.mem_range] at hR
              exact mul_le_mul_of_nonneg_left (h_lt R hR (by omega)) (hw_nn R)
        _ = (1 - (1 - p) ^ k) * B := by rw [← Finset.sum_mul, hw_sum]
        _ ≤ B := by nlinarith [pow_nonneg h1p_nn k, hB_nn]
    · have hsk_le : s ≤ k := by omega
      rw [← Finset.sum_range_add_sum_Ico _ hsk_le]
      have h_pref :
          (∑ R ∈ Finset.range s, ((1 - p) ^ R * p) * val R) ≤ (1 - (1 - p) ^ s) * B := by
        calc
          (∑ R ∈ Finset.range s, ((1 - p) ^ R * p) * val R)
            ≤ ∑ R ∈ Finset.range s, ((1 - p) ^ R * p) * B := by
                refine Finset.sum_le_sum (fun R hR => ?_)
                rw [Finset.mem_range] at hR
                exact mul_le_mul_of_nonneg_left (h_lt R (by omega) (by omega)) (hw_nn R)
          _ = (1 - (1 - p) ^ s) * B := by rw [← Finset.sum_mul, hw_sum]
      have hw_Ico : (∑ R ∈ Finset.Ico s k, (1 - p) ^ R * p) = (1 - p) ^ s - (1 - p) ^ k := by
        have hsplit := Finset.sum_range_add_sum_Ico (fun R => (1 - p) ^ R * p) hsk_le
        rw [hw_sum s, hw_sum k] at hsplit
        linarith
      let P_pred : ℕ → Prop := fun R => ρ_u + 1 ≤ (R : ℤ) ∧ (R : ℤ) ≤ ρ_v - 2
      have h_pt : ∀ R ∈ Finset.Ico s k,
          val R ≤ G_child + (if P_pred R then Δ else 0) := by
        intro R hR
        rw [Finset.mem_Ico] at hR
        have hR_ge : ρ_u - 1 ≤ (R : ℤ) := by omega
        by_cases hP : P_pred R
        · simp only [hP, ↓reduceIte]
          have := h_mid R hR.2 hP.1 hP.2
          linarith
        · simp only [hP, ↓reduceIte, add_zero]
          have hP' : ¬(ρ_u + 1 ≤ (R : ℤ) ∧ (R : ℤ) ≤ ρ_v - 2) := hP
          by_cases hgt : ρ_v + 1 ≤ (R : ℤ)
          · exact h_gt R hR.2 hgt
          · have hpad :
                (R : ℤ) = ρ_u - 1 ∨ (R : ℤ) = ρ_u ∨ (R : ℤ) = ρ_v - 1 ∨ (R : ℤ) = ρ_v := by
              omega
            linarith [h_pad R hR.2 hpad]
      have h_suff1 :
          (∑ R ∈ Finset.Ico s k, ((1 - p) ^ R * p) * val R) ≤
          ((1 - p) ^ s - (1 - p) ^ k) * G_child +
            ∑ R ∈ (Finset.Ico s k).filter P_pred, ((1 - p) ^ R * p) * Δ := by
        calc
          (∑ R ∈ Finset.Ico s k, ((1 - p) ^ R * p) * val R)
            ≤ ∑ R ∈ Finset.Ico s k,
                (((1 - p) ^ R * p) * G_child +
                  if P_pred R then ((1 - p) ^ R * p) * Δ else 0) := by
                refine Finset.sum_le_sum (fun R hR => ?_)
                have hptR := mul_le_mul_of_nonneg_left (h_pt R hR) (hw_nn R)
                by_cases hP : P_pred R <;> simp only [hP, ↓reduceIte] at hptR ⊢ <;> linarith
          _ = (∑ R ∈ Finset.Ico s k, ((1 - p) ^ R * p) * G_child) +
              (∑ R ∈ Finset.Ico s k, if P_pred R then ((1 - p) ^ R * p) * Δ else 0) :=
                Finset.sum_add_distrib
          _ = ((1 - p) ^ s - (1 - p) ^ k) * G_child +
              ∑ R ∈ (Finset.Ico s k).filter P_pred, ((1 - p) ^ R * p) * Δ := by
                rw [← Finset.sum_mul, hw_Ico, ← Finset.sum_filter]
      set P_set := (Finset.Ico s k).filter P_pred
      have h_filter_le :
          (∑ R ∈ P_set, ((1 - p) ^ R * p) * Δ) ≤
          (P_set.card : ℝ) * (((1 - p) ^ s * p) * Δ) := by
        calc
          (∑ R ∈ P_set, ((1 - p) ^ R * p) * Δ)
            ≤ ∑ _R ∈ P_set, ((1 - p) ^ s * p) * Δ := by
                refine Finset.sum_le_sum (fun R hR => ?_)
                have hsR : s ≤ R := (Finset.mem_Ico.mp (Finset.mem_filter.mp hR).1).1
                have hpow : (1 - p) ^ R ≤ (1 - p) ^ s :=
                  pow_le_pow_of_le_one h1p_nn h1p_le1 hsR
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hpow (le_of_lt hp_pos)) hΔ_nn
          _ = (P_set.card : ℝ) * (((1 - p) ^ s * p) * Δ) := by
                simp [Finset.sum_const, nsmul_eq_mul]
      set χ : ℝ := d_uv / q
      have hχ_pos : 0 < χ := div_pos hd_pos hq_pos
      have h_card : (P_set.card : ℝ) ≤ χ := by
        by_cases hP_ne : P_set.Nonempty
        · rcases hP_ne with ⟨R₀, hR₀⟩
          have hR₀' := Finset.mem_filter.mp hR₀
          set a : ℕ := Int.toNat (max 0 (ρ_u + 1))
          set b : ℕ := Int.toNat (max 0 (ρ_v - 1))
          have ha_int : (a : ℤ) = max 0 (ρ_u + 1) := Int.toNat_of_nonneg (le_max_left 0 _)
          have hb_int : (b : ℤ) = max 0 (ρ_v - 1) := Int.toNat_of_nonneg (le_max_left 0 _)
          have h_sub_Ico : P_set ⊆ Finset.Ico a b := by
            intro R hR
            have hR' := Finset.mem_filter.mp hR
            rw [Finset.mem_Ico]
            have hP_R : ρ_u + 1 ≤ (R : ℤ) ∧ (R : ℤ) ≤ ρ_v - 2 := hR'.2
            omega
          have hab : a ≤ b := by
            have := Finset.mem_Ico.mp (h_sub_Ico hR₀)
            omega
          have hcard_nat : P_set.card ≤ b - a := by
            simpa only [Nat.card_Ico] using Finset.card_le_card h_sub_Ico
          have hP_R₀ : ρ_u + 1 ≤ (R₀ : ℤ) ∧ (R₀ : ℤ) ≤ ρ_v - 2 := hR₀'.2
          have hcard_int : (P_set.card : ℤ) ≤ (Nat.ceil χ : ℤ) - 2 := by omega
          have hcard_real : (P_set.card : ℝ) ≤ (Nat.ceil χ : ℝ) - 2 := by
            exact_mod_cast hcard_int
          have hceil_lt : (Nat.ceil χ : ℝ) < χ + 1 := Nat.ceil_lt_add_one (le_of_lt hχ_pos)
          linarith
        · rw [Finset.not_nonempty_iff_eq_empty.mp hP_ne]
          simp [le_of_lt hχ_pos]
      have h_filter_le2 :
          (P_set.card : ℝ) * (((1 - p) ^ s * p) * Δ) ≤ χ * (((1 - p) ^ s * p) * Δ) :=
        mul_le_mul_of_nonneg_right h_card (mul_nonneg (hw_nn s) hΔ_nn)
      have h_pow_s_nn : 0 ≤ (1 - p) ^ s := pow_nonneg h1p_nn s
      have h_pow_k_nn : 0 ≤ (1 - p) ^ k := pow_nonneg h1p_nn k
      have h_G_drop : ((1 - p) ^ s - (1 - p) ^ k) * G_child ≤ (1 - p) ^ s * G_child := by
        nlinarith
      have h_comb :
          (1 - p) ^ s * G_child + χ * (((1 - p) ^ s * p) * Δ) ≤ (1 - p) ^ s * B := by
        calc
          (1 - p) ^ s * G_child + χ * (((1 - p) ^ s * p) * Δ)
            = (1 - p) ^ s * (G_child + χ * p * Δ) := by ring
          _ ≤ (1 - p) ^ s * B := mul_le_mul_of_nonneg_left hB_bound h_pow_s_nn
      linarith

  
  have h_hop_comm : ∀ (H : ℕ) (x y : Fin n), hopDist G w H x y = hopDist G w H y x := by
    have h_le : ∀ (H : ℕ) (x y : Fin n), hopDist G w H x y ≤ hopDist G w H y x := by
      intro H x y
      simp only [hopDist]
      refine le_iInf₂ (fun p hp => ?_)
      have hlen : p.reverse.length ≤ H := by
        simpa only [SimpleGraph.Walk.length_reverse] using hp
      refine le_trans (iInf₂_le p.reverse hlen) ?_
      have hw_rev : walkWeight w p.reverse = walkWeight w p := by
        simp only [walkWeight, SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]
      rw [hw_rev]
    exact fun H x y => le_antisymm (h_le H x y) (h_le H y x)

  have h_dist_go : ∀ (u v : Fin n) (Δ : ℝ) (cs : List (RawHST (Fin n))) (c₀ : RawHST (Fin n)),
      (cs.map RawHST.cluster).Pairwise Disjoint →
      c₀ ∈ cs → u ∈ c₀.cluster → v ∈ c₀.cluster →
      RawHST.dist.go u v Δ cs = c₀.dist u v := by
    intro u v Δ cs c₀
    induction cs with
    | nil => intro _ hc₀; cases hc₀
    | cons c cs' ih =>
      intro hp hc₀ hu₀ hv₀
      rw [List.map_cons, List.pairwise_cons] at hp
      rcases List.mem_cons.mp hc₀ with rfl | hc₀'
      · simp [RawHST.dist.go, hu₀, hv₀]
      · have hdisj : Disjoint c.cluster c₀.cluster :=
          hp.1 c₀.cluster (List.mem_map.mpr ⟨c₀, hc₀', rfl⟩)
        have hu_not : u ∉ c.cluster := Finset.disjoint_right.mp hdisj hu₀
        simp [RawHST.dist.go, hu_not, ih hp.2 hc₀' hu₀ hv₀]

  have h_sub_sum_one : ∀ (d : ℕ),
      (∑ sub : Fin N → TreeTape N Φ ε d, ∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) = 1 := by
    intro d
    rw [← Fintype.prod_sum (fun (_ : Fin N) (ω : TreeTape N Φ ε d) => treeTapeProb N Φ ε d ω)]
    simp [h_params.prob_sum d]

  have h_sub_marg : ∀ (d : ℕ) (q₀ : Fin N) (F : TreeTape N Φ ε d → ℝ),
      (∑ sub : Fin N → TreeTape N Φ ε d,
        (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) * F (sub q₀)) =
      ∑ ω : TreeTape N Φ ε d, treeTapeProb N Φ ε d ω * F ω := by
    intro d q₀ F
    let g : Fin N → TreeTape N Φ ε d → ℝ :=
      fun q ω => if q = q₀ then treeTapeProb N Φ ε d ω * F ω else treeTapeProb N Φ ε d ω
    have h_pt : ∀ sub : Fin N → TreeTape N Φ ε d,
        (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) * F (sub q₀) =
        ∏ q : Fin N, g q (sub q) := by
      intro sub
      rw [← Finset.mul_prod_erase Finset.univ (fun q => treeTapeProb N Φ ε d (sub q))
            (Finset.mem_univ q₀),
          ← Finset.mul_prod_erase Finset.univ (fun q => g q (sub q)) (Finset.mem_univ q₀)]
      have h_rest : (∏ q ∈ Finset.univ.erase q₀, g q (sub q)) =
          ∏ q ∈ Finset.univ.erase q₀, treeTapeProb N Φ ε d (sub q) := by
        refine Finset.prod_congr rfl (fun q hq => ?_)
        simp [g, (Finset.mem_erase.mp hq).1]
      simp only [g, ↓reduceIte, h_rest]
      ring
    simp_rw [h_pt]
    rw [← Fintype.prod_sum g,
        ← Finset.mul_prod_erase Finset.univ (fun q => ∑ ω, g q ω) (Finset.mem_univ q₀)]
    have h_rest_one : (∏ q ∈ Finset.univ.erase q₀, ∑ ω, g q ω) = 1 := by
      refine Finset.prod_eq_one (fun q hq => ?_)
      have hne : q ≠ q₀ := (Finset.mem_erase.mp hq).1
      simp [g, hne, h_params.prob_sum d]
    rw [h_rest_one, mul_one]
    simp [g]

  
  have h_level_step :
      ∀ (d : ℕ) (X M : Finset (Fin n)), 2 ≤ X.card → M ⊆ X →
        ∀ (Δ : ℝ), 0 < Δ →
          (∀ x ∈ X, ∀ y ∈ X,
            hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) x y ≤
              ENNReal.ofReal Δ) →
          Δ < 8 * (2 : ℝ) ^ d →
          (∀ (Xq Mq : Finset (Fin n)), Xq.Nonempty → Mq ⊆ Xq →
            (∀ x ∈ Xq, ∀ y ∈ Xq,
              hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) x y ≤
                ENNReal.ofReal (Δ / 2)) →
            (2 ≤ Xq.card → 1 ≤ d ∧ Δ / 2 < 8 * (2 : ℝ) ^ (d - 1)) →
            ∀ u' ∈ Xq, ∀ v' ∈ Xq,
              (∑ ω : TreeTape N Φ ε d,
                treeTapeProb N Φ ε d ω *
                  savedRawDist (hseRun G w N h Φ ε d Xq Mq (Δ / 2) ω) u' v') ≤
              hseExpDistFactor N (Xq.card : ℝ) (Δ / 2) * (hopDist G w h u' v').toReal) →
          ∀ u ∈ M, ∀ v ∈ M, u ≠ v →
            ∀ (τ : FinTape N Φ ε),
              (∑ sub : Fin N → TreeTape N Φ ε d,
                (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) *
                  savedRawDist (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)) u v) ≤
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ (hopDist G w h u v).toReal
                u v X M (hseExpDistStepsOfTape (sspSlotPhases N) τ) := by
    intro d X M hX2 hMX Δ hΔ_pos hΔ_diam hΔ_depth h_ih u huM v hvM huv τ
    set d_uv : ℝ := (hopDist G w h u v).toReal
    have hd_uv_ge2 : 2 ≤ d_uv := (h_ssp.hopDist_toReal_bounds u v huv).1
    have hd_uv_nn : 0 ≤ d_uv := by linarith
    have hscale := h_ssp.scale_spec X M hX2 hMX Δ hΔ_pos hΔ_diam
    have hΔ_ge2 : 2 ≤ Δ := hscale.1
    have hX1_real : (1 : ℝ) ≤ (X.card : ℝ) := by
      have : 1 ≤ X.card := by omega
      exact_mod_cast this

    
    have h_dom : ∀ (steps : List (ℕ × ℕ)),
        (∀ p ∈ steps, 1 ≤ p.1 ∧ p.1 ≤ hstPhaseCount N) →
        ∀ (X_cur M_cur : Finset (Fin n)), X_cur ⊆ X → M_cur ⊆ X_cur →
          let res_ssp := sspRunSteps G w N h Φ ε Δ X.card X_cur M_cur steps
          let outList :=
            if res_ssp.2.1.Nonempty then res_ssp.1 ++ [(0, res_ssp.2.1, res_ssp.2.2)]
            else res_ssp.1
          let P := hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur steps
          (∀ t ∈ outList, t.2.2 ⊆ M_cur) ∧
          0 ≤ P ∧
          (∀ t ∈ outList, u ∈ t.2.2 → v ∈ t.2.2 →
            (if t.1 = 0 then hseExpDistFactor N (X.card : ℝ) (Δ / 2)
             else hseExpDistFactor N ((X.card : ℝ) / (hstMu N t.1 : ℝ)) (Δ / 2)) * d_uv ≤ P) ∧
          ((∃ t₁ ∈ outList, u ∈ t₁.2.2) → (∃ t₂ ∈ outList, v ∈ t₂.2.2) →
            ¬(∃ t ∈ outList, u ∈ t.2.2 ∧ v ∈ t.2.2) → Δ ≤ P) := by
      intro steps
      induction steps with
      | nil =>
        intro _ X_cur M_cur _ _
        dsimp only [sspRunSteps, hseExpDistPenaltySteps]
        have hB2_nn : 0 ≤ hseExpDistFactor N (X.card : ℝ) (Δ / 2) * d_uv :=
          mul_nonneg (h_exp_mono _ _ hX1_real le_rfl (Δ / 2)).1 hd_uv_nn
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro t ht
          by_cases hne : X_cur.Nonempty <;> simp [hne] at ht
          rcases ht with rfl
          exact Finset.Subset.refl _
        · by_cases huvM : u ∈ M_cur ∧ v ∈ M_cur <;> simp [huvM, hB2_nn]
        · intro t ht hu_t hv_t
          by_cases hne : X_cur.Nonempty <;> simp [hne] at ht
          rcases ht with rfl
          simp [hu_t, hv_t]
        · intro h1 h2 hnot
          by_cases hne : X_cur.Nonempty <;> simp [hne] at h1 h2 hnot
          exfalso
          exact hnot h1 h2
      | cons step rest ih_steps =>
        rcases step with ⟨ℓ, R⟩
        intro hsteps X_cur M_cur hX_cur hM_cur
        have hℓ : 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N := hsteps (ℓ, R) List.mem_cons_self
        have hrest : ∀ p ∈ rest, 1 ≤ p.1 ∧ p.1 ≤ hstPhaseCount N :=
          fun p hp => hsteps p (List.mem_cons_of_mem _ hp)
        set cands := sspCands G w N h Φ ε Δ X.card X_cur ℓ
        by_cases hc : cands.Nonempty
        · set x := cands.min' hc
          set Xj := hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ)
          set Mj := hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur
          set M_next := M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1)
          have hx_cands : x ∈ cands := Finset.min'_mem cands hc
          simp only [cands, sspCands, Finset.mem_filter] at hx_cands
          have hx_cur : x ∈ X_cur := hx_cands.1
          have hx_upper :
              ((hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) ≤
              (X.card : ℝ) / (hstMu N ℓ : ℝ) := hx_cands.2.2
          have hball_spec := hscale.2.2 X_cur hX_cur x hx_cur ℓ hℓ.1 hℓ.2
          have hx_in_k : x ∈ hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ) :=
            hball_spec.2.1 0 (hstRadiusSteps N Φ ε : ℤ) (by positivity) hball_spec.1
          have h_ratio1 : 1 ≤ (X.card : ℝ) / (hstMu N ℓ : ℝ) := by
            have hcard1 : 1 ≤ (hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card :=
              Finset.one_le_card.mpr ⟨x, hx_in_k⟩
            have hcard1_real :
                (1 : ℝ) ≤ ((hstBall G w N h Φ ε Δ X_cur x ℓ (hstRadiusSteps N Φ ε : ℤ)).card : ℝ) := by
              exact_mod_cast hcard1
            linarith
          have hXnext_sub : X_cur \ Xj ⊆ X := Finset.Subset.trans Finset.sdiff_subset hX_cur
          have hMnext_sub_Xnext : M_next ⊆ X_cur \ Xj := by
            intro z hz
            rw [Finset.mem_sdiff] at hz ⊢
            refine ⟨hM_cur hz.1, fun hzXj => hz.2 ?_⟩
            exact hball_spec.2.1 (R : ℤ) ((R : ℤ) + 1) (by omega) hzXj
          have hDisj_M : Disjoint Mj M_next := by
            refine Finset.disjoint_left.mpr (fun z hz1 hz2 => ?_)
            exact (Finset.mem_sdiff.mp hz2).2
              (hball_spec.2.1 ((R : ℤ) - 1) ((R : ℤ) + 1) (by omega) (Finset.mem_inter.mp hz1).1)
          have ih' := ih_steps hrest (X_cur \ Xj) M_next hXnext_sub hMnext_sub_Xnext
          set res' := sspRunSteps G w N h Φ ε Δ X.card (X_cur \ Xj) M_next rest
          set outList' :=
            if res'.2.1.Nonempty then res'.1 ++ [(0, res'.2.1, res'.2.2)] else res'.1
          set P' := hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v (X_cur \ Xj) M_next rest
          have hout_eq :
              (let res_ssp := sspRunSteps G w N h Φ ε Δ X.card X_cur M_cur ((ℓ, R) :: rest)
               if res_ssp.2.1.Nonempty then res_ssp.1 ++ [(0, res_ssp.2.1, res_ssp.2.2)]
               else res_ssp.1) = (ℓ, Xj, Mj) :: outList' := by
            simp only [sspRunSteps, show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl,
              dif_pos hc]
            by_cases hne : res'.2.1.Nonempty <;> simp [outList', res', Xj, Mj, M_next, x, hne]
          have hP_eq :
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur ((ℓ, R) :: rest) =
              if u ∈ Mj ∧ v ∈ Mj then
                hseExpDistFactor N ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2) * d_uv
              else if (u ∈ Mj ∧ v ∈ M_next) ∨ (v ∈ Mj ∧ u ∈ M_next) then
                Δ
              else if u ∈ M_next ∧ v ∈ M_next then
                P'
              else 0 := by
            simp only [hseExpDistPenaltySteps,
              show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl, dif_pos hc]
            rfl
          dsimp only
          rw [hout_eq, hP_eq]
          have hI0 : ∀ t ∈ (ℓ, Xj, Mj) :: outList', t.2.2 ⊆ M_cur := by
            intro t ht
            rcases List.mem_cons.mp ht with rfl | ht'
            · exact Finset.inter_subset_right
            · exact Finset.Subset.trans (ih'.1 t ht') Finset.sdiff_subset
          refine ⟨hI0, ?_⟩
          by_cases hb1 : u ∈ Mj ∧ v ∈ Mj
          · simp only [hb1]
            refine ⟨mul_nonneg (h_exp_mono _ _ h_ratio1 le_rfl (Δ / 2)).1 hd_uv_nn, ?_, ?_⟩
            · intro t ht hu_t _
              rcases List.mem_cons.mp ht with rfl | ht'
              · have hℓ_ne0 : ℓ ≠ 0 := by omega
                simp [hℓ_ne0]
              · exfalso
                exact Finset.disjoint_left.mp hDisj_M hb1.1 (ih'.1 t ht' hu_t)
            · intro _ _ hnot
              exfalso
              exact hnot ⟨(ℓ, Xj, Mj), List.mem_cons_self, hb1.1, hb1.2⟩
          · simp only [hb1, ↓reduceIte]
            by_cases hb2 : (u ∈ Mj ∧ v ∈ M_next) ∨ (v ∈ Mj ∧ u ∈ M_next)
            · simp only [hb2, ↓reduceIte]
              refine ⟨by linarith, ?_, fun _ _ _ => le_rfl⟩
              intro t ht hu_t hv_t
              exfalso
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact hb1 ⟨hu_t, hv_t⟩
              · have hu_next : u ∈ M_next := ih'.1 t ht' hu_t
                have hv_next : v ∈ M_next := ih'.1 t ht' hv_t
                rcases hb2 with ⟨hu_j, _⟩ | ⟨hv_j, _⟩
                · exact Finset.disjoint_left.mp hDisj_M hu_j hu_next
                · exact Finset.disjoint_left.mp hDisj_M hv_j hv_next
            · simp only [hb2, ↓reduceIte]
              by_cases hb3 : u ∈ M_next ∧ v ∈ M_next
              · simp only [hb3]
                have hu_not_j : u ∉ Mj := fun hj => Finset.disjoint_left.mp hDisj_M hj hb3.1
                have hv_not_j : v ∉ Mj := fun hj => Finset.disjoint_left.mp hDisj_M hj hb3.2
                refine ⟨ih'.2.1, ?_, ?_⟩
                · intro t ht hu_t hv_t
                  rcases List.mem_cons.mp ht with rfl | ht'
                  · exfalso; exact hu_not_j hu_t
                  · exact ih'.2.2.1 t ht' hu_t hv_t
                · rintro ⟨t₁, ht₁, hu₁⟩ ⟨t₂, ht₂, hv₂⟩ hnot
                  have ht₁' : t₁ ∈ outList' := by
                    rcases List.mem_cons.mp ht₁ with rfl | h
                    · exfalso; exact hu_not_j hu₁
                    · exact h
                  have ht₂' : t₂ ∈ outList' := by
                    rcases List.mem_cons.mp ht₂ with rfl | h
                    · exfalso; exact hv_not_j hv₂
                    · exact h
                  have hnot' : ¬∃ t ∈ outList', u ∈ t.2.2 ∧ v ∈ t.2.2 :=
                    fun ⟨t, ht, huv_t⟩ => hnot ⟨t, List.mem_cons_of_mem _ ht, huv_t⟩
                  exact ih'.2.2.2 ⟨t₁, ht₁', hu₁⟩ ⟨t₂, ht₂', hv₂⟩ hnot'
              · simp only [hb3, ↓reduceIte]
                have h_miss : (u ∉ Mj ∧ u ∉ M_next) ∨ (v ∉ Mj ∧ v ∉ M_next) := by tauto
                have h_no_mem :
                    (∀ t ∈ (ℓ, Xj, Mj) :: outList', u ∉ t.2.2) ∨
                    (∀ t ∈ (ℓ, Xj, Mj) :: outList', v ∉ t.2.2) := by
                  rcases h_miss with ⟨hu1, hu2⟩ | ⟨hv1, hv2⟩
                  · left
                    intro t ht hu_t
                    rcases List.mem_cons.mp ht with rfl | ht'
                    · exact hu1 hu_t
                    · exact hu2 (ih'.1 t ht' hu_t)
                  · right
                    intro t ht hv_t
                    rcases List.mem_cons.mp ht with rfl | ht'
                    · exact hv1 hv_t
                    · exact hv2 (ih'.1 t ht' hv_t)
                refine ⟨le_rfl, ?_, ?_⟩
                · intro t ht hu_t hv_t
                  exfalso
                  rcases h_no_mem with hnu | hnv
                  · exact hnu t ht hu_t
                  · exact hnv t ht hv_t
                · rintro ⟨t₁, ht₁, hu₁⟩ ⟨t₂, ht₂, hv₂⟩ _
                  exfalso
                  rcases h_no_mem with hnu | hnv
                  · exact hnu t₁ ht₁ hu₁
                  · exact hnv t₂ ht₂ hv₂
        · dsimp only
          simp only [sspRunSteps, hseExpDistPenaltySteps,
            show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl, dif_neg hc]
          exact ih_steps hrest X_cur M_cur hX_cur hM_cur

    
    have h_steps_valid :
        ∀ p ∈ hseExpDistStepsOfTape (sspSlotPhases N) τ, 1 ≤ p.1 ∧ p.1 ≤ hstPhaseCount N := by
      intro p hp
      rw [hseExpDistStepsOfTape, List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact h_params.slot_phases_bounds _ (List.get_mem (sspSlotPhases N) i)
    have h_dom_τ :
        (∀ t ∈ sspTaggedClusters G w N h Φ ε X M Δ τ, t.2.2 ⊆ M) ∧
        0 ≤ hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X M
          (hseExpDistStepsOfTape (sspSlotPhases N) τ) ∧
        (∀ t ∈ sspTaggedClusters G w N h Φ ε X M Δ τ, u ∈ t.2.2 → v ∈ t.2.2 →
          (if t.1 = 0 then hseExpDistFactor N (X.card : ℝ) (Δ / 2)
           else hseExpDistFactor N ((X.card : ℝ) / (hstMu N t.1 : ℝ)) (Δ / 2)) * d_uv ≤
            hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X M
              (hseExpDistStepsOfTape (sspSlotPhases N) τ)) ∧
        ((∃ t₁ ∈ sspTaggedClusters G w N h Φ ε X M Δ τ, u ∈ t₁.2.2) →
          (∃ t₂ ∈ sspTaggedClusters G w N h Φ ε X M Δ τ, v ∈ t₂.2.2) →
          ¬(∃ t ∈ sspTaggedClusters G w N h Φ ε X M Δ τ, u ∈ t.2.2 ∧ v ∈ t.2.2) →
          Δ ≤ hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X M
            (hseExpDistStepsOfTape (sspSlotPhases N) τ)) :=
      h_dom (hseExpDistStepsOfTape (sspSlotPhases N) τ) h_steps_valid
        X M (Finset.Subset.refl X) hMX
    have htclus_spec :
        sspTaggedClusters G w N h Φ ε X M Δ τ ≠ [] ∧
        (sspTaggedClusters G w N h Φ ε X M Δ τ).length ≤ N ∧
        ((sspTaggedClusters G w N h Φ ε X M Δ τ).map (fun t => t.2.1)).Pairwise Disjoint ∧
        (sspTaggedClusters G w N h Φ ε X M Δ τ).foldr (fun t acc => t.2.1 ∪ acc) ∅ = X ∧
        (∀ t ∈ sspTaggedClusters G w N h Φ ε X M Δ τ,
          t.2.1.Nonempty ∧
          t.2.1 ⊆ X ∧
          t.2.2 ⊆ M ∩ t.2.1 ∧
          (∀ x ∈ t.2.1, ∀ y ∈ t.2.1,
            hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) x y ≤
              ENNReal.ofReal (Δ / 2)) ∧
          (1 ≤ t.1 → (t.2.1.card : ℝ) ≤ (X.card : ℝ) / (hstMu N t.1 : ℝ)) ∧
          (∀ x ∈ t.2.2, ∀ y ∈ X \ t.2.1,
            ENNReal.ofReal Δ ≤
              ENNReal.ofReal (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ)) *
                hopDist G w h x y) ∧
          (Δ < 8 → t.2.1.card = 1)) := hscale.2.1 τ
    have hclus_def :
        sspClusters G w N h Φ ε X M Δ τ =
          (sspTaggedClusters G w N h Φ ε X M Δ τ).map (fun t => (t.2.1, t.2.2)) := rfl
    have hX_not_le1 : ¬(X.card ≤ 1) := by omega
    have hX_ne : X.Nonempty := ⟨u, hMX huM⟩
    have h_parent_depth : 2 ≤ X.card → 1 ≤ d + 1 ∧ Δ < 8 * (2 : ℝ) ^ ((d + 1) - 1) :=
      fun _ => ⟨by omega, hΔ_depth⟩
    have hse_step_eq : ∀ sub : Fin N → TreeTape N Φ ε d,
        hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub) =
          let clus := sspClusters G w N h Φ ε X M Δ τ
          let childRes : Fin clus.length → RawHST (Fin n) × Finset (Fin n) :=
            fun idx =>
              let c := clus.get idx
              if hq : idx.1 < N then
                hseRun G w N h Φ ε d c.1 c.2 (Δ / 2) (sub ⟨idx.1, hq⟩)
              else
                (RawHST.leaf c.1, c.2)
          (RawHST.node X Δ (List.ofFn (fun idx => (childRes idx).1)),
           Finset.univ.biUnion (fun idx => (childRes idx).2)) := by
      intro sub
      simp only [hseRun, hX_not_le1, ↓reduceIte]
    have h_parent_valid_and_dist : ∀ sub : Fin N → TreeTape N Φ ε d,
        ValidRawHST (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).1 ∧
        (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).1.dist u v ≤ Δ := by
      intro sub
      have hrun := h_hse.run_spec (d + 1) X M hX_ne hMX Δ hΔ_pos hΔ_diam h_parent_depth (τ, sub)
      exact ⟨hrun.1, (hrun.2.2.2.2.1 u v).2⟩

    generalize sspTaggedClusters G w N h Φ ε X M Δ τ = tclus at h_dom_τ htclus_spec hclus_def
    generalize sspClusters G w N h Φ ε X M Δ τ = clus at hclus_def hse_step_eq
    generalize hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X M
      (hseExpDistStepsOfTape (sspSlotPhases N) τ) = P at h_dom_τ ⊢

    have hclus_len : clus.length = tclus.length := by rw [hclus_def, List.length_map]
    have hclus_get : ∀ (idx : Fin clus.length),
        clus.get idx =
          ((tclus.get ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩).2.1,
           (tclus.get ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩).2.2) := by
      intro idx
      simp only [hclus_def, List.get_eq_getElem, List.getElem_map]
    have h_child_depth : ∀ t ∈ tclus, 2 ≤ t.2.1.card → 1 ≤ d ∧ Δ / 2 < 8 * (2 : ℝ) ^ (d - 1) := by
      intro t ht hcard2
      rcases Nat.eq_zero_or_pos d with rfl | hd_pos
      · exfalso
        have hΔ8 : Δ < 8 := by simpa using hΔ_depth
        have hcard1 := (htclus_spec.2.2.2.2 t ht).2.2.2.2.2.2 hΔ8
        omega
      · refine ⟨hd_pos, ?_⟩
        obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
        change Δ / 2 < 8 * (2 : ℝ) ^ d'
        rw [pow_succ] at hΔ_depth
        linarith

    by_cases hA : ∃ t ∈ tclus, u ∈ t.2.2 ∧ v ∈ t.2.2
    · rcases hA with ⟨t₀, ht₀_mem, hu₀, hv₀⟩
      obtain ⟨idx₀', hidx₀'_eq⟩ := List.mem_iff_get.mp ht₀_mem
      let idx₀ : Fin clus.length := ⟨idx₀'.1, lt_of_lt_of_eq idx₀'.2 hclus_len.symm⟩
      have hq₀ : idx₀.1 < N := lt_of_lt_of_le idx₀'.2 htclus_spec.2.1
      let q₀ : Fin N := ⟨idx₀.1, hq₀⟩
      have ht₀_props := htclus_spec.2.2.2.2 t₀ ht₀_mem
      have hu_X0 : u ∈ t₀.2.1 := (Finset.mem_inter.mp (ht₀_props.2.2.1 hu₀)).2
      have hv_X0 : v ∈ t₀.2.1 := (Finset.mem_inter.mp (ht₀_props.2.2.1 hv₀)).2

      have h_saved_eq : ∀ sub : Fin N → TreeTape N Φ ε d,
          savedRawDist (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)) u v =
          savedRawDist (hseRun G w N h Φ ε d t₀.2.1 t₀.2.2 (Δ / 2) (sub q₀)) u v := by
        intro sub
        let childRes : Fin clus.length → RawHST (Fin n) × Finset (Fin n) :=
          fun idx =>
            let c := clus.get idx
            if hq : idx.1 < N then
              hseRun G w N h Φ ε d c.1 c.2 (Δ / 2) (sub ⟨idx.1, hq⟩)
            else
              (RawHST.leaf c.1, c.2)
        have hres_eq : hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub) =
            (RawHST.node X Δ (List.ofFn (fun idx => (childRes idx).1)),
             Finset.univ.biUnion (fun idx => (childRes idx).2)) := hse_step_eq sub
        have hchild0_eq : childRes idx₀ =
            hseRun G w N h Φ ε d t₀.2.1 t₀.2.2 (Δ / 2) (sub q₀) := by
          have hc0 : clus.get idx₀ = (t₀.2.1, t₀.2.2) := by
            rw [hclus_get idx₀]
            have hfin : (⟨idx₀.1, lt_of_lt_of_eq idx₀.2 hclus_len⟩ : Fin tclus.length) = idx₀' := rfl
            rw [hfin, hidx₀'_eq]
          dsimp only [childRes]
          rw [dif_pos hq₀, hc0]
        have hchild_spec : ∀ idx : Fin clus.length,
            let idx' : Fin tclus.length := ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩
            (childRes idx).1.cluster = (tclus.get idx').2.1 ∧
            (childRes idx).2 ⊆ (tclus.get idx').2.2 := by
          intro idx
          let idx' : Fin tclus.length := ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩
          have hq : idx.1 < N := lt_of_lt_of_le idx'.2 htclus_spec.2.1
          have ht_mem : tclus.get idx' ∈ tclus := List.get_mem tclus idx'
          have ht_p := htclus_spec.2.2.2.2 (tclus.get idx') ht_mem
          have hc_run := h_hse.run_spec d (tclus.get idx').2.1 (tclus.get idx').2.2
            ht_p.1 (Finset.Subset.trans ht_p.2.2.1 Finset.inter_subset_right)
            (Δ / 2) (by linarith) ht_p.2.2.2.1 (h_child_depth _ ht_mem) (sub ⟨idx.1, hq⟩)
          have hcr_eq : childRes idx =
              hseRun G w N h Φ ε d (tclus.get idx').2.1 (tclus.get idx').2.2
                (Δ / 2) (sub ⟨idx.1, hq⟩) := by
            dsimp only [childRes]
            rw [dif_pos hq, hclus_get idx]
          rw [hcr_eq]
          exact ⟨hc_run.2.1, hc_run.2.2.2.1⟩
        have h_disj_idx : ∀ idx : Fin clus.length, idx ≠ idx₀ →
            Disjoint (tclus.get ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩).2.1 t₀.2.1 := by
          intro idx hne
          let idx' : Fin tclus.length := ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩
          have hne_val : idx'.1 ≠ idx₀'.1 := by
            intro heq
            exact hne (Fin.ext heq)
          have hp_get := List.pairwise_iff_get.mp htclus_spec.2.2.1
          have hmap_len : (tclus.map (fun t => t.2.1)).length = tclus.length := List.length_map _
          let i1 : Fin (tclus.map (fun t => t.2.1)).length :=
            ⟨idx'.1, lt_of_lt_of_eq idx'.2 hmap_len.symm⟩
          let i2 : Fin (tclus.map (fun t => t.2.1)).length :=
            ⟨idx₀'.1, lt_of_lt_of_eq idx₀'.2 hmap_len.symm⟩
          have hg1 : (tclus.map (fun t => t.2.1)).get i1 = (tclus.get idx').2.1 := by
            simp only [i1, idx', List.get_eq_getElem, List.getElem_map]
          have hg2 : (tclus.map (fun t => t.2.1)).get i2 = t₀.2.1 := by
            rw [← hidx₀'_eq]
            simp only [i2, List.get_eq_getElem, List.getElem_map]
          rcases lt_or_gt_of_ne hne_val with hlt | hgt
          · have h12 : i1 < i2 := hlt
            simpa only [hg1, hg2] using hp_get i1 i2 h12
          · have h21 : i2 < i1 := hgt
            have hdisj21 : Disjoint t₀.2.1 (tclus.get idx').2.1 := by
              simpa only [hg1, hg2] using hp_get i2 i1 h21
            exact hdisj21.symm
        have h_mem_iff : ∀ z : Fin n, z ∈ t₀.2.1 →
            (z ∈ Finset.univ.biUnion (fun idx => (childRes idx).2) ↔ z ∈ (childRes idx₀).2) := by
          intro z hz0
          rw [Finset.mem_biUnion]
          constructor
          · rintro ⟨idx, _, hz_idx⟩
            by_cases h_eq : idx = idx₀
            · subst h_eq; exact hz_idx
            · exfalso
              have ht_mem : tclus.get ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩ ∈ tclus :=
                List.get_mem _ _
              have hz_sub : z ∈ (tclus.get ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩).2.1 :=
                (Finset.mem_inter.mp ((htclus_spec.2.2.2.2 _ ht_mem).2.2.1
                  ((hchild_spec idx).2 hz_idx))).2
              exact Finset.disjoint_left.mp (h_disj_idx idx h_eq) hz_sub hz0
          · intro hz_idx0
            exact ⟨idx₀, Finset.mem_univ _, hz_idx0⟩
        have hvalid_node : ValidRawHST
            (RawHST.node X Δ (List.ofFn (fun idx => (childRes idx).1))) := by
          have hv1 := (h_parent_valid_and_dist sub).1
          rwa [hres_eq] at hv1
        have hp_children :
            ((List.ofFn (fun idx => (childRes idx).1)).map RawHST.cluster).Pairwise Disjoint :=
          hvalid_node.2.2.2.2.1
        have hc0_cluster : (childRes idx₀).1.cluster = t₀.2.1 := by
          rw [(hchild_spec idx₀).1]
          have hfin : (⟨idx₀.1, lt_of_lt_of_eq idx₀.2 hclus_len⟩ : Fin tclus.length) = idx₀' := rfl
          rw [hfin, hidx₀'_eq]
        have hu_c0 : u ∈ (childRes idx₀).1.cluster := by rwa [hc0_cluster]
        have hv_c0 : v ∈ (childRes idx₀).1.cluster := by rwa [hc0_cluster]
        have hdist_eq :
            (RawHST.node X Δ (List.ofFn (fun idx => (childRes idx).1))).dist u v =
            (childRes idx₀).1.dist u v := by
          simp only [RawHST.dist, huv, ↓reduceIte]
          exact h_dist_go u v Δ _ (childRes idx₀).1 hp_children
            (List.mem_ofFn.mpr ⟨idx₀, rfl⟩) hu_c0 hv_c0
        rw [hres_eq, ← hchild0_eq]
        simp only [savedRawDist, h_mem_iff u hu_X0, h_mem_iff v hv_X0, hdist_eq]

      simp_rw [h_saved_eq]
      rw [h_sub_marg d q₀
        (fun ω => savedRawDist (hseRun G w N h Φ ε d t₀.2.1 t₀.2.2 (Δ / 2) ω) u v)]
      have h_ih_0 := h_ih t₀.2.1 t₀.2.2 ht₀_props.1
        (Finset.Subset.trans ht₀_props.2.2.1 Finset.inter_subset_right)
        ht₀_props.2.2.2.1 (h_child_depth t₀ ht₀_mem) u hu_X0 v hv_X0
      refine le_trans h_ih_0 ?_
      have ht₀_card1 : (1 : ℝ) ≤ (t₀.2.1.card : ℝ) := by
        exact_mod_cast (Finset.one_le_card.mpr ht₀_props.1)
      have hI2 := h_dom_τ.2.2.1 t₀ ht₀_mem hu₀ hv₀
      by_cases ht1 : t₀.1 = 0
      · simp only [ht1, ↓reduceIte] at hI2
        have hsub_card : (t₀.2.1.card : ℝ) ≤ (X.card : ℝ) := by
          exact_mod_cast (Finset.card_le_card ht₀_props.2.1)
        exact le_trans
          (mul_le_mul_of_nonneg_right
            (h_exp_mono _ _ ht₀_card1 hsub_card (Δ / 2)).2 hd_uv_nn) hI2
      · have ht1_ge1 : 1 ≤ t₀.1 := by omega
        simp only [ht1, ↓reduceIte] at hI2
        have hmu_card : (t₀.2.1.card : ℝ) ≤ (X.card : ℝ) / (hstMu N t₀.1 : ℝ) :=
          ht₀_props.2.2.2.2.1 ht1_ge1
        exact le_trans
          (mul_le_mul_of_nonneg_right
            (h_exp_mono _ _ ht₀_card1 hmu_card (Δ / 2)).2 hd_uv_nn) hI2

    · by_cases hB : (∃ t₁ ∈ tclus, u ∈ t₁.2.2) ∧ (∃ t₂ ∈ tclus, v ∈ t₂.2.2)
      · have hI3 : Δ ≤ P := h_dom_τ.2.2.2 hB.1 hB.2 hA
        calc
          (∑ sub : Fin N → TreeTape N Φ ε d,
              (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) *
                savedRawDist (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)) u v)
            ≤ ∑ sub : Fin N → TreeTape N Φ ε d,
                (∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) * Δ := by
                refine Finset.sum_le_sum (fun sub _ => ?_)
                have hprod_nn : 0 ≤ ∏ q : Fin N, treeTapeProb N Φ ε d (sub q) :=
                  Finset.prod_nonneg (fun q _ => h_params.prob_nonneg d (sub q))
                have hsrd_le :
                    savedRawDist (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)) u v ≤ Δ := by
                  unfold savedRawDist
                  split_ifs
                  · exact (h_parent_valid_and_dist sub).2
                  · linarith
                exact mul_le_mul_of_nonneg_left hsrd_le hprod_nn
          _ = (∑ sub : Fin N → TreeTape N Φ ε d,
                ∏ q : Fin N, treeTapeProb N Φ ε d (sub q)) * Δ :=
                (Finset.sum_mul _ _ _).symm
          _ = Δ := by rw [h_sub_sum_one d, one_mul]
          _ ≤ P := hI3
      · have h_zero : ∀ sub : Fin N → TreeTape N Φ ε d,
            savedRawDist (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)) u v = 0 := by
          intro sub
          let childRes : Fin clus.length → RawHST (Fin n) × Finset (Fin n) :=
            fun idx =>
              let c := clus.get idx
              if hq : idx.1 < N then
                hseRun G w N h Φ ε d c.1 c.2 (Δ / 2) (sub ⟨idx.1, hq⟩)
              else
                (RawHST.leaf c.1, c.2)
          have hres2_eq : (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 =
              Finset.univ.biUnion (fun idx => (childRes idx).2) :=
            congrArg Prod.snd (hse_step_eq sub)
          have hnot_mem : ¬(u ∈ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2 ∧
              v ∈ (hseRun G w N h Φ ε (d + 1) X M Δ (τ, sub)).2) := by
            rintro ⟨hu_r, hv_r⟩
            rw [hres2_eq, Finset.mem_biUnion] at hu_r hv_r
            rcases hu_r with ⟨i1, _, hu_i1⟩
            rcases hv_r with ⟨i2, _, hv_i2⟩
            have h_sub_M : ∀ idx : Fin clus.length,
                (childRes idx).2 ⊆ (tclus.get ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩).2.2 := by
              intro idx
              let idx' : Fin tclus.length := ⟨idx.1, lt_of_lt_of_eq idx.2 hclus_len⟩
              have hq : idx.1 < N := lt_of_lt_of_le idx'.2 htclus_spec.2.1
              have ht_mem : tclus.get idx' ∈ tclus := List.get_mem tclus idx'
              have ht_p := htclus_spec.2.2.2.2 (tclus.get idx') ht_mem
              have hc_run := h_hse.run_spec d (tclus.get idx').2.1 (tclus.get idx').2.2
                ht_p.1 (Finset.Subset.trans ht_p.2.2.1 Finset.inter_subset_right)
                (Δ / 2) (by linarith) ht_p.2.2.2.1 (h_child_depth _ ht_mem) (sub ⟨idx.1, hq⟩)
              have hcr_eq : childRes idx =
                  hseRun G w N h Φ ε d (tclus.get idx').2.1 (tclus.get idx').2.2
                    (Δ / 2) (sub ⟨idx.1, hq⟩) := by
                dsimp only [childRes]
                rw [dif_pos hq, hclus_get idx]
              rw [hcr_eq]
              exact hc_run.2.2.2.1
            exact hB ⟨⟨_, List.get_mem tclus _, h_sub_M i1 hu_i1⟩,
                      ⟨_, List.get_mem tclus _, h_sub_M i2 hv_i2⟩⟩
          simp [savedRawDist, hnot_mem]
        simp only [h_zero, mul_zero, Finset.sum_const_zero]
        exact h_dom_τ.2.1

  
  have h_unnorm_sum :
      ∀ (X M : Finset (Fin n)), 2 ≤ X.card → M ⊆ X →
        ∀ (Δ : ℝ), 0 < Δ →
          (∀ x ∈ X, ∀ y ∈ X,
            hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) x y ≤
              ENNReal.ofReal Δ) →
          ∀ u ∈ X, ∀ v ∈ X, u ≠ v →
            ∀ (phases : List ℕ), (∀ r ∈ phases, 1 ≤ r ∧ r ≤ hstPhaseCount N) →
              ∀ (X_cur M_cur : Finset (Fin n)), X_cur ⊆ X → M_cur ⊆ X_cur →
                u ∈ M_cur → v ∈ M_cur →
                (∑ τ : Fin phases.length → Fin (hstRadiusSteps N Φ ε),
                  hseExpDistUnnormTape N Φ ε phases τ *
                    hseExpDistPenaltySteps G w N h Φ ε X.card Δ (hopDist G w h u v).toReal
                      u v X_cur M_cur (hseExpDistStepsOfTape phases τ)) ≤
                hseExpDistFactor N (X.card : ℝ) (Δ / 2) * (hopDist G w h u v).toReal := by
    intro X M hX2 hMX Δ hΔ_pos hΔ_diam u huX v hvX huv
    set k : ℕ := hstRadiusSteps N Φ ε
    have hk1 : 1 ≤ k := h_params.one_le_k
    set d_uv : ℝ := (hopDist G w h u v).toReal
    have hd_uv_ge2 : 2 ≤ d_uv := (h_ssp.hopDist_toReal_bounds u v huv).1
    have hd_uv_pos : 0 < d_uv := by linarith
    have hd_uv_nn : 0 ≤ d_uv := le_of_lt hd_uv_pos
    have hscale := h_ssp.scale_spec X M hX2 hMX Δ hΔ_pos hΔ_diam
    have hΔ_ge2 : 2 ≤ Δ := hscale.1
    have hX2_real : (2 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hX2
    set B₂ : ℝ := hseExpDistFactor N (X.card : ℝ) (Δ / 2) * d_uv
    have hB₂_nn : 0 ≤ B₂ :=
      mul_nonneg (h_exp_mono _ _ (by linarith) le_rfl (Δ / 2)).1 hd_uv_nn

    have h_geom_sum : ∀ r : ℕ, 1 ≤ r → r ≤ hstPhaseCount N →
        (∑ R ∈ Finset.range k, hseExpDistUnnormGeom N Φ ε r R) =
        1 - (1 - hstGeomP N Φ ε r) ^ k := by
      intro r hr1 hrL
      calc
        (∑ R ∈ Finset.range k, (1 - hstGeomP N Φ ε r) ^ R * hstGeomP N Φ ε r)
          = (∑ R ∈ Finset.range k, (1 - hstGeomP N Φ ε r) ^ R) *
              (1 - (1 - hstGeomP N Φ ε r)) := by
              rw [← Finset.sum_mul]; ring
        _ = 1 - (1 - hstGeomP N Φ ε r) ^ k := geom_sum_mul_neg _ k

    have h_tail_nn : ∀ (r_list : List ℕ), (∀ r ∈ r_list, 1 ≤ r ∧ r ≤ hstPhaseCount N) →
        ∀ τ' : Fin r_list.length → Fin k, 0 ≤ hseExpDistUnnormTape N Φ ε r_list τ' := by
      intro r_list hr_list τ'
      refine Finset.prod_nonneg (fun i _ => ?_)
      have hi := hr_list (r_list.get i) (List.get_mem r_list i)
      have hp := h_params.geomP_bounds _ hi.1 hi.2
      have h1p : 0 ≤ 1 - hstGeomP N Φ ε (r_list.get i) := by linarith [hp.2]
      exact mul_nonneg (pow_nonneg h1p _) (le_of_lt hp.1)

    have h_tail_sum_le1 : ∀ (r_list : List ℕ), (∀ r ∈ r_list, 1 ≤ r ∧ r ≤ hstPhaseCount N) →
        (∑ τ' : Fin r_list.length → Fin k, hseExpDistUnnormTape N Φ ε r_list τ') ≤ 1 := by
      intro r_list hr_list
      unfold hseExpDistUnnormTape
      rw [← Fintype.prod_sum
        (fun (i : Fin r_list.length) (R : Fin k) => hseExpDistUnnormGeom N Φ ε (r_list.get i) R.1)]
      refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
      · have hi := hr_list (r_list.get i) (List.get_mem r_list i)
        have hp := h_params.geomP_bounds _ hi.1 hi.2
        rw [Fin.sum_univ_eq_sum_range (fun R => hseExpDistUnnormGeom N Φ ε (r_list.get i) R) k,
            h_geom_sum _ hi.1 hi.2]
        have hpow_le1 : (1 - hstGeomP N Φ ε (r_list.get i)) ^ k ≤ 1 :=
          pow_le_one₀ (by linarith [hp.2]) (by linarith [hp.1])
        linarith
      · have hi := hr_list (r_list.get i) (List.get_mem r_list i)
        have hp := h_params.geomP_bounds _ hi.1 hi.2
        rw [Fin.sum_univ_eq_sum_range (fun R => hseExpDistUnnormGeom N Φ ε (r_list.get i) R) k,
            h_geom_sum _ hi.1 hi.2]
        have hpow_nn : 0 ≤ (1 - hstGeomP N Φ ε (r_list.get i)) ^ k :=
          pow_nonneg (by linarith [hp.2]) k
        linarith

    intro phases
    induction phases with
    | nil =>
      intro _ X_cur M_cur _ _ huM hvM
      change (∑ τ : Fin ([] : List ℕ).length → Fin k,
          hseExpDistUnnormTape N Φ ε [] τ *
            hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
              (hseExpDistStepsOfTape [] τ)) ≤ B₂
      let τ0 : Fin ([] : List ℕ).length → Fin k := fun i => Fin.elim0 i
      have h_uniq : ∀ τ : Fin ([] : List ℕ).length → Fin k, τ = τ0 := by
        intro τ; funext i; exact Fin.elim0 i
      have h_univ_eq : (Finset.univ : Finset (Fin ([] : List ℕ).length → Fin k)) = {τ0} := by
        ext τ
        exact ⟨fun _ => Finset.mem_singleton.mpr (h_uniq τ), fun _ => Finset.mem_univ τ⟩
      rw [h_univ_eq, Finset.sum_singleton]
      have hw0 : hseExpDistUnnormTape N Φ ε [] τ0 = 1 := by simp [hseExpDistUnnormTape]
      have hs0 : hseExpDistStepsOfTape ([] : List ℕ) τ0 = [] := by simp [hseExpDistStepsOfTape]
      rw [hw0, hs0, one_mul]
      simp [hseExpDistPenaltySteps, huM, hvM, B₂, d_uv]
    | cons ℓ rest ih_ph =>
      intro hph X_cur M_cur hX_cur hM_cur huM hvM
      have hℓ : 1 ≤ ℓ ∧ ℓ ≤ hstPhaseCount N := hph ℓ List.mem_cons_self
      have hrest : ∀ r ∈ rest, 1 ≤ r ∧ r ≤ hstPhaseCount N :=
        fun r hr => hph r (List.mem_cons_of_mem _ hr)
      let F_tau : (Fin (rest.length + 1) → Fin k) → ℝ :=
        fun τ =>
          hseExpDistUnnormTape N Φ ε (ℓ :: rest) τ *
            hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
              (hseExpDistStepsOfTape (ℓ :: rest) τ)
      change (∑ τ : Fin (rest.length + 1) → Fin k, F_tau τ) ≤ B₂
      let e_cons := Fin.consEquiv (fun _ : Fin (rest.length + 1) => Fin k)
      rw [← Fintype.sum_equiv e_cons (fun p => F_tau (e_cons p)) F_tau (fun _ => rfl),
          Fintype.sum_prod_type]
      let val : ℕ → ℝ :=
        fun R =>
          ∑ τ' : Fin rest.length → Fin k,
            hseExpDistUnnormTape N Φ ε rest τ' *
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                ((ℓ, R) :: hseExpDistStepsOfTape rest τ')
      have h_factor_cons : ∀ (r0 : Fin k) (τ' : Fin rest.length → Fin k),
          F_tau (e_cons (r0, τ')) =
          hseExpDistUnnormGeom N Φ ε ℓ r0.1 *
            (hseExpDistUnnormTape N Φ ε rest τ' *
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                ((ℓ, r0.1) :: hseExpDistStepsOfTape rest τ')) := by
        intro r0 τ'
        let τ_cons : Fin (rest.length + 1) → Fin k := @Fin.cons rest.length (fun _ => Fin k) r0 τ'
        have he_apply : e_cons (r0, τ') = τ_cons := rfl
        have hw_cons :
            hseExpDistUnnormTape N Φ ε (ℓ :: rest) τ_cons =
            hseExpDistUnnormGeom N Φ ε ℓ r0.1 * hseExpDistUnnormTape N Φ ε rest τ' := by
          unfold hseExpDistUnnormTape
          change (∏ i : Fin (rest.length + 1),
              hseExpDistUnnormGeom N Φ ε ((ℓ :: rest).get i) (τ_cons i).1) = _
          rw [Fin.prod_univ_succ]
          congr 1
        have hs_cons :
            hseExpDistStepsOfTape (ℓ :: rest) τ_cons =
            (ℓ, r0.1) :: hseExpDistStepsOfTape rest τ' := by
          unfold hseExpDistStepsOfTape
          change List.ofFn (fun i : Fin (rest.length + 1) =>
              ((ℓ :: rest).get i, (τ_cons i).1)) = _
          rw [List.ofFn_succ]
          congr 1
        dsimp only [F_tau]
        rw [he_apply, hw_cons, hs_cons, mul_assoc]
      have h_sum_val :
          (∑ r0 : Fin k, ∑ τ' : Fin rest.length → Fin k, F_tau (e_cons (r0, τ'))) =
          ∑ R ∈ Finset.range k, ((1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ) * val R := by
        have h1 : ∀ r0 : Fin k,
            (∑ τ' : Fin rest.length → Fin k, F_tau (e_cons (r0, τ'))) =
            hseExpDistUnnormGeom N Φ ε ℓ r0.1 * val r0.1 := by
          intro r0
          simp_rw [h_factor_cons r0]
          exact (Finset.mul_sum _ _ _).symm
        simp_rw [h1]
        rw [Fin.sum_univ_eq_sum_range (fun R => hseExpDistUnnormGeom N Φ ε ℓ R * val R) k]
        rfl
      rw [h_sum_val]

      set cands := sspCands G w N h Φ ε Δ X.card X_cur ℓ
      have hp_bounds := h_params.geomP_bounds ℓ hℓ.1 hℓ.2
      by_cases hc : cands.Nonempty
      · set x := cands.min' hc
        have hx_cands : x ∈ cands := Finset.min'_mem cands hc
        simp only [cands, sspCands, Finset.mem_filter] at hx_cands
        have hx_cur : x ∈ X_cur := hx_cands.1
        have hx_upper :
            ((hstBall G w N h Φ ε Δ X_cur x ℓ (k : ℤ)).card : ℝ) ≤
            (X.card : ℝ) / (hstMu N ℓ : ℝ) := hx_cands.2.2
        have hball_spec := hscale.2.2 X_cur hX_cur x hx_cur ℓ hℓ.1 hℓ.2
        have hx_in_k : x ∈ hstBall G w N h Φ ε Δ X_cur x ℓ (k : ℤ) :=
          hball_spec.2.1 0 (k : ℤ) (by positivity) hball_spec.1
        have h_ratio1 : 1 ≤ (X.card : ℝ) / (hstMu N ℓ : ℝ) := by
          have hcard1 : 1 ≤ (hstBall G w N h Φ ε Δ X_cur x ℓ (k : ℤ)).card :=
            Finset.one_le_card.mpr ⟨x, hx_in_k⟩
          have hcard1_real : (1 : ℝ) ≤ ((hstBall G w N h Φ ε Δ X_cur x ℓ (k : ℤ)).card : ℝ) := by
            exact_mod_cast hcard1
          linarith
        rcases hball_spec.2.2 with ⟨ρ, hρ_mem, hρ_lip⟩
        have hu_cur : u ∈ X_cur := hM_cur huM
        have hv_cur : v ∈ X_cur := hM_cur hvM
        set q_ℓ : ℝ := hstStep N Φ ε Δ ℓ
        have hq_pos : 0 < q_ℓ := ((h_params.radius_bounds Δ hΔ_pos).2.2 ℓ hℓ.1 hℓ.2).2.1
        set G_child : ℝ := hseExpDistFactor N ((X.card : ℝ) / (hstMu N ℓ : ℝ)) (Δ / 2) * d_uv
        have hG_nn : 0 ≤ G_child :=
          mul_nonneg (h_exp_mono _ _ h_ratio1 le_rfl (Δ / 2)).1 hd_uv_nn
        have h_contr : G_child + (d_uv / q_ℓ) * hstGeomP N Φ ε ℓ * Δ ≤ B₂ :=
          h_slot_contraction (X.card : ℝ) Δ d_uv hX2_real hΔ_ge2 hd_uv_nn ℓ hℓ.1 hℓ.2
        set ρ_a : ℤ := min (ρ u) (ρ v)
        set ρ_b : ℤ := max (ρ u) (ρ v)
        have hρ_ab_le : ρ_a ≤ ρ_b := min_le_max
        have hlip_uv : ρ v ≤ ρ u + (Nat.ceil (d_uv / q_ℓ) : ℤ) := hρ_lip u hu_cur v hv_cur huv
        have hlip_vu : ρ u ≤ ρ v + (Nat.ceil (d_uv / q_ℓ) : ℤ) := by
          have := hρ_lip v hv_cur u hu_cur huv.symm
          rwa [h_hop_comm h v u] at this
        have hρ_ab_lip : ρ_b ≤ ρ_a + (Nat.ceil (d_uv / q_ℓ) : ℤ) := by omega

        have h_mem_Mj : ∀ (z : Fin n) (R : ℕ), z ∈ M_cur →
            (z ∈ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) - 1) ∩ M_cur ↔ ρ z ≤ (R : ℤ) - 1) := by
          intro z R hzM
          rw [Finset.mem_inter, hρ_mem z (hM_cur hzM) ((R : ℤ) - 1)]
          exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, hzM⟩⟩
        have h_mem_Mnext : ∀ (z : Fin n) (R : ℕ), z ∈ M_cur →
            (z ∈ M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1) ↔ ¬(ρ z ≤ (R : ℤ) + 1)) := by
          intro z R hzM
          rw [Finset.mem_sdiff, hρ_mem z (hM_cur hzM) ((R : ℤ) + 1)]
          exact ⟨fun h1 => h1.2, fun h1 => ⟨hzM, h1⟩⟩

        refine h_single_slot k hk1 (hstGeomP N Φ ε ℓ) d_uv q_ℓ Δ G_child B₂
          hp_bounds.1 hp_bounds.2 hd_uv_pos hq_pos (by linarith) hG_nn h_contr
          ρ_a ρ_b hρ_ab_le hρ_ab_lip val ?_ ?_ ?_ ?_
        · 
          intro R _ hR_lt
          have hu_j : ¬(ρ u ≤ (R : ℤ) - 1) := by omega
          have hv_j : ¬(ρ v ≤ (R : ℤ) - 1) := by omega
          have hu_n : ¬(ρ u ≤ (R : ℤ) + 1) := by omega
          have hv_n : ¬(ρ v ≤ (R : ℤ) + 1) := by omega
          set Xj := hstBall G w N h Φ ε Δ X_cur x ℓ (R : ℤ)
          set M_next := M_cur \ hstBall G w N h Φ ε Δ X_cur x ℓ ((R : ℤ) + 1)
          have hpen_eq : ∀ τ' : Fin rest.length → Fin k,
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                ((ℓ, R) :: hseExpDistStepsOfTape rest τ') =
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v (X_cur \ Xj) M_next
                (hseExpDistStepsOfTape rest τ') := by
            intro τ'
            simp only [hseExpDistPenaltySteps,
              show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl, dif_pos hc,
              show cands.min' hc = x from rfl,
              h_mem_Mj u R huM, h_mem_Mj v R hvM, h_mem_Mnext u R huM, h_mem_Mnext v R hvM,
              hu_j, hv_j, hu_n, hv_n]
            simp [Xj, M_next]
          have hval_eq : val R =
              ∑ τ' : Fin rest.length → Fin k,
                hseExpDistUnnormTape N Φ ε rest τ' *
                  hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v (X_cur \ Xj) M_next
                    (hseExpDistStepsOfTape rest τ') := by
            dsimp only [val]
            refine Finset.sum_congr rfl (fun τ' _ => ?_)
            rw [hpen_eq τ']
          rw [hval_eq]
          have hMnext_sub : M_next ⊆ X_cur \ Xj := by
            intro z hz
            rw [Finset.mem_sdiff] at hz ⊢
            exact ⟨hM_cur hz.1, fun hzXj => hz.2 (hball_spec.2.1 (R : ℤ) ((R : ℤ) + 1) (by omega) hzXj)⟩
          exact ih_ph hrest (X_cur \ Xj) M_next
            (Finset.Subset.trans Finset.sdiff_subset hX_cur) hMnext_sub
            ((h_mem_Mnext u R huM).mpr hu_n) ((h_mem_Mnext v R hvM).mpr hv_n)
        · 
          intro R _ hR_gt
          have hu_j : ρ u ≤ (R : ℤ) - 1 := by omega
          have hv_j : ρ v ≤ (R : ℤ) - 1 := by omega
          have hpen_eq : ∀ τ' : Fin rest.length → Fin k,
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                ((ℓ, R) :: hseExpDistStepsOfTape rest τ') = G_child := by
            intro τ'
            simp only [hseExpDistPenaltySteps,
              show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl, dif_pos hc,
              show cands.min' hc = x from rfl,
              h_mem_Mj u R huM, h_mem_Mj v R hvM, hu_j, hv_j, and_self, ↓reduceIte, G_child]
          have hval_eq : val R =
              (∑ τ' : Fin rest.length → Fin k, hseExpDistUnnormTape N Φ ε rest τ') * G_child := by
            dsimp only [val]
            simp_rw [hpen_eq]
            exact (Finset.sum_mul _ _ _).symm
          rw [hval_eq]
          exact le_trans (mul_le_mul_of_nonneg_right (h_tail_sum_le1 rest hrest) hG_nn) (one_mul _).le
        · 
          intro R _ hR_lo hR_hi
          have h_split :
              (ρ u ≤ (R : ℤ) - 1 ∧ ¬(ρ v ≤ (R : ℤ) - 1) ∧ ¬(ρ v ≤ (R : ℤ) + 1)) ∨
              (ρ v ≤ (R : ℤ) - 1 ∧ ¬(ρ u ≤ (R : ℤ) - 1) ∧ ¬(ρ u ≤ (R : ℤ) + 1)) := by omega
          have hpen_eq : ∀ τ' : Fin rest.length → Fin k,
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                ((ℓ, R) :: hseExpDistStepsOfTape rest τ') = Δ := by
            intro τ'
            simp only [hseExpDistPenaltySteps,
              show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl, dif_pos hc,
              show cands.min' hc = x from rfl,
              h_mem_Mj u R huM, h_mem_Mj v R hvM, h_mem_Mnext u R huM, h_mem_Mnext v R hvM]
            rcases h_split with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp [h1, h2, h3]
          have hval_eq : val R =
              (∑ τ' : Fin rest.length → Fin k, hseExpDistUnnormTape N Φ ε rest τ') * Δ := by
            dsimp only [val]
            simp_rw [hpen_eq]
            exact (Finset.sum_mul _ _ _).symm
          rw [hval_eq]
          exact le_trans (mul_le_mul_of_nonneg_right (h_tail_sum_le1 rest hrest) (by linarith))
            (one_mul _).le
        · 
          intro R _ hR_pad
          have h_ann :
              (¬(ρ u ≤ (R : ℤ) - 1) ∧ ρ u ≤ (R : ℤ) + 1) ∨
              (¬(ρ v ≤ (R : ℤ) - 1) ∧ ρ v ≤ (R : ℤ) + 1) := by omega
          have hpen_eq : ∀ τ' : Fin rest.length → Fin k,
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                ((ℓ, R) :: hseExpDistStepsOfTape rest τ') = 0 := by
            intro τ'
            simp only [hseExpDistPenaltySteps,
              show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl, dif_pos hc,
              show cands.min' hc = x from rfl,
              h_mem_Mj u R huM, h_mem_Mj v R hvM, h_mem_Mnext u R huM, h_mem_Mnext v R hvM]
            rcases h_ann with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
          dsimp only [val]
          simp [hpen_eq]
      · 
        have hval_le : ∀ R ∈ Finset.range k, val R ≤ B₂ := by
          intro R _
          have hpen_eq : ∀ τ' : Fin rest.length → Fin k,
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                ((ℓ, R) :: hseExpDistStepsOfTape rest τ') =
              hseExpDistPenaltySteps G w N h Φ ε X.card Δ d_uv u v X_cur M_cur
                (hseExpDistStepsOfTape rest τ') := by
            intro τ'
            simp [hseExpDistPenaltySteps,
              show sspCands G w N h Φ ε Δ X.card X_cur ℓ = cands from rfl, dif_neg hc]
          dsimp only [val]
          simp_rw [hpen_eq]
          exact ih_ph hrest X_cur M_cur hX_cur hM_cur huM hvM
        have h1p_nn : 0 ≤ 1 - hstGeomP N Φ ε ℓ := by linarith [hp_bounds.2]
        calc
          (∑ R ∈ Finset.range k, ((1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ) * val R)
            ≤ ∑ R ∈ Finset.range k, ((1 - hstGeomP N Φ ε ℓ) ^ R * hstGeomP N Φ ε ℓ) * B₂ := by
                refine Finset.sum_le_sum (fun R hR => ?_)
                exact mul_le_mul_of_nonneg_left (hval_le R hR)
                  (mul_nonneg (pow_nonneg h1p_nn R) (le_of_lt hp_bounds.1))
          _ = (1 - (1 - hstGeomP N Φ ε ℓ) ^ k) * B₂ := by
                rw [← Finset.sum_mul]
                exact congrArg (· * B₂) (h_geom_sum ℓ hℓ.1 hℓ.2)
          _ ≤ B₂ := by nlinarith [pow_nonneg h1p_nn k, hB₂_nn]

  
  have h_depth_ind :
      ∀ (d : ℕ) (X M : Finset (Fin n)), X.Nonempty → M ⊆ X →
        ∀ (Δ : ℝ), 0 < Δ →
          (∀ x ∈ X, ∀ y ∈ X,
            hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) x y ≤
              ENNReal.ofReal Δ) →
          (2 ≤ X.card → 1 ≤ d ∧ Δ < 8 * (2 : ℝ) ^ (d - 1)) →
          ∀ u ∈ X, ∀ v ∈ X,
            (∑ ω : TreeTape N Φ ε d,
              treeTapeProb N Φ ε d ω *
                savedRawDist (hseRun G w N h Φ ε d X M Δ ω) u v) ≤
            hseExpDistFactor N (X.card : ℝ) Δ * (hopDist G w h u v).toReal := by
    intro d
    induction d with
    | zero =>
      intro X M hX_ne hMX Δ hΔ_pos hΔ_diam h_depth u huX v hvX
      have hX1 : (1 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast (Finset.one_le_card.mpr hX_ne)
      have hrhs_nn : 0 ≤ hseExpDistFactor N (X.card : ℝ) Δ * (hopDist G w h u v).toReal :=
        mul_nonneg (h_exp_mono _ _ hX1 le_rfl Δ).1 ENNReal.toReal_nonneg
      by_cases huv : u = v
      · subst huv
        have h_self : ∀ t : RawHST (Fin n), t.dist u u = 0 := fun t => by
          cases t <;> simp [RawHST.dist]
        simp [savedRawDist, h_self, hrhs_nn]
      · exfalso
        have hX2 : 2 ≤ X.card := Finset.one_lt_card_iff.mpr ⟨u, v, huX, hvX, huv⟩
        have := (h_depth hX2).1
        omega
    | succ d' ih_d =>
      intro X M hX_ne hMX Δ hΔ_pos hΔ_diam h_depth u huX v hvX
      have hX1 : (1 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast (Finset.one_le_card.mpr hX_ne)
      have hrhs_nn : 0 ≤ hseExpDistFactor N (X.card : ℝ) Δ * (hopDist G w h u v).toReal :=
        mul_nonneg (h_exp_mono _ _ hX1 le_rfl Δ).1 ENNReal.toReal_nonneg
      by_cases huv : u = v
      · subst huv
        have h_self : ∀ t : RawHST (Fin n), t.dist u u = 0 := fun t => by
          cases t <;> simp [RawHST.dist]
        simp [savedRawDist, h_self, hrhs_nn]
      · by_cases huvM : u ∈ M ∧ v ∈ M
        · have hX2 : 2 ≤ X.card := Finset.one_lt_card_iff.mpr ⟨u, v, huX, hvX, huv⟩
          have hΔ_lt : Δ < 8 * (2 : ℝ) ^ d' := (h_depth hX2).2
          have h_prod_split :
              (∑ ω : TreeTape N Φ ε (d' + 1),
                treeTapeProb N Φ ε (d' + 1) ω *
                  savedRawDist (hseRun G w N h Φ ε (d' + 1) X M Δ ω) u v) =
              ∑ τ : FinTape N Φ ε,
                finTapeProb N Φ ε τ *
                  (∑ sub : Fin N → TreeTape N Φ ε d',
                    (∏ q : Fin N, treeTapeProb N Φ ε d' (sub q)) *
                      savedRawDist (hseRun G w N h Φ ε (d' + 1) X M Δ (τ, sub)) u v) := by
            change (∑ ω : FinTape N Φ ε × (Fin N → TreeTape N Φ ε d'), _) = _
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl (fun τ _ => ?_)
            simp only [treeTapeProb, mul_assoc]
            exact (Finset.mul_sum _ _ _).symm
          rw [h_prod_split]
          set Z_tot : ℝ := ∏ i : Fin (hstTotalSlots N),
            (1 - (1 - hstGeomP N Φ ε ((sspSlotPhases N).get i)) ^ hstRadiusSteps N Φ ε)
          have h_ftp_nn : ∀ τ : FinTape N Φ ε, 0 ≤ finTapeProb N Φ ε τ := by
            intro τ
            simpa [treeTapeProb] using h_params.prob_nonneg 1 (τ, fun _ => PUnit.unit)
          have h_ftp_div : ∀ τ : FinTape N Φ ε,
              finTapeProb N Φ ε τ = hseExpDistUnnormTape N Φ ε (sspSlotPhases N) τ / Z_tot := by
            intro τ
            unfold finTapeProb truncGeomWeight hseExpDistUnnormTape hseExpDistUnnormGeom
              Z_tot hstTotalSlots
            rw [Finset.prod_div_distrib]
          have h_step1 :
              (∑ τ : FinTape N Φ ε,
                finTapeProb N Φ ε τ *
                  (∑ sub : Fin N → TreeTape N Φ ε d',
                    (∏ q : Fin N, treeTapeProb N Φ ε d' (sub q)) *
                      savedRawDist (hseRun G w N h Φ ε (d' + 1) X M Δ (τ, sub)) u v)) ≤
              (∑ τ : FinTape N Φ ε,
                hseExpDistUnnormTape N Φ ε (sspSlotPhases N) τ *
                  hseExpDistPenaltySteps G w N h Φ ε X.card Δ (hopDist G w h u v).toReal
                    u v X M (hseExpDistStepsOfTape (sspSlotPhases N) τ)) / Z_tot := by
            calc
              _ ≤ ∑ τ : FinTape N Φ ε,
                    finTapeProb N Φ ε τ *
                      hseExpDistPenaltySteps G w N h Φ ε X.card Δ (hopDist G w h u v).toReal
                        u v X M (hseExpDistStepsOfTape (sspSlotPhases N) τ) := by
                  refine Finset.sum_le_sum (fun τ _ => ?_)
                  exact mul_le_mul_of_nonneg_left
                    (h_level_step d' X M hX2 hMX Δ hΔ_pos hΔ_diam hΔ_lt
                      (fun Xq Mq hXq_ne hMq hXq_diam hXq_depth =>
                        ih_d Xq Mq hXq_ne hMq (Δ / 2) (by linarith) hXq_diam hXq_depth)
                      u huvM.1 v huvM.2 huv τ)
                    (h_ftp_nn τ)
              _ = ∑ τ : FinTape N Φ ε,
                    (hseExpDistUnnormTape N Φ ε (sspSlotPhases N) τ *
                      hseExpDistPenaltySteps G w N h Φ ε X.card Δ (hopDist G w h u v).toReal
                        u v X M (hseExpDistStepsOfTape (sspSlotPhases N) τ)) / Z_tot := by
                  refine Finset.sum_congr rfl (fun τ _ => ?_)
                  rw [h_ftp_div τ, div_mul_eq_mul_div]
              _ = _ := (Finset.sum_div _ _ _).symm
          refine le_trans h_step1 ?_
          have h_num_le :=
            h_unnorm_sum X M hX2 hMX Δ hΔ_pos hΔ_diam u huX v hvX huv
              (sspSlotPhases N) (fun r hr => h_params.slot_phases_bounds r hr)
              X M (Finset.Subset.refl X) hMX huvM.1 huvM.2
          exact h_norm_rescale (X.card : ℝ) Δ (hopDist G w h u v).toReal _
            hX1 hΔ_pos ENNReal.toReal_nonneg h_num_le
        · have h_zero : ∀ ω : TreeTape N Φ ε (d' + 1),
              savedRawDist (hseRun G w N h Φ ε (d' + 1) X M Δ ω) u v = 0 := by
            intro ω
            have hsubM :=
              (h_hse.run_spec (d' + 1) X M hX_ne hMX Δ hΔ_pos hΔ_diam h_depth ω).2.2.2.1
            have hnot : ¬(u ∈ (hseRun G w N h Φ ε (d' + 1) X M Δ ω).2 ∧
                v ∈ (hseRun G w N h Φ ε (d' + 1) X M Δ ω).2) :=
              fun ⟨hu_r, hv_r⟩ => huvM ⟨hsubM hu_r, hsubM hv_r⟩
            simp [savedRawDist, hnot]
          simp only [h_zero, mul_zero, Finset.sum_const_zero]
          exact hrhs_nn

  
  intro u v
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hΦ_pos : 0 < Φ := by linarith
  have hβ_diam : ∀ x ∈ (Finset.univ : Finset (Fin n)), ∀ y ∈ (Finset.univ : Finset (Fin n)),
      hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) x y ≤
        ENNReal.ofReal Φ := by
    intro x _ y _
    have h_mono :
        hopDist G w (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h) x y ≤
          hopDist G w h x y := by
      simp only [hopDist]
      refine le_iInf₂ (fun p hp_len => ?_)
      have h_le : h ≤ 2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1) * h :=
        Nat.le_mul_of_pos_left h (lt_of_lt_of_le Nat.zero_lt_one h_params.one_le_beta)
      exact iInf_le_of_le p (iInf_le_of_le (le_trans hp_len h_le) le_rfl)
    exact le_trans h_mono (hΦ_diam x y)
  have h_root := h_depth_ind (hstDepth Φ) Finset.univ Finset.univ huniv_ne
    (Finset.Subset.refl _) Φ hΦ_pos hβ_diam
    (fun _ => ⟨h_params.one_le_depth, h_params.diam_lt_depth⟩)
    u (Finset.mem_univ u) v (Finset.mem_univ v)
  have huniv_card : ((Finset.univ : Finset (Fin n)).card : ℝ) = (n : ℝ) := by simp
  rw [huniv_card] at h_root
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact_mod_cast this
  have hnN_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have h_mono_N :
      hseExpDistFactor N (n : ℝ) Φ * (hopDist G w h u v).toReal ≤
      (256 * (hstPhaseCount N : ℝ) * Real.logb 2 (N : ℝ) *
        (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Φ)) * (hopDist G w h u v).toReal := by
    change hseExpDistFactor N (n : ℝ) Φ * (hopDist G w h u v).toReal ≤
      hseExpDistFactor N (N : ℝ) Φ * (hopDist G w h u v).toReal
    exact mul_le_mul_of_nonneg_right
      (h_exp_mono (n : ℝ) (N : ℝ) hn1 hnN_real Φ).2 ENNReal.toReal_nonneg
  exact le_trans h_root h_mono_N

theorem finite_diam_hc_ramsey_hst (N : ℕ) (V : Type) [Fintype V]
    (hV : 2 ≤ Fintype.card V) (hN : Fintype.card V ≤ N)
    (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e ∈ G.edgeSet, 2 ≤ w e)
    (h : ℕ) (hh : 1 ≤ h)
    (Φ : ℝ) (hΦ_ge : 2 ≤ Φ)
    (hΦ_diam : ∀ u v : V, hopDist G w h u v ≤ ENNReal.ofReal Φ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ D : PMF (HST V × Set V),
      IsStochasticHCRamseyHSTEmbedding G w h ε
        (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1))
        (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ))
        (256 * (hstPhaseCount N : ℝ) * Real.logb 2 (N : ℝ) *
          (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Φ))
        D :=
by
  classical
  set n := Fintype.card V
  have hN2 : 2 ≤ N := le_trans hV hN
  let e : V ≃ Fin n := Fintype.equivFin V
  let G' : SimpleGraph (Fin n) :=
    { Adj := fun i j => G.Adj (e.symm i) (e.symm j)
      symm := fun _ _ hadj => G.symm hadj
      loopless := fun i hadj => G.loopless (e.symm i) hadj }
  let w' : Sym2 (Fin n) → ℝ := fun s => w (Sym2.map e.symm s)
  let hom : G →g G' :=
    { toFun := e
      map_rel' := by
        intro a b hab
        change G.Adj (e.symm (e a)) (e.symm (e b))
        simpa only [Equiv.symm_apply_apply] using hab }
  let homInv : G' →g G :=
    { toFun := e.symm
      map_rel' := fun {_ _} hab => hab }
  have h_walk_to : ∀ {u v : V} (p : G.Walk u v),
      walkWeight w' (p.map hom) = walkWeight w p := by
    intro u v p
    simp only [walkWeight, SimpleGraph.Walk.edges_map, List.map_map]
    congr 1
    refine List.map_congr_left (fun s _ => ?_)
    induction s using Sym2.ind with
    | _ a b =>
      simp [w', hom]
  have h_walk_from : ∀ {u v : V} (q : G'.Walk (e u) (e v)),
      walkWeight w ((q.map homInv).copy (e.symm_apply_apply u) (e.symm_apply_apply v)) =
        walkWeight w' q := by
    intro u v q
    simp only [walkWeight, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map, List.map_map]
    rfl
  have h_hop_eq : ∀ (H : ℕ) (u v : V), hopDist G' w' H (e u) (e v) = hopDist G w H u v := by
    intro H u v
    simp only [hopDist]
    apply le_antisymm
    · refine le_iInf₂ (fun p hp => ?_)
      have hlen : (p.map hom).length ≤ H := by
        simpa only [SimpleGraph.Walk.length_map] using hp
      refine le_trans (iInf₂_le (p.map hom) hlen) ?_
      rw [h_walk_to]
    · refine le_iInf₂ (fun q hq => ?_)
      let p : G.Walk u v := (q.map homInv).copy (e.symm_apply_apply u) (e.symm_apply_apply v)
      have hlen : p.length ≤ H := by
        simpa only [p, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map] using hq
      refine le_trans (iInf₂_le p hlen) ?_
      rw [h_walk_from]
  have hw' : ∀ s ∈ G'.edgeSet, 2 ≤ w' s := by
    intro s hs
    induction s using Sym2.ind with
    | _ i j =>
      have hadj : G.Adj (e.symm i) (e.symm j) := by
        simpa [SimpleGraph.mem_edgeSet] using hs
      have hmem : s(e.symm i, e.symm j) ∈ G.edgeSet := by
        simpa [SimpleGraph.mem_edgeSet] using hadj
      simpa [w'] using hw _ hmem
  have hΦ_diam' : ∀ i j : Fin n, hopDist G' w' h i j ≤ ENNReal.ofReal Φ := by
    intro i j
    have h1 := h_hop_eq h (e.symm i) (e.symm j)
    simp only [Equiv.apply_symm_apply] at h1
    rw [h1]
    exact hΦ_diam (e.symm i) (e.symm j)
  have hp : HSTParamSpec N Φ ε := hst_param_bounds N hN2 Φ hΦ_ge ε hε_pos hε_lt
  obtain ⟨hssp, hhse⟩ :=
    ssp_and_hse_deterministic N n hV hN G' w' hw' h hh Φ hΦ_ge hΦ_diam' ε hε_pos hε_lt hp
  have hexcl :=
    hse_exclusion_prob_bound N n hV hN G' w' hw' h hh Φ hΦ_ge hΦ_diam' ε hε_pos hε_lt hp hssp hhse
  have hexp :=
    hse_expected_distortion_bound N n hV hN G' w' hw' h hh Φ hΦ_ge hΦ_diam' ε hε_pos hε_lt
      hp hssp hhse
  set L := hstPhaseCount N
  set δ := hstTruncDelta N
  set k := hstRadiusSteps N Φ ε
  set β := 2 * k * (L + 1)
  set K := 8 * (k : ℝ) * (L : ℝ)
  set α := 256 * (L : ℝ) * Real.logb 2 (N : ℝ) * (1 + 2 * δ) ^ (Real.logb 2 Φ)
  set d₀ := hstDepth Φ
  have hβ_ge : 1 ≤ β := hp.one_le_beta
  have hK_ge : 1 ≤ K := hp.one_le_K
  have hα_ge : 1 ≤ α := hp.one_le_alpha
  have hd₀_ge : 1 ≤ d₀ := hp.one_le_depth
  have hΦ_lt_d₀ : Φ < 8 * (2 : ℝ) ^ (d₀ - 1) := hp.diam_lt_depth
  have hprob_nonneg : ∀ ω : TreeTape N Φ ε d₀, 0 ≤ treeTapeProb N Φ ε d₀ ω := hp.prob_nonneg d₀
  have hprob_sum : (∑ ω : TreeTape N Φ ε d₀, treeTapeProb N Φ ε d₀ ω) = 1 := hp.prob_sum d₀
  have huniv_ne : (Finset.univ : Finset (Fin n)).Nonempty := by
    have hn_pos : 0 < n := by omega
    exact ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  have hΦ_pos : 0 < Φ := by linarith
  have hβ_diam' : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      hopDist G' w' (β * h) i j ≤ ENNReal.ofReal Φ := by
    intro i _ j _
    have h_mono : hopDist G' w' (β * h) i j ≤ hopDist G' w' h i j := by
      simp only [hopDist]
      refine le_iInf₂ (fun p hp_len => ?_)
      have h_le : h ≤ β * h := Nat.le_mul_of_pos_left h (by omega)
      exact iInf_le_of_le p (iInf_le_of_le (le_trans hp_len h_le) le_rfl)
    exact le_trans h_mono (hΦ_diam' i j)
  have h_root_inv :=
    hhse.run_spec d₀ Finset.univ Finset.univ huniv_ne (Finset.Subset.refl _) Φ hΦ_pos hβ_diam'
      (fun _ => ⟨hd₀_ge, hΦ_lt_d₀⟩)
  let res : TreeTape N Φ ε d₀ → RawHST (Fin n) × Finset (Fin n) :=
    fun ω => hseRun G' w' N h Φ ε d₀ Finset.univ Finset.univ Φ ω
  have h_ex_U' : ∀ ω : TreeTape N Φ ε d₀, ∃ U' : HST (Fin n),
      U'.label U'.root = ENNReal.ofReal (res ω).1.topLabel ∧
      ∀ i j : Fin n, U'.dist i j = ENNReal.ofReal ((res ω).1.dist i j) := by
    intro ω
    exact exists_hst_of_valid_raw_hst (Fin n) (res ω).1 (h_root_inv ω).1 (h_root_inv ω).2.1
  let U' : TreeTape N Φ ε d₀ → HST (Fin n) := fun ω => Classical.choose (h_ex_U' ω)
  have hU'_dist : ∀ (ω : TreeTape N Φ ε d₀) (i j : Fin n),
      (U' ω).dist i j = ENNReal.ofReal ((res ω).1.dist i j) :=
    fun ω => (Classical.choose_spec (h_ex_U' ω)).2
  let U : TreeTape N Φ ε d₀ → HST V :=
    fun ω => { U' ω with leafEquiv := e.trans (U' ω).leafEquiv }
  have hU_dist : ∀ (ω : TreeTape N Φ ε d₀) (u v : V),
      (U ω).dist u v = ENNReal.ofReal ((res ω).1.dist (e u) (e v)) := by
    intro ω u v
    exact hU'_dist ω (e u) (e v)
  let S : TreeTape N Φ ε d₀ → Set V := fun ω => { v : V | e v ∈ (res ω).2 }
  let sample : TreeTape N Φ ε d₀ → HST V × Set V := fun ω => (U ω, S ω)
  have h_enn_sum :
      (∑ ω : TreeTape N Φ ε d₀, ENNReal.ofReal (treeTapeProb N Φ ε d₀ ω)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hprob_nonneg ω), hprob_sum, ENNReal.ofReal_one]
  let P_Ω : PMF (TreeTape N Φ ε d₀) :=
    PMF.ofFintype (fun ω => ENNReal.ofReal (treeTapeProb N Φ ε d₀ ω)) h_enn_sum
  have hP_Ω_apply : ∀ ω : TreeTape N Φ ε d₀,
      P_Ω ω = ENNReal.ofReal (treeTapeProb N Φ ε d₀ ω) := by
    intro ω
    exact PMF.ofFintype_apply h_enn_sum ω
  let D : PMF (HST V × Set V) := P_Ω.map sample
  refine ⟨D, hβ_ge, hK_ge, hα_ge, ?_, ?_, ?_, ?_, ?_⟩
  · rw [PMF.support_map]
    exact (Set.toFinite P_Ω.support).image sample
  · intro p hp_supp u v
    rw [PMF.support_map] at hp_supp
    rcases hp_supp with ⟨ω, _, rfl⟩
    change hopDist G w (β * h) u v ≤ (U ω).dist u v
    rw [← h_hop_eq (β * h) u v, hU_dist ω u v]
    exact (h_root_inv ω).2.2.2.2.2.1 (e u) (Finset.mem_univ _) (e v) (Finset.mem_univ _)
  · intro p hp_supp u hu v
    rw [PMF.support_map] at hp_supp
    rcases hp_supp with ⟨ω, _, rfl⟩
    change (U ω).dist u v ≤ ENNReal.ofReal K * hopDist G w h u v
    have heu : e u ∈ (res ω).2 := hu
    rw [hU_dist ω u v, ← h_hop_eq h u v]
    exact (h_root_inv ω).2.2.2.2.2.2 (e u) heu (e v) (Finset.mem_univ _)
  · intro v
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype]
    have h_ind_eq :
        (∑ ω : TreeTape N Φ ε d₀, (sample ⁻¹' {p : HST V × Set V | v ∉ p.2}).indicator P_Ω ω) =
        ENNReal.ofReal (∑ ω : TreeTape N Φ ε d₀,
          treeTapeProb N Φ ε d₀ ω * (if e v ∉ (res ω).2 then (1 : ℝ) else 0)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl (fun ω _ => ?_)
        by_cases hmem : e v ∈ (res ω).2
        · simp [Set.indicator, sample, S, hmem]
        · simp [Set.indicator, sample, S, hmem, hP_Ω_apply]
      · intro ω _
        by_cases hmem : e v ∈ (res ω).2 <;> simp [hmem, hprob_nonneg ω]
    rw [h_ind_eq, ENNReal.toReal_ofReal]
    · exact hexcl (e v)
    · refine Finset.sum_nonneg (fun ω _ => ?_)
      by_cases hmem : e v ∈ (res ω).2 <;> simp [hmem, hprob_nonneg ω]
  · intro u v
    have h_tsum_eq :
        (∑' p : HST V × Set V, D p * savedHSTDist p.1 p.2 u v) =
        ∑ ω : TreeTape N Φ ε d₀, P_Ω ω * savedHSTDist (U ω) (S ω) u v := by
      calc
        (∑' p : HST V × Set V, D p * savedHSTDist p.1 p.2 u v)
            = ∑' p : HST V × Set V,
                (∑' ω : TreeTape N Φ ε d₀, if p = sample ω then P_Ω ω else 0) *
                  savedHSTDist p.1 p.2 u v := by
              refine tsum_congr (fun p => ?_)
              rw [PMF.map_apply]
              congr 1
              refine tsum_congr (fun ω => ?_)
              by_cases hps : p = sample ω <;> simp [hps]
        _ = ∑' p : HST V × Set V, ∑' ω : TreeTape N Φ ε d₀,
              (if p = sample ω then P_Ω ω else 0) * savedHSTDist p.1 p.2 u v := by
              refine tsum_congr (fun p => ?_)
              rw [ENNReal.tsum_mul_right]
        _ = ∑' ω : TreeTape N Φ ε d₀, ∑' p : HST V × Set V,
              if p = sample ω then P_Ω ω * savedHSTDist p.1 p.2 u v else 0 := by
              rw [ENNReal.tsum_comm]
              refine tsum_congr (fun ω => tsum_congr (fun p => ?_))
              split_ifs <;> simp
        _ = ∑' ω : TreeTape N Φ ε d₀, P_Ω ω * savedHSTDist (U ω) (S ω) u v := by
              refine tsum_congr (fun ω => ?_)
              simp [sample]
        _ = ∑ ω : TreeTape N Φ ε d₀, P_Ω ω * savedHSTDist (U ω) (S ω) u v := by
              rw [tsum_fintype]
    rw [h_tsum_eq]
    have h_sum_real :
        (∑ ω : TreeTape N Φ ε d₀, P_Ω ω * savedHSTDist (U ω) (S ω) u v) =
        ENNReal.ofReal (∑ ω : TreeTape N Φ ε d₀,
          treeTapeProb N Φ ε d₀ ω * savedRawDist (res ω) (e u) (e v)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · refine Finset.sum_congr rfl (fun ω _ => ?_)
        have hsrd_eq : savedHSTDist (U ω) (S ω) u v =
            ENNReal.ofReal (savedRawDist (res ω) (e u) (e v)) := by
          by_cases huv : e u ∈ (res ω).2 ∧ e v ∈ (res ω).2
          · have huv' : u ∈ S ω ∧ v ∈ S ω := huv
            simp [savedHSTDist, savedRawDist, huv, huv', hU_dist]
          · have huv' : ¬(u ∈ S ω ∧ v ∈ S ω) := huv
            simp [savedHSTDist, savedRawDist, huv, huv']
        rw [hP_Ω_apply ω, hsrd_eq, ← ENNReal.ofReal_mul (hprob_nonneg ω)]
      · intro ω _
        refine mul_nonneg (hprob_nonneg ω) ?_
        have hdist_nonneg : 0 ≤ (res ω).1.dist (e u) (e v) :=
          ((h_root_inv ω).2.2.2.2.1 (e u) (e v)).1
        by_cases huv : e u ∈ (res ω).2 ∧ e v ∈ (res ω).2 <;>
          simp [savedRawDist, huv, hdist_nonneg]
    rw [h_sum_real]
    have h_le := ENNReal.ofReal_le_ofReal (hexp (e u) (e v))
    refine le_trans h_le ?_
    have hα_nonneg : 0 ≤ α := by linarith
    rw [ENNReal.ofReal_mul hα_nonneg, h_hop_eq h u v]
    have h_ne_top : hopDist G w h u v ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hΦ_diam u v)
    rw [ENNReal.ofReal_toReal h_ne_top]

theorem thm1_from_finite_diam (h_core : ∀ (N : ℕ) (V : Type) [Fintype V],
      2 ≤ Fintype.card V → Fintype.card V ≤ N →
      ∀ (G : SimpleGraph V) (w : Sym2 V → ℝ),
        (∀ e ∈ G.edgeSet, 2 ≤ w e) →
        ∀ h : ℕ, 1 ≤ h →
          ∀ Φ : ℝ, 2 ≤ Φ →
            (∀ u v : V, hopDist G w h u v ≤ ENNReal.ofReal Φ) →
            ∀ ε : ℝ, 0 < ε → ε < 1 →
              ∃ D : PMF (HST V × Set V),
                IsStochasticHCRamseyHSTEmbedding G w h ε
                  (2 * hstRadiusSteps N Φ ε * (hstPhaseCount N + 1))
                  (8 * (hstRadiusSteps N Φ ε : ℝ) * (hstPhaseCount N : ℝ))
                  (256 * (hstPhaseCount N : ℝ) * Real.logb 2 (N : ℝ) *
                    (1 + 2 * hstTruncDelta N) ^ (Real.logb 2 Φ))
                  D) :
    Theorem1 :=
by
  have hst_two_regime_polylog_bounds : ∀ (c₀ : ℝ), 1 ≤ c₀ →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ n : ℕ, 2 ≤ n →
          ∀ ε : ℝ, 0 < ε → ε < 1 →
            let B : ℝ := 2 * (n : ℝ) ^ c₀
            let M_fin : ℝ := (n : ℝ) * B
            let P : ℝ := Real.logb 2 (n : ℝ) * (Real.logb 2 (Real.logb 2 (n : ℝ) + 2)) ^ 2
            (let β_A := 2 * hstRadiusSteps n M_fin ε * (hstPhaseCount n + 1)
             let K_A := 8 * (hstRadiusSteps n M_fin ε : ℝ) * (hstPhaseCount n : ℝ)
             let α_A := 256 * (hstPhaseCount n : ℝ) * Real.logb 2 (n : ℝ) *
               (1 + 2 * hstTruncDelta n) ^ (Real.logb 2 M_fin)
             1 ≤ β_A ∧ 1 ≤ K_A ∧ 1 ≤ α_A ∧
             ((max β_A n : ℕ) : ℝ) ≤ ε⁻¹ * C * P ∧
             K_A ≤ ε⁻¹ * C * P ∧
             α_A ≤ C * P) ∨
            (let Φ_B : ℝ := (n : ℝ) ^ (c₀ + 5)
             let β_B := 2 * hstRadiusSteps n Φ_B ε * (hstPhaseCount n + 1)
             let K_B := 8 * (hstRadiusSteps n Φ_B ε : ℝ) * (hstPhaseCount n : ℝ)
             let α_B := 256 * (hstPhaseCount n : ℝ) * Real.logb 2 (n : ℝ) *
               (1 + 2 * hstTruncDelta n) ^ (Real.logb 2 Φ_B)
             2 ≤ Φ_B ∧ 1 ≤ K_B ∧ 2 * K_B * M_fin ≤ Φ_B ∧
             (β_B : ℝ) ≤ ε⁻¹ * C * P ∧
             K_B ≤ ε⁻¹ * C * P ∧
             α_B ≤ C * P) := by
    clear h_core
    intro c₀ hc₀
    let E_A : ℝ := Real.exp (2 * (c₀ + 2))
    let A_k : ℝ := 1 + 4 * E_A * (3 * c₀ + 7)
    let B_k : ℝ := 24 * c₀ + 129
    let N₁ : ℝ := (2 : ℝ) ^ (512 * (c₀ + 2))
    let C : ℝ := max (max (16 * A_k) N₁) (max (16 * B_k) (max (512 * E_A) 1024))
    have hC_1024 : 1024 ≤ C :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have hC_1 : 1 ≤ C := by linarith only [hC_1024]
    have hC_16Ak : 16 * A_k ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
    have hC_N1 : N₁ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
    have hC_16Bk : 16 * B_k ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    have hC_512EA : 512 * E_A ≤ C :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    refine ⟨C, hC_1, ?_⟩
    intro n hn ε hε0 hε1
    dsimp only
    let B : ℝ := 2 * (n : ℝ) ^ c₀
    let M_fin : ℝ := (n : ℝ) * B
    let x : ℝ := Real.logb 2 (n : ℝ)
    let y : ℝ := Real.logb 2 ((n : ℝ) + 1)
    let Z : ℝ := Real.logb 2 (x + 2)
    let P : ℝ := x * Z ^ 2
    let L : ℕ := hstPhaseCount n
    let δ : ℝ := hstTruncDelta n
    have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith only [hn_cast]
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      have h2 : Real.log 2 ≤ Real.log (Real.exp 1) :=
        Real.log_le_log (by norm_num) (by linarith only [h])
      rwa [Real.log_exp] at h2
    have hlog2_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.add_one_le_exp (- (1 / 2 : ℝ))
      rw [Real.exp_neg] at h
      have hexp_pos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
      have hexp_le2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
        have hmul := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * Real.exp (1 / 2 : ℝ))
        have hcancel : (Real.exp (1 / 2 : ℝ))⁻¹ * (2 * Real.exp (1 / 2 : ℝ)) = 2 := by
          field_simp [ne_of_gt hexp_pos]
        have hrhs : (- (1 / 2 : ℝ) + 1) * (2 * Real.exp (1 / 2 : ℝ)) = Real.exp (1 / 2 : ℝ) := by ring
        linarith only [hmul, hcancel, hrhs]
      have hlog := Real.log_le_log hexp_pos hexp_le2
      rwa [Real.log_exp] at hlog
    have hx_ge1 : 1 ≤ x := by
      dsimp [x]
      calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
        _ ≤ Real.logb 2 (n : ℝ) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn_cast
    have hx_pos : 0 < x := by linarith only [hx_ge1]
    have hZ_gt1 : 1 < Z := by
      dsimp [Z]
      calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
        _ < Real.logb 2 (x + 2) :=
            Real.logb_lt_logb (by norm_num) (by norm_num) (by linarith only [hx_ge1])
    have hZ_ge1 : 1 ≤ Z := le_of_lt hZ_gt1
    have hZ_pos : 0 < Z := by linarith only [hZ_ge1]
    have hZ2_ge1 : 1 ≤ Z ^ 2 := by
      calc (1 : ℝ) = 1 ^ 2 := by norm_num
        _ ≤ Z ^ 2 := pow_le_pow_left₀ (by norm_num) hZ_ge1 2
    have hP_ge1 : 1 ≤ P := by
      dsimp [P]
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ x * Z ^ 2 := mul_le_mul hx_ge1 hZ2_ge1 (by norm_num) (le_of_lt hx_pos)
    have hP_pos : 0 < P := by linarith only [hP_ge1]
    have hεinv_gt1 : 1 < ε⁻¹ := (one_lt_inv₀ hε0).mpr hε1
    have hεinv_ge1 : 1 ≤ ε⁻¹ := le_of_lt hεinv_gt1
    have hy_gt_x : x < y := by
      dsimp [x, y]
      exact Real.logb_lt_logb (by norm_num) hn_pos (by linarith only [hn_pos])
    have hy_gt1 : 1 < y := lt_of_le_of_lt hx_ge1 hy_gt_x
    have hy_pos : 0 < y := by linarith only [hy_gt1]
    have hy_lt : y < x + 1 := by
      dsimp [x, y]
      calc Real.logb 2 ((n : ℝ) + 1)
          < Real.logb 2 (2 * (n : ℝ)) :=
            Real.logb_lt_logb (by norm_num) (by linarith only [hn_cast]) (by linarith only [hn_cast])
        _ = Real.logb 2 2 + Real.logb 2 (n : ℝ) :=
            Real.logb_mul (by norm_num) (ne_of_gt hn_pos)
        _ = Real.logb 2 (n : ℝ) + 1 := by
            rw [Real.logb_self_eq_one (by norm_num)]; ring
    have hlogby_pos : 0 < Real.logb 2 y := Real.logb_pos (by norm_num) hy_gt1
    have hlogby_lt_Z : Real.logb 2 y < Z := by
      dsimp [Z]
      exact Real.logb_lt_logb (by norm_num) hy_pos (by linarith only [hy_lt])
    have hL_ge1 : 1 ≤ L := Nat.ceil_pos.mpr hlogby_pos
    have hL_cast_ge1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge1
    have hL_lt_2Z : (L : ℝ) < 2 * Z := by
      have hceil : (L : ℝ) < Real.logb 2 y + 1 := Nat.ceil_lt_add_one (le_of_lt hlogby_pos)
      linarith only [hceil, hlogby_lt_Z, hZ_gt1]
    have hL_le_2Z : (L : ℝ) ≤ 2 * Z := le_of_lt hL_lt_2Z
    have hL1_le_3Z : ((L + 1 : ℕ) : ℝ) ≤ 3 * Z := by
      push_cast
      linarith only [hL_le_2Z, hZ_ge1]
    have hδ_pos : 0 < δ := by
      dsimp [δ, hstTruncDelta]
      positivity
    have hδ_le_x2inv : δ ≤ (x ^ 2)⁻¹ := by
      dsimp [δ, hstTruncDelta]
      exact inv_anti₀ (pow_pos hx_pos 2) (pow_le_pow_left₀ (le_of_lt hx_pos) (le_of_lt hy_gt_x) 2)
    have hδ_le_xinv : δ ≤ x⁻¹ := by
      refine le_trans hδ_le_x2inv ?_
      apply inv_anti₀ hx_pos
      calc x = x * 1 := (mul_one x).symm
        _ ≤ x * x := mul_le_mul_of_nonneg_left hx_ge1 (le_of_lt hx_pos)
        _ = x ^ 2 := (sq x).symm
    have h2divδ_eq : 2 / δ = 2 * y ^ 2 := by
      dsimp [δ, hstTruncDelta]
      have hy_ne : y ^ 2 ≠ 0 := ne_of_gt (pow_pos hy_pos 2)
      field_simp [hy_ne]
      rfl
    have hlog_2divδ_pos : 0 < Real.log (2 / δ) := by
      rw [h2divδ_eq]
      apply Real.log_pos
      have hy2_ge1 : 1 ≤ y ^ 2 := by
        calc (1 : ℝ) = 1 ^ 2 := by norm_num
          _ ≤ y ^ 2 := pow_le_pow_left₀ (by norm_num) (le_of_lt hy_gt1) 2
      linarith only [hy2_ge1]
    have hlog_2divδ_le_3Z : Real.log (2 / δ) ≤ 3 * Z := by
      rw [h2divδ_eq]
      have hcub : 2 * y ^ 2 ≤ (x + 2) ^ 3 := by
        calc 2 * y ^ 2
            ≤ (x + 2) * (x + 2) ^ 2 :=
              mul_le_mul (by linarith only [hx_ge1])
                (pow_le_pow_left₀ (le_of_lt hy_pos) (by linarith only [hy_lt]) 2)
                (sq_nonneg y) (by linarith only [hx_ge1])
          _ = (x + 2) ^ 3 := by ring
      have hlog1 : Real.log (2 * y ^ 2) ≤ Real.log ((x + 2) ^ 3) :=
        Real.log_le_log (by positivity) hcub
      have hlog2_eq : Real.log ((x + 2) ^ 3) = 3 * Real.log (x + 2) := by
        rw [Real.log_pow]; norm_num
      have hlog_x2 : Real.log (x + 2) = Z * Real.log 2 := by
        dsimp [Z, Real.logb]
        field_simp [ne_of_gt hlog2_pos]
      have hZlog2_le : Z * Real.log 2 ≤ Z := by
        calc Z * Real.log 2 ≤ Z * 1 := mul_le_mul_of_nonneg_left hlog2_le1 (le_of_lt hZ_pos)
          _ = Z := mul_one Z
      linarith only [hlog1, hlog2_eq, hlog_x2, hZlog2_le]
    have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith only [hn_cast])
    have hlogn_le_x : Real.log (n : ℝ) ≤ x := by
      have h : Real.log (n : ℝ) = x * Real.log 2 := by
        dsimp [x, Real.logb]
        field_simp [ne_of_gt hlog2_pos]
      calc Real.log (n : ℝ) = x * Real.log 2 := h
        _ ≤ x * 1 := mul_le_mul_of_nonneg_left hlog2_le1 (le_of_lt hx_pos)
        _ = x := mul_one x
    have hnc0_ge2 : 2 ≤ (n : ℝ) ^ c₀ := by
      calc (2 : ℝ) ≤ (n : ℝ) := hn_cast
        _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ c₀ := Real.rpow_le_rpow_of_exponent_le (by linarith only [hn_cast]) hc₀
    have hB_ge4 : 4 ≤ B := by dsimp [B]; linarith only [hnc0_ge2]
    have hM_ge8 : 8 ≤ M_fin := by
      dsimp [M_fin]
      calc (8 : ℝ) = 2 * 4 := by norm_num
        _ ≤ (n : ℝ) * B := mul_le_mul hn_cast hB_ge4 (by norm_num) (le_of_lt hn_pos)
    have hlogM_eq : Real.logb 2 M_fin = 1 + (c₀ + 1) * x := by
      dsimp [M_fin, B]
      have hnc0_pos : 0 < (n : ℝ) ^ c₀ := by linarith only [hnc0_ge2]
      rw [Real.logb_mul (ne_of_gt hn_pos) (by positivity),
          Real.logb_mul (by norm_num) (ne_of_gt hnc0_pos),
          Real.logb_self_eq_one (by norm_num),
          Real.logb_rpow_eq_mul_logb_of_pos hn_pos]
      ring
    have h_rpow_exp : ∀ t : ℝ, 0 ≤ t →
        1 ≤ (1 + 2 * δ) ^ t ∧ (1 + 2 * δ) ^ t ≤ Real.exp (2 * δ * t) := by
      intro t ht
      refine ⟨Real.one_le_rpow (by linarith only [hδ_pos]) ht, ?_⟩
      have hexp_step : 1 + 2 * δ ≤ Real.exp (2 * δ) := by
        linarith only [Real.add_one_le_exp (2 * δ)]
      calc (1 + 2 * δ) ^ t
          ≤ (Real.exp (2 * δ)) ^ t :=
            Real.rpow_le_rpow (by linarith only [hδ_pos]) hexp_step ht
        _ = Real.exp (2 * δ * t) := (Real.exp_mul (2 * δ) t).symm
    have h1_le_εxZ : 1 ≤ ε⁻¹ * x * Z := by
      calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
        _ ≤ (ε⁻¹ * x) * Z :=
            mul_le_mul (mul_le_mul hεinv_ge1 hx_ge1 (by norm_num) (by positivity))
              hZ_ge1 (by norm_num) (by positivity)
        _ = ε⁻¹ * x * Z := by ring
    have hxZ_le_P : x * Z ≤ P := by
      dsimp [P]
      calc x * Z = (x * Z) * 1 := (mul_one _).symm
        _ ≤ (x * Z) * Z := mul_le_mul_of_nonneg_left hZ_ge1 (by positivity)
        _ = x * Z ^ 2 := by ring
    by_cases h_reg : x < 512 * (c₀ + 2) ∨ ε < ((n : ℝ) ^ 2)⁻¹
    · left
      let t_A : ℝ := Real.logb 2 M_fin
      have ht_A_pos : 0 < t_A := by
        have hc0x : 0 ≤ (c₀ + 1) * x := mul_nonneg (by linarith only [hc₀]) (le_of_lt hx_pos)
        change 0 < Real.logb 2 M_fin
        linarith only [hlogM_eq, hc0x]
      have ht_A_le : t_A ≤ (c₀ + 2) * x := by
        have hring : x + (c₀ + 1) * x = (c₀ + 2) * x := by ring
        change Real.logb 2 M_fin ≤ (c₀ + 2) * x
        linarith only [hlogM_eq, hx_ge1, hring]
      obtain ⟨h_pow_ge1, h_pow_exp⟩ := h_rpow_exp t_A (le_of_lt ht_A_pos)
      have h2δt_le : 2 * δ * t_A ≤ 2 * (c₀ + 2) := by
        calc 2 * δ * t_A
            ≤ (2 * x⁻¹) * ((c₀ + 2) * x) :=
              mul_le_mul (by linarith only [hδ_le_xinv]) ht_A_le (le_of_lt ht_A_pos) (by positivity)
          _ = 2 * (c₀ + 2) := by field_simp [ne_of_gt hx_pos]
      have h_pow_le_EA : (1 + 2 * δ) ^ t_A ≤ E_A :=
        le_trans h_pow_exp (Real.exp_le_exp.mpr h2δt_le)
      let inner_A : ℝ :=
        (4 / ε) * (1 + 2 * δ) ^ t_A * (Real.log (n : ℝ) + Real.log (2 / δ) * t_A)
      have h_inner_pos : 0 < inner_A := by dsimp [inner_A]; positivity
      let k_A : ℕ := hstRadiusSteps n M_fin ε
      have hk_A_eq : k_A = Nat.ceil inner_A := rfl
      have hk_A_ge1 : 1 ≤ k_A := by rw [hk_A_eq]; exact Nat.ceil_pos.mpr h_inner_pos
      have hk_A_cast_ge1 : (1 : ℝ) ≤ (k_A : ℝ) := by exact_mod_cast hk_A_ge1
      have h_logterm_A : Real.log (n : ℝ) + Real.log (2 / δ) * t_A ≤ (3 * c₀ + 7) * x * Z := by
        have hmul : Real.log (2 / δ) * t_A ≤ (3 * Z) * ((c₀ + 2) * x) :=
          mul_le_mul hlog_2divδ_le_3Z ht_A_le (le_of_lt ht_A_pos) (by positivity)
        have hx_le_xZ : x ≤ x * Z := by
          calc x = x * 1 := (mul_one x).symm
            _ ≤ x * Z := mul_le_mul_of_nonneg_left hZ_ge1 (le_of_lt hx_pos)
        have hring : x * Z + (3 * Z) * ((c₀ + 2) * x) = (3 * c₀ + 7) * x * Z := by ring
        linarith only [hlogn_le_x, hmul, hx_le_xZ, hring]
      have h_inner_le : inner_A ≤ 4 * E_A * (3 * c₀ + 7) * ε⁻¹ * x * Z := by
        dsimp [inner_A]
        rw [div_eq_mul_inv]
        have h1 : (4 * ε⁻¹) * (1 + 2 * δ) ^ t_A ≤ (4 * ε⁻¹) * E_A :=
          mul_le_mul_of_nonneg_left h_pow_le_EA (by positivity)
        calc (4 * ε⁻¹) * (1 + 2 * δ) ^ t_A * (Real.log (n : ℝ) + Real.log (2 / δ) * t_A)
            ≤ ((4 * ε⁻¹) * E_A) * ((3 * c₀ + 7) * x * Z) :=
              mul_le_mul h1 h_logterm_A (by positivity) (by positivity)
          _ = 4 * E_A * (3 * c₀ + 7) * ε⁻¹ * x * Z := by ring
      have hk_A_le : (k_A : ℝ) ≤ A_k * ε⁻¹ * x * Z := by
        have hceil : (k_A : ℝ) < inner_A + 1 := by
          rw [hk_A_eq]; exact Nat.ceil_lt_add_one (le_of_lt h_inner_pos)
        have hring : 4 * E_A * (3 * c₀ + 7) * ε⁻¹ * x * Z + ε⁻¹ * x * Z = A_k * ε⁻¹ * x * Z := by
          dsimp [A_k]; ring
        linarith only [hceil, h_inner_le, h1_le_εxZ, hring]
      let β_A : ℕ := 2 * k_A * (L + 1)
      let K_A : ℝ := 8 * (k_A : ℝ) * (L : ℝ)
      let α_A : ℝ := 256 * (L : ℝ) * x * (1 + 2 * δ) ^ t_A
      have hβ_A_ge1 : 1 ≤ β_A := by
        dsimp [β_A]
        exact Nat.mul_pos (Nat.mul_pos (by norm_num) hk_A_ge1) (Nat.succ_pos L)
      have hK_A_ge1 : 1 ≤ K_A := by
        dsimp [K_A]
        calc (1 : ℝ) ≤ 8 * 1 * 1 := by norm_num
          _ ≤ 8 * (k_A : ℝ) * (L : ℝ) :=
              mul_le_mul (by linarith only [hk_A_cast_ge1]) hL_cast_ge1 (by norm_num) (by positivity)
      have hα_A_ge1 : 1 ≤ α_A := by
        dsimp [α_A]
        have h256Lx : 1 ≤ 256 * (L : ℝ) * x := by
          calc (1 : ℝ) ≤ (256 * 1) * 1 := by norm_num
            _ ≤ (256 * (L : ℝ)) * x :=
                mul_le_mul (by linarith only [hL_cast_ge1]) hx_ge1 (by norm_num) (by positivity)
        calc (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (256 * (L : ℝ) * x) * (1 + 2 * δ) ^ t_A :=
              mul_le_mul h256Lx h_pow_ge1 (by norm_num) (by positivity)
      have hAk_nn : 0 ≤ A_k := by
        dsimp [A_k]
        have : 0 ≤ E_A := le_of_lt (Real.exp_pos _)
        have : 0 ≤ 3 * c₀ + 7 := by linarith only [hc₀]
        positivity
      have hβ_A_bound : (β_A : ℝ) ≤ ε⁻¹ * C * P := by
        have hcast : (β_A : ℝ) = 2 * (k_A : ℝ) * ((L + 1 : ℕ) : ℝ) := by
          dsimp [β_A]; push_cast; ring
        rw [hcast]
        calc 2 * (k_A : ℝ) * ((L + 1 : ℕ) : ℝ)
            ≤ (2 * (A_k * ε⁻¹ * x * Z)) * (3 * Z) :=
              mul_le_mul (by linarith only [hk_A_le]) hL1_le_3Z (by positivity) (by positivity)
          _ = (6 * A_k) * (ε⁻¹ * P) := by dsimp [P]; ring
          _ ≤ (16 * A_k) * (ε⁻¹ * P) :=
              mul_le_mul_of_nonneg_right (by linarith only [hAk_nn]) (by positivity)
          _ ≤ C * (ε⁻¹ * P) := mul_le_mul_of_nonneg_right hC_16Ak (by positivity)
          _ = ε⁻¹ * C * P := by ring
      have hK_A_bound : K_A ≤ ε⁻¹ * C * P := by
        dsimp [K_A]
        calc 8 * (k_A : ℝ) * (L : ℝ)
            ≤ (8 * (A_k * ε⁻¹ * x * Z)) * (2 * Z) :=
              mul_le_mul (by linarith only [hk_A_le]) hL_le_2Z (by positivity) (by positivity)
          _ = (16 * A_k) * (ε⁻¹ * P) := by dsimp [P]; ring
          _ ≤ C * (ε⁻¹ * P) := mul_le_mul_of_nonneg_right hC_16Ak (by positivity)
          _ = ε⁻¹ * C * P := by ring
      have hα_A_bound : α_A ≤ C * P := by
        dsimp [α_A]
        have h256 : 256 * (L : ℝ) * x ≤ 256 * (2 * Z) * x :=
          mul_le_mul_of_nonneg_right (by linarith only [hL_le_2Z]) (le_of_lt hx_pos)
        calc 256 * (L : ℝ) * x * (1 + 2 * δ) ^ t_A
            ≤ (256 * (2 * Z) * x) * E_A :=
              mul_le_mul h256 h_pow_le_EA (by positivity) (by positivity)
          _ = (512 * E_A) * (x * Z) := by ring
          _ ≤ (512 * E_A) * P := mul_le_mul_of_nonneg_left hxZ_le_P (by positivity)
          _ ≤ C * P := mul_le_mul_of_nonneg_right hC_512EA (le_of_lt hP_pos)
      have hn_bound : (n : ℝ) ≤ ε⁻¹ * C * P := by
        rcases h_reg with hx_lt | hε_lt
        · have hn_eq : (n : ℝ) = (2 : ℝ) ^ x :=
            (Real.rpow_logb (by norm_num) (by norm_num) hn_pos).symm
          have hn_le_N1 : (n : ℝ) ≤ N₁ := by
            rw [hn_eq]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hx_lt)
          have hn_le_C : (n : ℝ) ≤ C := le_trans hn_le_N1 hC_N1
          have h1_le_εP : 1 ≤ ε⁻¹ * P := by
            calc (1 : ℝ) = 1 * 1 := by norm_num
              _ ≤ ε⁻¹ * P := mul_le_mul hεinv_ge1 hP_ge1 (by norm_num) (by positivity)
          calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
            _ ≤ C * (ε⁻¹ * P) := mul_le_mul hn_le_C h1_le_εP (by norm_num) (by linarith only [hC_1])
            _ = ε⁻¹ * C * P := by ring
        · have hn2_lt : (n : ℝ) ^ 2 < ε⁻¹ := by
            have hmul := mul_lt_mul_of_pos_right hε_lt (by positivity : 0 < (n : ℝ) ^ 2 * ε⁻¹)
            have h1 : ε * ((n : ℝ) ^ 2 * ε⁻¹) = (n : ℝ) ^ 2 := by field_simp [ne_of_gt hε0]
            have h2 : ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) ^ 2 * ε⁻¹) = ε⁻¹ := by
              field_simp [ne_of_gt hn_pos]
            linarith only [hmul, h1, h2]
          have hn_le_n2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
            calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
              _ ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_left (by linarith only [hn_cast]) (le_of_lt hn_pos)
              _ = (n : ℝ) ^ 2 := (sq _).symm
          have h1_le_CP : 1 ≤ C * P := by
            calc (1 : ℝ) = 1 * 1 := by norm_num
              _ ≤ C * P := mul_le_mul hC_1 hP_ge1 (by norm_num) (by linarith only [hC_1])
          calc (n : ℝ) ≤ ε⁻¹ * 1 := by rw [mul_one]; linarith only [hn_le_n2, hn2_lt]
            _ ≤ ε⁻¹ * (C * P) := mul_le_mul_of_nonneg_left h1_le_CP (by positivity)
            _ = ε⁻¹ * C * P := by ring
      have hmax_bound : ((max β_A n : ℕ) : ℝ) ≤ ε⁻¹ * C * P := by
        rw [Nat.cast_max]
        exact max_le hβ_A_bound hn_bound
      exact ⟨hβ_A_ge1, hK_A_ge1, hα_A_ge1, hmax_bound, hK_A_bound, hα_A_bound⟩
    · right
      push_neg at h_reg
      rcases h_reg with ⟨hx_ge_cut, hε_ge_n2⟩
      have hx_ge_1536 : 1536 ≤ x := by linarith only [hx_ge_cut, hc₀]
      have hεinv_le_n2 : ε⁻¹ ≤ (n : ℝ) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hε_ge_n2 (by positivity : 0 ≤ (n : ℝ) ^ 2 * ε⁻¹)
        have h1 : ((n : ℝ) ^ 2)⁻¹ * ((n : ℝ) ^ 2 * ε⁻¹) = ε⁻¹ := by field_simp [ne_of_gt hn_pos]
        have h2 : ε * ((n : ℝ) ^ 2 * ε⁻¹) = (n : ℝ) ^ 2 := by field_simp [ne_of_gt hε0]
        linarith only [hmul, h1, h2]
      let Φ_B : ℝ := (n : ℝ) ^ (c₀ + 5)
      have hΦ_B_ge2 : 2 ≤ Φ_B := by
        dsimp [Φ_B]
        calc (2 : ℝ) ≤ (n : ℝ) := hn_cast
          _ = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ (c₀ + 5) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith only [hn_cast]) (by linarith only [hc₀])
      let t_B : ℝ := Real.logb 2 Φ_B
      have ht_B_eq : t_B = (c₀ + 5) * x := by
        dsimp [t_B, Φ_B]
        exact Real.logb_rpow_eq_mul_logb_of_pos hn_pos
      have ht_B_pos : 0 < t_B := by
        rw [ht_B_eq]
        exact mul_pos (by linarith only [hc₀]) hx_pos
      obtain ⟨_, h_pow_exp⟩ := h_rpow_exp t_B (le_of_lt ht_B_pos)
      have h2δtB_le : 2 * δ * t_B ≤ 1 / 4 := by
        have ht_le : t_B ≤ 2 * (c₀ + 2) * x := by
          rw [ht_B_eq]
          exact mul_le_mul_of_nonneg_right (by linarith only [hc₀]) (le_of_lt hx_pos)
        have h1 : 2 * δ * t_B ≤ (2 * (x ^ 2)⁻¹) * (2 * (c₀ + 2) * x) :=
          mul_le_mul (by linarith only [hδ_le_x2inv]) ht_le (le_of_lt ht_B_pos) (by positivity)
        have h2 : (2 * (x ^ 2)⁻¹) * (2 * (c₀ + 2) * x) = 4 * (c₀ + 2) / x := by
          field_simp [ne_of_gt hx_pos]; ring
        have h3 : 4 * (c₀ + 2) / x ≤ 1 / 4 := by
          rw [div_le_iff₀ hx_pos]
          linarith only [hx_ge_cut, hc₀]
        linarith only [h1, h2, h3]
      have hexp_quarter_le2 : Real.exp (1 / 4 : ℝ) ≤ 2 := by
        have h := Real.add_one_le_exp (- (1 / 4 : ℝ))
        rw [Real.exp_neg] at h
        have hexp_pos : 0 < Real.exp (1 / 4 : ℝ) := Real.exp_pos _
        have hmul := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * Real.exp (1 / 4 : ℝ))
        have hcancel : (Real.exp (1 / 4 : ℝ))⁻¹ * (2 * Real.exp (1 / 4 : ℝ)) = 2 := by
          field_simp [ne_of_gt hexp_pos]
        have hlhs : (- (1 / 4 : ℝ) + 1) * (2 * Real.exp (1 / 4 : ℝ)) =
            (3 / 2 : ℝ) * Real.exp (1 / 4 : ℝ) := by ring
        linarith only [hmul, hcancel, hlhs, hexp_pos]
      have h_pow_le2 : (1 + 2 * δ) ^ t_B ≤ 2 :=
        le_trans h_pow_exp (le_trans (Real.exp_le_exp.mpr h2δtB_le) hexp_quarter_le2)
      let inner_B : ℝ :=
        (4 / ε) * (1 + 2 * δ) ^ t_B * (Real.log (n : ℝ) + Real.log (2 / δ) * t_B)
      have h_inner_pos : 0 < inner_B := by dsimp [inner_B]; positivity
      let k_B : ℕ := hstRadiusSteps n Φ_B ε
      have hk_B_eq : k_B = Nat.ceil inner_B := rfl
      have hk_B_ge1 : 1 ≤ k_B := by rw [hk_B_eq]; exact Nat.ceil_pos.mpr h_inner_pos
      have hk_B_cast_ge1 : (1 : ℝ) ≤ (k_B : ℝ) := by exact_mod_cast hk_B_ge1
      have h_logterm_B : Real.log (n : ℝ) + Real.log (2 / δ) * t_B ≤ (3 * c₀ + 16) * x * Z := by
        have hmul : Real.log (2 / δ) * t_B ≤ (3 * Z) * ((c₀ + 5) * x) := by
          rw [ht_B_eq]
          exact mul_le_mul_of_nonneg_right hlog_2divδ_le_3Z
            (mul_nonneg (by linarith only [hc₀]) (le_of_lt hx_pos))
        have hx_le_xZ : x ≤ x * Z := by
          calc x = x * 1 := (mul_one x).symm
            _ ≤ x * Z := mul_le_mul_of_nonneg_left hZ_ge1 (le_of_lt hx_pos)
        have hring : x * Z + (3 * Z) * ((c₀ + 5) * x) = (3 * c₀ + 16) * x * Z := by ring
        linarith only [hlogn_le_x, hmul, hx_le_xZ, hring]
      have h_inner_le : inner_B ≤ (24 * c₀ + 128) * ε⁻¹ * x * Z := by
        dsimp [inner_B]
        rw [div_eq_mul_inv]
        have h1 : (4 * ε⁻¹) * (1 + 2 * δ) ^ t_B ≤ (4 * ε⁻¹) * 2 :=
          mul_le_mul_of_nonneg_left h_pow_le2 (by positivity)
        calc (4 * ε⁻¹) * (1 + 2 * δ) ^ t_B * (Real.log (n : ℝ) + Real.log (2 / δ) * t_B)
            ≤ ((4 * ε⁻¹) * 2) * ((3 * c₀ + 16) * x * Z) :=
              mul_le_mul h1 h_logterm_B (by positivity) (by positivity)
          _ = (24 * c₀ + 128) * ε⁻¹ * x * Z := by ring
      have hk_B_le : (k_B : ℝ) ≤ B_k * ε⁻¹ * x * Z := by
        have hceil : (k_B : ℝ) < inner_B + 1 := by
          rw [hk_B_eq]; exact Nat.ceil_lt_add_one (le_of_lt h_inner_pos)
        have hring : (24 * c₀ + 128) * ε⁻¹ * x * Z + ε⁻¹ * x * Z = B_k * ε⁻¹ * x * Z := by
          dsimp [B_k]; ring
        linarith only [hceil, h_inner_le, h1_le_εxZ, hring]
      let β_B : ℕ := 2 * k_B * (L + 1)
      let K_B : ℝ := 8 * (k_B : ℝ) * (L : ℝ)
      let α_B : ℝ := 256 * (L : ℝ) * x * (1 + 2 * δ) ^ t_B
      have hK_B_ge1 : 1 ≤ K_B := by
        dsimp [K_B]
        calc (1 : ℝ) ≤ 8 * 1 * 1 := by norm_num
          _ ≤ 8 * (k_B : ℝ) * (L : ℝ) :=
              mul_le_mul (by linarith only [hk_B_cast_ge1]) hL_cast_ge1 (by norm_num) (by positivity)
      have hBk_nn : 0 ≤ B_k := by dsimp [B_k]; linarith only [hc₀]
      have hβ_B_bound : (β_B : ℝ) ≤ ε⁻¹ * C * P := by
        have hcast : (β_B : ℝ) = 2 * (k_B : ℝ) * ((L + 1 : ℕ) : ℝ) := by
          dsimp [β_B]; push_cast; ring
        rw [hcast]
        calc 2 * (k_B : ℝ) * ((L + 1 : ℕ) : ℝ)
            ≤ (2 * (B_k * ε⁻¹ * x * Z)) * (3 * Z) :=
              mul_le_mul (by linarith only [hk_B_le]) hL1_le_3Z (by positivity) (by positivity)
          _ = (6 * B_k) * (ε⁻¹ * P) := by dsimp [P]; ring
          _ ≤ (16 * B_k) * (ε⁻¹ * P) :=
              mul_le_mul_of_nonneg_right (by linarith only [hBk_nn]) (by positivity)
          _ ≤ C * (ε⁻¹ * P) := mul_le_mul_of_nonneg_right hC_16Bk (by positivity)
          _ = ε⁻¹ * C * P := by ring
      have hK_B_bound : K_B ≤ ε⁻¹ * C * P := by
        dsimp [K_B]
        calc 8 * (k_B : ℝ) * (L : ℝ)
            ≤ (8 * (B_k * ε⁻¹ * x * Z)) * (2 * Z) :=
              mul_le_mul (by linarith only [hk_B_le]) hL_le_2Z (by positivity) (by positivity)
          _ = (16 * B_k) * (ε⁻¹ * P) := by dsimp [P]; ring
          _ ≤ C * (ε⁻¹ * P) := mul_le_mul_of_nonneg_right hC_16Bk (by positivity)
          _ = ε⁻¹ * C * P := by ring
      have hα_B_bound : α_B ≤ C * P := by
        dsimp [α_B]
        have h256 : 256 * (L : ℝ) * x ≤ 256 * (2 * Z) * x :=
          mul_le_mul_of_nonneg_right (by linarith only [hL_le_2Z]) (le_of_lt hx_pos)
        calc 256 * (L : ℝ) * x * (1 + 2 * δ) ^ t_B
            ≤ (256 * (2 * Z) * x) * 2 :=
              mul_le_mul h256 h_pow_le2 (by positivity) (by positivity)
          _ = 1024 * (x * Z) := by ring
          _ ≤ 1024 * P := mul_le_mul_of_nonneg_left hxZ_le_P (by norm_num)
          _ ≤ C * P := mul_le_mul_of_nonneg_right hC_1024 (le_of_lt hP_pos)
      have hZ_le_3x : Z ≤ 3 * x := by
        have hlog_x2_le : Real.log (x + 2) ≤ x + 1 := by
          have h := Real.add_one_le_exp (x + 1)
          have h2 : Real.log (x + 2) ≤ Real.log (Real.exp (x + 1)) :=
            Real.log_le_log (by linarith only [hx_pos]) (by linarith only [h])
          rwa [Real.log_exp] at h2
        have hZ_def : Z * Real.log 2 = Real.log (x + 2) := by
          dsimp [Z, Real.logb]; field_simp [ne_of_gt hlog2_pos]
        have hhalf_Z : (1 / 2 : ℝ) * Z ≤ Z * Real.log 2 := by
          calc (1 / 2 : ℝ) * Z = Z * (1 / 2 : ℝ) := mul_comm _ _
            _ ≤ Z * Real.log 2 := mul_le_mul_of_nonneg_left hlog2_ge_half (le_of_lt hZ_pos)
        linarith only [hhalf_Z, hZ_def, hlog_x2_le, hx_ge_1536]
      have hL_le_6x : (L : ℝ) ≤ 6 * x := by linarith only [hL_le_2Z, hZ_le_3x]
      have hlog2δ_le_9x : Real.log (2 / δ) ≤ 9 * x := by linarith only [hlog_2divδ_le_3Z, hZ_le_3x]
      have ht_B_le_x2 : t_B ≤ x ^ 2 / 8 := by
        rw [ht_B_eq]
        have h1 : c₀ + 5 ≤ x / 8 := by linarith only [hx_ge_cut, hc₀]
        calc (c₀ + 5) * x ≤ (x / 8) * x := mul_le_mul_of_nonneg_right h1 (le_of_lt hx_pos)
          _ = x ^ 2 / 8 := by ring
      have h_logterm_x3 : Real.log (n : ℝ) + Real.log (2 / δ) * t_B ≤ 2 * x ^ 3 := by
        have hmul : Real.log (2 / δ) * t_B ≤ (9 * x) * (x ^ 2 / 8) :=
          mul_le_mul hlog2δ_le_9x ht_B_le_x2 (le_of_lt ht_B_pos) (by linarith only [hx_pos])
        have hx3 : x ≤ (7 / 8 : ℝ) * x ^ 3 := by
          have hx2 : 2 ≤ x ^ 2 := by
            calc (2 : ℝ) ≤ 2 * 1 := by norm_num
              _ ≤ x * x := mul_le_mul (by linarith only [hx_ge_1536]) hx_ge1 (by norm_num) (le_of_lt hx_pos)
              _ = x ^ 2 := (sq x).symm
          calc x = x * 1 := (mul_one x).symm
            _ ≤ x * ((7 / 8 : ℝ) * x ^ 2) :=
                mul_le_mul_of_nonneg_left (by linarith only [hx2]) (le_of_lt hx_pos)
            _ = (7 / 8 : ℝ) * x ^ 3 := by ring
        have hring : (7 / 8 : ℝ) * x ^ 3 + (9 * x) * (x ^ 2 / 8) = 2 * x ^ 3 := by ring
        linarith only [hlogn_le_x, hmul, hx3, hring]
      have hk_B_poly : (k_B : ℝ) ≤ 17 * (n : ℝ) ^ 2 * x ^ 3 := by
        have h4ε : 4 / ε ≤ 4 * (n : ℝ) ^ 2 := by
          rw [div_eq_mul_inv]; linarith only [hεinv_le_n2]
        have h_in : inner_B ≤ 16 * (n : ℝ) ^ 2 * x ^ 3 := by
          dsimp [inner_B]
          have h1 : (4 / ε) * (1 + 2 * δ) ^ t_B ≤ (4 * (n : ℝ) ^ 2) * 2 :=
            mul_le_mul h4ε h_pow_le2 (by positivity) (by positivity)
          calc (4 / ε) * (1 + 2 * δ) ^ t_B * (Real.log (n : ℝ) + Real.log (2 / δ) * t_B)
              ≤ ((4 * (n : ℝ) ^ 2) * 2) * (2 * x ^ 3) :=
                mul_le_mul h1 h_logterm_x3 (by positivity) (by positivity)
            _ = 16 * (n : ℝ) ^ 2 * x ^ 3 := by ring
        have hceil : (k_B : ℝ) < inner_B + 1 := by
          rw [hk_B_eq]; exact Nat.ceil_lt_add_one (le_of_lt h_inner_pos)
        have h1le : 1 ≤ (n : ℝ) ^ 2 * x ^ 3 := by
          have hx3_ge1 : 1 ≤ x ^ 3 := by
            calc (1 : ℝ) = 1 ^ 3 := by norm_num
              _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx_ge1 3
          have hn2_ge1 : 1 ≤ (n : ℝ) ^ 2 := by
            calc (1 : ℝ) = 1 ^ 2 := by norm_num
              _ ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith only [hn_cast]) 2
          calc (1 : ℝ) = 1 * 1 := by norm_num
            _ ≤ (n : ℝ) ^ 2 * x ^ 3 := mul_le_mul hn2_ge1 hx3_ge1 (by norm_num) (by positivity)
        linarith only [hceil, h_in, h1le]
      have h8x_pow4 : (8 * x) ^ 4 ≤ (n : ℝ) ^ 2 := by
        have hexp1 : x / 8 ≤ Real.exp (x / 8) := by
          linarith only [Real.add_one_le_exp (x / 8)]
        have hexp2 : (x / 8) ^ 2 ≤ Real.exp (x / 4) := by
          have hsq : (x / 8) ^ 2 ≤ (Real.exp (x / 8)) ^ 2 :=
            pow_le_pow_left₀ (by linarith only [hx_pos]) hexp1 2
          have hadd : (Real.exp (x / 8)) ^ 2 = Real.exp (x / 4) := by
            rw [sq, ← Real.exp_add]; ring_nf
          linarith only [hsq, hadd]
        have h8x_le_sq : 8 * x ≤ (x / 8) ^ 2 := by
          calc 8 * x = 512 * (x / 64) := by ring
            _ ≤ x * (x / 64) :=
                mul_le_mul_of_nonneg_right (by linarith only [hx_ge_1536]) (by linarith only [hx_pos])
            _ = (x / 8) ^ 2 := by ring
        have h_quarter : x / 4 ≤ (x / 2) * Real.log 2 := by
          calc x / 4 = (x / 2) * (1 / 2 : ℝ) := by ring
            _ ≤ (x / 2) * Real.log 2 :=
                mul_le_mul_of_nonneg_left hlog2_ge_half (by linarith only [hx_pos])
        have h8x_le_exp : 8 * x ≤ Real.exp ((x / 2) * Real.log 2) :=
          le_trans h8x_le_sq (le_trans hexp2 (Real.exp_le_exp.mpr h_quarter))
        have hpow4 : (8 * x) ^ 4 ≤ (Real.exp ((x / 2) * Real.log 2)) ^ 4 :=
          pow_le_pow_left₀ (by linarith only [hx_pos]) h8x_le_exp 4
        have hexp4 : (Real.exp ((x / 2) * Real.log 2)) ^ 4 = (n : ℝ) ^ 2 := by
          have hmul4 : (Real.exp ((x / 2) * Real.log 2)) ^ 4 = Real.exp (2 * (x * Real.log 2)) := by
            have h := Real.exp_nat_mul ((x / 2) * Real.log 2) 4
            rw [← h]; congr 1; push_cast; ring
          have hxlog : x * Real.log 2 = Real.log (n : ℝ) := by
            dsimp [x, Real.logb]; field_simp [ne_of_gt hlog2_pos]
          rw [hmul4, hxlog, two_mul, Real.exp_add, Real.exp_log hn_pos, sq]
        linarith only [hpow4, hexp4]
      have h32kL : 32 * (k_B : ℝ) * (L : ℝ) ≤ (n : ℝ) ^ 4 := by
        have h1 : 32 * (k_B : ℝ) * (L : ℝ) ≤ (32 * (17 * (n : ℝ) ^ 2 * x ^ 3)) * (6 * x) :=
          mul_le_mul (by linarith only [hk_B_poly]) hL_le_6x (by positivity) (by positivity)
        have h2 : (32 * (17 * (n : ℝ) ^ 2 * x ^ 3)) * (6 * x) = 3264 * x ^ 4 * (n : ℝ) ^ 2 := by ring
        have h3 : 3264 * x ^ 4 ≤ (8 * x) ^ 4 := by
          have hring : (8 * x) ^ 4 = 4096 * x ^ 4 := by ring
          have hx4_nn : 0 ≤ x ^ 4 := by positivity
          linarith only [hring, hx4_nn]
        calc 32 * (k_B : ℝ) * (L : ℝ)
            ≤ 3264 * x ^ 4 * (n : ℝ) ^ 2 := by linarith only [h1, h2]
          _ ≤ (8 * x) ^ 4 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
          _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h8x_pow4 (by positivity)
          _ = (n : ℝ) ^ 4 := by ring
      have h_self_cons : 2 * K_B * M_fin ≤ Φ_B := by
        have hlhs : 2 * K_B * M_fin = (32 * (k_B : ℝ) * (L : ℝ)) * ((n : ℝ) * (n : ℝ) ^ c₀) := by
          dsimp [K_B, M_fin, B]; ring
        have hrhs : (n : ℝ) ^ 4 * ((n : ℝ) * (n : ℝ) ^ c₀) = Φ_B := by
          dsimp [Φ_B]
          have h5 : (n : ℝ) ^ 4 * (n : ℝ) = (n : ℝ) ^ (5 : ℝ) := by
            have : (n : ℝ) ^ 4 * (n : ℝ) = (n : ℝ) ^ (5 : ℕ) := by ring
            rw [this, ← Real.rpow_natCast]; norm_num
          calc (n : ℝ) ^ 4 * ((n : ℝ) * (n : ℝ) ^ c₀)
              = ((n : ℝ) ^ 4 * (n : ℝ)) * (n : ℝ) ^ c₀ := by ring
            _ = (n : ℝ) ^ (5 : ℝ) * (n : ℝ) ^ c₀ := by rw [h5]
            _ = (n : ℝ) ^ ((5 : ℝ) + c₀) := (Real.rpow_add hn_pos 5 c₀).symm
            _ = (n : ℝ) ^ (c₀ + 5) := by ring_nf
        rw [hlhs, ← hrhs]
        exact mul_le_mul_of_nonneg_right h32kL (by positivity)
      exact ⟨hΦ_B_ge2, hK_B_ge1, h_self_cons, hβ_B_bound, hK_B_bound, hα_B_bound⟩
  have pmf_map_tsum : ∀ {α β : Type 1} (D : PMF α) (f : α → β) (g : β → ENNReal),
      (∑' b : β, (D.map f) b * g b) = ∑' a : α, D a * g (f a) := by
    clear h_core hst_two_regime_polylog_bounds
    intro α β D f g
    classical
    have h1 : ∀ b : β, (D.map f) b * g b = ∑' a : α, if b = f a then D a * g b else 0 := by
      intro b
      rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
      congr 1; ext a; split_ifs <;> simp
    simp_rw [h1]
    rw [ENNReal.tsum_comm]
    congr 1; ext a
    exact tsum_ite_eq (f a) (fun b => D a * g b)
  have pmf_bind_map_tsum : ∀ {α β γ : Type 1}
      (D₁ : PMF α) (D₂ : PMF β) (glue : α → β → γ) (g : γ → ENNReal),
      (∑' c : γ, (D₁.bind (fun a => D₂.map (fun b => glue a b))) c * g c) =
        ∑' a : α, D₁ a * (∑' b : β, D₂ b * g (glue a b)) := by
    clear h_core hst_two_regime_polylog_bounds
    intro α β γ D₁ D₂ glue g
    have h1 : ∀ c : γ, (D₁.bind (fun a => D₂.map (fun b => glue a b))) c * g c =
        ∑' a : α, D₁ a * ((D₂.map (fun b => glue a b)) c * g c) := by
      intro c
      rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
      congr 1; ext a; ring
    simp_rw [h1]
    rw [ENNReal.tsum_comm]
    congr 1; ext a
    rw [ENNReal.tsum_mul_left, pmf_map_tsum]
  have tree_lca_props : ∀ {Node : Type} [Finite Node] {T : SimpleGraph Node} (hT : T.IsTree)
      (rt : Node),
      (∀ {x y z : Node}, IsLCA T rt x y z → rootedLCA T rt x y = z) ∧
      (∀ x y : Node, IsLCA T rt x y (rootedLCA T rt x y)) := by
    clear h_core hst_two_regime_polylog_bounds pmf_map_tsum pmf_bind_map_tsum
    intro Node _ T hT rt
    letI : Fintype Node := Fintype.ofFinite Node
    letI : DecidableEq Node := Classical.decEq Node
    let uPath : ∀ q : Node, T.Walk rt q := fun q => Classical.choose (hT.existsUnique_path rt q)
    have huPath_isPath : ∀ q : Node, (uPath q).IsPath :=
      fun q => (Classical.choose_spec (hT.existsUnique_path rt q)).1
    have huPath_eq : ∀ {q : Node} (p : T.Walk rt q), p.IsPath → p = uPath q :=
      fun p hp => (Classical.choose_spec (hT.existsUnique_path rt _)).2 p hp
    have hdesc_iff : ∀ q z : Node, IsDescendant T rt q z ↔ z ∈ (uPath q).support := by
      intro q z
      refine ⟨?_, fun hz => ⟨uPath q, huPath_isPath q, hz⟩⟩
      rintro ⟨p, hp, hz⟩
      rwa [huPath_eq p hp] at hz
    have hdesc_antisymm : ∀ {a b : Node},
        IsDescendant T rt a b → IsDescendant T rt b a → a = b := by
      intro a b hab hba
      rw [hdesc_iff] at hab hba
      have eq_b : (uPath a).takeUntil b hab = uPath b :=
        huPath_eq _ ((huPath_isPath a).takeUntil hab)
      have eq_a : (uPath b).takeUntil a hba = uPath a :=
        huPath_eq _ ((huPath_isPath b).takeUntil hba)
      have hlen_a := congrArg SimpleGraph.Walk.length ((uPath a).take_spec hab)
      have hlen_b := congrArg SimpleGraph.Walk.length ((uPath b).take_spec hba)
      rw [SimpleGraph.Walk.length_append, eq_b] at hlen_a
      rw [SimpleGraph.Walk.length_append, eq_a] at hlen_b
      have hdrop0 : ((uPath a).dropUntil b hab).length = 0 := by omega
      exact (((uPath a).dropUntil b hab).eq_of_length_eq_zero hdrop0).symm
    have hlca_unique : ∀ {x y z₁ z₂ : Node},
        IsLCA T rt x y z₁ → IsLCA T rt x y z₂ → z₁ = z₂ := by
      intro x y z₁ z₂ h₁ h₂
      exact hdesc_antisymm (h₁.2.2 z₂ h₂.1 h₂.2.1) (h₂.2.2 z₁ h₁.1 h₁.2.1)
    have h_eq_of_isLCA : ∀ {x y z : Node}, IsLCA T rt x y z → rootedLCA T rt x y = z := by
      intro x y z hz
      unfold rootedLCA
      have hex : ∃ z', IsLCA T rt x y z' := ⟨z, hz⟩
      rw [dif_pos hex]
      exact hlca_unique (Classical.choose_spec hex) hz
    refine ⟨h_eq_of_isLCA, ?_⟩
    intro x y
    suffices hex : ∃ z : Node, IsLCA T rt x y z by
      rcases hex with ⟨z, hz⟩
      rwa [h_eq_of_isLCA hz]
    let S : Finset Node := (uPath x).support.toFinset ∩ (uPath y).support.toFinset
    have hrt_mem : rt ∈ S := by
      simp [S, SimpleGraph.Walk.start_mem_support]
    obtain ⟨z, hzS, hz_max⟩ := Finset.exists_max_image S (fun w => (uPath w).length) ⟨rt, hrt_mem⟩
    simp only [S, Finset.mem_inter, List.mem_toFinset] at hzS
    rcases hzS with ⟨hzx, hzy⟩
    refine ⟨z, (hdesc_iff x z).mpr hzx, (hdesc_iff y z).mpr hzy, ?_⟩
    intro w hwx hwy
    have hwx_mem : w ∈ (uPath x).support := (hdesc_iff x w).mp hwx
    have hwy_mem : w ∈ (uPath y).support := (hdesc_iff y w).mp hwy
    have hwS : w ∈ S := by simp [S, hwx_mem, hwy_mem]
    have hlen_le : (uPath w).length ≤ (uPath z).length := hz_max w hwS
    have hsplit := (uPath x).take_spec hzx
    have hsupp : w ∈ ((uPath x).takeUntil z hzx).support ++
        ((uPath x).dropUntil z hzx).support.tail := by
      rw [← SimpleGraph.Walk.support_append, hsplit]
      exact hwx_mem
    rcases List.mem_append.mp hsupp with hw_take | hw_tail
    · exact ⟨(uPath x).takeUntil z hzx, (huPath_isPath x).takeUntil hzx, hw_take⟩
    · have hw_drop : w ∈ ((uPath x).dropUntil z hzx).support := List.tail_subset _ hw_tail
      let q₁ := (uPath x).takeUntil z hzx
      let q₂ := ((uPath x).dropUntil z hzx).takeUntil w hw_drop
      let q₃ := ((uPath x).dropUntil z hzx).dropUntil w hw_drop
      have hq1_eq : q₁ = uPath z := huPath_eq q₁ ((huPath_isPath x).takeUntil hzx)
      have h_assoc : (q₁.append q₂).append q₃ = uPath x := by
        rw [← SimpleGraph.Walk.append_assoc]
        dsimp [q₂, q₃]
        rw [((uPath x).dropUntil z hzx).take_spec hw_drop]
        exact hsplit
      have hq12_path : (q₁.append q₂).IsPath :=
        SimpleGraph.Walk.IsPath.of_append_left (h_assoc.symm ▸ huPath_isPath x)
      have hq12_eq : q₁.append q₂ = uPath w := huPath_eq _ hq12_path
      have hlen_eq : (uPath z).length + q₂.length = (uPath w).length := by
        rw [← hq1_eq, ← hq12_eq, SimpleGraph.Walk.length_append]
      have hq2_zero : q₂.length = 0 := by omega
      have hzw : z = w := q₂.eq_of_length_eq_zero hq2_zero
      subst hzw
      exact ⟨uPath z, huPath_isPath z, SimpleGraph.Walk.end_mem_support _⟩
  have join_two_hsts : ∀ {V : Type} (P : V → Prop) [DecidablePred P]
      (U₁ : HST {u : V // P u}) (U₂ : HST {u : V // ¬ P u}),
      ∃ U : HST V,
        (∀ (u v : V) (hu : P u) (hv : P v), U.dist u v = U₁.dist ⟨u, hu⟩ ⟨v, hv⟩) ∧
        (∀ (u v : V) (hu : ¬ P u) (hv : ¬ P v), U.dist u v = U₂.dist ⟨u, hu⟩ ⟨v, hv⟩) ∧
        (∀ (u v : V), (P u ∧ ¬ P v) ∨ (¬ P u ∧ P v) → U.dist u v = ⊤) := by
    clear h_core hst_two_regime_polylog_bounds pmf_map_tsum pmf_bind_map_tsum
    intro V P _ U₁ U₂
    haveI : Finite U₁.Node := U₁.finiteNode
    haveI : Finite U₂.Node := U₂.finiteNode
    obtain ⟨hU₁_conn, hU₁_acyc⟩ := (SimpleGraph.isTree_iff U₁.tree).mp U₁.isTree
    obtain ⟨hU₂_conn, hU₂_acyc⟩ := (SimpleGraph.isTree_iff U₂.tree).mp U₂.isTree
    let NodeJ := Option (U₁.Node ⊕ U₂.Node)
    let adjJ : NodeJ → NodeJ → Prop
      | none, some (.inl q₁) => q₁ = U₁.root
      | some (.inl q₁), none => q₁ = U₁.root
      | none, some (.inr q₂) => q₂ = U₂.root
      | some (.inr q₂), none => q₂ = U₂.root
      | some (.inl q₁), some (.inl r₁) => U₁.tree.Adj q₁ r₁
      | some (.inr q₂), some (.inr r₂) => U₂.tree.Adj q₂ r₂
      | _, _ => False
    let T : SimpleGraph NodeJ :=
      { Adj := adjJ
        symm := by
          intro x y h
          rcases x with _ | (q₁ | q₂) <;> rcases y with _ | (r₁ | r₂) <;>
            try exact h
          · exact U₁.tree.symm h
          · exact U₂.tree.symm h
        loopless := by
          intro x h
          rcases x with _ | (q₁ | q₂)
          · exact h
          · exact U₁.tree.loopless q₁ h
          · exact U₂.tree.loopless q₂ h }
    let inlHom : U₁.tree →g T :=
      { toFun := fun q₁ => some (.inl q₁)
        map_rel' := fun h => h }
    let inrHom : U₂.tree →g T :=
      { toFun := fun q₂ => some (.inr q₂)
        map_rel' := fun h => h }
    have hinl_inj : Function.Injective inlHom := by
      intro a b h; injection h with h'; injection h'
    have hinr_inj : Function.Injective inrHom := by
      intro a b h; injection h with h'; injection h'
    have hadj_none_inl : T.Adj none (some (.inl U₁.root)) := rfl
    have hadj_none_inr : T.Adj none (some (.inr U₂.root)) := rfl
    have hT_conn : T.Connected := by
      refine ⟨fun x y => ?_⟩
      suffices h_from_none : ∀ z : NodeJ, T.Reachable none z from
        (h_from_none x).symm.trans (h_from_none y)
      intro z
      rcases z with _ | (q₁ | q₂)
      · exact SimpleGraph.Reachable.refl none
      · obtain ⟨p₁⟩ := hU₁_conn U₁.root q₁
        exact ⟨SimpleGraph.Walk.cons hadj_none_inl (p₁.map inlHom)⟩
      · obtain ⟨p₂⟩ := hU₂_conn U₂.root q₂
        exact ⟨SimpleGraph.Walk.cons hadj_none_inr (p₂.map inrHom)⟩
    have h_stay_inl : ∀ {a b : NodeJ} (w : T.Walk a b) (q₁ : U₁.Node),
        a = some (.inl q₁) → s(none, some (.inl U₁.root)) ∉ w.edges →
        ∃ r₁ : U₁.Node, b = some (.inl r₁) := by
      intro a b w
      induction w with
      | nil => intro q₁ ha _; exact ⟨q₁, ha⟩
      | @cons x y z hadj w' ih =>
        intro q₁ hx hnot
        subst hx
        rcases y with _ | (q₁' | q₂')
        · have hq : q₁ = U₁.root := hadj
          subst hq
          exfalso
          apply hnot
          simp [SimpleGraph.Walk.edges, Sym2.eq_swap]
        · exact ih q₁' rfl (fun hm => hnot (List.mem_cons_of_mem _ hm))
        · exact False.elim hadj
    have h_stay_inr : ∀ {a b : NodeJ} (w : T.Walk a b) (q₂ : U₂.Node),
        a = some (.inr q₂) → s(none, some (.inr U₂.root)) ∉ w.edges →
        ∃ r₂ : U₂.Node, b = some (.inr r₂) := by
      intro a b w
      induction w with
      | nil => intro q₂ ha _; exact ⟨q₂, ha⟩
      | @cons x y z hadj w' ih =>
        intro q₂ hx hnot
        subst hx
        rcases y with _ | (q₁' | q₂')
        · have hq : q₂ = U₂.root := hadj
          subst hq
          exfalso
          apply hnot
          simp [SimpleGraph.Walk.edges, Sym2.eq_swap]
        · exact False.elim hadj
        · exact ih q₂' rfl (fun hm => hnot (List.mem_cons_of_mem _ hm))
    have h_lift_inl : ∀ {x y : NodeJ} (w : T.Walk x y),
        none ∉ w.support → ∀ (a b : U₁.Node) (hx : x = inlHom a) (hy : y = inlHom b),
        ∃ w₁ : U₁.tree.Walk a b, (w₁.map inlHom).copy hx.symm hy.symm = w := by
      intro x y w
      induction w with
      | nil =>
        intro _ a b hx hy
        subst hx
        have hab : a = b := hinl_inj hy
        subst hab
        exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | @cons x z y hadj w' ih =>
        intro hnone a b hx hy
        subst hx; subst hy
        have hnone' : none ∉ w'.support := fun hm => hnone (List.mem_cons_of_mem _ hm)
        rcases z with _ | (c₁ | c₂)
        · exfalso; exact hnone' (SimpleGraph.Walk.start_mem_support _)
        · have hadj₁ : U₁.tree.Adj a c₁ := hadj
          obtain ⟨w₁', hw₁'⟩ := ih hnone' c₁ b rfl rfl
          refine ⟨SimpleGraph.Walk.cons hadj₁ w₁', ?_⟩
          simpa [inlHom] using congrArg (SimpleGraph.Walk.cons hadj) hw₁'
        · exact False.elim hadj
    have h_lift_inr : ∀ {x y : NodeJ} (w : T.Walk x y),
        none ∉ w.support → ∀ (a b : U₂.Node) (hx : x = inrHom a) (hy : y = inrHom b),
        ∃ w₂ : U₂.tree.Walk a b, (w₂.map inrHom).copy hx.symm hy.symm = w := by
      intro x y w
      induction w with
      | nil =>
        intro _ a b hx hy
        subst hx
        have hab : a = b := hinr_inj hy
        subst hab
        exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | @cons x z y hadj w' ih =>
        intro hnone a b hx hy
        subst hx; subst hy
        have hnone' : none ∉ w'.support := fun hm => hnone (List.mem_cons_of_mem _ hm)
        rcases z with _ | (c₁ | c₂)
        · exfalso; exact hnone' (SimpleGraph.Walk.start_mem_support _)
        · exact False.elim hadj
        · have hadj₂ : U₂.tree.Adj a c₂ := hadj
          obtain ⟨w₂', hw₂'⟩ := ih hnone' c₂ b rfl rfl
          refine ⟨SimpleGraph.Walk.cons hadj₂ w₂', ?_⟩
          simpa [inrHom] using congrArg (SimpleGraph.Walk.cons hadj) hw₂'
    have hT_acyclic : T.IsAcyclic := by
      letI : DecidableEq NodeJ := Classical.decEq NodeJ
      intro u c hc
      by_cases hnone : none ∈ c.support
      · generalize hc'_def : c.rotate hnone = c'
        have hc' : c'.IsCycle := hc'_def ▸ hc.rotate hnone
        rcases c' with _ | @⟨_, x, _, hadj, r⟩
        · exact hc'.ne_nil rfl
        · have hnodup : (SimpleGraph.Walk.cons hadj r).edges.Nodup := hc'.edges_nodup
          have hnot_edge : s(none, x) ∉ r.edges := (List.nodup_cons.mp hnodup).1
          rcases x with _ | (q₁ | q₂)
          · exact T.loopless none hadj
          · have hq : q₁ = U₁.root := hadj
            subst hq
            obtain ⟨r₁, hr₁⟩ := h_stay_inl r U₁.root rfl hnot_edge
            cases hr₁
          · have hq : q₂ = U₂.root := hadj
            subst hq
            obtain ⟨r₂, hr₂⟩ := h_stay_inr r U₂.root rfl hnot_edge
            cases hr₂
      · rcases u with _ | (q₁ | q₂)
        · exact hnone (SimpleGraph.Walk.start_mem_support _)
        · obtain ⟨c₁, hc₁_eq⟩ := h_lift_inl c hnone q₁ q₁ rfl rfl
          have hc₁_map : c₁.map inlHom = c := by simpa using hc₁_eq
          have hc₁ : c₁.IsCycle := by
            have hed : c₁.edges.Nodup := by
              have h1 : (c₁.map inlHom).edges.Nodup := hc₁_map.symm ▸ hc.edges_nodup
              rw [SimpleGraph.Walk.edges_map] at h1
              exact List.Nodup.of_map _ h1
            have hne : c₁ ≠ SimpleGraph.Walk.nil := by
              intro hnil; subst hnil
              exact hc.ne_nil hc₁_map.symm
            have hsup : c₁.support.tail.Nodup := by
              have h1 : (c₁.map inlHom).support.tail.Nodup := hc₁_map.symm ▸ hc.support_nodup
              rw [SimpleGraph.Walk.support_map, ← List.map_tail] at h1
              exact List.Nodup.of_map _ h1
            exact ⟨⟨⟨hed⟩, hne⟩, hsup⟩
          exact hU₁_acyc c₁ hc₁
        · obtain ⟨c₂, hc₂_eq⟩ := h_lift_inr c hnone q₂ q₂ rfl rfl
          have hc₂_map : c₂.map inrHom = c := by simpa using hc₂_eq
          have hc₂ : c₂.IsCycle := by
            have hed : c₂.edges.Nodup := by
              have h1 : (c₂.map inrHom).edges.Nodup := hc₂_map.symm ▸ hc.edges_nodup
              rw [SimpleGraph.Walk.edges_map] at h1
              exact List.Nodup.of_map _ h1
            have hne : c₂ ≠ SimpleGraph.Walk.nil := by
              intro hnil; subst hnil
              exact hc.ne_nil hc₂_map.symm
            have hsup : c₂.support.tail.Nodup := by
              have h1 : (c₂.map inrHom).support.tail.Nodup := hc₂_map.symm ▸ hc.support_nodup
              rw [SimpleGraph.Walk.support_map, ← List.map_tail] at h1
              exact List.Nodup.of_map _ h1
            exact ⟨⟨⟨hed⟩, hne⟩, hsup⟩
          exact hU₂_acyc c₂ hc₂
    have hT_tree : T.IsTree := ⟨hT_conn, hT_acyclic⟩
    have hdesc_none : ∀ z : NodeJ, IsDescendant T none none z ↔ z = none := by
      intro z
      constructor
      · rintro ⟨p, hp, hz⟩
        have hp_eq : p = SimpleGraph.Walk.nil :=
          (hT_tree.existsUnique_path none none).unique hp SimpleGraph.Walk.IsPath.nil
        subst hp_eq
        simpa using hz
      · rintro rfl
        exact ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp⟩
    have hdesc_inl : ∀ (q₁ : U₁.Node) (z : NodeJ),
        IsDescendant T none (some (.inl q₁)) z ↔
          z = none ∨ ∃ z₁ : U₁.Node, z = some (.inl z₁) ∧ IsDescendant U₁.tree U₁.root q₁ z₁ := by
      intro q₁ z
      obtain ⟨p₁, hp₁, hp₁_uniq⟩ := U₁.isTree.existsUnique_path U₁.root q₁
      let P₁ : T.Walk none (some (.inl q₁)) := SimpleGraph.Walk.cons hadj_none_inl (p₁.map inlHom)
      have hP₁_path : P₁.IsPath := by
        rw [SimpleGraph.Walk.isPath_def]
        change (none :: (p₁.map inlHom).support).Nodup
        rw [SimpleGraph.Walk.support_map, List.nodup_cons]
        refine ⟨?_, hp₁.support_nodup.map hinl_inj⟩
        intro hmem
        rcases List.mem_map.mp hmem with ⟨x, _, hx⟩
        cases hx
      constructor
      · rintro ⟨p, hp, hz⟩
        have hp_eq : p = P₁ := (hT_tree.existsUnique_path _ _).unique hp hP₁_path
        subst hp_eq
        change z ∈ none :: (p₁.map inlHom).support at hz
        rw [SimpleGraph.Walk.support_map, List.mem_cons] at hz
        rcases hz with rfl | hmem
        · exact Or.inl rfl
        · rcases List.mem_map.mp hmem with ⟨z₁, hz₁, rfl⟩
          exact Or.inr ⟨z₁, rfl, ⟨p₁, hp₁, hz₁⟩⟩
      · rintro (rfl | ⟨z₁, rfl, ⟨p₁', hp₁', hz₁⟩⟩)
        · exact ⟨P₁, hP₁_path, SimpleGraph.Walk.start_mem_support _⟩
        · have heq : p₁' = p₁ := hp₁_uniq p₁' hp₁'
          subst heq
          refine ⟨P₁, hP₁_path, ?_⟩
          change some (.inl z₁) ∈ none :: (p₁'.map inlHom).support
          rw [SimpleGraph.Walk.support_map]
          exact List.mem_cons_of_mem _ (List.mem_map_of_mem hz₁)
    have hdesc_inr : ∀ (q₂ : U₂.Node) (z : NodeJ),
        IsDescendant T none (some (.inr q₂)) z ↔
          z = none ∨ ∃ z₂ : U₂.Node, z = some (.inr z₂) ∧ IsDescendant U₂.tree U₂.root q₂ z₂ := by
      intro q₂ z
      obtain ⟨p₂, hp₂, hp₂_uniq⟩ := U₂.isTree.existsUnique_path U₂.root q₂
      let P₂ : T.Walk none (some (.inr q₂)) := SimpleGraph.Walk.cons hadj_none_inr (p₂.map inrHom)
      have hP₂_path : P₂.IsPath := by
        rw [SimpleGraph.Walk.isPath_def]
        change (none :: (p₂.map inrHom).support).Nodup
        rw [SimpleGraph.Walk.support_map, List.nodup_cons]
        refine ⟨?_, hp₂.support_nodup.map hinr_inj⟩
        intro hmem
        rcases List.mem_map.mp hmem with ⟨x, _, hx⟩
        cases hx
      constructor
      · rintro ⟨p, hp, hz⟩
        have hp_eq : p = P₂ := (hT_tree.existsUnique_path _ _).unique hp hP₂_path
        subst hp_eq
        change z ∈ none :: (p₂.map inrHom).support at hz
        rw [SimpleGraph.Walk.support_map, List.mem_cons] at hz
        rcases hz with rfl | hmem
        · exact Or.inl rfl
        · rcases List.mem_map.mp hmem with ⟨z₂, hz₂, rfl⟩
          exact Or.inr ⟨z₂, rfl, ⟨p₂, hp₂, hz₂⟩⟩
      · rintro (rfl | ⟨z₂, rfl, ⟨p₂', hp₂', hz₂⟩⟩)
        · exact ⟨P₂, hP₂_path, SimpleGraph.Walk.start_mem_support _⟩
        · have heq : p₂' = p₂ := hp₂_uniq p₂' hp₂'
          subst heq
          refine ⟨P₂, hP₂_path, ?_⟩
          change some (.inr z₂) ∈ none :: (p₂'.map inrHom).support
          rw [SimpleGraph.Walk.support_map]
          exact List.mem_cons_of_mem _ (List.mem_map_of_mem hz₂)
    have hleaf_none : ¬ IsRootedLeaf T none none := by
      intro hleaf
      have h1 : IsDescendant T none (some (.inl U₁.root)) none :=
        (hdesc_inl U₁.root none).mpr (Or.inl rfl)
      have hbad := hleaf _ h1
      cases hbad
    have hleaf_inl : ∀ q₁ : U₁.Node,
        IsRootedLeaf T none (some (.inl q₁)) ↔ IsRootedLeaf U₁.tree U₁.root q₁ := by
      intro q₁
      constructor
      · intro hleaf w₁ hw₁
        have hd : IsDescendant T none (some (.inl w₁)) (some (.inl q₁)) :=
          (hdesc_inl w₁ _).mpr (Or.inr ⟨q₁, rfl, hw₁⟩)
        exact hinl_inj (hleaf _ hd)
      · intro hleaf₁ w hw
        rcases w with _ | (w₁ | w₂)
        · rw [hdesc_none] at hw; cases hw
        · rw [hdesc_inl] at hw
          rcases hw with hno | ⟨z₁, hz₁, hdesc₁⟩
          · cases hno
          · have hzq : q₁ = z₁ := hinl_inj hz₁
            subst hzq
            rw [hleaf₁ w₁ hdesc₁]
        · rw [hdesc_inr] at hw
          rcases hw with hno | ⟨z₂, hz₂, _⟩
          · cases hno
          · cases hz₂
    have hleaf_inr : ∀ q₂ : U₂.Node,
        IsRootedLeaf T none (some (.inr q₂)) ↔ IsRootedLeaf U₂.tree U₂.root q₂ := by
      intro q₂
      constructor
      · intro hleaf w₂ hw₂
        have hd : IsDescendant T none (some (.inr w₂)) (some (.inr q₂)) :=
          (hdesc_inr w₂ _).mpr (Or.inr ⟨q₂, rfl, hw₂⟩)
        exact hinr_inj (hleaf _ hd)
      · intro hleaf₂ w hw
        rcases w with _ | (w₁ | w₂)
        · rw [hdesc_none] at hw; cases hw
        · rw [hdesc_inl] at hw
          rcases hw with hno | ⟨z₁, hz₁, _⟩
          · cases hno
          · cases hz₁
        · rw [hdesc_inr] at hw
          rcases hw with hno | ⟨z₂, hz₂, hdesc₂⟩
          · cases hno
          · have hzq : q₂ = z₂ := hinr_inj hz₂
            subst hzq
            rw [hleaf₂ w₂ hdesc₂]
    let leafSumEquiv :
        {q₁ : U₁.Node // IsRootedLeaf U₁.tree U₁.root q₁} ⊕
        {q₂ : U₂.Node // IsRootedLeaf U₂.tree U₂.root q₂} ≃
        {q : NodeJ // IsRootedLeaf T none q} :=
      { toFun := fun s => match s with
          | .inl ⟨q₁, h₁⟩ => ⟨some (.inl q₁), (hleaf_inl q₁).mpr h₁⟩
          | .inr ⟨q₂, h₂⟩ => ⟨some (.inr q₂), (hleaf_inr q₂).mpr h₂⟩
        invFun := fun ⟨q, hq⟩ => match q, hq with
          | none, hq => False.elim (hleaf_none hq)
          | some (.inl q₁), hq => .inl ⟨q₁, (hleaf_inl q₁).mp hq⟩
          | some (.inr q₂), hq => .inr ⟨q₂, (hleaf_inr q₂).mp hq⟩
        left_inv := by rintro (⟨q₁, h₁⟩ | ⟨q₂, h₂⟩) <;> rfl
        right_inv := by
          rintro ⟨_ | (q₁ | q₂), hq⟩
          · exact False.elim (hleaf_none hq)
          · rfl
          · rfl }
    let leafEquivJ : V ≃ {q : NodeJ // IsRootedLeaf T none q} :=
      (Equiv.sumCompl P).symm.trans ((Equiv.sumCongr U₁.leafEquiv U₂.leafEquiv).trans leafSumEquiv)
    let labelJ : NodeJ → ENNReal
      | none => ⊤
      | some (.inl q₁) => U₁.label q₁
      | some (.inr q₂) => U₂.label q₂
    let U : HST V :=
      { Node := NodeJ
        finiteNode := inferInstance
        tree := T
        isTree := hT_tree
        root := none
        leafEquiv := leafEquivJ
        label := labelJ
        label_mono := by
          intro q z hqz
          rcases z with _ | (z₁ | z₂)
          · exact le_top
          · rcases q with _ | (q₁ | q₂)
            · rw [hdesc_none] at hqz; cases hqz
            · rw [hdesc_inl] at hqz
              rcases hqz with hno | ⟨z₁', hz₁', hd₁⟩
              · cases hno
              · have heq : z₁ = z₁' := hinl_inj hz₁'
                subst heq
                exact U₁.label_mono q₁ z₁ hd₁
            · rw [hdesc_inr] at hqz
              rcases hqz with hno | ⟨z₂', hz₂', _⟩
              · cases hno
              · cases hz₂'
          · rcases q with _ | (q₁ | q₂)
            · rw [hdesc_none] at hqz; cases hqz
            · rw [hdesc_inl] at hqz
              rcases hqz with hno | ⟨z₁', hz₁', _⟩
              · cases hno
              · cases hz₁'
            · rw [hdesc_inr] at hqz
              rcases hqz with hno | ⟨z₂', hz₂', hd₂⟩
              · cases hno
              · have heq : z₂ = z₂' := hinr_inj hz₂'
                subst heq
                exact U₂.label_mono q₂ z₂ hd₂
        label_eq_zero_iff := by
          intro q
          rcases q with _ | (q₁ | q₂)
          · dsimp [labelJ]
            exact ⟨fun h => absurd h ENNReal.top_ne_zero, fun h => absurd h hleaf_none⟩
          · dsimp [labelJ]
            rw [U₁.label_eq_zero_iff, hleaf_inl]
          · dsimp [labelJ]
            rw [U₂.label_eq_zero_iff, hleaf_inr] }
    obtain ⟨hTJ_eq_lca, _⟩ := tree_lca_props hT_tree none
    obtain ⟨_, hU₁_isLCA⟩ := tree_lca_props U₁.isTree U₁.root
    obtain ⟨_, hU₂_isLCA⟩ := tree_lca_props U₂.isTree U₂.root
    have hleaf_val_pos : ∀ (u : V) (hu : P u),
        (U.leafEquiv u).1 = some (.inl (U₁.leafEquiv ⟨u, hu⟩).1) := by
      intro u hu
      change (leafSumEquiv ((Equiv.sumCongr U₁.leafEquiv U₂.leafEquiv) ((Equiv.sumCompl P).symm u))).1 = _
      rw [Equiv.sumCompl_symm_apply_of_pos hu]
      rfl
    have hleaf_val_neg : ∀ (u : V) (hu : ¬ P u),
        (U.leafEquiv u).1 = some (.inr (U₂.leafEquiv ⟨u, hu⟩).1) := by
      intro u hu
      change (leafSumEquiv ((Equiv.sumCongr U₁.leafEquiv U₂.leafEquiv) ((Equiv.sumCompl P).symm u))).1 = _
      rw [Equiv.sumCompl_symm_apply_of_neg hu]
      rfl
    refine ⟨U, ?_, ?_, ?_⟩
    · intro u v hu hv
      unfold HST.dist
      rw [hleaf_val_pos u hu, hleaf_val_pos v hv]
      let x₁ := (U₁.leafEquiv ⟨u, hu⟩).1
      let y₁ := (U₁.leafEquiv ⟨v, hv⟩).1
      let z₁ := rootedLCA U₁.tree U₁.root x₁ y₁
      have hz₁ : IsLCA U₁.tree U₁.root x₁ y₁ z₁ := hU₁_isLCA x₁ y₁
      have hzJ : IsLCA T none (some (.inl x₁)) (some (.inl y₁)) (some (.inl z₁)) := by
        refine ⟨(hdesc_inl x₁ _).mpr (Or.inr ⟨z₁, rfl, hz₁.1⟩),
                (hdesc_inl y₁ _).mpr (Or.inr ⟨z₁, rfl, hz₁.2.1⟩), ?_⟩
        intro w hwx hwy
        rw [hdesc_inl] at hwx hwy
        rcases hwx with rfl | ⟨w₁, rfl, hwx₁⟩
        · exact (hdesc_inl z₁ none).mpr (Or.inl rfl)
        · rcases hwy with hno | ⟨w₁', hw₁', hwy₁⟩
          · cases hno
          · have heq : w₁ = w₁' := hinl_inj hw₁'
            subst heq
            exact (hdesc_inl z₁ _).mpr (Or.inr ⟨w₁, rfl, hz₁.2.2 w₁ hwx₁ hwy₁⟩)
      change labelJ (rootedLCA T none (some (.inl x₁)) (some (.inl y₁))) = U₁.label z₁
      rw [hTJ_eq_lca hzJ]
    · intro u v hu hv
      unfold HST.dist
      rw [hleaf_val_neg u hu, hleaf_val_neg v hv]
      let x₂ := (U₂.leafEquiv ⟨u, hu⟩).1
      let y₂ := (U₂.leafEquiv ⟨v, hv⟩).1
      let z₂ := rootedLCA U₂.tree U₂.root x₂ y₂
      have hz₂ : IsLCA U₂.tree U₂.root x₂ y₂ z₂ := hU₂_isLCA x₂ y₂
      have hzJ : IsLCA T none (some (.inr x₂)) (some (.inr y₂)) (some (.inr z₂)) := by
        refine ⟨(hdesc_inr x₂ _).mpr (Or.inr ⟨z₂, rfl, hz₂.1⟩),
                (hdesc_inr y₂ _).mpr (Or.inr ⟨z₂, rfl, hz₂.2.1⟩), ?_⟩
        intro w hwx hwy
        rw [hdesc_inr] at hwx hwy
        rcases hwx with rfl | ⟨w₂, rfl, hwx₂⟩
        · exact (hdesc_inr z₂ none).mpr (Or.inl rfl)
        · rcases hwy with hno | ⟨w₂', hw₂', hwy₂⟩
          · cases hno
          · have heq : w₂ = w₂' := hinr_inj hw₂'
            subst heq
            exact (hdesc_inr z₂ _).mpr (Or.inr ⟨w₂, rfl, hz₂.2.2 w₂ hwx₂ hwy₂⟩)
      change labelJ (rootedLCA T none (some (.inr x₂)) (some (.inr y₂))) = U₂.label z₂
      rw [hTJ_eq_lca hzJ]
    · intro u v hcross
      unfold HST.dist
      rcases hcross with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [hleaf_val_pos u hu, hleaf_val_neg v hv]
        let x₁ := (U₁.leafEquiv ⟨u, hu⟩).1
        let y₂ := (U₂.leafEquiv ⟨v, hv⟩).1
        have hzJ : IsLCA T none (some (.inl x₁)) (some (.inr y₂)) none := by
          refine ⟨(hdesc_inl x₁ none).mpr (Or.inl rfl),
                  (hdesc_inr y₂ none).mpr (Or.inl rfl), ?_⟩
          intro w hwx hwy
          rw [hdesc_inl] at hwx
          rw [hdesc_inr] at hwy
          rcases hwx with rfl | ⟨w₁, rfl, _⟩
          · exact (hdesc_none none).mpr rfl
          · rcases hwy with hno | ⟨w₂, hw₂, _⟩
            · cases hno
            · cases hw₂
        change labelJ (rootedLCA T none (some (.inl x₁)) (some (.inr y₂))) = ⊤
        rw [hTJ_eq_lca hzJ]
      · rw [hleaf_val_neg u hu, hleaf_val_pos v hv]
        let x₂ := (U₂.leafEquiv ⟨u, hu⟩).1
        let y₁ := (U₁.leafEquiv ⟨v, hv⟩).1
        have hzJ : IsLCA T none (some (.inr x₂)) (some (.inl y₁)) none := by
          refine ⟨(hdesc_inr x₂ none).mpr (Or.inl rfl),
                  (hdesc_inl y₁ none).mpr (Or.inl rfl), ?_⟩
          intro w hwx hwy
          rw [hdesc_inr] at hwx
          rw [hdesc_inl] at hwy
          rcases hwx with rfl | ⟨w₂, rfl, _⟩
          · exact (hdesc_none none).mpr rfl
          · rcases hwy with hno | ⟨w₁, hw₁, _⟩
            · cases hno
            · cases hw₁
        change labelJ (rootedLCA T none (some (.inr x₂)) (some (.inl y₁))) = ⊤
        rw [hTJ_eq_lca hzJ]
  have induced_closed_hopDist : ∀ {V : Type} (G : SimpleGraph V) (w : Sym2 V → ℝ)
      (Q : V → Prop) (hQ_closed : ∀ {x y : V}, G.Adj x y → Q x → Q y),
      (∀ {u v : V}, Q u → ¬ Q v → ∀ H : ℕ, hopDist G w H u v = ⊤) ∧
      (∀ (H : ℕ) (x y : {u : V // Q u}),
        hopDist (G.induce {u : V | Q u}) (fun e => w (Sym2.map Subtype.val e)) H x y =
          hopDist G w H x.1 y.1) := by
    clear h_core hst_two_regime_polylog_bounds pmf_map_tsum pmf_bind_map_tsum tree_lca_props join_two_hsts
    intro V G w Q hQ_closed
    let G_Q : SimpleGraph {u : V // Q u} := G.induce {u : V | Q u}
    let w_Q : Sym2 {u : V // Q u} → ℝ := fun e => w (Sym2.map Subtype.val e)
    have h_walk_stay : ∀ {u v : V} (p : G.Walk u v), Q u → Q v := by
      intro u v p
      induction p with
      | nil => exact id
      | @cons x y z hadj q ih => intro hx; exact ih (hQ_closed hadj hx)
    have h_walk_down : ∀ {u v : V} (p : G.Walk u v) (hu : Q u) (hv : Q v),
        ∃ q : G_Q.Walk ⟨u, hu⟩ ⟨v, hv⟩, q.length = p.length ∧ walkWeight w_Q q = walkWeight w p := by
      intro u v p
      induction p with
      | nil =>
        intro hu _
        exact ⟨SimpleGraph.Walk.nil, rfl, rfl⟩
      | @cons x y z hadj r ih =>
        intro hx hz
        have hy : Q y := hQ_closed hadj hx
        obtain ⟨q', hlen, hwt⟩ := ih hy hz
        have hadj_Q : G_Q.Adj ⟨x, hx⟩ ⟨y, hy⟩ := hadj
        refine ⟨SimpleGraph.Walk.cons hadj_Q q', ?_, ?_⟩
        · simp [hlen]
        · unfold walkWeight at hwt ⊢
          simp [w_Q, hwt]
    have h_walk_up : ∀ {x y : {u : V // Q u}} (q : G_Q.Walk x y),
        ∃ p : G.Walk x.1 y.1, p.length = q.length ∧ walkWeight w p = walkWeight w_Q q := by
      intro x y q
      induction q with
      | nil => exact ⟨SimpleGraph.Walk.nil, rfl, rfl⟩
      | @cons a b c hadj_Q r ih =>
        obtain ⟨p', hlen, hwt⟩ := ih
        have hadj : G.Adj a.1 b.1 := hadj_Q
        refine ⟨SimpleGraph.Walk.cons hadj p', ?_, ?_⟩
        · simp [hlen]
        · unfold walkWeight at hwt ⊢
          simp [w_Q, hwt]
    refine ⟨?_, ?_⟩
    · intro u v hu hnv H
      unfold hopDist
      rw [iInf_eq_top]
      intro p
      exfalso
      exact hnv (h_walk_stay p hu)
    · intro H x y
      apply le_antisymm
      · apply le_iInf₂; intro p hp
        obtain ⟨q, hlen, hwt⟩ := h_walk_down p x.2 y.2
        change _ ≤ ENNReal.ofReal (walkWeight w p)
        rw [← hwt]
        exact iInf₂_le q (hlen ▸ hp)
      · apply le_iInf₂; intro q hq
        obtain ⟨p, hlen, hwt⟩ := h_walk_up q
        change _ ≤ ENNReal.ofReal (walkWeight w_Q q)
        rw [← hwt]
        exact iInf₂_le p (hlen ▸ hq)
  have weight_doubling_hst_reduction : ∀ {V : Type} (G : SimpleGraph V) (w : Sym2 V → ℝ)
      (h : ℕ) (ε : ℝ) (β : ℕ) (K α : ℝ) (D₂ : PMF (HST V × Set V)),
      IsStochasticHCRamseyHSTEmbedding G (fun e => 2 * w e) h ε β K α D₂ →
      ∃ D : PMF (HST V × Set V), IsStochasticHCRamseyHSTEmbedding G w h ε β K α D := by
    clear h_core hst_two_regime_polylog_bounds pmf_bind_map_tsum tree_lca_props join_two_hsts induced_closed_hopDist
    intro V G w h ε β K α D₂ hD₂
    let w₂ : Sym2 V → ℝ := fun e => 2 * w e
    have h_ww : ∀ {u v : V} (p : G.Walk u v), walkWeight w₂ p = 2 * walkWeight w p := by
      intro u v p
      unfold walkWeight
      dsimp [w₂]
      rw [List.sum_map_mul_left]
    have h_hd : ∀ (H : ℕ) (u v : V), hopDist G w₂ H u v = 2 * hopDist G w H u v := by
      intro H u v
      have h2_ne0 : (2 : ENNReal) ≠ 0 := by norm_num
      have h2_netop : (2 : ENNReal) ≠ ⊤ := by norm_num
      have h_inv_two : (2 : ENNReal)⁻¹ * 2 = 1 := ENNReal.inv_mul_cancel h2_ne0 h2_netop
      have h_two_inv : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by rw [mul_comm]; exact h_inv_two
      have h_ofReal2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
      apply le_antisymm
      · have h_half : (2 : ENNReal)⁻¹ * hopDist G w₂ H u v ≤ hopDist G w H u v := by
          apply le_iInf₂; intro p hp
          calc (2 : ENNReal)⁻¹ * hopDist G w₂ H u v
              ≤ (2 : ENNReal)⁻¹ * ENNReal.ofReal (walkWeight w₂ p) :=
                mul_le_mul_right (iInf₂_le p hp) _
            _ = (2 : ENNReal)⁻¹ * (2 * ENNReal.ofReal (walkWeight w p)) := by
                rw [h_ww p, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), h_ofReal2]
            _ = ENNReal.ofReal (walkWeight w p) := by
                rw [← mul_assoc, h_inv_two, one_mul]
        calc hopDist G w₂ H u v
            = 1 * hopDist G w₂ H u v := (one_mul _).symm
          _ = (2 * (2 : ENNReal)⁻¹) * hopDist G w₂ H u v := by rw [h_two_inv]
          _ = 2 * ((2 : ENNReal)⁻¹ * hopDist G w₂ H u v) := mul_assoc _ _ _
          _ ≤ 2 * hopDist G w H u v := mul_le_mul_right h_half _
      · apply le_iInf₂; intro p hp
        calc 2 * hopDist G w H u v
            ≤ 2 * ENNReal.ofReal (walkWeight w p) := mul_le_mul_right (iInf₂_le p hp) _
          _ = ENNReal.ofReal (walkWeight w₂ p) := by
              rw [h_ww p, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), h_ofReal2]
    have h2inv_ne0 : (2 : ENNReal)⁻¹ ≠ 0 := by simp
    have h_inv_two : (2 : ENNReal)⁻¹ * 2 = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    let halfHST : HST V → HST V := fun U =>
      { Node := U.Node
        finiteNode := U.finiteNode
        tree := U.tree
        isTree := U.isTree
        root := U.root
        leafEquiv := U.leafEquiv
        label := fun q => (2 : ENNReal)⁻¹ * U.label q
        label_mono := fun q z hqz => mul_le_mul_right (U.label_mono q z hqz) _
        label_eq_zero_iff := fun q => by
          rw [mul_eq_zero, U.label_eq_zero_iff]
          exact ⟨fun h_or => h_or.resolve_left h2inv_ne0, fun hleaf => Or.inr hleaf⟩ }
    let f : HST V × Set V → HST V × Set V := fun p => (halfHST p.1, p.2)
    refine ⟨D₂.map f, ?_⟩
    rcases hD₂ with ⟨hβ, hK, hα, hfin, hstretch, hdist, hexcl, hexp⟩
    refine ⟨hβ, hK, hα, ?_, ?_, ?_, ?_, ?_⟩
    · rw [PMF.support_map]; exact hfin.image f
    · intro p hp u v
      rw [PMF.support_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      have h1 := hstretch q hq u v
      rw [h_hd] at h1
      calc hopDist G w (β * h) u v
          = ((2 : ENNReal)⁻¹ * 2) * hopDist G w (β * h) u v := by rw [h_inv_two, one_mul]
        _ = (2 : ENNReal)⁻¹ * (2 * hopDist G w (β * h) u v) := mul_assoc _ _ _
        _ ≤ (2 : ENNReal)⁻¹ * q.1.dist u v := mul_le_mul_right h1 _
        _ = (halfHST q.1).dist u v := rfl
    · intro p hp u hu v
      rw [PMF.support_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      have h1 := hdist q hq u hu v
      rw [h_hd] at h1
      calc (halfHST q.1).dist u v
          = (2 : ENNReal)⁻¹ * q.1.dist u v := rfl
        _ ≤ (2 : ENNReal)⁻¹ * (ENNReal.ofReal K * (2 * hopDist G w h u v)) :=
            mul_le_mul_right h1 _
        _ = ((2 : ENNReal)⁻¹ * 2) * (ENNReal.ofReal K * hopDist G w h u v) := by ring
        _ = ENNReal.ofReal K * hopDist G w h u v := by rw [h_inv_two, one_mul]
    · intro v
      rw [PMF.toOuterMeasure_map_apply]
      exact hexcl v
    · intro u v
      have h_saved : ∀ q : HST V × Set V,
          savedHSTDist (halfHST q.1) q.2 u v = (2 : ENNReal)⁻¹ * savedHSTDist q.1 q.2 u v := by
        intro q; unfold savedHSTDist; split_ifs
        · rfl
        · simp
      have h_tsum := pmf_map_tsum D₂ f (fun p => savedHSTDist p.1 p.2 u v)
      rw [h_tsum]
      have h_factor : (∑' q : HST V × Set V, D₂ q * savedHSTDist (halfHST q.1) q.2 u v) =
          (2 : ENNReal)⁻¹ * ∑' q : HST V × Set V, D₂ q * savedHSTDist q.1 q.2 u v := by
        rw [← ENNReal.tsum_mul_left]
        congr 1; ext q
        rw [h_saved q]; ring
      rw [h_factor]
      have h1 := hexp u v
      rw [h_hd] at h1
      calc (2 : ENNReal)⁻¹ * ∑' q : HST V × Set V, D₂ q * savedHSTDist q.1 q.2 u v
          ≤ (2 : ENNReal)⁻¹ * (ENNReal.ofReal α * (2 * hopDist G w h u v)) :=
            mul_le_mul_right h1 _
        _ = ((2 : ENNReal)⁻¹ * 2) * (ENNReal.ofReal α * hopDist G w h u v) := by ring
        _ = ENNReal.ofReal α * hopDist G w h u v := by rw [h_inv_two, one_mul]
  have hop_saturation_hst_shift : ∀ (n : ℕ) (_hn : 2 ≤ n) (V : Type) [Fintype V]
      (hV : Fintype.card V = n) (G : SimpleGraph V) (w : Sym2 V → ℝ)
      (hw : ∀ e ∈ G.edgeSet, 0 ≤ w e) (h : ℕ) (hh1 : 1 ≤ h) (hhn : h ≤ n)
      (ε : ℝ) (β₀ : ℕ) (K₀ α₀ : ℝ) (D : PMF (HST V × Set V)),
      IsStochasticHCRamseyHSTEmbedding G w n ε β₀ K₀ α₀ D →
      IsStochasticHCRamseyHSTEmbedding G w h ε (max β₀ n) K₀ α₀ D := by
    clear h_core hst_two_regime_polylog_bounds pmf_map_tsum pmf_bind_map_tsum tree_lca_props
      join_two_hsts induced_closed_hopDist weight_doubling_hst_reduction
    intro n _hn V _ hV G w hw h hh1 hhn ε β₀ K₀ α₀ D hD
    letI : DecidableEq V := Classical.decEq V
    have h_ww_nonneg : ∀ {u v : V} (p : G.Walk u v), 0 ≤ walkWeight w p := by
      intro u v p
      unfold walkWeight
      apply List.sum_nonneg
      intro x hx
      rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
      exact hw e (p.edges_subset_edgeSet he)
    have h_ww_append : ∀ {u v z : V} (p : G.Walk u v) (q : G.Walk v z),
        walkWeight w (p.append q) = walkWeight w p + walkWeight w q := by
      intro u v z p q
      unfold walkWeight
      rw [SimpleGraph.Walk.edges_append, List.map_append, List.sum_append]
    have h_ww_cons : ∀ {u v' v : V} (ha : G.Adj u v') (q : G.Walk v' v),
        walkWeight w (SimpleGraph.Walk.cons ha q) = w s(u, v') + walkWeight w q := by
      intro u v' v ha q
      unfold walkWeight
      simp
    have h_bypass : ∀ {u v : V} (p : G.Walk u v), walkWeight w p.bypass ≤ walkWeight w p := by
      intro u v p
      induction p with
      | nil => simp [SimpleGraph.Walk.bypass]
      | @cons u v' v ha q ih =>
        have hw_edge : 0 ≤ w s(u, v') := hw s(u, v') (G.mem_edgeSet.mpr ha)
        rw [h_ww_cons]
        dsimp [SimpleGraph.Walk.bypass]
        split_ifs with hm
        · have hsplit := q.bypass.take_spec hm
          have hsum := congrArg (walkWeight w) hsplit
          rw [h_ww_append] at hsum
          have htake : 0 ≤ walkWeight w (q.bypass.takeUntil u hm) := h_ww_nonneg _
          linarith
        · rw [h_ww_cons]
          linarith
    have h_hd_mono : ∀ u v : V, hopDist G w n u v ≤ hopDist G w h u v := by
      intro u v
      apply le_iInf₂; intro p hp
      exact iInf₂_le p (hp.trans hhn)
    rcases hD with ⟨hβ₀, hK₀, hα₀, hfin, hstretch, hdist, hexcl, hexp⟩
    refine ⟨le_trans hβ₀ (le_max_left _ _), hK₀, hα₀, hfin, ?_, ?_, hexcl, ?_⟩
    · intro p₀ hp₀ u v
      refine le_trans ?_ (hstretch p₀ hp₀ u v)
      apply le_iInf₂; intro p _hp
      have hlen_lt : p.bypass.length < n := by
        rw [← hV]
        exact p.bypass_isPath.length_lt
      have hlen_le : p.bypass.length ≤ max β₀ n * h := by
        have h1 : n ≤ max β₀ n := le_max_right _ _
        have h2 : max β₀ n * 1 ≤ max β₀ n * h := Nat.mul_le_mul_left _ hh1
        omega
      exact le_trans (iInf₂_le p.bypass hlen_le) (ENNReal.ofReal_le_ofReal (h_bypass p))
    · intro p₀ hp₀ u hu v
      exact le_trans (hdist p₀ hp₀ u hu v) (mul_le_mul_right (h_hd_mono u v) _)
    · intro u v
      exact le_trans (hexp u v) (mul_le_mul_right (h_hd_mono u v) _)
  have disconnected_hst_gluing_reduction : ∀ (n : ℕ) (_hn : 2 ≤ n) (B : ℝ) (hB : 2 ≤ B)
      (ε : ℝ) (hε : 0 ≤ ε) (β₀ : ℕ) (hβ₀ : 1 ≤ β₀)
      (K₀ α₀ : ℝ) (hK₀ : 1 ≤ K₀) (hα₀ : 1 ≤ α₀),
      (∀ (W : Type) [Fintype W],
        2 ≤ Fintype.card W → Fintype.card W ≤ n →
        ∀ (G_W : SimpleGraph W) (w_W : Sym2 W → ℝ),
          (∀ e ∈ G_W.edgeSet, 2 ≤ w_W e) →
          (∀ u v : W, hopDist G_W w_W n u v ≤ ENNReal.ofReal ((n : ℝ) * B)) →
          ∃ D_W : PMF (HST W × Set W),
            IsStochasticHCRamseyHSTEmbedding G_W w_W n ε β₀ K₀ α₀ D_W) →
      ∀ (V : Type) [Fintype V],
        1 ≤ Fintype.card V → Fintype.card V ≤ n →
        ∀ (G : SimpleGraph V) (w : Sym2 V → ℝ),
          (∀ e ∈ G.edgeSet, 2 ≤ w e ∧ w e ≤ B) →
          ∃ D : PMF (HST V × Set V),
            IsStochasticHCRamseyHSTEmbedding G w n ε β₀ K₀ α₀ D := by
    clear h_core hst_two_regime_polylog_bounds pmf_map_tsum tree_lca_props
      weight_doubling_hst_reduction hop_saturation_hst_shift
    intro n _hn B hB ε hε β₀ hβ₀ K₀ α₀ hK₀ hα₀ h_conn_diam
    suffices h_ind : ∀ m : ℕ, 1 ≤ m → m ≤ n →
        ∀ (V : Type) [Fintype V], Fintype.card V = m →
          ∀ (G : SimpleGraph V) (w : Sym2 V → ℝ),
            (∀ e ∈ G.edgeSet, 2 ≤ w e ∧ w e ≤ B) →
            ∃ D : PMF (HST V × Set V),
              IsStochasticHCRamseyHSTEmbedding G w n ε β₀ K₀ α₀ D by
      intro V _ h1 hnV G w hw
      exact h_ind (Fintype.card V) h1 hnV V rfl G w hw
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm1 hmn V _ hcard G w hw
      by_cases hm_eq1 : m = 1
      · have hcard1 : Fintype.card V = 1 := hcard.trans hm_eq1
        obtain ⟨v₀, hv₀⟩ := Fintype.card_eq_one_iff.mp hcard1
        have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        have hUnit_tree : (⊥ : SimpleGraph Unit).IsTree := by
          refine ⟨⟨fun x y => ?_⟩, ?_⟩
          · cases x; cases y; exact SimpleGraph.Reachable.refl ()
          · intro x c hc
            cases c with
            | nil => exact hc.ne_nil rfl
            | cons hadj _ => exact hadj
        have hUnit_leaf : IsRootedLeaf (⊥ : SimpleGraph Unit) () () := by
          intro x _; cases x; rfl
        let singleHST : HST V :=
          { Node := Unit
            finiteNode := inferInstance
            tree := ⊥
            isTree := hUnit_tree
            root := ()
            leafEquiv :=
              { toFun := fun _ => ⟨(), hUnit_leaf⟩
                invFun := fun _ => v₀
                left_inv := fun v => (hv₀ v).symm
                right_inv := fun ⟨(), _⟩ => rfl }
            label := fun _ => 0
            label_mono := fun _ _ _ => le_refl 0
            label_eq_zero_iff := fun q => by
              cases q; exact ⟨fun _ => hUnit_leaf, fun _ => rfl⟩ }
        let D : PMF (HST V × Set V) := PMF.pure (singleHST, Set.univ)
        refine ⟨D, hβ₀, hK₀, hα₀, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp [D]; rw [PMF.support_pure]; exact Set.finite_singleton _
        · intro p hp u v
          dsimp [D] at hp; rw [PMF.support_pure, Set.mem_singleton_iff] at hp; subst hp
          have huv : u = v := Subsingleton.elim u v
          subst huv
          refine le_trans (iInf₂_le SimpleGraph.Walk.nil (Nat.zero_le _)) ?_
          simp [walkWeight, singleHST, HST.dist]
        · intro p hp u _ v
          dsimp [D] at hp; rw [PMF.support_pure, Set.mem_singleton_iff] at hp; subst hp
          change (0 : ENNReal) ≤ _
          exact zero_le _
        · intro v
          dsimp [D]
          rw [PMF.toOuterMeasure_pure_apply]
          simp [hε]
        · intro u v
          have hzero : ∀ p : HST V × Set V, D p * savedHSTDist p.1 p.2 u v = 0 := by
            intro p
            by_cases hp : p ∈ D.support
            · dsimp [D] at hp; rw [PMF.support_pure, Set.mem_singleton_iff] at hp; subst hp
              simp [savedHSTDist, singleHST, HST.dist]
            · have hp0 : D p = 0 := by simpa [PMF.mem_support_iff] using hp
              simp [hp0]
          simp_rw [hzero, tsum_zero]
          exact zero_le _
      · have hm2 : 2 ≤ m := by omega
        by_cases hG_conn : G.Connected
        · letI : DecidableEq V := Classical.decEq V
          have hdiam : ∀ u v : V, hopDist G w n u v ≤ ENNReal.ofReal ((n : ℝ) * B) := by
            intro u v
            obtain ⟨p⟩ := hG_conn u v
            let q := p.bypass
            have hq_len : q.length ≤ n := by
              have hlt : q.length < Fintype.card V := p.bypass_isPath.length_lt
              omega
            have hq_wt : walkWeight w q ≤ (n : ℝ) * B := by
              unfold walkWeight
              have hbound : ∀ x ∈ q.edges.map w, x ≤ B := by
                intro x hx
                rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
                exact (hw e (q.edges_subset_edgeSet he)).2
              have hsum := List.sum_le_card_nsmul (q.edges.map w) B hbound
              simp only [List.length_map, SimpleGraph.Walk.length_edges, nsmul_eq_mul] at hsum
              have hqlen_cast : (q.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hq_len
              calc (q.edges.map w).sum
                  ≤ (q.length : ℝ) * B := hsum
                _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_right hqlen_cast (by linarith)
            exact le_trans (iInf₂_le q hq_len) (ENNReal.ofReal_le_ofReal hq_wt)
          exact h_conn_diam V (by omega) (by omega) G w (fun e he => (hw e he).1) hdiam
        · have hV_nonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
          let v₀ : V := Classical.arbitrary V
          let P : V → Prop := G.Reachable v₀
          letI : DecidablePred P := Classical.decPred P
          let V₁ := {u : V // P u}
          let V₂ := {u : V // ¬ P u}
          have hV₁_pos : 1 ≤ Fintype.card V₁ :=
            @Fintype.card_pos V₁ _ ⟨⟨v₀, SimpleGraph.Reachable.refl v₀⟩⟩
          have hV₂_nonempty : Nonempty V₂ := by
            by_contra h_empty
            rw [not_nonempty_iff] at h_empty
            apply hG_conn
            refine ⟨fun x y => ?_⟩
            have hx : P x := by by_contra hnx; exact h_empty.false ⟨x, hnx⟩
            have hy : P y := by by_contra hny; exact h_empty.false ⟨y, hny⟩
            exact hx.symm.trans hy
          have hV₂_pos : 1 ≤ Fintype.card V₂ := @Fintype.card_pos V₂ _ hV₂_nonempty
          have hcard_sum : Fintype.card V₁ + Fintype.card V₂ = m := by
            rw [← Fintype.card_sum]
            exact (Fintype.card_congr (Equiv.sumCompl P)).trans hcard
          have hP_closed : ∀ {x y : V}, G.Adj x y → P x → P y :=
            fun hadj hx => hx.trans hadj.reachable
          have hnP_closed : ∀ {x y : V}, G.Adj x y → ¬ P x → ¬ P y :=
            fun hadj hnx hy => hnx (hy.trans hadj.symm.reachable)
          obtain ⟨hcross1, hhop1⟩ := induced_closed_hopDist G w P hP_closed
          obtain ⟨hcross2, hhop2⟩ := induced_closed_hopDist G w (fun u => ¬ P u) hnP_closed
          let G₁ : SimpleGraph V₁ := G.induce {u : V | P u}
          let w₁ : Sym2 V₁ → ℝ := fun e => w (Sym2.map Subtype.val e)
          let G₂ : SimpleGraph V₂ := G.induce {u : V | ¬ P u}
          let w₂ : Sym2 V₂ → ℝ := fun e => w (Sym2.map Subtype.val e)
          have hw₁ : ∀ e ∈ G₁.edgeSet, 2 ≤ w₁ e ∧ w₁ e ≤ B := by
            intro e he
            induction e using Sym2.ind with
            | _ x y =>
              have hadj : G.Adj x.1 y.1 := G₁.mem_edgeSet.mp he
              exact hw s(x.1, y.1) (G.mem_edgeSet.mpr hadj)
          have hw₂ : ∀ e ∈ G₂.edgeSet, 2 ≤ w₂ e ∧ w₂ e ≤ B := by
            intro e he
            induction e using Sym2.ind with
            | _ x y =>
              have hadj : G.Adj x.1 y.1 := G₂.mem_edgeSet.mp he
              exact hw s(x.1, y.1) (G.mem_edgeSet.mpr hadj)
          obtain ⟨D₁, hD₁⟩ := ih (Fintype.card V₁) (by omega) hV₁_pos (by omega) V₁ rfl G₁ w₁ hw₁
          obtain ⟨D₂, hD₂⟩ := ih (Fintype.card V₂) (by omega) hV₂_pos (by omega) V₂ rfl G₂ w₂ hw₂
          choose joinHST hjoin_pos hjoin_neg hjoin_cross using
            fun (U₁ : HST V₁) (U₂ : HST V₂) => join_two_hsts P U₁ U₂
          let glueSet : Set V₁ → Set V₂ → Set V := fun M₁ M₂ =>
            {u : V | if h : P u then ⟨u, h⟩ ∈ M₁ else ⟨u, h⟩ ∈ M₂}
          let glue : (HST V₁ × Set V₁) → (HST V₂ × Set V₂) → (HST V × Set V) :=
            fun p₁ p₂ => (joinHST p₁.1 p₂.1, glueSet p₁.2 p₂.2)
          let D : PMF (HST V × Set V) := D₁.bind (fun p₁ => D₂.map (fun p₂ => glue p₁ p₂))
          rcases hD₁ with ⟨_, _, _, hfin₁, hstr₁, hdist₁, hexcl₁, hexp₁⟩
          rcases hD₂ with ⟨_, _, _, hfin₂, hstr₂, hdist₂, hexcl₂, hexp₂⟩
          refine ⟨D, hβ₀, hK₀, hα₀, ?_, ?_, ?_, ?_, ?_⟩
          · dsimp [D]
            rw [PMF.support_bind]
            refine hfin₁.biUnion (fun p₁ _ => ?_)
            rw [PMF.support_map]
            exact hfin₂.image _
          · intro p hp u v
            dsimp [D] at hp
            rw [PMF.support_bind, Set.mem_iUnion₂] at hp
            rcases hp with ⟨p₁, hp₁_in, hp₂_map⟩
            rw [PMF.support_map] at hp₂_map
            rcases hp₂_map with ⟨p₂, hp₂_in, rfl⟩
            by_cases hu : P u <;> by_cases hv : P v
            · rw [← hhop1 (β₀ * n) ⟨u, hu⟩ ⟨v, hv⟩, hjoin_pos p₁.1 p₂.1 u v hu hv]
              exact hstr₁ p₁ hp₁_in ⟨u, hu⟩ ⟨v, hv⟩
            · rw [hjoin_cross p₁.1 p₂.1 u v (Or.inl ⟨hu, hv⟩)]
              exact le_top
            · rw [hjoin_cross p₁.1 p₂.1 u v (Or.inr ⟨hu, hv⟩)]
              exact le_top
            · rw [← hhop2 (β₀ * n) ⟨u, hu⟩ ⟨v, hv⟩, hjoin_neg p₁.1 p₂.1 u v hu hv]
              exact hstr₂ p₂ hp₂_in ⟨u, hu⟩ ⟨v, hv⟩
          · intro p hp u hu_mem v
            dsimp [D] at hp
            rw [PMF.support_bind, Set.mem_iUnion₂] at hp
            rcases hp with ⟨p₁, hp₁_in, hp₂_map⟩
            rw [PMF.support_map] at hp₂_map
            rcases hp₂_map with ⟨p₂, hp₂_in, rfl⟩
            have hK₀_ne0 : ENNReal.ofReal K₀ ≠ 0 :=
              ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
            by_cases hu : P u <;> by_cases hv : P v
            · have hu₁ : ⟨u, hu⟩ ∈ p₁.2 := by simpa [glue, glueSet, hu] using hu_mem
              rw [← hhop1 n ⟨u, hu⟩ ⟨v, hv⟩, hjoin_pos p₁.1 p₂.1 u v hu hv]
              exact hdist₁ p₁ hp₁_in ⟨u, hu⟩ hu₁ ⟨v, hv⟩
            · rw [hcross1 hu hv n, ENNReal.mul_top hK₀_ne0]
              exact le_top
            · rw [hcross2 hu (not_not.mpr hv) n, ENNReal.mul_top hK₀_ne0]
              exact le_top
            · have hu₂ : ⟨u, hu⟩ ∈ p₂.2 := by simpa [glue, glueSet, hu] using hu_mem
              rw [← hhop2 n ⟨u, hu⟩ ⟨v, hv⟩, hjoin_neg p₁.1 p₂.1 u v hu hv]
              exact hdist₂ p₂ hp₂_in ⟨u, hu⟩ hu₂ ⟨v, hv⟩
          · intro v
            dsimp [D]
            rw [PMF.toOuterMeasure_bind_apply]
            by_cases hv : P v
            · have h_eq : (∑' p₁, D₁ p₁ * (D₂.map (fun p₂ => glue p₁ p₂)).toOuterMeasure {p | v ∉ p.2}) =
                  D₁.toOuterMeasure {p₁ | ⟨v, hv⟩ ∉ p₁.2} := by
                rw [PMF.toOuterMeasure_apply]
                congr 1; ext p₁
                rw [PMF.toOuterMeasure_map_apply]
                by_cases hmem : ⟨v, hv⟩ ∈ p₁.2
                · have hpre : (fun p₂ => glue p₁ p₂) ⁻¹' {p | v ∉ p.2} = ∅ := by
                    ext p₂; simp [glue, glueSet, hv, hmem]
                  simp [hpre, hmem]
                · have hpre : (fun p₂ => glue p₁ p₂) ⁻¹' {p | v ∉ p.2} = Set.univ := by
                    ext p₂; simp [glue, glueSet, hv, hmem]
                  have huniv : D₂.toOuterMeasure Set.univ = 1 := by
                    rw [PMF.toOuterMeasure_apply]; simp [PMF.tsum_coe]
                  simp [hpre, huniv, hmem]
              rw [h_eq]
              exact hexcl₁ ⟨v, hv⟩
            · have h_eq : (∑' p₁, D₁ p₁ * (D₂.map (fun p₂ => glue p₁ p₂)).toOuterMeasure {p | v ∉ p.2}) =
                  D₂.toOuterMeasure {p₂ | ⟨v, hv⟩ ∉ p₂.2} := by
                have hpre : ∀ p₁, (fun p₂ => glue p₁ p₂) ⁻¹' {p | v ∉ p.2} = {p₂ | ⟨v, hv⟩ ∉ p₂.2} := by
                  intro p₁; ext p₂; simp [glue, glueSet, hv]
                simp_rw [PMF.toOuterMeasure_map_apply, hpre]
                rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
              rw [h_eq]
              exact hexcl₂ ⟨v, hv⟩
          · intro u v
            have hα₀_ne0 : ENNReal.ofReal α₀ ≠ 0 :=
              ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
            have hD_def : D = D₁.bind (fun p₁ => D₂.map (fun p₂ => glue p₁ p₂)) := rfl
            by_cases hu : P u <;> by_cases hv : P v
            · rw [hD_def, pmf_bind_map_tsum]
              have hsaved : ∀ p₁ p₂, savedHSTDist (glue p₁ p₂).1 (glue p₁ p₂).2 u v =
                  savedHSTDist p₁.1 p₁.2 ⟨u, hu⟩ ⟨v, hv⟩ := by
                intro p₁ p₂
                unfold savedHSTDist
                have hmem_iff : (u ∈ (glue p₁ p₂).2 ∧ v ∈ (glue p₁ p₂).2) ↔
                    (⟨u, hu⟩ ∈ p₁.2 ∧ ⟨v, hv⟩ ∈ p₁.2) := by
                  simp [glue, glueSet, hu, hv]
                split_ifs with h1 h2 h2
                · exact hjoin_pos p₁.1 p₂.1 u v hu hv
                · exfalso; exact h2 (hmem_iff.mp h1)
                · exfalso; exact h1 (hmem_iff.mpr h2)
                · rfl
              simp_rw [hsaved, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
                       ← hhop1 n ⟨u, hu⟩ ⟨v, hv⟩]
              exact hexp₁ ⟨u, hu⟩ ⟨v, hv⟩
            · rw [hcross1 hu hv n, ENNReal.mul_top hα₀_ne0]
              exact le_top
            · rw [hcross2 hu (not_not.mpr hv) n, ENNReal.mul_top hα₀_ne0]
              exact le_top
            · rw [hD_def, pmf_bind_map_tsum]
              have hsaved : ∀ p₁ p₂, savedHSTDist (glue p₁ p₂).1 (glue p₁ p₂).2 u v =
                  savedHSTDist p₂.1 p₂.2 ⟨u, hu⟩ ⟨v, hv⟩ := by
                intro p₁ p₂
                unfold savedHSTDist
                have hmem_iff : (u ∈ (glue p₁ p₂).2 ∧ v ∈ (glue p₁ p₂).2) ↔
                    (⟨u, hu⟩ ∈ p₂.2 ∧ ⟨v, hv⟩ ∈ p₂.2) := by
                  simp [glue, glueSet, hu, hv]
                split_ifs with h1 h2 h2
                · exact hjoin_neg p₁.1 p₂.1 u v hu hv
                · exfalso; exact h2 (hmem_iff.mp h1)
                · exfalso; exact h1 (hmem_iff.mpr h2)
                · rfl
              simp_rw [hsaved]
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ← hhop2 n ⟨u, hu⟩ ⟨v, hv⟩]
              exact hexp₂ ⟨u, hu⟩ ⟨v, hv⟩
  have heavy_edge_completion_hst_reduction : ∀ (n : ℕ) (hn : 2 ≤ n) (V : Type) [Fintype V]
      (hV : Fintype.card V = n) (G : SimpleGraph V) (w : Sym2 V → ℝ) (B : ℝ) (hB : 2 ≤ B)
      (hw : ∀ e ∈ G.edgeSet, 2 ≤ w e ∧ w e ≤ B)
      (h : ℕ) (hh1 : 1 ≤ h) (hhn : h ≤ n)
      (ε : ℝ) (β₀ : ℕ) (K₀ α₀ ω : ℝ)
      (hK₀ : 1 ≤ K₀) (hω : 2 * K₀ * ((n : ℝ) * B) ≤ ω),
      (∀ (G' : SimpleGraph V) (w' : Sym2 V → ℝ),
        (∀ e ∈ G'.edgeSet, 2 ≤ w' e) →
        (∀ u v : V, hopDist G' w' h u v ≤ ENNReal.ofReal ω) →
        ∃ D' : PMF (HST V × Set V), IsStochasticHCRamseyHSTEmbedding G' w' h ε β₀ K₀ α₀ D') →
      ∃ D : PMF (HST V × Set V), IsStochasticHCRamseyHSTEmbedding G w h ε β₀ K₀ α₀ D := by
    clear h_core hst_two_regime_polylog_bounds pmf_bind_map_tsum tree_lca_props join_two_hsts
      induced_closed_hopDist weight_doubling_hst_reduction hop_saturation_hst_shift
      disconnected_hst_gluing_reduction
    intro n hn V _ _hV G w B hB hw h hh1 hhn ε β₀ K₀ α₀ ω hK₀ hω h_cb
    classical
    let M_fin : ℝ := (n : ℝ) * B
    let τ : ℝ := K₀ * M_fin
    have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hM_ge4 : 4 ≤ M_fin := by dsimp [M_fin]; nlinarith
    have hB_le_M : B ≤ M_fin := by dsimp [M_fin]; nlinarith
    have hM_le_τ : M_fin ≤ τ := by dsimp [τ]; nlinarith
    have hτ_pos : 0 < τ := by linarith
    have hτ_lt_ω : τ < ω := by dsimp [τ] at *; linarith
    have hω_ge2 : 2 ≤ ω := by linarith
    have hB_le_ω : B ≤ ω := by linarith
    let G' : SimpleGraph V := ⊤
    let w' : Sym2 V → ℝ := fun e => if e ∈ G.edgeSet then w e else ω
    have hw'_ge2 : ∀ e : Sym2 V, 2 ≤ w' e := by
      intro e; dsimp [w']; split_ifs with he
      · exact (hw e he).1
      · exact hω_ge2
    have hw'_le_ω : ∀ e : Sym2 V, w' e ≤ ω := by
      intro e; dsimp [w']; split_ifs with he
      · exact le_trans (hw e he).2 hB_le_ω
      · exact le_refl ω
    have hG'_diam : ∀ u v : V, hopDist G' w' h u v ≤ ENNReal.ofReal ω := by
      intro u v
      by_cases huv : u = v
      · subst huv
        refine le_trans (iInf₂_le SimpleGraph.Walk.nil (Nat.zero_le h)) ?_
        simp [walkWeight]
      · have hadj : G'.Adj u v := by simpa [G'] using huv
        let p : G'.Walk u v := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
        refine le_trans (iInf₂_le p hh1) ?_
        apply ENNReal.ofReal_le_ofReal
        simpa [p, walkWeight] using hw'_le_ω s(u, v)
    obtain ⟨D', hD'⟩ := h_cb G' w' (fun e _ => hw'_ge2 e) hG'_diam
    have h_hd_le : ∀ (H : ℕ) (u v : V), hopDist G' w' H u v ≤ hopDist G w H u v := by
      intro H u v
      apply le_iInf₂; intro p hp
      let p' : G'.Walk u v := p.map (SimpleGraph.Hom.ofLE (le_top : G ≤ G'))
      have hp'_len : p'.length ≤ H := by simpa [p'] using hp
      have hp'_wt : walkWeight w' p' = walkWeight w p := by
        unfold walkWeight
        have hedges : p'.edges = p.edges := by simp [p', SimpleGraph.Walk.edges_map]
        rw [hedges]
        congr 1
        apply List.map_congr_left
        intro e he
        have heG : e ∈ G.edgeSet := p.edges_subset_edgeSet he
        simp [w', heG]
      rw [← hp'_wt]
      exact iInf₂_le p' hp'_len
    have h_transfer : ∀ {u v : V} (p' : G'.Walk u v),
        walkWeight w' p' < ω → ∃ p : G.Walk u v, p.length = p'.length ∧ walkWeight w p = walkWeight w' p' := by
      intro u v p' hlt
      have heG : ∀ e ∈ p'.edges, e ∈ G.edgeSet := by
        intro e he
        by_contra hnot
        have hw'e : w' e = ω := by simp [w', hnot]
        have hmem : w' e ∈ p'.edges.map w' := List.mem_map_of_mem he
        have hnn : ∀ x ∈ p'.edges.map w', 0 ≤ x := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨e', _, rfl⟩
          linarith [hw'_ge2 e']
        have hle : w' e ≤ walkWeight w' p' := List.single_le_sum hnn (w' e) hmem
        linarith
      let p : G.Walk u v := p'.transfer G heG
      refine ⟨p, SimpleGraph.Walk.length_transfer p' heG, ?_⟩
      unfold walkWeight
      rw [SimpleGraph.Walk.edges_transfer]
      congr 1
      apply List.map_congr_left
      intro e he
      have := heG e he
      simp [w', this]
    have h_hd_eq_of_lt : ∀ (H : ℕ) (u v : V),
        hopDist G' w' H u v < ENNReal.ofReal ω → hopDist G w H u v ≤ hopDist G' w' H u v := by
      intro H u v hlt
      have hex : ∃ (q' : G'.Walk u v), q'.length ≤ H ∧ walkWeight w' q' < ω := by
        unfold hopDist at hlt
        rw [iInf_lt_iff] at hlt
        rcases hlt with ⟨q', hlt⟩
        rw [iInf_lt_iff] at hlt
        rcases hlt with ⟨hq', hlt⟩
        exact ⟨q', hq', (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < ω)).mp hlt⟩
      apply le_iInf₂; intro p' hp'
      by_cases hwt : walkWeight w' p' < ω
      · obtain ⟨p, hplen, hpwt⟩ := h_transfer p' hwt
        rw [← hpwt]
        exact iInf₂_le p (hplen ▸ hp')
      · push_neg at hwt
        rcases hex with ⟨q', hq'len, hq'wt⟩
        obtain ⟨q, hqlen, hqwt⟩ := h_transfer q' hq'wt
        calc hopDist G w H u v
            ≤ ENNReal.ofReal (walkWeight w q) := iInf₂_le q (hqlen ▸ hq'len)
          _ = ENNReal.ofReal (walkWeight w' q') := by rw [hqwt]
          _ ≤ ENNReal.ofReal ω := ENNReal.ofReal_le_ofReal (le_of_lt hq'wt)
          _ ≤ ENNReal.ofReal (walkWeight w' p') := ENNReal.ofReal_le_ofReal hwt
    have h_fin_bound : ∀ u v : V, hopDist G w h u v ≠ ⊤ →
        hopDist G w h u v ≤ ENNReal.ofReal M_fin ∧ hopDist G' w' h u v = hopDist G w h u v := by
      intro u v hne
      have hlt_top : hopDist G w h u v < ⊤ := lt_top_iff_ne_top.mpr hne
      unfold hopDist at hlt_top
      rw [iInf_lt_iff] at hlt_top
      rcases hlt_top with ⟨p, hlt_top⟩
      rw [iInf_lt_iff] at hlt_top
      rcases hlt_top with ⟨hp, _⟩
      have hp_wt : walkWeight w p ≤ M_fin := by
        unfold walkWeight
        have hbound : ∀ x ∈ p.edges.map w, x ≤ B := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
          exact (hw e (p.edges_subset_edgeSet he)).2
        have hsum := List.sum_le_card_nsmul (p.edges.map w) B hbound
        simp only [List.length_map, SimpleGraph.Walk.length_edges, nsmul_eq_mul] at hsum
        have hplen : (p.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast (hp.trans hhn)
        have hB0 : 0 ≤ B := by linarith
        calc (p.edges.map w).sum
            ≤ (p.length : ℝ) * B := hsum
          _ ≤ (n : ℝ) * B := mul_le_mul_of_nonneg_right hplen hB0
      have h1 : hopDist G w h u v ≤ ENNReal.ofReal M_fin :=
        le_trans (iInf₂_le p hp) (ENNReal.ofReal_le_ofReal hp_wt)
      refine ⟨h1, le_antisymm (h_hd_le h u v) ?_⟩
      apply h_hd_eq_of_lt h u v
      calc hopDist G' w' h u v
          ≤ hopDist G w h u v := h_hd_le h u v
        _ ≤ ENNReal.ofReal M_fin := h1
        _ < ENNReal.ofReal ω := (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < ω)).mpr (by linarith)
    let thresholdHST : HST V → HST V := fun U' =>
      { Node := U'.Node
        finiteNode := U'.finiteNode
        tree := U'.tree
        isTree := U'.isTree
        root := U'.root
        leafEquiv := U'.leafEquiv
        label := fun q => if U'.label q ≤ ENNReal.ofReal τ then U'.label q else ⊤
        label_mono := fun q z hqz => by
          have hm := U'.label_mono q z hqz
          split_ifs with h1 h2 h2
          · exact hm
          · exact le_top
          · exfalso; exact h1 (le_trans hm h2)
          · exact le_top
        label_eq_zero_iff := fun q => by
          rw [← U'.label_eq_zero_iff]
          split_ifs with h1
          · rfl
          · constructor
            · intro htop; exact absurd htop ENNReal.top_ne_zero
            · intro h0; exfalso; exact h1 (by simp [h0]) }
    let f : HST V × Set V → HST V × Set V := fun p => (thresholdHST p.1, p.2)
    refine ⟨D'.map f, ?_⟩
    rcases hD' with ⟨hβ₀, _, hα₀, hfin, hstretch, hdist, hexcl, hexp⟩
    refine ⟨hβ₀, hK₀, hα₀, ?_, ?_, ?_, ?_, ?_⟩
    · rw [PMF.support_map]; exact hfin.image f
    · intro p hp u v
      rw [PMF.support_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      change hopDist G w (β₀ * h) u v ≤
        if q.1.dist u v ≤ ENNReal.ofReal τ then q.1.dist u v else ⊤
      split_ifs with hle
      · have hlt : hopDist G' w' (β₀ * h) u v < ENNReal.ofReal ω :=
          lt_of_le_of_lt (le_trans (hstretch q hq u v) hle)
            ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < ω)).mpr hτ_lt_ω)
        exact le_trans (h_hd_eq_of_lt (β₀ * h) u v hlt) (hstretch q hq u v)
      · exact le_top
    · intro p hp u hu v
      rw [PMF.support_map] at hp
      rcases hp with ⟨q, hq, rfl⟩
      by_cases htop : hopDist G w h u v = ⊤
      · rw [htop, ENNReal.mul_top]
        · exact le_top
        · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
      · obtain ⟨hM, heq⟩ := h_fin_bound u v htop
        have hq_le : q.1.dist u v ≤ ENNReal.ofReal K₀ * hopDist G w h u v := by
          rw [← heq]; exact hdist q hq u hu v
        have hq_τ : q.1.dist u v ≤ ENNReal.ofReal τ := by
          calc q.1.dist u v
              ≤ ENNReal.ofReal K₀ * hopDist G w h u v := hq_le
            _ ≤ ENNReal.ofReal K₀ * ENNReal.ofReal M_fin := mul_le_mul_right hM _
            _ = ENNReal.ofReal τ := (ENNReal.ofReal_mul (by linarith)).symm
        change (if q.1.dist u v ≤ ENNReal.ofReal τ then q.1.dist u v else ⊤) ≤ _
        rw [if_pos hq_τ]
        exact hq_le
    · intro v
      rw [PMF.toOuterMeasure_map_apply]
      exact hexcl v
    · intro u v
      by_cases htop : hopDist G w h u v = ⊤
      · rw [htop, ENNReal.mul_top]
        · exact le_top
        · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
      · obtain ⟨hM, heq⟩ := h_fin_bound u v htop
        rw [pmf_map_tsum]
        dsimp only [f]
        have hsame : ∀ q : HST V × Set V,
            D' q * savedHSTDist (thresholdHST q.1) q.2 u v = D' q * savedHSTDist q.1 q.2 u v := by
          intro q
          by_cases hq_supp : q ∈ D'.support
          · unfold savedHSTDist
            split_ifs with huv_mem
            · have hq_τ : q.1.dist u v ≤ ENNReal.ofReal τ := by
                calc q.1.dist u v
                    ≤ ENNReal.ofReal K₀ * hopDist G' w' h u v := hdist q hq_supp u huv_mem.1 v
                  _ = ENNReal.ofReal K₀ * hopDist G w h u v := by rw [heq]
                  _ ≤ ENNReal.ofReal K₀ * ENNReal.ofReal M_fin := mul_le_mul_right hM _
                  _ = ENNReal.ofReal τ := (ENNReal.ofReal_mul (by linarith)).symm
              change D' q * (if q.1.dist u v ≤ ENNReal.ofReal τ then q.1.dist u v else ⊤) = _
              rw [if_pos hq_τ]
            · rfl
          · have hq0 : D' q = 0 := by
              simpa [PMF.mem_support_iff] using hq_supp
            simp [hq0]
        simp_rw [hsame, ← heq]
        exact hexp u v
  
  intro c₀ hc₀
  obtain ⟨C, hC_ge1, h_regimes⟩ := hst_two_regime_polylog_bounds c₀ hc₀
  refine ⟨C, 2, hC_ge1, ?_⟩
  intro n hn V _ hcard G w hw h hh1 hhn ε hε0 hε1
  let B : ℝ := 2 * (n : ℝ) ^ c₀
  let M_fin : ℝ := (n : ℝ) * B
  let w₂ : Sym2 V → ℝ := fun e => 2 * w e
  have hn_cast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnc0_ge1 : 1 ≤ (n : ℝ) ^ c₀ :=
    Real.one_le_rpow (by linarith only [hn_cast]) (by linarith only [hc₀])
  have hB_ge2 : 2 ≤ B := by dsimp [B]; linarith only [hnc0_ge1]
  have hM_ge2 : 2 ≤ M_fin := by
    dsimp [M_fin]
    calc (2 : ℝ) ≤ 2 * 2 := by norm_num
      _ ≤ (n : ℝ) * B := mul_le_mul hn_cast hB_ge2 (by norm_num) (by linarith only [hn_cast])
  have hw₂ : ∀ e ∈ G.edgeSet, 2 ≤ w₂ e ∧ w₂ e ≤ B := by
    intro e he
    obtain ⟨h1, h2⟩ := hw e he
    exact ⟨by dsimp [w₂]; linarith only [h1], by dsimp [w₂, B]; linarith only [h2]⟩
  rcases h_regimes n hn ε hε0 hε1 with hRegA | hRegB
  · dsimp only at hRegA
    rcases hRegA with ⟨hβA_ge1, hKA_ge1, hαA_ge1, hmax_bd, hKA_bd, hαA_bd⟩
    let β_A : ℕ := 2 * hstRadiusSteps n M_fin ε * (hstPhaseCount n + 1)
    let K_A : ℝ := 8 * (hstRadiusSteps n M_fin ε : ℝ) * (hstPhaseCount n : ℝ)
    let α_A : ℝ := 256 * (hstPhaseCount n : ℝ) * Real.logb 2 (n : ℝ) *
      (1 + 2 * hstTruncDelta n) ^ (Real.logb 2 M_fin)
    obtain ⟨D_n, hD_n⟩ := disconnected_hst_gluing_reduction n hn B hB_ge2 ε (le_of_lt hε0)
      β_A hβA_ge1 K_A α_A hKA_ge1 hαA_ge1
      (fun W _ hW2 hWn G_W w_W hw_W hdiam_W =>
        h_core n W hW2 hWn G_W w_W hw_W n (by omega) M_fin hM_ge2 hdiam_W ε hε0 hε1)
      V (by omega) (by omega) G w₂ hw₂
    have hD_h := hop_saturation_hst_shift n hn V hcard G w₂
      (fun e he => by linarith [(hw₂ e he).1]) h hh1 hhn ε β_A K_A α_A D_n hD_n
    obtain ⟨D, hD⟩ := weight_doubling_hst_reduction G w h ε (max β_A n) K_A α_A D_n hD_h
    refine ⟨max β_A n, K_A, α_A, D, hD.1, hD.2.1, hD.2.2.1, hD, ?_, ?_, ?_⟩
    · rw [mul_assoc]; exact hmax_bd
    · rw [mul_assoc]; exact hKA_bd
    · rw [mul_assoc]; exact hαA_bd
  · dsimp only at hRegB
    rcases hRegB with ⟨hΦB_ge2, hKB_ge1, h_self_cons, hβB_bd, hKB_bd, hαB_bd⟩
    let Φ_B : ℝ := (n : ℝ) ^ (c₀ + 5)
    let β_B : ℕ := 2 * hstRadiusSteps n Φ_B ε * (hstPhaseCount n + 1)
    let K_B : ℝ := 8 * (hstRadiusSteps n Φ_B ε : ℝ) * (hstPhaseCount n : ℝ)
    let α_B : ℝ := 256 * (hstPhaseCount n : ℝ) * Real.logb 2 (n : ℝ) *
      (1 + 2 * hstTruncDelta n) ^ (Real.logb 2 Φ_B)
    obtain ⟨D₂, hD₂⟩ := heavy_edge_completion_hst_reduction n hn V hcard G w₂ B hB_ge2 hw₂
      h hh1 hhn ε β_B K_B α_B Φ_B hKB_ge1 h_self_cons
      (fun G' w' hw' hdiam' =>
        h_core n V (by omega) (by omega) G' w' hw' h hh1 Φ_B hΦB_ge2 hdiam' ε hε0 hε1)
    obtain ⟨D, hD⟩ := weight_doubling_hst_reduction G w h ε β_B K_B α_B D₂ hD₂
    refine ⟨β_B, K_B, α_B, D, hD.1, hD.2.1, hD.2.2.1, hD, ?_, ?_, ?_⟩
    · rw [mul_assoc]; exact hβB_bd
    · rw [mul_assoc]; exact hKB_bd
    · rw [mul_assoc]; exact hαB_bd

theorem exists_bounded_degree_expander : ∃ (D : ℕ) (φ : ℝ), 3 ≤ D ∧ 0 < φ ∧
      ∀ N₀ : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N₀ ≤ n ∧ IsBoundedDegreeEdgeExpander G D φ :=
by
  have h_s1 : ∀ (n d : ℕ) (π : Fin d → Equiv.Perm (Fin n)),
      ∃ G : SimpleGraph (Fin n),
        (∀ v : Fin n, (G.neighborSet v).ncard ≤ 2 * d) ∧
        (∀ S : Finset (Fin n),
          ((Finset.univ.biUnion (fun i : Fin d => S.image (π i))) \ S).card ≤
            {p : Fin n × Fin n |
              p.1 ∈ (S : Set (Fin n)) ∧ p.2 ∉ (S : Set (Fin n)) ∧ G.Adj p.1 p.2}.ncard) := by
    intro n d π
    let G : SimpleGraph (Fin n) :=
      { Adj := fun u v => u ≠ v ∧ ∃ i : Fin d, (π i u = v ∨ π i v = u)
        symm := by
          intro u v ⟨hne, i, h⟩
          exact ⟨hne.symm, i, h.symm⟩
        loopless := by
          intro u ⟨hne, _⟩
          exact hne rfl }
    refine ⟨G, ?_, ?_⟩
    · intro v
      let C : Finset (Fin n) :=
        Finset.univ.biUnion (fun i : Fin d => ({π i v, (π i).symm v} : Finset (Fin n)))
      have hsub : G.neighborSet v ⊆ (C : Set (Fin n)) := by
        intro w hw
        rcases hw with ⟨_, i, hw1 | hw2⟩
        · exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ i, by simp [hw1]⟩)
        · have hw2' : w = (π i).symm v := by
            rw [← hw2, Equiv.symm_apply_apply]
          exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ i, by simp [hw2']⟩)
      have hle1 : (G.neighborSet v).ncard ≤ C.card := by
        calc (G.neighborSet v).ncard
            ≤ (C : Set (Fin n)).ncard := Set.ncard_le_ncard hsub C.finite_toSet
          _ = C.card := Set.ncard_coe_finset C
      have hle2 : C.card ≤ 2 * d := by
        calc C.card
            ≤ ∑ i ∈ (Finset.univ : Finset (Fin d)),
                ({π i v, (π i).symm v} : Finset (Fin n)).card := Finset.card_biUnion_le
          _ ≤ (Finset.univ : Finset (Fin d)).card • 2 := by
              refine Finset.sum_le_card_nsmul _ _ 2 ?_
              intro i _
              exact (Finset.card_insert_le _ _).trans (by simp)
          _ = 2 * d := by
              simp [Nat.mul_comm]
      exact hle1.trans hle2
    · intro S
      let B : Finset (Fin n) :=
        (Finset.univ.biUnion (fun i : Fin d => S.image (π i))) \ S
      let Eout : Set (Fin n × Fin n) :=
        {p : Fin n × Fin n |
          p.1 ∈ (S : Set (Fin n)) ∧ p.2 ∉ (S : Set (Fin n)) ∧ G.Adj p.1 p.2}
      have hex : ∀ w : B, ∃ u : Fin n, u ∈ S ∧ G.Adj u w.1 := by
        intro w
        have hw : w.1 ∈ B := w.2
        rw [Finset.mem_sdiff, Finset.mem_biUnion] at hw
        rcases hw with ⟨⟨i, _, hi⟩, hnotS⟩
        rcases Finset.mem_image.mp hi with ⟨u, huS, huw⟩
        have hne : u ≠ w.1 := by
          intro heq
          exact hnotS (heq ▸ huS)
        exact ⟨u, huS, hne, i, Or.inl huw⟩
      let g : B → Fin n × Fin n := fun w => (Classical.choose (hex w), w.1)
      have hg_inj : Function.Injective g := by
        intro w₁ w₂ h
        exact Subtype.ext (congrArg Prod.snd h)
      let F : Finset (Fin n × Fin n) := (Finset.univ : Finset B).image g
      have hF_sub : (F : Set (Fin n × Fin n)) ⊆ Eout := by
        intro p hp
        rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨w, _, rfl⟩
        have hspec := Classical.choose_spec (hex w)
        have hw_notS : w.1 ∉ S := (Finset.mem_sdiff.mp w.2).2
        exact ⟨Finset.mem_coe.mpr hspec.1, fun h => hw_notS (Finset.mem_coe.mp h), hspec.2⟩
      calc B.card
          = (Finset.univ : Finset B).card := by simp
        _ = F.card := (Finset.card_image_of_injective _ hg_inj).symm
        _ = (F : Set (Fin n × Fin n)).ncard := (Set.ncard_coe_finset F).symm
        _ ≤ Eout.ncard := Set.ncard_le_ncard hF_sub (Set.toFinite Eout)
  have h_s2 : ∀ (n : ℕ) (S U : Finset (Fin n)),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => S.image σ ⊆ U)).card ≤
        U.card.choose S.card * S.card.factorial * (n - S.card).factorial := by
    intro n S U
    let s := S.card
    let P := Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => S.image σ ⊆ U)
    have hS_card : Fintype.card S = s := Fintype.card_coe S
    have hSc_card : Fintype.card (Sᶜ : Finset (Fin n)) = n - s := by
      rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    let eS : S ≃ Fin s := Fintype.equivFinOfCardEq hS_card
    let eSc : (Sᶜ : Finset (Fin n)) ≃ Fin (n - s) := Fintype.equivFinOfCardEq hSc_card
    let eJ : ∀ J : U.powersetCard s, J.1 ≃ Fin s := fun J =>
      Fintype.equivFinOfCardEq ((Fintype.card_coe J.1).trans (Finset.mem_powersetCard.mp J.2).2)
    let eJc : ∀ J : U.powersetCard s, (J.1ᶜ : Finset (Fin n)) ≃ Fin (n - s) := fun J =>
      Fintype.equivFinOfCardEq (by
        rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin,
          (Finset.mem_powersetCard.mp J.2).2])
    let Jof : P → U.powersetCard s := fun σ =>
      ⟨S.image σ.1, Finset.mem_powersetCard.mpr
        ⟨(Finset.mem_filter.mp σ.2).2, Finset.card_image_of_injective S σ.1.injective⟩⟩
    let b1 : ∀ σ : P, S ≃ (Jof σ).1 := fun σ =>
      { toFun := fun x => ⟨σ.1 x.1, Finset.mem_image_of_mem σ.1 x.2⟩
        invFun := fun y => ⟨σ.1.symm y.1, by
          rcases Finset.mem_image.mp y.2 with ⟨x, hx, hxy⟩
          rw [← hxy, Equiv.symm_apply_apply]
          exact hx⟩
        left_inv := fun x => Subtype.ext (σ.1.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (σ.1.apply_symm_apply y.1) }
    let b2 : ∀ σ : P, (Sᶜ : Finset (Fin n)) ≃ ((Jof σ).1ᶜ : Finset (Fin n)) := fun σ =>
      { toFun := fun x => ⟨σ.1 x.1, by
          rw [Finset.mem_compl]
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨z, hz, hzx⟩
          have heq : z = x.1 := σ.1.injective hzx
          exact (Finset.mem_compl.mp x.2) (heq ▸ hz)⟩
        invFun := fun y => ⟨σ.1.symm y.1, by
          rw [Finset.mem_compl]
          intro hmem
          have hy : y.1 ∈ S.image σ.1 := by
            rw [← σ.1.apply_symm_apply y.1]
            exact Finset.mem_image_of_mem σ.1 hmem
          exact (Finset.mem_compl.mp y.2) hy⟩
        left_inv := fun x => Subtype.ext (σ.1.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (σ.1.apply_symm_apply y.1) }
    let Y := U.powersetCard s × Equiv.Perm (Fin s) × Equiv.Perm (Fin (n - s))
    let Φ : P → Y := fun σ =>
      (Jof σ, eS.symm.trans ((b1 σ).trans (eJ (Jof σ))),
        eSc.symm.trans ((b2 σ).trans (eJc (Jof σ))))
    let decode : Y → Fin n → Fin n := fun t x =>
      if hx : x ∈ S then
        ((eJ t.1).symm (t.2.1 (eS ⟨x, hx⟩))).1
      else
        ((eJc t.1).symm (t.2.2 (eSc ⟨x, Finset.mem_compl.mpr hx⟩))).1
    have hdecode : ∀ (σ : P) (x : Fin n), decode (Φ σ) x = σ.1 x := by
      intro σ x
      dsimp only [decode, Φ]
      split_ifs with hx
      · simp [b1]
      · simp [b2]
    have hΦ_inj : Function.Injective Φ := by
      intro σ₁ σ₂ h
      apply Subtype.ext
      ext x
      rw [← hdecode σ₁ x, ← hdecode σ₂ x, h]
    have hcard_le : Fintype.card P ≤ Fintype.card Y := Fintype.card_le_of_injective Φ hΦ_inj
    calc P.card
        = Fintype.card P := (Fintype.card_coe P).symm
      _ ≤ Fintype.card Y := hcard_le
      _ = U.card.choose s * s.factorial * (n - s).factorial := by
          change Fintype.card (U.powersetCard s × Equiv.Perm (Fin s) × Equiv.Perm (Fin (n - s))) = _
          rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Finset.card_powersetCard,
            Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, ← Nat.mul_assoc]
  have h_s3 : ∀ (n s : ℕ), 1 ≤ s → 2 * s ≤ n →
      2 ^ s * n.choose s * (n - s).choose (s / 2) *
        ((s + s / 2).choose s * s.factorial * (n - s).factorial) ^ 32 ≤
      (n.factorial) ^ 32 := by
    have h_pow_fact : ∀ a b : ℕ, a ^ b * a.factorial ≤ (a + b).factorial := by
      intro a b
      induction b with
      | zero => simp
      | succ b ih =>
        calc a ^ (b + 1) * a.factorial
            = a * (a ^ b * a.factorial) := by ring
          _ ≤ a * (a + b).factorial := Nat.mul_le_mul_left a ih
          _ ≤ (a + b + 1) * (a + b).factorial := Nat.mul_le_mul_right _ (by omega)
          _ = (a + (b + 1)).factorial := by
              rw [← Nat.add_assoc, ← Nat.factorial_succ]
    have h_kk : ∀ k : ℕ, k ^ k ≤ 8 ^ k * k.factorial := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        rcases (by omega : k = 0 ∨ k = 1 ∨ (2 ≤ k ∧ k % 2 = 0) ∨ (3 ≤ k ∧ k % 2 = 1)) with
          rfl | rfl | ⟨hk2, heven⟩ | ⟨hk3, hodd⟩
        · simp
        · simp
        · let m := k / 2
          have hk_eq : k = 2 * m := by omega
          have hm_lt : m < k := by omega
          have ihm : m ^ m ≤ 8 ^ m * m.factorial := ih m hm_lt
          have hmf : m ^ m * m.factorial ≤ (2 * m).factorial := by
            have h := h_pow_fact m m
            rwa [← two_mul] at h
          have h48 : 2 ^ (2 * m) ≤ 8 ^ m := by
            calc 2 ^ (2 * m) = (2 ^ 2) ^ m := by rw [pow_mul]
              _ ≤ 8 ^ m := Nat.pow_le_pow_left (by omega) m
          rw [hk_eq]
          calc (2 * m) ^ (2 * m)
              = 2 ^ (2 * m) * (m ^ m * m ^ m) := by
                  rw [Nat.mul_pow, show m ^ (2 * m) = m ^ m * m ^ m by rw [two_mul, pow_add]]
            _ ≤ 8 ^ m * ((8 ^ m * m.factorial) * m ^ m) :=
                  Nat.mul_le_mul h48 (Nat.mul_le_mul_right (m ^ m) ihm)
            _ = 8 ^ (2 * m) * (m ^ m * m.factorial) := by
                  rw [two_mul m, pow_add]; ring
            _ ≤ 8 ^ (2 * m) * (2 * m).factorial :=
                  Nat.mul_le_mul_left _ hmf
        · let m := k / 2
          have hk_eq : k = 2 * m + 1 := by omega
          have hm1_lt : m + 1 < k := by omega
          have ihm : (m + 1) ^ (m + 1) ≤ 8 ^ (m + 1) * (m + 1).factorial := ih (m + 1) hm1_lt
          have hmf : (m + 1) ^ m * (m + 1).factorial ≤ (2 * m + 1).factorial := by
            have h := h_pow_fact (m + 1) m
            have heq : m + 1 + m = 2 * m + 1 := by omega
            rwa [heq] at h
          have h28 : 2 ^ (2 * m + 1) ≤ 8 ^ m := by
            calc 2 ^ (2 * m + 1)
                ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by omega) (by omega)
              _ = (2 ^ 3) ^ m := by rw [pow_mul]
              _ = 8 ^ m := by norm_num
          rw [hk_eq]
          calc (2 * m + 1) ^ (2 * m + 1)
              ≤ (2 * (m + 1)) ^ (2 * m + 1) := Nat.pow_le_pow_left (by omega) _
            _ = 2 ^ (2 * m + 1) * ((m + 1) ^ (m + 1) * (m + 1) ^ m) := by
                  rw [Nat.mul_pow]
                  have hexp : 2 * m + 1 = (m + 1) + m := by omega
                  conv_lhs => rhs; rw [hexp, pow_add]
            _ ≤ 8 ^ m * ((8 ^ (m + 1) * (m + 1).factorial) * (m + 1) ^ m) :=
                  Nat.mul_le_mul h28 (Nat.mul_le_mul_right _ ihm)
            _ = 8 ^ (2 * m + 1) * ((m + 1) ^ m * (m + 1).factorial) := by
                  have hexp : 2 * m + 1 = m + (m + 1) := by omega
                  rw [hexp, pow_add]; ring
            _ ≤ 8 ^ (2 * m + 1) * (2 * m + 1).factorial :=
                  Nat.mul_le_mul_left _ hmf
    have h_kk_choose : ∀ m k : ℕ, k ^ k * m.choose k ≤ (8 * m) ^ k := by
      intro m k
      calc k ^ k * m.choose k
          ≤ (8 ^ k * k.factorial) * m.choose k := Nat.mul_le_mul_right _ (h_kk k)
        _ = 8 ^ k * (k.factorial * m.choose k) := by ring
        _ = 8 ^ k * m.descFactorial k := by rw [← Nat.descFactorial_eq_factorial_mul_choose]
        _ ≤ 8 ^ k * m ^ k := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow m k)
        _ = (8 * m) ^ k := by rw [Nat.mul_pow]
    have h_choose_pow : ∀ u m k : ℕ, u ≤ m → u.choose k * m ^ k ≤ m.choose k * u ^ k := by
      intro u m k hum
      have h_desc : u.descFactorial k * m ^ k ≤ m.descFactorial k * u ^ k := by
        induction k with
        | zero => simp
        | succ k ih =>
          have hstep : (u - k) * m ≤ (m - k) * u := by
            rw [Nat.sub_mul, Nat.sub_mul, mul_comm u m]
            exact Nat.sub_le_sub_left (Nat.mul_le_mul_left k hum) (m * u)
          calc u.descFactorial (k + 1) * m ^ (k + 1)
              = ((u - k) * m) * (u.descFactorial k * m ^ k) := by
                  rw [Nat.descFactorial_succ, pow_succ']; ring
            _ ≤ ((m - k) * u) * (m.descFactorial k * u ^ k) :=
                  Nat.mul_le_mul hstep ih
            _ = m.descFactorial (k + 1) * u ^ (k + 1) := by
                  rw [Nat.descFactorial_succ, pow_succ']; ring
      have h_mul : k.factorial * (u.choose k * m ^ k) ≤ k.factorial * (m.choose k * u ^ k) := by
        calc k.factorial * (u.choose k * m ^ k)
            = (k.factorial * u.choose k) * m ^ k := by ring
          _ = u.descFactorial k * m ^ k := by rw [← Nat.descFactorial_eq_factorial_mul_choose]
          _ ≤ m.descFactorial k * u ^ k := h_desc
          _ = (k.factorial * m.choose k) * u ^ k := by rw [Nat.descFactorial_eq_factorial_mul_choose]
          _ = k.factorial * (m.choose k * u ^ k) := by ring
      exact Nat.le_of_mul_le_mul_left h_mul (Nat.factorial_pos k)
    intro n s hs1 hsn
    let r := s / 2
    have h_perm1 : ((s + r).choose s * s.factorial * (n - s).factorial) * n ^ s ≤
        n.factorial * (s + r) ^ s := by
      calc ((s + r).choose s * s.factorial * (n - s).factorial) * n ^ s
          = ((s + r).choose s * n ^ s) * (s.factorial * (n - s).factorial) := by ring
        _ ≤ (n.choose s * (s + r) ^ s) * (s.factorial * (n - s).factorial) :=
              Nat.mul_le_mul_right _ (h_choose_pow (s + r) n s (by omega))
        _ = (n.choose s * s.factorial * (n - s).factorial) * (s + r) ^ s := by ring
        _ = n.factorial * (s + r) ^ s := by
              rw [Nat.choose_mul_factorial_mul_factorial (by omega)]
    have h_perm32 : ((s + r).choose s * s.factorial * (n - s).factorial) ^ 32 * n ^ (32 * s) ≤
        (n.factorial) ^ 32 * (s + r) ^ (32 * s) := by
      calc ((s + r).choose s * s.factorial * (n - s).factorial) ^ 32 * n ^ (32 * s)
          = (((s + r).choose s * s.factorial * (n - s).factorial) * n ^ s) ^ 32 := by
              rw [mul_comm 32 s, pow_mul, ← Nat.mul_pow]
        _ ≤ (n.factorial * (s + r) ^ s) ^ 32 := Nat.pow_le_pow_left h_perm1 32
        _ = (n.factorial) ^ 32 * (s + r) ^ (32 * s) := by
              rw [Nat.mul_pow, ← pow_mul, mul_comm s 32]
    have h_sr_choose : s ^ r * (n - s).choose r ≤ (24 * n) ^ r := by
      rcases (by omega : r = 0 ∨ 1 ≤ r) with hr0 | hr1
      · simp [hr0]
      · calc s ^ r * (n - s).choose r
            ≤ (3 * r) ^ r * (n - s).choose r :=
                Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) r)
          _ = 3 ^ r * (r ^ r * (n - s).choose r) := by rw [Nat.mul_pow]; ring
          _ ≤ 3 ^ r * (8 * (n - s)) ^ r := Nat.mul_le_mul_left _ (h_kk_choose (n - s) r)
          _ ≤ 3 ^ r * (8 * n) ^ r :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) r)
          _ = (24 * n) ^ r := by rw [← Nat.mul_pow, ← Nat.mul_assoc]
    have h_ss_choose : s ^ s * n.choose s ≤ (24 * n) ^ s := by
      exact (h_kk_choose n s).trans (Nat.pow_le_pow_left (by omega) s)
    have h_binom_sr : n.choose s * (n - s).choose r * (s + r) ^ (s + r) ≤
        48 ^ (s + r) * n ^ (s + r) := by
      have hsr_pow : (s + r) ^ (s + r) ≤ 2 ^ (s + r) * (s ^ s * s ^ r) := by
        calc (s + r) ^ (s + r)
            ≤ (2 * s) ^ (s + r) := Nat.pow_le_pow_left (by omega) (s + r)
          _ = 2 ^ (s + r) * (s ^ s * s ^ r) := by rw [Nat.mul_pow, pow_add s s r]
      calc n.choose s * (n - s).choose r * (s + r) ^ (s + r)
          ≤ n.choose s * (n - s).choose r * (2 ^ (s + r) * (s ^ s * s ^ r)) :=
              Nat.mul_le_mul_left _ hsr_pow
        _ = 2 ^ (s + r) * ((s ^ s * n.choose s) * (s ^ r * (n - s).choose r)) := by ring
        _ ≤ 2 ^ (s + r) * ((24 * n) ^ s * (24 * n) ^ r) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul h_ss_choose h_sr_choose)
        _ = 2 ^ (s + r) * (24 * n) ^ (s + r) := by rw [← pow_add]
        _ = 48 ^ (s + r) * n ^ (s + r) := by
              rw [← Nat.mul_pow, ← Nat.mul_assoc]
              have h48 : 2 * 24 = 48 := by norm_num
              rw [h48, Nat.mul_pow]
    have h_ratio : 4 ^ (31 * s - r) * (s + r) ^ (31 * s - r) ≤
        3 ^ (31 * s - r) * n ^ (31 * s - r) := by
      calc 4 ^ (31 * s - r) * (s + r) ^ (31 * s - r)
          = (4 * (s + r)) ^ (31 * s - r) := by rw [Nat.mul_pow]
        _ ≤ (3 * n) ^ (31 * s - r) := Nat.pow_le_pow_left (by omega) _
        _ = 3 ^ (31 * s - r) * n ^ (31 * s - r) := by rw [Nat.mul_pow]
    have h_const : 2 ^ s * 48 ^ (s + r) * 3 ^ (31 * s - r) ≤ 4 ^ (31 * s - r) := by
      have hexp : 31 * s - r = 30 * s + (s - r) := by omega
      have hnum : 2 * 48 ^ 2 * 3 ^ 30 ≤ 4 ^ 30 := by norm_num
      calc 2 ^ s * 48 ^ (s + r) * 3 ^ (31 * s - r)
          ≤ 2 ^ s * 48 ^ (2 * s) * 3 ^ (30 * s + (s - r)) := by
              rw [hexp]
              exact Nat.mul_le_mul_right _
                (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
        _ = (2 * 48 ^ 2 * 3 ^ 30) ^ s * 3 ^ (s - r) := by
              rw [pow_add 3 (30 * s) (s - r), pow_mul 48 2 s, pow_mul 3 30 s,
                Nat.mul_pow, Nat.mul_pow]
              ring
        _ ≤ (4 ^ 30) ^ s * 4 ^ (s - r) :=
              Nat.mul_le_mul (Nat.pow_le_pow_left hnum s) (Nat.pow_le_pow_left (by omega) _)
        _ = 4 ^ (31 * s - r) := by
              rw [← pow_mul 4 30 s, ← pow_add 4 (30 * s) (s - r), ← hexp]
    have h_poly : 2 ^ s * n.choose s * (n - s).choose r * (s + r) ^ (32 * s) ≤ n ^ (32 * s) := by
      have hexp32 : 32 * s = (s + r) + (31 * s - r) := by omega
      have h_mul4 : 4 ^ (31 * s - r) *
          (2 ^ s * n.choose s * (n - s).choose r * (s + r) ^ (32 * s)) ≤
          4 ^ (31 * s - r) * n ^ (32 * s) := by
        calc 4 ^ (31 * s - r) * (2 ^ s * n.choose s * (n - s).choose r * (s + r) ^ (32 * s))
            = 2 ^ s * (n.choose s * (n - s).choose r * (s + r) ^ (s + r)) *
                (4 ^ (31 * s - r) * (s + r) ^ (31 * s - r)) := by
                  rw [hexp32, pow_add]; ring
          _ ≤ 2 ^ s * (48 ^ (s + r) * n ^ (s + r)) *
                (3 ^ (31 * s - r) * n ^ (31 * s - r)) :=
                  Nat.mul_le_mul (Nat.mul_le_mul_left _ h_binom_sr) h_ratio
          _ = (2 ^ s * 48 ^ (s + r) * 3 ^ (31 * s - r)) *
                (n ^ (s + r) * n ^ (31 * s - r)) := by ring
          _ = (2 ^ s * 48 ^ (s + r) * 3 ^ (31 * s - r)) * n ^ (32 * s) := by
                  rw [← pow_add, ← hexp32]
          _ ≤ 4 ^ (31 * s - r) * n ^ (32 * s) := Nat.mul_le_mul_right _ h_const
      exact Nat.le_of_mul_le_mul_left h_mul4 (Nat.pow_pos (by omega))
    have h_final_mul :
        n ^ (32 * s) * (2 ^ s * n.choose s * (n - s).choose r *
          ((s + r).choose s * s.factorial * (n - s).factorial) ^ 32) ≤
        n ^ (32 * s) * (n.factorial) ^ 32 := by
      calc n ^ (32 * s) * (2 ^ s * n.choose s * (n - s).choose r *
            ((s + r).choose s * s.factorial * (n - s).factorial) ^ 32)
          = (2 ^ s * n.choose s * (n - s).choose r) *
              (((s + r).choose s * s.factorial * (n - s).factorial) ^ 32 * n ^ (32 * s)) := by
                ring
        _ ≤ (2 ^ s * n.choose s * (n - s).choose r) *
              ((n.factorial) ^ 32 * (s + r) ^ (32 * s)) :=
                Nat.mul_le_mul_left _ h_perm32
        _ = (n.factorial) ^ 32 *
              (2 ^ s * n.choose s * (n - s).choose r * (s + r) ^ (32 * s)) := by ring
        _ ≤ (n.factorial) ^ 32 * n ^ (32 * s) := Nat.mul_le_mul_left _ h_poly
        _ = n ^ (32 * s) * (n.factorial) ^ 32 := by ring
    exact Nat.le_of_mul_le_mul_left h_final_mul (Nat.pow_pos (by omega))
  have h_s4 : ∀ n : ℕ, 2 ≤ n →
      ∃ π : Fin 32 → Equiv.Perm (Fin n),
        ∀ S : Finset (Fin n), 1 ≤ S.card → 2 * S.card ≤ n →
          S.card / 2 < ((Finset.univ.biUnion (fun i : Fin 32 => S.image (π i))) \ S).card := by
    intro n hn
    classical
    by_contra! h_bad
    let Ω := Fin 32 → Equiv.Perm (Fin n)
    let m := n / 2
    let Slice : ℕ → Finset Ω := fun s =>
      ((Finset.univ : Finset (Fin n)).powersetCard s).biUnion (fun S =>
        (Sᶜ.powersetCard (s / 2)).biUnion (fun T =>
          Fintype.piFinset (fun _ : Fin 32 =>
            Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => S.image σ ⊆ S ∪ T))))
    have h_cover : (Finset.univ : Finset Ω) ⊆ (Finset.Icc 1 m).biUnion Slice := by
      intro π _
      rcases h_bad π with ⟨S, hs1, hsn, hB_le⟩
      let s := S.card
      let r := s / 2
      let B := (Finset.univ.biUnion (fun i : Fin 32 => S.image (π i))) \ S
      have hB_sub_Sc : B ⊆ Sᶜ := by
        intro x hx
        exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
      have hSc_card : Sᶜ.card = n - s := by
        rw [Finset.card_compl, Fintype.card_fin]
      have hsdiff_card : (Sᶜ \ B).card + B.card = n - s := by
        rw [Finset.card_sdiff_add_card_eq_card hB_sub_Sc, hSc_card]
      have hB_le' : B.card ≤ r := hB_le
      have hsn' : 2 * s ≤ n := hsn
      have hr_le : r - B.card ≤ (Sᶜ \ B).card := by omega
      rcases Finset.exists_subset_card_eq hr_le with ⟨C, hC_sub, hC_card⟩
      let T := B ∪ C
      have hdisj_BC : Disjoint B C := by
        rw [Finset.disjoint_left]
        intro x hxB hxC
        exact (Finset.mem_sdiff.mp (hC_sub hxC)).2 hxB
      have hT_sub : T ⊆ Sᶜ := Finset.union_subset hB_sub_Sc (hC_sub.trans Finset.sdiff_subset)
      have hT_card : T.card = r := by
        rw [Finset.card_union_of_disjoint hdisj_BC, hC_card]
        omega
      have hπ_mem : π ∈ Fintype.piFinset (fun _ : Fin 32 =>
          Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => S.image σ ⊆ S ∪ T)) := by
        rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro y hy
        by_cases hyS : y ∈ S
        · exact Finset.mem_union_left T hyS
        · have hyB : y ∈ B := Finset.mem_sdiff.mpr
            ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩, hyS⟩
          exact Finset.mem_union_right S (Finset.mem_union_left C hyB)
      have hs_le_m : s ≤ m := by change S.card ≤ n / 2; omega
      refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_Icc.mpr ⟨hs1, hs_le_m⟩, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩, ?_⟩
      exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hT_sub, hT_card⟩, hπ_mem⟩
    have hΩ_card : Fintype.card Ω = (n.factorial) ^ 32 := by
      simp [Ω, Fintype.card_perm]
    have h_slice_le : ∀ s ∈ Finset.Icc 1 m, 2 ^ m * (Slice s).card ≤ 2 ^ (m - s) * Fintype.card Ω := by
      intro s hs_mem
      rcases Finset.mem_Icc.mp hs_mem with ⟨hs1, hsm⟩
      have hsn : 2 * s ≤ n := by omega
      let term := ((s + s / 2).choose s * s.factorial * (n - s).factorial) ^ 32
      have h_inner1 : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          ((Sᶜ.powersetCard (s / 2)).biUnion (fun T =>
            Fintype.piFinset (fun _ : Fin 32 =>
              Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => S.image σ ⊆ S ∪ T)))).card ≤
          (n - s).choose (s / 2) * term := by
        intro S hS
        have hS_card : S.card = s := (Finset.mem_powersetCard.mp hS).2
        have hSc_card : Sᶜ.card = n - s := by
          rw [Finset.card_compl, Fintype.card_fin, hS_card]
        calc ((Sᶜ.powersetCard (s / 2)).biUnion _).card
            ≤ ∑ T ∈ Sᶜ.powersetCard (s / 2),
                (Fintype.piFinset (fun _ : Fin 32 =>
                  Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => S.image σ ⊆ S ∪ T))).card :=
                Finset.card_biUnion_le
          _ ≤ (Sᶜ.powersetCard (s / 2)).card • term := by
                refine Finset.sum_le_card_nsmul _ _ term ?_
                intro T hT
                rcases Finset.mem_powersetCard.mp hT with ⟨hT_sub, hT_card⟩
                have hdisj : Disjoint S T := by
                  rw [Finset.disjoint_left]
                  intro x hxS hxT
                  exact (Finset.mem_compl.mp (hT_sub hxT)) hxS
                have hST_card : (S ∪ T).card = s + s / 2 := by
                  rw [Finset.card_union_of_disjoint hdisj, hS_card, hT_card]
                rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                have hsingle := h_s2 n S (S ∪ T)
                rw [hS_card, hST_card] at hsingle
                exact Nat.pow_le_pow_left hsingle 32
          _ = (n - s).choose (s / 2) * term := by
                rw [Finset.card_powersetCard, hSc_card, smul_eq_mul]
      have h_slice_raw : (Slice s).card ≤ n.choose s * ((n - s).choose (s / 2) * term) := by
        calc (Slice s).card
            ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
                ((Sᶜ.powersetCard (s / 2)).biUnion _).card := Finset.card_biUnion_le
          _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard s).card •
                ((n - s).choose (s / 2) * term) :=
                Finset.sum_le_card_nsmul _ _ _ h_inner1
          _ = n.choose s * ((n - s).choose (s / 2) * term) := by
                rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have h_2s : 2 ^ s * (Slice s).card ≤ Fintype.card Ω := by
        calc 2 ^ s * (Slice s).card
            ≤ 2 ^ s * (n.choose s * ((n - s).choose (s / 2) * term)) :=
                Nat.mul_le_mul_left _ h_slice_raw
          _ = 2 ^ s * n.choose s * (n - s).choose (s / 2) * term := by ring
          _ ≤ (n.factorial) ^ 32 := h_s3 n s hs1 hsn
          _ = Fintype.card Ω := hΩ_card.symm
      calc 2 ^ m * (Slice s).card
          = 2 ^ (m - s) * (2 ^ s * (Slice s).card) := by
              rw [← Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hsm]
        _ ≤ 2 ^ (m - s) * Fintype.card Ω := Nat.mul_le_mul_left _ h_2s
    have h_geom : ∀ k : ℕ, ∑ s ∈ Finset.Icc 1 k, 2 ^ (k - s) < 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hsum_eq : ∑ s ∈ Finset.Icc 1 k, 2 ^ (k + 1 - s) =
            2 * ∑ s ∈ Finset.Icc 1 k, 2 ^ (k - s) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro s hs
          have hsk : s ≤ k := (Finset.mem_Icc.mp hs).2
          have hexp : k + 1 - s = (k - s) + 1 := by omega
          rw [hexp, pow_succ']
        rw [hsum_eq, Nat.sub_self, pow_zero, pow_succ']
        omega
    have hΩ_pos : 0 < Fintype.card Ω := by
      rw [hΩ_card]
      exact Nat.pow_pos (Nat.factorial_pos n)
    have h_contra : 2 ^ m * Fintype.card Ω < 2 ^ m * Fintype.card Ω := by
      calc 2 ^ m * Fintype.card Ω
          = 2 ^ m * (Finset.univ : Finset Ω).card := by rw [Finset.card_univ]
        _ ≤ 2 ^ m * ((Finset.Icc 1 m).biUnion Slice).card :=
              Nat.mul_le_mul_left _ (Finset.card_le_card h_cover)
        _ ≤ 2 ^ m * ∑ s ∈ Finset.Icc 1 m, (Slice s).card :=
              Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ s ∈ Finset.Icc 1 m, 2 ^ m * (Slice s).card := Finset.mul_sum _ _ _
        _ ≤ ∑ s ∈ Finset.Icc 1 m, 2 ^ (m - s) * Fintype.card Ω :=
              Finset.sum_le_sum h_slice_le
        _ = (∑ s ∈ Finset.Icc 1 m, 2 ^ (m - s)) * Fintype.card Ω :=
              (Finset.sum_mul _ _ _).symm
        _ < 2 ^ m * Fintype.card Ω :=
              Nat.mul_lt_mul_of_pos_right (h_geom m) hΩ_pos
    exact (lt_irrefl _ h_contra)
  refine ⟨64, (1 / 2 : ℝ), by omega, by norm_num, ?_⟩
  intro N₀
  let n := max N₀ 2
  have hN₀ : N₀ ≤ n := Nat.le_max_left N₀ 2
  have hn : 2 ≤ n := Nat.le_max_right N₀ 2
  rcases h_s4 n hn with ⟨π, hπ⟩
  rcases h_s1 n 32 π with ⟨G, hdeg, hbdry⟩
  refine ⟨n, G, hN₀, ?_, ?_⟩
  · intro v
    exact (hdeg v).trans (by omega)
  · intro S hS
    classical
    let S₀ : Finset (Fin n) := S.toFinset
    have hS₀_coe : (S₀ : Set (Fin n)) = S := Set.coe_toFinset S
    have hS₀_card : S.ncard = S₀.card := Set.ncard_eq_toFinset_card' S
    rcases (by omega : S₀.card = 0 ∨ 1 ≤ S₀.card) with h0 | h1
    · rw [hS₀_card, h0]
      simp
    · have h2S₀ : 2 * S₀.card ≤ n := by omega
      have hlt : S₀.card / 2 <
          ((Finset.univ.biUnion (fun i : Fin 32 => S₀.image (π i))) \ S₀).card :=
        hπ S₀ h1 h2S₀
      have hle := hbdry S₀
      rw [hS₀_coe] at hle
      have hlt_out : S₀.card / 2 <
          {p : Fin n × Fin n | p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2}.ncard :=
        lt_of_lt_of_le hlt hle
      have hnat : S.ncard ≤
          2 * {p : Fin n × Fin n | p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2}.ncard := by
        omega
      have hreal : (S.ncard : ℝ) ≤
          2 * ({p : Fin n × Fin n | p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2}.ncard : ℝ) := by
        exact_mod_cast hnat
      linarith

theorem thm2_from_expander (h_exp : ∃ (D : ℕ) (φ : ℝ), 3 ≤ D ∧ 0 < φ ∧
      ∀ N₀ : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N₀ ≤ n ∧ IsBoundedDegreeEdgeExpander G D φ) :
    Theorem2 :=
by
  classical
  rcases h_exp with ⟨D, φ, hD, hφ, h_exp_all⟩
  let φ₁ : ℝ := min φ 1
  have hφ₁_pos : 0 < φ₁ := lt_min hφ zero_lt_one
  have hφ₁_le_φ : φ₁ ≤ φ := min_le_left φ 1
  have hφ₁_le_one : φ₁ ≤ 1 := min_le_right φ 1
  have hD_real : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hD_pos : (0 : ℝ) < (D : ℝ) := by linarith
  have hD1_gt_one : (1 : ℝ) < ((D + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hlogD1_pos : 0 < Real.logb 2 ((D + 1 : ℕ) : ℝ) :=
    Real.logb_pos (by norm_num) hD1_gt_one
  let ε₀ : ℝ := φ₁ / (32 * (D : ℝ) ^ 2)
  let c : ℝ := φ₁ / (32 * (D : ℝ) ^ 2 * Real.logb 2 ((D + 1 : ℕ) : ℝ))
  have hc_pos : 0 < c := by positivity
  have hε₀_pos : 0 < ε₀ := by positivity
  have hε₀_lt_one : ε₀ < 1 := by
    dsimp [ε₀]
    rw [div_lt_one (by positivity)]
    nlinarith
  refine ⟨c, ε₀, hc_pos, hε₀_pos, hε₀_lt_one, ?_⟩
  intro ε hε_pos hε_le N₀ hN₀
  let k : ℕ := ⌊φ₁ / (16 * (D : ℝ) ^ 2 * ε)⌋₊
  have hk_ge_two : 2 ≤ k := by
    apply Nat.le_floor
    have h1 : ε * (32 * (D : ℝ) ^ 2) ≤ φ₁ := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * (D : ℝ) ^ 2)).mp hε_le
      linarith
    rw [le_div_iff₀ (by positivity)]
    push_cast
    linarith
  have hk_pos : 0 < k := by omega
  have hk_ge_one : 1 ≤ k := by omega
  let N₁ : ℕ := max N₀ (⌈2 / ε⌉₊ + 4)
  rcases h_exp_all N₁ with ⟨n, G₀, hn_N₁, hG₀⟩
  rcases hG₀ with ⟨hdeg, hexp⟩
  have hN₀_le_n : N₀ ≤ n := le_trans (le_max_left _ _) hn_N₁
  have hceil_le_n : ⌈2 / ε⌉₊ + 4 ≤ n := le_trans (le_max_right _ _) hn_N₁
  have hn_ge_four : 4 ≤ n := by omega
  have hdeg_finset : ∀ y : Fin n, (G₀.neighborFinset y).card ≤ D := by
    intro y
    have h1 : (G₀.neighborSet y).ncard ≤ D := hdeg y
    rw [← SimpleGraph.coe_neighborFinset G₀ y, Set.ncard_coe_finset] at h1
    exact h1
  
  let OrderedEdge : Type := { p : Fin n × Fin n // p.1 < p.2 ∧ G₀.Adj p.1 p.2 }
  let V : Type := Fin n ⊕ (OrderedEdge × Fin k)
  let hV : Fintype V := inferInstance
  let subdivStep : V → V → Prop := fun x y =>
    match x, y with
    | Sum.inl u, Sum.inr (e, j) => u = e.1.1 ∧ j.1 = 0
    | Sum.inr (e, j), Sum.inr (e', j') => e = e' ∧ j'.1 = j.1 + 1
    | Sum.inr (e, j), Sum.inl w => w = e.1.2 ∧ j.1 + 1 = k
    | Sum.inl _, Sum.inl _ => False
  let subdivAdj : V → V → Prop := fun x y => subdivStep x y ∨ subdivStep y x
  have h_subdiv_symm : Symmetric subdivAdj := fun _ _ h => h.symm
  have h_subdiv_loopless : Irreflexive subdivAdj := by
    intro x hx
    have hstep : subdivStep x x := by
      rcases hx with h | h <;> exact h
    rcases x with u | ⟨e, j⟩
    · exact hstep
    · dsimp [subdivStep] at hstep
      omega
  let G : SimpleGraph V :=
    { Adj := subdivAdj
      symm := h_subdiv_symm
      loopless := h_subdiv_loopless }
  let N : ℕ := @Fintype.card V hV
  
  have hN_eq : N = n + Fintype.card OrderedEdge * k := by
    change Fintype.card (Fin n ⊕ (OrderedEdge × Fin k)) = n + Fintype.card OrderedEdge * k
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hn_le_N : n ≤ N := by omega
  have hOrd_le : Fintype.card OrderedEdge ≤ n * D := by
    let allDir : Finset (Fin n × Fin n) :=
      Finset.univ.biUnion (fun u => (G₀.neighborFinset u).image (fun w => (u, w)))
    have hsub : (Finset.univ : Finset OrderedEdge).image Subtype.val ⊆ allDir := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨e, _, rfl⟩
      refine Finset.mem_biUnion.mpr ⟨e.1.1, Finset.mem_univ _, ?_⟩
      refine Finset.mem_image.mpr ⟨e.1.2, ?_, rfl⟩
      exact (G₀.mem_neighborFinset e.1.1 e.1.2).mpr e.2.2
    have hcard1 : Fintype.card OrderedEdge =
        ((Finset.univ : Finset OrderedEdge).image Subtype.val).card := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
    calc
      Fintype.card OrderedEdge
          = ((Finset.univ : Finset OrderedEdge).image Subtype.val).card := hcard1
      _ ≤ allDir.card := Finset.card_le_card hsub
      _ ≤ ∑ u ∈ (Finset.univ : Finset (Fin n)),
            ((G₀.neighborFinset u).image (fun w => (u, w))).card := Finset.card_biUnion_le
      _ ≤ ∑ u ∈ (Finset.univ : Finset (Fin n)), (G₀.neighborFinset u).card :=
            Finset.sum_le_sum (fun u _ => Finset.card_image_le)
      _ ≤ (Finset.univ : Finset (Fin n)).card • D :=
            Finset.sum_le_card_nsmul _ _ D (fun u _ => hdeg_finset u)
      _ = n * D := by simp [smul_eq_mul]
  have hN_le : N ≤ n + k * D * n := by
    have hmul : Fintype.card OrderedEdge * k ≤ (n * D) * k :=
      Nat.mul_le_mul_right k hOrd_le
    have hcomm : (n * D) * k = k * D * n := by ring
    omega
  
  have hN₀_le_N : N₀ ≤ N := le_trans hN₀_le_n hn_le_N
  have h2_le_εN : 2 ≤ ε * (N : ℝ) := by
    have h1 : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil (2 / ε)
    have h2 : (⌈2 / ε⌉₊ : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : ⌈2 / ε⌉₊ ≤ N)
    have h3 : 2 / ε ≤ (N : ℝ) := le_trans h1 h2
    have h4 := (div_le_iff₀ hε_pos).mp h3
    linarith
  have hεN_le_frac : ε * (N : ℝ) ≤ (φ₁ / (8 * (D : ℝ))) * (n : ℝ) := by
    have hk_real : (k : ℝ) ≤ φ₁ / (16 * (D : ℝ) ^ 2 * ε) :=
      Nat.floor_le (by positivity)
    have hk_prod : (k : ℝ) * (16 * (D : ℝ) ^ 2 * ε) ≤ φ₁ :=
      (le_div_iff₀ (by positivity)).mp hk_real
    have h_term2 : ε * (k : ℝ) * (D : ℝ) ≤ φ₁ / (16 * (D : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h_term1 : ε ≤ φ₁ / (16 * (D : ℝ)) := by
      have hε_prod : ε * (32 * (D : ℝ) ^ 2) ≤ φ₁ :=
        (le_div_iff₀ (by positivity)).mp hε_le
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hN_real : (N : ℝ) ≤ (1 + (k : ℝ) * (D : ℝ)) * (n : ℝ) := by
      have hcast : (N : ℝ) ≤ (n : ℝ) + (k : ℝ) * (D : ℝ) * (n : ℝ) := by
        exact_mod_cast hN_le
      linarith
    calc
      ε * (N : ℝ) ≤ ε * ((1 + (k : ℝ) * (D : ℝ)) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hN_real (le_of_lt hε_pos)
      _ = (ε + ε * (k : ℝ) * (D : ℝ)) * (n : ℝ) := by ring
      _ ≤ (φ₁ / (16 * (D : ℝ)) + φ₁ / (16 * (D : ℝ))) * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right (add_le_add h_term1 h_term2) (by positivity)
      _ = (φ₁ / (8 * (D : ℝ))) * (n : ℝ) := by ring
  have h2εN_le : 2 * (ε * (N : ℝ)) ≤ (φ₁ / (4 * (D : ℝ))) * (n : ℝ) := by
    calc
      2 * (ε * (N : ℝ)) ≤ 2 * ((φ₁ / (8 * (D : ℝ))) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hεN_le_frac (by norm_num)
      _ = (φ₁ / (4 * (D : ℝ))) * (n : ℝ) := by ring
  have hεN_le_n : ε * (N : ℝ) ≤ (n : ℝ) := by
    have hcoef_le_one : φ₁ / (8 * (D : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc
      ε * (N : ℝ) ≤ (φ₁ / (8 * (D : ℝ))) * (n : ℝ) := hεN_le_frac
      _ ≤ 1 * (n : ℝ) := mul_le_mul_of_nonneg_right hcoef_le_one (by positivity)
      _ = (n : ℝ) := one_mul _
  let r₀ : ℕ := ⌊Real.logb 2 (n : ℝ) / (2 * Real.logb 2 ((D + 1 : ℕ) : ℝ))⌋₊
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlogn_pos : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos (by norm_num) hn_gt_one
  have hpow_le_n : (D + 1) ^ (2 * r₀) ≤ n := by
    have hr₀_le : (r₀ : ℝ) ≤ Real.logb 2 (n : ℝ) / (2 * Real.logb 2 ((D + 1 : ℕ) : ℝ)) :=
      Nat.floor_le (by positivity)
    have hmul_log : ((2 * r₀ : ℕ) : ℝ) * Real.logb 2 ((D + 1 : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) := by
      have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.logb 2 ((D + 1 : ℕ) : ℝ))).mp hr₀_le
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    have hlog_pow : Real.logb 2 (((D + 1 : ℕ) : ℝ) ^ (2 * r₀)) ≤ Real.logb 2 (n : ℝ) := by
      rw [Real.logb_pow]
      exact hmul_log
    have hreal_pow_le : (((D + 1 : ℕ) : ℝ) ^ (2 * r₀)) ≤ (n : ℝ) := by
      by_contra h_gt
      push_neg at h_gt
      have hlt := Real.strictMonoOn_logb (by norm_num : (1 : ℝ) < 2)
        (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < (n : ℝ)))
        (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < (((D + 1 : ℕ) : ℝ) ^ (2 * r₀))))
        h_gt
      linarith
    exact_mod_cast hreal_pow_le
  have h_final_param_bound :
      c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ)) ≤ (((k + 1) * (r₀ + 1) : ℕ) : ℝ) := by
    have hεN_pos : 0 < ε * (N : ℝ) := by linarith
    have hlog_mono : Real.logb 2 (ε * (N : ℝ)) ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hεN_pos hεN_le_n
    have hk1 : φ₁ / (16 * (D : ℝ) ^ 2 * ε) ≤ (k : ℝ) + 1 :=
      le_of_lt (Nat.lt_floor_add_one _)
    have hr1 : Real.logb 2 (n : ℝ) / (2 * Real.logb 2 ((D + 1 : ℕ) : ℝ)) ≤ (r₀ : ℝ) + 1 :=
      le_of_lt (Nat.lt_floor_add_one _)
    have h_ident : c * ε⁻¹ * Real.logb 2 (n : ℝ) =
        (φ₁ / (16 * (D : ℝ) ^ 2 * ε)) *
          (Real.logb 2 (n : ℝ) / (2 * Real.logb 2 ((D + 1 : ℕ) : ℝ))) := by
      dsimp [c]
      have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
      have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
      have hlog_ne : Real.logb 2 ((D + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hlogD1_pos
      field_simp
      ring
    calc
      c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ))
          ≤ c * ε⁻¹ * Real.logb 2 (n : ℝ) :=
            mul_le_mul_of_nonneg_left hlog_mono (by positivity)
      _ = (φ₁ / (16 * (D : ℝ) ^ 2 * ε)) *
            (Real.logb 2 (n : ℝ) / (2 * Real.logb 2 ((D + 1 : ℕ) : ℝ))) := h_ident
      _ ≤ ((k : ℝ) + 1) * ((r₀ : ℝ) + 1) :=
            mul_le_mul hk1 hr1 (by positivity) (by positivity)
      _ = (((k + 1) * (r₀ + 1) : ℕ) : ℝ) := by push_cast; ring
  
  refine ⟨V, hV, G, hN₀_le_N, h2_le_εN, ?_⟩
  intro X dX hdX f M hM t ht β hβ h_stretch h_dist
  rcases hdX with ⟨hdX_self, hdX_symm, hdX_tri⟩
  
  let R_fin : Finset V := Finset.univ.filter (fun x => x ∉ M)
  have hR_fin_coe : (R_fin : Set V) = Set.univ \ M := by
    ext x
    simp [R_fin]
  have hR_fin_card : R_fin.card = (Set.univ \ M).ncard := by
    rw [← hR_fin_coe, Set.ncard_coe_finset]
  let touch : V → Finset (Fin n) := fun x =>
    match x with
    | Sum.inl w => {w}
    | Sum.inr (e, _) => {e.1.1, e.1.2}
  have htouch_card : ∀ x : V, (touch x).card ≤ 2 := by
    rintro (w | ⟨e, j⟩)
    · simp [touch]
    · dsimp [touch]
      exact le_trans (Finset.card_insert_le _ _) (by simp)
  let R_V : Finset (Fin n) := R_fin.biUnion touch
  have hRV_card_nat : R_V.card ≤ 2 * (Set.univ \ M).ncard := by
    calc
      R_V.card ≤ ∑ x ∈ R_fin, (touch x).card := Finset.card_biUnion_le
      _ ≤ R_fin.card • 2 := Finset.sum_le_card_nsmul _ _ 2 (fun x _ => htouch_card x)
      _ = 2 * (Set.univ \ M).ncard := by
        rw [smul_eq_mul, hR_fin_card, mul_comm]
  have hRV_card_real : (R_V.card : ℝ) ≤ (φ₁ / (4 * (D : ℝ))) * (n : ℝ) := by
    have h1 : (R_V.card : ℝ) ≤ 2 * ((Set.univ \ M).ncard : ℝ) := by
      exact_mod_cast hRV_card_nat
    linarith
  
  let S_set : Set (Fin n) := {w : Fin n | w ∉ R_V}
  let H : SimpleGraph S_set := G₀.induce S_set
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite H.ConnectedComponent
  let U : Finset (Fin n) := Finset.univ \ R_V
  have hU_add_RV : U.card + R_V.card = n := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R_V)
  let compSub : H.ConnectedComponent → Finset S_set :=
    fun γ => Finset.univ.filter (fun x : S_set => H.connectedComponentMk x = γ)
  let C : H.ConnectedComponent → Finset (Fin n) :=
    fun γ => (compSub γ).map ⟨Subtype.val, Subtype.val_injective⟩
  have hmem_C : ∀ (γ : H.ConnectedComponent) (w : Fin n),
      w ∈ C γ ↔ ∃ hw : w ∉ R_V, H.connectedComponentMk ⟨w, hw⟩ = γ := by
    intro γ w
    simp only [C, compSub, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk, Subtype.exists, S_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, ha, hmk, rfl⟩
      exact ⟨ha, hmk⟩
    · rintro ⟨hw, hmk⟩
      exact ⟨w, hw, hmk, rfl⟩
  have hsum_C_card : ∑ γ : H.ConnectedComponent, (C γ).card = U.card := by
    have hmap_univ : (Finset.univ : Finset S_set).map ⟨Subtype.val, Subtype.val_injective⟩ = U := by
      ext w
      simp [U, S_set]
    have hU_eq_S : U.card = (Finset.univ : Finset S_set).card := by
      rw [← hmap_univ, Finset.card_map]
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := H.connectedComponentMk) (s := (Finset.univ : Finset S_set))
      (t := (Finset.univ : Finset H.ConnectedComponent))
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    rw [hU_eq_S, hfib]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    simp [C, compSub]
  let bdry : Finset (Fin n) → Finset (Fin n × Fin n) :=
    fun A => Finset.univ.filter (fun p => p.1 ∈ A ∧ p.2 ∉ A ∧ G₀.Adj p.1 p.2)
  have hbdry_disj :
      ((Finset.univ : Finset H.ConnectedComponent) : Set H.ConnectedComponent).PairwiseDisjoint
        (fun γ => bdry (C γ)) := by
    intro γ₁ _ γ₂ _ hne
    change Disjoint (bdry (C γ₁)) (bdry (C γ₂))
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have hx1 : p.1 ∈ C γ₁ := (Finset.mem_filter.mp hp1).2.1
    have hx2 : p.1 ∈ C γ₂ := (Finset.mem_filter.mp hp2).2.1
    rcases (hmem_C γ₁ p.1).mp hx1 with ⟨hw1, hmk1⟩
    rcases (hmem_C γ₂ p.1).mp hx2 with ⟨hw2, hmk2⟩
    apply hne
    rw [← hmk1, ← hmk2]
  have hbdry_sum_le : ∑ γ : H.ConnectedComponent, (bdry (C γ)).card ≤ R_V.card * D := by
    let rvInEdges : Finset (Fin n × Fin n) :=
      R_V.biUnion (fun y => (G₀.neighborFinset y).image (fun x => (x, y)))
    have hsub : (Finset.univ : Finset H.ConnectedComponent).biUnion (fun γ => bdry (C γ)) ⊆
        rvInEdges := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨γ, _, hp_bdry⟩
      rcases p with ⟨x, y⟩
      have h_and := (Finset.mem_filter.mp hp_bdry).2
      rcases h_and with ⟨hxC, hy_notC, hadj_xy⟩
      rcases (hmem_C γ x).mp hxC with ⟨hx_notRV, hmk_x⟩
      have hy_RV : y ∈ R_V := by
        by_contra hy_notRV
        have hadj_H : H.Adj ⟨x, hx_notRV⟩ ⟨y, hy_notRV⟩ := hadj_xy
        have hmk_y : H.connectedComponentMk ⟨y, hy_notRV⟩ = γ := by
          rw [← hmk_x, SimpleGraph.ConnectedComponent.eq]
          exact hadj_H.symm.reachable
        exact hy_notC ((hmem_C γ y).mpr ⟨hy_notRV, hmk_y⟩)
      refine Finset.mem_biUnion.mpr ⟨y, hy_RV, ?_⟩
      refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
      exact (G₀.mem_neighborFinset y x).mpr (G₀.symm hadj_xy)
    calc
      ∑ γ : H.ConnectedComponent, (bdry (C γ)).card
          = ((Finset.univ : Finset H.ConnectedComponent).biUnion (fun γ => bdry (C γ))).card :=
            (Finset.card_biUnion hbdry_disj).symm
      _ ≤ rvInEdges.card := Finset.card_le_card hsub
      _ ≤ ∑ y ∈ R_V, ((G₀.neighborFinset y).image (fun x => (x, y))).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ y ∈ R_V, (G₀.neighborFinset y).card :=
            Finset.sum_le_sum (fun y _ => Finset.card_image_le)
      _ ≤ R_V.card • D := Finset.sum_le_card_nsmul _ _ D (fun y _ => hdeg_finset y)
      _ = R_V.card * D := smul_eq_mul _ _
  have hexists_giant : ∃ γ₀ : H.ConnectedComponent, n < 2 * (C γ₀).card := by
    by_contra h_all_small
    push_neg at h_all_small
    have hcomp_exp : ∀ γ : H.ConnectedComponent,
        φ₁ * ((C γ).card : ℝ) ≤ ((bdry (C γ)).card : ℝ) := by
      intro γ
      have h2le : 2 * ((C γ : Set (Fin n))).ncard ≤ n := by
        rw [Set.ncard_coe_finset]
        exact h_all_small γ
      have hexp_γ := hexp (C γ : Set (Fin n)) h2le
      rw [Set.ncard_coe_finset] at hexp_γ
      have hset_eq : {p : Fin n × Fin n |
          p.1 ∈ (C γ : Set (Fin n)) ∧ p.2 ∉ (C γ : Set (Fin n)) ∧ G₀.Adj p.1 p.2} =
          ((bdry (C γ) : Finset (Fin n × Fin n)) : Set (Fin n × Fin n)) := by
        ext p
        simp [bdry]
      rw [hset_eq, Set.ncard_coe_finset] at hexp_γ
      exact le_trans (mul_le_mul_of_nonneg_right hφ₁_le_φ (by positivity)) hexp_γ
    have hsum_exp : φ₁ * (U.card : ℝ) ≤ (R_V.card : ℝ) * (D : ℝ) := by
      have h1 : ∑ γ : H.ConnectedComponent, φ₁ * ((C γ).card : ℝ) ≤
          ∑ γ : H.ConnectedComponent, ((bdry (C γ)).card : ℝ) :=
        Finset.sum_le_sum (fun γ _ => hcomp_exp γ)
      rw [← Finset.mul_sum] at h1
      have hsum_real : (∑ γ : H.ConnectedComponent, ((C γ).card : ℝ)) = (U.card : ℝ) := by
        exact_mod_cast hsum_C_card
      have hbdry_real : (∑ γ : H.ConnectedComponent, ((bdry (C γ)).card : ℝ)) ≤
          (R_V.card : ℝ) * (D : ℝ) := by
        exact_mod_cast hbdry_sum_le
      rw [hsum_real] at h1
      exact le_trans h1 hbdry_real
    have hRV_D_le : (R_V.card : ℝ) * (D : ℝ) ≤ (φ₁ / 4) * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hRV_card_real (le_of_lt hD_pos)
      have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_pos
      have hsimp : (φ₁ / (4 * (D : ℝ))) * (n : ℝ) * (D : ℝ) = (φ₁ / 4) * (n : ℝ) := by
        field_simp
      linarith
    have hRV_lt_quarter : (R_V.card : ℝ) < (1 / 4 : ℝ) * (n : ℝ) := by
      have hfrac_le : φ₁ / (4 * (D : ℝ)) ≤ 1 / 12 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      have h12 : (R_V.card : ℝ) ≤ (1 / 12 : ℝ) * (n : ℝ) :=
        le_trans hRV_card_real
          (mul_le_mul_of_nonneg_right hfrac_le (by positivity))
      have hn_pos : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_four
      linarith
    have hU_plus_RV_real : (U.card : ℝ) + (R_V.card : ℝ) = (n : ℝ) := by
      exact_mod_cast hU_add_RV
    have hU_gt : (3 / 4 : ℝ) * (n : ℝ) < (U.card : ℝ) := by linarith
    have hφU_gt : (3 / 4 : ℝ) * φ₁ * (n : ℝ) < φ₁ * (U.card : ℝ) := by nlinarith
    have hn_pos : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_four
    nlinarith
  rcases hexists_giant with ⟨γ₀, hγ₀_giant⟩
  
  have hCγ₀_nonempty : (C γ₀).Nonempty := by
    apply Finset.card_pos.mp
    omega
  rcases hCγ₀_nonempty with ⟨u₀, hu₀_C⟩
  rcases (hmem_C γ₀ u₀).mp hu₀_C with ⟨hu₀_notRV, hmk_u₀⟩
  obtain ⟨B, hB0, hBsucc⟩ : ∃ B : ℕ → Finset (Fin n),
      B 0 = {u₀} ∧ ∀ s, B (s + 1) = B s ∪ (B s).biUnion (fun w => G₀.neighborFinset w) :=
    ⟨fun s => Nat.rec ({u₀} : Finset (Fin n))
      (fun _ Bs => Bs ∪ Bs.biUnion (fun w => G₀.neighborFinset w)) s, rfl, fun _ => rfl⟩
  have hu₀_mem_B : ∀ s : ℕ, u₀ ∈ B s := by
    intro s
    induction s with
    | zero => rw [hB0]; exact Finset.mem_singleton_self u₀
    | succ s ih => rw [hBsucc]; exact Finset.mem_union_left _ ih
  have hB_mono_step : ∀ s : ℕ, B s ⊆ B (s + 1) := by
    intro s
    rw [hBsucc]
    exact Finset.subset_union_left
  have hB_mono : ∀ {s₁ s₂ : ℕ}, s₁ ≤ s₂ → B s₁ ⊆ B s₂ := by
    intro s₁ s₂ hle
    induction hle with
    | refl => exact Finset.Subset.refl _
    | step _ ih => exact Finset.Subset.trans ih (hB_mono_step _)
  have hB_card : ∀ s : ℕ, (B s).card ≤ (D + 1) ^ s := by
    intro s
    induction s with
    | zero => rw [hB0]; simp
    | succ s ih =>
      have h1 : (B (s + 1)).card ≤
          (B s).card + ((B s).biUnion (fun w => G₀.neighborFinset w)).card := by
        rw [hBsucc]
        exact Finset.card_union_le _ _
      have h2 : ((B s).biUnion (fun w => G₀.neighborFinset w)).card ≤ (B s).card * D := by
        calc
          ((B s).biUnion (fun w => G₀.neighborFinset w)).card
              ≤ ∑ w ∈ B s, (G₀.neighborFinset w).card := Finset.card_biUnion_le
          _ ≤ (B s).card • D := Finset.sum_le_card_nsmul _ _ D (fun w _ => hdeg_finset w)
          _ = (B s).card * D := smul_eq_mul _ _
      have h3 : (B (s + 1)).card ≤ (B s).card * (D + 1) := by
        calc
          (B (s + 1)).card ≤ (B s).card + (B s).card * D := le_trans h1 (Nat.add_le_add_left h2 _)
          _ = (B s).card * (D + 1) := by ring
      calc
        (B (s + 1)).card ≤ (B s).card * (D + 1) := h3
        _ ≤ (D + 1) ^ s * (D + 1) := Nat.mul_le_mul_right (D + 1) ih
        _ = (D + 1) ^ (s + 1) := (pow_succ (D + 1) s).symm
  have hBr₀_lt_C : (B r₀).card < (C γ₀).card := by
    let m : ℕ := (D + 1) ^ r₀
    have hm_sq : m * m ≤ n := by
      have : m * m = (D + 1) ^ (2 * r₀) := by
        dsimp [m]
        rw [← pow_add, two_mul]
      omega
    have h2m_le_n : 2 * m ≤ n := by
      by_contra h_gt
      have h1 : n + 1 ≤ 2 * m := by omega
      have h2 : (n + 1) * (n + 1) ≤ (2 * m) * (2 * m) := Nat.mul_le_mul h1 h1
      have h3 : 4 * n ≤ n * n := Nat.mul_le_mul_right n hn_ge_four
      nlinarith
    have hB_le_m : (B r₀).card ≤ m := hB_card r₀
    omega
  have h_not_sub : ¬ (C γ₀ ⊆ B r₀) := by
    intro hsub
    exact absurd (Finset.card_le_card hsub) (not_le_of_gt hBr₀_lt_C)
  rcases Finset.not_subset.mp h_not_sub with ⟨v₀, hv₀_C, hv₀_not_B⟩
  rcases (hmem_C γ₀ v₀).mp hv₀_C with ⟨hv₀_notRV, hmk_v₀⟩
  have hreach_uv : H.Reachable ⟨u₀, hu₀_notRV⟩ ⟨v₀, hv₀_notRV⟩ := by
    apply SimpleGraph.ConnectedComponent.exact
    rw [hmk_u₀, hmk_v₀]
  let h : Fin n → ℕ := fun w =>
    (((Finset.range (r₀ + 1)).filter (fun s => w ∉ B s) : Finset ℕ)).card
  have h_u₀ : h u₀ = 0 := by
    dsimp [h]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s _
    exact not_not.mpr (hu₀_mem_B s)
  have h_v₀ : h v₀ = r₀ + 1 := by
    dsimp [h]
    rw [Finset.filter_eq_self.mpr, Finset.card_range]
    intro s hs
    have hs_le : s ≤ r₀ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    intro hv_in_s
    exact hv₀_not_B (hB_mono hs_le hv_in_s)
  have h_step_lip : ∀ a b : Fin n, G₀.Adj a b → h b ≤ h a + 1 := by
    intro a b hadj
    let Sa : Finset ℕ := (Finset.range (r₀ + 1)).filter (fun s => a ∉ B s)
    let Sb : Finset ℕ := (Finset.range (r₀ + 1)).filter (fun s => b ∉ B s)
    have hsub : Sb ⊆ insert 0 (Sa.image (· + 1)) := by
      intro s hs
      rcases s with _ | s'
      · exact Finset.mem_insert_self 0 _
      · apply Finset.mem_insert_of_mem
        refine Finset.mem_image.mpr ⟨s', ?_, rfl⟩
        have hs_mem := Finset.mem_filter.mp hs
        have hs'_lt : s' < r₀ + 1 := by
          have := Finset.mem_range.mp hs_mem.1
          omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs'_lt, ?_⟩
        intro ha_in
        apply hs_mem.2
        rw [hBsucc]
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨a, ha_in, (G₀.mem_neighborFinset a b).mpr hadj⟩
    calc
      h b = Sb.card := rfl
      _ ≤ (insert 0 (Sa.image (· + 1))).card := Finset.card_le_card hsub
      _ ≤ (Sa.image (· + 1)).card + 1 := Finset.card_insert_le _ _
      _ ≤ Sa.card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ = h a + 1 := rfl
  have h_lip : ∀ a b : Fin n, G₀.Adj a b → h a ≤ h b + 1 ∧ h b ≤ h a + 1 :=
    fun a b hadj => ⟨h_step_lip b a (G₀.symm hadj), h_step_lip a b hadj⟩
  
  let finRel : V → V → Prop := fun x y => dX (f x) (f y) < ⊤
  have hfin_refl : ∀ x : V, finRel x x := by
    intro x
    dsimp [finRel]
    rw [hdX_self]
    exact ENNReal.zero_lt_top
  have hfin_symm : ∀ {x y : V}, finRel x y → finRel y x := by
    intro x y hxy
    dsimp [finRel] at hxy ⊢
    rw [hdX_symm]
    exact hxy
  have hfin_trans : ∀ {x y z : V}, finRel x y → finRel y z → finRel x z := by
    intro x y z hxy hyz
    dsimp [finRel] at hxy hyz ⊢
    exact lt_of_le_of_lt (hdX_tri (f x) (f y) (f z)) (ENNReal.add_lt_top.mpr ⟨hxy, hyz⟩)
  have hfin_adj : ∀ {x y : V}, x ∈ M → G.Adj x y → finRel x y := by
    intro x y hxM hadj
    have hhop1 : unweightedHopDist G 1 x y ≤ 1 := by
      dsimp [unweightedHopDist, hopDist]
      refine iInf_le_of_le hadj.toWalk (iInf_le_of_le ?_ ?_)
      · simp [SimpleGraph.Adj.toWalk]
      · norm_num [walkWeight, SimpleGraph.Adj.toWalk]
    have hd_le : dX (f x) (f y) ≤ ENNReal.ofReal t := by
      calc
        dX (f x) (f y) ≤ ENNReal.ofReal t * unweightedHopDist G 1 x y := h_dist x hxM y
        _ ≤ ENNReal.ofReal t * 1 := mul_le_mul_of_nonneg_left hhop1 (zero_le _)
        _ = ENNReal.ofReal t := mul_one _
    exact lt_of_le_of_lt hd_le ENNReal.ofReal_lt_top
  have hinl_mem_M : ∀ {w : Fin n}, w ∉ R_V → (Sum.inl w : V) ∈ M := by
    intro w hw_notRV
    by_contra hw_notM
    apply hw_notRV
    refine Finset.mem_biUnion.mpr ⟨Sum.inl w, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_notM⟩
    · simp [touch]
  have hinr_mem_M : ∀ (e : OrderedEdge) (j : Fin k), e.1.1 ∉ R_V → (Sum.inr (e, j) : V) ∈ M := by
    intro e j ha_notRV
    by_contra hj_notM
    apply ha_notRV
    refine Finset.mem_biUnion.mpr ⟨Sum.inr (e, j), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_notM⟩
    · simp [touch]
  have hfin_ord_edge : ∀ (e : OrderedEdge), e.1.1 ∉ R_V →
      finRel (Sum.inl e.1.1) (Sum.inl e.1.2) := by
    intro e ha_notRV
    let j0 : Fin k := ⟨0, hk_pos⟩
    have h_start : finRel (Sum.inl e.1.1) (Sum.inr (e, j0)) := by
      apply hfin_adj (hinl_mem_M ha_notRV)
      exact Or.inl ⟨rfl, rfl⟩
    have h_mid : ∀ (m : ℕ) (hm : m < k),
        finRel (Sum.inr (e, j0)) (Sum.inr (e, ⟨m, hm⟩)) := by
      intro m
      induction m with
      | zero =>
        intro hm
        have hj_eq : (⟨0, hm⟩ : Fin k) = j0 := rfl
        rw [hj_eq]
        exact hfin_refl _
      | succ m ih =>
        intro hm1
        have hm : m < k := by omega
        have h1 := ih hm
        have h2 : finRel (Sum.inr (e, ⟨m, hm⟩)) (Sum.inr (e, ⟨m + 1, hm1⟩)) := by
          apply hfin_adj (hinr_mem_M e ⟨m, hm⟩ ha_notRV)
          exact Or.inl ⟨rfl, rfl⟩
        exact hfin_trans h1 h2
    have hk_pred : k - 1 < k := by omega
    have h_end : finRel (Sum.inr (e, ⟨k - 1, hk_pred⟩)) (Sum.inl e.1.2) := by
      apply hfin_adj (hinr_mem_M e ⟨k - 1, hk_pred⟩ ha_notRV)
      exact Or.inl ⟨rfl, Nat.sub_add_cancel hk_ge_one⟩
    exact hfin_trans h_start (hfin_trans (h_mid (k - 1) hk_pred) h_end)
  have hfin_base_adj : ∀ {a b : Fin n}, a ∉ R_V → b ∉ R_V → G₀.Adj a b →
      finRel (Sum.inl a) (Sum.inl b) := by
    intro a b ha hb hadj
    have hne : a ≠ b := G₀.ne_of_adj hadj
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact hfin_ord_edge ⟨(a, b), ⟨hab, hadj⟩⟩ ha
    · exact hfin_symm (hfin_ord_edge ⟨(b, a), ⟨hba, G₀.symm hadj⟩⟩ hb)
  have hfin_uv : finRel (Sum.inl u₀) (Sum.inl v₀) := by
    rcases hreach_uv with ⟨p⟩
    have hwalk : ∀ {x y : S_set} (q : H.Walk x y), finRel (Sum.inl x.1) (Sum.inl y.1) := by
      intro x y q
      induction q with
      | nil => exact hfin_refl _
      | @cons x z y hadj q' ih =>
        exact hfin_trans (hfin_base_adj x.2 z.2 hadj) ih
    exact hwalk p
  have hhop_lt_top : unweightedHopDist G β (Sum.inl u₀) (Sum.inl v₀) < ⊤ :=
    lt_of_le_of_lt (h_stretch (Sum.inl u₀) (Sum.inl v₀)) hfin_uv
  
  let F : V → ℕ := fun x =>
    match x with
    | Sum.inl w => (k + 1) * h w
    | Sum.inr (e, j) =>
      if h e.1.1 = h e.1.2 then (k + 1) * h e.1.1
      else if h e.1.1 < h e.1.2 then (k + 1) * h e.1.1 + (j.1 + 1)
      else (k + 1) * h e.1.2 + (k - j.1)
  have hF_step : ∀ {x y : V}, subdivStep x y → F x ≤ F y + 1 ∧ F y ≤ F x + 1 := by
    intro x y hstep
    rcases x with u | ⟨e, j⟩ <;> rcases y with w | ⟨e', j'⟩
    · exact False.elim hstep
    · rcases hstep with ⟨rfl, hj0⟩
      obtain ⟨ha_le, hb_le⟩ := h_lip e'.1.1 e'.1.2 e'.2.2
      dsimp [F]
      split_ifs with heq hlt
      · omega
      · omega
      · have ha_eq : h e'.1.1 = h e'.1.2 + 1 := by omega
        have hmul : (k + 1) * h e'.1.1 = (k + 1) * h e'.1.2 + (k + 1) := by
          rw [ha_eq]; ring
        omega
    · rcases hstep with ⟨rfl, hj_end⟩
      obtain ⟨ha_le, hb_le⟩ := h_lip e.1.1 e.1.2 e.2.2
      dsimp [F]
      split_ifs with heq hlt
      · have hmul : (k + 1) * h e.1.1 = (k + 1) * h e.1.2 := by rw [heq]
        omega
      · have hb_eq : h e.1.2 = h e.1.1 + 1 := by omega
        have hmul : (k + 1) * h e.1.2 = (k + 1) * h e.1.1 + (k + 1) := by
          rw [hb_eq]; ring
        omega
      · omega
    · rcases hstep with ⟨rfl, hj_succ⟩
      have hj_lt : j.1 + 1 < k := by
        have := j'.2
        omega
      dsimp [F]
      split_ifs with heq hlt
      · omega
      · omega
      · omega
  have hF_adj : ∀ {x y : V}, G.Adj x y → F y ≤ F x + 1 := by
    intro x y hadj
    rcases hadj with h1 | h2
    · exact (hF_step h1).2
    · exact (hF_step h2).1
  have hF_walk : ∀ {x y : V} (p : G.Walk x y), F y ≤ F x + p.length := by
    intro x y p
    induction p with
    | nil => simp
    | @cons x z y hadj q ih =>
      have h1 := hF_adj hadj
      simp only [SimpleGraph.Walk.length_cons]
      omega
  have h_beta_nat : (k + 1) * (r₀ + 1) ≤ β := by
    by_contra h_gt
    have h_top : ⊤ ≤ unweightedHopDist G β (Sum.inl u₀) (Sum.inl v₀) := by
      dsimp [unweightedHopDist, hopDist]
      refine le_iInf fun p => le_iInf fun hp => False.elim ?_
      have hw := hF_walk p
      have hFu : F (Sum.inl u₀) = 0 := by simp [F, h_u₀]
      have hFv : F (Sum.inl v₀) = (k + 1) * (r₀ + 1) := by simp [F, h_v₀]
      omega
    exact not_le_of_gt hhop_lt_top h_top
  have h_beta_real : (((k + 1) * (r₀ + 1) : ℕ) : ℝ) ≤ (β : ℝ) := by
    exact_mod_cast h_beta_nat
  exact le_trans h_final_param_bound h_beta_real

theorem thm3_from_expander (h_exp : ∃ (D : ℕ) (φ : ℝ), 3 ≤ D ∧ 0 < φ ∧
      ∀ N₀ : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
        N₀ ≤ n ∧ IsBoundedDegreeEdgeExpander G D φ) :
    Theorem3 :=
by
  have hs1_lem : ∀ {D n : ℕ} {φ : ℝ}, 0 < φ → 2 ≤ n →
      ∀ (G : SimpleGraph (Fin n)), IsBoundedDegreeEdgeExpander G D φ →
        G.Connected ∧
        ∀ m : ℕ, 2 * (D + 1) ^ m ≤ n →
          ∀ S : Set (Fin n), (∀ u ∈ S, ∀ v ∈ S, G.dist u v ≤ m) → 2 * S.ncard ≤ n := by
    intro D n φ hφ hn G hG
    have h_conn : G.Connected := by
      haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      refine ⟨fun u v => ?_⟩
      by_contra h_nreach
      let C : Set (Fin n) := {w | G.Reachable u w}
      have huC : u ∈ C := SimpleGraph.Reachable.refl u
      have hvC : v ∈ Cᶜ := h_nreach
      have hC_pos : 1 ≤ C.ncard :=
        Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite C)).mpr ⟨u, huC⟩)
      have hCc_pos : 1 ≤ Cᶜ.ncard :=
        Nat.succ_le_of_lt ((Set.ncard_pos (Set.toFinite Cᶜ)).mpr ⟨v, hvC⟩)
      have h_sum : C.ncard + Cᶜ.ncard = n := by
        simpa [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl C
      have h_no_cut : ∀ S : Set (Fin n),
          (∀ x ∈ S, ∀ y ∉ S, ¬ G.Adj x y) → 1 ≤ S.ncard → 2 * S.ncard ≤ n → False := by
        intro S h_empty hS1 hS2
        have h_eq : {p : Fin n × Fin n | p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2} = ∅ := by
          ext p
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro hp1 hp2 hp_adj
          exact h_empty p.1 hp1 p.2 hp2 hp_adj
        have h_exp_S := hG.2 S hS2
        rw [h_eq, Set.ncard_empty, Nat.cast_zero] at h_exp_S
        have hS_pos_R : (1 : ℝ) ≤ (S.ncard : ℝ) := by exact_mod_cast hS1
        nlinarith
      rcases (by omega : 2 * C.ncard ≤ n ∨ 2 * Cᶜ.ncard ≤ n) with hC_half | hCc_half
      · exact h_no_cut C (fun x hx y hy hxy => hy (hx.trans hxy.reachable)) hC_pos hC_half
      · refine h_no_cut Cᶜ (fun x hx y hy hxy => ?_) hCc_pos hCc_half
        rw [Set.mem_compl_iff, not_not] at hy
        exact hx (hy.trans (G.symm hxy).reachable)
    refine ⟨h_conn, ?_⟩
    intro m hm S hS_diam
    rcases S.eq_empty_or_nonempty with rfl | ⟨u₀, hu₀⟩
    · simp
    · let B : ℕ → Set (Fin n) := fun k => {v | G.dist u₀ v ≤ k}
      have h_ball : ∀ k : ℕ, (B k).ncard ≤ (D + 1) ^ k := by
        intro k
        induction k with
        | zero =>
          have hB0 : B 0 = {u₀} := by
            ext v
            simp only [B, Set.mem_setOf_eq, Nat.le_zero, Set.mem_singleton_iff]
            constructor
            · intro hv
              by_contra hne
              have hpos := h_conn.pos_dist_of_ne (Ne.symm hne)
              omega
            · rintro rfl
              exact SimpleGraph.dist_self
          rw [hB0, Set.ncard_singleton, pow_zero]
        | succ k ih =>
          classical
          have h_sub : B (k + 1) ⊆ B k ∪ ⋃ w ∈ B k, G.neighborSet w := by
            intro v hv
            simp only [B, Set.mem_setOf_eq] at hv
            rcases (by omega : G.dist u₀ v ≤ k ∨ G.dist u₀ v = k + 1) with hle | heq
            · exact Or.inl hle
            · right
              obtain ⟨p, hp⟩ := h_conn.exists_walk_length_eq_dist u₀ v
              have hp' : p.reverse.length = k + 1 := by
                rw [SimpleGraph.Walk.length_reverse, hp, heq]
              cases hrev : p.reverse with
              | nil =>
                rw [hrev] at hp'
                simp at hp'
              | @cons _ w _ h_vw q =>
                rw [hrev, SimpleGraph.Walk.length_cons] at hp'
                have hq_len : q.reverse.length = k := by
                  rw [SimpleGraph.Walk.length_reverse]; omega
                have hw_Bk : w ∈ B k := by
                  simp only [B, Set.mem_setOf_eq]
                  calc G.dist u₀ w ≤ q.reverse.length := SimpleGraph.dist_le q.reverse
                    _ = k := hq_len
                exact Set.mem_biUnion hw_Bk (G.symm h_vw)
          have h_biUnion_le : (⋃ w ∈ B k, G.neighborSet w).ncard ≤ D * (B k).ncard := by
            have h_fin_eq : (⋃ w ∈ B k, G.neighborSet w).toFinset =
                (B k).toFinset.biUnion (fun w => (G.neighborSet w).toFinset) := by
              ext x; simp
            rw [Set.ncard_eq_toFinset_card', h_fin_eq]
            calc ((B k).toFinset.biUnion (fun w => (G.neighborSet w).toFinset)).card
                ≤ ∑ w ∈ (B k).toFinset, (G.neighborSet w).toFinset.card := Finset.card_biUnion_le
              _ ≤ ∑ _w ∈ (B k).toFinset, D := by
                refine Finset.sum_le_sum (fun w _ => ?_)
                rw [← Set.ncard_eq_toFinset_card']
                exact hG.1 w
              _ = (B k).toFinset.card * D := by simp
              _ = D * (B k).ncard := by rw [← Set.ncard_eq_toFinset_card', mul_comm]
          calc (B (k + 1)).ncard
              ≤ (B k ∪ ⋃ w ∈ B k, G.neighborSet w).ncard := Set.ncard_le_ncard h_sub
            _ ≤ (B k).ncard + (⋃ w ∈ B k, G.neighborSet w).ncard := Set.ncard_union_le _ _
            _ ≤ (B k).ncard + D * (B k).ncard := Nat.add_le_add_left h_biUnion_le _
            _ = (D + 1) * (B k).ncard := by ring
            _ ≤ (D + 1) * (D + 1) ^ k := Nat.mul_le_mul_left _ ih
            _ = (D + 1) ^ (k + 1) := by rw [pow_succ']
      have hS_sub : S ⊆ B m := fun v hv => hS_diam u₀ hu₀ v hv
      have hS_le : S.ncard ≤ (D + 1) ^ m := (Set.ncard_le_ncard hS_sub).trans (h_ball m)
      omega
  have hs2_lem : ∀ {D n : ℕ} {φ : ℝ} (G : SimpleGraph (Fin n)),
      IsBoundedDegreeEdgeExpander G D φ →
        {p : Fin n × Fin n | G.Adj p.1 p.2}.ncard ≤ D * n ∧
        ∀ (M : Set (Fin n)) (c : Fin n → ℕ),
          (∀ q : ℕ, 2 * {u ∈ M | c u = q}.ncard ≤ n) →
          φ * (n : ℝ) - (φ + (D : ℝ)) * ((Set.univ \ M).ncard : ℝ) ≤
            ({p : Fin n × Fin n | p.1 ∈ M ∧ p.2 ∈ M ∧ c p.1 ≠ c p.2 ∧ G.Adj p.1 p.2}.ncard : ℝ) := by
    intro D n φ G hG
    classical
    have h_out_deg : ∀ T : Set (Fin n),
        {p : Fin n × Fin n | p.1 ∈ T ∧ G.Adj p.1 p.2}.ncard ≤ D * T.ncard := by
      intro T
      have h_eq : {p : Fin n × Fin n | p.1 ∈ T ∧ G.Adj p.1 p.2}.toFinset =
          T.toFinset.biUnion (fun u => ({u} : Finset (Fin n)) ×ˢ (G.neighborSet u).toFinset) := by
        ext ⟨a, b⟩
        simp [SimpleGraph.mem_neighborSet]
      rw [Set.ncard_eq_toFinset_card', h_eq]
      calc (T.toFinset.biUnion (fun u => ({u} : Finset (Fin n)) ×ˢ (G.neighborSet u).toFinset)).card
          ≤ ∑ u ∈ T.toFinset, (({u} : Finset (Fin n)) ×ˢ (G.neighborSet u).toFinset).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ T.toFinset, D := by
          refine Finset.sum_le_sum (fun u _ => ?_)
          rw [Finset.card_product, Finset.card_singleton, one_mul, ← Set.ncard_eq_toFinset_card']
          exact hG.1 u
        _ = D * T.ncard := by
          rw [Finset.sum_const, smul_eq_mul, ← Set.ncard_eq_toFinset_card', mul_comm]
    refine ⟨?_, ?_⟩
    · have h_univ := h_out_deg Set.univ
      simpa [Nat.card_eq_fintype_card] using h_univ
    · intro M c h_small
      let R : Set (Fin n) := Set.univ \ M
      let A₁ : Set (Fin n × Fin n) :=
        {p | p.1 ∈ M ∧ p.2 ∈ M ∧ c p.1 ≠ c p.2 ∧ G.Adj p.1 p.2}
      let A₂ : Set (Fin n × Fin n) :=
        {p | p.1 ∈ M ∧ p.2 ∉ M ∧ G.Adj p.1 p.2}
      let Q : Finset ℕ := M.toFinset.image c
      let C : ℕ → Set (Fin n) := fun q => {u ∈ M | c u = q}
      let B : ℕ → Set (Fin n × Fin n) := fun q => {p | p.1 ∈ C q ∧ p.2 ∉ C q ∧ G.Adj p.1 p.2}
      have hM_part : M.ncard = ∑ q ∈ Q, (C q).ncard := by
        have h_disj : (Q : Set ℕ).PairwiseDisjoint (fun q => (C q).toFinset) := by
          intro q₁ _ q₂ _ hne
          dsimp [Function.onFun]
          rw [Finset.disjoint_left]
          intro u hu₁ hu₂
          simp only [C, Set.mem_toFinset, Set.mem_sep_iff] at hu₁ hu₂
          exact hne (hu₁.2.symm.trans hu₂.2)
        have h_eq : M.toFinset = Q.biUnion (fun q => (C q).toFinset) := by
          ext u
          simp only [Set.mem_toFinset, Finset.mem_biUnion, Q, Finset.mem_image, C, Set.mem_sep_iff]
          constructor
          · intro hu; exact ⟨c u, ⟨u, hu, rfl⟩, hu, rfl⟩
          · rintro ⟨_, _, hu, _⟩; exact hu
        rw [Set.ncard_eq_toFinset_card', h_eq, Finset.card_biUnion h_disj]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [Set.ncard_eq_toFinset_card']
      have hMR : M.ncard + R.ncard = n := by
        have hR_eq : R = Mᶜ := by ext x; simp [R]
        rw [hR_eq]
        simpa [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl M
      have hB_le : ∑ q ∈ Q, (B q).ncard ≤ A₁.ncard + A₂.ncard := by
        have h_disj : (Q : Set ℕ).PairwiseDisjoint (fun q => (B q).toFinset) := by
          intro q₁ _ q₂ _ hne
          dsimp [Function.onFun]
          rw [Finset.disjoint_left]
          intro p hp₁ hp₂
          simp only [B, C, Set.mem_toFinset, Set.mem_setOf_eq] at hp₁ hp₂
          exact hne (hp₁.1.2.symm.trans hp₂.1.2)
        have h_sub : Q.biUnion (fun q => (B q).toFinset) ⊆ A₁.toFinset ∪ A₂.toFinset := by
          intro p hp
          simp only [Finset.mem_biUnion, Q, Finset.mem_image, B, C, Set.mem_toFinset,
            Set.mem_setOf_eq] at hp
          rcases hp with ⟨q, _, ⟨hp1M, hcp1⟩, hp2nC, hadj⟩
          rw [Finset.mem_union, Set.mem_toFinset, Set.mem_toFinset]
          by_cases hp2M : p.2 ∈ M
          · left
            refine ⟨hp1M, hp2M, ?_, hadj⟩
            intro h_eq_c
            exact hp2nC ⟨hp2M, h_eq_c.symm.trans hcp1⟩
          · right
            exact ⟨hp1M, hp2M, hadj⟩
        calc ∑ q ∈ Q, (B q).ncard
            = ∑ q ∈ Q, (B q).toFinset.card := by
              refine Finset.sum_congr rfl (fun q _ => Set.ncard_eq_toFinset_card' _)
          _ = (Q.biUnion (fun q => (B q).toFinset)).card := (Finset.card_biUnion h_disj).symm
          _ ≤ (A₁.toFinset ∪ A₂.toFinset).card := Finset.card_le_card h_sub
          _ ≤ A₁.toFinset.card + A₂.toFinset.card := Finset.card_union_le _ _
          _ = A₁.ncard + A₂.ncard := by
            rw [← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card']
      have hA₂_le : A₂.ncard ≤ D * R.ncard := by
        have h_img : A₂.toFinset.image Prod.swap ⊆
            {q : Fin n × Fin n | q.1 ∈ R ∧ G.Adj q.1 q.2}.toFinset := by
          intro q hq
          simp only [Finset.mem_image, Set.mem_toFinset, A₂, R, Set.mem_setOf_eq,
            Set.mem_diff, Set.mem_univ, true_and] at hq ⊢
          rcases hq with ⟨⟨a, b⟩, ⟨_, hbM, hab⟩, rfl⟩
          exact ⟨hbM, G.symm hab⟩
        calc A₂.ncard
            = A₂.toFinset.card := Set.ncard_eq_toFinset_card' _
          _ = (A₂.toFinset.image Prod.swap).card :=
            (Finset.card_image_of_injective _ Prod.swap_injective).symm
          _ ≤ {q : Fin n × Fin n | q.1 ∈ R ∧ G.Adj q.1 q.2}.toFinset.card :=
            Finset.card_le_card h_img
          _ = {q : Fin n × Fin n | q.1 ∈ R ∧ G.Adj q.1 q.2}.ncard :=
            (Set.ncard_eq_toFinset_card' _).symm
          _ ≤ D * R.ncard := h_out_deg R
      have h_sum_exp : φ * (M.ncard : ℝ) ≤ ∑ q ∈ Q, ((B q).ncard : ℝ) := by
        rw [hM_part, Nat.cast_sum, Finset.mul_sum]
        exact Finset.sum_le_sum (fun q _ => hG.2 (C q) (h_small q))
      have hB_le_R : (∑ q ∈ Q, ((B q).ncard : ℝ)) ≤ (A₁.ncard : ℝ) + (A₂.ncard : ℝ) := by
        exact_mod_cast hB_le
      have hA₂_le_R : (A₂.ncard : ℝ) ≤ (D : ℝ) * (R.ncard : ℝ) := by
        exact_mod_cast hA₂_le
      have hMR_R : (M.ncard : ℝ) + (R.ncard : ℝ) = (n : ℝ) := by
        exact_mod_cast hMR
      change φ * (n : ℝ) - (φ + (D : ℝ)) * (R.ncard : ℝ) ≤ (A₁.ncard : ℝ)
      have h_lin1 : φ * (n : ℝ) = φ * (M.ncard : ℝ) + φ * (R.ncard : ℝ) := by
        rw [← hMR_R, mul_add]
      have h_lin2 : (φ + (D : ℝ)) * (R.ncard : ℝ) =
          φ * (R.ncard : ℝ) + (D : ℝ) * (R.ncard : ℝ) := add_mul _ _ _
      linarith
  have hs3_lem : ∀ (T : FiniteWeightedTree),
      ∃ (rt : T.Node) (lca : T.Node → T.Node → T.Node) (c : (ℝ → ℤ) → T.Node → ℕ),
        (∀ x y : T.Node,
          T.dist rt (lca x y) ≤ T.dist rt x ∧
          T.dist rt (lca x y) ≤ T.dist rt y ∧
          T.dist x y =
            (T.dist rt x - T.dist rt (lca x y)) + (T.dist rt y - T.dist rt (lca x y))) ∧
        (∀ g : ℝ → ℤ, Monotone g → ∀ x y : T.Node,
          c g x = c g y ↔
            g (T.dist rt x) = g (T.dist rt (lca x y)) ∧
            g (T.dist rt y) = g (T.dist rt (lca x y))) := by
    intro T
    classical
    haveI : Finite T.Node := T.finiteNode
    let P : ∀ a b : T.Node, T.tree.Walk a b :=
      fun a b => Classical.choose (T.isTree.existsUnique_path a b)
    have hP_path : ∀ a b : T.Node, (P a b).IsPath :=
      fun a b => (Classical.choose_spec (T.isTree.existsUnique_path a b)).1
    have hP_uniq : ∀ (a b : T.Node) (q : T.tree.Walk a b), q.IsPath → q = P a b :=
      fun a b q hq => (Classical.choose_spec (T.isTree.existsUnique_path a b)).2 q hq
    have h_ww_nonneg : ∀ {a b : T.Node} (p : T.tree.Walk a b), 0 ≤ walkWeight T.weight p := by
      intro a b p
      unfold walkWeight
      refine List.sum_nonneg ?_
      intro x hx
      rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
      exact T.weight_nonneg e (p.edges_subset_edgeSet he)
    have h_ww_path_le : ∀ {a b : T.Node} (p : T.tree.Walk a b),
        walkWeight T.weight (P a b) ≤ walkWeight T.weight p := by
      intro a b p
      let q : T.tree.Walk a b := (p.toPath : T.tree.Walk a b)
      have hq_eq : q = P a b := hP_uniq a b q p.toPath.2
      rw [← hq_eq]
      unfold walkWeight
      have h_sub : q.edges.Subperm p.edges :=
        List.subperm_of_subset p.toPath.2.isTrail.edges_nodup (SimpleGraph.Walk.edges_toPath_subset p)
      have h_mle : ((q.edges.map T.weight : List ℝ) : Multiset ℝ) ≤
          ((p.edges.map T.weight : List ℝ) : Multiset ℝ) := by
        simpa only [Multiset.map_coe] using Multiset.map_le_map (Multiset.coe_le.mpr h_sub)
      rcases Multiset.le_iff_exists_add.mp h_mle with ⟨u, hu⟩
      have hu_nonneg : 0 ≤ u.sum := by
        refine Multiset.sum_nonneg (fun x hx => ?_)
        have hx_mem : x ∈ ((p.edges.map T.weight : List ℝ) : Multiset ℝ) := by
          rw [hu]; exact Multiset.mem_add.mpr (Or.inr hx)
        rcases List.mem_map.mp (Multiset.mem_coe.mp hx_mem) with ⟨e, he, rfl⟩
        exact T.weight_nonneg e (p.edges_subset_edgeSet he)
      have h_sum_eq : (p.edges.map T.weight).sum = (q.edges.map T.weight).sum + u.sum := by
        have := congr_arg Multiset.sum hu
        simpa only [Multiset.sum_coe, Multiset.sum_add] using this
      linarith
    have h_dist_eq : ∀ a b : T.Node, T.dist a b = walkWeight T.weight (P a b) := by
      intro a b
      unfold FiniteWeightedTree.dist
      have h_iInf : (⨅ p : T.tree.Walk a b, ENNReal.ofReal (walkWeight T.weight p)) =
          ENNReal.ofReal (walkWeight T.weight (P a b)) :=
        le_antisymm (iInf_le _ (P a b))
          (le_iInf (fun p => ENNReal.ofReal_le_ofReal (h_ww_path_le p)))
      rw [h_iInf, ENNReal.toReal_ofReal (h_ww_nonneg (P a b))]
    have h_dist_nonneg : ∀ a b : T.Node, 0 ≤ T.dist a b :=
      fun a b => by rw [h_dist_eq]; exact h_ww_nonneg _
    have h_subpath : ∀ (a b w : T.Node), w ∈ (P a b).support →
        P a b = (P a w).append (P w b) := by
      intro a b w hw
      have h_sp := SimpleGraph.Walk.take_spec (P a b) hw
      have h_app_path : (((P a b).takeUntil w hw).append ((P a b).dropUntil w hw)).IsPath := by
        rw [h_sp]; exact hP_path a b
      have h1 : (P a b).takeUntil w hw = P a w :=
        hP_uniq a w _ (SimpleGraph.Walk.IsPath.of_append_left h_app_path)
      have h2 : (P a b).dropUntil w hw = P w b :=
        hP_uniq w b _ (SimpleGraph.Walk.IsPath.of_append_right h_app_path)
      rw [← h1, ← h2, h_sp]
    have h_ww_append : ∀ {a b d : T.Node} (p : T.tree.Walk a b) (q : T.tree.Walk b d),
        walkWeight T.weight (p.append q) = walkWeight T.weight p + walkWeight T.weight q := by
      intro a b d p q
      unfold walkWeight
      rw [SimpleGraph.Walk.edges_append, List.map_append, List.sum_append]
    have h_ww_rev : ∀ {a b : T.Node} (p : T.tree.Walk a b),
        walkWeight T.weight p.reverse = walkWeight T.weight p := by
      intro a b p
      unfold walkWeight
      rw [SimpleGraph.Walk.edges_reverse, List.map_reverse, List.sum_reverse]
    have h_dist_split : ∀ (a b w : T.Node), w ∈ (P a b).support →
        T.dist a b = T.dist a w + T.dist w b := by
      intro a b w hw
      rw [h_dist_eq a b, h_dist_eq a w, h_dist_eq w b, h_subpath a b w hw, h_ww_append]
    let rt : T.Node := Classical.choice T.isTree.isConnected.nonempty
    let S_anc : T.Node → T.Node → Finset T.Node :=
      fun x y => (P rt x).support.toFinset ∩ (P rt y).support.toFinset
    have hS_anc_ne : ∀ x y : T.Node, (S_anc x y).Nonempty := by
      intro x y
      refine ⟨rt, ?_⟩
      simp [S_anc, SimpleGraph.Walk.start_mem_support]
    let lca : T.Node → T.Node → T.Node := fun x y =>
      Classical.choose (Finset.exists_max_image (S_anc x y) (fun w => (P rt w).length) (hS_anc_ne x y))
    have hlca_spec : ∀ x y : T.Node,
        lca x y ∈ S_anc x y ∧ ∀ w ∈ S_anc x y, (P rt w).length ≤ (P rt (lca x y)).length :=
      fun x y => Classical.choose_spec
        (Finset.exists_max_image (S_anc x y) (fun w => (P rt w).length) (hS_anc_ne x y))
    have h_branch_path : ∀ (a x w : T.Node),
        a ∈ (P rt x).support → w ∈ (P a x).support →
        P rt w = (P rt a).append (P a w) := by
      intro a x w ha hw
      have h1 := h_subpath rt x a ha
      have h2 := h_subpath a x w hw
      rw [h2, SimpleGraph.Walk.append_assoc] at h1
      have h_path : (((P rt a).append (P a w)).append (P w x)).IsPath := by
        rw [← h1]; exact hP_path rt x
      exact (hP_uniq rt w _ (SimpleGraph.Walk.IsPath.of_append_left h_path)).symm
    have hP_xy_eq : ∀ x y : T.Node,
        P x y = (P (lca x y) x).reverse.append (P (lca x y) y) := by
      intro x y
      let z := lca x y
      have hz_mem := (hlca_spec x y).1
      simp only [S_anc, Finset.mem_inter, List.mem_toFinset] at hz_mem
      rcases hz_mem with ⟨hzx, hzy⟩
      symm
      refine hP_uniq x y _ ?_
      rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append,
        SimpleGraph.Walk.support_reverse]
      have h_nodup1 : (P z x).support.reverse.Nodup :=
        List.nodup_reverse.mpr ((SimpleGraph.Walk.isPath_def _).mp (hP_path z x))
      have h_zy_nodup : (P z y).support.Nodup :=
        (SimpleGraph.Walk.isPath_def _).mp (hP_path z y)
      have h_zy_cons : (P z y).support = z :: (P z y).support.tail :=
        SimpleGraph.Walk.support_eq_cons (P z y)
      rw [h_zy_cons, List.nodup_cons] at h_zy_nodup
      refine List.nodup_append.mpr ⟨h_nodup1, h_zy_nodup.2, ?_⟩
      intro w hw1 w' hw2 h_eq
      subst h_eq
      rw [List.mem_reverse] at hw1
      have hw_ne_z : w ≠ z := fun h => by subst h; exact h_zy_nodup.1 hw2
      have hw_zy : w ∈ (P z y).support := by rw [h_zy_cons]; exact List.mem_cons_of_mem z hw2
      have hw_rtx : w ∈ (P rt x).support := by
        rw [h_subpath rt x z hzx, SimpleGraph.Walk.support_append]
        rcases (List.mem_cons.mp (by rw [← SimpleGraph.Walk.support_eq_cons]; exact hw1)) with rfl | htail
        · exact False.elim (hw_ne_z rfl)
        · exact List.mem_append_right _ htail
      have hw_rty : w ∈ (P rt y).support := by
        rw [h_subpath rt y z hzy, SimpleGraph.Walk.support_append]
        exact List.mem_append_right _ hw2
      have hw_S : w ∈ S_anc x y := by
        simp [S_anc, hw_rtx, hw_rty]
      have h_rtw : P rt w = (P rt z).append (P z w) := h_branch_path z x w hzx hw1
      have h_len_eq : (P rt w).length = (P rt z).length + (P z w).length := by
        rw [h_rtw, SimpleGraph.Walk.length_append]
      have h_pos_zw : 1 ≤ (P z w).length := by
        cases hp : P z w with
        | nil => exact False.elim (hw_ne_z rfl)
        | cons _ _ => simp
      have h_max := (hlca_spec x y).2 w hw_S
      change (P rt w).length ≤ (P rt z).length at h_max
      omega
    let F : (ℝ → ℤ) → SimpleGraph T.Node := fun g =>
      { Adj := fun a b => T.tree.Adj a b ∧ g (T.dist rt a) = g (T.dist rt b)
        symm := fun _ _ h => ⟨T.tree.symm h.1, h.2.symm⟩
        loopless := fun a h => T.tree.loopless a h.1 }
    have hF_fin : ∀ g : ℝ → ℤ, Finite (F g).ConnectedComponent :=
      fun g => Finite.of_surjective (F g).connectedComponentMk (fun c => c.exists_rep)
    let c : (ℝ → ℤ) → T.Node → ℕ := fun g x =>
      letI : Finite (F g).ConnectedComponent := hF_fin g
      let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (F g).ConnectedComponent))
      (e ((F g).connectedComponentMk x)).val
    refine ⟨rt, lca, c, ?_, ?_⟩
    · intro x y
      let z := lca x y
      have hz_mem := (hlca_spec x y).1
      simp only [S_anc, Finset.mem_inter, List.mem_toFinset] at hz_mem
      rcases hz_mem with ⟨hzx, hzy⟩
      have hdx : T.dist rt x = T.dist rt z + T.dist z x := h_dist_split rt x z hzx
      have hdy : T.dist rt y = T.dist rt z + T.dist z y := h_dist_split rt y z hzy
      have hdxy : T.dist x y = T.dist z x + T.dist z y := by
        rw [h_dist_eq x y, hP_xy_eq x y, h_ww_append, h_ww_rev, ← h_dist_eq z x, ← h_dist_eq z y]
      have hzx_nn := h_dist_nonneg z x
      have hzy_nn := h_dist_nonneg z y
      refine ⟨by linarith, by linarith, by linarith⟩
    · intro g hg x y
      have hc_iff : c g x = c g y ↔ (F g).Reachable x y := by
        letI : Finite (F g).ConnectedComponent := hF_fin g
        let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (F g).ConnectedComponent))
        change (e ((F g).connectedComponentMk x)).val = (e ((F g).connectedComponentMk y)).val ↔ _
        rw [Fin.val_inj, e.injective.eq_iff, SimpleGraph.ConnectedComponent.eq]
      rw [hc_iff]
      let z := lca x y
      have hz_mem := (hlca_spec x y).1
      simp only [S_anc, Finset.mem_inter, List.mem_toFinset] at hz_mem
      rcases hz_mem with ⟨hzx, hzy⟩
      constructor
      · rintro ⟨W⟩
        have h_const_and_sub : ∀ {a b : T.Node} (W : (F g).Walk a b),
            (∀ u ∈ W.support, g (T.dist rt u) = g (T.dist rt a)) ∧
            ∃ W' : T.tree.Walk a b, W'.support ⊆ W.support := by
          intro a b W
          induction W with
          | nil =>
            refine ⟨?_, ⟨.nil, List.Subset.refl _⟩⟩
            intro u hu
            simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
            rw [hu]
          | @cons a b' d hab W' ih =>
            rcases ih with ⟨h_const', ⟨W_tree, h_sub'⟩⟩
            refine ⟨?_, ⟨.cons hab.1 W_tree, ?_⟩⟩
            · intro u hu
              simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
              rcases hu with rfl | hu'
              · rfl
              · rw [h_const' u hu', ← hab.2]
            · simp only [SimpleGraph.Walk.support_cons]
              exact List.cons_subset_cons a h_sub'
        rcases h_const_and_sub W with ⟨h_const, ⟨W_tree, h_sub⟩⟩
        have h_toPath_eq : (W_tree.toPath : T.tree.Walk x y) = P x y :=
          hP_uniq x y _ W_tree.toPath.2
        have hz_in_Pxy : z ∈ (P x y).support := by
          rw [hP_xy_eq x y, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse]
          apply List.mem_append_left
          rw [List.mem_reverse]
          exact SimpleGraph.Walk.start_mem_support (P z x)
        have hz_in_W : z ∈ W.support := by
          apply h_sub
          apply SimpleGraph.Walk.support_toPath_subset W_tree
          rw [h_toPath_eq]
          exact hz_in_Pxy
        have hy_in_W : y ∈ W.support := SimpleGraph.Walk.end_mem_support W
        have hgx := (h_const z hz_in_W).symm
        have hgy := (h_const y hy_in_W).trans hgx
        exact ⟨hgx, hgy⟩
      · rintro ⟨hgx, hgy⟩
        have h_on_Pxy : ∀ w ∈ (P x y).support, g (T.dist rt w) = g (T.dist rt z) := by
          intro w hw
          rw [hP_xy_eq x y, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse] at hw
          rcases List.mem_append.mp hw with hw_left | hw_right
          · rw [List.mem_reverse] at hw_left
            have h_rtw : P rt w = (P rt z).append (P z w) := h_branch_path z x w hzx hw_left
            have hd_zw : T.dist rt w = T.dist rt z + T.dist z w := by
              rw [h_dist_eq rt w, h_rtw, h_ww_append, ← h_dist_eq rt z, ← h_dist_eq z w]
            have hw_rtx : w ∈ (P rt x).support := by
              rw [h_subpath rt x z hzx, SimpleGraph.Walk.support_append]
              by_cases hwz : w = z
              · subst hwz; exact List.mem_append_left _ (SimpleGraph.Walk.end_mem_support _)
              · have htail : w ∈ (P z x).support.tail := by
                  have hc := SimpleGraph.Walk.support_eq_cons (P z x)
                  rw [hc] at hw_left
                  exact (List.mem_cons.mp hw_left).resolve_left hwz
                exact List.mem_append_right _ htail
            have hd_wx : T.dist rt x = T.dist rt w + T.dist w x := h_dist_split rt x w hw_rtx
            have h1 : T.dist rt z ≤ T.dist rt w := by linarith [h_dist_nonneg z w]
            have h2 : T.dist rt w ≤ T.dist rt x := by linarith [h_dist_nonneg w x]
            exact le_antisymm ((hg h2).trans_eq hgx) (hg h1)
          · have hw_zy : w ∈ (P z y).support := by
              rw [SimpleGraph.Walk.support_eq_cons (P z y)]
              exact List.mem_cons_of_mem z hw_right
            have h_rtw : P rt w = (P rt z).append (P z w) := h_branch_path z y w hzy hw_zy
            have hd_zw : T.dist rt w = T.dist rt z + T.dist z w := by
              rw [h_dist_eq rt w, h_rtw, h_ww_append, ← h_dist_eq rt z, ← h_dist_eq z w]
            have hw_rty : w ∈ (P rt y).support := by
              rw [h_subpath rt y z hzy, SimpleGraph.Walk.support_append]
              exact List.mem_append_right _ hw_right
            have hd_wy : T.dist rt y = T.dist rt w + T.dist w y := h_dist_split rt y w hw_rty
            have h1 : T.dist rt z ≤ T.dist rt w := by linarith [h_dist_nonneg z w]
            have h2 : T.dist rt w ≤ T.dist rt y := by linarith [h_dist_nonneg w y]
            exact le_antisymm ((hg h2).trans_eq hgy) (hg h1)
        have h_lift : ∀ {a b : T.Node} (W : T.tree.Walk a b),
            (∀ w ∈ W.support, g (T.dist rt w) = g (T.dist rt z)) →
            (F g).Reachable a b := by
          intro a b W
          induction W with
          | nil => intro _; exact SimpleGraph.Reachable.refl _
          | @cons a b' d hab W' ih =>
            intro hsup
            have ha : g (T.dist rt a) = g (T.dist rt z) :=
              hsup a (by simp [SimpleGraph.Walk.support_cons])
            have hb' : g (T.dist rt b') = g (T.dist rt z) :=
              hsup b' (by simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.start_mem_support])
            have hF_adj : (F g).Adj a b' := ⟨hab, ha.trans hb'.symm⟩
            have h_rem : ∀ w ∈ W'.support, g (T.dist rt w) = g (T.dist rt z) :=
              fun w hw => hsup w (by simp [SimpleGraph.Walk.support_cons, hw])
            exact hF_adj.reachable.trans (ih h_rem)
        exact h_lift (P x y) h_on_Pxy
  have hs4_lem : ∀ {K : ℕ}, 1 ≤ K → ∀ {r z₀ x₀ y₀ : ℝ}, 0 < r → z₀ ≤ x₀ → z₀ ≤ y₀ →
      let g : Fin K → ℝ → ℤ := fun i t => ⌊t / r + (i.1 : ℝ) / (K : ℝ)⌋
      (∀ i : Fin K, Monotone (g i)) ∧
      (∀ i : Fin K, g i x₀ = g i z₀ ∧ g i y₀ = g i z₀ → (x₀ - z₀) + (y₀ - z₀) < 2 * r) ∧
      ((Finset.univ.filter (fun i : Fin K => ¬(g i x₀ = g i z₀ ∧ g i y₀ = g i z₀))).card : ℝ) ≤
        (K : ℝ) * (((x₀ - z₀) + (y₀ - z₀)) / r) + 2 := by
    intro K hK r z₀ x₀ y₀ hr hx hy g
    have hK_pos : (0 : ℝ) < (K : ℝ) := by positivity
    have hK_int_pos : (0 : ℤ) < (K : ℤ) := by omega
    have h_mono : ∀ i : Fin K, Monotone (g i) := by
      intro i a b hab
      apply Int.floor_mono
      gcongr
    have h_diam : ∀ i : Fin K, g i x₀ = g i z₀ ∧ g i y₀ = g i z₀ →
        (x₀ - z₀) + (y₀ - z₀) < 2 * r := by
      intro i ⟨hxz, hyz⟩
      have h1 : x₀ - z₀ < r := by
        have hlt := Int.lt_floor_add_one (x₀ / r + (i.1 : ℝ) / (K : ℝ))
        have hle := Int.floor_le (z₀ / r + (i.1 : ℝ) / (K : ℝ))
        change x₀ / r + (i.1 : ℝ) / (K : ℝ) < (g i x₀ : ℝ) + 1 at hlt
        change (g i z₀ : ℝ) ≤ z₀ / r + (i.1 : ℝ) / (K : ℝ) at hle
        rw [hxz] at hlt
        have hdiv : (x₀ - z₀) / r < 1 := by
          rw [sub_div]
          linarith
        exact (div_lt_one hr).mp hdiv
      have h2 : y₀ - z₀ < r := by
        have hlt := Int.lt_floor_add_one (y₀ / r + (i.1 : ℝ) / (K : ℝ))
        have hle := Int.floor_le (z₀ / r + (i.1 : ℝ) / (K : ℝ))
        change y₀ / r + (i.1 : ℝ) / (K : ℝ) < (g i y₀ : ℝ) + 1 at hlt
        change (g i z₀ : ℝ) ≤ z₀ / r + (i.1 : ℝ) / (K : ℝ) at hle
        rw [hyz] at hlt
        have hdiv : (y₀ - z₀) / r < 1 := by
          rw [sub_div]
          linarith
        exact (div_lt_one hr).mp hdiv
      linarith
    have h_hermite : ∀ θ : ℝ, ∑ i : Fin K, ⌊θ + (i.1 : ℝ) / (K : ℝ)⌋ = ⌊(K : ℝ) * θ⌋ := by
      intro θ
      let m : ℤ := ⌊(K : ℝ) * θ⌋
      let q : ℤ := m / (K : ℤ)
      let t : ℤ := m % (K : ℤ)
      have ht0 : 0 ≤ t := Int.emod_nonneg m (by omega)
      have htK : t < (K : ℤ) := Int.emod_lt_of_pos m hK_int_pos
      have hm_eq : (K : ℤ) * q + t = m := Int.mul_ediv_add_emod m (K : ℤ)
      let tN : ℕ := t.toNat
      have htN_eq : (tN : ℤ) = t := Int.toNat_of_nonneg ht0
      have htN_lt : tN < K := by omega
      have hm_le : (m : ℝ) ≤ (K : ℝ) * θ := Int.floor_le _
      have hm_lt : (K : ℝ) * θ < (m : ℝ) + 1 := Int.lt_floor_add_one _
      have hm_R : (m : ℝ) = (K : ℝ) * (q : ℝ) + (tN : ℝ) := by
        have := congr_arg (Int.cast : ℤ → ℝ) hm_eq.symm
        rw [← htN_eq] at this
        push_cast at this
        exact this
      have h_term : ∀ i : Fin K,
          ⌊θ + (i.1 : ℝ) / (K : ℝ)⌋ = q + (if K - tN ≤ i.1 then (1 : ℤ) else 0) := by
        intro i
        have hi_lt : i.1 < K := i.2
        by_cases hi : K - tN ≤ i.1
        · rw [if_pos hi, Int.floor_eq_iff]
          have h_ge_K : (K : ℝ) ≤ (tN : ℝ) + (i.1 : ℝ) := by
            exact_mod_cast (by omega : K ≤ tN + i.1)
          have h_lt_2K : (tN : ℝ) + (i.1 : ℝ) + 1 ≤ 2 * (K : ℝ) - 1 := by
            have : tN + i.1 + 1 + 1 ≤ 2 * K := by omega
            have hR : ((tN + i.1 + 1 + 1 : ℕ) : ℝ) ≤ ((2 * K : ℕ) : ℝ) := by exact_mod_cast this
            push_cast at hR
            linarith
          constructor
          · rw [Int.cast_add, Int.cast_one]
            refine le_of_mul_le_mul_left ?_ hK_pos
            have hdiv : (K : ℝ) * (θ + (i.1 : ℝ) / (K : ℝ)) = (K : ℝ) * θ + (i.1 : ℝ) := by
              field_simp
            linarith
          · rw [Int.cast_add, Int.cast_one]
            refine lt_of_mul_lt_mul_left ?_ hK_pos.le
            have hdiv : (K : ℝ) * (θ + (i.1 : ℝ) / (K : ℝ)) = (K : ℝ) * θ + (i.1 : ℝ) := by
              field_simp
            linarith
        · rw [if_neg hi, add_zero, Int.floor_eq_iff]
          have h_lt_K : (tN : ℝ) + (i.1 : ℝ) + 1 ≤ (K : ℝ) := by
            exact_mod_cast (by omega : tN + i.1 + 1 ≤ K)
          have h_nonneg : (0 : ℝ) ≤ (tN : ℝ) + (i.1 : ℝ) := by positivity
          constructor
          · refine le_of_mul_le_mul_left ?_ hK_pos
            have hdiv : (K : ℝ) * (θ + (i.1 : ℝ) / (K : ℝ)) = (K : ℝ) * θ + (i.1 : ℝ) := by
              field_simp
            linarith
          · refine lt_of_mul_lt_mul_left ?_ hK_pos.le
            have hdiv : (K : ℝ) * (θ + (i.1 : ℝ) / (K : ℝ)) = (K : ℝ) * θ + (i.1 : ℝ) := by
              field_simp
            linarith
      have h_card : (Finset.univ.filter (fun i : Fin K => K - tN ≤ i.1)).card = tN := by
        have h_img : (Finset.univ.filter (fun i : Fin K => K - tN ≤ i.1)).image Fin.val =
            Finset.Ico (K - tN) K := by
          ext j
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
          constructor
          · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i.2⟩
          · rintro ⟨hj1, hj2⟩; exact ⟨⟨j, hj2⟩, hj1, rfl⟩
        calc (Finset.univ.filter (fun i : Fin K => K - tN ≤ i.1)).card
            = ((Finset.univ.filter (fun i : Fin K => K - tN ≤ i.1)).image Fin.val).card :=
              (Finset.card_image_of_injective _ Fin.val_injective).symm
          _ = (Finset.Ico (K - tN) K).card := by rw [h_img]
          _ = K - (K - tN) := Nat.card_Ico _ _
          _ = tN := by omega
      calc ∑ i : Fin K, ⌊θ + (i.1 : ℝ) / (K : ℝ)⌋
          = ∑ i : Fin K, (q + (if K - tN ≤ i.1 then (1 : ℤ) else 0)) :=
            Finset.sum_congr rfl (fun i _ => h_term i)
        _ = (∑ _i : Fin K, q) + ∑ i : Fin K, (if K - tN ≤ i.1 then (1 : ℤ) else 0) :=
            Finset.sum_add_distrib
        _ = (K : ℤ) * q + ((Finset.univ.filter (fun i : Fin K => K - tN ≤ i.1)).card : ℤ) := by
            simp [Finset.sum_boole]
        _ = (K : ℤ) * q + t := by rw [h_card, htN_eq]
        _ = m := hm_eq
    have h_branch : ∀ a b : ℝ, a ≤ b →
        ((Finset.univ.filter (fun i : Fin K => g i b ≠ g i a)).card : ℝ) ≤
          (K : ℝ) * ((b - a) / r) + 1 := by
      intro a b hab
      let θa : ℝ := a / r
      let θb : ℝ := b / r
      have hθ : θa ≤ θb := div_le_div_of_nonneg_right hab hr.le
      have h_int : ((Finset.univ.filter (fun i : Fin K => g i b ≠ g i a)).card : ℤ) ≤
          ⌊(K : ℝ) * θb⌋ - ⌊(K : ℝ) * θa⌋ := by
        calc ((Finset.univ.filter (fun i : Fin K => g i b ≠ g i a)).card : ℤ)
            = ∑ i : Fin K, (if g i b ≠ g i a then (1 : ℤ) else 0) := by
              rw [Finset.card_filter, Nat.cast_sum]
              refine Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
          _ ≤ ∑ i : Fin K, (g i b - g i a) := by
              refine Finset.sum_le_sum (fun i _ => ?_)
              have hle := h_mono i hab
              split_ifs with hne <;> omega
          _ = (∑ i : Fin K, g i b) - (∑ i : Fin K, g i a) := Finset.sum_sub_distrib _ _
          _ = ⌊(K : ℝ) * θb⌋ - ⌊(K : ℝ) * θa⌋ := by
              rw [← h_hermite θb, ← h_hermite θa]
      have h_real : ((Finset.univ.filter (fun i : Fin K => g i b ≠ g i a)).card : ℝ) ≤
          (⌊(K : ℝ) * θb⌋ : ℝ) - (⌊(K : ℝ) * θa⌋ : ℝ) := by
        exact_mod_cast h_int
      have h1 := Int.floor_le ((K : ℝ) * θb)
      have h2 := Int.sub_one_lt_floor ((K : ℝ) * θa)
      have h_diff : (K : ℝ) * θb - (K : ℝ) * θa = (K : ℝ) * ((b - a) / r) := by
        dsimp [θa, θb]
        ring
      linarith
    refine ⟨h_mono, h_diam, ?_⟩
    have h_sub : Finset.univ.filter (fun i : Fin K => ¬(g i x₀ = g i z₀ ∧ g i y₀ = g i z₀)) ⊆
        Finset.univ.filter (fun i : Fin K => g i x₀ ≠ g i z₀) ∪
        Finset.univ.filter (fun i : Fin K => g i y₀ ≠ g i z₀) := by
      intro i hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      tauto
    have h_card_nat :
        (Finset.univ.filter (fun i : Fin K => ¬(g i x₀ = g i z₀ ∧ g i y₀ = g i z₀))).card ≤
        (Finset.univ.filter (fun i : Fin K => g i x₀ ≠ g i z₀)).card +
        (Finset.univ.filter (fun i : Fin K => g i y₀ ≠ g i z₀)).card :=
      (Finset.card_le_card h_sub).trans (Finset.card_union_le _ _)
    have h_card_R :
        ((Finset.univ.filter (fun i : Fin K => ¬(g i x₀ = g i z₀ ∧ g i y₀ = g i z₀))).card : ℝ) ≤
        ((Finset.univ.filter (fun i : Fin K => g i x₀ ≠ g i z₀)).card : ℝ) +
        ((Finset.univ.filter (fun i : Fin K => g i y₀ ≠ g i z₀)).card : ℝ) := by
      exact_mod_cast h_card_nat
    have hbx := h_branch z₀ x₀ hx
    have hby := h_branch z₀ y₀ hy
    have h_alg : (K : ℝ) * ((x₀ - z₀) / r) + 1 + ((K : ℝ) * ((y₀ - z₀) / r) + 1) =
        (K : ℝ) * (((x₀ - z₀) + (y₀ - z₀)) / r) + 2 := by ring
    linarith
  have hs5_lem : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) {ε α A B r : ℝ},
      0 ≤ B → 0 < r → ∀ (μ : PMF (TreeEmbeddingSample V)),
        IsStochasticRamseyTreeEmbedding G ε α μ →
        (∀ s ∈ μ.support,
          A - B * ((Set.univ \ s.M).ncard : ℝ) ≤
            (1 / r) * ∑ p : V × V,
              {p : V × V | G.Adj p.1 p.2}.indicator (fun p => savedTreeDist s p.1 p.2) p) →
        A - B * ε * (Fintype.card V : ℝ) ≤
          (α / r) * ({p : V × V | G.Adj p.1 p.2}.ncard : ℝ) := by
    intro V _ G ε α A B r hB hr μ h_emb h_sample
    classical
    rcases h_emb with ⟨hα, h_fin, _h_dom, h_excl, h_edist⟩
    let S : Finset (TreeEmbeddingSample V) := h_fin.toFinset
    have h_out_S : ∀ s, s ∉ S → μ s = 0 := by
      intro s hs
      rw [Set.Finite.mem_toFinset, PMF.mem_support_iff, not_not] at hs
      exact hs
    have h_sum_one : ∑ s ∈ S, (μ s).toReal = 1 := by
      have h1 : ∑' s, μ s = 1 := PMF.tsum_coe μ
      rw [tsum_eq_sum h_out_S] at h1
      have h2 := congr_arg ENNReal.toReal h1
      rw [ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top μ s), ENNReal.toReal_one] at h2
      exact h2
    have h_excl_sum : ∑ s ∈ S, (μ s).toReal * ((Set.univ \ s.M).ncard : ℝ) ≤
        ε * (Fintype.card V : ℝ) := by
      have h_ncard_eq : ∀ s : TreeEmbeddingSample V,
          ((Set.univ \ s.M).ncard : ℝ) = ∑ v : V, (if v ∉ s.M then (1 : ℝ) else 0) := by
        intro s
        have h_fin_eq : (Set.univ \ s.M).toFinset = Finset.univ.filter (fun v : V => v ∉ s.M) := by
          ext v; simp
        rw [Set.ncard_eq_toFinset_card', h_fin_eq, Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl (fun v _ => by split_ifs <;> simp)
      calc ∑ s ∈ S, (μ s).toReal * ((Set.univ \ s.M).ncard : ℝ)
          = ∑ s ∈ S, ∑ v : V, (μ s).toReal * (if v ∉ s.M then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [h_ncard_eq s, Finset.mul_sum]
        _ = ∑ v : V, ∑ s ∈ S, (if v ∉ s.M then (μ s).toReal else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun s _ => ?_))
            split_ifs <;> ring
        _ ≤ ∑ _v : V, ε := by
            refine Finset.sum_le_sum (fun v _ => ?_)
            let Ev : Set (TreeEmbeddingSample V) := {s | v ∉ s.M}
            have h_ev := h_excl v
            rw [PMF.toOuterMeasure_apply] at h_ev
            have h_tsum : ∑' s, Ev.indicator μ s = ∑ s ∈ S, Ev.indicator μ s :=
              tsum_eq_sum (fun s hs => Set.indicator_apply_eq_zero.mpr (fun _ => h_out_S s hs))
            rw [h_tsum, ENNReal.toReal_sum] at h_ev
            · convert h_ev using 1
              refine Finset.sum_congr rfl (fun s _ => ?_)
              by_cases hv : v ∉ s.M
              · simp [Ev, hv]
              · simp [Ev, hv]
            · intro s _
              by_cases hv : s ∈ Ev
              · rw [Set.indicator_of_mem hv]; exact PMF.apply_ne_top μ s
              · rw [Set.indicator_of_notMem hv]; exact ENNReal.zero_ne_top
        _ = ε * (Fintype.card V : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    let E_adj : Set (V × V) := {p : V × V | G.Adj p.1 p.2}
    have h_edge_sum :
        ∑ s ∈ S, (μ s).toReal *
          (∑ p : V × V, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) ≤
        α * (E_adj.ncard : ℝ) := by
      calc ∑ s ∈ S, (μ s).toReal *
            (∑ p : V × V, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p)
          = ∑ p : V × V, ∑ s ∈ S,
              (μ s).toReal * E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p := by
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
        _ ≤ ∑ p : V × V, E_adj.indicator (fun _ => α) p := by
            refine Finset.sum_le_sum (fun p _ => ?_)
            by_cases hp : p ∈ E_adj
            · rw [Set.indicator_of_mem hp]
              simp_rw [Set.indicator_of_mem hp]
              have h_tsum : ∑ s ∈ S, (μ s).toReal * savedTreeDist s p.1 p.2 =
                  ∑' s, (μ s).toReal * savedTreeDist s p.1 p.2 := by
                refine (tsum_eq_sum (fun s hs => ?_)).symm
                rw [h_out_S s hs, ENNReal.toReal_zero, zero_mul]
              rw [h_tsum]
              have h_dist1 : graphDist G p.1 p.2 = 1 := by
                unfold graphDist
                have hd : G.dist p.1 p.2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hp
                rw [hd, Nat.cast_one]
              have h_ed := h_edist p.1 p.2
              rw [h_dist1, mul_one] at h_ed
              exact h_ed
            · rw [Set.indicator_of_notMem hp]
              simp_rw [Set.indicator_of_notMem hp, mul_zero, Finset.sum_const_zero]
              exact le_rfl
        _ = α * (E_adj.ncard : ℝ) := by
            have h_fin_eq : E_adj.toFinset = Finset.univ.filter (fun p : V × V => p ∈ E_adj) := by
              ext p; simp
            have h_ind_sum : (∑ p : V × V, E_adj.indicator (fun _ => α) p) =
                ∑ p : V × V, α * (if p ∈ E_adj then (1 : ℝ) else 0) := by
              refine Finset.sum_congr rfl (fun p _ => ?_)
              by_cases hp : p ∈ E_adj <;> simp [hp]
            rw [h_ind_sum, ← Finset.mul_sum, Finset.sum_boole,
              Set.ncard_eq_toFinset_card', h_fin_eq]
    have h_weighted :
        ∑ s ∈ S, (μ s).toReal * (A - B * ((Set.univ \ s.M).ncard : ℝ)) ≤
        ∑ s ∈ S, (μ s).toReal *
          ((1 / r) * ∑ p : V × V, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) := by
      refine Finset.sum_le_sum (fun s hs => ?_)
      have hs_mem : s ∈ μ.support := (Set.Finite.mem_toFinset h_fin).mp hs
      exact mul_le_mul_of_nonneg_left (h_sample s hs_mem) ENNReal.toReal_nonneg
    have h_lhs :
        ∑ s ∈ S, (μ s).toReal * (A - B * ((Set.univ \ s.M).ncard : ℝ)) =
        A - B * (∑ s ∈ S, (μ s).toReal * ((Set.univ \ s.M).ncard : ℝ)) := by
      have h1 : ∑ s ∈ S, (μ s).toReal * (A - B * ((Set.univ \ s.M).ncard : ℝ)) =
          (∑ s ∈ S, (μ s).toReal * A) -
          (∑ s ∈ S, (μ s).toReal * (B * ((Set.univ \ s.M).ncard : ℝ))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun s _ => by ring)
      have h2 : ∑ s ∈ S, (μ s).toReal * A = A := by
        rw [← Finset.sum_mul, h_sum_one, one_mul]
      have h3 : ∑ s ∈ S, (μ s).toReal * (B * ((Set.univ \ s.M).ncard : ℝ)) =
          B * ∑ s ∈ S, (μ s).toReal * ((Set.univ \ s.M).ncard : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => by ring)
      rw [h1, h2, h3]
    have h_rhs :
        ∑ s ∈ S, (μ s).toReal *
          ((1 / r) * ∑ p : V × V, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) =
        (1 / r) * ∑ s ∈ S, (μ s).toReal *
          (∑ p : V × V, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => by ring)
    rw [h_lhs, h_rhs] at h_weighted
    have hB_le : B * (∑ s ∈ S, (μ s).toReal * ((Set.univ \ s.M).ncard : ℝ)) ≤
        B * (ε * (Fintype.card V : ℝ)) :=
      mul_le_mul_of_nonneg_left h_excl_sum hB
    have hr_le : (1 / r) * (∑ s ∈ S, (μ s).toReal *
        (∑ p : V × V, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p)) ≤
        (1 / r) * (α * (E_adj.ncard : ℝ)) :=
      mul_le_mul_of_nonneg_left h_edge_sum (by positivity)
    have h_alg : (1 / r) * (α * (E_adj.ncard : ℝ)) = (α / r) * (E_adj.ncard : ℝ) := by ring
    linarith
  classical
  rcases h_exp with ⟨D, φ, hD, hφ, h_fam⟩
  have hD_gt0 : 0 < D := by omega
  have hD_pos : (0 : ℝ) < (D : ℝ) := Nat.cast_pos.mpr hD_gt0
  have hD1_gt1 : (1 : ℝ) < (D : ℝ) + 1 := by
    have : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    linarith
  have hlog_pos : 0 < Real.logb 2 ((D : ℝ) + 1) := Real.logb_pos (by norm_num) hD1_gt1
  let c : ℝ := φ / (16 * (D : ℝ) * Real.logb 2 ((D : ℝ) + 1))
  have hc_pos : 0 < c := div_pos hφ (by positivity)
  let ε₀ : ℝ := min (1 / 2) (φ / (2 * (φ + (D : ℝ))))
  have hφD_pos : 0 < φ + (D : ℝ) := by linarith
  have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (div_pos hφ (by positivity))
  have hε₀_lt1 : ε₀ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨c, ε₀, hc_pos, hε₀_pos, hε₀_lt1, ?_⟩
  intro ε hε_pos hε_le N₀ hN₀
  let N₁ : ℕ := max N₀ (2 * (D + 1))
  rcases h_fam N₁ with ⟨n, G, hn_N₁, hG_exp⟩
  have hN₀_le : N₀ ≤ n := (le_max_left _ _).trans hn_N₁
  have h2D1_le : 2 * (D + 1) ≤ n := (le_max_right _ _).trans hn_N₁
  have hn2 : 2 ≤ n := by omega
  have hn_gt0 : 0 < n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_gt0
  have hs1 := hs1_lem hφ hn2 G hG_exp
  have hs2 := hs2_lem G hG_exp
  refine ⟨Fin n, inferInstance, G, hs1.1, ?_, ?_⟩
  · simpa using hN₀_le
  · intro α hα μ h_emb
    let m : ℕ := Nat.log (D + 1) (n / 2)
    have hm_ge1 : 1 ≤ m :=
      Nat.le_log_of_pow_le (by omega) (by simpa only [pow_one] using (by omega : D + 1 ≤ n / 2))
    have hm_pow_le : 2 * (D + 1) ^ m ≤ n := by
      have h1 : (D + 1) ^ m ≤ n / 2 := Nat.pow_log_le_self (D + 1) (by omega)
      omega
    have hn_le_pow : n ≤ (D + 1) ^ (2 * (m + 1)) := by
      have hlt : n / 2 < (D + 1) ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) (n / 2)
      have h1 : n ≤ 2 * (n / 2 + 1) := by omega
      have h2 : 2 * (n / 2 + 1) ≤ (D + 1) * (D + 1) ^ (m + 1) :=
        Nat.mul_le_mul (by omega) hlt
      have h3 : (D + 1) * (D + 1) ^ (m + 1) = (D + 1) ^ (m + 2) :=
        (pow_succ' (D + 1) (m + 1)).symm
      have h4 : (D + 1) ^ (m + 2) ≤ (D + 1) ^ (2 * (m + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    let Δ : ℝ := (m + 1 : ℝ)
    have hΔ_pos : 0 < Δ := by positivity
    let r : ℝ := Δ / 2
    have hr_pos : 0 < r := by positivity
    let K : ℕ := ⌈8 * (D : ℝ) / φ⌉₊
    have h8Dφ_pos : 0 < 8 * (D : ℝ) / φ := by positivity
    have hK_ge1 : 1 ≤ K := Nat.succ_le_of_lt (Nat.ceil_pos.mpr h8Dφ_pos)
    have hK_pos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr (by omega)
    have hK_ge_frac : 8 * (D : ℝ) / φ ≤ (K : ℝ) := Nat.le_ceil _
    let E_adj : Set (Fin n × Fin n) := {p : Fin n × Fin n | G.Adj p.1 p.2}
    let A : ℝ := φ * (n : ℝ) - 2 * (D : ℝ) * (n : ℝ) / (K : ℝ)
    let B : ℝ := φ + (D : ℝ)
    have h_sample : ∀ s ∈ μ.support,
        A - B * ((Set.univ \ s.M).ncard : ℝ) ≤
          (1 / r) * ∑ p : Fin n × Fin n,
            E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p := by
      intro s hs
      have h_dom : ∀ u v : Fin n, graphDist G u v ≤ s.T.dist (s.f u) (s.f v) :=
        h_emb.2.2.1 s hs
      rcases hs3_lem s.T with ⟨rt, lca, c_T, h_lca_dist, h_cut_iff⟩
      let g : Fin K → ℝ → ℤ := fun i t => ⌊t / r + (i.1 : ℝ) / (K : ℝ)⌋
      let c_i : Fin K → Fin n → ℕ := fun i u => c_T (g i) (s.f u)
      have h_small_clusters : ∀ (i : Fin K) (q : ℕ),
          2 * {u ∈ s.M | c_i i u = q}.ncard ≤ n := by
        intro i q
        refine hs1.2 m hm_pow_le {u ∈ s.M | c_i i u = q} ?_
        intro u hu v hv
        simp only [Set.mem_sep_iff] at hu hv
        have hc_eq : c_T (g i) (s.f u) = c_T (g i) (s.f v) := hu.2.trans hv.2.symm
        have hlca_uv := h_lca_dist (s.f u) (s.f v)
        have hs4_uv := hs4_lem hK_ge1 hr_pos hlca_uv.1 hlca_uv.2.1
        have hg_eq := (h_cut_iff (g i) (hs4_uv.1 i) (s.f u) (s.f v)).mp hc_eq
        have hT_lt : s.T.dist (s.f u) (s.f v) < 2 * r := by
          rw [hlca_uv.2.2]
          exact hs4_uv.2.1 i hg_eq
        have hG_lt : ((G.dist u v : ℕ) : ℝ) < ((m + 1 : ℕ) : ℝ) := by
          have hd := h_dom u v
          unfold graphDist at hd
          have h2r : 2 * r = ((m + 1 : ℕ) : ℝ) := by
            dsimp [r, Δ]; push_cast; ring
          linarith
        have hG_lt_nat : G.dist u v < m + 1 := Nat.cast_lt.mp hG_lt
        omega
      let Cut : Fin K → Set (Fin n × Fin n) := fun i =>
        {p | p.1 ∈ s.M ∧ p.2 ∈ s.M ∧ c_i i p.1 ≠ c_i i p.2 ∧ G.Adj p.1 p.2}
      have h_cut_lb : ∀ i : Fin K,
          φ * (n : ℝ) - B * ((Set.univ \ s.M).ncard : ℝ) ≤ ((Cut i).ncard : ℝ) :=
        fun i => hs2.2 s.M (c_i i) (h_small_clusters i)
      have h_sum_lb :
          (K : ℝ) * (φ * (n : ℝ) - B * ((Set.univ \ s.M).ncard : ℝ)) ≤
          ∑ i : Fin K, ((Cut i).ncard : ℝ) := by
        calc (K : ℝ) * (φ * (n : ℝ) - B * ((Set.univ \ s.M).ncard : ℝ))
            = ∑ _i : Fin K, (φ * (n : ℝ) - B * ((Set.univ \ s.M).ncard : ℝ)) := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          _ ≤ ∑ i : Fin K, ((Cut i).ncard : ℝ) := Finset.sum_le_sum (fun i _ => h_cut_lb i)
      have h_cut_as_sum : ∀ i : Fin K,
          ((Cut i).ncard : ℝ) = ∑ p : Fin n × Fin n, (if p ∈ Cut i then (1 : ℝ) else 0) := by
        intro i
        have h_eq : (Cut i).toFinset = Finset.univ.filter (fun p => p ∈ Cut i) := by ext p; simp
        rw [Set.ncard_eq_toFinset_card', h_eq, Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl (fun p _ => by split_ifs <;> simp)
      have h_pointwise : ∀ p : Fin n × Fin n,
          (∑ i : Fin K, (if p ∈ Cut i then (1 : ℝ) else 0)) ≤
            ((K : ℝ) / r) * E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p +
            E_adj.indicator (fun _ => (2 : ℝ)) p := by
        intro p
        by_cases hp_adj : p ∈ E_adj
        · rw [Set.indicator_of_mem hp_adj, Set.indicator_of_mem hp_adj]
          have hp_adj' : G.Adj p.1 p.2 := hp_adj
          by_cases hpM : p.1 ∈ s.M ∧ p.2 ∈ s.M
          · have h_saved : savedTreeDist s p.1 p.2 = s.T.dist (s.f p.1) (s.f p.2) := by
              unfold savedTreeDist
              exact if_pos hpM
            have hlca_p := h_lca_dist (s.f p.1) (s.f p.2)
            have hs4_p := hs4_lem hK_ge1 hr_pos hlca_p.1 hlca_p.2.1
            have h_iff_p : ∀ i : Fin K,
                p ∈ Cut i ↔ ¬(g i (s.T.dist rt (s.f p.1)) =
                    g i (s.T.dist rt (lca (s.f p.1) (s.f p.2))) ∧
                  g i (s.T.dist rt (s.f p.2)) =
                    g i (s.T.dist rt (lca (s.f p.1) (s.f p.2)))) := by
              intro i
              have hm_i : Monotone (g i) := hs4_p.1 i
              simp only [Cut, Set.mem_setOf_eq, c_i, hpM.1, hpM.2, hp_adj', true_and, and_true, ne_eq]
              exact not_congr (h_cut_iff (g i) hm_i (s.f p.1) (s.f p.2))
            have h_lhs_eq : (∑ i : Fin K, (if p ∈ Cut i then (1 : ℝ) else 0)) =
                ((Finset.univ.filter (fun i : Fin K =>
                  ¬(g i (s.T.dist rt (s.f p.1)) =
                      g i (s.T.dist rt (lca (s.f p.1) (s.f p.2))) ∧
                    g i (s.T.dist rt (s.f p.2)) =
                      g i (s.T.dist rt (lca (s.f p.1) (s.f p.2)))))).card : ℝ) := by
              rw [Finset.card_filter, Nat.cast_sum]
              refine Finset.sum_congr rfl (fun i _ => ?_)
              by_cases hc : p ∈ Cut i
              · rw [if_pos hc, if_pos ((h_iff_p i).mp hc)]; simp
              · rw [if_neg hc, if_neg (fun h => hc ((h_iff_p i).mpr h))]; simp
            rw [h_lhs_eq, h_saved]
            have h_bound := hs4_p.2.2
            rw [← hlca_p.2.2] at h_bound
            have h_alg : (K : ℝ) * (s.T.dist (s.f p.1) (s.f p.2) / r) + 2 =
                ((K : ℝ) / r) * s.T.dist (s.f p.1) (s.f p.2) + 2 := by ring
            linarith
          · have h_zero : (∑ i : Fin K, (if p ∈ Cut i then (1 : ℝ) else 0)) = 0 := by
              refine Finset.sum_eq_zero (fun i _ => ?_)
              rw [if_neg]
              intro hp_cut
              exact hpM ⟨hp_cut.1, hp_cut.2.1⟩
            have h_saved : savedTreeDist s p.1 p.2 = 0 := by
              unfold savedTreeDist
              exact if_neg hpM
            rw [h_zero, h_saved, mul_zero, zero_add]
            norm_num
        · rw [Set.indicator_of_notMem hp_adj, Set.indicator_of_notMem hp_adj, mul_zero, add_zero]
          have h_zero : (∑ i : Fin K, (if p ∈ Cut i then (1 : ℝ) else 0)) = 0 := by
            refine Finset.sum_eq_zero (fun i _ => ?_)
            rw [if_neg]
            intro hp_cut
            exact hp_adj hp_cut.2.2.2
          rw [h_zero]
      have h_sum_ub :
          (∑ i : Fin K, ((Cut i).ncard : ℝ)) ≤
          ((K : ℝ) / r) * (∑ p : Fin n × Fin n, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) +
          2 * (D : ℝ) * (n : ℝ) := by
        have h_2E : (∑ p : Fin n × Fin n, E_adj.indicator (fun _ => (2 : ℝ)) p) ≤
            2 * (D : ℝ) * (n : ℝ) := by
          have h_fin_eq : E_adj.toFinset = Finset.univ.filter (fun p => p ∈ E_adj) := by ext p; simp
          have h_ind_eq : (∑ p : Fin n × Fin n, E_adj.indicator (fun _ => (2 : ℝ)) p) =
              2 * (E_adj.ncard : ℝ) := by
            calc (∑ p : Fin n × Fin n, E_adj.indicator (fun _ => (2 : ℝ)) p)
                = ∑ p : Fin n × Fin n, (2 : ℝ) * (if p ∈ E_adj then (1 : ℝ) else 0) := by
                  refine Finset.sum_congr rfl (fun p _ => by by_cases hp : p ∈ E_adj <;> simp [hp])
              _ = 2 * (E_adj.ncard : ℝ) := by
                  rw [← Finset.mul_sum, Finset.sum_boole, Set.ncard_eq_toFinset_card', h_fin_eq]
          have hE_le : (E_adj.ncard : ℝ) ≤ (D : ℝ) * (n : ℝ) := by exact_mod_cast hs2.1
          linarith
        calc (∑ i : Fin K, ((Cut i).ncard : ℝ))
            = ∑ i : Fin K, ∑ p : Fin n × Fin n, (if p ∈ Cut i then (1 : ℝ) else 0) :=
              Finset.sum_congr rfl (fun i _ => h_cut_as_sum i)
          _ = ∑ p : Fin n × Fin n, ∑ i : Fin K, (if p ∈ Cut i then (1 : ℝ) else 0) :=
              Finset.sum_comm
          _ ≤ ∑ p : Fin n × Fin n,
                (((K : ℝ) / r) * E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p +
                E_adj.indicator (fun _ => (2 : ℝ)) p) :=
              Finset.sum_le_sum (fun p _ => h_pointwise p)
          _ = ((K : ℝ) / r) * (∑ p : Fin n × Fin n, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) +
              (∑ p : Fin n × Fin n, E_adj.indicator (fun _ => (2 : ℝ)) p) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ ≤ ((K : ℝ) / r) * (∑ p : Fin n × Fin n, E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) +
              2 * (D : ℝ) * (n : ℝ) := by linarith
      have h_comb := h_sum_lb.trans h_sum_ub
      refine le_of_mul_le_mul_left ?_ hK_pos
      have h_lhs_mul : (K : ℝ) * (A - B * ((Set.univ \ s.M).ncard : ℝ)) =
          (K : ℝ) * (φ * (n : ℝ) - B * ((Set.univ \ s.M).ncard : ℝ)) - 2 * (D : ℝ) * (n : ℝ) := by
        dsimp [A]
        field_simp
        ring
      have h_rhs_mul : (K : ℝ) * ((1 / r) * ∑ p : Fin n × Fin n,
            E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p) =
          ((K : ℝ) / r) * ∑ p : Fin n × Fin n,
            E_adj.indicator (fun p => savedTreeDist s p.1 p.2) p := by ring
      linarith
    have h_exp_ineq := hs5_lem G hφD_pos.le hr_pos μ h_emb h_sample
    rw [Fintype.card_fin] at h_exp_ineq
    have h_rhs_ub : (α / r) * (E_adj.ncard : ℝ) ≤ (α / r) * ((D : ℝ) * (n : ℝ)) := by
      have hE_le : (E_adj.ncard : ℝ) ≤ (D : ℝ) * (n : ℝ) := by exact_mod_cast hs2.1
      exact mul_le_mul_of_nonneg_left hE_le (div_nonneg hα hr_pos.le)
    have h_2Dn_K : 2 * (D : ℝ) * (n : ℝ) / (K : ℝ) ≤ (φ / 4) * (n : ℝ) := by
      rw [div_le_iff₀ hK_pos]
      have h8D : 8 * (D : ℝ) ≤ (K : ℝ) * φ := (div_le_iff₀ hφ).mp hK_ge_frac
      nlinarith
    have h_Bε : B * ε * (n : ℝ) ≤ (φ / 2) * (n : ℝ) := by
      have hε_bound : ε ≤ φ / (2 * B) := hε_le.trans (min_le_right _ _)
      have hBε_le : B * ε ≤ φ / 2 := by
        have := mul_le_mul_of_nonneg_left hε_bound hφD_pos.le
        have h_eq : B * (φ / (2 * B)) = φ / 2 := by
          have hB_ne : B ≠ 0 := hφD_pos.ne'
          field_simp
        linarith
      exact mul_le_mul_of_nonneg_right hBε_le hn_pos.le
    have h_lhs_lb : (φ / 4) * (n : ℝ) ≤ A - B * ε * (n : ℝ) := by
      dsimp [A]
      linarith
    have h_n_ineq : (φ / 4) * (n : ℝ) ≤ (α / r) * ((D : ℝ) * (n : ℝ)) :=
      h_lhs_lb.trans (h_exp_ineq.trans h_rhs_ub)
    have h_cancel_n : φ / 4 ≤ (α / r) * (D : ℝ) := by
      refine le_of_mul_le_mul_right ?_ hn_pos
      linarith
    have h_α_lb : φ * Δ / (8 * (D : ℝ)) ≤ α := by
      have h_mul := mul_le_mul_of_nonneg_right h_cancel_n (show 0 ≤ r / (D : ℝ) by positivity)
      have h_lhs_eq : (φ / 4) * (r / (D : ℝ)) = φ * Δ / (8 * (D : ℝ)) := by
        dsimp [r]
        ring
      have h_rhs_eq : ((α / r) * (D : ℝ)) * (r / (D : ℝ)) = α := by
        have hr_ne : r ≠ 0 := hr_pos.ne'
        have hD_ne : (D : ℝ) ≠ 0 := hD_pos.ne'
        field_simp
      linarith
    have h_log_ub : Real.logb 2 (n : ℝ) ≤ 2 * Δ * Real.logb 2 ((D : ℝ) + 1) := by
      have hn_pow_R : (n : ℝ) ≤ ((D : ℝ) + 1) ^ (2 * (m + 1)) := by
        exact_mod_cast hn_le_pow
      calc Real.logb 2 (n : ℝ)
          ≤ Real.logb 2 (((D : ℝ) + 1) ^ (2 * (m + 1))) :=
            Real.logb_le_logb_of_le (by norm_num) hn_pos hn_pow_R
        _ = ((2 * (m + 1) : ℕ) : ℝ) * Real.logb 2 ((D : ℝ) + 1) := Real.logb_pow _ _ _
        _ = 2 * Δ * Real.logb 2 ((D : ℝ) + 1) := by
            dsimp [Δ]; push_cast; ring
    calc c * Real.logb 2 (Fintype.card (Fin n) : ℝ)
        = c * Real.logb 2 (n : ℝ) := by rw [Fintype.card_fin]
      _ ≤ c * (2 * Δ * Real.logb 2 ((D : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h_log_ub hc_pos.le
      _ = φ * Δ / (8 * (D : ℝ)) := by
          dsimp [c]
          have hD_ne : (D : ℝ) ≠ 0 := hD_pos.ne'
          have hlog_ne : Real.logb 2 ((D : ℝ) + 1) ≠ 0 := hlog_pos.ne'
          field_simp
          ring
      _ ≤ α := h_α_lb

theorem thm4_ramsey_tree_lower_bound : Theorem4 :=
by
  have s1 : ∀ g : ℕ, 3 ≤ g →
      ∃ (m : ℕ) (H : SimpleGraph (Fin m)),
        g ≤ m ∧ m ≤ 16 ^ g ∧ H.Connected ∧
        (∀ v : Fin m, (H.neighborSet v).ncard ≤ 3) ∧
        5 * m < 4 * H.edgeSet.ncard ∧ 2 * H.edgeSet.ncard ≤ 3 * m ∧
        (∀ (u : Fin m) (c : H.Walk u u), c.IsCycle → g ≤ c.length) := by
    intro g hg3
    classical
    let m₀ : ℕ := 16 ^ g
    have hm₀Pos : 0 < m₀ := by positivity
    let V₀ := Fin m₀
    have hCardV₀ : Fintype.card V₀ = m₀ := Fintype.card_fin m₀
    let Good (G : SimpleGraph V₀) : Prop :=
      (∀ v : V₀, (G.neighborSet v).ncard ≤ 3) ∧
      (∀ (u : V₀) (c : G.Walk u u), c.IsCycle → g ≤ c.length)
    have hGoodBot : Good (⊥ : SimpleGraph V₀) := by
      refine ⟨fun v => by
        have hEmp : (⊥ : SimpleGraph V₀).neighborSet v = ∅ := by ext x; simp
        rw [hEmp, Set.ncard_empty]; omega,
        fun u c hc => False.elim (hc.ne_bot rfl)⟩
    let maxE : ℕ := Fintype.card (Sym2 V₀)
    have hEdgeLeMax : ∀ G : SimpleGraph V₀, G.edgeSet.ncard ≤ maxE := by
      intro G
      rw [Set.ncard_eq_toFinset_card']
      exact Finset.card_le_univ _
    let Kset : Finset ℕ :=
      (Finset.range (maxE + 1)).filter (fun k => ∃ G : SimpleGraph V₀, Good G ∧ G.edgeSet.ncard = k)
    have h0Mem : 0 ∈ Kset := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr (Nat.zero_lt_succ maxE), ⟨⊥, hGoodBot, by simp⟩⟩
    let kMax : ℕ := Kset.max' ⟨0, h0Mem⟩
    have hkMaxMem : kMax ∈ Kset := Finset.max'_mem Kset ⟨0, h0Mem⟩
    obtain ⟨G₀, hG₀Good, hG₀Card⟩ := (Finset.mem_filter.mp hkMaxMem).2
    have hG₀Max : ∀ G₁ : SimpleGraph V₀, Good G₁ → G₁.edgeSet.ncard ≤ G₀.edgeSet.ncard := by
      intro G₁ hG₁
      rw [hG₀Card]
      apply Finset.le_max'
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hEdgeLeMax G₁)), ⟨G₁, hG₁, rfl⟩⟩
    have hG₀Deg : ∀ v : V₀, G₀.degree v ≤ 3 := by
      intro v
      have h1 := hG₀Good.1 v
      rw [Set.ncard_eq_toFinset_card'] at h1
      have hEq : (G₀.neighborSet v).toFinset = G₀.neighborFinset v := by ext y; simp
      rw [hEq, SimpleGraph.card_neighborFinset_eq_degree] at h1
      exact h1
    have hG₀EdgeEq : G₀.edgeSet.ncard = G₀.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
    let reachBall : ℕ → V₀ → Finset V₀ :=
      Nat.rec (fun u => {u}) (fun _ rec u => insert u ((G₀.neighborFinset u).biUnion rec))
    have hBallSelf : ∀ (t : ℕ) (u : V₀), u ∈ reachBall t u := by
      intro t u
      cases t <;> simp [reachBall]
    have hBallCard : ∀ (t : ℕ) (u : V₀), (reachBall t u).card ≤ 4 ^ t := by
      intro t
      induction t with
      | zero => intro u; simp [reachBall]
      | succ t ih =>
        intro u
        change (insert u ((G₀.neighborFinset u).biUnion (reachBall t))).card ≤ 4 ^ (t + 1)
        have h1 : (insert u ((G₀.neighborFinset u).biUnion (reachBall t))).card ≤
            1 + ((G₀.neighborFinset u).biUnion (reachBall t)).card := by
          have := Finset.card_insert_le u ((G₀.neighborFinset u).biUnion (reachBall t))
          omega
        have h2 : ((G₀.neighborFinset u).biUnion (reachBall t)).card ≤
            ∑ z ∈ G₀.neighborFinset u, (reachBall t z).card := Finset.card_biUnion_le
        have h3 : ∑ z ∈ G₀.neighborFinset u, (reachBall t z).card ≤
            ∑ _z ∈ G₀.neighborFinset u, 4 ^ t := Finset.sum_le_sum (fun z _ => ih z)
        have h4 : (∑ _z ∈ G₀.neighborFinset u, 4 ^ t) = G₀.degree u * 4 ^ t := by
          simp [SimpleGraph.card_neighborFinset_eq_degree]
        have h5 : G₀.degree u * 4 ^ t ≤ 3 * 4 ^ t := Nat.mul_le_mul_right (4 ^ t) (hG₀Deg u)
        have hPowPos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by omega)
        have hPowSucc : 4 ^ (t + 1) = 4 * 4 ^ t := by ring
        omega
    have hWalkMemBall : ∀ {u w : V₀} (p : G₀.Walk u w) (t : ℕ),
        p.length ≤ t → w ∈ reachBall t u := by
      intro u w p
      induction p with
      | @nil u =>
        intro t _; exact hBallSelf t u
      | @cons u z w h rest ih =>
        intro t ht
        cases t with
        | zero => simp at ht
        | succ t' =>
          simp only [SimpleGraph.Walk.length_cons, Nat.add_le_add_iff_right] at ht
          change w ∈ insert u ((G₀.neighborFinset u).biUnion (reachBall t'))
          apply Finset.mem_insert_of_mem
          rw [Finset.mem_biUnion]
          exact ⟨z, (G₀.mem_neighborFinset u z).mpr h, ih t' ht⟩
    let S : Finset V₀ := Finset.univ.filter (fun w : V₀ => G₀.degree w ≤ 2)
    have hSCard : S.card ≤ 4 ^ (g - 2) := by
      by_contra hGt
      push_neg at hGt
      have hPowGe1 : 1 ≤ 4 ^ (g - 2) := Nat.one_le_pow (g - 2) 4 (by omega)
      have hSNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u, huS⟩ := hSNonempty
      have hNotSub : ¬ S ⊆ reachBall (g - 2) u := by
        intro hSub
        have := Finset.card_le_card hSub
        have := hBallCard (g - 2) u
        omega
      obtain ⟨v, hvS, hvNotBall⟩ := Finset.not_subset.mp hNotSub
      have huDeg : G₀.degree u ≤ 2 := (Finset.mem_filter.mp huS).2
      have hvDeg : G₀.degree v ≤ 2 := (Finset.mem_filter.mp hvS).2
      have huv : u ≠ v := by
        intro hEq
        subst hEq
        exact hvNotBall (hBallSelf (g - 2) u)
      have hNotAdj : ¬ G₀.Adj u v := by
        intro hAdj
        have hWalk1 : (SimpleGraph.Walk.cons hAdj SimpleGraph.Walk.nil).length ≤ g - 2 := by
          simp; omega
        exact hvNotBall (hWalkMemBall _ (g - 2) hWalk1)
      let G₁ : SimpleGraph V₀ := {
        Adj := fun x y => G₀.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
        symm := by
          intro x y h
          rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl h.symm
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        loopless := by
          intro x h
          rcases h with h | ⟨rfl, hEq⟩ | ⟨rfl, hEq⟩
          · exact G₀.loopless x h
          · exact huv hEq
          · exact huv hEq.symm
      }
      have hG₁Edge : G₁.edgeSet = insert s(u, v) G₀.edgeSet := by
        ext e
        refine Sym2.ind (fun x y => ?_) e
        simp only [SimpleGraph.mem_edgeSet, Set.mem_insert_iff, Sym2.eq_iff, G₁]
        tauto
      have hNotMemEdge : s(u, v) ∉ G₀.edgeSet := by
        simp [hNotAdj]
      have hG₁CardGt : G₀.edgeSet.ncard < G₁.edgeSet.ncard := by
        rw [hG₁Edge, Set.ncard_insert_of_notMem hNotMemEdge G₀.edgeSet.toFinite]
        omega
      have hG₁Deg : ∀ w : V₀, (G₁.neighborSet w).ncard ≤ 3 := by
        intro w
        rw [Set.ncard_eq_toFinset_card']
        by_cases hwu : w = u
        · subst hwu
          have hSub : (G₁.neighborSet w).toFinset ⊆ insert v (G₀.neighborFinset w) := by
            intro y hy
            simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet, Finset.mem_insert,
              SimpleGraph.mem_neighborFinset, G₁] at hy ⊢
            tauto
          have h1 := Finset.card_le_card hSub
          have h2 := Finset.card_insert_le v (G₀.neighborFinset w)
          rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
          omega
        · by_cases hwv : w = v
          · subst hwv
            have hSub : (G₁.neighborSet w).toFinset ⊆ insert u (G₀.neighborFinset w) := by
              intro y hy
              simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet, Finset.mem_insert,
                SimpleGraph.mem_neighborFinset, G₁] at hy ⊢
              tauto
            have h1 := Finset.card_le_card hSub
            have h2 := Finset.card_insert_le u (G₀.neighborFinset w)
            rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
            omega
          · have hSub : (G₁.neighborSet w).toFinset ⊆ G₀.neighborFinset w := by
              intro y hy
              simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet,
                SimpleGraph.mem_neighborFinset, G₁] at hy ⊢
              tauto
            have h1 := Finset.card_le_card hSub
            rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
            exact le_trans h1 (hG₀Deg w)
      have hEdgeOr : ∀ {x y : V₀}, G₁.Adj x y → s(x, y) ≠ s(u, v) → G₀.Adj x y := by
        intro x y hAdj hNe
        rcases hAdj with h0 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h0
        · exact False.elim (hNe rfl)
        · exact False.elim (hNe Sym2.eq_swap)
      have hNoUVSub : ∀ {a b : V₀} (p : G₁.Walk a b),
          s(u, v) ∉ p.edges → ∀ e ∈ p.edges, e ∈ G₀.edgeSet := by
        intro a b p hNotIn e he
        have heG₁ : e ∈ G₁.edgeSet := p.edges_subset_edgeSet he
        rw [hG₁Edge, Set.mem_insert_iff] at heG₁
        rcases heG₁ with rfl | heG₀
        · exact False.elim (hNotIn he)
        · exact heG₀
      have hSplitTrail : ∀ {a b : V₀} (p : G₁.Walk a b),
          p.edges.Nodup → s(u, v) ∈ p.edges →
          (∃ (q₁ : G₀.Walk a u) (q₂ : G₀.Walk v b), q₁.length + q₂.length + 1 = p.length) ∨
          (∃ (q₁ : G₀.Walk a v) (q₂ : G₀.Walk u b), q₁.length + q₂.length + 1 = p.length) := by
        intro a b p
        induction p with
        | nil => intro _ hMem; simp at hMem
        | @cons a z b h rest ih =>
          intro hNodup hMem
          rw [SimpleGraph.Walk.edges_cons, List.nodup_cons] at hNodup
          rcases hNodup with ⟨hNotRest, hNodupRest⟩
          rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hMem
          by_cases hEq : s(a, z) = s(u, v)
          · have huvNotRest : s(u, v) ∉ rest.edges := hEq ▸ hNotRest
            let q₂ : G₀.Walk z b := rest.transfer G₀ (hNoUVSub rest huvNotRest)
            have hq₂Len : q₂.length = rest.length := rest.length_transfer _
            rw [Sym2.eq_iff] at hEq
            rcases hEq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inl ⟨SimpleGraph.Walk.nil, q₂, by simp [hq₂Len]⟩
            · exact Or.inr ⟨SimpleGraph.Walk.nil, q₂, by simp [hq₂Len]⟩
          · have hMemRest : s(u, v) ∈ rest.edges := hMem.resolve_left (Ne.symm hEq)
            have h₀ : G₀.Adj a z := hEdgeOr h hEq
            rcases ih hNodupRest hMemRest with ⟨q₁, q₂, hL⟩ | ⟨q₁, q₂, hL⟩
            · exact Or.inl ⟨SimpleGraph.Walk.cons h₀ q₁, q₂, by simp; omega⟩
            · exact Or.inr ⟨SimpleGraph.Walk.cons h₀ q₁, q₂, by simp; omega⟩
      have hG₁Girth : ∀ (w₀ : V₀) (c : G₁.Walk w₀ w₀), c.IsCycle → g ≤ c.length := by
        intro w₀ c hc
        by_cases hMem : s(u, v) ∈ c.edges
        · rcases hSplitTrail c hc.isCircuit.isTrail.edges_nodup hMem with
            ⟨q₁, q₂, hL⟩ | ⟨q₁, q₂, hL⟩
          · let W₀ : G₀.Walk u v := (q₂.append q₁).reverse
            have hW₀Len : W₀.length = q₂.length + q₁.length := by
              simp [W₀, SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.length_append]; omega
            by_contra hLt
            have hLe : W₀.length ≤ g - 2 := by omega
            exact hvNotBall (hWalkMemBall W₀ (g - 2) hLe)
          · let W₀ : G₀.Walk u v := q₂.append q₁
            have hW₀Len : W₀.length = q₂.length + q₁.length := by
              simp [W₀, SimpleGraph.Walk.length_append]
            by_contra hLt
            have hLe : W₀.length ≤ g - 2 := by omega
            exact hvNotBall (hWalkMemBall W₀ (g - 2) hLe)
        · let c₀ : G₀.Walk w₀ w₀ := c.transfer G₀ (hNoUVSub c hMem)
          have hc₀ : c₀.IsCycle := hc.transfer _
          have hLen : c₀.length = c.length := c.length_transfer _
          rw [← hLen]
          exact hG₀Good.2 w₀ c₀ hc₀
      have hLe := hG₀Max G₁ ⟨hG₁Deg, hG₁Girth⟩
      omega
    let Sc : Finset V₀ := Finset.univ \ S
    have hPartS : (Finset.univ : Finset V₀) = S ∪ Sc := by
      ext x; simp [Sc]
    have hDisjS : Disjoint S Sc := disjoint_sdiff_self_right
    have hScCard : S.card + Sc.card = m₀ := by
      have := Finset.card_union_of_disjoint hDisjS
      rw [← hPartS, Finset.card_univ, hCardV₀] at this
      omega
    have hDegSc : ∀ w ∈ Sc, 3 ≤ G₀.degree w := by
      intro w hw
      simp only [Sc, S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hw
      omega
    have hSumDegG₀ : 3 * Sc.card ≤ 2 * G₀.edgeFinset.card := by
      rw [← G₀.sum_degrees_eq_twice_card_edges, hPartS, Finset.sum_union hDisjS]
      have h1 : 3 * Sc.card = ∑ _w ∈ Sc, 3 := by simp [Nat.mul_comm]
      have h2 : ∑ _w ∈ Sc, 3 ≤ ∑ w ∈ Sc, G₀.degree w := Finset.sum_le_sum hDegSc
      omega
    have h48S : 48 * S.card < 3 * m₀ := by
      have h1 : 16 * S.card ≤ 16 * 4 ^ (g - 2) := Nat.mul_le_mul_left 16 hSCard
      have h2 : 16 * 4 ^ (g - 2) = 4 ^ g := by
        have hg2 : g = (g - 2) + 2 := by omega
        conv_rhs => rw [hg2, pow_add]
        ring
      have h3 : 4 ^ g < 16 ^ g := Nat.pow_lt_pow_left (by omega) (by omega)
      dsimp [m₀]
      omega
    have hDenseG₀ : 5 * m₀ < 4 * G₀.edgeFinset.card := by omega
    have hSumLtG₀ : (∑ _v : V₀, 5) < ∑ v : V₀, 2 * G₀.degree v := by
      have hL : (∑ _v : V₀, 5) = 5 * m₀ := by simp [hCardV₀, Nat.mul_comm]
      have hR : (∑ v : V₀, 2 * G₀.degree v) = 4 * G₀.edgeFinset.card := by
        rw [← Finset.mul_sum, G₀.sum_degrees_eq_twice_card_edges]
        ring
      omega
    have hFibL : (∑ c ∈ (Finset.univ : Finset G₀.ConnectedComponent),
        ∑ _v ∈ Finset.univ.filter (fun v : V₀ => G₀.connectedComponentMk v = c), 5) =
        ∑ _v : V₀, 5 :=
      Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    have hFibR : (∑ c ∈ (Finset.univ : Finset G₀.ConnectedComponent),
        ∑ v ∈ Finset.univ.filter (fun v : V₀ => G₀.connectedComponentMk v = c), 2 * G₀.degree v) =
        ∑ v : V₀, 2 * G₀.degree v :=
      Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    rw [← hFibL, ← hFibR] at hSumLtG₀
    obtain ⟨C, _, hCLt⟩ := Finset.exists_lt_of_sum_lt hSumLtG₀
    have hMemC : ∀ x : V₀, x ∈ C ↔ G₀.connectedComponentMk x = C :=
      fun x => SimpleGraph.ConnectedComponent.mem_supp_iff C x
    let m : ℕ := Fintype.card C
    let eFin : C ≃ Fin m := Fintype.equivFin C
    let H : SimpleGraph (Fin m) := {
      Adj := fun x y => C.toSimpleGraph.Adj (eFin.symm x) (eFin.symm y)
      symm := fun _ _ h => C.toSimpleGraph.symm h
      loopless := fun x h => C.toSimpleGraph.loopless (eFin.symm x) h
    }
    let embHG₀ : H ↪g G₀ := {
      toEmbedding := ⟨fun x => (eFin.symm x).1, fun x y h => eFin.symm.injective (Subtype.ext h)⟩
      map_rel_iff' := Iff.rfl
    }
    have hHDegEq : ∀ x : Fin m, H.degree x = G₀.degree (eFin.symm x).1 := by
      intro x
      simp only [← SimpleGraph.card_neighborFinset_eq_degree]
      refine Finset.card_bij (fun y _ => (eFin.symm y).1) ?_ ?_ ?_
      · intro y hy
        simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
        exact hy
      · intro y₁ _ y₂ _ h
        exact eFin.symm.injective (Subtype.ext h)
      · intro w hw
        simp only [SimpleGraph.mem_neighborFinset] at hw
        have hwC : w ∈ C := by
          rw [hMemC, ← (hMemC (eFin.symm x).1).mp (eFin.symm x).2]
          exact SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hw.symm)
        refine ⟨eFin ⟨w, hwC⟩, ?_, by simp⟩
        rw [H.mem_neighborFinset]
        change G₀.Adj (eFin.symm x).1 (eFin.symm (eFin ⟨w, hwC⟩)).1
        simp [hw]
    have hFibCard : (Finset.univ.filter (fun v : V₀ => G₀.connectedComponentMk v = C)).card = m := by
      dsimp [m]
      rw [← Finset.card_univ]
      refine Finset.card_bij (fun v hv => ⟨v, (hMemC v).mpr (Finset.mem_filter.mp hv).2⟩) ?_ ?_ ?_
      · intros; simp
      · intro v₁ _ v₂ _ h; exact congrArg Subtype.val h
      · intro z _; exact ⟨z.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hMemC z.1).mp z.2⟩, rfl⟩
    have hFibSum : (∑ v ∈ Finset.univ.filter (fun v : V₀ => G₀.connectedComponentMk v = C),
        2 * G₀.degree v) = ∑ x : Fin m, 2 * H.degree x := by
      refine Finset.sum_bij
        (fun v hv => eFin ⟨v, (hMemC v).mpr (Finset.mem_filter.mp hv).2⟩) ?_ ?_ ?_ ?_
      · intros; simp
      · intro v₁ hv₁ v₂ hv₂ h
        have := eFin.injective h
        exact congrArg Subtype.val this
      · intro x _
        refine ⟨(eFin.symm x).1,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hMemC _).mp (eFin.symm x).2⟩, by simp⟩
      · intro v hv
        rw [hHDegEq, Equiv.symm_apply_apply]
    have h5mLt : 5 * m < 4 * H.edgeFinset.card := by
      have hL : (∑ _v ∈ Finset.univ.filter (fun v : V₀ => G₀.connectedComponentMk v = C), 5) =
          5 * m := by simp [hFibCard, Nat.mul_comm]
      have hR : (∑ x : Fin m, 2 * H.degree x) = 4 * H.edgeFinset.card := by
        rw [← Finset.mul_sum, H.sum_degrees_eq_twice_card_edges]
        ring
      omega
    have hmPos : 0 < m := by
      rw [← hFibCard]
      apply Finset.card_pos.mpr
      apply Finset.nonempty_of_ne_empty
      intro hEmpty
      rw [hEmpty] at hCLt
      simp at hCLt
    have hmLe16 : m ≤ 16 ^ g := by
      dsimp [m]
      exact le_trans (Fintype.card_subtype_le _) (by rw [hCardV₀])
    have hHConn : H.Connected := by
      haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hmPos
      refine SimpleGraph.Connected.mk ?_
      intro x y
      have hReachC : C.toSimpleGraph.Reachable (eFin.symm x) (eFin.symm y) :=
        C.connected_toSimpleGraph (eFin.symm x) (eFin.symm y)
      rcases hReachC with ⟨w⟩
      let homCH : C.toSimpleGraph →g H := {
        toFun := eFin
        map_rel' := by
          intro a b hab
          change C.toSimpleGraph.Adj (eFin.symm (eFin a)) (eFin.symm (eFin b))
          simpa using hab
      }
      have hwMap := (w.map homCH).reachable
      simpa [homCH] using hwMap
    have hHDegNcard : ∀ v : Fin m, (H.neighborSet v).ncard ≤ 3 := by
      intro v
      rw [Set.ncard_eq_toFinset_card']
      have hEq : (H.neighborSet v).toFinset = H.neighborFinset v := by ext y; simp
      rw [hEq, SimpleGraph.card_neighborFinset_eq_degree, hHDegEq v]
      exact hG₀Deg (eFin.symm v).1
    have hHEdgeEq : H.edgeSet.ncard = H.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
    have h2ELe3m : 2 * H.edgeFinset.card ≤ 3 * m := by
      rw [← H.sum_degrees_eq_twice_card_edges]
      calc ∑ x : Fin m, H.degree x
          ≤ ∑ _x : Fin m, 3 := Finset.sum_le_sum (fun x _ => by rw [hHDegEq]; exact hG₀Deg _)
        _ = 3 * m := by simp [Nat.mul_comm]
    have hHGirth : ∀ (u : Fin m) (c : H.Walk u u), c.IsCycle → g ≤ c.length := by
      intro u c hc
      have hcMap : (c.map embHG₀.toHom).IsCycle := hc.map embHG₀.injective
      have hLen : (c.map embHG₀.toHom).length = c.length := c.length_map _
      rw [← hLen]
      exact hG₀Good.2 _ _ hcMap
    have hgm : g ≤ m := by
      have hNotAcycH : ¬ H.IsAcyclic := by
        intro hAcyc
        have hTreeH : H.IsTree := ⟨hHConn, hAcyc⟩
        have hCardE := hTreeH.card_edgeFinset
        simp only [Fintype.card_fin] at hCardE
        omega
      unfold SimpleGraph.IsAcyclic at hNotAcycH
      push_neg at hNotAcycH
      rcases hNotAcycH with ⟨u₀, c₀, hc₀⟩
      have h1 : g ≤ c₀.length := hHGirth u₀ c₀ hc₀
      have hNodup : c₀.support.tail.Nodup := hc₀.support_nodup
      have hTailLen : c₀.support.tail.length = c₀.length := by
        have := c₀.length_support
        simp [this]
      have hLeCard : c₀.support.tail.length ≤ Fintype.card (Fin m) :=
        hNodup.length_le_card
      simp only [Fintype.card_fin] at hLeCard
      omega
    refine ⟨m, H, hgm, hmLe16, hHConn, hHDegNcard, ?_, ?_, hHGirth⟩
    · omega
    · omega
  have s2 : ∀ (m g k : ℕ), 3 ≤ g → g ≤ m → 1 ≤ k → ∀ H : SimpleGraph (Fin m),
      H.Connected → (∀ v : Fin m, (H.neighborSet v).ncard ≤ 3) →
      (∀ (u : Fin m) (c : H.Walk u u), c.IsCycle → g ≤ c.length) →
      ∃ (V' : Type) (hF : Fintype V') (hD : DecidableEq V') (G' : SimpleGraph V'),
        letI := hF; letI := hD
        G'.Connected ∧
        Fintype.card V' = m + k * H.edgeSet.ncard ∧
        G'.edgeSet.ncard = (k + 1) * H.edgeSet.ncard ∧
        (∀ v : V', (G'.neighborSet v).ncard ≤ 3) ∧
        (∀ (w₀ : V') (W : G'.Walk w₀ w₀), W.length < (k + 1) * g →
          ∀ a : Sym2 V', (W.edges.count a : ZMod 2) = 0) := by
    intro m g k hg3 hgm hk1 H hHConn hHDeg hHGirth
    classical
    have hHDegF : ∀ u : Fin m, H.degree u ≤ 3 := by
      intro u
      have h1 := hHDeg u
      rw [Set.ncard_eq_toFinset_card'] at h1
      have hEq : (H.neighborSet u).toFinset = H.neighborFinset u := by ext y; simp
      rw [hEq, SimpleGraph.card_neighborFinset_eq_degree] at h1
      exact h1
    have hHEdgeCard : H.edgeSet.ncard = H.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
    let UpperEdge := { p : Fin m × Fin m // p.1 < p.2 ∧ H.Adj p.1 p.2 }
    have hUpperCard : Fintype.card UpperEdge = H.edgeSet.ncard := by
      rw [hHEdgeCard, ← Finset.card_univ]
      refine Finset.card_bij (fun e _ => s(e.1.1, e.1.2)) ?_ ?_ ?_
      · intro e _
        exact H.mem_edgeFinset.mpr e.2.2
      · intro e₁ _ e₂ _ hEq
        rw [Sym2.eq_iff] at hEq
        rcases hEq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Subtype.ext (Prod.ext h1 h2)
        · exfalso
          have hlt1 := e₁.2.1
          have hlt2 := e₂.2.1
          omega
      · intro a ha
        refine Sym2.ind (fun u w ha' => ?_) a ha
        have hAdj : H.Adj u w := H.mem_edgeFinset.mp ha'
        have hNe : u ≠ w := H.ne_of_adj hAdj
        rcases lt_or_gt_of_ne hNe with hlt | hgt
        · exact ⟨⟨(u, w), hlt, hAdj⟩, Finset.mem_univ _, rfl⟩
        · exact ⟨⟨(w, u), hgt, hAdj.symm⟩, Finset.mem_univ _, Sym2.eq_swap⟩
    let V' : Type := Fin m ⊕ (UpperEdge × Fin k)
    have hV'Card : Fintype.card V' = m + k * H.edgeSet.ncard := by
      simp only [V', Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hUpperCard]
      ring
    let chainPt (e : UpperEdge) (t : Fin (k + 2)) : Fin m ⊕ (UpperEdge × Fin k) :=
      if t.1 = 0 then Sum.inl e.1.1
      else if t.1 = k + 1 then Sum.inl e.1.2
      else Sum.inr (e, ⟨min (t.1 - 1) (k - 1), by omega⟩)
    have hChain0 : ∀ e : UpperEdge, chainPt e ⟨0, by omega⟩ = Sum.inl e.1.1 := by
      intro e; simp [chainPt]
    have hChainEnd : ∀ e : UpperEdge, chainPt e ⟨k + 1, by omega⟩ = Sum.inl e.1.2 := by
      intro e; simp [chainPt]
    have hChainMid : ∀ (e : UpperEdge) (i : Fin k),
        chainPt e ⟨i.1 + 1, by omega⟩ = Sum.inr (e, i) := by
      intro e i
      have hi : i.1 < k := i.2
      dsimp [chainPt]
      split_ifs <;> try omega
      congr 2
      ext
      dsimp
      omega
    have hChainInrIff : ∀ (e' e : UpperEdge) (t : Fin (k + 2)) (i : Fin k),
        chainPt e' t = Sum.inr (e, i) ↔ e' = e ∧ t.1 = i.1 + 1 := by
      intro e' e t i
      have ht : t.1 < k + 2 := t.2
      have hi : i.1 < k := i.2
      dsimp [chainPt]
      split_ifs with h0 hkp1
      · constructor
        · intro h; cases h
        · rintro ⟨_, h⟩; omega
      · constructor
        · intro h; cases h
        · rintro ⟨_, h⟩; omega
      · constructor
        · intro h
          injection h with h'
          injection h' with he hfin
          have hval : min (t.1 - 1) (k - 1) = i.1 := congrArg Fin.val hfin
          exact ⟨he, by omega⟩
        · rintro ⟨rfl, hEq⟩
          congr 2
          ext
          dsimp
          omega
    have hChainInlIff : ∀ (e : UpperEdge) (t : Fin (k + 2)) (u : Fin m),
        chainPt e t = Sum.inl u ↔ (t.1 = 0 ∧ e.1.1 = u) ∨ (t.1 = k + 1 ∧ e.1.2 = u) := by
      intro e t u
      dsimp [chainPt]
      split_ifs with h0 hkp1
      · constructor
        · intro h; injection h with hu; exact Or.inl ⟨h0, hu⟩
        · rintro (⟨_, hu⟩ | ⟨h1, _⟩)
          · exact congrArg Sum.inl hu
          · omega
      · constructor
        · intro h; injection h with hu; exact Or.inr ⟨hkp1, hu⟩
        · rintro (⟨h1, _⟩ | ⟨_, hu⟩)
          · omega
          · exact congrArg Sum.inl hu
      · constructor
        · intro h; cases h
        · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> omega
    have hChainInj : ∀ e : UpperEdge, Function.Injective (chainPt e) := by
      intro e t₁ t₂ hEq
      have ht1Lt : t₁.1 < k + 2 := t₁.2
      ext
      by_cases ht10 : t₁.1 = 0
      · have h1 : chainPt e t₁ = Sum.inl e.1.1 := by
          have : t₁ = ⟨0, by omega⟩ := Fin.ext ht10
          rw [this, hChain0]
        rw [h1] at hEq
        rcases (hChainInlIff e t₂ e.1.1).mp hEq.symm with ⟨ht20, _⟩ | ⟨_, hBad⟩
        · omega
        · have := e.2.1; omega
      · by_cases ht1k : t₁.1 = k + 1
        · have h1 : chainPt e t₁ = Sum.inl e.1.2 := by
            have : t₁ = ⟨k + 1, by omega⟩ := Fin.ext ht1k
            rw [this, hChainEnd]
          rw [h1] at hEq
          rcases (hChainInlIff e t₂ e.1.2).mp hEq.symm with ⟨_, hBad⟩ | ⟨ht2k, _⟩
          · have := e.2.1; omega
          · omega
        · let i : Fin k := ⟨t₁.1 - 1, by omega⟩
          have ht1Eq : t₁ = ⟨i.1 + 1, by omega⟩ := by
            ext; dsimp [i]; omega
          have h1 : chainPt e t₁ = Sum.inr (e, i) := by
            rw [ht1Eq, hChainMid]
          rw [h1] at hEq
          have ht2 := ((hChainInrIff e e t₂ i).mp hEq.symm).2
          dsimp [i] at ht2
          omega
    let Φ (p : UpperEdge × Fin (k + 1)) : Sym2 V' :=
      s(chainPt p.1 p.2.castSucc, chainPt p.1 p.2.succ)
    have hΦNe : ∀ p : UpperEdge × Fin (k + 1),
        chainPt p.1 p.2.castSucc ≠ chainPt p.1 p.2.succ := by
      intro p hEq
      have := congrArg Fin.val (hChainInj p.1 hEq)
      simp at this
    have hΦInrMem : ∀ (p : UpperEdge × Fin (k + 1)) (e : UpperEdge) (i : Fin k),
        Sum.inr (e, i) ∈ Φ p ↔ p.1 = e ∧ (p.2.1 = i.1 + 1 ∨ p.2.1 = i.1) := by
      intro p e i
      dsimp [Φ]
      rw [Sym2.mem_iff, eq_comm, (eq_comm (a := Sum.inr (e, i)) (b := chainPt p.1 p.2.succ)),
        hChainInrIff, hChainInrIff]
      simp only [Fin.val_castSucc, Fin.val_succ]
      constructor
      · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
        · exact ⟨rfl, Or.inl h⟩
        · exact ⟨rfl, Or.inr (by omega)⟩
      · rintro ⟨rfl, h | h⟩
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨rfl, by omega⟩
    have hΦHasInr : ∀ p : UpperEdge × Fin (k + 1), ∃ i : Fin k, Sum.inr (p.1, i) ∈ Φ p := by
      intro p
      by_cases hj0 : p.2.1 = 0
      · refine ⟨⟨0, by omega⟩, ?_⟩
        rw [hΦInrMem]
        exact ⟨rfl, Or.inr hj0⟩
      · have hp2 : p.2.1 < k + 1 := p.2.2
        refine ⟨⟨p.2.1 - 1, by omega⟩, ?_⟩
        rw [hΦInrMem]
        dsimp
        exact ⟨rfl, Or.inl (by omega)⟩
    have hΦInlMem : ∀ (p : UpperEdge × Fin (k + 1)) (u : Fin m),
        Sum.inl u ∈ Φ p ↔ (p.2.1 = 0 ∧ p.1.1.1 = u) ∨ (p.2.1 = k ∧ p.1.1.2 = u) := by
      intro p u
      dsimp [Φ]
      rw [Sym2.mem_iff, eq_comm, (eq_comm (a := Sum.inl u) (b := chainPt p.1 p.2.succ)),
        hChainInlIff, hChainInlIff]
      simp only [Fin.val_castSucc, Fin.val_succ]
      have hjLt : p.2.1 < k + 1 := p.2.2
      constructor
      · rintro ((⟨h1, h2⟩ | ⟨h1, _⟩) | (⟨h1, _⟩ | ⟨h1, h2⟩))
        · exact Or.inl ⟨h1, h2⟩
        · omega
        · omega
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl (Or.inl ⟨h1, h2⟩)
        · exact Or.inr (Or.inr ⟨by omega, h2⟩)
    have hΦInj : Function.Injective Φ := by
      intro p q hEq
      obtain ⟨i, hi⟩ := hΦHasInr p
      have hiQ : Sum.inr (p.1, i) ∈ Φ q := hEq ▸ hi
      have hq1 : q.1 = p.1 := ((hΦInrMem q p.1 i).mp hiQ).1
      rcases p with ⟨e, j₁⟩
      rcases q with ⟨e', j₂⟩
      dsimp at hq1
      subst e'
      dsimp [Φ] at hEq
      rw [Sym2.eq_iff] at hEq
      rcases hEq with ⟨h1, _⟩ | ⟨h1, h2⟩
      · have hj := congrArg Fin.val (hChainInj e h1)
        simp only [Fin.val_castSucc] at hj
        exact Prod.ext rfl (Fin.ext hj)
      · have hj1 := congrArg Fin.val (hChainInj e h1)
        have hj2 := congrArg Fin.val (hChainInj e h2)
        simp only [Fin.val_castSucc, Fin.val_succ] at hj1 hj2
        omega
    let G' : SimpleGraph V' := {
      Adj := fun x y => x ≠ y ∧ s(x, y) ∈ Set.range Φ
      symm := by
        intro x y ⟨hne, hp⟩
        exact ⟨hne.symm, Sym2.eq_swap ▸ hp⟩
      loopless := fun _ h => h.1 rfl
    }
    have hG'EdgeSet : G'.edgeSet = Set.range Φ := by
      ext a
      refine Sym2.ind (fun x y => ?_) a
      simp only [SimpleGraph.mem_edgeSet, G', Set.mem_range]
      constructor
      · exact And.right
      · rintro ⟨p, hp⟩
        refine ⟨?_, p, hp⟩
        rintro rfl
        have hDiag := Sym2.eq_iff.mp hp.symm
        rcases hDiag with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hΦNe p (h1.symm.trans h2)
        · exact hΦNe p (h2.symm.trans h1)
    have hG'EdgeCard : G'.edgeSet.ncard = (k + 1) * H.edgeSet.ncard := by
      rw [hG'EdgeSet, Set.ncard_eq_toFinset_card']
      have hImg : (Set.range Φ).toFinset = Finset.univ.image Φ := by
        ext a; simp
      rw [hImg, Finset.card_image_of_injective _ hΦInj, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, hUpperCard]
      ring
    have hStepAdj : ∀ (e : UpperEdge) (j : Fin (k + 1)),
        G'.Adj (chainPt e j.castSucc) (chainPt e j.succ) := by
      intro e j
      exact ⟨hΦNe (e, j), ⟨(e, j), rfl⟩⟩
    have hChainReach : ∀ (e : UpperEdge) (t : ℕ) (ht : t ≤ k + 1),
        G'.Reachable (chainPt e ⟨0, by omega⟩) (chainPt e ⟨t, by omega⟩) := by
      intro e t
      induction t with
      | zero => intro _; exact SimpleGraph.Reachable.refl _
      | succ t ih =>
        intro ht
        exact (ih (by omega)).trans (SimpleGraph.Adj.reachable (hStepAdj e ⟨t, by omega⟩))
    have hHAdjReach : ∀ {u w : Fin m}, H.Adj u w → G'.Reachable (Sum.inl u) (Sum.inl w) := by
      intro u w hAdj
      rcases lt_or_gt_of_ne (H.ne_of_adj hAdj) with hlt | hgt
      · let e : UpperEdge := ⟨(u, w), hlt, hAdj⟩
        have hR := hChainReach e (k + 1) (le_refl _)
        rw [hChain0 e, hChainEnd e] at hR
        exact hR
      · let e : UpperEdge := ⟨(w, u), hgt, hAdj.symm⟩
        have hR := hChainReach e (k + 1) (le_refl _)
        rw [hChain0 e, hChainEnd e] at hR
        exact hR.symm
    have hHWalkReach : ∀ {u w : Fin m} (p : H.Walk u w), G'.Reachable (Sum.inl u) (Sum.inl w) := by
      intro u w p
      induction p with
      | nil => exact SimpleGraph.Reachable.refl _
      | cons h _ ih => exact (hHAdjReach h).trans ih
    have hVertReachInl : ∀ v : V', ∃ u : Fin m, G'.Reachable (Sum.inl u) v := by
      rintro (u | ⟨e, i⟩)
      · exact ⟨u, SimpleGraph.Reachable.refl _⟩
      · refine ⟨e.1.1, ?_⟩
        have hR := hChainReach e (i.1 + 1) (by omega)
        rw [hChain0 e, hChainMid e i] at hR
        exact hR
    have hG'Conn : G'.Connected := by
      have hmPos : 0 < m := by omega
      haveI : Nonempty V' := ⟨Sum.inl ⟨0, hmPos⟩⟩
      refine SimpleGraph.Connected.mk ?_
      intro x y
      obtain ⟨ux, hux⟩ := hVertReachInl x
      obtain ⟨uy, huy⟩ := hVertReachInl y
      obtain ⟨wH⟩ := hHConn ux uy
      exact hux.symm.trans ((hHWalkReach wH).trans huy)
    have hDegLeInc : ∀ v : V',
        (G'.neighborSet v).ncard ≤ (Finset.univ.filter (fun p => v ∈ Φ p)).card := by
      intro v
      rw [Set.ncard_eq_toFinset_card']
      let otherPt (p : UpperEdge × Fin (k + 1)) : V' :=
        if chainPt p.1 p.2.castSucc = v then chainPt p.1 p.2.succ else chainPt p.1 p.2.castSucc
      have hSub : (G'.neighborSet v).toFinset ⊆
          (Finset.univ.filter (fun p => v ∈ Φ p)).image otherPt := by
        intro w hw
        rw [Set.mem_toFinset, SimpleGraph.mem_neighborSet] at hw
        rcases hw with ⟨hvw, p, hp⟩
        rw [Finset.mem_image]
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [hp]; simp
        · dsimp [otherPt]
          have hp' := Sym2.eq_iff.mp hp
          rcases hp' with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [if_pos h1, h2]
          · have hne : chainPt p.1 p.2.castSucc ≠ v := by
              rw [h1]; exact hvw.symm
            rw [if_neg hne, h1]
      exact le_trans (Finset.card_le_card hSub) Finset.card_image_le
    have hG'Deg : ∀ v : V', (G'.neighborSet v).ncard ≤ 3 := by
      rintro (u | ⟨e, i⟩)
      · refine le_trans (hDegLeInc (Sum.inl u)) ?_
        have hInjH : (Finset.univ.filter (fun p => Sum.inl u ∈ Φ p)).card ≤
            (H.neighborFinset u).card := by
          refine Finset.card_le_card_of_injOn
            (fun p => if p.1.1.1 = u then p.1.1.2 else p.1.1.1) ?_ ?_
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
              hΦInlMem] at hp
            rw [Finset.mem_coe, H.mem_neighborFinset]
            dsimp only
            rcases hp with ⟨_, h1⟩ | ⟨_, h2⟩
            · rw [if_pos h1]; rw [← h1]; exact p.1.2.2
            · have hne : p.1.1.1 ≠ u := by have := p.1.2.1; omega
              rw [if_neg hne]; rw [← h2]; exact p.1.2.2.symm
          · intro p₁ hp₁ p₂ hp₂ hOut
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
              hΦInlMem] at hp₁ hp₂
            dsimp only at hOut
            have hSym : s(p₁.1.1.1, p₁.1.1.2) = s(p₂.1.1.1, p₂.1.1.2) := by
              rcases hp₁ with ⟨_, h1⟩ | ⟨_, h1⟩ <;> rcases hp₂ with ⟨_, h2⟩ | ⟨_, h2⟩
              · rw [if_pos h1, if_pos h2] at hOut
                rw [h1, h2, hOut]
              · have hne2 : p₂.1.1.1 ≠ u := by have := p₂.1.2.1; omega
                rw [if_pos h1, if_neg hne2] at hOut
                rw [h1, hOut, h2, Sym2.eq_swap]
              · have hne1 : p₁.1.1.1 ≠ u := by have := p₁.1.2.1; omega
                rw [if_neg hne1, if_pos h2] at hOut
                rw [h1, hOut, h2, Sym2.eq_swap]
              · have hne1 : p₁.1.1.1 ≠ u := by have := p₁.1.2.1; omega
                have hne2 : p₂.1.1.1 ≠ u := by have := p₂.1.2.1; omega
                rw [if_neg hne1, if_neg hne2] at hOut
                rw [h1, h2, hOut]
            have heEq : p₁.1 = p₂.1 := by
              rw [Sym2.eq_iff] at hSym
              rcases hSym with ⟨ha, hb⟩ | ⟨ha, hb⟩
              · exact Subtype.ext (Prod.ext ha hb)
              · have := p₁.1.2.1; have := p₂.1.2.1; omega
            have hjEq : p₁.2 = p₂.2 := by
              ext
              rcases hp₁ with ⟨hj1, h1⟩ | ⟨hj1, h1⟩ <;> rcases hp₂ with ⟨hj2, h2⟩ | ⟨hj2, h2⟩
              · omega
              · rw [heEq] at h1; have := p₂.1.2.1; omega
              · rw [heEq] at h1; have := p₂.1.2.1; omega
              · omega
            exact Prod.ext heEq hjEq
        rw [SimpleGraph.card_neighborFinset_eq_degree] at hInjH
        exact le_trans hInjH (hHDegF u)
      · refine le_trans (hDegLeInc (Sum.inr (e, i))) ?_
        let pA : UpperEdge × Fin (k + 1) := (e, ⟨i.1, by omega⟩)
        let pB : UpperEdge × Fin (k + 1) := (e, ⟨i.1 + 1, by omega⟩)
        have hSub2 : Finset.univ.filter (fun p => Sum.inr (e, i) ∈ Φ p) ⊆ {pA, pB} := by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hΦInrMem] at hp
          rw [Finset.mem_insert, Finset.mem_singleton]
          rcases hp with ⟨hp1, hjp1 | hj0⟩
          · right; exact Prod.ext hp1 (Fin.ext hjp1)
          · left; exact Prod.ext hp1 (Fin.ext hj0)
        have hCardLe := Finset.card_le_card hSub2
        have hCard2 := Finset.card_insert_le pA {pB}
        simp at hCard2
        omega
    have hZ2_self : ∀ b : ZMod 2, b + b = 0 := by decide
    have hZ2_eq_of_add_zero : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
    have hZ2_one_of_ne_zero : ∀ b : ZMod 2, b ≠ 0 → b = 1 := by decide
    have hZ2_zero_of_ne_one : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
    have hWalkInc : ∀ {x y : V'} (W : G'.Walk x y) (v : V'),
        (∑ a : Sym2 V', if v ∈ a then (W.edges.count a : ZMod 2) else 0) =
          (if v = x then 1 else 0) + (if v = y then 1 else 0) := by
      intro x y W
      induction W with
      | @nil x =>
        intro v
        simp [hZ2_self]
      | @cons x z y h W' ih =>
        intro v
        have hCountCons : ∀ a : Sym2 V',
            ((SimpleGraph.Walk.cons h W').edges.count a : ZMod 2) =
              (if a = s(x, z) then 1 else 0) + (W'.edges.count a : ZMod 2) := by
          intro a
          rw [SimpleGraph.Walk.edges_cons, List.count_cons, Nat.cast_add]
          by_cases ha : a = s(x, z)
          · subst ha; simp [add_comm]
          · have hbe : (s(x, z) == a) = false := beq_false_of_ne (Ne.symm ha)
            simp [ha, hbe]
        have hSplit : (∑ a : Sym2 V',
            if v ∈ a then ((SimpleGraph.Walk.cons h W').edges.count a : ZMod 2) else 0) =
            (∑ a : Sym2 V', if a = s(x, z) then (if v ∈ a then (1 : ZMod 2) else 0) else 0) +
            (∑ a : Sym2 V', if v ∈ a then (W'.edges.count a : ZMod 2) else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [hCountCons a]
          split_ifs <;> simp
        have hSingle : (∑ a : Sym2 V',
            if a = s(x, z) then (if v ∈ a then (1 : ZMod 2) else 0) else 0) =
            if v = x ∨ v = z then 1 else 0 := by
          rw [Finset.sum_eq_single s(x, z)]
          · rw [if_pos rfl]
            by_cases hv : v = x ∨ v = z <;> simp [Sym2.mem_iff, hv]
          · intro a _ hne; exact if_neg hne
          · intro hAbs; exact False.elim (hAbs (Finset.mem_univ _))
        rw [hSplit, hSingle, ih v]
        have hxz : x ≠ z := G'.ne_of_adj h
        have hEdgeTerm : (if v = x ∨ v = z then (1 : ZMod 2) else 0) =
            (if v = x then 1 else 0) + (if v = z then 1 else 0) := by
          by_cases hvx : v = x <;> by_cases hvz : v = z
          · exact False.elim (hxz (hvx.symm.trans hvz))
          · rw [if_pos (Or.inl hvx), if_pos hvx, if_neg hvz, add_zero]
          · rw [if_pos (Or.inr hvz), if_neg hvx, if_pos hvz, zero_add]
          · rw [if_neg (by tauto), if_neg hvx, if_neg hvz, add_zero]
        rw [hEdgeTerm, add_assoc, ← add_assoc (if v = z then (1 : ZMod 2) else 0),
          hZ2_self, zero_add]
    have hG'Short : ∀ (w₀ : V') (W : G'.Walk w₀ w₀), W.length < (k + 1) * g →
        ∀ a : Sym2 V', (W.edges.count a : ZMod 2) = 0 := by
      intro w₀ W hWLen a₀
      by_contra hNeZero
      let χ (a : Sym2 V') : ZMod 2 := (W.edges.count a : ZMod 2)
      have hχZeroOut : ∀ a : Sym2 V', a ∉ Set.range Φ → χ a = 0 := by
        intro a haOut
        have hNotEdges : a ∉ W.edges := by
          intro haMem
          exact haOut (hG'EdgeSet ▸ W.edges_subset_edgeSet haMem)
        simp [χ, List.count_eq_zero_of_not_mem hNotEdges]
      have hIncΦ : ∀ v : V',
          (∑ p : UpperEdge × Fin (k + 1), if v ∈ Φ p then χ (Φ p) else 0) = 0 := by
        intro v
        have hClosed := hWalkInc W v
        rw [hZ2_self] at hClosed
        have hImg : (∑ p : UpperEdge × Fin (k + 1), if v ∈ Φ p then χ (Φ p) else 0) =
            ∑ a ∈ Finset.univ.image Φ, if v ∈ a then χ a else 0 := by
          rw [Finset.sum_image (fun _ _ _ _ h => hΦInj h)]
        rw [hImg]
        refine Eq.trans ?_ hClosed
        dsimp only [χ]
        refine Finset.sum_subset (Finset.subset_univ _) (fun a _ haNot => ?_)
        have haOut : a ∉ Set.range Φ := by
          rintro ⟨p, rfl⟩
          exact haNot (Finset.mem_image_of_mem Φ (Finset.mem_univ p))
        have h0 : χ a = 0 := hχZeroOut a haOut
        dsimp only [χ] at h0
        rw [h0]
        simp
      have hChainStep : ∀ (e : UpperEdge) (i : Fin k),
          χ (Φ (e, ⟨i.1 + 1, by omega⟩)) = χ (Φ (e, ⟨i.1, by omega⟩)) := by
        intro e i
        have hAt := hIncΦ (Sum.inr (e, i))
        let pA : UpperEdge × Fin (k + 1) := (e, ⟨i.1, by omega⟩)
        let pB : UpperEdge × Fin (k + 1) := (e, ⟨i.1 + 1, by omega⟩)
        have hpANe : pA ≠ pB := by
          intro hEq
          have := congrArg (fun q : UpperEdge × Fin (k + 1) => q.2.1) hEq
          dsimp [pA, pB] at this
          omega
        have hSubEq : (∑ p : UpperEdge × Fin (k + 1),
            if Sum.inr (e, i) ∈ Φ p then χ (Φ p) else 0) = χ (Φ pA) + χ (Φ pB) := by
          have hOnly : (∑ p : UpperEdge × Fin (k + 1),
              if Sum.inr (e, i) ∈ Φ p then χ (Φ p) else 0) =
              ∑ p ∈ ({pA, pB} : Finset (UpperEdge × Fin (k + 1))),
                if Sum.inr (e, i) ∈ Φ p then χ (Φ p) else 0 := by
            symm
            refine Finset.sum_subset (Finset.subset_univ _) (fun p _ hpNot => ?_)
            rw [if_neg]
            intro hMem
            rw [hΦInrMem] at hMem
            apply hpNot
            rw [Finset.mem_insert, Finset.mem_singleton]
            rcases hMem with ⟨hp1, h1 | h0⟩
            · right; exact Prod.ext hp1 (Fin.ext h1)
            · left; exact Prod.ext hp1 (Fin.ext h0)
          rw [hOnly, Finset.sum_pair hpANe]
          have hMemA : Sum.inr (e, i) ∈ Φ pA := by rw [hΦInrMem]; exact ⟨rfl, Or.inr rfl⟩
          have hMemB : Sum.inr (e, i) ∈ Φ pB := by rw [hΦInrMem]; exact ⟨rfl, Or.inl rfl⟩
          rw [if_pos hMemA, if_pos hMemB]
        rw [hSubEq] at hAt
        exact hZ2_eq_of_add_zero _ _ hAt
      let ψ (e : UpperEdge) : ZMod 2 := χ (Φ (e, ⟨0, by omega⟩))
      have hChainConst : ∀ (e : UpperEdge) (j : Fin (k + 1)), χ (Φ (e, j)) = ψ e := by
        intro e ⟨t, ht⟩
        induction t with
        | zero => rfl
        | succ t ih =>
          have h1 := hChainStep e ⟨t, by omega⟩
          dsimp at h1
          rw [h1, ih (by omega)]
      have ha₀Range : a₀ ∈ Set.range Φ := by
        by_contra hOut
        exact hNeZero (hχZeroOut a₀ hOut)
      obtain ⟨⟨e₀, j₀⟩, rfl⟩ := ha₀Range
      have hψe₀ : ψ e₀ = 1 := by
        apply hZ2_one_of_ne_zero
        rw [← hChainConst e₀ j₀]
        exact hNeZero
      have hOrigInc : ∀ u : Fin m,
          (∑ e : UpperEdge, if e.1.1 = u ∨ e.1.2 = u then ψ e else 0) = 0 := by
        intro u
        have hAt := hIncΦ (Sum.inl u)
        rw [Fintype.sum_prod_type] at hAt
        refine Eq.trans ?_ hAt
        refine Finset.sum_congr rfl (fun e _ => ?_)
        simp_rw [hChainConst e]
        by_cases h1 : e.1.1 = u
        · have h2 : e.1.2 ≠ u := by have := e.2.1; omega
          rw [if_pos (Or.inl h1)]
          symm
          rw [Finset.sum_eq_single ⟨0, by omega⟩]
          · have hMem0 : Sum.inl u ∈ Φ (e, ⟨0, by omega⟩) :=
              (hΦInlMem (e, ⟨0, by omega⟩) u).mpr (Or.inl ⟨rfl, h1⟩)
            exact if_pos hMem0
          · intro j _ hjNe
            refine if_neg (fun hMem => ?_)
            rcases (hΦInlMem (e, j) u).mp hMem with ⟨hj0, _⟩ | ⟨_, he2⟩
            · exact hjNe (Fin.ext hj0)
            · exact h2 he2
          · intro hAbs; exact False.elim (hAbs (Finset.mem_univ _))
        · by_cases h2 : e.1.2 = u
          · rw [if_pos (Or.inr h2)]
            symm
            rw [Finset.sum_eq_single ⟨k, by omega⟩]
            · have hMemK : Sum.inl u ∈ Φ (e, ⟨k, by omega⟩) :=
                (hΦInlMem (e, ⟨k, by omega⟩) u).mpr (Or.inr ⟨rfl, h2⟩)
              exact if_pos hMemK
            · intro j _ hjNe
              refine if_neg (fun hMem => ?_)
              rcases (hΦInlMem (e, j) u).mp hMem with ⟨_, he1⟩ | ⟨hjk, _⟩
              · exact h1 he1
              · exact hjNe (Fin.ext hjk)
            · intro hAbs; exact False.elim (hAbs (Finset.mem_univ _))
          · rw [if_neg (by tauto)]
            symm
            refine Finset.sum_eq_zero (fun j _ => if_neg (fun hMem => ?_))
            rcases (hΦInlMem (e, j) u).mp hMem with ⟨_, he1⟩ | ⟨_, he2⟩
            · exact h1 he1
            · exact h2 he2
      let Hψ : SimpleGraph (Fin m) := {
        Adj := fun x y => ∃ e : UpperEdge, s(x, y) = s(e.1.1, e.1.2) ∧ ψ e = 1
        symm := by
          intro x y ⟨e, hs, hψ⟩
          exact ⟨e, Sym2.eq_swap.trans hs, hψ⟩
        loopless := by
          intro x ⟨e, hs, _⟩
          rw [Sym2.eq_iff] at hs
          have := e.2.1
          rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
      }
      have hHψLe : Hψ ≤ H := by
        intro x y hAdj
        rcases hAdj with ⟨e, hs, _⟩
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact e.2.2
        · exact e.2.2.symm
      have hHψDegMod2 : ∀ u : Fin m, (Hψ.degree u : ZMod 2) = 0 := by
        intro u
        have hCardBij : Hψ.degree u =
            (Finset.univ.filter (fun e : UpperEdge => (e.1.1 = u ∨ e.1.2 = u) ∧ ψ e = 1)).card := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_bij
            (fun w hw => ((Hψ.mem_neighborFinset u w).mp hw).choose) ?_ ?_ ?_
          · intro w hw
            obtain ⟨hs, hψ⟩ := ((Hψ.mem_neighborFinset u w).mp hw).choose_spec
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_, hψ⟩
            have huMem : u ∈ s(((Hψ.mem_neighborFinset u w).mp hw).choose.1.1,
                ((Hψ.mem_neighborFinset u w).mp hw).choose.1.2) := by
              rw [← hs]; simp
            rw [Sym2.mem_iff] at huMem
            tauto
          · intro w₁ hw₁ w₂ hw₂ hEq
            dsimp only at hEq
            obtain ⟨hs1, _⟩ := ((Hψ.mem_neighborFinset u w₁).mp hw₁).choose_spec
            obtain ⟨hs2, _⟩ := ((Hψ.mem_neighborFinset u w₂).mp hw₂).choose_spec
            have hsEq : s(u, w₁) = s(u, w₂) := by rw [hs1, hs2, hEq]
            rw [Sym2.eq_iff] at hsEq
            rcases hsEq with ⟨_, h⟩ | ⟨huw₂, _⟩
            · exact h
            · exact False.elim (Hψ.ne_of_adj ((Hψ.mem_neighborFinset u w₂).mp hw₂) huw₂)
          · intro e he
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
            rcases he with ⟨hEnd, hψ⟩
            let w : Fin m := if e.1.1 = u then e.1.2 else e.1.1
            have hsuw : s(u, w) = s(e.1.1, e.1.2) := by
              dsimp [w]
              rcases hEnd with h1 | h2
              · rw [if_pos h1, h1]
              · have hne : e.1.1 ≠ u := by have := e.2.1; omega
                rw [if_neg hne, h2, Sym2.eq_swap]
            have hwMem : w ∈ Hψ.neighborFinset u :=
              (Hψ.mem_neighborFinset u w).mpr ⟨e, hsuw, hψ⟩
            refine ⟨w, hwMem, ?_⟩
            obtain ⟨hs', _⟩ := ((Hψ.mem_neighborFinset u w).mp hwMem).choose_spec
            have hsEq := hs'.symm.trans hsuw
            rw [Sym2.eq_iff] at hsEq
            rcases hsEq with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · exact Subtype.ext (Prod.ext ha hb)
            · have := e.2.1
              have := ((Hψ.mem_neighborFinset u w).mp hwMem).choose.2.1
              omega
        rw [hCardBij, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        simp only [Nat.cast_one]
        refine Eq.trans ?_ (hOrigInc u)
        refine Finset.sum_congr rfl (fun e _ => ?_)
        by_cases hEnd : e.1.1 = u ∨ e.1.2 = u
        · by_cases hψ1 : ψ e = 1
          · rw [if_pos ⟨hEnd, hψ1⟩, if_pos hEnd, hψ1]
          · have hψ0 : ψ e = 0 := hZ2_zero_of_ne_one (ψ e) hψ1
            rw [if_neg (fun h => hψ1 h.2), if_pos hEnd, hψ0]
        · rw [if_neg (fun h => hEnd h.1), if_neg hEnd]
      have hAdjE₀ : Hψ.Adj e₀.1.1 e₀.1.2 := ⟨e₀, rfl, hψe₀⟩
      have hNotAcycΨ : ¬ Hψ.IsAcyclic := by
        intro hAcyc
        let C₀ := Hψ.connectedComponentMk e₀.1.1
        have hTreeC₀ : C₀.toSimpleGraph.IsTree := hAcyc.isTree_connectedComponent C₀
        have hMemC₀ : ∀ x : Fin m, x ∈ C₀ ↔ Hψ.connectedComponentMk x = C₀ :=
          fun x => SimpleGraph.ConnectedComponent.mem_supp_iff C₀ x
        have he1Mem : e₀.1.1 ∈ C₀ := (hMemC₀ _).mpr rfl
        have he2Mem : e₀.1.2 ∈ C₀ :=
          (hMemC₀ _).mpr (SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hAdjE₀.symm))
        haveI : Nontrivial C₀ := ⟨⟨e₀.1.1, he1Mem⟩, ⟨e₀.1.2, he2Mem⟩, by
          intro hEq
          have hVal : e₀.1.1 = e₀.1.2 := congrArg Subtype.val hEq
          have := e₀.2.1
          omega⟩
        obtain ⟨z, hzDeg1⟩ := hTreeC₀.exists_vert_degree_one_of_nontrivial
        have hzDegEq : C₀.toSimpleGraph.degree z = Hψ.degree z.1 := by
          simp only [← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
          · intro y hy
            simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
            exact hy
          · intro y₁ _ y₂ _ h; exact Subtype.ext h
          · intro y hy
            simp only [SimpleGraph.mem_neighborFinset] at hy
            have hyC₀ : y ∈ C₀ := by
              rw [hMemC₀, ← (hMemC₀ z.1).mp z.2]
              exact SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hy.symm)
            exact ⟨⟨y, hyC₀⟩, (C₀.toSimpleGraph.mem_neighborFinset _ _).mpr hy, rfl⟩
        have hMod := hHψDegMod2 z.1
        rw [← hzDegEq, hzDeg1] at hMod
        exact absurd hMod (by decide)
      unfold SimpleGraph.IsAcyclic at hNotAcycΨ
      push_neg at hNotAcycΨ
      rcases hNotAcycΨ with ⟨u₀, cψ, hcψ⟩
      have hcH : (cψ.map (SimpleGraph.Hom.ofLE hHψLe)).IsCycle :=
        hcψ.map Function.injective_id
      have hLenGeG : g ≤ cψ.length := by
        have h1 := hHGirth u₀ _ hcH
        rwa [SimpleGraph.Walk.length_map] at h1
      let S₁ : Finset UpperEdge := Finset.univ.filter (fun e : UpperEdge => ψ e = 1)
      have hgLeS₁ : g ≤ S₁.card := by
        have hNodup : cψ.edges.Nodup := hcψ.isCircuit.isTrail.edges_nodup
        have hCardEdges : cψ.edges.toFinset.card = cψ.length := by
          rw [List.toFinset_card_of_nodup hNodup, SimpleGraph.Walk.length_edges]
        have hSubImg : cψ.edges.toFinset ⊆ S₁.image (fun e : UpperEdge => s(e.1.1, e.1.2)) := by
          intro b hb
          have hbEdge : b ∈ Hψ.edgeSet := cψ.edges_subset_edgeSet (List.mem_toFinset.mp hb)
          refine Sym2.ind (fun x y hxy => ?_) b hbEdge
          simp only [SimpleGraph.mem_edgeSet, Hψ] at hxy
          rcases hxy with ⟨e, hs, hψ1⟩
          rw [Finset.mem_image]
          exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψ1⟩, hs.symm⟩
        have h1 := Finset.card_le_card hSubImg
        have h2 := Finset.card_image_le (f := fun e : UpperEdge => s(e.1.1, e.1.2)) (s := S₁)
        omega
      have hSubW : (S₁ ×ˢ (Finset.univ : Finset (Fin (k + 1)))).image Φ ⊆ W.edges.toFinset := by
        intro a ha
        rw [Finset.mem_image] at ha
        rcases ha with ⟨⟨e, j⟩, hej, rfl⟩
        have heS₁ : e ∈ S₁ := (Finset.mem_product.mp hej).1
        have hψ1 : ψ e = 1 := (Finset.mem_filter.mp heS₁).2
        have hχ1 : χ (Φ (e, j)) = 1 := (hChainConst e j).trans hψ1
        have hCountNe : W.edges.count (Φ (e, j)) ≠ 0 := by
          intro hZero
          dsimp [χ] at hχ1
          rw [hZero] at hχ1
          exact absurd hχ1 (by decide)
        exact List.mem_toFinset.mpr (List.count_pos_iff.mp (Nat.pos_of_ne_zero hCountNe))
      have hCardProd : ((S₁ ×ˢ (Finset.univ : Finset (Fin (k + 1)))).image Φ).card =
          S₁.card * (k + 1) := by
        rw [Finset.card_image_of_injective _ hΦInj, Finset.card_product, Finset.card_univ,
          Fintype.card_fin]
      have hCardLeW := Finset.card_le_card hSubW
      have hToFinLe : W.edges.toFinset.card ≤ W.length := by
        rw [← SimpleGraph.Walk.length_edges]
        exact List.toFinset_card_le W.edges
      have hMulLe : (k + 1) * g ≤ S₁.card * (k + 1) := by
        rw [Nat.mul_comm (k + 1) g]
        exact Nat.mul_le_mul_right (k + 1) hgLeS₁
      omega
    exact ⟨V', inferInstance, inferInstance, G', hG'Conn, hV'Card, hG'EdgeCard, hG'Deg, hG'Short⟩
  have s3 : ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (M : Set V),
      (∀ v : V, (G.neighborSet v).ncard ≤ 3) →
      Fintype.card V + 3 * (Set.univ \ M).ncard < G.edgeSet.ncard →
      ∃ (v₀ : V) (C : G.Walk v₀ v₀), C.IsCycle ∧ ∀ x ∈ C.support, x ∈ M := by
    intro V _instFV G M hDeg hDense
    letI := _instFV
    classical
    have hDegF : ∀ v : V, G.degree v ≤ 3 := by
      intro v
      have h1 := hDeg v
      rw [Set.ncard_eq_toFinset_card'] at h1
      have hEq : (G.neighborSet v).toFinset = G.neighborFinset v := by
        ext x; simp
      rw [hEq, SimpleGraph.card_neighborFinset_eq_degree] at h1
      exact h1
    have hEdgeCard : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
    let R : Set V := Set.univ \ M
    have hRCard : R.ncard = R.toFinset.card := Set.ncard_eq_toFinset_card' R
    let GM : SimpleGraph M := G.induce M
    have hPart : (Finset.univ : Finset V) = M.toFinset ∪ R.toFinset := by
      ext x; simp [R]
    have hDisj : Disjoint M.toFinset R.toFinset := by
      rw [Finset.disjoint_left]
      intro x hxM hxR
      simp [R] at hxM hxR
      exact hxR hxM
    have hSplitDeg : ∀ x : M, G.degree x.1 =
        GM.degree x + (G.neighborFinset x.1 ∩ R.toFinset).card := by
      intro x
      have hN : G.neighborFinset x.1 =
          (G.neighborFinset x.1 ∩ M.toFinset) ∪ (G.neighborFinset x.1 ∩ R.toFinset) := by
        ext y
        simp only [Finset.mem_union, Finset.mem_inter, Set.mem_toFinset, R, Set.mem_diff,
          Set.mem_univ, true_and]
        tauto
      have hNDisj : Disjoint (G.neighborFinset x.1 ∩ M.toFinset)
          (G.neighborFinset x.1 ∩ R.toFinset) :=
        Disjoint.mono inf_le_right inf_le_right hDisj
      have hCardM : (G.neighborFinset x.1 ∩ M.toFinset).card = GM.degree x := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        refine Finset.card_bij (fun y hy => ⟨y, Set.mem_toFinset.mp (Finset.mem_inter.mp hy).2⟩)
          ?_ ?_ ?_
        · intro y hy
          have hy1 := (Finset.mem_inter.mp hy).1
          simp only [SimpleGraph.mem_neighborFinset] at hy1 ⊢
          exact hy1
        · intro y₁ _ y₂ _ h
          exact congrArg Subtype.val h
        · rintro ⟨y, hyM⟩ hyAdj
          simp only [SimpleGraph.mem_neighborFinset] at hyAdj
          exact ⟨y, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyAdj,
            Set.mem_toFinset.mpr hyM⟩, rfl⟩
      conv_lhs => rw [← SimpleGraph.card_neighborFinset_eq_degree, hN]
      rw [Finset.card_union_of_disjoint hNDisj, hCardM]
    have hSumM : ∑ u ∈ M.toFinset, G.degree u =
        (∑ x : M, GM.degree x) + ∑ u ∈ M.toFinset, (G.neighborFinset u ∩ R.toFinset).card := by
      have hBij : ∑ u ∈ M.toFinset, G.degree u = ∑ x : M, G.degree x.1 := by
        refine Finset.sum_bij (fun u hu => ⟨u, Set.mem_toFinset.mp hu⟩) ?_ ?_ ?_ ?_
        · intros; simp
        · intro a₁ _ a₂ _ h; exact congrArg Subtype.val h
        · rintro ⟨a, ha⟩ _; exact ⟨a, Set.mem_toFinset.mpr ha, rfl⟩
        · intros; rfl
      have hBij2 : ∑ x : M, (G.neighborFinset x.1 ∩ R.toFinset).card =
          ∑ u ∈ M.toFinset, (G.neighborFinset u ∩ R.toFinset).card := by
        refine Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_
        · intro x _; exact Set.mem_toFinset.mpr x.2
        · intro x₁ _ x₂ _ h; exact Subtype.ext h
        · intro u hu; exact ⟨⟨u, Set.mem_toFinset.mp hu⟩, Finset.mem_univ _, rfl⟩
        · intros; rfl
      rw [hBij, ← hBij2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => hSplitDeg x)
    have hCross : ∑ u ∈ M.toFinset, (G.neighborFinset u ∩ R.toFinset).card ≤
        3 * R.toFinset.card := by
      have hSwap : ∑ u ∈ M.toFinset, (G.neighborFinset u ∩ R.toFinset).card =
          ∑ w ∈ R.toFinset, (G.neighborFinset w ∩ M.toFinset).card := by
        have hL : ∀ u : V, (G.neighborFinset u ∩ R.toFinset).card =
            ∑ w ∈ R.toFinset, if G.Adj u w then 1 else 0 := by
          intro u
          rw [Finset.card_eq_sum_ones, Finset.inter_comm, ← Finset.filter_mem_eq_inter,
            Finset.sum_filter]
          refine Finset.sum_congr rfl (fun w _ => ?_)
          simp [SimpleGraph.mem_neighborFinset]
        have hR : ∀ w : V, (G.neighborFinset w ∩ M.toFinset).card =
            ∑ u ∈ M.toFinset, if G.Adj w u then 1 else 0 := by
          intro w
          rw [Finset.card_eq_sum_ones, Finset.inter_comm, ← Finset.filter_mem_eq_inter,
            Finset.sum_filter]
          refine Finset.sum_congr rfl (fun u _ => ?_)
          simp [SimpleGraph.mem_neighborFinset]
        simp_rw [hL, hR]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun u _ => ?_))
        simp [G.adj_comm]
      rw [hSwap]
      calc ∑ w ∈ R.toFinset, (G.neighborFinset w ∩ M.toFinset).card
          ≤ ∑ w ∈ R.toFinset, G.degree w := by
            refine Finset.sum_le_sum (fun w _ => ?_)
            rw [← SimpleGraph.card_neighborFinset_eq_degree]
            exact Finset.card_le_card Finset.inter_subset_left
        _ ≤ ∑ _w ∈ R.toFinset, 3 := Finset.sum_le_sum (fun w _ => hDegF w)
        _ = 3 * R.toFinset.card := by simp [Nat.mul_comm]
    have hSumR : ∑ w ∈ R.toFinset, G.degree w ≤ 3 * R.toFinset.card := by
      calc ∑ w ∈ R.toFinset, G.degree w ≤ ∑ _w ∈ R.toFinset, 3 :=
            Finset.sum_le_sum (fun w _ => hDegF w)
        _ = 3 * R.toFinset.card := by simp [Nat.mul_comm]
    have hHand := G.sum_degrees_eq_twice_card_edges
    rw [hPart, Finset.sum_union hDisj] at hHand
    rw [hEdgeCard, hRCard] at hDense
    have hGMDegGt : 2 * Fintype.card M < ∑ x : M, GM.degree x := by
      have hMleV : Fintype.card M ≤ Fintype.card V := Fintype.card_subtype_le _
      omega
    have hMNonempty : Nonempty M := by
      by_contra hEmpty
      rw [not_nonempty_iff] at hEmpty
      have : (∑ x : M, GM.degree x) = 0 := by simp
      omega
    have hMemComp : ∀ (c : GM.ConnectedComponent) (x : M), x ∈ c ↔ GM.connectedComponentMk x = c :=
      fun c x => SimpleGraph.ConnectedComponent.mem_supp_iff c x
    have hNotAcyc : ¬ GM.IsAcyclic := by
      intro hAcyc
      have hCompBound : ∀ c : GM.ConnectedComponent,
          (∑ x ∈ Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c), GM.degree x) <
          2 * (Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c)).card := by
        intro c
        have hTreeC : c.toSimpleGraph.IsTree := hAcyc.isTree_connectedComponent c
        have hCardE := hTreeC.card_edgeFinset
        have hHandC := c.toSimpleGraph.sum_degrees_eq_twice_card_edges
        have hDegEq : ∀ z : c, c.toSimpleGraph.degree z = GM.degree z.1 := by
          intro z
          simp only [← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
          · intro y hy
            simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
            exact hy
          · intro y₁ _ y₂ _ h; exact Subtype.ext h
          · intro y hy
            simp only [SimpleGraph.mem_neighborFinset] at hy
            have hyc : y ∈ c := by
              rw [hMemComp]
              rw [← (hMemComp c z.1).mp z.2]
              exact SimpleGraph.ConnectedComponent.eq.mpr (SimpleGraph.Adj.reachable hy.symm)
            exact ⟨⟨y, hyc⟩, (c.toSimpleGraph.mem_neighborFinset _ _).mpr hy, rfl⟩
        have hSumBij : (∑ z : c, GM.degree z.1) =
            ∑ x ∈ Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c), GM.degree x := by
          refine Finset.sum_bij (fun z _ => z.1) ?_ ?_ ?_ ?_
          · intro z _; simp [(hMemComp c z.1).mp z.2]
          · intro z₁ _ z₂ _ h; exact Subtype.ext h
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            exact ⟨⟨x, (hMemComp c x).mpr hx⟩, Finset.mem_univ _, rfl⟩
          · intros; rfl
        have hCardBij : Fintype.card c =
            (Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c)).card := by
          rw [← Finset.card_univ]
          refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
          · intro z _; simp [(hMemComp c z.1).mp z.2]
          · intro z₁ _ z₂ _ h; exact Subtype.ext h
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            exact ⟨⟨x, (hMemComp c x).mpr hx⟩, Finset.mem_univ _, rfl⟩
        have hSumDegC : (∑ z : c, c.toSimpleGraph.degree z) = ∑ z : c, GM.degree z.1 :=
          Finset.sum_congr rfl (fun z _ => hDegEq z)
        omega
      haveI : Nonempty GM.ConnectedComponent :=
        ⟨GM.connectedComponentMk (Classical.arbitrary M)⟩
      have hSumLt : (∑ c ∈ (Finset.univ : Finset GM.ConnectedComponent),
          ∑ x ∈ Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c), GM.degree x) <
          ∑ c ∈ (Finset.univ : Finset GM.ConnectedComponent),
            2 * (Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c)).card :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => hCompBound c)
      have hLHS : (∑ c ∈ (Finset.univ : Finset GM.ConnectedComponent),
          ∑ x ∈ Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c), GM.degree x) =
          ∑ x : M, GM.degree x :=
        Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
      have hRHS : (∑ c ∈ (Finset.univ : Finset GM.ConnectedComponent),
          2 * (Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c)).card) =
          2 * Fintype.card M := by
        have hCardSum : (∑ c ∈ (Finset.univ : Finset GM.ConnectedComponent),
            (Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c)).card) =
            Fintype.card M := by
          simp_rw [Finset.card_eq_sum_ones]
          have hF : (∑ c ∈ (Finset.univ : Finset GM.ConnectedComponent),
              ∑ x ∈ Finset.univ.filter (fun x : M => GM.connectedComponentMk x = c), (1 : ℕ)) =
              ∑ _x : M, (1 : ℕ) :=
            Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
          rw [hF]
          simp
        rw [← Finset.mul_sum, hCardSum]
      omega
    unfold SimpleGraph.IsAcyclic at hNotAcyc
    push_neg at hNotAcyc
    rcases hNotAcyc with ⟨u₀, CM, hCM⟩
    let emb := SimpleGraph.Embedding.induce M (G := G)
    refine ⟨u₀.1, CM.map emb.toHom, hCM.map emb.injective, ?_⟩
    intro x hx
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
    rcases hx with ⟨y, _, rfl⟩
    exact y.2
  have s4 : ∀ (T : FiniteWeightedTree) (rt p q r : T.Node),
      T.dist rt q ≤ T.dist rt p → T.dist rt r ≤ T.dist rt p →
      T.dist q r ≤ max (T.dist q p) (T.dist p r) := by
    intro T rt p q r hq hr
    classical
    let PT (x y : T.Node) : T.tree.Walk x y := (T.isTree.existsUnique_path x y).choose
    have hPT_path : ∀ x y : T.Node, (PT x y).IsPath :=
      fun x y => (T.isTree.existsUnique_path x y).choose_spec.1
    have hPT_uniq : ∀ {x y : T.Node} (w : T.tree.Walk x y), w.IsPath → w = PT x y :=
      fun w hw => (T.isTree.existsUnique_path _ _).choose_spec.2 w hw
    have hWalkNonneg : ∀ {x y : T.Node} (w : T.tree.Walk x y), 0 ≤ walkWeight T.weight w := by
      intro x y w
      apply List.sum_nonneg
      intro a ha
      rw [List.mem_map] at ha
      rcases ha with ⟨e, he, rfl⟩
      exact T.weight_nonneg e (w.edges_subset_edgeSet he)
    have hPT_le_walk : ∀ {x y : T.Node} (w : T.tree.Walk x y),
        walkWeight T.weight (PT x y) ≤ walkWeight T.weight w := by
      intro x y w
      let Q := w.toPath
      have hQeq : Q.1 = PT x y := hPT_uniq Q.1 Q.2
      rw [← hQeq]
      have hSubperm : Q.1.edges.Subperm w.edges :=
        Q.2.isTrail.edges_nodup.subperm w.edges_toPath_subset
      rcases hSubperm with ⟨l, hPerm, hSub⟩
      have hPermMap : (l.map T.weight).Perm (Q.1.edges.map T.weight) := hPerm.map T.weight
      have hSubMap : (l.map T.weight).Sublist (w.edges.map T.weight) := hSub.map T.weight
      unfold walkWeight
      rw [← hPermMap.sum_eq]
      refine hSubMap.sum_le_sum ?_
      intro a ha
      rw [List.mem_map] at ha
      rcases ha with ⟨e, he, rfl⟩
      exact T.weight_nonneg e (w.edges_subset_edgeSet he)
    have hDistEq : ∀ x y : T.Node, T.dist x y = walkWeight T.weight (PT x y) := by
      intro x y
      unfold FiniteWeightedTree.dist
      have hInf : (⨅ w : T.tree.Walk x y, ENNReal.ofReal (walkWeight T.weight w)) =
          ENNReal.ofReal (walkWeight T.weight (PT x y)) := by
        apply le_antisymm
        · exact ciInf_le ⟨0, fun _ _ => zero_le _⟩ (PT x y)
        · exact le_iInf (fun w => ENNReal.ofReal_le_ofReal (hPT_le_walk w))
      rw [hInf, ENNReal.toReal_ofReal (hWalkNonneg (PT x y))]
    have hDistSelf : ∀ x : T.Node, T.dist x x = 0 := by
      intro x
      rw [hDistEq, ← hPT_uniq SimpleGraph.Walk.nil SimpleGraph.Walk.IsPath.nil]
      simp [walkWeight]
    have hDistSymm : ∀ x y : T.Node, T.dist x y = T.dist y x := by
      intro x y
      rw [hDistEq x y, hDistEq y x, ← hPT_uniq (PT x y).reverse (hPT_path x y).reverse]
      simp [walkWeight, SimpleGraph.Walk.edges_reverse]
    have hDistTri : ∀ x y z : T.Node, T.dist x z ≤ T.dist x y + T.dist y z := by
      intro x y z
      rw [hDistEq x z, hDistEq x y, hDistEq y z]
      have hApp : walkWeight T.weight ((PT x y).append (PT y z)) =
          walkWeight T.weight (PT x y) + walkWeight T.weight (PT y z) := by
        simp [walkWeight, SimpleGraph.Walk.edges_append]
      rw [← hApp]
      exact hPT_le_walk ((PT x y).append (PT y z))
    have hCaseA : ∀ {u m : T.Node} (h : T.tree.Adj u m) (z : T.Node),
        m ∈ (PT u z).support → T.dist u z = T.weight s(u, m) + T.dist m z := by
      intro u m h z hm
      let Q := PT u z
      have hQ : Q.IsPath := hPT_path u z
      have hSpec := Q.take_spec hm
      have hStepPath : (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil).IsPath := by
        rw [SimpleGraph.Walk.isPath_def]
        simp [T.tree.ne_of_adj h]
      have hTakeEq : Q.takeUntil m hm = SimpleGraph.Walk.cons h SimpleGraph.Walk.nil := by
        rw [hPT_uniq (Q.takeUntil m hm) (hQ.takeUntil hm),
          hPT_uniq (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) hStepPath]
      have hDropEq : Q.dropUntil m hm = PT m z := hPT_uniq _ (hQ.dropUntil hm)
      rw [hDistEq u z, hDistEq m z]
      change walkWeight T.weight Q = T.weight s(u, m) + walkWeight T.weight (PT m z)
      rw [← hSpec, hTakeEq, hDropEq]
      simp [walkWeight]
    have hCaseB : ∀ {u m p' : T.Node} (h : T.tree.Adj u m) (P₁ : T.tree.Walk m p'),
        (SimpleGraph.Walk.cons h P₁).IsPath →
        ∀ z : T.Node, m ∉ (PT u z).support → T.dist z p' = T.dist u z + T.dist u p' := by
      intro u m p' h P₁ hCons z hm
      let Q := PT u z
      have hQ : Q.IsPath := hPT_path u z
      have huNotMem : u ∉ P₁.support := by
        have hNodup := (SimpleGraph.Walk.isPath_def _).mp hCons
        simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hNodup
        exact hNodup.1
      have hDisjSupp : ∀ v : T.Node, v ∈ Q.support → v ∈ P₁.support → False := by
        intro v hvQ hvP₁
        have hvu : v ≠ u := fun hEq => huNotMem (hEq ▸ hvP₁)
        have hvCons : v ∈ (SimpleGraph.Walk.cons h P₁).support := by
          simp [SimpleGraph.Walk.support_cons, hvP₁]
        have hUniqV : Q.takeUntil v hvQ = (SimpleGraph.Walk.cons h P₁).takeUntil v hvCons := by
          rw [hPT_uniq _ (hQ.takeUntil hvQ), hPT_uniq _ (hCons.takeUntil hvCons)]
        have hmInR : m ∈ ((SimpleGraph.Walk.cons h P₁).takeUntil v hvCons).support := by
          simp [SimpleGraph.Walk.takeUntil, hvu.symm]
        have hmInL : m ∈ Q.support :=
          SimpleGraph.Walk.support_takeUntil_subset Q hvQ (hUniqV ▸ hmInR)
        exact hm hmInL
      let W := Q.reverse.append (SimpleGraph.Walk.cons h P₁)
      have hWPath : W.IsPath := by
        rw [SimpleGraph.Walk.isPath_def]
        have hSupp : W.support = Q.support.reverse ++ P₁.support := by
          simp [W, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse]
        rw [hSupp, List.nodup_append]
        refine ⟨List.nodup_reverse.mpr ((SimpleGraph.Walk.isPath_def _).mp hQ),
          (SimpleGraph.Walk.isPath_def _).mp hCons.of_cons, ?_⟩
        intro v hv1 w hv2 hEq
        subst hEq
        rw [List.mem_reverse] at hv1
        exact hDisjSupp v hv1 hv2
      have hWEq : W = PT z p' := hPT_uniq W hWPath
      have hConsEq : SimpleGraph.Walk.cons h P₁ = PT u p' := hPT_uniq _ hCons
      rw [hDistEq z p', ← hWEq, hDistEq u z, hDistEq u p', ← hConsEq]
      change walkWeight T.weight (Q.reverse.append (SimpleGraph.Walk.cons h P₁)) =
        walkWeight T.weight Q + walkWeight T.weight (SimpleGraph.Walk.cons h P₁)
      simp [walkWeight, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse]
    have hFourPt : ∀ {u p' : T.Node} (P₀ : T.tree.Walk u p'), P₀.IsPath →
        ∀ q' r' : T.Node,
        T.dist q' r' + T.dist u p' ≤
          max (T.dist q' p' + T.dist u r') (T.dist p' r' + T.dist u q') := by
      intro u p' P₀
      induction P₀ with
      | @nil u =>
        intro _ q' r'
        rw [hDistSelf]
        have hTri := hDistTri q' u r'
        have hLe := le_max_left (T.dist q' u + T.dist u r') (T.dist u r' + T.dist u q')
        linarith
      | @cons u m p' h P₁ ih =>
        intro hP₀ q' r'
        by_cases hmq : m ∈ (PT u q').support
        · by_cases hmr : m ∈ (PT u r').support
          · have hup : T.dist u p' = T.weight s(u, m) + T.dist m p' := by
              have hConsEq : SimpleGraph.Walk.cons h P₁ = PT u p' := hPT_uniq _ hP₀
              have hP₁Eq : P₁ = PT m p' := hPT_uniq _ hP₀.of_cons
              rw [hDistEq u p', ← hConsEq, hDistEq m p', ← hP₁Eq]
              simp [walkWeight]
            have huq := hCaseA h q' hmq
            have hur := hCaseA h r' hmr
            have hIH := ih hP₀.of_cons q' r'
            rcases le_max_iff.mp hIH with hL | hR
            · exact le_trans (by linarith) (le_max_left _ _)
            · exact le_trans (by linarith) (le_max_right _ _)
          · have hrp := hCaseB h P₁ hP₀ r' hmr
            rw [hDistSymm r' p'] at hrp
            have hTri := hDistTri q' u r'
            rw [hDistSymm q' u] at hTri
            exact le_trans (by linarith) (le_max_right _ _)
        · have hqp := hCaseB h P₁ hP₀ q' hmq
          have hTri := hDistTri q' u r'
          rw [hDistSymm q' u] at hTri
          exact le_trans (by linarith) (le_max_left _ _)
    have hMain := hFourPt (PT rt p) (hPT_path rt p) q r
    rcases le_max_iff.mp hMain with hL | hR
    · exact le_trans (by linarith) (le_max_left _ _)
    · exact le_trans (by linarith) (le_max_right _ _)
  have s5 : ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (g' : ℕ)
      (M : Set V) (v₀ : V) (C : G.Walk v₀ v₀) (T : FiniteWeightedTree) (t : ℝ) (f : M → T.Node),
      G.Connected →
      (∀ (w₀ : V) (W : G.Walk w₀ w₀), W.length < g' →
        ∀ a : Sym2 V, (W.edges.count a : ZMod 2) = 0) →
      C.IsCycle →
      (∀ x ∈ C.support, x ∈ M) →
      (∀ rt p q r : T.Node, T.dist rt q ≤ T.dist rt p → T.dist rt r ≤ T.dist rt p →
        T.dist q r ≤ max (T.dist q p) (T.dist p r)) →
      IsDominatingRamseyTreeEmbedding G M T t f →
      (g' : ℝ) / 3 ≤ t := by
    intro V _instFV _instDV G g' M v₀ C T t f hConn hShort hCycle hCM hTree hf
    letI := _instFV
    letI := _instDV
    classical
    by_contra hNotLe
    have ht3 : 3 * t < (g' : ℝ) := by linarith
    let eV : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    let P₀ (u v : V) : G.Walk u v := (hConn.exists_walk_length_eq_dist u v).choose
    have hP₀_len : ∀ u v : V, (P₀ u v).length = G.dist u v :=
      fun u v => (hConn.exists_walk_length_eq_dist u v).choose_spec
    let P (u v : V) : G.Walk u v := if eV u ≤ eV v then P₀ u v else (P₀ v u).reverse
    have hP_len : ∀ u v : V, (P u v).length = G.dist u v := by
      intro u v
      dsimp [P]
      split_ifs
      · exact hP₀_len u v
      · rw [SimpleGraph.Walk.length_reverse, hP₀_len v u, SimpleGraph.dist_comm]
    let χ {u v : V} (W : G.Walk u v) : Sym2 V → ZMod 2 :=
      fun a => (W.edges.count a : ZMod 2)
    have hχ_append : ∀ {u v w : V} (W₁ : G.Walk u v) (W₂ : G.Walk v w),
        χ (W₁.append W₂) = χ W₁ + χ W₂ := by
      intro u v w W₁ W₂
      ext a
      simp [χ, SimpleGraph.Walk.edges_append, List.count_append, Nat.cast_add]
    have hχ_rev : ∀ {u v : V} (W : G.Walk u v), χ W.reverse = χ W := by
      intro u v W
      ext a
      simp [χ, SimpleGraph.Walk.edges_reverse, List.count_reverse]
    have hZ2_self : ∀ b : ZMod 2, b + b = 0 := by decide
    have hFn_self : ∀ z : Sym2 V → ZMod 2, z + z = 0 := by
      intro z; ext a; exact hZ2_self (z a)
    have hP_self : ∀ u : V, χ (P u u) = 0 := by
      intro u
      have hLen : (P u u).edges.length = 0 := by
        rw [SimpleGraph.Walk.length_edges, hP_len, SimpleGraph.dist_self]
      have hNil : (P u u).edges = [] := List.eq_nil_of_length_eq_zero hLen
      ext a
      simp [χ, hNil]
    have hP_symm : ∀ u v : V, χ (P u v) = χ (P v u) := by
      intro u v
      by_cases huv : u = v
      · subst huv; rfl
      · have heNe : eV u ≠ eV v := fun h => huv (eV.injective h)
        rcases lt_or_gt_of_ne heNe with hlt | hgt
        · have h1 : eV u ≤ eV v := le_of_lt hlt
          have h2 : ¬ eV v ≤ eV u := not_le_of_gt hlt
          dsimp [P]
          rw [if_pos h1, if_neg h2, hχ_rev]
        · have h1 : ¬ eV u ≤ eV v := not_le_of_gt hgt
          have h2 : eV v ≤ eV u := le_of_lt hgt
          dsimp [P]
          rw [if_neg h1, if_pos h2, hχ_rev]
    have hWalkLen1 : ∀ {u v : V} (W : G.Walk u v), W.length = 1 → W.edges = [s(u, v)] := by
      intro u v W hW
      cases W with
      | nil => simp at hW
      | cons h₁ W' =>
        cases W' with
        | nil => rfl
        | cons _ _ => simp at hW
    have hP_adj : ∀ {u v : V} (h : G.Adj u v),
        χ (P u v) = χ (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) := by
      intro u v h
      have hLen : (P u v).length = 1 := by
        rw [hP_len, SimpleGraph.dist_eq_one_iff_adj.mpr h]
      have hEdges := hWalkLen1 (P u v) hLen
      ext a
      simp [χ, hEdges]
    have hTriCancel : ∀ y x z : M,
        T.dist (f y) (f x) ≤ t → T.dist (f x) (f z) ≤ t → T.dist (f y) (f z) ≤ t →
        χ (P y.1 x.1) + χ (P x.1 z.1) = χ (P y.1 z.1) := by
      intro y x z hyx hxz hyz
      have d1 : (G.dist y.1 x.1 : ℝ) ≤ t := le_trans (hf.2 y x).1 hyx
      have d2 : (G.dist x.1 z.1 : ℝ) ≤ t := le_trans (hf.2 x z).1 hxz
      have d3 : (G.dist z.1 y.1 : ℝ) ≤ t := by
        rw [SimpleGraph.dist_comm]
        exact le_trans (hf.2 y z).1 hyz
      let WΔ := (P y.1 x.1).append ((P x.1 z.1).append (P z.1 y.1))
      have hWLen : WΔ.length < g' := by
        have hEq : WΔ.length = G.dist y.1 x.1 + (G.dist x.1 z.1 + G.dist z.1 y.1) := by
          simp [WΔ, SimpleGraph.Walk.length_append, hP_len]
        have hR : (WΔ.length : ℝ) < (g' : ℝ) := by
          rw [hEq]
          push_cast
          linarith
        exact_mod_cast hR
      have hZero : χ WΔ = 0 := by
        ext a
        exact hShort y.1 WΔ hWLen a
      rw [hχ_append, hχ_append, hP_symm z.1 y.1] at hZero
      calc χ (P y.1 x.1) + χ (P x.1 z.1)
          = (χ (P y.1 x.1) + (χ (P x.1 z.1) + χ (P y.1 z.1))) + χ (P y.1 z.1) := by
            rw [add_assoc, add_assoc, hFn_self, add_zero]
        _ = 0 + χ (P y.1 z.1) := by rw [hZero]
        _ = χ (P y.1 z.1) := zero_add _
    let stepChi (x y : M) : Sym2 V → ZMod 2 := χ (P x.1 y.1)
    let stepRel (x y : M) : Prop := T.dist (f x) (f y) ≤ t
    let cycSum (L : List M) : Sym2 V → ZMod 2 :=
      match L with
      | [] => 0
      | u :: ws => thm4OpenSum stepChi u ws u
    let cycRel (L : List M) : Prop :=
      match L with
      | [] => True
      | u :: ws => thm4OpenRel stepRel u ws u
    have hSplitSum : ∀ (A : List M) (u x : M) (B : List M) (last : M),
        thm4OpenSum stepChi u (A ++ x :: B) last =
          thm4OpenSum stepChi u A x + thm4OpenSum stepChi x B last := by
      intro A
      induction A with
      | nil => intros; rfl
      | cons w ws ih =>
        intro u x B last
        simp only [List.cons_append, thm4OpenSum, ih, add_assoc]
    have hSplitRel : ∀ (A : List M) (u x : M) (B : List M) (last : M),
        thm4OpenRel stepRel u (A ++ x :: B) last ↔
          thm4OpenRel stepRel u A x ∧ thm4OpenRel stepRel x B last := by
      intro A
      induction A with
      | nil => intros; rfl
      | cons w ws ih =>
        intro u x B last
        simp only [List.cons_append, thm4OpenRel, ih, and_assoc]
    have hRot1Sum : ∀ (u : M) (ws : List M), cycSum (u :: ws) = cycSum (ws ++ [u]) := by
      intro u ws
      cases ws with
      | nil => rfl
      | cons w rest =>
        dsimp [cycSum]
        rw [hSplitSum rest w u [] w]
        simp [thm4OpenSum, add_comm]
    have hRot1Rel : ∀ (u : M) (ws : List M), cycRel (u :: ws) ↔ cycRel (ws ++ [u]) := by
      intro u ws
      cases ws with
      | nil => rfl
      | cons w rest =>
        dsimp [cycRel]
        rw [hSplitRel rest w u [] w]
        simp [thm4OpenRel, and_comm]
    have hRotSum : ∀ A B : List M, cycSum (A ++ B) = cycSum (B ++ A) := by
      intro A
      induction A with
      | nil => intro B; simp
      | cons u ws ih =>
        intro B
        calc cycSum ((u :: ws) ++ B)
            = cycSum (u :: (ws ++ B)) := rfl
          _ = cycSum ((ws ++ B) ++ [u]) := hRot1Sum u (ws ++ B)
          _ = cycSum (ws ++ (B ++ [u])) := by rw [List.append_assoc]
          _ = cycSum ((B ++ [u]) ++ ws) := ih (B ++ [u])
          _ = cycSum (B ++ (u :: ws)) := by simp
    have hRotRel : ∀ A B : List M, cycRel (A ++ B) ↔ cycRel (B ++ A) := by
      intro A
      induction A with
      | nil => intro B; simp
      | cons u ws ih =>
        intro B
        calc cycRel ((u :: ws) ++ B)
            ↔ cycRel (u :: (ws ++ B)) := Iff.rfl
          _ ↔ cycRel ((ws ++ B) ++ [u]) := hRot1Rel u (ws ++ B)
          _ ↔ cycRel (ws ++ (B ++ [u])) := by rw [List.append_assoc]
          _ ↔ cycRel ((B ++ [u]) ++ ws) := ih (B ++ [u])
          _ ↔ cycRel (B ++ (u :: ws)) := by simp
    let rt : T.Node := f ⟨v₀, hCM v₀ C.start_mem_support⟩
    have hMainElim : ∀ n : ℕ, ∀ L : List M, L.length = n → cycRel L → cycSum L = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro L hLen hRel
        match L with
        | [] => rfl
        | [a] =>
          dsimp [cycSum, thm4OpenSum, stepChi]
          exact hP_self a.1
        | [a, b] =>
          dsimp [cycSum, thm4OpenSum, stepChi]
          rw [hP_symm b.1 a.1]
          exact hFn_self _
        | a₀ :: a₁ :: a₂ :: rest₀ =>
          let Lfull := a₀ :: a₁ :: a₂ :: rest₀
          have hNe : Lfull.toFinset.Nonempty := ⟨a₀, List.mem_toFinset.mpr (by simp [Lfull])⟩
          obtain ⟨x, hxFin, hxMax⟩ :=
            Finset.exists_max_image Lfull.toFinset (fun w : M => T.dist rt (f w)) hNe
          have hxMem : x ∈ Lfull := List.mem_toFinset.mp hxFin
          obtain ⟨A, B, hLAB⟩ := List.append_of_mem hxMem
          have hBALen : 2 ≤ (B ++ A).length := by
            have h1 := congrArg List.length hLAB
            simp only [Lfull, List.length_cons, List.length_append] at h1 ⊢
            omega
          match hBA : B ++ A with
          | [] => simp [hBA] at hBALen
          | [_] => simp [hBA] at hBALen
          | z :: rest₁ =>
            have hRestNe : rest₁ ≠ [] := by
              intro hNil
              simp [hBA, hNil] at hBALen
            let mid := rest₁.dropLast
            let y := rest₁.getLast hRestNe
            have hRestEq : mid ++ [y] = rest₁ := List.dropLast_append_getLast hRestNe
            have hBA2 : B ++ A = (z :: mid) ++ [y] := by
              rw [hBA, List.cons_append, hRestEq]
            let L₂ : List M := y :: x :: z :: mid
            have hRotSumL : cycSum Lfull = cycSum L₂ := by
              calc cycSum Lfull
                  = cycSum (A ++ (x :: B)) := by rw [hLAB]
                _ = cycSum ((x :: B) ++ A) := hRotSum A (x :: B)
                _ = cycSum (x :: (B ++ A)) := rfl
                _ = cycSum ((x :: z :: mid) ++ [y]) := by rw [hBA2]; rfl
                _ = cycSum ([y] ++ (x :: z :: mid)) := hRotSum (x :: z :: mid) [y]
                _ = cycSum L₂ := rfl
            have hRotRelL : cycRel L₂ := by
              have h1 : cycRel (A ++ (x :: B)) := hLAB ▸ hRel
              have h2 : cycRel ((x :: B) ++ A) := (hRotRel A (x :: B)).mp h1
              have h3 : cycRel ((x :: z :: mid) ++ [y]) := by
                change cycRel (x :: (B ++ A)) at h2
                rw [hBA2] at h2
                exact h2
              exact (hRotRel (x :: z :: mid) [y]).mp h3
            have hyMemBA : y ∈ B ++ A := by
              rw [hBA2]; simp
            have hzMemBA : z ∈ B ++ A := by
              rw [hBA2]; simp
            have hyMemL : y ∈ Lfull := by
              rw [hLAB, List.mem_append, List.mem_cons]
              rw [List.mem_append] at hyMemBA
              tauto
            have hzMemL : z ∈ Lfull := by
              rw [hLAB, List.mem_append, List.mem_cons]
              rw [List.mem_append] at hzMemBA
              tauto
            have hyDist : T.dist rt (f y) ≤ T.dist rt (f x) :=
              hxMax y (List.mem_toFinset.mpr hyMemL)
            have hzDist : T.dist rt (f z) ≤ T.dist rt (f x) :=
              hxMax z (List.mem_toFinset.mpr hzMemL)
            dsimp [L₂, cycRel, thm4OpenRel, stepRel] at hRotRelL
            rcases hRotRelL with ⟨hyx, hxz, hMidRel⟩
            have hyz : T.dist (f y) (f z) ≤ t := by
              have h4 := hTree rt (f x) (f y) (f z) hyDist hzDist
              exact le_trans h4 (max_le hyx hxz)
            let L' : List M := y :: z :: mid
            have hLenL' : L'.length < n := by
              have h1 := congrArg List.length hLAB
              have h2 := congrArg List.length hBA2
              simp only [Lfull, L', List.length_cons, List.length_append] at h1 h2 hLen ⊢
              omega
            have hRelL' : cycRel L' := ⟨hyz, hMidRel⟩
            have hSumL' : cycSum L' = 0 := ih L'.length hLenL' L' rfl hRelL'
            rw [hRotSumL]
            dsimp [L₂, L', cycSum, thm4OpenSum, stepChi] at hSumL' ⊢
            rw [← add_assoc, hTriCancel y x z hyx hxz hyz]
            exact hSumL'
    have hWalkToList : ∀ {u last : V} (W : G.Walk u last),
        ¬ W.Nil → (hW : ∀ w ∈ W.support, w ∈ M) →
        ∃ mid : List M,
          thm4OpenRel stepRel ⟨u, hW u W.start_mem_support⟩ mid ⟨last, hW last W.end_mem_support⟩ ∧
          thm4OpenSum stepChi ⟨u, hW u W.start_mem_support⟩ mid ⟨last, hW last W.end_mem_support⟩ =
            χ W := by
      intro u last W
      induction W with
      | nil =>
        intro hNotNil _
        exact absurd SimpleGraph.Walk.Nil.nil hNotNil
      | @cons u w last h W' ih =>
        intro _ hW
        have hu : u ∈ M := hW u (by simp)
        have hw : w ∈ M := hW w (by simp [W'.start_mem_support])
        have hStepDist : stepRel ⟨u, hu⟩ ⟨w, hw⟩ := by
          dsimp [stepRel]
          have h1 := (hf.2 ⟨u, hu⟩ ⟨w, hw⟩).2
          unfold graphDist at h1
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr h] at h1
          push_cast at h1
          linarith
        have hStepChi : stepChi ⟨u, hu⟩ ⟨w, hw⟩ = χ (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil) :=
          hP_adj h
        cases W' with
        | nil =>
          refine ⟨[], hStepDist, ?_⟩
          dsimp [thm4OpenSum]
          exact hStepChi
        | cons h₂ W'' =>
          have hW'NotNil : ¬ (SimpleGraph.Walk.cons h₂ W'').Nil := by simp
          have hW'Sub : ∀ z ∈ (SimpleGraph.Walk.cons h₂ W'').support, z ∈ M :=
            fun z hz => hW z (List.mem_cons_of_mem u hz)
          obtain ⟨mid', hRel', hSum'⟩ := ih hW'NotNil hW'Sub
          refine ⟨⟨w, hw⟩ :: mid', ⟨hStepDist, hRel'⟩, ?_⟩
          dsimp [thm4OpenSum]
          rw [hStepChi, hSum', ← hχ_append]
          rfl
    have hC3 : 3 ≤ C.length := hCycle.three_le_length
    have hCNotNil : ¬ C.Nil := by
      intro hNil
      cases hNil
      simp at hC3
    obtain ⟨midC, hRelC, hSumC⟩ := hWalkToList C hCNotNil hCM
    let LC : List M := ⟨v₀, hCM v₀ C.start_mem_support⟩ :: midC
    have hChiCZero : χ C = 0 := by
      rw [← hSumC]
      exact hMainElim LC.length LC rfl hRelC
    have hEdgesNe : C.edges ≠ [] := by
      intro hNil
      have : C.edges.length = 0 := by simp [hNil]
      rw [SimpleGraph.Walk.length_edges] at this
      omega
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil C.edges hEdgesNe
    have hCount1 : C.edges.count e₀ = 1 :=
      List.count_eq_one_of_mem hCycle.isCircuit.isTrail.edges_nodup he₀
    have hOneEqZero : (1 : ZMod 2) = 0 := by
      have hAt := congrFun hChiCZero e₀
      dsimp [χ] at hAt
      rw [hCount1] at hAt
      exact_mod_cast hAt
    exact absurd hOneEqZero (by decide)
  refine ⟨(1 : ℝ) / 288, (1 : ℝ) / 48, by norm_num, by norm_num, by norm_num, ?_⟩
  intro ε hεPos hεLe N₀ hN₀
  let g : ℕ := max N₀ 100
  have hg100 : 100 ≤ g := le_max_right N₀ 100
  have hg3 : 3 ≤ g := by omega
  have hN₀g : N₀ ≤ g := le_max_left N₀ 100
  obtain ⟨m, H, hgm, hm16, hHConn, hHDeg, hHDense, hHUpper, hHGirth⟩ := s1 g hg3
  let k : ℕ := ⌊(1 : ℝ) / (24 * ε)⌋₊
  have h24εPos : 0 < 24 * ε := by linarith
  have hDivGe2 : (2 : ℝ) ≤ (1 : ℝ) / (24 * ε) := by
    rw [le_div_iff₀ h24εPos]
    linarith
  have hk2 : 2 ≤ k := Nat.le_floor hDivGe2
  have hk1 : 1 ≤ k := by omega
  have hkUpper : (k : ℝ) ≤ (1 : ℝ) / (24 * ε) := Nat.floor_le (by positivity)
  have hεkUpper : ε * (k : ℝ) ≤ (1 : ℝ) / 24 := by
    have h1 : (k : ℝ) * (24 * ε) ≤ 1 := (le_div_iff₀ h24εPos).mp hkUpper
    linarith
  have hkLower : (1 : ℝ) / (24 * ε) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hεkLower : (1 : ℝ) / 36 < ε * (k : ℝ) := by
    have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hkp1 : (k : ℝ) + 1 ≤ (3 / 2 : ℝ) * (k : ℝ) := by linarith
    have hlt : (1 : ℝ) / (24 * ε) < (3 / 2 : ℝ) * (k : ℝ) := lt_of_lt_of_le hkLower hkp1
    have hmul : 1 < (3 / 2 : ℝ) * (k : ℝ) * (24 * ε) := (div_lt_iff₀ h24εPos).mp hlt
    linarith
  obtain ⟨V', hF, hD, G', hG'⟩ := s2 m g k hg3 hgm hk1 H hHConn hHDeg hHGirth
  letI := hF
  letI := hD
  rcases hG' with ⟨hG'Conn, hV'Card, hG'Edge, hG'Deg, hG'Short⟩
  refine ⟨V', hF, G', hG'Conn, ?_, ?_, ?_⟩
  · omega
  · let EH : ℕ := H.edgeSet.ncard
    have hEH126 : 126 ≤ EH := by omega
    have hEHR : (125 : ℝ) ≤ (EH : ℝ) := by
      have : (126 : ℝ) ≤ (EH : ℝ) := by exact_mod_cast hEH126
      linarith
    have hNR : ((k * EH : ℕ) : ℝ) ≤ (Fintype.card V' : ℝ) := by
      have : k * EH ≤ Fintype.card V' := by dsimp [EH]; omega
      exact_mod_cast this
    have hMul : ε * ((k * EH : ℕ) : ℝ) ≤ ε * (Fintype.card V' : ℝ) :=
      mul_le_mul_of_nonneg_left hNR (le_of_lt hεPos)
    push_cast at hMul
    nlinarith
  · intro M hM T t _ht f hf
    let EH : ℕ := H.edgeSet.ncard
    have hEHR_le : (EH : ℝ) ≤ (3 / 2 : ℝ) * (m : ℝ) := by
      have : (2 : ℝ) * (EH : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast hHUpper
      linarith
    have hEHR_gt : (5 / 4 : ℝ) * (m : ℝ) < (EH : ℝ) := by
      have : (5 : ℝ) * (m : ℝ) < 4 * (EH : ℝ) := by exact_mod_cast hHDense
      linarith
    have hNR_eq : (Fintype.card V' : ℝ) = (m : ℝ) + (k : ℝ) * (EH : ℝ) := by
      exact_mod_cast hV'Card
    have hεN_le_m12 : ε * (Fintype.card V' : ℝ) ≤ (m : ℝ) / 12 := by
      rw [hNR_eq]
      have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hEHNonneg : (0 : ℝ) ≤ (EH : ℝ) := Nat.cast_nonneg EH
      nlinarith
    have hDenseM : Fintype.card V' + 3 * (Set.univ \ M).ncard < G'.edgeSet.ncard := by
      have hR : ((Fintype.card V' + 3 * (Set.univ \ M).ncard : ℕ) : ℝ) <
          (G'.edgeSet.ncard : ℝ) := by
        have hER_eq : (G'.edgeSet.ncard : ℝ) = ((k : ℝ) + 1) * (EH : ℝ) := by
          exact_mod_cast hG'Edge
        push_cast
        linarith
      exact_mod_cast hR
    obtain ⟨v₀, C, hCycle, hCM⟩ := s3 G' M hG'Deg hDenseM
    have hDistort : (((k + 1) * g : ℕ) : ℝ) / 3 ≤ t :=
      s5 G' ((k + 1) * g) M v₀ C T t f hG'Conn hG'Short hCycle hCM (s4 T) hf
    have hεN_ge2 : (2 : ℝ) ≤ ε * (Fintype.card V' : ℝ) := by
      have hEH126 : 126 ≤ EH := by omega
      have hEHR : (125 : ℝ) ≤ (EH : ℝ) := by
        have : (126 : ℝ) ≤ (EH : ℝ) := by exact_mod_cast hEH126
        linarith
      rw [hNR_eq]
      have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    have hεN_le_pow : ε * (Fintype.card V' : ℝ) ≤ (2 : ℝ) ^ (4 * g) := by
      have hm_le_pow : (m : ℝ) ≤ (2 : ℝ) ^ (4 * g) := by
        have h1 : (m : ℝ) ≤ ((16 ^ g : ℕ) : ℝ) := by exact_mod_cast hm16
        have h2 : ((16 ^ g : ℕ) : ℝ) = (2 : ℝ) ^ (4 * g) := by
          push_cast
          rw [pow_mul]
          norm_num
        linarith
      have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hLog2Pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLogbNonneg : 0 ≤ Real.logb 2 (ε * (Fintype.card V' : ℝ)) := by
      rw [Real.logb]
      apply div_nonneg
      · exact Real.log_nonneg (by linarith)
      · exact le_of_lt hLog2Pos
    have hLogbLe : Real.logb 2 (ε * (Fintype.card V' : ℝ)) ≤ 4 * (g : ℝ) := by
      rw [Real.logb, div_le_iff₀ hLog2Pos]
      have h1 := Real.log_le_log (by linarith) hεN_le_pow
      rw [Real.log_pow] at h1
      push_cast at h1
      linarith
    have hTerm1 : (1 / 24 : ℝ) * ε⁻¹ ≤ (k : ℝ) + 1 := by
      have hEq : (1 / 24 : ℝ) * ε⁻¹ = (1 : ℝ) / (24 * ε) := by ring
      linarith
    have hTerm2 : (1 / 4 : ℝ) * Real.logb 2 (ε * (Fintype.card V' : ℝ)) ≤ (g : ℝ) := by
      linarith
    have hProd : ((1 / 24 : ℝ) * ε⁻¹) * ((1 / 4 : ℝ) * Real.logb 2 (ε * (Fintype.card V' : ℝ))) ≤
        ((k : ℝ) + 1) * (g : ℝ) := by
      refine mul_le_mul hTerm1 hTerm2 (by positivity) ?_
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    push_cast at hDistort
    linarith

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
                      (Real.logb 2 (Real.logb 2 (n : ℝ) + 2)) ^ d :=
  thm1_from_finite_diam finite_diam_hc_ramsey_hst

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
                    c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ)) ≤ (β : ℝ) :=
  thm2_from_expander exists_bounded_degree_expander

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
                c * Real.logb 2 (n : ℝ) ≤ α :=
  thm3_from_expander exists_bounded_degree_expander

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
                  c * ε⁻¹ * Real.logb 2 (ε * (N : ℝ)) ≤ t :=
  thm4_ramsey_tree_lower_bound
