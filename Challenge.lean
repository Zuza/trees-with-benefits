import Mathlib

set_option maxHeartbeats 4000000

/-!
# Original Problem
# Scope Note
Source paper: Arnold Filtser and Goran Zuzic, "Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion" (Sections 1 through 5 ONLY; reference copies up to Section 5 are in `<problem_root>/reference/filtser_zuzic_sections_1_to_5.md` and `<problem_root>/reference/filtser_zuzic_sections_1_to_5.pdf`).
Formalize the paper ONLY up to Section 5 (not after Section 5 — ignore Sections 6 and 7 completely). Formalize all definitions and all four theorems of Sections 1 through 5 (**Theorem 1**, **Theorem 2**, **Theorem 3**, and **Theorem 4**) in this single workspace, with root theorem `trees_with_benefits` asserting the conjunction of Theorem 1, Theorem 2, Theorem 3, and Theorem 4 (define each of the four theorem statements as a `def ... : Prop` above `theorem trees_with_benefits`).

# Shared Definitions (Sections 3–5)
1. **Graphs, shortest-path distance, and bounded-hop distance**:
   - Let $G = (V, E, w)$ be a finite undirected simple graph on $n = |V|$ vertices with edge weights $w : E \to \mathbb{R}_{>0}$ (an unweighted graph has unit weights $w(e) = 1$).
   - When $G$ is connected and unweighted, $d_G : V \times V \to \mathbb{R}_{\ge 0}$ denotes its shortest-path distance (minimum number of edges in a path between $u$ and $v$).
   - For an integer hop bound $H \ge 0$ and vertices $u, v \in V$, the $H$-hop distance $d_G^{(H)}(u, v) \in [0, \infty]$ is the minimum total edge weight $\sum_{i=1}^{q} w(\{v_{i-1}, v_i\})$ over all paths (or walks) $(v_0 = u, v_1, \dots, v_q = v)$ in $G$ of length $q \le H$ hops, with $d_G^{(H)}(u, u) = 0$ and $d_G^{(H)}(u, v) = \infty$ if no path of at most $H$ edges connects $u$ and $v$.

2. **Extended metric spaces and finite weighted trees**:
   - An extended metric space $(X, d_X)$ is a set $X$ equipped with a distance $d_X : X \times X \to [0, \infty]$ satisfying $d_X(x, x) = 0$, symmetry $d_X(x, y) = d_X(y, x)$, and the triangle inequality $d_X(x, z) \le d_X(x, y) + d_X(y, z)$ for all $x, y, z \in X$ (allowing $\infty$ distances between points, as in Section 3).
   - A finite weighted tree $T = (V(T), E(T), w_T)$ is a finite connected acyclic simple graph equipped with non-negative edge weights $w_T : E(T) \to \mathbb{R}_{\ge 0}$ and induced shortest-path tree distance $d_T : V(T) \times V(T) \to \mathbb{R}_{\ge 0}$.

3. **Hierarchically Separated Trees (HST, Definition 1)**:
   - An HST on leaf set $V$ is a metric space $(V, d_U)$ (with distances in $[0, \infty]$) induced by a finite rooted tree $T$ whose set of leaves is bijectively identified with $V$, equipped with node labels $\ell : V(T) \to [0, \infty]$ such that:
     - whenever $q \in V(T)$ is a descendant of $z \in V(T)$, $\ell(q) \le \ell(z)$;
     - for every $q \in V(T)$, $\ell(q) = 0$ if and only if $q$ is a leaf of $T$;
     - for all $u, v \in V$, $d_U(u, v) = \ell(\mathrm{lca}_T(u, v))$, where $\mathrm{lca}_T(u, v)$ is the least common ancestor of the leaves corresponding to $u$ and $v$ in $T$.

4. **Stochastic hop-constrained Ramsey-type embeddings into HSTs (Definition 2)**:
   - Given hop parameter $h \in \{1, \dots, n\}$, a stochastic hop-constrained Ramsey-type embedding of $G$ into HSTs is a finite-support probability distribution $\mathcal{D}$ over pairs $(U, M)$, where $U$ is an HST on leaf set $V$ (with induced distance $d_U : V \times V \to [0, \infty]$) and $M \subseteq V$ is the *saved set*:
     - **hop-stretch** $\beta$ (integer $\beta \ge 1$): for every $(U, M) \in \mathrm{supp}(\mathcal{D})$ and all $u, v \in V$, $d_G^{(\beta \cdot h)}(u, v) \le d_U(u, v)$ in $[0, \infty]$.
     - **worst-case distortion** $K$ (real $K \ge 1$): for every $(U, M) \in \mathrm{supp}(\mathcal{D})$, every $u \in M$, and every $v \in V$, $d_U(u, v) \le K \cdot d_G^{(h)}(u, v)$ in $[0, \infty]$ (with $K \cdot 0 = 0$ and $K \cdot \infty = \infty$).
     - **exclusion probability** $\varepsilon$: for every $v \in V$, $\Pr_{(U, M) \sim \mathcal{D}}[v \notin M] \le \varepsilon$.
     - **expected distortion** $\alpha$ (real $\alpha \ge 1$): for all $u, v \in V$, defining $d_{U, M}(u, v) = d_U(u, v)$ when $u \in M \land v \in M$ and $d_{U, M}(u, v) = 0$ otherwise (even when $d_U(u, v) = \infty$), $\mathbb{E}_{(U, M) \sim \mathcal{D}}[d_{U, M}(u, v)] \le \alpha \cdot d_G^{(h)}(u, v)$ in $[0, \infty]$.

5. **Stochastic and deterministic Ramsey-type tree embeddings (Section 5.2 and Section 5.3)**:
   - For a finite connected unweighted simple graph $G = (V, E)$, a stochastic Ramsey-type embedding of $G$ into finite weighted trees with exclusion probability $\varepsilon$ and expected distortion $\alpha \ge 0$ is a finite-support probability distribution $\mathcal{D}$ over triples $(T, f, M)$, where $T$ is a finite weighted tree, $M \subseteq V$, and $f : V \to V(T)$ satisfies $\forall u, v \in V,\; d_G(u, v) \le d_T(f(u), f(v))$, such that $\forall v \in V,\; \Pr_{(T, f, M) \sim \mathcal{D}}[v \notin M] \le \varepsilon$ and $\forall u, v \in V,\; \mathbb{E}_{(T, f, M) \sim \mathcal{D}}[d_{T, M}(u, v)] \le \alpha \cdot d_G(u, v)$, where $d_{T, M}(u, v) = d_T(f(u), f(v))$ if $u \in M \land v \in M$ and $0$ otherwise.
   - Given $M \subseteq V$ and real $t \ge 1$, a dominating Ramsey-type embedding of $G$ on saved set $M$ into a finite weighted tree $T$ with distortion $t$ is a map $f : M \to V(T)$ satisfying $\forall u, v \in M,\; d_G(u, v) \le d_T(f(u), f(v)) \le t \cdot d_G(u, v)$.

# Theorems to Formalize and Prove (`trees_with_benefits`: Conjunction of Theorems 1–4)
1. **Theorem 1 (Sections 3–4, Upper Bound)**:
   For every real polynomial-weight exponent $c_0 \ge 1$, there exist constants $C \ge 1$ and $d \in \mathbb{N}$ (depending only on $c_0$, independent of $n, G, w, h, \varepsilon$) such that for every integer $n \ge 2$, every $n$-vertex undirected simple graph $G = (V, E, w)$ whose edge weights satisfy $1 \le w(e) \le n^{c_0}$ for all $e \in E$, every integer hop parameter $h \in \{1, \dots, n\}$, and every real $\varepsilon \in (0, 1)$, there exist an integer $\beta \ge 1$, reals $K \ge 1$ and $\alpha \ge 1$, and a stochastic hop-constrained Ramsey-type embedding $\mathcal{D}$ of $G$ into HSTs with hop parameter $h$, exclusion probability $\varepsilon$, hop-stretch $\beta$, worst-case distortion $K$, and expected distortion $\alpha$ satisfying:
   - $\beta \le \varepsilon^{-1} \cdot C \cdot \log_2 n \cdot (\log_2(\log_2 n + 2))^d$,
   - $K \le \varepsilon^{-1} \cdot C \cdot \log_2 n \cdot (\log_2(\log_2 n + 2))^d$, and
   - $\alpha \le C \cdot \log_2 n \cdot (\log_2(\log_2 n + 2))^d$.

2. **Theorem 2 (Section 5.1, Hop-Stretch Lower Bound)**:
   There exist absolute constants $c > 0$ and $\varepsilon_0 \in (0, 1)$ such that for every real $\varepsilon \in (0, \varepsilon_0]$ and every integer $N_0 \ge 1$, there exists a finite unweighted undirected simple graph $G = (V, E)$ on $N = |V| \ge N_0$ vertices with $\varepsilon N \ge 2$ such that for every extended metric space $(X, d_X)$, every mapping $f : V \to X$, every saved subset $M \subseteq V$ with $|V \setminus M| \le \varepsilon N$, every finite real distortion $t \ge 1$, and every integer hop-stretch $\beta \ge 1$: if (i) $\forall u, v \in V,\; d_G^{(\beta)}(u, v) \le d_X(f(u), f(v))$ in $[0, \infty]$ and (ii) $\forall u \in M,\; \forall v \in V,\; d_X(f(u), f(v)) \le t \cdot d_G^{(1)}(u, v)$ in $[0, \infty]$ (with $t \cdot 0 = 0$ and $t \cdot \infty = \infty$), then $\beta \ge c \cdot \varepsilon^{-1} \cdot \log_2(\varepsilon N)$.

3. **Theorem 3 (Section 5.2, Expected Distortion Lower Bound)**:
   There exist absolute constants $c > 0$ and $\varepsilon_0 \in (0, 1)$ such that for every real $\varepsilon \in (0, \varepsilon_0]$ and every integer $N_0 \ge 2$, there exists a finite connected unweighted undirected simple graph $G = (V, E)$ on $n = |V| \ge N_0$ vertices such that for every stochastic Ramsey-type embedding $\mathcal{D}$ of $G$ into finite weighted trees with exclusion probability $\varepsilon$ and expected distortion $\alpha \ge 0$, $\alpha \ge c \cdot \log_2 n$.

4. **Theorem 4 (Section 5.3, Ramsey Tree Distortion Lower Bound)**:
   There exist absolute constants $c > 0$ and $\varepsilon_0 \in (0, 1)$ such that for every real $\varepsilon \in (0, \varepsilon_0]$ and every integer $N_0 \ge 2$, there exists a finite connected unweighted undirected simple graph $G = (V, E)$ on $N = |V| \ge N_0$ vertices with $\varepsilon N \ge 2$ such that for every saved subset $M \subseteq V$ with $|V \setminus M| \le \varepsilon N$, every finite weighted tree $T$, every real $t \ge 1$, and every dominating Ramsey-type embedding $f : M \to V(T)$ of $G$ on saved set $M$ into $T$ with distortion $t$, $t \ge c \cdot \varepsilon^{-1} \cdot \log_2(\varepsilon N)$.
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

theorem trees_with_benefits : Theorem1 ∧ Theorem2 ∧ Theorem3 ∧ Theorem4 := by
  sorry
