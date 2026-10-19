import HigherDimLFPP.Lower.Triples
import HigherDimLFPP.Lower.Glue
import HigherDimLFPP.Lower.ClassC

/-!
# Decision trees, the recursive construction and its polygons (lower comparison, §5.3)

Packet P-L2a, target T2 (ruling H6; audit HA4, "Details for later use" D7, "Construction" and
"Measurability").

* `lamax`: the least index attaining the maximum (the selector (5.7) is the least argmax of a
  selection statistic), and the measurability of its level sets (`measurableSet_lamax_eq`).
* `DT J K k`: decision trees of depth `k`: `DT₀ = {∗}`, `DT_{k+1} = [J+1] × DT_k^K`.  Finite,
  with the discrete σ-algebra.
* `LParams`: the data of the construction: the number `J + 1` of profiles, `K` edges per
  replacement polygon, the Riemann parameter `N`, `ζ`, `ρ`, the common edge length `q`, the
  vertices `v j` of the replacement polygons, and a **selection statistic** `stat j` reading
  the root band field `z ↦ Y(ρq, ρ, z)` at the finitely many points of `R` (kept abstract: the
  specific statistic (5.7) is plugged in later).
* `T j i = edgeSim q (v j) i`: the edge similarities (ratio `q`, orthogonal frame with
  `O e₁ =` edge direction, P-L1); `sel Y = lamax (stat · (rootField Y))`: the selector.
* `dec k Y`: the rule, `dec₀ Y = ∗`, `dec_{k+1} Y = (I(Y), i ↦ dec_k(Y ∘ τ_{T_i^{I(Y)}}))`.
  The selection at a depth-`m` node reads `Y(ρq^{m+1}, ρq^m, S_node(·))`, with `S_node` the
  composite similarity of the node (`tau_comp`, recursive frames `O_child = O_parent ∘ O_local`).
* `polyOf k t`: the polygon of a tree: `poly₀ = [0, e₁]`, `poly_{k+1}(j, c) =` concatenation over
  `i` of `T_i^j(poly_k(c_i))`.  `Good.edges_polyOf`: its edges are `S([0, e₁])` for composite
  similarities `S ∈ compSims k` (ratio `q^k`); `Good.polyOf_ends`: it runs from `0` to `e₁`;
  `Good.mem_polyOf_of_mapsTo`: its vertices stay in every set mapped into itself by all `T_i^j`.
* `S k`: the Riemann points of depth `k` (`S 0 = refSet N`, `S (k+1) = stepPts (S k)`), and
  `Good.riemannPts_polyOf_subset`.
* `Qs k`: the finite set of triples read at depth `k`; `Good.Qs_band`: all lie in the band
  `[ρ q^k, ρ]`.
* **Locality and measurability**: `Good.dec_loc` (`dec k` reads only `Qs k`) and
  `Good.measurable_dec` (measurable into the finite type `DT J K k`).

2D source: `LQGDimension/LFPP/BlockConstructionAux4.lean` (`amin`, `measurableSet_amin_eq`,
`DT`, `BParams`, `sim`, `rr`, `tau`, `Lsim`, `S`, `Qs`, `polyOf`, `dec`, `Good`) and
`BlockConstructionAux5.lean` (`measurable_dec`, `Good.dec_loc`).  Changes: the rule selects by a
statistic of the root band (5.7) instead of minimizing the block cost against the expected
occupation; similarities are `SimD` with orthogonal frames composed recursively; all edges have
ratio `q`, so a single scale `ρ q^k` indexes depth `k`; there are no unused bands.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

/-! ## The least argmax -/

theorem lamax_ne {J : ℕ} (g : Fin (J + 1) → ℝ) :
    (Finset.univ.filter fun j => ∀ k, g k ≤ g j).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k => hj k (Finset.mem_univ _)⟩⟩

/-- The least index attaining the maximum of `g`. -/
def lamax {J : ℕ} (g : Fin (J + 1) → ℝ) : Fin (J + 1) :=
  (Finset.univ.filter fun j => ∀ k, g k ≤ g j).min' (lamax_ne g)

theorem le_lamax {J : ℕ} (g : Fin (J + 1) → ℝ) (k : Fin (J + 1)) : g k ≤ g (lamax g) :=
  (Finset.mem_filter.1 (Finset.min'_mem _ (lamax_ne g))).2 k

theorem lamax_eq_iff {J : ℕ} (g : Fin (J + 1) → ℝ) (j : Fin (J + 1)) :
    lamax g = j ↔ (∀ k, g k ≤ g j) ∧ ∀ k, (∀ l, g l ≤ g k) → j ≤ k := by
  constructor
  · rintro rfl
    exact ⟨le_lamax g, fun k hk =>
      Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)⟩
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
    · exact h2 _ (le_lamax g)

theorem iSup_eq_lamax {J : ℕ} (g : Fin (J + 1) → ℝ) : ⨆ j, g j = g (lamax g) :=
  le_antisymm (ciSup_le (le_lamax g)) (le_ciSup (Finite.bddAbove_range g) _)

theorem measurableSet_lamax_eq {α : Type*} [MeasurableSpace α] {J : ℕ}
    (G : Fin (J + 1) → α → ℝ) (hG : ∀ j, Measurable (G j)) (j₀ : Fin (J + 1)) :
    MeasurableSet {x | lamax (fun j => G j x) = j₀} := by
  have hset : ∀ k, MeasurableSet {x | ∀ l, G l x ≤ G k x} := by
    intro k
    have : {x | ∀ l, G l x ≤ G k x} = ⋂ l, {x | G l x ≤ G k x} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun l => measurableSet_le (hG l) (hG k)
  have : {x | lamax (fun j => G j x) = j₀} =
      {x | ∀ l, G l x ≤ G j₀ x} ∩ ⋂ k, ({x | ∀ l, G l x ≤ G k x}ᶜ ∪ {_x | j₀ ≤ k}) := by
    ext x
    simp only [mem_ofPred_eq, lamax_eq_iff, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun k => ?_⟩
      by_cases hk : ∀ l, G l x ≤ G k x
      · exact Or.inr (h2 k hk)
      · exact Or.inl hk
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun k hk => (h2 k).resolve_left (not_not.2 hk)⟩
  rw [this]
  refine (hset j₀).inter (MeasurableSet.iInter fun k => (hset k).compl.union ?_)
  by_cases h : j₀ ≤ k
  · simp [h]
  · simp [h]

theorem measurable_lamax {α : Type*} [MeasurableSpace α] {J : ℕ} (G : Fin (J + 1) → α → ℝ)
    (hG : ∀ j, Measurable (G j)) : Measurable fun x => lamax fun j => G j x :=
  measurable_to_countable' fun j₀ => measurableSet_lamax_eq G hG j₀

/-! ## Decision trees -/

/-- Decision trees of depth `k`: a choice among `J + 1` profiles at the root and a depth-`k-1`
tree in each of the `K` children. -/
def DT (J K : ℕ) : ℕ → Type
  | 0 => Unit
  | k + 1 => Fin (J + 1) × (Fin K → DT J K k)

instance instFintypeDT (J K : ℕ) : ∀ k, Fintype (DT J K k)
  | 0 => (inferInstance : Fintype Unit)
  | k + 1 => by
    haveI := instFintypeDT J K k
    exact (inferInstance : Fintype (Fin (J + 1) × (Fin K → DT J K k)))

instance instMeasurableSpaceDT (J K k : ℕ) : MeasurableSpace (DT J K k) := ⊤

instance instMeasurableSingletonClassDT (J K k : ℕ) : MeasurableSingletonClass (DT J K k) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The depth-`0` tree. -/
def DT.leaf {J K : ℕ} : DT J K 0 := ()

/-- A tree from its root choice and its children. -/
def DT.mk {J K k : ℕ} (j : Fin (J + 1)) (c : Fin K → DT J K k) : DT J K (k + 1) := (j, c)

/-- The root choice of a tree. -/
def DT.fst {J K k : ℕ} (t : DT J K (k + 1)) : Fin (J + 1) :=
  (t : Fin (J + 1) × (Fin K → DT J K k)).1

/-- The children of a tree. -/
def DT.snd {J K k : ℕ} (t : DT J K (k + 1)) : Fin K → DT J K k :=
  (t : Fin (J + 1) × (Fin K → DT J K k)).2

@[simp] theorem DT.fst_mk {J K k : ℕ} (j : Fin (J + 1)) (c : Fin K → DT J K k) :
    (DT.mk j c).fst = j := rfl

@[simp] theorem DT.snd_mk {J K k : ℕ} (j : Fin (J + 1)) (c : Fin K → DT J K k) :
    (DT.mk j c).snd = c := rfl

theorem DT.eta {J K k : ℕ} (t : DT J K (k + 1)) : DT.mk t.fst t.snd = t := rfl

theorem DT.ext_iff' {J K k : ℕ} (t t' : DT J K (k + 1)) :
    t = t' ↔ t.fst = t'.fst ∧ t.snd = t'.snd := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← DT.eta t, ← DT.eta t', h1, h2]

/-! ## Parameters -/

variable {d : ℕ}

/-- Data of the depth-`k` construction of the lower comparison (source §5.3). -/
structure LParams (d : ℕ) where
  /-- `J + 1` replacement polygons (profiles). -/
  J : ℕ
  /-- Number of edges of each replacement polygon (`K = 2^{n+g}`). -/
  K : ℕ
  /-- Riemann parameter: `N` left Riemann points per edge. -/
  N : ℕ
  /-- The coupling constant `ζ = δ^{3/2}`. -/
  ζ : ℝ
  /-- Top of the root band, `ρ = δ L`. -/
  ρ : ℝ
  /-- Common edge length `q = s/K` of the replacement polygons. -/
  q : ℝ
  /-- Vertices of the replacement polygons. -/
  v : Fin (J + 1) → ℕ → Rd d
  /-- The finitely many points at which the selection statistic reads the root band. -/
  R : Finset (Rd d)
  /-- The selection statistic, a function of the root band field `z ↦ Y(ρq, ρ, z)`. -/
  stat : Fin (J + 1) → (Rd d → ℝ) → ℝ

namespace LParams

variable (P : LParams d)

/-- The edge similarity `T_i^j` (ratio `q`, frame `O e₁ =` direction of edge `i` of `v j`). -/
def T (j : Fin (P.J + 1)) (i : ℕ) : SimD d := edgeSim P.q (P.v j) i

theorem T_r (j : Fin (P.J + 1)) (i : ℕ) : (P.T j i).r = P.q := rfl

theorem T_app_zero (j : Fin (P.J + 1)) (i : ℕ) : (P.T j i).app 0 = P.v j i :=
  edgeSim_app_zero _ _ _

/-- The root band field `z ↦ Y(ρq, ρ, z)`. -/
def rootField (Y : TriD d → ℝ) : Rd d → ℝ := fun z => Y (P.ρ * P.q, P.ρ, z)

/-- **The selector** (5.7): the least index maximizing the selection statistic of the root
band. -/
def sel (Y : TriD d → ℝ) : Fin (P.J + 1) := lamax fun j => P.stat j (P.rootField Y)

/-- **The rule** `dec_k`: at the root, select `I(Y)`; in child `i`, run the depth-`k` rule on
the field `Y ∘ τ_{T_i^{I(Y)}}` (the finer bands in the child's coordinates). -/
def dec : (k : ℕ) → (TriD d → ℝ) → DT P.J P.K k
  | 0, _ => DT.leaf
  | k + 1, Y => DT.mk (P.sel Y) fun i => dec k fun t => Y (tau (P.T (P.sel Y) i) t)

theorem dec_succ (k : ℕ) (Y : TriD d → ℝ) :
    P.dec (k + 1) Y = DT.mk (P.sel Y) fun i => P.dec k fun t => Y (tau (P.T (P.sel Y) i) t) :=
  rfl

/-- The polygon of a decision tree: `poly₀ = [0, e₁]`, and `poly_{k+1}(j, c)` is the
concatenation over the edges `i` of `T_i^j(poly_k(c_i))`. -/
def polyOf : (k : ℕ) → DT P.J P.K k → List (Rd d)
  | 0, _ => [0, e₁ d]
  | k + 1, t => glueFn P.K fun i => (polyOf k (t.snd i)).map (P.T t.fst i).app

/-- The composite similarities `T_{i₁}^{j₁} ∘ ⋯ ∘ T_{i_k}^{j_k}` of depth `k`. -/
def compSims : ℕ → Set (SimD d)
  | 0 => {SimD.id}
  | k + 1 => {S | ∃ j, ∃ i < P.K, ∃ L ∈ compSims k, S = (P.T j i).comp L}

/-- `stepPts Sμ = ⋃_{j, i < K} T_i^j(Sμ)`: the support of the replaced measures `ν_{j,μ}`. -/
def stepPts (Sμ : Finset (Rd d)) : Finset (Rd d) :=
  Finset.univ.biUnion fun j => (Finset.range P.K).biUnion fun i => Sμ.image (P.T j i).app

/-- The Riemann points of depth `k`: `S 0 = {(l/N) e₁ : l < N}`, `S (k+1) = stepPts (S k)`. -/
def S : ℕ → Finset (Rd d)
  | 0 => refSet P.N
  | k + 1 => P.stepPts (S k)

theorem S_succ (k : ℕ) : P.S (k + 1) = P.stepPts (P.S k) := rfl

/-- The root-band triples `(ρq, ρ, z)`, `z ∈ R ∪ stepPts Sμ`, read by one replacement step
(the selection and the coarse factor `e^{ζ Y(ρq, ρ, ·)}`). -/
def stepTris (Sμ : Finset (Rd d)) : Finset (TriD d) :=
  (P.R ∪ P.stepPts Sμ).image fun z => (P.ρ * P.q, P.ρ, z)

/-- The cost-band triples `(ρ q^k, ρ, p)`, `p ∈ S k`. -/
def costTris (k : ℕ) : Finset (TriD d) := (P.S k).image fun p => (P.ρ * P.q ^ k, P.ρ, p)

/-- The triples of the children: `τ_{T_i^j}(Qs k)`. -/
def childTris (Q : Finset (TriD d)) : Finset (TriD d) :=
  Finset.univ.biUnion fun j => (Finset.range P.K).biUnion fun i => Q.image (tau (P.T j i))

/-- The finite set of triples read at depth `k` (by the rule and by the cost band). -/
def Qs : ℕ → Finset (TriD d)
  | 0 => P.costTris 0
  | k + 1 => P.stepTris (P.S k) ∪ P.childTris (Qs k) ∪ P.costTris (k + 1)

/-! ## Standing hypotheses -/

/-- Standing hypotheses on the parameters: positive scales, `q ≤ 1`, `K, N ≥ 1`, polygons from
`0` to `e₁` with all edges of length `q`, and a measurable statistic reading only `R`. -/
structure Good : Prop where
  d_pos : 0 < d
  K_pos : 0 < P.K
  N_pos : 0 < P.N
  ρ_pos : 0 < P.ρ
  q_pos : 0 < P.q
  q_le_one : P.q ≤ 1
  start : ∀ j, P.v j 0 = 0
  finish : ∀ j, P.v j P.K = e₁ d
  edge_len : ∀ j, ∀ i < P.K, ‖P.v j (i + 1) - P.v j i‖ = P.q
  stat_meas : ∀ j, Measurable (P.stat j)
  stat_loc : ∀ j, ∀ φ φ' : Rd d → ℝ, (∀ z ∈ P.R, φ z = φ' z) → P.stat j φ = P.stat j φ'

variable {P}

/-- The standing hypotheses from P-L1's equal-edge polygons (`EqualEdgeData`, Lemma 5.1). -/
theorem Good.of_equalEdgeData (hd : 0 < d) (hK : 0 < P.K) (hN : 0 < P.N) (hρ : 0 < P.ρ)
    (hq : 0 < P.q) (hq1 : P.q ≤ 1) {δ E₀ M₀ c : ℝ}
    (hE : ∀ j, EqualEdgeData P.K δ P.q E₀ M₀ c (P.v j)) (hstat : ∀ j, Measurable (P.stat j))
    (hloc : ∀ j, ∀ φ φ' : Rd d → ℝ, (∀ z ∈ P.R, φ z = φ' z) → P.stat j φ = P.stat j φ') :
    P.Good where
  d_pos := hd
  K_pos := hK
  N_pos := hN
  ρ_pos := hρ
  q_pos := hq
  q_le_one := hq1
  start j := (hE j).start
  finish j := (hE j).finish
  edge_len j := (hE j).edge_len
  stat_meas := hstat
  stat_loc := hloc

theorem Good.T_app_e₁ (hP : P.Good) (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) :
    (P.T j i).app (e₁ d) = P.v j (i + 1) :=
  edgeSim_app_e₁ hP.d_pos hP.q_pos (hP.edge_len j i hi)

theorem Good.q_pow_pos (hP : P.Good) (k : ℕ) : 0 < P.q ^ k := pow_pos hP.q_pos k

theorem Good.q_pow_le_one (hP : P.Good) (k : ℕ) : P.q ^ k ≤ 1 :=
  pow_le_one₀ hP.q_pos.le hP.q_le_one

theorem Good.rho_q_pow_pos (hP : P.Good) (k : ℕ) : 0 < P.ρ * P.q ^ k :=
  mul_pos hP.ρ_pos (hP.q_pow_pos k)

theorem Good.rho_q_pow_le (hP : P.Good) (k : ℕ) : P.ρ * P.q ^ k ≤ P.ρ :=
  mul_le_of_le_one_right hP.ρ_pos.le (hP.q_pow_le_one k)

theorem Good.rho_q_pos (hP : P.Good) : 0 < P.ρ * P.q := mul_pos hP.ρ_pos hP.q_pos

theorem Good.rho_q_le (hP : P.Good) : P.ρ * P.q ≤ P.ρ :=
  mul_le_of_le_one_right hP.ρ_pos.le hP.q_le_one

/-- `ρ q^{k+1} ≤ ρ q`. -/
theorem Good.rho_q_pow_succ_le (hP : P.Good) (k : ℕ) : P.ρ * P.q ^ (k + 1) ≤ P.ρ * P.q := by
  rw [pow_succ, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hP.rho_q_pow_le k) hP.q_pos.le

/-! ## Polygons: endpoints, junctions, edges -/

theorem glueFn_head?_of_pos {α : Type*} (m : ℕ) (hm : 0 < m) (f : Fin m → List α)
    (h0 : f ⟨0, hm⟩ ≠ []) : (glueFn m f).head? = (f ⟨0, hm⟩).head? := by
  cases m with
  | zero => omega
  | succ m => exact head?_glueFn m f h0

theorem glueFn_getLast?_of_pos {α : Type*} (m : ℕ) (hm : 0 < m) (f : Fin m → List α)
    (hne : ∀ i, f i ≠ []) (hJ : Junction m f) :
    (glueFn m f).getLast? = (f ⟨m - 1, by omega⟩).getLast? := by
  cases m with
  | zero => omega
  | succ m => exact getLast?_glueFn m f hne hJ

/-- **Endpoints**: every polygon runs from `0` to `e₁`. -/
theorem Good.polyOf_ends (hP : P.Good) :
    ∀ k (t : DT P.J P.K k), (P.polyOf k t).head? = some 0 ∧
      (P.polyOf k t).getLast? = some (e₁ d)
  | 0, _ => by simp [polyOf]
  | k + 1, t => by
    have ih := Good.polyOf_ends hP k
    have hne : ∀ i : Fin P.K, (P.polyOf k (t.snd i)).map (P.T t.fst i).app ≠ [] := by
      intro i hc
      have := (ih (t.snd i)).1
      rw [List.map_eq_nil_iff] at hc
      rw [hc] at this
      simp at this
    have hJ : Junction P.K fun i => (P.polyOf k (t.snd i)).map (P.T t.fst i).app := by
      intro i hi
      rw [List.getLast?_map, List.head?_map, (ih _).2, (ih _).1]
      simp only [Option.map_some]
      rw [hP.T_app_e₁ _ (by omega : i < P.K), T_app_zero]
    simp only [polyOf]
    refine ⟨?_, ?_⟩
    · rw [glueFn_head?_of_pos P.K hP.K_pos _ (hne _), List.head?_map, (ih _).1,
        Option.map_some, T_app_zero, hP.start]
    · rw [glueFn_getLast?_of_pos P.K hP.K_pos _ hne hJ, List.getLast?_map, (ih _).2,
        Option.map_some, hP.T_app_e₁ _ (by simpa using Nat.sub_lt hP.K_pos one_pos),
        Nat.sub_add_cancel hP.K_pos, hP.finish]

theorem Good.polyOf_ne_nil (hP : P.Good) (k : ℕ) (t : DT P.J P.K k) : P.polyOf k t ≠ [] := by
  intro h
  have := (hP.polyOf_ends k t).1
  rw [h] at this
  simp at this

theorem Good.junction (hP : P.Good) (k : ℕ) (t : DT P.J P.K (k + 1)) :
    Junction P.K fun i => (P.polyOf k (t.snd i)).map (P.T t.fst i).app := by
  intro i hi
  rw [List.getLast?_map, List.head?_map, (hP.polyOf_ends k _).2, (hP.polyOf_ends k _).1]
  simp only [Option.map_some]
  rw [hP.T_app_e₁ _ (by omega : i < P.K), T_app_zero]

theorem Good.pieces_ne_nil (hP : P.Good) (k : ℕ) (t : DT P.J P.K (k + 1)) (i : Fin P.K) :
    (P.polyOf k (t.snd i)).map (P.T t.fst i).app ≠ [] := by
  rw [Ne, List.map_eq_nil_iff]
  exact hP.polyOf_ne_nil k _

theorem T_comp_mem_compSims {k : ℕ} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {L : SimD d}
    (hL : L ∈ P.compSims k) : (P.T j i).comp L ∈ P.compSims (k + 1) :=
  ⟨j, i, hi, L, hL, rfl⟩

/-- Composite similarities of depth `k` have ratio `q^k`. -/
theorem compSims_r : ∀ {k : ℕ} {L : SimD d}, L ∈ P.compSims k → L.r = P.q ^ k
  | 0, L, hL => by
    rw [show L = SimD.id from hL]
    simp [SimD.id]
  | k + 1, _, ⟨j, i, _, L, hL, rfl⟩ => by
    rw [SimD.comp_r, T_r, compSims_r hL, pow_succ']

/-- **Recursive frames**: the root band read in the coordinates of a depth-`m` composite
similarity `L` (ratio `q^m`) is the band `(ρ q^{m+1}, ρ q^m]` at `L z`; so the selection at a
depth-`m` node reads `Y(ρq^{m+1}, ρq^m, S_node(·))`. -/
theorem tau_root_of_mem_compSims {m : ℕ} {L : SimD d} (hL : L ∈ P.compSims m) (z : Rd d) :
    tau L (P.ρ * P.q, P.ρ, z) = (P.ρ * P.q ^ (m + 1), P.ρ * P.q ^ m, L.app z) := by
  rw [tau_mk, compSims_r hL]
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · simp only
    ring
  · simp only
    ring

/-- The field of a grandchild is the field pulled back by the composite similarity. -/
theorem comp_tau_eq (Y : TriD d → ℝ) (S T : SimD d) :
    (fun t => (fun s => Y (tau S s)) (tau T t)) = fun t => Y (tau (S.comp T) t) := by
  funext t
  simp only [tau_comp]

/-- Composite similarities map every set mapped into itself by all edge similarities into
itself (Lemma 5.3 (i) along the recursion). -/
theorem compSims_mapsTo {V : Set (Rd d)} (hV : ∀ j, ∀ i < P.K, MapsTo (P.T j i).app V V) :
    ∀ {k : ℕ} {L : SimD d}, L ∈ P.compSims k → MapsTo L.app V V
  | 0, L, hL => by
    rw [show L = SimD.id from hL]
    intro z hz
    rwa [SimD.app_id]
  | k + 1, _, ⟨j, i, hi, L, hL, rfl⟩ => by
    intro z hz
    rw [SimD.app_comp]
    exact hV j i hi (compSims_mapsTo hV hL hz)

/-- **Leaf edges**: the edges of a depth-`k` polygon are the images `S([0, e₁])` of the unit
segment under composite similarities `S ∈ compSims k`. -/
theorem Good.edges_polyOf (hP : P.Good) :
    ∀ k (t : DT P.J P.K k), ∀ e ∈ edges (P.polyOf k t),
      ∃ L ∈ P.compSims k, e = (L.app 0, L.app (e₁ d))
  | 0, _, e, he => by
    simp only [polyOf, edges_cons_cons, edges_single, List.mem_singleton] at he
    refine ⟨SimD.id, rfl, ?_⟩
    rw [he, SimD.app_id, SimD.app_id]
  | k + 1, t, e, he => by
    simp only [polyOf] at he
    obtain ⟨i, hi⟩ := mem_edges_glueFn P.K _ (hP.pieces_ne_nil k t) (hP.junction k t) e he
    rw [edges_map, List.mem_map] at hi
    obtain ⟨e', he', rfl⟩ := hi
    obtain ⟨L, hL, rfl⟩ := Good.edges_polyOf hP k _ e' he'
    exact ⟨(P.T t.fst i).comp L, T_comp_mem_compSims _ i.2 hL,
      by simp only [SimD.app_comp]⟩

/-- **Vertices**: every vertex of a depth-`k` polygon is `S 0` or `S e₁` for a composite
similarity `S ∈ compSims k`. -/
theorem Good.mem_polyOf (hP : P.Good) :
    ∀ k (t : DT P.J P.K k), ∀ z ∈ P.polyOf k t,
      ∃ L ∈ P.compSims k, z = L.app 0 ∨ z = L.app (e₁ d)
  | 0, _, z, hz => by
    simp only [polyOf, List.mem_cons, List.not_mem_nil, or_false] at hz
    refine ⟨SimD.id, rfl, ?_⟩
    rcases hz with rfl | rfl
    · left
      rw [SimD.app_id]
    · right
      rw [SimD.app_id]
  | k + 1, t, z, hz => by
    simp only [polyOf] at hz
    obtain ⟨i, hi⟩ := mem_glueFn P.K _ z hz
    rw [List.mem_map] at hi
    obtain ⟨z', hz', rfl⟩ := hi
    obtain ⟨L, hL, h⟩ := Good.mem_polyOf hP k _ z' hz'
    refine ⟨(P.T t.fst i).comp L, T_comp_mem_compSims _ i.2 hL, ?_⟩
    rcases h with rfl | rfl
    · left
      rw [SimD.app_comp]
    · right
      rw [SimD.app_comp]

/-- If every edge similarity maps `V` into itself and `0, e₁ ∈ V`, all vertices of all
polygons lie in `V` (with `V = V_δ ⊆ U`, the polygons are admissible). -/
theorem Good.mem_polyOf_of_mapsTo (hP : P.Good) {V : Set (Rd d)}
    (hV : ∀ j, ∀ i < P.K, MapsTo (P.T j i).app V V) (h0 : (0 : Rd d) ∈ V) (h1 : e₁ d ∈ V)
    (k : ℕ) (t : DT P.J P.K k) : ∀ z ∈ P.polyOf k t, z ∈ V := by
  intro z hz
  obtain ⟨L, hL, h⟩ := hP.mem_polyOf k t z hz
  rcases h with rfl | rfl
  · exact compSims_mapsTo hV hL h0
  · exact compSims_mapsTo hV hL h1

/-- The edges of a depth-`k` polygon have length `q^k`. -/
theorem Good.norm_edge_polyOf (hP : P.Good) (k : ℕ) (t : DT P.J P.K k) (e : Rd d × Rd d)
    (he : e ∈ edges (P.polyOf k t)) : ‖e.2 - e.1‖ = P.q ^ k := by
  obtain ⟨L, hL, rfl⟩ := hP.edges_polyOf k t e he
  rw [SimD.norm_app_sub, sub_zero, norm_e₁ hP.d_pos, mul_one, compSims_r hL,
    abs_of_pos (hP.q_pow_pos k)]

/-! ## Riemann points -/

theorem mem_stepPts {Sμ : Finset (Rd d)} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {z : Rd d}
    (hz : z ∈ Sμ) : (P.T j i).app z ∈ P.stepPts Sμ := by
  simp only [stepPts, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range, Finset.mem_image,
    true_and]
  exact ⟨j, i, hi, z, hz, rfl⟩

theorem mem_stepPts_iff {Sμ : Finset (Rd d)} {p : Rd d} :
    p ∈ P.stepPts Sμ ↔ ∃ j, ∃ i < P.K, ∃ z ∈ Sμ, (P.T j i).app z = p := by
  simp only [stepPts, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range, Finset.mem_image,
    true_and]

theorem mem_S_succ {k : ℕ} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {z : Rd d}
    (hz : z ∈ P.S k) : (P.T j i).app z ∈ P.S (k + 1) :=
  mem_stepPts j hi hz

/-- The Riemann points of every depth-`k` polygon lie in `S k`. -/
theorem Good.riemannPts_polyOf_subset (hP : P.Good) :
    ∀ k (t : DT P.J P.K k), riemannPts P.N (P.polyOf k t) ⊆ ↑(P.S k)
  | 0, _ => by
    rintro p ⟨e, he, l, hl, rfl⟩
    simp only [polyOf, edges_cons_cons, edges_single, List.mem_singleton] at he
    subst he
    simp only [S, refSet, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
    exact ⟨l, hl, by simp [refPt]⟩
  | k + 1, t => by
    rintro p ⟨e, he, l, hl, rfl⟩
    simp only [polyOf] at he
    obtain ⟨i, hi⟩ := mem_edges_glueFn P.K _ (hP.pieces_ne_nil k t) (hP.junction k t) e he
    rw [edges_map, List.mem_map] at hi
    obtain ⟨e', he', rfl⟩ := hi
    have hmem := Good.riemannPts_polyOf_subset hP k (t.snd i) ⟨e', he', l, hl, rfl⟩
    simp only
    rw [← SimD.app_add_smul_sub]
    exact mem_S_succ _ i.2 hmem

/-! ## Triples -/

theorem mem_stepTris_of_R {Sμ : Finset (Rd d)} {z : Rd d} (hz : z ∈ P.R) :
    (P.ρ * P.q, P.ρ, z) ∈ P.stepTris Sμ :=
  Finset.mem_image_of_mem _ (Finset.mem_union_left _ hz)

theorem mem_stepTris_of_stepPts {Sμ : Finset (Rd d)} {z : Rd d} (hz : z ∈ P.stepPts Sμ) :
    (P.ρ * P.q, P.ρ, z) ∈ P.stepTris Sμ :=
  Finset.mem_image_of_mem _ (Finset.mem_union_right _ hz)

theorem mem_stepTris_iff {Sμ : Finset (Rd d)} {t : TriD d} :
    t ∈ P.stepTris Sμ ↔ ∃ z ∈ P.R ∪ P.stepPts Sμ, (P.ρ * P.q, P.ρ, z) = t :=
  Finset.mem_image

theorem mem_costTris {k : ℕ} {p : Rd d} (hp : p ∈ P.S k) :
    (P.ρ * P.q ^ k, P.ρ, p) ∈ P.costTris k :=
  Finset.mem_image_of_mem _ hp

theorem mem_childTris {Q : Finset (TriD d)} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K)
    {t : TriD d} (ht : t ∈ Q) : tau (P.T j i) t ∈ P.childTris Q := by
  simp only [childTris, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range, Finset.mem_image,
    true_and]
  exact ⟨j, i, hi, t, ht, rfl⟩

theorem stepTris_subset_Qs (k : ℕ) : P.stepTris (P.S k) ⊆ P.Qs (k + 1) := fun _ ht =>
  Finset.mem_union_left _ (Finset.mem_union_left _ ht)

theorem childTris_subset_Qs (k : ℕ) : P.childTris (P.Qs k) ⊆ P.Qs (k + 1) := fun _ ht =>
  Finset.mem_union_left _ (Finset.mem_union_right _ ht)

theorem costTris_subset_Qs : ∀ k, P.costTris k ⊆ P.Qs k
  | 0 => le_rfl
  | _ + 1 => fun _ ht => Finset.mem_union_right _ ht

theorem mem_Qs_cost {k : ℕ} {p : Rd d} (hp : p ∈ P.S k) : (P.ρ * P.q ^ k, P.ρ, p) ∈ P.Qs k :=
  costTris_subset_Qs k (mem_costTris hp)

theorem mem_Qs_tau {k : ℕ} (j : Fin (P.J + 1)) {i : ℕ} (hi : i < P.K) {t : TriD d}
    (ht : t ∈ P.Qs k) : tau (P.T j i) t ∈ P.Qs (k + 1) :=
  childTris_subset_Qs k (mem_childTris j hi ht)

theorem mem_Qs_root_R {k : ℕ} {z : Rd d} (hz : z ∈ P.R) : (P.ρ * P.q, P.ρ, z) ∈ P.Qs (k + 1) :=
  stepTris_subset_Qs k (mem_stepTris_of_R hz)

theorem mem_Qs_root {k : ℕ} {z : Rd d} (hz : z ∈ P.S (k + 1)) :
    (P.ρ * P.q, P.ρ, z) ∈ P.Qs (k + 1) :=
  stepTris_subset_Qs k (mem_stepTris_of_stepPts hz)

/-- **Bands**: all triples read at depth `k` lie in `[ρ q^k, ρ]`. -/
theorem Good.Qs_band (hP : P.Good) :
    ∀ k, ∀ t ∈ P.Qs k, P.ρ * P.q ^ k ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ P.ρ
  | 0, t, ht => by
    simp only [Qs, costTris, Finset.mem_image] at ht
    obtain ⟨p, -, rfl⟩ := ht
    exact ⟨le_rfl, hP.rho_q_pow_le 0, le_rfl⟩
  | k + 1, t, ht => by
    have ih := Good.Qs_band hP k
    simp only [Qs, Finset.mem_union] at ht
    rcases ht with (ht | ht) | ht
    · obtain ⟨z, -, rfl⟩ := mem_stepTris_iff.1 ht
      exact ⟨hP.rho_q_pow_succ_le k, hP.rho_q_le, le_rfl⟩
    · simp only [childTris, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_range,
        Finset.mem_image, true_and] at ht
      obtain ⟨j, i, -, t', ht', rfl⟩ := ht
      obtain ⟨h1, h2, h3⟩ := ih t' ht'
      simp only [tau, T_r]
      refine ⟨?_, mul_le_mul_of_nonneg_left h2 hP.q_pos.le, ?_⟩
      · rw [pow_succ, mul_comm (P.q ^ k) P.q, ← mul_assoc, mul_comm P.ρ P.q, mul_assoc]
        exact mul_le_mul_of_nonneg_left h1 hP.q_pos.le
      · calc P.q * t'.2.1 ≤ 1 * P.ρ := mul_le_mul hP.q_le_one h3
              ((hP.rho_q_pow_pos k).le.trans (h1.trans h2)) zero_le_one
          _ = P.ρ := one_mul _
    · simp only [costTris, Finset.mem_image] at ht
      obtain ⟨p, -, rfl⟩ := ht
      exact ⟨le_rfl, hP.rho_q_pow_le _, le_rfl⟩

theorem Good.Qs_pos (hP : P.Good) (k : ℕ) : ∀ t ∈ P.Qs k, 0 < t.1 := fun t ht =>
  (hP.rho_q_pow_pos k).trans_le (hP.Qs_band k t ht).1

theorem Good.stepTris_pos (hP : P.Good) (Sμ : Finset (Rd d)) : ∀ t ∈ P.stepTris Sμ, 0 < t.1 :=
  fun t ht => by
    obtain ⟨z, -, rfl⟩ := mem_stepTris_iff.1 ht
    exact hP.rho_q_pos

/-- Child triples lie in bands `≤ ρq`, below the root band `(ρq, ρ]`. -/
theorem Good.tau_Qs_snd_fst_le (hP : P.Good) {k : ℕ} (j : Fin (P.J + 1)) (i : ℕ) {t : TriD d}
    (ht : t ∈ P.Qs k) : (tau (P.T j i) t).2.1 ≤ P.ρ * P.q := by
  rw [tau_snd_fst, T_r, mul_comm P.ρ P.q]
  exact mul_le_mul_of_nonneg_left (hP.Qs_band k t ht).2.2 hP.q_pos.le

/-! ## The selector: locality and measurability -/

theorem measurable_rootField : Measurable (P.rootField) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

theorem Good.measurable_stat_root (hP : P.Good) (j : Fin (P.J + 1)) :
    Measurable fun Y : TriD d → ℝ => P.stat j (P.rootField Y) :=
  (hP.stat_meas j).comp measurable_rootField

theorem Good.measurable_sel (hP : P.Good) : Measurable P.sel :=
  measurable_lamax (fun j Y => P.stat j (P.rootField Y)) hP.measurable_stat_root

theorem Good.measurableSet_sel_eq (hP : P.Good) (j : Fin (P.J + 1)) :
    MeasurableSet {Y : TriD d → ℝ | P.sel Y = j} :=
  measurableSet_lamax_eq (fun j Y => P.stat j (P.rootField Y)) hP.measurable_stat_root j

/-- The selector reads only the root triples `(ρq, ρ, z)`, `z ∈ R`. -/
theorem Good.sel_loc (hP : P.Good) (Sμ : Finset (Rd d)) : IsLoc (P.stepTris Sμ) P.sel := by
  intro Y Y' h
  have hs : ∀ j, P.stat j (P.rootField Y) = P.stat j (P.rootField Y') := fun j =>
    hP.stat_loc j _ _ fun z hz => h _ (mem_stepTris_of_R hz)
  simp only [sel, hs]

/-! ## The rule: locality and measurability -/

theorem measurable_comp_tri (τ : TriD d → TriD d) :
    Measurable fun Y : TriD d → ℝ => fun t => Y (τ t) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

/-- **Measurability of the rule** into the finite type `DT J K k`. -/
theorem Good.measurable_dec (hP : P.Good) : ∀ k, Measurable (P.dec k)
  | 0 => measurable_const
  | k + 1 => by
    refine measurable_to_countable' fun t => ?_
    have ih := Good.measurable_dec hP k
    have hset : P.dec (k + 1) ⁻¹' {t} = {Y | P.sel Y = t.fst} ∩
        ⋂ i : Fin P.K, (fun Y : TriD d → ℝ => fun s => Y (tau (P.T t.fst i) s)) ⁻¹'
          (P.dec k ⁻¹' {t.snd i}) := by
      ext Y
      simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter]
      rw [dec_succ, DT.ext_iff']
      simp only [DT.fst_mk, DT.snd_mk]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i => ?_⟩
        rw [← h1]
        exact congrFun h2 i
      · rintro ⟨h1, h2⟩
        refine ⟨h1, funext fun i => ?_⟩
        rw [h1]
        exact h2 i
    rw [hset]
    exact (hP.measurableSet_sel_eq _).inter (MeasurableSet.iInter fun i =>
      (ih.comp (measurable_comp_tri _)) (measurableSet_singleton _))

/-- Measurability of `Y ↦ Φ (dec k Y) Y` for measurable `Φ d` (finitely many trees). -/
theorem Good.measurable_of_dec (hP : P.Good) {k : ℕ} {Φ : DT P.J P.K k → (TriD d → ℝ) → ℝ}
    (hΦ : ∀ t, Measurable (Φ t)) : Measurable fun Y => Φ (P.dec k Y) Y := by
  have h : Measurable fun p : DT P.J P.K k × (TriD d → ℝ) => Φ p.1 p.2 :=
    measurable_from_prod_countable_right fun t => hΦ t
  exact h.comp ((hP.measurable_dec k).prodMk measurable_id)

/-- **Locality of the rule**: `dec k` reads only the finitely many triples `Qs k`. -/
theorem Good.dec_loc (hP : P.Good) : ∀ k, IsLoc (P.Qs k) (P.dec k)
  | 0 => fun _ _ _ => rfl
  | k + 1 => fun Y Y' h => by
    have hs : P.sel Y = P.sel Y' :=
      hP.sel_loc (P.S k) Y Y' fun t ht => h t (stepTris_subset_Qs k ht)
    rw [dec_succ, dec_succ, hs]
    congr 1
    funext i
    exact Good.dec_loc hP k _ _ fun t ht => h _ (mem_Qs_tau _ i.2 ht)

end LParams

end HigherDimLFPP.Lower
