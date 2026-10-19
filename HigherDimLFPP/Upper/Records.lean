import HigherDimLFPP.Upper.PolygonMeasure
import LQGDimension.LFPP.ChainUnionAux
import Mathlib.Data.Int.Log

/-!
# Records of chains: scale indices, lattices, locations and record families

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.3 ("Records of chains", lines 804–873 of
the text version), as corrected by the planning audit HA3 (`planning/audits/HA3-section-4.md`):
the scale-index fact of Details D1 and the record design of Details D6 with the fix **F1** (the
record families carry the chord-length constraints); ruling H7 (dyadic blocks `K = 2ⁿ`,
threshold `a₀ = c₀/K`, `c₀ = 1/500`).

2D source: the record design of `LQGDimension/LFPP/RecordsAux3.lean` and `RecordsAux4.lean`
(`side`, `Loc`, `RecData`, `RecValid`, `recSet`): a validity predicate, actual records are valid,
and valid records are counted.  The grids are now `ℤ^d`, there are two record types (good and bad
nodes, HA3 D6), and the families are explicit sets of configurations with the length
constraints of F1 instead of similarity images of normalized families.

Contents:

* `scaleIdx R = ⌊log₂(1/R)⌋`, with `2^{-j-1} < R ≤ 2^{-j}` (`scaleIdx_spec`), and the scale-index
  fact of HA3 D1 (`scaleIdx_child`): for a child `v` of an internal node `u` of a well-formed tree
  with `K = 2ⁿ`, `j_v - j_u ∈ {n-1, n, n+1}`;
* the half-open lattice cubes `Q_j(p) = δ 2^{-j} (p + [0,1)^d)` (`Qcube`, `latCube`) and the cube
  index `p_j(z)` (`cubeIdx`);
* locations `λ = (j, p, q)` (`Loc`), the location of a chord (`locOf`) and the relation "`[x, y]`
  has location `λ`" (`HasLoc`), which includes the length condition `|y - x| ∈ (2^{-j-1}, 2^{-j}]`;
* good records `(good, k, ι, λ, λ')` (`GoodRec`) and bad records `(bad, λ, p'', q'', λ')`
  (`BadRec`), their configuration families `Φ(ρ)` (`goodFam`, `badFam`, `family`) with the
  constraints of F1, the record variables (`cfgVal`) and deterministic costs (`Record.cost`);
* the valid records `𝓡` (`RecValid`) and chain records (`IsChainRec`);
* elementary properties: valid records step down `n - 1`, `n` or `n + 1` scales
  (`RecValid.scaleStep`), hence scale separation along chain records
  (`IsChainRec.scale_sep`: `(n-1)k ≤ j_{i+k} - j_i ≤ (n+1)k`), and the polygons of family
  configurations are nondegenerate (`polyLen_pos_of_mem_family`).

The followed-child index `ι` is 0-based here: the followed child of a good node is the edge
`[z_ι, z_{ι+1}]` of its child polygon, `0 ≤ ι < K` (the paper's `[z_{ι-1}, z_ι]`, `1 ≤ ι ≤ K`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

/-! ## Parameters -/

/-- The block threshold `a₀ = c₀ / K` with `c₀ = 1/500` and `K = 2ⁿ` (ruling H7, HA3 F5); it is
the threshold of `GoodNodeGeometry`. -/
def a0 (n : ℕ) : ℝ := 1 / 500 / ((2 ^ n : ℕ) : ℝ)

/-- The containment radius `ρ₀ = max(4, 2√d)` of the bad families (HA3 F1, F7). -/
def rho0 (d : ℕ) : ℝ := max 4 (2 * Real.sqrt d)

theorem a0_pos (n : ℕ) : 0 < a0 n := by
  unfold a0; positivity

theorem a0_le_one (n : ℕ) : a0 n ≤ 1 := by
  unfold a0
  have h : (1 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  rw [div_le_one (by positivity)]
  linarith

theorem four_le_rho0 (d : ℕ) : 4 ≤ rho0 d := le_max_left _ _

theorem two_sqrt_le_rho0 (d : ℕ) : 2 * Real.sqrt d ≤ rho0 d := le_max_right _ _

theorem rho0_pos (d : ℕ) : 0 < rho0 d := by
  have := four_le_rho0 d; linarith

/-! ## Scale indices (HA3 D1) -/

/-- The scale index `j(R) = ⌊log₂(1/R)⌋`, so that `2^{-j-1} < R ≤ 2^{-j}` for `R > 0`. -/
def scaleIdx (R : ℝ) : ℤ := Int.log 2 R⁻¹

theorem scaleIdx_spec {R : ℝ} (hR : 0 < R) :
    (2 : ℝ) ^ (-scaleIdx R - 1) < R ∧ R ≤ (2 : ℝ) ^ (-scaleIdx R) := by
  have h1 := Int.zpow_log_le_self (b := 2) (by norm_num) (inv_pos.2 hR)
  have h2 := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) R⁻¹
  push_cast at h1 h2
  constructor
  · have e : (2 : ℝ) ^ (-scaleIdx R - 1) = ((2 : ℝ) ^ (scaleIdx R + 1))⁻¹ := by
      rw [← zpow_neg]; congr 1; ring
    rw [e, inv_lt_comm₀ (by positivity) hR]
    exact h2
  · rw [zpow_neg, le_inv_comm₀ hR (by positivity)]
    exact h1

/-- The scale index is characterized by `2^{-j-1} < R ≤ 2^{-j}`. -/
theorem scaleIdx_eq {R : ℝ} {j : ℤ} (h1 : (2 : ℝ) ^ (-j - 1) < R) (h2 : R ≤ (2 : ℝ) ^ (-j)) :
    scaleIdx R = j := by
  have hR : 0 < R := lt_trans (by positivity) h1
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  have hle : j ≤ scaleIdx R := by
    have := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (x := j) hRi).1
    push_cast at this
    refine this ?_
    rw [le_inv_comm₀ (by positivity) hR, ← zpow_neg]
    exact h2
  have hlt : scaleIdx R < j + 1 := by
    have := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (x := j + 1) hRi).1
    push_cast at this
    refine this ?_
    rw [inv_lt_comm₀ hR (by positivity), ← zpow_neg]
    have e : -(j + 1) = -j - 1 := by ring
    rw [e]
    exact h1
  omega

theorem scaleIdx_nonneg {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) : 0 ≤ scaleIdx R := by
  have hRi : 0 < R⁻¹ := inv_pos.2 hR
  have := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (x := 0) hRi).1
  push_cast at this
  refine this ?_
  rw [zpow_zero]
  exact (one_le_inv₀ hR).2 hR1

/-- An upper bound on the scale index from a lower bound on `R`: if `r < R` then
`j(R) ≤ ⌊log₂(1/r)⌋`. -/
theorem scaleIdx_le_log {R r : ℝ} (hr : 0 < r) (hrR : r < R) : scaleIdx R ≤ Int.log 2 r⁻¹ := by
  have hR : 0 < R := hr.trans hrR
  have hri : 0 < r⁻¹ := inv_pos.2 hr
  have h := (scaleIdx_spec hR).2
  have := (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (x := scaleIdx R) hri).1
  push_cast at this
  refine this ?_
  rw [le_inv_comm₀ (by positivity) hr, ← zpow_neg]
  exact hrR.le.trans h

theorem two_zpow_sub_natCast (m : ℤ) (k : ℕ) : (2 : ℝ) ^ (m - k) = (2 : ℝ) ^ m / 2 ^ k := by
  rw [zpow_sub₀ two_ne_zero, zpow_natCast]

/-- **The scale-index fact of HA3 D1** (generic form).  If `R_u > 0` and
`R_u / (2·2ⁿ) ≤ R_v ≤ 3 R_u / (2·2ⁿ)`, then `n - 1 ≤ j(R_v) - j(R_u) ≤ n + 1`. -/
theorem scaleIdx_child_bounds {Ru Rv : ℝ} (n : ℕ) (hRu : 0 < Ru)
    (h1 : Ru / (2 * 2 ^ n) ≤ Rv) (h2 : Rv ≤ 3 * Ru / (2 * 2 ^ n)) :
    (n : ℤ) - 1 ≤ scaleIdx Rv - scaleIdx Ru ∧ scaleIdx Rv - scaleIdx Ru ≤ n + 1 := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hRv : 0 < Rv := lt_of_lt_of_le (by positivity) h1
  obtain ⟨hu1, hu2⟩ := scaleIdx_spec hRu
  obtain ⟨hv1, hv2⟩ := scaleIdx_spec hRv
  set j := scaleIdx Ru with hj
  set j' := scaleIdx Rv with hj'
  constructor
  · by_contra hcon
    -- `j' ≤ j + n - 2`, so `2^{-j'-1} ≥ 4 · 2^{-j} / 2^{n+1}`
    have hle : -j + 2 - ((n + 1 : ℕ) : ℤ) ≤ -j' - 1 := by push_cast; omega
    have hmono := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle
    rw [two_zpow_sub_natCast, zpow_add₀ two_ne_zero] at hmono
    have e : (2 : ℝ) ^ (2 : ℤ) = 4 := by norm_num
    rw [e, pow_succ] at hmono
    -- `Rv > 2^{-j'-1} ≥ 4 · 2^{-j}/(2·2ⁿ) ≥ 4 Ru/(2·2ⁿ) > 3 Ru/(2·2ⁿ) ≥ Rv`
    have h3 : 4 * Ru / (2 * 2 ^ n) ≤ (2 : ℝ) ^ (-j) * 4 / (2 ^ n * 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h4 : 3 * Ru / (2 * 2 ^ n) < 4 * Ru / (2 * 2 ^ n) := by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; linarith
    linarith
  · by_contra hcon
    -- `j' ≥ j + n + 2`, so `2^{-j'} ≤ 2^{-j-1} / 2^{n+1}`
    have hle : -j' ≤ -j - 1 - ((n + 1 : ℕ) : ℤ) := by push_cast; omega
    have hmono := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle
    rw [two_zpow_sub_natCast, pow_succ] at hmono
    have h3 : (2 : ℝ) ^ (-j - 1) / (2 ^ n * 2) < Ru / (2 * 2 ^ n) := by
      rw [mul_comm (2 : ℝ) (2 ^ n)]
      exact div_lt_div_of_pos_right hu1 (by positivity)
    linarith

/-- **The scale-index fact of HA3 D1** for the partition tree: with `K = 2ⁿ`, every child `v` of
an internal node `u` of a well-formed tree satisfies `j_v - j_u ∈ {n - 1, n, n + 1}`, where
`j = scaleIdx R`. -/
theorem scaleIdx_child {E : Type*} [NormedAddCommGroup E] {T : CutTree} {γ : ℝ → E} {n : ℕ}
    {ε ρ' : ℝ} (hT : T.WF γ (2 ^ n) ε ρ') (hε : 0 ≤ ε) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) :
    scaleIdx (T.R γ (u ++ [i])) - scaleIdx (T.R γ u) ∈
      ({(n : ℤ) - 1, (n : ℤ), (n : ℤ) + 1} : Finset ℤ) := by
  have hRu : 0 < T.R γ u := lt_of_le_of_lt hε ((hT.internal_iff u hu).1 (by omega))
  obtain ⟨h1, h2⟩ := hT.scale u hu i hi
  push_cast at h1 h2
  obtain ⟨b1, b2⟩ := scaleIdx_child_bounds n hRu h1 h2
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ## Lattice cubes -/

section Lattice

variable {d : ℕ}

/-- The side `δ 2^{-j}` of the lattice cubes at scale index `j`. -/
def side (δ : ℝ) (j : ℤ) : ℝ := δ * (2 : ℝ) ^ (-j)

theorem side_pos {δ : ℝ} (hδ : 0 < δ) (j : ℤ) : 0 < side δ j := by
  unfold side; positivity

/-- `side` is antitone in the scale index. -/
theorem side_anti {δ : ℝ} (hδ : 0 ≤ δ) {j j' : ℤ} (h : j ≤ j') : side δ j' ≤ side δ j := by
  unfold side
  exact mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (by omega)) hδ

/-- The index `p_s(z) ∈ ℤ^d` of the half-open lattice cube of side `s` containing `z`. -/
def cubeIdx (s : ℝ) (z : Rd d) : Fin d → ℤ := fun i => ⌊z i / s⌋

/-- The half-open lattice cube `s (p + [0,1)^d)`. -/
def latCube (s : ℝ) (p : Fin d → ℤ) : Set (Rd d) :=
  {z | ∀ i, (p i : ℝ) * s ≤ z i ∧ z i < ((p i : ℝ) + 1) * s}

/-- The lattice cube `Q_j(p) = δ 2^{-j} (p + [0,1)^d)` of HA3 D6. -/
def Qcube (δ : ℝ) (j : ℤ) (p : Fin d → ℤ) : Set (Rd d) := latCube (side δ j) p

/-- The corner `s p` of the lattice cube `s (p + [0,1)^d)`. -/
def corner (s : ℝ) (p : Fin d → ℤ) : Rd d := WithLp.toLp 2 fun i => (p i : ℝ) * s

theorem mem_latCube_iff {s : ℝ} (hs : 0 < s) {p : Fin d → ℤ} {z : Rd d} :
    z ∈ latCube s p ↔ cubeIdx s z = p := by
  simp only [latCube, Set.mem_ofPred_eq, cubeIdx, funext_iff, Int.floor_eq_iff,
    le_div_iff₀ hs, div_lt_iff₀ hs]

theorem mem_latCube_cubeIdx {s : ℝ} (hs : 0 < s) (z : Rd d) : z ∈ latCube s (cubeIdx s z) :=
  (mem_latCube_iff hs).2 rfl

theorem corner_apply (s : ℝ) (p : Fin d → ℤ) (i : Fin d) : corner s p i = (p i : ℝ) * s := rfl

/-- A point of a lattice cube of side `s` is within `√d s` of its corner. -/
theorem norm_sub_corner_le {s : ℝ} (hs : 0 < s) {p : Fin d → ℤ} {z : Rd d}
    (hz : z ∈ latCube s p) : ‖z - corner s p‖ ≤ Real.sqrt d * s := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin d, ‖(z - corner s p).ofLp i‖ ^ 2 ≤ d * s ^ 2 := by
    calc ∑ i : Fin d, ‖(z - corner s p).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, s ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          obtain ⟨h1, h2⟩ := hz i
          have e : (z - corner s p).ofLp i = z i - (p i : ℝ) * s := rfl
          rw [e, Real.norm_eq_abs, sq_abs]
          have h0 : 0 ≤ z i - (p i : ℝ) * s := by linarith
          have h3 : z i - (p i : ℝ) * s ≤ s := by linarith
          nlinarith
      _ = d * s ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (∑ i : Fin d, ‖(z - corner s p).ofLp i‖ ^ 2) ≤ Real.sqrt (d * s ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * s := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hs.le]

end Lattice

/-! ## Locations -/

section Locations

variable {d : ℕ}

/-- A location `λ = (j, p, q)`: a scale index and the indices of two lattice cubes of side
`δ 2^{-j}` (HA3 D6). -/
abbrev Loc (d : ℕ) : Type := ℤ × (Fin d → ℤ) × (Fin d → ℤ)

/-- The location `(j(|y - x|), p_j(x), p_j(y))` of the chord `[x, y]` (HA3 D6). -/
def locOf (δ : ℝ) (x y : Rd d) : Loc d :=
  (scaleIdx ‖y - x‖, cubeIdx (side δ (scaleIdx ‖y - x‖)) x,
    cubeIdx (side δ (scaleIdx ‖y - x‖)) y)

/-- The chord `[x, y]` has location `λ = (j, p, q)`: `|y - x| ∈ (2^{-j-1}, 2^{-j}]` (the
chord-length condition, part of the fix F1), `x ∈ Q_j(p)` and `y ∈ Q_j(q)`. -/
def HasLoc (δ : ℝ) (l : Loc d) (x y : Rd d) : Prop :=
  (2 : ℝ) ^ (-l.1 - 1) < ‖y - x‖ ∧ ‖y - x‖ ≤ (2 : ℝ) ^ (-l.1) ∧
    x ∈ Qcube δ l.1 l.2.1 ∧ y ∈ Qcube δ l.1 l.2.2

/-- The location of the root chord `[0, e₁]`. -/
def rootLoc (d : ℕ) (δ : ℝ) : Loc d := locOf δ 0 (e₁ d)

theorem HasLoc.norm_pos {δ : ℝ} {l : Loc d} {x y : Rd d} (h : HasLoc δ l x y) : 0 < ‖y - x‖ :=
  lt_trans (by positivity) h.1

theorem HasLoc.ne {δ : ℝ} {l : Loc d} {x y : Rd d} (h : HasLoc δ l x y) : x ≠ y := by
  intro hxy
  have := h.norm_pos
  rw [hxy, sub_self, norm_zero] at this
  exact lt_irrefl _ this

theorem hasLoc_locOf {δ : ℝ} (hδ : 0 < δ) {x y : Rd d} (hxy : x ≠ y) :
    HasLoc δ (locOf δ x y) x y := by
  have hR : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  obtain ⟨h1, h2⟩ := scaleIdx_spec hR
  exact ⟨h1, h2, mem_latCube_cubeIdx (side_pos hδ _) x, mem_latCube_cubeIdx (side_pos hδ _) y⟩

theorem HasLoc.locOf_eq {δ : ℝ} (hδ : 0 < δ) {l : Loc d} {x y : Rd d} (h : HasLoc δ l x y) :
    locOf δ x y = l := by
  obtain ⟨h1, h2, hx, hy⟩ := h
  have hj : scaleIdx ‖y - x‖ = l.1 := scaleIdx_eq h1 h2
  have hs := side_pos hδ l.1
  simp only [locOf, hj]
  rw [(mem_latCube_iff hs).1 hx, (mem_latCube_iff hs).1 hy]

theorem hasLoc_iff {δ : ℝ} (hδ : 0 < δ) {l : Loc d} {x y : Rd d} :
    HasLoc δ l x y ↔ x ≠ y ∧ locOf δ x y = l :=
  ⟨fun h => ⟨h.ne, h.locOf_eq hδ⟩, fun ⟨hxy, hl⟩ => hl ▸ hasLoc_locOf hδ hxy⟩

end Locations

/-! ## Records, configurations and families (HA3 D6, fix F1) -/

section RecordsDef

variable {d : ℕ}

/-- A good record `(good, k, ι, λ, λ')` (HA3 D6): the bin `k`, the 0-based index `ι` of the
followed child (the edge `[z_ι, z_{ι+1}]` of the child polygon), the current location `λ` and the
location `λ'` of the followed child. -/
structure GoodRec (d : ℕ) where
  /-- The bin `k = ⌊a_u/δ²⌋`. -/
  bin : ℕ
  /-- The index of the followed child (0-based). -/
  idx : ℕ
  /-- The current location `λ`. -/
  loc : Loc d
  /-- The location `λ'` of the followed child. -/
  next : Loc d
deriving DecidableEq

/-- A bad record `(bad, λ, p'', q'', λ')` (HA3 D6): the current location `λ = (j, p, q)`, the
cubes `Q_j(p'')`, `Q_j(q'')` of the endpoints of the adverse child (in the lattice of `λ`), and the
location `λ'` of the followed child. -/
structure BadRec (d : ℕ) where
  /-- The current location `λ`. -/
  loc : Loc d
  /-- The cube index `p''` of the start of the adverse child. -/
  advP : Fin d → ℤ
  /-- The cube index `q''` of the end of the adverse child. -/
  advQ : Fin d → ℤ
  /-- The location `λ'` of the followed child. -/
  next : Loc d
deriving DecidableEq

/-- A record: good (`Sum.inl`) or bad (`Sum.inr`). -/
abbrev Record (d : ℕ) : Type := GoodRec d ⊕ BadRec d

namespace Record

/-- The current location `λ(ρ)`. -/
def loc : Record d → Loc d
  | .inl g => g.loc
  | .inr b => b.loc

/-- The location `λ'(ρ)` of the followed child. -/
def nextLoc : Record d → Loc d
  | .inl g => g.next
  | .inr b => b.next

/-- The bin of a good record (`0` for bad records; it is not used for them). -/
def bin : Record d → ℕ
  | .inl g => g.bin
  | .inr _ => 0

/-- The deterministic cost of a record (HA3 D7): `k` for a good record in bin `k`, and
`a₀/δ²` for a bad record; `B_ρ = Σ_i cost(ρ_i)`. -/
def cost (n : ℕ) (δ : ℝ) : Record d → ℝ
  | .inl g => g.bin
  | .inr _ => a0 n / δ ^ 2

@[simp] theorem loc_inl (g : GoodRec d) : loc (Sum.inl g : Record d) = g.loc := rfl
@[simp] theorem loc_inr (b : BadRec d) : loc (Sum.inr b : Record d) = b.loc := rfl
@[simp] theorem nextLoc_inl (g : GoodRec d) : nextLoc (Sum.inl g : Record d) = g.next := rfl
@[simp] theorem nextLoc_inr (b : BadRec d) : nextLoc (Sum.inr b : Record d) = b.next := rfl
@[simp] theorem bin_inl (g : GoodRec d) : bin (Sum.inl g : Record d) = g.bin := rfl
@[simp] theorem cost_inl (n : ℕ) (δ : ℝ) (g : GoodRec d) :
    cost n δ (Sum.inl g : Record d) = g.bin := rfl
@[simp] theorem cost_inr (n : ℕ) (δ : ℝ) (b : BadRec d) :
    cost n δ (Sum.inr b : Record d) = a0 n / δ ^ 2 := rfl

end Record

/-- A configuration `(P₁, P₂)` of vertex lists: the parent chord `P₁ = [x, y]` and either the child
polygon `P₂ = Q` (good records) or the adverse child chord `P₂ = [x', y']` (bad records). -/
abbrev Config (d : ℕ) : Type := List (Rd d) × List (Rd d)

/-- The record variable `Y(c) = δ^{-1/2} ⟨φ, ν_{P₁} - ν_{P₂}⟩` of a configuration `c = (P₁, P₂)`
(HA3 D6: `δ^{-1/2}⟨H, ν_{[x,y]} - ν_Q⟩` for good and `δ^{-1/2}⟨H, ν_{[x,y]} - ν_{[x',y']}⟩` for
bad records). -/
def cfgVal (δ : ℝ) (φ : Rd d → ℝ) (c : Config d) : ℝ :=
  δ ^ (-(1 / 2 : ℝ)) * ((∫ z, φ z ∂(polyMeasure c.1)) - ∫ z, φ z ∂(polyMeasure c.2))

/-- The child-chord constraints (HA3 D6, fix F1): with `K = 2ⁿ`,
`|y' - x'| ∈ [|y - x|/(2K), 3|y - x|/(2K)]` and `x', y' ∈ B̄(x, ρ₀ |y - x|)`,
`ρ₀ = max(4, 2√d)`. -/
def ChildChord (n : ℕ) (x y x' y' : Rd d) : Prop :=
  ‖y - x‖ / (2 * 2 ^ n) ≤ ‖y' - x'‖ ∧ ‖y' - x'‖ ≤ 3 * ‖y - x‖ / (2 * 2 ^ n) ∧
    ‖x' - x‖ ≤ rho0 d * ‖y - x‖ ∧ ‖y' - x‖ ≤ rho0 d * ‖y - x‖

/-- The family `Φ(ρ)` of a good record `ρ = (good, k, ι, λ, λ')` (HA3 D6): configurations
`([x, y], Q)` with `[x, y]` of location `λ`, `Q ∈ G_K(x, y)` (`K = 2ⁿ`, threshold `a₀`),
`kδ² ≤ log(len Q / |y - x|) < (k+1)δ²`, `ι < K`, and the edge `[z_ι, z_{ι+1}]` of `Q` of
location `λ'`. -/
def goodFam (n : ℕ) (δ : ℝ) (g : GoodRec d) : Set (Config d) :=
  {c | ∃ x y : Rd d, c.1 = [x, y] ∧ HasLoc δ g.loc x y ∧ c.2 ∈ goodFamily (2 ^ n) (a0 n) x y ∧
    (g.bin : ℝ) * δ ^ 2 ≤ Real.log (polyLen c.2 / ‖y - x‖) ∧
    Real.log (polyLen c.2 / ‖y - x‖) < ((g.bin : ℝ) + 1) * δ ^ 2 ∧
    g.idx < 2 ^ n ∧ HasLoc δ g.next (c.2.getD g.idx 0) (c.2.getD (g.idx + 1) 0)}

/-- The family `Φ(ρ)` of a bad record `ρ = (bad, λ, p'', q'', λ')` (HA3 D6, fix F1):
configurations `([x, y], [x', y'])` with `[x, y]` of location `λ = (j, p, q)`, `x' ∈ Q_j(p'')`,
`y' ∈ Q_j(q'')` and the child-chord constraints `ChildChord`. -/
def badFam (n : ℕ) (δ : ℝ) (b : BadRec d) : Set (Config d) :=
  {c | ∃ x y x' y' : Rd d, c = ([x, y], [x', y']) ∧ HasLoc δ b.loc x y ∧
    x' ∈ Qcube δ b.loc.1 b.advP ∧ y' ∈ Qcube δ b.loc.1 b.advQ ∧ ChildChord n x y x' y'}

/-- The configuration family `Φ(ρ)` of a record. -/
def family (n : ℕ) (δ : ℝ) : Record d → Set (Config d)
  | .inl g => goodFam n δ g
  | .inr b => badFam n δ b

@[simp] theorem family_inl (n : ℕ) (δ : ℝ) (g : GoodRec d) :
    family n δ (Sum.inl g : Record d) = goodFam n δ g := rfl
@[simp] theorem family_inr (n : ℕ) (δ : ℝ) (b : BadRec d) :
    family n δ (Sum.inr b : Record d) = badFam n δ b := rfl

/-- The scale condition `j' - j ∈ {n - 1, n, n + 1}` of the record set. -/
def ScaleStep (n : ℕ) (j j' : ℤ) : Prop := (n : ℤ) - 1 ≤ j' - j ∧ j' - j ≤ n + 1

/-- The valid records `𝓡` (HA3 D6): `Φ(ρ) ≠ ∅`, `j' - j ∈ {n-1, n, n+1}`, and, for a bad record,
some chord of location `λ'` satisfies the child-chord constraints relative to the parent chord
of some element of `Φ(ρ)`.  (For good records `ι < K` is part of `Φ(ρ) ≠ ∅`; it is repeated for
convenience.) -/
def RecValid (n : ℕ) (δ : ℝ) : Record d → Prop
  | .inl g => (goodFam n δ g).Nonempty ∧ g.idx < 2 ^ n ∧ ScaleStep n g.loc.1 g.next.1
  | .inr b => (badFam n δ b).Nonempty ∧ ScaleStep n b.loc.1 b.next.1 ∧
      ∃ x y x' y' x₁ y₁ : Rd d, ([x, y], [x', y']) ∈ badFam n δ b ∧ HasLoc δ b.next x₁ y₁ ∧
        ChildChord n x y x₁ y₁

/-- A chain record (HA3 D6): `λ(ρ₀) = (0, p₀(0), p₀(e₁))` is the root location and
`λ(ρ_{i+1}) = λ'(ρ_i)`.  This is `LQGDimension.ChainUnion.IsChainQ` for these relations, so that
the 2D chain counting applies verbatim. -/
def IsChainRec (δ : ℝ) {l : ℕ} (ρ : Fin l → Record d) : Prop :=
  LQGDimension.ChainUnion.IsChainQ (fun r r' : Record d => r'.loc = r.nextLoc)
    (fun r : Record d => r.loc = rootLoc d δ) ρ

end RecordsDef

/-! ## Two-point polygons -/

section Pair

variable {d : ℕ}

theorem polyLen_pair (x y : Rd d) : polyLen [x, y] = ‖y - x‖ := by
  simp only [polyLen, edges, List.tail_cons, List.zip_cons_cons, List.zip_nil_right, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- The polygon `[x, y]` carries the uniform measure on the chord. -/
theorem polyMeasure_pair {x y : Rd d} (hxy : x ≠ y) : polyMeasure [x, y] = segMeasure x y := by
  have hR : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  simp only [polyMeasure, polyLen, edges, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, div_self hR,
    ENNReal.ofReal_one, one_smul]

end Pair

/-! ## Elementary properties of records, families and chains -/

section Properties

variable {d : ℕ}

/-- Valid records step down `n - 1`, `n` or `n + 1` scales. -/
theorem RecValid.scaleStep {n : ℕ} {δ : ℝ} {ρ : Record d} (h : RecValid n δ ρ) :
    ScaleStep n ρ.loc.1 ρ.nextLoc.1 := by
  rcases ρ with g | b
  · exact h.2.2
  · exact h.2.1

/-- The polygons of the configurations of a family are nondegenerate (`len > 0`). -/
theorem polyLen_pos_of_mem_family {n : ℕ} {δ : ℝ} {ρ : Record d} {c : Config d}
    (hc : c ∈ family n δ ρ) : 0 < polyLen c.1 ∧ 0 < polyLen c.2 := by
  rcases ρ with g | b
  · obtain ⟨x, y, h1, hloc, hQ, -⟩ := hc
    have hR := hloc.norm_pos
    rw [h1, polyLen_pair]
    refine ⟨hR, ?_⟩
    obtain ⟨V, hzV, hV0, hVK, -, -, -⟩ := goodFamily_vertex hQ
    rw [hzV, polyLen_range_map]
    have := norm_sub_le_plen V (2 ^ n)
    rw [hV0, hVK] at this
    exact hR.trans_le this
  · obtain ⟨x, y, x', y', rfl, hloc, -, -, hch⟩ := hc
    have hR := hloc.norm_pos
    refine ⟨by rw [polyLen_pair]; exact hR, ?_⟩
    rw [polyLen_pair]
    exact lt_of_lt_of_le (by positivity) hch.1

/-- The first record of a chain record sits at the root location. -/
theorem IsChainRec.loc_zero {δ : ℝ} {l : ℕ} {ρ : Fin l → Record d} (h : IsChainRec δ ρ)
    (hl : 0 < l) : (ρ ⟨0, hl⟩).loc = rootLoc d δ :=
  h.1 hl

/-- Consecutive records of a chain record: `λ(ρ_{i+1}) = λ'(ρ_i)`. -/
theorem IsChainRec.loc_succ {δ : ℝ} {l : ℕ} {ρ : Fin l → Record d} (h : IsChainRec δ ρ) {i : ℕ}
    (hi : i + 1 < l) : (ρ ⟨i + 1, hi⟩).loc = (ρ ⟨i, by omega⟩).nextLoc :=
  h.2 i hi

/-- **Scale separation along a chain record of valid records**: the scale indices satisfy
`(n - 1) k ≤ j_{i+k} - j_i ≤ (n + 1) k` (HA3 D6 (iii), step 1). -/
theorem IsChainRec.scale_sep {n : ℕ} {δ : ℝ} {l : ℕ} {ρ : Fin l → Record d} (h : IsChainRec δ ρ)
    (hv : ∀ i, RecValid n δ (ρ i)) (i : ℕ) :
    ∀ (k : ℕ) (hik : i + k < l),
      ((n : ℤ) - 1) * k ≤ (ρ ⟨i + k, hik⟩).loc.1 - (ρ ⟨i, by omega⟩).loc.1 ∧
        (ρ ⟨i + k, hik⟩).loc.1 - (ρ ⟨i, by omega⟩).loc.1 ≤ ((n : ℤ) + 1) * k := by
  intro k
  induction k with
  | zero =>
    intro hik
    simp only [CharP.cast_eq_zero, mul_zero, add_zero, sub_self, le_refl, and_self]
  | succ k ih =>
    intro hik
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hstep := (hv ⟨i + k, by omega⟩).scaleStep
    have hsucc : (ρ ⟨i + (k + 1), hik⟩).loc = (ρ ⟨i + k, by omega⟩).nextLoc :=
      h.loc_succ (i := i + k) hik
    unfold ScaleStep at hstep
    rw [hsucc]
    push_cast
    constructor <;> nlinarith

end Properties

end HigherDimLFPP.Upper
