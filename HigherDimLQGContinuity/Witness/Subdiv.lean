import HigherDimLQGContinuity.Witness.Refs

/-!
# Subdivision of witnesses ([C] p. 6, l. 289–297)

Packet P5a. Source: blueprint Part A, Lemma `a:lem-subdiv` (constants `N∗`, `w∗`, `d∗`,
`δ₀(Rfc)`); planning audit NA1, item 21 and Details (c) **R5**; NA1's probe shape
`hup_subdivision`, adapted to Part A's `A`-form witness.

For reference constants `(H₀, σ₀, β₀, m, M)` let `δ₀ = subdivDelta0 H₀ σ₀ β₀`,
`N∗ = subdivN H₀ σ₀ β₀ M = ⌈H₀ M (2/δ₀)^{β₀}⌉ + 1`,
`w∗ = subdivW H₀ σ₀ β₀ m M = (m/(N∗ H₀))^{1/σ₀}`, `d∗ = subdivD H₀ σ₀ β₀ m M = m/N∗`. Let `D', E'`
be continuous length metrics with `LocalRefs` for these constants (`0 < H₀`, `0 < σ₀`, `0 < β₀`,
`0 < m` are the only constraints used).

* (a) `hup_subdivision`: a witness `γ` for `D'` with `b D'(γ0, γ1; A) < E'(γ0, γ1; A)` has
  consecutive subdivision points `x = γ(i/N∗)`, `y = γ((i+1)/N∗)` in `K` with
  `w∗ ≤ |x - y| ≤ δ₀/2`, `D'(x, y) ≥ d∗` and `b D'(x, y) < E'(x, y)`; both `A`-internal distances
  of `(x, y)` are global.
* (b) `hdown_subdivision`: a witness `γ` for `E'` with `E'(γ0, γ1; A) ≤ b D'(γ0, γ1; A)` has a
  piece `η = subdivPiece γ N∗ i` (`η s = γ((i + s)/N∗)`), the **favorable arc**:
  `IsSubdivPiece E' … λ η` with `λ = E'(γ0, γ1; A)/N∗ ∈ [m/N∗, M/N∗]` (continuous, in `K`,
  `E'(η s, η t; A) = E'(η s, η t) = λ|s - t|`, an `E'`-geodesic segment, Euclidean diameter
  `< δ₀/2`, two-sided moduli `H₀⁻¹|η s - η t|^{β₀} ≤ λ|s - t| ≤ H₀|η s - η t|^{σ₀}`), with
  `w∗ ≤ |η 0 - η 1|`, `E'(η 0, η 1) ≥ d∗`, `E'(η 0, η 1) ≤ b D'(η 0, η 1)` and
  `D'(η 0, η 1; A) = D'(η 0, η 1)`.
* (c) `hup_empty_of_supDiff`: if `|E' - D'| ≤ u` on `K × K`, no witness for `D'` satisfies (a)
  with `b = 1 + u/d∗`, and no witness for `E'` satisfies the reverse of (a) with `b = 1 + u/d∗`.
* Event forms for the pinned fields: `exists_pair_of_mem_hup` ((a) on `H↑ ∩ PairRefs`),
  `exists_piece_of_mem_hdown` ((b) on `H↓ ∩ PairRefs`), `not_mem_hup_of_abs_sub_le` and
  `not_mem_hup_of_supDistLU_le` ((c): `H↑(D, E; 1 + u/d∗) ∩ PairRefs` and
  `H↑(E, D; 1 + u/d∗) ∩ PairRefs` are empty when `|ρ^E - ρ^D| ≤ u` on `K²`).

**Proof** (R5). Let `ℓ` be the `A`-length of the witness: `m ≤ ℓ ≤ M` (cross, diamK). By the
witness identity the `N∗` consecutive subdivision points have `A`-distances `ℓ/N∗`, summing to `ℓ`
(`IsWitness.sum_internal_subdivPt`), while the other metric is subadditive along the chain
(`internal_le_sum_chain`); so some piece is bad (`IsWitness.exists_index_lt`) or good
(`IsWitness.exists_index_le`). On every piece (`IsWitness.exists_isSubdivPiece`) the lower
reference gives `H₀⁻¹|η s - η t|^{β₀} ≤ λ|s - t| ≤ M/N∗ < H₀⁻¹(δ₀/2)^{β₀}` (`div_subdivN_lt`), so
the piece has Euclidean diameter `< δ₀/2 ≤ 1/128`; then the upper reference at close points gives
`λ|s - t| ≤ H₀|η s - η t|^{σ₀}` (hence `|η 0 - η 1| ≥ w∗`), and (2.12) on the references
(`refs_internal_eq_global`) makes all `A`-distances on the piece global.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### The subdivision constants -/

/-- `N∗ = ⌈H₀ M (2/δ₀)^{β₀}⌉ + 1` (Lemma `a:lem-subdiv`). -/
def subdivN (H₀ σ₀ β₀ M : ℝ) : ℕ :=
  ⌈H₀ * M * (2 / subdivDelta0 H₀ σ₀ β₀) ^ β₀⌉₊ + 1

/-- `w∗ = (m/(N∗ H₀))^{1/σ₀}` (Lemma `a:lem-subdiv`). -/
def subdivW (H₀ σ₀ β₀ m M : ℝ) : ℝ :=
  (m / (subdivN H₀ σ₀ β₀ M * H₀)) ^ (1 / σ₀)

/-- `d∗ = m/N∗` (Lemma `a:lem-subdiv`). -/
def subdivD (H₀ σ₀ β₀ m M : ℝ) : ℝ :=
  m / subdivN H₀ σ₀ β₀ M

theorem one_le_subdivN (H₀ σ₀ β₀ M : ℝ) : 1 ≤ subdivN H₀ σ₀ β₀ M :=
  Nat.le_add_left 1 _

theorem subdivN_pos (H₀ σ₀ β₀ M : ℝ) : (0 : ℝ) < subdivN H₀ σ₀ β₀ M := by
  have h := one_le_subdivN H₀ σ₀ β₀ M
  have h' : (1 : ℝ) ≤ subdivN H₀ σ₀ β₀ M := by exact_mod_cast h
  linarith

theorem lt_subdivN (H₀ σ₀ β₀ M : ℝ) :
    H₀ * M * (2 / subdivDelta0 H₀ σ₀ β₀) ^ β₀ < subdivN H₀ σ₀ β₀ M := by
  unfold subdivN
  push_cast
  linarith [Nat.le_ceil (H₀ * M * (2 / subdivDelta0 H₀ σ₀ β₀) ^ β₀)]

/-- The defining property of `N∗`: `M/N∗ < H₀⁻¹ (δ₀/2)^{β₀}`. -/
theorem div_subdivN_lt {H₀ σ₀ β₀ M : ℝ} (hH₀ : 0 < H₀) :
    M / subdivN H₀ σ₀ β₀ M < H₀⁻¹ * (subdivDelta0 H₀ σ₀ β₀ / 2) ^ β₀ := by
  set δ := subdivDelta0 H₀ σ₀ β₀ with hδ
  have hN : (0 : ℝ) < subdivN H₀ σ₀ β₀ M := subdivN_pos H₀ σ₀ β₀ M
  have hδ0 : 0 < δ := subdivDelta0_pos hH₀
  have hq : 0 < (δ / 2) ^ β₀ := Real.rpow_pos_of_pos (by positivity) _
  have hinv : (2 / δ) ^ β₀ = ((δ / 2) ^ β₀)⁻¹ := by
    rw [← inv_div, Real.inv_rpow (by positivity)]
  have h := lt_subdivN H₀ σ₀ β₀ M
  rw [← hδ, hinv] at h
  rw [div_lt_iff₀ hN]
  calc M = H₀ * M * ((δ / 2) ^ β₀)⁻¹ * (H₀⁻¹ * (δ / 2) ^ β₀) := by field_simp
    _ < subdivN H₀ σ₀ β₀ M * (H₀⁻¹ * (δ / 2) ^ β₀) :=
        mul_lt_mul_of_pos_right h (mul_pos (inv_pos.2 hH₀) hq)
    _ = H₀⁻¹ * (δ / 2) ^ β₀ * subdivN H₀ σ₀ β₀ M := mul_comm _ _

theorem subdivD_pos {H₀ σ₀ β₀ m M : ℝ} (hm : 0 < m) : 0 < subdivD H₀ σ₀ β₀ m M :=
  div_pos hm (subdivN_pos H₀ σ₀ β₀ M)

theorem subdivW_pos {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hm : 0 < m) :
    0 < subdivW H₀ σ₀ β₀ m M :=
  Real.rpow_pos_of_pos (div_pos hm (mul_pos (subdivN_pos H₀ σ₀ β₀ M) hH₀)) _

/-! ### Subdivision points and pieces -/

/-- The subdivision point `γ(i/N)`. -/
def subdivPt (γ : C(unitInterval, Rd d)) (N i : ℕ) : Rd d :=
  witExt γ ((i : ℝ) / N)

/-- The `i`-th of the `N` pieces of `γ`, rescaled to `[0, 1]`: `s ↦ γ((i + s)/N)`. -/
def subdivPiece (γ : C(unitInterval, Rd d)) (N i : ℕ) : ℝ → Rd d :=
  fun s => witExt γ (((i : ℝ) + s) / N)

theorem subdivPiece_zero (γ : C(unitInterval, Rd d)) (N i : ℕ) :
    subdivPiece γ N i 0 = subdivPt γ N i := by
  simp only [subdivPiece, subdivPt, add_zero]

theorem subdivPiece_one (γ : C(unitInterval, Rd d)) (N i : ℕ) :
    subdivPiece γ N i 1 = subdivPt γ N (i + 1) := by
  simp only [subdivPiece, subdivPt, Nat.cast_add, Nat.cast_one]

theorem subdivPt_zero (γ : C(unitInterval, Rd d)) (N : ℕ) : subdivPt γ N 0 = γ 0 := by
  simp only [subdivPt, Nat.cast_zero, zero_div, witExt_zero]

theorem subdivPt_self (γ : C(unitInterval, Rd d)) {N : ℕ} (hN : N ≠ 0) :
    subdivPt γ N N = γ 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN
  simp only [subdivPt, div_self hN', witExt_one]

theorem continuous_subdivPiece (γ : C(unitInterval, Rd d)) (N i : ℕ) :
    Continuous (subdivPiece γ N i) :=
  (continuous_witExt γ).comp ((continuous_const.add continuous_id).div_const _)

theorem subdiv_param_mem {N i : ℕ} (hi : i < N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ((i : ℝ) + s) / N ∈ Icc (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hi
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  constructor
  · exact div_nonneg (add_nonneg (Nat.cast_nonneg i) hs.1) hN.le
  · rw [div_le_one hN]
    linarith [hs.2]

theorem subdivPiece_mem {γ : C(unitInterval, Rd d)} {S : Set (Rd d)} (hγ : ∀ t, γ t ∈ S)
    (N i : ℕ) (s : ℝ) : subdivPiece γ N i s ∈ S :=
  witExt_mem hγ _

theorem subdivPt_mem {γ : C(unitInterval, Rd d)} {S : Set (Rd d)} (hγ : ∀ t, γ t ∈ S)
    (N i : ℕ) : subdivPt γ N i ∈ S :=
  witExt_mem hγ _

/-- Subadditivity of an internal metric along a chain of points. -/
theorem internal_le_sum_chain (G : ContMetric d) (U : Set (Rd d)) {p : ℕ → Rd d}
    (hp0 : p 0 ∈ U) (n : ℕ) :
    G.internal U (p 0) (p n) ≤ ∑ i ∈ Finset.range n, G.internal U (p i) (p (i + 1)) := by
  induction n with
  | zero => simp only [G.internal_self hp0, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (G.internal_triangle U _ (p n) _).trans (add_le_add ih le_rfl)

/-! ### The witness identity on the pieces -/

namespace IsWitness

variable {G : ContMetric d} {γ : C(unitInterval, Rd d)}

/-- On the `i`-th piece, `G(η s, η t; A) = (|s - t|/N) G(γ 0, γ 1; A)`. -/
theorem internal_subdivPiece (hγ : IsWitness G γ) {N i : ℕ} (hi : i < N) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    G.internal (annA d) (subdivPiece γ N i s) (subdivPiece γ N i t) =
      ENNReal.ofReal (|s - t| / N) * G.internal (annA d) (γ 0) (γ 1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.zero_lt_of_lt hi
  unfold subdivPiece
  rw [hγ.internal_witExt (subdiv_param_mem hi hs) (subdiv_param_mem hi ht), ← sub_div,
    add_sub_add_left_eq_sub, abs_div, abs_of_pos hN]

/-- The `N` consecutive subdivision points of a witness have `A`-distances summing to the
`A`-length of the witness. -/
theorem sum_internal_subdivPt (hγ : IsWitness G γ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Finset.range N, G.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) =
      G.internal (annA d) (γ 0) (γ 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ i ∈ Finset.range N,
      G.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) =
        ENNReal.ofReal (1 / N) * G.internal (annA d) (γ 0) (γ 1) := by
    intro i hi
    rw [← subdivPiece_zero, ← subdivPiece_one, hγ.internal_subdivPiece (Finset.mem_range.1 hi)
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩]
    norm_num
  have hone : (N : ℝ≥0∞) * ENNReal.ofReal (1 / N) = 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      mul_one_div_cancel hNpos.ne', ENNReal.ofReal_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← mul_assoc, hone, one_mul]

/-- **A bad piece** (`H↑` direction): if `b D'(γ0, γ1; A) < E'(γ0, γ1; A)` for a witness `γ` of
`D'`, then `b D'(p_i, p_{i+1}; A) < E'(p_i, p_{i+1}; A)` for two consecutive subdivision points. -/
theorem exists_index_lt {D' E' : ContMetric d} (hγ : IsWitness D' γ) {N : ℕ} (hN : 1 ≤ N)
    {b : ℝ≥0∞}
    (hbad : b * D'.internal (annA d) (γ 0) (γ 1) < E'.internal (annA d) (γ 0) (γ 1)) :
    ∃ i < N, b * D'.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) <
      E'.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) := by
  by_contra hcon
  push Not at hcon
  have hp0 : subdivPt γ N 0 ∈ annA d := by
    rw [subdivPt_zero]; exact annK_subset_annA (hγ.mem_annK 0)
  have hchain := internal_le_sum_chain E' (annA d) hp0 N
  rw [subdivPt_zero, subdivPt_self γ (by omega)] at hchain
  have hsum :
      ∑ i ∈ Finset.range N, E'.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) ≤
        b * D'.internal (annA d) (γ 0) (γ 1) := by
    rw [← hγ.sum_internal_subdivPt hN, Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hcon i (Finset.mem_range.1 hi)
  exact (lt_irrefl _) ((hchain.trans hsum).trans_lt hbad)

/-- **A good piece** (`H↓` direction): if `E'(γ0, γ1; A) ≤ b D'(γ0, γ1; A)` for a witness `γ` of
`E'`, then `E'(p_i, p_{i+1}; A) ≤ b D'(p_i, p_{i+1}; A)` for two consecutive subdivision points. -/
theorem exists_index_le {D' E' : ContMetric d} (hγ : IsWitness E' γ) {N : ℕ} (hN : 1 ≤ N)
    {b : ℝ≥0∞}
    (hgood : E'.internal (annA d) (γ 0) (γ 1) ≤ b * D'.internal (annA d) (γ 0) (γ 1)) :
    ∃ i < N, E'.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) ≤
      b * D'.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) := by
  by_contra hcon
  push Not at hcon
  have hp0 : subdivPt γ N 0 ∈ annA d := by
    rw [subdivPt_zero]; exact annK_subset_annA (hγ.mem_annK 0)
  have hchain := internal_le_sum_chain D' (annA d) hp0 N
  rw [subdivPt_zero, subdivPt_self γ (by omega)] at hchain
  have hlt :
      ∑ i ∈ Finset.range N, b * D'.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) <
        ∑ i ∈ Finset.range N, E'.internal (annA d) (subdivPt γ N i) (subdivPt γ N (i + 1)) :=
    ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.2 (by omega)⟩
      fun i hi => hcon i (Finset.mem_range.1 hi)
  rw [hγ.sum_internal_subdivPt hN, ← Finset.mul_sum] at hlt
  exact (lt_irrefl _) ((hgood.trans (mul_le_mul_right hchain b)).trans_lt hlt)

end IsWitness

/-! ### The pieces of a witness on the references -/

/-- **A piece of a subdivided witness** (Part A `a:lem-subdiv`(b), the favorable arc, for
`G = E'`): `η : ℝ → ℝ^d` is a continuous curve in `K` along which both `G(·, ·; A)` and `G` grow
linearly with slope `lam` on `[0, 1]`; it is a `G`-geodesic segment on `[0, 1]`, has Euclidean
diameter `< δ/2`, and satisfies the two-sided moduli in own units (the hypothesis `hη` of
`Routing.arcModuli_of_twoSided`). -/
structure IsSubdivPiece (G : ContMetric d) (H₀ σ₀ β₀ δ lam : ℝ) (η : ℝ → Rd d) : Prop where
  continuous : Continuous η
  mem_annK : ∀ s ∈ Icc (0 : ℝ) 1, η s ∈ annK d
  internal_eq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
    G.internal (annA d) (η s) (η t) = ENNReal.ofReal (lam * |s - t|)
  apply_eq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, G.1 (η s, η t) = lam * |s - t|
  geodSeg : IsGeodSeg G η 0 1
  norm_sub_lt : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖η s - η t‖ < δ / 2
  moduli : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
    H₀⁻¹ * ‖η s - η t‖ ^ β₀ ≤ lam * |s - t| ∧ lam * |s - t| ≤ H₀ * ‖η s - η t‖ ^ σ₀

/-- **Every piece of a witness on the references is a favorable arc** (R5): for a length metric
`G` with `LocalRefs G (H₀, σ₀, β₀, m, M)` and a witness `γ` for `G`, each of the `N∗` pieces
`subdivPiece γ N∗ i` is an `IsSubdivPiece` with slope `lam = G(γ0, γ1; A)/N∗ ∈ [m/N∗, M/N∗]`, and
its endpoints are at Euclidean distance `≥ w∗`. -/
theorem IsWitness.exists_isSubdivPiece {G : ContMetric d} (hG : G.IsLength)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hR : LocalRefs G H₀ σ₀ β₀ m M) {γ : C(unitInterval, Rd d)} (hγ : IsWitness G γ)
    {i : ℕ} (hi : i < subdivN H₀ σ₀ β₀ M) :
    ∃ lam : ℝ, ENNReal.ofReal (lam * subdivN H₀ σ₀ β₀ M) = G.internal (annA d) (γ 0) (γ 1) ∧
      m / subdivN H₀ σ₀ β₀ M ≤ lam ∧ lam ≤ M / subdivN H₀ σ₀ β₀ M ∧
      IsSubdivPiece G H₀ σ₀ β₀ (subdivDelta0 H₀ σ₀ β₀) lam
        (subdivPiece γ (subdivN H₀ σ₀ β₀ M) i) ∧
      subdivW H₀ σ₀ β₀ m M ≤
        ‖subdivPt γ (subdivN H₀ σ₀ β₀ M) i - subdivPt γ (subdivN H₀ σ₀ β₀ M) (i + 1)‖ := by
  set N := subdivN H₀ σ₀ β₀ M with hNdef
  set δ := subdivDelta0 H₀ σ₀ β₀ with hδdef
  set ℓ := G.internal (annA d) (γ 0) (γ 1) with hℓdef
  set η := subdivPiece γ N i with hηdef
  have hNpos : (0 : ℝ) < N := subdivN_pos H₀ σ₀ β₀ M
  have hδpos : 0 < δ := subdivDelta0_pos hH₀
  -- the `A`-length of the witness lies in `[m, M]`
  have h0K : γ 0 ∈ annK d := hγ.mem_annK 0
  have h1K : γ 1 ∈ annK d := hγ.mem_annK 1
  have hℓM : ℓ ≤ ENNReal.ofReal M := by
    refine le_trans ?_ hR.diamK
    unfold diamIn
    exact le_iSup₂_of_le (γ 0) h0K (le_iSup₂_of_le (γ 1) h1K le_rfl)
  have hmℓ : ENNReal.ofReal m ≤ ℓ := by
    refine hR.cross.trans ?_
    unfold setDistIn
    exact iInf₂_le_of_le (γ 0) (mem_sphere_zero_iff_norm.2 hγ.norm_apply_zero)
      (iInf₂_le_of_le (γ 1) (mem_sphere_zero_iff_norm.2 hγ.norm_apply_one) le_rfl)
  have hℓtop : ℓ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hℓM
  set L := ℓ.toReal with hLdef
  have hℓL : ℓ = ENNReal.ofReal L := (ENNReal.ofReal_toReal hℓtop).symm
  have hmL : m ≤ L := by
    rw [hℓL] at hmℓ
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 hmℓ
  have hLM : L ≤ M := by
    rw [hℓL] at hℓM
    rcases ENNReal.ofReal_le_ofReal_iff'.1 hℓM with h | h
    · exact h
    · linarith
  set lam := L / N with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg (hm.le.trans hmL) hNpos.le
  have hmlam : m / N ≤ lam := div_le_div_of_nonneg_right hmL hNpos.le
  have hlamM : lam ≤ M / N := div_le_div_of_nonneg_right hLM hNpos.le
  have hMN : M / N < H₀⁻¹ * (δ / 2) ^ β₀ := div_subdivN_lt hH₀
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, η s ∈ annK d :=
    fun s _ => subdivPiece_mem hγ.mem_annK N i s
  -- the `A`-internal distances on the piece
  have hint : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      G.internal (annA d) (η s) (η t) = ENNReal.ofReal (lam * |s - t|) := by
    intro s hs t ht
    rw [hηdef, hγ.internal_subdivPiece hi hs ht, ← hℓdef, hℓL,
      ← ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) hNpos.le), hlamdef]
    congr 1
    ring
  -- the lower modulus
  have hlow : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      H₀⁻¹ * ‖η s - η t‖ ^ β₀ ≤ lam * |s - t| := by
    intro s hs t ht
    have h := hR.lower _ (annK_subset_annCl (hmem s hs)) _ (annK_subset_annCl (hmem t ht))
    rw [hint s hs t ht] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hlam0 (abs_nonneg _))).1 h
  -- the Euclidean diameter
  have hnorm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ‖η s - η t‖ < δ / 2 := by
    intro s hs t ht
    have habs : |s - t| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
    have h1 : lam * |s - t| ≤ lam := by
      calc lam * |s - t| ≤ lam * 1 := mul_le_mul_of_nonneg_left habs hlam0
        _ = lam := mul_one _
    have h2 : H₀⁻¹ * ‖η s - η t‖ ^ β₀ < H₀⁻¹ * (δ / 2) ^ β₀ :=
      ((hlow s hs t ht).trans h1).trans_lt (hlamM.trans_lt hMN)
    have h3 : ‖η s - η t‖ ^ β₀ < (δ / 2) ^ β₀ :=
      lt_of_mul_lt_mul_left h2 (inv_nonneg.2 hH₀.le)
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) (by positivity) hβ₀).1 h3
  -- the upper modulus
  have hupp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      lam * |s - t| ≤ H₀ * ‖η s - η t‖ ^ σ₀ := by
    intro s hs t ht
    have hclose : ‖η s - η t‖ ≤ 1 / 64 := by
      have h1 := hnorm s hs t ht
      have h2 := subdivDelta0_le H₀ σ₀ β₀
      rw [← hδdef] at h2
      linarith
    have h :=
      hR.upper _ (annK_subset_annCl (hmem s hs)) _ (annK_subset_annCl (hmem t ht)) hclose
    rw [hint s hs t ht] at h
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hH₀.le (Real.rpow_nonneg (norm_nonneg _) _))).1 h
  -- the global distances on the piece
  have hglob : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, G.1 (η s, η t) = lam * |s - t| := by
    intro s hs t ht
    have h := refs_internal_eq_global hG hH₀ hσ₀ hR _ (hmem s hs) _ (hmem t ht)
      (by linarith [hnorm s hs t ht])
    rw [hint s hs t ht] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (G.nonneg _ _)
      (mul_nonneg hlam0 (abs_nonneg _))).1 h.symm
  -- the piece is a geodesic segment
  have hgeod : IsGeodSeg G η 0 1 := by
    refine ⟨zero_le_one, (continuous_subdivPiece γ N i).continuousOn, ?_⟩
    rw [hglob 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩, ContMetric.len_def,
      ← curveLengthWith_edist]
    rw [witness_curveLengthWith_eq (L := ENNReal.ofReal lam) zero_le_one
      fun u v hu huv hv => ?_]
    · rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      norm_num
    · rw [Function.comp_apply, Function.comp_apply, G.edist_pt,
        hglob u ⟨hu, huv.trans hv⟩ v ⟨hu.trans huv, hv⟩,
        ← ENNReal.ofReal_mul (sub_nonneg.2 huv), abs_sub_comm, abs_of_nonneg (sub_nonneg.2 huv),
        mul_comm]
  -- the separation `w∗` of the endpoints
  have hW : subdivW H₀ σ₀ β₀ m M ≤ ‖η 0 - η 1‖ := by
    have h := hupp 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    have h1 : m / N ≤ H₀ * ‖η 0 - η 1‖ ^ σ₀ := by
      refine hmlam.trans (le_of_eq_of_le ?_ h)
      norm_num
    have h2 : m / (N * H₀) ≤ ‖η 0 - η 1‖ ^ σ₀ := by
      rw [← div_div, div_le_iff₀ hH₀, mul_comm]
      exact h1
    unfold subdivW
    rw [← hNdef]
    calc (m / (N * H₀)) ^ (1 / σ₀) ≤ (‖η 0 - η 1‖ ^ σ₀) ^ (1 / σ₀) :=
          Real.rpow_le_rpow (div_nonneg hm.le (mul_pos hNpos hH₀).le) h2 (by positivity)
      _ = ‖η 0 - η 1‖ := by
          rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hσ₀.ne', Real.rpow_one]
  refine ⟨lam, ?_, hmlam, hlamM, ⟨continuous_subdivPiece γ N i, hmem, hint, hglob, hgeod,
    hnorm, fun s hs t ht => ⟨hlow s hs t ht, hupp s hs t ht⟩⟩, ?_⟩
  · rw [hlamdef, div_mul_cancel₀ L hNpos.ne', hℓL]
  · rw [← subdivPiece_zero, ← subdivPiece_one]
    exact hW

/-! ### Lemma `a:lem-subdiv` -/

/-- **Subdivision, (a)** (Lemma `a:lem-subdiv`(a); NA1 R5, probe shape `hup_subdivision`): on the
references, a witness `γ` for `D'` with `b D'(γ0, γ1; A) < E'(γ0, γ1; A)` gives consecutive
subdivision points `x = γ(i/N∗)`, `y = γ((i+1)/N∗)` in `K` with `w∗ ≤ |x - y| ≤ δ₀/2`,
`D'(x, y) ≥ d∗` and `b D'(x, y) < E'(x, y)` (global distances by (2.12)). -/
theorem hup_subdivision {D' E' : ContMetric d} (hD' : D'.IsLength) (hE' : E'.IsLength)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hRD : LocalRefs D' H₀ σ₀ β₀ m M) (hRE : LocalRefs E' H₀ σ₀ β₀ m M)
    {b : ℝ} (hb : 0 ≤ b) {γ : C(unitInterval, Rd d)} (hγ : IsWitness D' γ)
    (hbad : ENNReal.ofReal b * D'.internal (annA d) (γ 0) (γ 1) <
      E'.internal (annA d) (γ 0) (γ 1)) :
    ∃ x ∈ annK d, ∃ y ∈ annK d,
      (∃ i : ℕ, i < subdivN H₀ σ₀ β₀ M ∧ x = subdivPt γ (subdivN H₀ σ₀ β₀ M) i ∧
        y = subdivPt γ (subdivN H₀ σ₀ β₀ M) (i + 1)) ∧
      subdivW H₀ σ₀ β₀ m M ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ subdivDelta0 H₀ σ₀ β₀ / 2 ∧
      subdivD H₀ σ₀ β₀ m M ≤ D'.1 (x, y) ∧ b * D'.1 (x, y) < E'.1 (x, y) ∧
      D'.internal (annA d) x y = ENNReal.ofReal (D'.1 (x, y)) ∧
      E'.internal (annA d) x y = ENNReal.ofReal (E'.1 (x, y)) := by
  set N := subdivN H₀ σ₀ β₀ M with hNdef
  obtain ⟨i, hi, hbadi⟩ := hγ.exists_index_lt (E' := E') (one_le_subdivN H₀ σ₀ β₀ M) hbad
  obtain ⟨lam, -, hmlam, -, hP, hW⟩ := hγ.exists_isSubdivPiece hD' hH₀ hσ₀ hβ₀ hm hRD hi
  have hx : subdivPt γ N i ∈ annK d := subdivPt_mem hγ.mem_annK N i
  have hy : subdivPt γ N (i + 1) ∈ annK d := subdivPt_mem hγ.mem_annK N (i + 1)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hxy : ‖subdivPt γ N i - subdivPt γ N (i + 1)‖ < subdivDelta0 H₀ σ₀ β₀ / 2 := by
    rw [← subdivPiece_zero, ← subdivPiece_one]
    exact hP.norm_sub_lt 0 h0 1 h1
  have hδ : ‖subdivPt γ N i - subdivPt γ N (i + 1)‖ ≤ subdivDelta0 H₀ σ₀ β₀ := by
    linarith [subdivDelta0_pos (σ₀ := σ₀) (β₀ := β₀) hH₀]
  have hDxy : D'.1 (subdivPt γ N i, subdivPt γ N (i + 1)) = lam := by
    rw [← subdivPiece_zero, ← subdivPiece_one, hP.apply_eq 0 h0 1 h1]
    norm_num
  have hDA := refs_internal_eq_global hD' hH₀ hσ₀ hRD _ hx _ hy hδ
  have hEA := refs_internal_eq_global hE' hH₀ hσ₀ hRE _ hx _ hy hδ
  refine ⟨_, hx, _, hy, ⟨i, hi, rfl, rfl⟩, hW, hxy.le, ?_, ?_, hDA, hEA⟩
  · rw [hDxy]
    exact hmlam
  · rw [hDA, hEA, ← ENNReal.ofReal_mul hb] at hbadi
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hbadi).1

/-- **Subdivision, (b)** (Lemma `a:lem-subdiv`(b); NA1 R5): on the references, a witness `γ` for
`E'` with `E'(γ0, γ1; A) ≤ b D'(γ0, γ1; A)` has a piece `η = subdivPiece γ N∗ i` which is a
favorable arc: `IsSubdivPiece E' (H₀, σ₀, β₀) δ₀ lam η` with `lam ∈ [m/N∗, M/N∗]` (globally
`E'`-minimizing, constant speed, `E'`-length `lam`, two-sided moduli, Euclidean diameter `< δ₀/2`),
its endpoints `η 0 = γ(i/N∗)`, `η 1 = γ((i+1)/N∗)` satisfy `w∗ ≤ |η 0 - η 1|`,
`E'(η 0, η 1) ≥ d∗`, `E'(η 0, η 1) ≤ b D'(η 0, η 1)`, and `D'(η 0, η 1; A) = D'(η 0, η 1)`. -/
theorem hdown_subdivision {D' E' : ContMetric d} (hD' : D'.IsLength) (hE' : E'.IsLength)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hRD : LocalRefs D' H₀ σ₀ β₀ m M) (hRE : LocalRefs E' H₀ σ₀ β₀ m M)
    {b : ℝ} (hb : 0 ≤ b) {γ : C(unitInterval, Rd d)} (hγ : IsWitness E' γ)
    (hgood : E'.internal (annA d) (γ 0) (γ 1) ≤
      ENNReal.ofReal b * D'.internal (annA d) (γ 0) (γ 1)) :
    ∃ η : ℝ → Rd d, ∃ lam : ℝ,
      (∃ i : ℕ, i < subdivN H₀ σ₀ β₀ M ∧ η = subdivPiece γ (subdivN H₀ σ₀ β₀ M) i) ∧
      m / subdivN H₀ σ₀ β₀ M ≤ lam ∧ lam ≤ M / subdivN H₀ σ₀ β₀ M ∧
      ENNReal.ofReal (lam * subdivN H₀ σ₀ β₀ M) = E'.internal (annA d) (γ 0) (γ 1) ∧
      IsSubdivPiece E' H₀ σ₀ β₀ (subdivDelta0 H₀ σ₀ β₀) lam η ∧
      subdivW H₀ σ₀ β₀ m M ≤ ‖η 0 - η 1‖ ∧
      subdivD H₀ σ₀ β₀ m M ≤ E'.1 (η 0, η 1) ∧ E'.1 (η 0, η 1) ≤ b * D'.1 (η 0, η 1) ∧
      D'.internal (annA d) (η 0) (η 1) = ENNReal.ofReal (D'.1 (η 0, η 1)) := by
  set N := subdivN H₀ σ₀ β₀ M with hNdef
  obtain ⟨i, hi, hgoodi⟩ := hγ.exists_index_le (D' := D') (one_le_subdivN H₀ σ₀ β₀ M) hgood
  obtain ⟨lam, hlamℓ, hmlam, hlamM, hP, hW⟩ :=
    hγ.exists_isSubdivPiece hE' hH₀ hσ₀ hβ₀ hm hRE hi
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hx : subdivPiece γ N i 0 ∈ annK d := hP.mem_annK 0 h0
  have hy : subdivPiece γ N i 1 ∈ annK d := hP.mem_annK 1 h1
  have hδ : ‖subdivPiece γ N i 0 - subdivPiece γ N i 1‖ ≤ subdivDelta0 H₀ σ₀ β₀ := by
    linarith [hP.norm_sub_lt 0 h0 1 h1, subdivDelta0_pos (σ₀ := σ₀) (β₀ := β₀) hH₀]
  have hExy : E'.1 (subdivPiece γ N i 0, subdivPiece γ N i 1) = lam := by
    rw [hP.apply_eq 0 h0 1 h1]
    norm_num
  have hEA : E'.internal (annA d) (subdivPiece γ N i 0) (subdivPiece γ N i 1) =
      ENNReal.ofReal lam := by
    rw [hP.internal_eq 0 h0 1 h1]
    norm_num
  have hDA := refs_internal_eq_global hD' hH₀ hσ₀ hRD _ hx _ hy hδ
  refine ⟨subdivPiece γ N i, lam, ⟨i, hi, rfl⟩, hmlam, hlamM, hlamℓ, hP, ?_, ?_, ?_, hDA⟩
  · rw [subdivPiece_zero, subdivPiece_one]
    exact hW
  · rw [hExy]
    exact hmlam
  · rw [subdivPiece_zero, subdivPiece_one] at hEA hDA
    rw [hEA, hDA, ← ENNReal.ofReal_mul hb] at hgoodi
    rw [hExy, subdivPiece_zero, subdivPiece_one]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hb (D'.nonneg _ _))).1 hgoodi

/-- One orientation of (c): if `E' ≤ D' + u` on `K × K` (`u ≥ 0`), no witness for `D'` has
`(1 + u/d∗) D'(γ0, γ1; A) < E'(γ0, γ1; A)`. -/
theorem not_hup_of_le_add {D' E' : ContMetric d} (hD' : D'.IsLength) (hE' : E'.IsLength)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hRD : LocalRefs D' H₀ σ₀ β₀ m M) (hRE : LocalRefs E' H₀ σ₀ β₀ m M) {u : ℝ} (hu : 0 ≤ u)
    (hle : ∀ x ∈ annK d, ∀ y ∈ annK d, E'.1 (x, y) ≤ D'.1 (x, y) + u)
    {γ : C(unitInterval, Rd d)} (hγ : IsWitness D' γ) :
    ¬ ENNReal.ofReal (1 + u / subdivD H₀ σ₀ β₀ m M) * D'.internal (annA d) (γ 0) (γ 1) <
      E'.internal (annA d) (γ 0) (γ 1) := by
  intro hbad
  have hd : 0 < subdivD H₀ σ₀ β₀ m M := subdivD_pos hm
  have hb : 0 ≤ 1 + u / subdivD H₀ σ₀ β₀ m M := by positivity
  obtain ⟨x, hx, y, hy, -, -, -, hdx, hlt, -, -⟩ :=
    hup_subdivision hD' hE' hH₀ hσ₀ hβ₀ hm hRD hRE hb hγ hbad
  have hfac : u ≤ u / subdivD H₀ σ₀ β₀ m M * D'.1 (x, y) := by
    calc u = u / subdivD H₀ σ₀ β₀ m M * subdivD H₀ σ₀ β₀ m M :=
          (div_mul_cancel₀ u hd.ne').symm
      _ ≤ u / subdivD H₀ σ₀ β₀ m M * D'.1 (x, y) :=
          mul_le_mul_of_nonneg_left hdx (div_nonneg hu hd.le)
  have hEle := hle x hx y hy
  have hexp : (1 + u / subdivD H₀ σ₀ β₀ m M) * D'.1 (x, y) =
      D'.1 (x, y) + u / subdivD H₀ σ₀ β₀ m M * D'.1 (x, y) := by ring
  linarith only [hlt, hfac, hEle, hexp]

/-- **Subdivision, (c)** (Lemma `a:lem-subdiv`(c); NA1 R5, R12): if `|E'(x, y) - D'(x, y)| ≤ u`
for all `x, y ∈ K`, then no witness for `D'` satisfies (a) with `b = 1 + u/d∗`, and no witness for
`E'` satisfies the reverse of (a) (`b E'(γ0, γ1; A) < D'(γ0, γ1; A)`) with `b = 1 + u/d∗`. -/
theorem hup_empty_of_supDiff {D' E' : ContMetric d} (hD' : D'.IsLength) (hE' : E'.IsLength)
    {H₀ σ₀ β₀ m M : ℝ} (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hRD : LocalRefs D' H₀ σ₀ β₀ m M) (hRE : LocalRefs E' H₀ σ₀ β₀ m M) {u : ℝ}
    (hdiff : ∀ x ∈ annK d, ∀ y ∈ annK d, |E'.1 (x, y) - D'.1 (x, y)| ≤ u) :
    (∀ γ : C(unitInterval, Rd d), IsWitness D' γ →
      ¬ ENNReal.ofReal (1 + u / subdivD H₀ σ₀ β₀ m M) * D'.internal (annA d) (γ 0) (γ 1) <
        E'.internal (annA d) (γ 0) (γ 1)) ∧
    (∀ γ : C(unitInterval, Rd d), IsWitness E' γ →
      ¬ ENNReal.ofReal (1 + u / subdivD H₀ σ₀ β₀ m M) * E'.internal (annA d) (γ 0) (γ 1) <
        D'.internal (annA d) (γ 0) (γ 1)) := by
  refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
  · have hu : 0 ≤ u := (abs_nonneg _).trans (hdiff _ (hγ.mem_annK 0) _ (hγ.mem_annK 0))
    refine not_hup_of_le_add hD' hE' hH₀ hσ₀ hβ₀ hm hRD hRE hu (fun x hx y hy => ?_) hγ
    have := hdiff x hx y hy
    rw [abs_le] at this
    linarith [this.2]
  · have hu : 0 ≤ u := (abs_nonneg _).trans (hdiff _ (hγ.mem_annK 0) _ (hγ.mem_annK 0))
    refine not_hup_of_le_add hE' hD' hH₀ hσ₀ hβ₀ hm hRE hRD hu (fun x hx y hy => ?_) hγ
    have := hdiff x hx y hy
    rw [abs_le] at this
    linarith [this.1]

/-! ### Event forms for the pinned fields -/

section Events

variable {D E : DistRd d → ContMetric d} {g : DistRd d} {H₀ σ₀ β₀ m M : ℝ}

/-- **(a) on `H↑ ∩ PairRefs`** (the `H↑` passage of §4.4): a pinned field in `H↑(D, E; b)` with
both references and length metrics has a separated global bad pair in `K`. -/
theorem exists_pair_of_mem_hup (hD : (rho D g).IsLength) (hE : (rho E g).IsLength)
    (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hg : g ∈ PairRefs D E H₀ σ₀ β₀ m M) {b : ℝ} (hb : 0 ≤ b) (hup : g ∈ Hup D E b) :
    ∃ x ∈ annK d, ∃ y ∈ annK d,
      subdivW H₀ σ₀ β₀ m M ≤ ‖x - y‖ ∧ ‖x - y‖ ≤ subdivDelta0 H₀ σ₀ β₀ / 2 ∧
      subdivD H₀ σ₀ β₀ m M ≤ (rho D g).1 (x, y) ∧
        b * (rho D g).1 (x, y) < (rho E g).1 (x, y) := by
  obtain ⟨γ, hγ, hbad⟩ := hup
  obtain ⟨x, hx, y, hy, -, hw, hδ, hdx, hlt, -, -⟩ :=
    hup_subdivision hD hE hH₀ hσ₀ hβ₀ hm hg.1 hg.2 hb hγ hbad
  exact ⟨x, hx, y, hy, hw, hδ, hdx, hlt⟩

/-- **(b) on `H↓ ∩ PairRefs`** (Lemma 3.4's favorable arc): a pinned field in `H↓(D, E; b)` with
both references and length metrics carries a witness for `ρ^E` with a favorable piece (the
conclusion of `hdown_subdivision` for `D' = ρ^D_g`, `E' = ρ^E_g`). -/
theorem exists_piece_of_mem_hdown (hD : (rho D g).IsLength) (hE : (rho E g).IsLength)
    (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hg : g ∈ PairRefs D E H₀ σ₀ β₀ m M) {b : ℝ} (hb : 0 ≤ b) (hdown : g ∈ Hdown D E b) :
    ∃ γ : C(unitInterval, Rd d), IsWitness (rho E g) γ ∧ ∃ η : ℝ → Rd d, ∃ lam : ℝ,
      (∃ i : ℕ, i < subdivN H₀ σ₀ β₀ M ∧ η = subdivPiece γ (subdivN H₀ σ₀ β₀ M) i) ∧
      m / subdivN H₀ σ₀ β₀ M ≤ lam ∧ lam ≤ M / subdivN H₀ σ₀ β₀ M ∧
      ENNReal.ofReal (lam * subdivN H₀ σ₀ β₀ M) = (rho E g).internal (annA d) (γ 0) (γ 1) ∧
      IsSubdivPiece (rho E g) H₀ σ₀ β₀ (subdivDelta0 H₀ σ₀ β₀) lam η ∧
      subdivW H₀ σ₀ β₀ m M ≤ ‖η 0 - η 1‖ ∧
      subdivD H₀ σ₀ β₀ m M ≤ (rho E g).1 (η 0, η 1) ∧
      (rho E g).1 (η 0, η 1) ≤ b * (rho D g).1 (η 0, η 1) ∧
      (rho D g).internal (annA d) (η 0) (η 1) = ENNReal.ofReal ((rho D g).1 (η 0, η 1)) := by
  obtain ⟨γ, hγ, hgood⟩ := hdown
  exact ⟨γ, hγ, hdown_subdivision hD hE hH₀ hσ₀ hβ₀ hm hg.1 hg.2 hb hγ hgood⟩

/-- **(c) on the events** (Lemma `a:lem-subdiv`(c), as used by Propositions 3.6–3.7): if
`|ρ^E_g - ρ^D_g| ≤ u` on `K × K`, then a pinned field with both references and length metrics
lies in neither `H↑(D, E; 1 + u/d∗)` nor `H↑(E, D; 1 + u/d∗)`. -/
theorem not_mem_hup_of_abs_sub_le (hD : (rho D g).IsLength) (hE : (rho E g).IsLength)
    (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hg : g ∈ PairRefs D E H₀ σ₀ β₀ m M) {u : ℝ}
    (hdiff : ∀ x ∈ annK d, ∀ y ∈ annK d, |(rho E g).1 (x, y) - (rho D g).1 (x, y)| ≤ u) :
    g ∉ Hup D E (1 + u / subdivD H₀ σ₀ β₀ m M) ∧
      g ∉ Hup E D (1 + u / subdivD H₀ σ₀ β₀ m M) := by
  obtain ⟨h1, h2⟩ := hup_empty_of_supDiff hD hE hH₀ hσ₀ hβ₀ hm hg.1 hg.2 hdiff
  exact ⟨fun ⟨γ, hγ, hbad⟩ => h1 γ hγ hbad, fun ⟨γ, hγ, hbad⟩ => h2 γ hγ hbad⟩

/-- `supDistLU d R F G ≤ u` bounds `|F - G|` pointwise on `B̄_R × B̄_R` (`u ≥ 0`). -/
theorem abs_sub_le_of_supDistLU_le {F G : C(Rd d × Rd d, ℝ)} {R u : ℝ} (hu : 0 ≤ u)
    (h : supDistLU d R F G ≤ ENNReal.ofReal u) {x y : Rd d} (hx : x ∈ closedBall (0 : Rd d) R)
    (hy : y ∈ closedBall (0 : Rd d) R) : |F (x, y) - G (x, y)| ≤ u := by
  have hle : edist (F (x, y)) (G (x, y)) ≤ supDistLU d R F G := by
    unfold supDistLU
    exact le_iSup₂_of_le (x, y) (mk_mem_prod hx hy) le_rfl
  rw [edist_dist, Real.dist_eq] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hu).1 (hle.trans h)

/-- **(c) on the events, `supDistLU` form**: if `supDistLU d R ρ^D_g ρ^E_g ≤ u` with `R ≥ 1`
(so that `K ⊆ B̄_R`) and `u ≥ 0`, then `g ∉ H↑(D, E; 1 + u/d∗)` and `g ∉ H↑(E, D; 1 + u/d∗)` on
the references (both metrics length metrics). -/
theorem not_mem_hup_of_supDistLU_le (hD : (rho D g).IsLength) (hE : (rho E g).IsLength)
    (hH₀ : 0 < H₀) (hσ₀ : 0 < σ₀) (hβ₀ : 0 < β₀) (hm : 0 < m)
    (hg : g ∈ PairRefs D E H₀ σ₀ β₀ m M) {R u : ℝ} (hR : 1 ≤ R) (hu : 0 ≤ u)
    (hsup : supDistLU d R (rho D g).1 (rho E g).1 ≤ ENNReal.ofReal u) :
    g ∉ Hup D E (1 + u / subdivD H₀ σ₀ β₀ m M) ∧
      g ∉ Hup E D (1 + u / subdivD H₀ σ₀ β₀ m M) := by
  have hKR : ∀ x ∈ annK d, x ∈ closedBall (0 : Rd d) R := fun x hx => by
    rw [mem_closedBall, dist_zero_right]
    exact (mem_annK_iff.1 hx).2.trans hR
  refine not_mem_hup_of_abs_sub_le hD hE hH₀ hσ₀ hβ₀ hm hg fun x hx y hy => ?_
  rw [abs_sub_comm]
  exact abs_sub_le_of_supDistLU_le hu hsup (hKR x hx) (hKR y hy)

end Events

end HigherDimLQGContinuity
