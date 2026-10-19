import LQGMetric.Papers.DDDF.S6P28L1C

/-!
# Inverse separated-distance moments, the planar part (Route U, item U13 (a))

Phase B, packet PB-U13 (ledger packet B-9). Mathematical source: the uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statement U13 (a) and Finding `fd:shapes`, with the
corrections S-1 and M-4 of the audit `planning/audits/B0b-ledger-audit.md`. Templates (not
edited): `T20D.piece_of_cross` (`LQGMetric/Papers/DDDF/T20DGeom.lean`), `S6P28L.cross_lower`
(`S6P28L1A.lean`) and `S6P28L.not_mem_box` (`S6P28L1C.lean`); DDDF20 (arXiv:1904.08021 v2),
`tightness.tex` l. 1131–1135 and 1457–1460.

Everything here is deterministic and holds for every weight `f : ℂ → ℝ` (no continuity is used)
and every level `K` (the ledger's `K ≥ 1` is not needed).

* `min_short_le_lfppDOn`: if `x ∈ P = T20.dyBlock K b` and `y ∉ interior (T20D.hatBox K b)`, then
  the whole-plane LFPP distance `lfppDOn ξ f univ x y` is at least the minimum over the four
  short strips `T20D.RS K j`, `j ∈ T20D.shortJ K b`, of their short-way crossing lengths
  (every path from `x` to `y` in `ℂ` has a piece crossing one of them, `T20D.piece_of_cross`).
* `min_short_le_lfppDOn_of_le_norm`: the same when `4 · 2^{-K} ≤ δ ≤ ‖x − y‖`
  (`S6P28L.not_mem_box`).
* `kDelta δ = ⌈log₂(4/δ)⌉₊`, with `4 · 2^{-kDelta δ} ≤ δ` (`four_mul_le_kDelta`) and, for
  `δ ≤ 1`, `2 ≤ kDelta δ` (`two_le_kDelta`) and `2^{kDelta δ} ≤ 8/δ` (`two_pow_kDelta_le`).
* `blockSet K₀ k`: the blocks `b : ℤ × ℤ` of level `k` meeting `K₀`; finite for bounded `K₀`
  (`blockSet_finite`), with at most `C_{K₀} δ^{-2}` blocks at level `kDelta δ` for `δ ≤ 1`
  (`ncard_blockSet_le`); each block has at most four strips (`T20D.card_shortJ_le`), so there
  are at most `4 C_{K₀} δ^{-2}` strips (`card_strips_le`).
* `min_strips_le_lfppDOn` (the form consumed by the (★) packet U15): for `z ∈ K₀` and
  `δ ≤ ‖z − w‖`, the global distance `lfppDOn ξ f univ z w` is at least the `ℝ≥0∞`-minimum
  `⨅ b ∈ blockSet K₀ (kDelta δ), ⨅ j ∈ T20D.shortJ (kDelta δ) b, crossLenIn ξ f (RS …) (RS₁ …)
  (RS₂ …)`. All infima are in `ℝ≥0∞`, where an empty index gives `⊤` (audit S-1).
* `exists_near_of_mem_strip` (`norm_sub_le_of_mem_RS`): every point of a strip of the family lies
  within `8 · 2^{-k}` of `K₀` (≤ 2 for `δ ≤ 1`), where U15 compares the weights.

Helpers (`interior_hatBox`, `mem_dyBlock_floor`, `blockSet_subset`) are in the namespace
`GaussianLQG.Uniform.InvMom`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

/-! ### The planar lemma for one block -/

namespace InvMom

/-- the interior of `\hat P` is the open box of `T20D.piece_of_cross` -/
lemma interior_hatBox (K : ℕ) (b : ℤ × ℤ) :
    interior (T20D.hatBox K b) =
      Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
        Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) := by
  rw [T20D.hatBox, Complex.interior_reProdIm, interior_Icc, interior_Icc]

end InvMom

open InvMom

/-- **The planar part of U13** (ledger U13 (a); DDDF l. 1131–1135, 1457–1460): for every weight
`f`, every `x` in the block `P = T20.dyBlock K b` and every `y` outside the open box `\hat P°`,
`D_f(x, y; ℂ) ≥ min_{j ∈ shortJ K b} L_f(RS K j)`. -/
theorem min_short_le_lfppDOn (ξ : ℝ) (f : ℂ → ℝ) (K : ℕ) (b : ℤ × ℤ) {x y : ℂ}
    (hx : x ∈ T20.dyBlock K b) (hy : y ∉ interior (T20D.hatBox K b)) :
    ⨅ j ∈ T20D.shortJ K b, crossLenIn ξ f (T20D.RS K j) (T20D.RS₁ K j) (T20D.RS₂ K j) ≤
      lfppDOn ξ f univ x y := by
  rw [interior_hatBox] at hy
  refine le_iInf fun G => ?_
  obtain ⟨G, hG, -⟩ := G
  have h0 : G 0 ∈ T20.dyBlock K b := by rw [hG.source]; exact hx
  have h1 : G 1 ∉ Ioo (((b.1 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) ×ℂ
      Ioo (((b.2 : ℝ) - 1) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 2) * (2 : ℝ)⁻¹ ^ K) := by
    rw [hG.target]; exact hy
  obtain ⟨u, v, hu, huv, hv, -, j, hj, hadm⟩ :=
    T20D.piece_of_cross hG ⟨le_rfl, zero_le_one⟩ h0 h1
  calc ⨅ j ∈ T20D.shortJ K b, crossLenIn ξ f (T20D.RS K j) (T20D.RS₁ K j) (T20D.RS₂ K j)
      ≤ crossLenIn ξ f (T20D.RS K j) (T20D.RS₁ K j) (T20D.RS₂ K j) := iInf₂_le j hj
    _ ≤ lfppLen ξ f (subPath G u v) := crossLenIn_le_lfppLen hadm
    _ ≤ lfppLen ξ f G := by
        rw [lfppLen_subPath G huv, lfppLen_eq]
        exact MeasureTheory.lintegral_mono_set (Icc_subset_Icc hu hv)

/-- **The δ-separated form** (ledger U13 (a), last sentence): if `4 · 2^{-K} ≤ δ ≤ ‖x − y‖` and
`x ∈ T20.dyBlock K b`, then `y ∉ \hat P°` (`S6P28L.not_mem_box`), so the bound of
`min_short_le_lfppDOn` holds. -/
theorem min_short_le_lfppDOn_of_le_norm (ξ : ℝ) (f : ℂ → ℝ) {K : ℕ} {δ : ℝ}
    (hKδ : 4 * (2 : ℝ)⁻¹ ^ K ≤ δ) (b : ℤ × ℤ) {x y : ℂ} (hx : x ∈ T20.dyBlock K b)
    (hxy : δ ≤ ‖x - y‖) :
    ⨅ j ∈ T20D.shortJ K b, crossLenIn ξ f (T20D.RS K j) (T20D.RS₁ K j) (T20D.RS₂ K j) ≤
      lfppDOn ξ f univ x y :=
  min_short_le_lfppDOn ξ f K b hx (by
    rw [interior_hatBox]; exact S6P28L.not_mem_box hx (hKδ.trans hxy))

/-! ### The level `k(δ)` -/

/-- the level `k(δ) = ⌈log₂(4/δ)⌉₊` of the strips used at separation `δ` (ledger U13 (b)) -/
def kDelta (δ : ℝ) : ℕ := ⌈Real.logb 2 (4 / δ)⌉₊

/-- `4 · 2^{-k(δ)} ≤ δ` -/
lemma four_mul_le_kDelta {δ : ℝ} (hδ : 0 < δ) : 4 * (2 : ℝ)⁻¹ ^ kDelta δ ≤ δ := by
  have h1 : Real.logb 2 (4 / δ) ≤ (kDelta δ : ℝ) := Nat.le_ceil _
  have h2 : 4 / δ ≤ (2 : ℝ) ^ kDelta δ := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).1 h1
  have h3 : 4 ≤ (2 : ℝ) ^ kDelta δ * δ := (div_le_iff₀ hδ).1 h2
  have h4 : (0 : ℝ) < (2 : ℝ) ^ kDelta δ := by positivity
  rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ h4]
  linarith

/-- `2 ≤ k(δ)` for `δ ≤ 1` (audit M-4) -/
lemma two_le_kDelta {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 2 ≤ kDelta δ := by
  have h4 : (4 : ℝ) ≤ 4 / δ := by rw [le_div_iff₀ hδ]; linarith
  have h1 : (2 : ℝ) ≤ Real.logb 2 (4 / δ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    norm_num; exact h4
  have h2 : (2 : ℝ) ≤ (kDelta δ : ℝ) := h1.trans (Nat.le_ceil _)
  exact_mod_cast h2

/-- `2^{k(δ)} ≤ 8/δ` for `δ ≤ 4` -/
lemma two_pow_kDelta_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 4) : (2 : ℝ) ^ kDelta δ ≤ 8 / δ := by
  have h4 : (1 : ℝ) ≤ 4 / δ := by rw [le_div_iff₀ hδ]; linarith
  have h0 : 0 ≤ Real.logb 2 (4 / δ) := Real.logb_nonneg (by norm_num) h4
  have h1 : (kDelta δ : ℝ) < Real.logb 2 (4 / δ) + 1 := Nat.ceil_lt_add_one h0
  have h2 : (2 : ℝ) ^ (kDelta δ : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (4 / δ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num), Real.rpow_one,
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at h2
  calc (2 : ℝ) ^ kDelta δ ≤ 4 / δ * 2 := h2
    _ = 8 / δ := by ring

/-! ### Blocks meeting a set -/

/-- the blocks `b : ℤ × ℤ` of level `k` that meet `K₀` (ledger U13 (b); audit S-1) -/
def blockSet (K₀ : Set ℂ) (k : ℕ) : Set (ℤ × ℤ) := {b | (T20.dyBlock k b ∩ K₀).Nonempty}

namespace InvMom

/-- every point lies in the block of level `K` indexed by the integer parts of its coordinates -/
lemma mem_dyBlock_floor (K : ℕ) (z : ℂ) :
    z ∈ T20.dyBlock K (⌊z.re / (2 : ℝ)⁻¹ ^ K⌋, ⌊z.im / (2 : ℝ)⁻¹ ^ K⌋) := by
  have hh : (0 : ℝ) < (2 : ℝ)⁻¹ ^ K := by positivity
  have key : ∀ t : ℝ, (⌊t / (2 : ℝ)⁻¹ ^ K⌋ : ℝ) * (2 : ℝ)⁻¹ ^ K ≤ t ∧
      t ≤ ((⌊t / (2 : ℝ)⁻¹ ^ K⌋ : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K := fun t =>
    ⟨(le_div_iff₀ hh).1 (Int.floor_le _), ((div_lt_iff₀ hh).1 (Int.lt_floor_add_one _)).le⟩
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc]
  exact ⟨key z.re, key z.im⟩

/-- the blocks of level `k` meeting a set of points of norm `≤ R` have indices in
`[-N, N]²`, `N = ⌈R 2^k⌉₊ + 1` -/
lemma blockSet_subset {K₀ : Set ℂ} {R : ℝ} (hR : ∀ z ∈ K₀, ‖z‖ ≤ R) (k : ℕ) :
    blockSet K₀ k ⊆ ↑(Finset.Icc (-((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ)) ((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ) ×ˢ
      Finset.Icc (-((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ)) ((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ)) := by
  intro b hb
  obtain ⟨z, hzb, hzK⟩ := hb
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc] at hzb
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hzb
  have hzR := hR z hzK
  have hre : |z.re| ≤ R := (Complex.abs_re_le_norm z).trans hzR
  have him : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hzR
  have hh : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  have h2 : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by rw [← mul_pow]; norm_num
  have hN : R * 2 ^ k + 1 ≤ ((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast; linarith [Nat.le_ceil (R * 2 ^ k)]
  -- `t ∈ [i h, (i+1) h]`, `|t| ≤ R` give `|i| ≤ R 2^k + 1`
  have key : ∀ (i : ℤ) (t : ℝ), (i : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ t →
      t ≤ ((i : ℝ) + 1) * (2 : ℝ)⁻¹ ^ k → |t| ≤ R →
      -((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ) ≤ i ∧ i ≤ ((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ) := by
    intro i t h1 h2' ht
    rw [abs_le] at ht
    have e1 : (i : ℝ) ≤ R * 2 ^ k := by
      have : (i : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ R * (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k := by
        rw [mul_assoc, h2, mul_one]; linarith
      exact le_of_mul_le_mul_right this hh
    have e2 : -(R * 2 ^ k) - 1 ≤ (i : ℝ) := by
      have : (-(R * 2 ^ k) - 1 + 1) * (2 : ℝ)⁻¹ ^ k ≤ ((i : ℝ) + 1) * (2 : ℝ)⁻¹ ^ k := by
        have e : (-(R * 2 ^ k) - 1 + 1) * (2 : ℝ)⁻¹ ^ k = -R := by
          rw [sub_add_cancel, neg_mul, mul_assoc, h2, mul_one]
        rw [e]; linarith
      linarith [le_of_mul_le_mul_right this hh]
    constructor
    · have : (-((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ) : ℝ) ≤ (i : ℝ) := by push_cast at hN ⊢; linarith
      exact_mod_cast this
    · have : (i : ℝ) ≤ (((⌈R * 2 ^ k⌉₊ + 1 : ℕ) : ℤ) : ℝ) := by push_cast at hN ⊢; linarith
      exact_mod_cast this
  obtain ⟨c1, c2⟩ := key b.1 z.re a1 a2 hre
  obtain ⟨c3, c4⟩ := key b.2 z.im b1 b2 him
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, mem_Icc]
  exact ⟨⟨c1, c2⟩, c3, c4⟩

end InvMom

/-- the blocks of level `k` meeting a bounded set form a finite set -/
lemma blockSet_finite {K₀ : Set ℂ} (hK₀ : Bornology.IsBounded K₀) (k : ℕ) :
    (blockSet K₀ k).Finite := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK₀
  exact (Finset.finite_toSet _).subset (blockSet_subset hR k)

/-- **Cardinality** (ledger U13 (b)): for bounded `K₀` there is `C_{K₀}` with at most
`C_{K₀} δ^{-2}` blocks of level `k(δ)` meeting `K₀`, for every `δ ∈ (0, 1]`; each block has at
most four strips (`T20D.card_shortJ_le`). -/
theorem ncard_blockSet_le {K₀ : Set ℂ} (hK₀ : Bornology.IsBounded K₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ((blockSet K₀ (kDelta δ)).ncard : ℝ) ≤ C * δ⁻¹ ^ 2 := by
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.1 hK₀
  set R : ℝ := max R₀ 0 with hR_def
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ z ∈ K₀, ‖z‖ ≤ R := fun z hz => (hR₀ z hz).trans (le_max_left _ _)
  refine ⟨(16 * R + 5) ^ 2, by positivity, fun δ hδ hδ1 => ?_⟩
  set k := kDelta δ
  set N : ℕ := ⌈R * 2 ^ k⌉₊ + 1 with hN_def
  have hsub := blockSet_subset hR k
  have hcard : (blockSet K₀ k).ncard ≤ (2 * N + 1) ^ 2 := by
    refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset, Finset.card_product, Int.card_Icc, ← sq]
    gcongr
    omega
  have hk : (2 : ℝ) ^ k ≤ 8 / δ := two_pow_kDelta_le hδ (by linarith)
  have hNle : (N : ℝ) ≤ R * (8 / δ) + 2 := by
    rw [hN_def]; push_cast
    have := Nat.ceil_lt_add_one (show 0 ≤ R * 2 ^ k by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hk hR0]
  have hδinv : 1 ≤ δ⁻¹ := one_le_inv_iff₀.2 ⟨hδ, hδ1⟩
  have h2N : (2 * (N : ℝ) + 1) ≤ (16 * R + 5) * δ⁻¹ := by
    have e : R * (8 / δ) = 8 * R * δ⁻¹ := by rw [div_eq_mul_inv]; ring
    rw [e] at hNle
    nlinarith
  calc ((blockSet K₀ k).ncard : ℝ) ≤ ((2 * N + 1) ^ 2 : ℕ) := by exact_mod_cast hcard
    _ = (2 * (N : ℝ) + 1) ^ 2 := by push_cast; ring
    _ ≤ ((16 * R + 5) * δ⁻¹) ^ 2 := by gcongr
    _ = (16 * R + 5) ^ 2 * δ⁻¹ ^ 2 := by ring

/-- **Number of strips** (ledger U13 (b): at most `C_{K₀} δ^{-2}` strips): for bounded `K₀` the
strips `RS (k δ) j`, `j ∈ shortJ (k δ) b`, `b ∈ blockSet K₀ (k δ)`, number at most
`C_{K₀} δ^{-2}` for every `δ ∈ (0, 1]`. -/
theorem card_strips_le {K₀ : Set ℂ} (hK₀ : Bornology.IsBounded K₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ((∑ b ∈ (blockSet_finite hK₀ (kDelta δ)).toFinset, (T20D.shortJ (kDelta δ) b).card : ℕ) : ℝ)
        ≤ C * δ⁻¹ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := ncard_blockSet_le hK₀
  refine ⟨4 * C, by positivity, fun δ hδ hδ1 => ?_⟩
  set hfin := blockSet_finite hK₀ (kDelta δ)
  have h1 : ∑ b ∈ hfin.toFinset, (T20D.shortJ (kDelta δ) b).card ≤ hfin.toFinset.card * 4 := by
    rw [← smul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun b _ => T20D.card_shortJ_le _ b
  have h2 : (hfin.toFinset.card : ℝ) = ((blockSet K₀ (kDelta δ)).ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
  calc ((∑ b ∈ hfin.toFinset, (T20D.shortJ (kDelta δ) b).card : ℕ) : ℝ)
      ≤ ((hfin.toFinset.card * 4 : ℕ) : ℝ) := by exact_mod_cast h1
    _ = 4 * ((blockSet K₀ (kDelta δ)).ncard : ℝ) := by push_cast; rw [h2]; ring
    _ ≤ 4 * (C * δ⁻¹ ^ 2) := by gcongr; exact hC δ hδ hδ1
    _ = 4 * C * δ⁻¹ ^ 2 := by ring

/-- **The strips stay near their block**: a point of a strip `RS K j`, `j ∈ shortJ K b`, is within
`8 · 2^{-K}` of every point of the block `T20.dyBlock K b` (for the weight comparison of U15). -/
lemma norm_sub_le_of_mem_RS {K : ℕ} {b : ℤ × ℤ} {j : Circle × ℂ} (hj : j ∈ T20D.shortJ K b)
    {x z : ℂ} (hx : x ∈ T20D.RS K j) (hz : z ∈ T20.dyBlock K b) :
    ‖x - z‖ ≤ 8 * (2 : ℝ)⁻¹ ^ K := by
  set h : ℝ := (2 : ℝ)⁻¹ ^ K with hh_def
  have hh : 0 < h := by positivity
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y.re ∈ Icc (0 : ℝ) 1 ∧ y.im ∈ Icc (0 : ℝ) 3 := by
    simpa [MarkedRect.toSet, rectAB, Complex.mem_reProdIm] using hy
  obtain ⟨⟨y1, y2⟩, y3, y4⟩ := hy'
  -- the similarity moves `y` by at most `4h` from the marked corner `j.2`
  have h1 : ‖T20B.mot K j.1 j.2 y - j.2‖ ≤ 4 * h := by
    rw [T20D.mot_apply, add_sub_cancel_right, norm_mul, Circle.norm_coe, one_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    have hn := Complex.norm_le_abs_re_add_abs_im y
    rw [abs_of_nonneg y1, abs_of_nonneg y3] at hn
    nlinarith
  -- the corner `j.2` is within `4h` of every point of the block
  have h2 : ‖j.2 - z‖ ≤ 4 * h := by
    simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc] at hz
    obtain ⟨⟨z1, z2⟩, z3, z4⟩ := hz
    have key : ∀ w : ℂ, |w.re| ≤ 2 * h → |w.im| ≤ 2 * h → ‖w‖ ≤ 4 * h := fun w hr hi =>
      (Complex.norm_le_abs_re_add_abs_im w).trans (by linarith)
    simp only [T20D.shortJ, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl <;>
      refine key _ ?_ ?_ <;> simp only [Complex.sub_re, Complex.sub_im] <;>
      rw [abs_le] <;> constructor <;> linarith
  calc ‖T20B.mot K j.1 j.2 y - z‖ = ‖(T20B.mot K j.1 j.2 y - j.2) + (j.2 - z)‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖T20B.mot K j.1 j.2 y - j.2‖ + ‖j.2 - z‖ := norm_add_le _ _
    _ ≤ 8 * h := by linarith

/-- every point of a strip of the family is within `8 · 2^{-k}` of `K₀` -/
theorem exists_near_of_mem_strip {K₀ : Set ℂ} {k : ℕ} {b : ℤ × ℤ} (hb : b ∈ blockSet K₀ k)
    {j : Circle × ℂ} (hj : j ∈ T20D.shortJ k b) {x : ℂ} (hx : x ∈ T20D.RS k j) :
    ∃ z ∈ K₀, ‖x - z‖ ≤ 8 * (2 : ℝ)⁻¹ ^ k :=
  let ⟨z, hzb, hzK⟩ := hb
  ⟨z, hzK, norm_sub_le_of_mem_RS hj hx hzb⟩

/-! ### The planar lemma for the strip family -/

/-- **The planar part for the family of strips** (U13 (a) in the form consumed by U15): for every
weight `f`, `δ > 0`, `z ∈ K₀` and `w` with `δ ≤ ‖z − w‖`, the global LFPP distance
`D_f(z, w; ℂ)` is at least the `ℝ≥0∞`-minimum of the short-way crossing lengths of the strips
`RS (k δ) j`, `j ∈ shortJ (k δ) b`, `b ∈ blockSet K₀ (k δ)`. -/
theorem min_strips_le_lfppDOn (ξ : ℝ) (f : ℂ → ℝ) (K₀ : Set ℂ) {δ : ℝ} (hδ : 0 < δ) {z w : ℂ}
    (hz : z ∈ K₀) (hzw : δ ≤ ‖z - w‖) :
    ⨅ b ∈ blockSet K₀ (kDelta δ), ⨅ j ∈ T20D.shortJ (kDelta δ) b,
        crossLenIn ξ f (T20D.RS (kDelta δ) j) (T20D.RS₁ (kDelta δ) j) (T20D.RS₂ (kDelta δ) j) ≤
      lfppDOn ξ f univ z w := by
  set b : ℤ × ℤ := (⌊z.re / (2 : ℝ)⁻¹ ^ kDelta δ⌋, ⌊z.im / (2 : ℝ)⁻¹ ^ kDelta δ⌋)
  have hzb : z ∈ T20.dyBlock (kDelta δ) b := mem_dyBlock_floor _ z
  have hb : b ∈ blockSet K₀ (kDelta δ) := ⟨z, hzb, hz⟩
  exact (iInf₂_le b hb).trans
    (min_short_le_lfppDOn_of_le_norm ξ f (four_mul_le_kDelta hδ) b hzb hzw)

end Uniform
end GaussianLQG
