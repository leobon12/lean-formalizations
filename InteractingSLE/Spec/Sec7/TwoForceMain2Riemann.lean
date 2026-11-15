/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoForceMain2Brownian
import MathFin.Probability.Martingales.UnifIntegrableL2

/-!
# The driving noise in the germ filtration: left-endpoint sums (Aux. lemma 47, (GB4))

Packet PROVE-SEC7-A3 (specification §7.1, Aux. lemma 47, `source/spec/p193-240.md` L653–L690,
pp. 227–229). After the hull germ is retained (`𝒢 ⊇ 𝓕`), the harmonic mean `M_t(z)` at a point above the
hulls is a `𝒢`-martingale (GB2); in the own filtration `dM = k dB` with `k = 2 Im (g_t(z) − W_t)⁻¹`
continuous and nonzero (GB3). The source then forms the stochastic integral `∫ k⁻¹ dM` (GB4): "form
left-endpoint sums for the integral against `M`. The same sums converge in probability to the stochastic
integral in either filtration; in the own filtration the identity (GB3) identifies their limit with the
stopped Brownian motion." This file proves that step without a stochastic integral, from the brackets of
(GB3) in martingale form (as `Spec/Ito/ExhaustMart.lean` provides them: `𝔥(z)`, `𝔥(z)² − ∫ k²`,
`𝔥(z) B − ∫ k` are martingales up to the localizing times):

* `integral_sq_cell_eq`, `integral_sq_sum_cells_eq`: the defects `ΔYᵢ − k(tᵢ)⁻¹ ΔXᵢ` of the left-endpoint
  sums are orthogonal, with `E[defect²] = E ∫_{tᵢ}^{tᵢ₊₁} e (1 − k/k(tᵢ))²`;
* `tendsto_sum_integral_freeze`: these tend to zero (uniform continuity of `k`);
* `martingale_of_bracket_freeze` (**(GB4)**): hence `Y` (the stopped `B`) is a `𝒢`-martingale whenever
  `X` (the stopped `M`) is;
* `martingale_of_tendsto_of_sq_bound`: removal of the localization (Vitali, with `E[Y_t²] ≤ t`);
* `isFilteredBrownianReal_of_localized_bracket` (**Aux. lemma 47, Brownian conclusion, abstract form**):
  with `isFilteredBrownianReal_of_martingale_of_null` (`TwoForceMain2Brownian`, Lévy's characterization),
  `B` is a Brownian motion in `𝒢`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- A weight that is `𝓕ₚ`-measurable and almost surely bounded, times a martingale increment, has
expectation zero. -/
lemma integral_mul_increment_eq_zero [IsFiniteMeasure P] {Z : ℝ≥0 → Ω → ℝ}
    (hZ : Martingale Z 𝓕 P) {p q : ℝ≥0} (hpq : p ≤ q) {g : Ω → ℝ}
    (hg : StronglyMeasurable[𝓕 p] g) {C : ℝ} (hC : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    ∫ ω, g ω * (Z q ω - Z p ω) ∂P = 0 := by
  have hgm : AEStronglyMeasurable g P := (hg.mono (𝓕.le p)).aestronglyMeasurable
  have hbdd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C := hC.mono fun ω h => by rw [Real.norm_eq_abs]; exact h
  have hintq : Integrable (g * Z q) P := (hZ.integrable q).bdd_mul hgm hbdd
  have hintp : Integrable (g * Z p) P := (hZ.integrable p).bdd_mul hgm hbdd
  have hcond := condExp_mul_of_stronglyMeasurable_left (m := 𝓕 p) hg hintq (hZ.integrable q)
  have h1 : ∫ ω, (g * Z q) ω ∂P = ∫ ω, (g * Z p) ω ∂P := by
    rw [← integral_condExp (𝓕.le p)]
    refine integral_congr_ae ?_
    filter_upwards [hcond, hZ.condExp_ae_eq hpq] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, Pi.mul_apply]
  have hsub : (fun ω => g ω * (Z q ω - Z p ω)) = fun ω => (g * Z q) ω - (g * Z p) ω := by
    funext ω; simp only [Pi.mul_apply]; ring
  rw [hsub, integral_sub hintq hintp, h1, sub_self]

lemma integrable_mul_increment {Z : ℝ≥0 → Ω → ℝ} (hZ : Martingale Z 𝓕 P) (p q : ℝ≥0)
    {g : Ω → ℝ} (hg : AEStronglyMeasurable g P) {C : ℝ} (hC : ∀ᵐ ω ∂P, |g ω| ≤ C) :
    Integrable (fun ω => g ω * (Z q ω - Z p ω)) P :=
  ((hZ.integrable q).sub (hZ.integrable p)).bdd_mul hg
    (hC.mono fun ω h => by rw [Real.norm_eq_abs]; exact h)

/-- **One cell of the left-endpoint approximation.** Let `X, Y` be bounded `𝓕`-martingales whose
brackets have densities: `X² − GXX`, `XY − GXY`, `Y² − GYY` are martingales. For an `𝓕ₚ`-measurable bounded
weight `l`, `E[(ΔY − l ΔX)²] = E[ΔGYY − 2 l ΔGXY + l² ΔGXX]` over a cell `[p, q]`. -/
lemma integral_sq_cell_eq [IsFiniteMeasure P] {X Y GXX GXY GYY : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓕 P) (hY : Martingale Y 𝓕 P)
    (hXX : Martingale (fun t ω => X t ω ^ 2 - GXX t ω) 𝓕 P)
    (hXY : Martingale (fun t ω => X t ω * Y t ω - GXY t ω) 𝓕 P)
    (hYY : Martingale (fun t ω => Y t ω ^ 2 - GYY t ω) 𝓕 P)
    {K : ℝ} (hXb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (hYb : ∀ t, ∀ᵐ ω ∂P, |Y t ω| ≤ K)
    {p q : ℝ≥0} (hpq : p ≤ q) {l : Ω → ℝ} (hl : StronglyMeasurable[𝓕 p] l) {L : ℝ}
    (hlb : ∀ ω, |l ω| ≤ L) :
    ∫ ω, ((Y q ω - Y p ω) - l ω * (X q ω - X p ω)) ^ 2 ∂P
      = ∫ ω, ((GYY q ω - GYY p ω) - 2 * l ω * (GXY q ω - GXY p ω)
          + l ω ^ 2 * (GXX q ω - GXX p ω)) ∂P := by
  have hlae : ∀ᵐ ω ∂P, |l ω| ≤ L := Eventually.of_forall hlb
  have hXp := (hX.stronglyAdapted p)
  have hYp := (hY.stronglyAdapted p)
  -- bounded weights at `p`
  have hb1 : ∀ᵐ ω ∂P, |l ω ^ 2 * X p ω| ≤ L ^ 2 * K := by
    filter_upwards [hXb p] with ω hω
    rw [abs_mul, abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hlb ω) 2) hω (abs_nonneg _)
      (by nlinarith [abs_nonneg (l ω), hlb ω])
  have hb2 : ∀ᵐ ω ∂P, |l ω * X p ω| ≤ L * K := by
    filter_upwards [hXb p] with ω hω
    rw [abs_mul]
    exact mul_le_mul (hlb ω) hω (abs_nonneg _) ((abs_nonneg _).trans (hlb ω))
  have hb3 : ∀ᵐ ω ∂P, |l ω * Y p ω| ≤ L * K := by
    filter_upwards [hYb p] with ω hω
    rw [abs_mul]
    exact mul_le_mul (hlb ω) hω (abs_nonneg _) ((abs_nonneg _).trans (hlb ω))
  have hb4 : ∀ᵐ ω ∂P, |Y p ω| ≤ K := hYb p
  have hb5 : ∀ᵐ ω ∂P, |l ω ^ 2| ≤ L ^ 2 := Eventually.of_forall fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hlb ω) 2
  have e1 : ∫ ω, l ω ^ 2 * X p ω * (X q ω - X p ω) ∂P = 0 :=
    integral_mul_increment_eq_zero hX hpq ((hl.pow 2).mul hXp) hb1
  have e2 : ∫ ω, l ω * X p ω * (Y q ω - Y p ω) ∂P = 0 :=
    integral_mul_increment_eq_zero hY hpq (hl.mul hXp) hb2
  have e3 : ∫ ω, l ω * Y p ω * (X q ω - X p ω) ∂P = 0 :=
    integral_mul_increment_eq_zero hX hpq (hl.mul hYp) hb3
  have e4 : ∫ ω, Y p ω * (Y q ω - Y p ω) ∂P = 0 := integral_mul_increment_eq_zero hY hpq hYp hb4
  have e5 : ∫ ω, l ω ^ 2 * ((X q ω ^ 2 - GXX q ω) - (X p ω ^ 2 - GXX p ω)) ∂P = 0 :=
    integral_mul_increment_eq_zero hXX hpq (hl.pow 2) hb5
  have e6 : ∫ ω, l ω * ((X q ω * Y q ω - GXY q ω) - (X p ω * Y p ω - GXY p ω)) ∂P = 0 :=
    integral_mul_increment_eq_zero hXY hpq hl hlae
  have e7 : ∫ ω, 1 * ((Y q ω ^ 2 - GYY q ω) - (Y p ω ^ 2 - GYY p ω)) ∂P = 0 :=
    integral_mul_increment_eq_zero hYY hpq stronglyMeasurable_const
      (Eventually.of_forall fun ω => le_refl |(1 : ℝ)|)
  have hlm : AEStronglyMeasurable l P := (hl.mono (𝓕.le p)).aestronglyMeasurable
  have hXpm : AEStronglyMeasurable (X p) P := (hXp.mono (𝓕.le p)).aestronglyMeasurable
  have hYpm : AEStronglyMeasurable (Y p) P := (hYp.mono (𝓕.le p)).aestronglyMeasurable
  have i1 : Integrable (fun ω => l ω ^ 2 * X p ω * (X q ω - X p ω)) P :=
    integrable_mul_increment hX p q ((hlm.pow 2).mul hXpm) hb1
  have i2 : Integrable (fun ω => l ω * X p ω * (Y q ω - Y p ω)) P :=
    integrable_mul_increment hY p q (hlm.mul hXpm) hb2
  have i3 : Integrable (fun ω => l ω * Y p ω * (X q ω - X p ω)) P :=
    integrable_mul_increment hX p q (hlm.mul hYpm) hb3
  have i4 : Integrable (fun ω => Y p ω * (Y q ω - Y p ω)) P :=
    integrable_mul_increment hY p q hYpm hb4
  have i5 : Integrable (fun ω => l ω ^ 2 * ((X q ω ^ 2 - GXX q ω) - (X p ω ^ 2 - GXX p ω))) P :=
    integrable_mul_increment hXX p q (hlm.pow 2) hb5
  have i6 : Integrable
      (fun ω => l ω * ((X q ω * Y q ω - GXY q ω) - (X p ω * Y p ω - GXY p ω))) P :=
    integrable_mul_increment hXY p q hlm hlae
  have i7 : Integrable (fun ω => 1 * ((Y q ω ^ 2 - GYY q ω) - (Y p ω ^ 2 - GYY p ω))) P :=
    integrable_mul_increment hYY p q (aestronglyMeasurable_const (b := (1 : ℝ)))
      (Eventually.of_forall fun ω => le_refl |(1 : ℝ)|)
  -- the left side is integrable (bounded)
  have hLb : ∀ᵐ ω ∂P, ‖((Y q ω - Y p ω) - l ω * (X q ω - X p ω)) ^ 2‖
      ≤ (2 * K + L * (2 * K)) ^ 2 := by
    filter_upwards [hXb p, hXb q, hYb p, hYb q] with ω h1 h2 h3 h4
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |(Y q ω - Y p ω) - l ω * (X q ω - X p ω)|
        ≤ |Y q ω - Y p ω| + |l ω| * |X q ω - X p ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 2 * K + L * (2 * K) := by
          have a1 : |Y q ω - Y p ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          have a2 : |X q ω - X p ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          gcongr
          · exact (abs_nonneg _).trans (hlb ω)
          · exact hlb ω
  have hLi : Integrable (fun ω => ((Y q ω - Y p ω) - l ω * (X q ω - X p ω)) ^ 2) P := by
    refine Integrable.of_bound ?_ _ hLb
    exact (((hY.integrable q).sub (hY.integrable p)).sub
      (((hX.integrable q).sub (hX.integrable p)).bdd_mul hlm
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hlb ω))).aestronglyMeasurable.pow 2
  set combo : Ω → ℝ := fun ω =>
    1 * ((Y q ω ^ 2 - GYY q ω) - (Y p ω ^ 2 - GYY p ω))
      - 2 * (Y p ω * (Y q ω - Y p ω))
      - 2 * (l ω * ((X q ω * Y q ω - GXY q ω) - (X p ω * Y p ω - GXY p ω)))
      + 2 * (l ω * X p ω * (Y q ω - Y p ω))
      + 2 * (l ω * Y p ω * (X q ω - X p ω))
      + (l ω ^ 2 * ((X q ω ^ 2 - GXX q ω) - (X p ω ^ 2 - GXX p ω)))
      - 2 * (l ω ^ 2 * X p ω * (X q ω - X p ω)) with hcombo
  have hci : Integrable combo P :=
    ((((((i7.sub (i4.const_mul 2)).sub (i6.const_mul 2)).add (i2.const_mul 2)).add
      (i3.const_mul 2)).add i5).sub (i1.const_mul 2))
  have hc0 : ∫ ω, combo ω ∂P = 0 := by
    simp only [hcombo]
    rw [integral_sub _ (i1.const_mul 2), integral_add _ i5, integral_add _ (i3.const_mul 2),
      integral_add _ (i2.const_mul 2), integral_sub _ (i6.const_mul 2),
      integral_sub i7 (i4.const_mul 2)]
    · simp only [integral_const_mul]
      rw [integral_const_mul] at e7
      rw [e1, e2, e3, e4, e5, e6, e7]
      ring
    all_goals first
      | exact (i7.sub (i4.const_mul 2))
      | exact ((i7.sub (i4.const_mul 2)).sub (i6.const_mul 2))
      | exact (((i7.sub (i4.const_mul 2)).sub (i6.const_mul 2)).add (i2.const_mul 2))
      | exact ((((i7.sub (i4.const_mul 2)).sub (i6.const_mul 2)).add (i2.const_mul 2)).add
          (i3.const_mul 2))
      | exact (((((i7.sub (i4.const_mul 2)).sub (i6.const_mul 2)).add (i2.const_mul 2)).add
          (i3.const_mul 2)).add i5)
  have hpt : (fun ω => (GYY q ω - GYY p ω) - 2 * l ω * (GXY q ω - GXY p ω)
      + l ω ^ 2 * (GXX q ω - GXX p ω))
      = fun ω => ((Y q ω - Y p ω) - l ω * (X q ω - X p ω)) ^ 2 - combo ω := by
    funext ω; simp only [hcombo]; ring
  rw [hpt, integral_sub hLi hci, hc0, sub_zero]

/-- **Orthogonality of the cells.** For bounded martingales `X, Y` and bounded weights `lᵢ`
measurable at the left endpoints of a monotone partition, the defects
`Dᵢ = ΔYᵢ − lᵢ ΔXᵢ` are orthogonal: `E[(∑ᵢ Dᵢ)²] = ∑ᵢ E[Dᵢ²]`. -/
lemma integral_sq_sum_cells_eq [IsFiniteMeasure P] {X Y : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓕 P) (hY : Martingale Y 𝓕 P)
    {K : ℝ} (hXb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (hYb : ∀ t, ∀ᵐ ω ∂P, |Y t ω| ≤ K)
    {π : ℕ → ℝ≥0} (hπ : Monotone π) {l : ℕ → Ω → ℝ} (hl : ∀ i, StronglyMeasurable[𝓕 (π i)] (l i))
    {L : ℝ} (hlb : ∀ i ω, |l i ω| ≤ L) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n,
        ((Y (π (i + 1)) ω - Y (π i) ω) - l i ω * (X (π (i + 1)) ω - X (π i) ω))) ^ 2 ∂P
      = ∑ i ∈ Finset.range n,
        ∫ ω, ((Y (π (i + 1)) ω - Y (π i) ω) - l i ω * (X (π (i + 1)) ω - X (π i) ω)) ^ 2 ∂P := by
  set D : ℕ → Ω → ℝ := fun i ω =>
    (Y (π (i + 1)) ω - Y (π i) ω) - l i ω * (X (π (i + 1)) ω - X (π i) ω) with hD
  have hDs : ∀ i, StronglyMeasurable[𝓕 (π (i + 1))] (D i) := fun i =>
    ((hY.stronglyAdapted _).sub ((hY.stronglyAdapted _).mono (𝓕.mono (hπ (Nat.le_succ i))))).sub
      (((hl i).mono (𝓕.mono (hπ (Nat.le_succ i)))).mul ((hX.stronglyAdapted _).sub
        ((hX.stronglyAdapted _).mono (𝓕.mono (hπ (Nat.le_succ i))))))
  have hDb : ∀ i, ∀ᵐ ω ∂P, |D i ω| ≤ 2 * K + L * (2 * K) := fun i => by
    filter_upwards [hXb (π i), hXb (π (i + 1)), hYb (π i), hYb (π (i + 1))] with ω h1 h2 h3 h4
    calc |D i ω| ≤ |Y (π (i + 1)) ω - Y (π i) ω| + |l i ω| * |X (π (i + 1)) ω - X (π i) ω| := by
          simp only [hD]; rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 2 * K + L * (2 * K) := by
          have a1 : |Y (π (i + 1)) ω - Y (π i) ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          have a2 : |X (π (i + 1)) ω - X (π i) ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          have hL0 : 0 ≤ L := (abs_nonneg _).trans (hlb i ω)
          gcongr
          exact hlb i ω
  have hDm : ∀ i, AEStronglyMeasurable (D i) P := fun i =>
    ((hDs i).mono (𝓕.le _)).aestronglyMeasurable
  have hDDi : ∀ i j, Integrable (fun ω => D i ω * D j ω) P := fun i j =>
    Integrable.of_bound ((hDm i).mul (hDm j)) ((2 * K + L * (2 * K)) * (2 * K + L * (2 * K)))
      (by
        filter_upwards [hDb i, hDb j] with ω h1 h2
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  -- the cross terms vanish
  have hcross : ∀ i j, i < j → ∫ ω, D i ω * D j ω ∂P = 0 := by
    intro i j hij
    have hle : π (i + 1) ≤ π j := hπ (Nat.succ_le_of_lt hij)
    have hDj : StronglyMeasurable[𝓕 (π j)] (D i) := (hDs i).mono (𝓕.mono hle)
    have e1 := integral_mul_increment_eq_zero hY (hπ (Nat.le_succ j)) hDj (hDb i)
    have e2 := integral_mul_increment_eq_zero hX (hπ (Nat.le_succ j)) (hDj.mul (hl j))
      (C := (2 * K + L * (2 * K)) * L) (by
        filter_upwards [hDb i] with ω h1
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul h1 (hlb j ω) (abs_nonneg _) ((abs_nonneg _).trans h1))
    have i1 := integrable_mul_increment hY (π j) (π (j + 1)) (hDm i) (hDb i)
    have i2 := integrable_mul_increment hX (π j) (π (j + 1)) ((hDm i).mul
      ((hl j).mono (𝓕.le _)).aestronglyMeasurable) (C := (2 * K + L * (2 * K)) * L) (by
        filter_upwards [hDb i] with ω h1
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul h1 (hlb j ω) (abs_nonneg _) ((abs_nonneg _).trans h1))
    have hpt : (fun ω => D i ω * D j ω) = fun ω => D i ω * (Y (π (j + 1)) ω - Y (π j) ω)
        - (D i * l j) ω * (X (π (j + 1)) ω - X (π j) ω) := by
      funext ω; simp only [hD, Pi.mul_apply]; ring
    rw [hpt, integral_sub i1 i2, e1, e2, sub_zero]
  have hsq : ∀ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, D i ω * D j ω := fun ω => by
    rw [sq, Finset.sum_mul_sum]
  show ∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P = ∑ i ∈ Finset.range n, ∫ ω, D i ω ^ 2 ∂P
  simp_rw [hsq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hDDi i j]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ fun j _ => hDDi i j]
  rw [Finset.sum_eq_single i]
  · simp only [sq]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [show (fun ω => D i ω * D j ω) = fun ω => D j ω * D i ω from
        funext fun ω => mul_comm _ _]
      exact hcross j i h
    · exact hcross i j h
  · intro h; exact absurd hi h

/-- The uniform partition points of `[s, t]` as real numbers. -/
lemma coe_unifPartIcc_succ_sub (s t : ℝ≥0) (hst : s ≤ t) (n i : ℕ) :
    ((MathFin.unifPartIcc s t n (i + 1) : ℝ≥0) : ℝ) - (MathFin.unifPartIcc s t n i : ℝ≥0)
      = ((t : ℝ) - s) / n := by
  simp only [MathFin.unifPartIcc, NNReal.coe_add]
  rw [add_sub_add_left_eq_sub, MathFin.unifPart_succ_sub, NNReal.coe_sub hst]

/-- **Left-endpoint freezing of a continuous coefficient is asymptotically exact.** For a continuous
`k` with `c ≤ |k|` and a measurable weight `0 ≤ e ≤ 1`, along the uniform partitions of `[s, t]`,
`∑ᵢ ∫_{tᵢ}^{tᵢ₊₁} e (1 − k(u)/k(tᵢ))² du → 0`. -/
theorem tendsto_sum_integral_freeze {k e : ℝ → ℝ} (hk : Continuous k) {c : ℝ} (hc : 0 < c)
    (hkc : ∀ u, c ≤ |k u|) (he : Measurable e) (he0 : ∀ u, 0 ≤ e u) (he1 : ∀ u, e u ≤ 1)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      ∫ u in ((MathFin.unifPartIcc s t n i : ℝ≥0) : ℝ)..((MathFin.unifPartIcc s t n (i + 1) : ℝ≥0)),
        e u * (1 - (k (MathFin.unifPartIcc s t n i))⁻¹ * k u) ^ 2) atTop (𝓝 0) := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have huc : UniformContinuousOn k (Icc (s : ℝ) t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hk.continuousOn
  rw [Metric.uniformContinuousOn_iff_le] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := Real.sqrt (ε / (2 * ((t : ℝ) - s + 1))) with hη
  have hD : 0 < 2 * ((t : ℝ) - s + 1) := by linarith
  have hη0 : 0 < η := Real.sqrt_pos.2 (div_pos hε hD)
  obtain ⟨δ, hδ, hδk⟩ := huc (η * c) (mul_pos hη0 hc)
  obtain ⟨N, hN⟩ := exists_nat_gt (((t : ℝ) - s) / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le N.succ_pos hn))
    linarith
  have hmesh : ((t : ℝ) - s) / n ≤ δ := by
    rw [div_le_iff₀ hn0]
    have h1 : ((t : ℝ) - s) / δ < n := hN.trans_le (by exact_mod_cast (Nat.le_of_succ_le hn))
    rw [div_lt_iff₀ hδ] at h1
    linarith
  -- each cell integrand is at most `η²`
  have hcell : ∀ i ∈ Finset.range n,
      ∫ u in ((MathFin.unifPartIcc s t n i : ℝ≥0) : ℝ)..((MathFin.unifPartIcc s t n (i + 1) : ℝ≥0)),
        e u * (1 - (k (MathFin.unifPartIcc s t n i))⁻¹ * k u) ^ 2
        ≤ η ^ 2 * (((t : ℝ) - s) / n) := by
    intro i hi
    set a : ℝ := ((MathFin.unifPartIcc s t n i : ℝ≥0) : ℝ) with ha
    set b : ℝ := ((MathFin.unifPartIcc s t n (i + 1) : ℝ≥0) : ℝ) with hb
    have hab : a ≤ b := by
      simp only [ha, hb]; exact_mod_cast MathFin.unifPartIcc_mono s t n (Nat.le_succ i)
    have hba : b - a = ((t : ℝ) - s) / n := coe_unifPartIcc_succ_sub s t hst n i
    have hsa : (s : ℝ) ≤ a := by
      simp only [ha]; exact_mod_cast (le_self_add : s ≤ s + MathFin.unifPart (t - s) n i)
    have hbt : b ≤ t := by
      simp only [hb]
      have := MathFin.unifPartIcc_mono s t n (Nat.succ_le_of_lt (Finset.mem_range.1 hi))
      rw [MathFin.unifPartIcc_self hst (by omega)] at this
      exact_mod_cast this
    have hbound : ∀ u ∈ Icc a b, e u * (1 - (k a)⁻¹ * k u) ^ 2 ≤ η ^ 2 := by
      intro u hu
      have hka : c ≤ |k a| := hkc a
      have hka0 : k a ≠ 0 := fun h => by rw [h, abs_zero] at hka; linarith
      have hdist : dist (k a) (k u) ≤ η * c := by
        refine hδk a ⟨hsa, hab.trans hbt⟩ u ⟨hsa.trans hu.1, hu.2.trans hbt⟩ ?_
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]
        linarith [hu.2]
      have h1 : |1 - (k a)⁻¹ * k u| ≤ η := by
        have : 1 - (k a)⁻¹ * k u = (k a - k u) / k a := by field_simp
        rw [this, abs_div, div_le_iff₀ (abs_pos.2 hka0)]
        rw [Real.dist_eq] at hdist
        nlinarith [abs_nonneg (k a - k u)]
      calc e u * (1 - (k a)⁻¹ * k u) ^ 2 ≤ 1 * (1 - (k a)⁻¹ * k u) ^ 2 :=
            mul_le_mul_of_nonneg_right (he1 u) (sq_nonneg _)
        _ ≤ η ^ 2 := by
            rw [one_mul, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hint := intervalIntegral.integral_mono_on (μ := volume) hab ?_
      (intervalIntegrable_const (c := η ^ 2)) hbound
    · simp only [intervalIntegral.integral_const, smul_eq_mul, hba] at hint
      linarith
    · refine (intervalIntegrable_const (c := η ^ 2)).mono_fun ?_ ?_
      · exact (he.mul ((measurable_const.sub (measurable_const.mul hk.measurable)).pow_const 2))
          |>.aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun u hu => ?_)
        have hu' : u ∈ Icc a b := by
          rw [uIoc_of_le hab] at hu; exact ⟨hu.1.le, hu.2⟩
        show ‖e u * (1 - (k a)⁻¹ * k u) ^ 2‖ ≤ ‖η ^ 2‖
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg η),
          abs_of_nonneg (mul_nonneg (he0 u) (sq_nonneg _))]
        exact hbound u hu'
  have hnn : ∀ i ∈ Finset.range n, 0 ≤
      ∫ u in ((MathFin.unifPartIcc s t n i : ℝ≥0) : ℝ)..((MathFin.unifPartIcc s t n (i + 1) : ℝ≥0)),
        e u * (1 - (k (MathFin.unifPartIcc s t n i))⁻¹ * k u) ^ 2 := fun i _ =>
    intervalIntegral.integral_nonneg
      (by exact_mod_cast (MathFin.unifPartIcc_mono s t n (Nat.le_succ i)))
      fun u _ => mul_nonneg (he0 u) (sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg hnn)]
  calc _ ≤ ∑ i ∈ Finset.range n, η ^ 2 * (((t : ℝ) - s) / n) := Finset.sum_le_sum hcell
    _ = η ^ 2 * ((t : ℝ) - s) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
    _ < ε := by
        rw [hη, Real.sq_sqrt (div_pos hε hD).le, div_mul_eq_mul_div, div_lt_iff₀ hD]
        nlinarith

lemma intervalIntegrable_mul_pow {e k : ℝ → ℝ} (he : Measurable e) (he0 : ∀ u, 0 ≤ e u)
    (he1 : ∀ u, e u ≤ 1) (hk : Continuous k) {C : ℝ} (hkC : ∀ u, |k u| ≤ C) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u => e u * k u ^ j) volume a b := by
  refine (intervalIntegrable_const (c := C ^ j)).mono_fun
    (he.mul (hk.measurable.pow_const j)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hkC u)
  show ‖e u * k u ^ j‖ ≤ ‖C ^ j‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (pow_nonneg hC0 j),
    abs_of_nonneg (he0 u)]
  calc e u * |k u| ^ j ≤ 1 * C ^ j :=
        mul_le_mul (he1 u) (pow_le_pow_left₀ (abs_nonneg _) (hkC u) j) (by positivity) zero_le_one
    _ = C ^ j := one_mul _

/-- The cell expression of the brackets is the integral of `e (1 − l k)²`. -/
lemma bracket_cell_eq {e k : ℝ → ℝ} (he : Measurable e) (he0 : ∀ u, 0 ≤ e u)
    (he1 : ∀ u, e u ≤ 1) (hk : Continuous k) {C : ℝ} (hkC : ∀ u, |k u| ≤ C) (l p q : ℝ) :
    ((∫ u in (0 : ℝ)..q, e u) - ∫ u in (0 : ℝ)..p, e u)
      - 2 * l * ((∫ u in (0 : ℝ)..q, e u * k u) - ∫ u in (0 : ℝ)..p, e u * k u)
      + l ^ 2 * ((∫ u in (0 : ℝ)..q, e u * k u ^ 2) - ∫ u in (0 : ℝ)..p, e u * k u ^ 2)
      = ∫ u in p..q, e u * (1 - l * k u) ^ 2 := by
  have i0 := fun a b => intervalIntegrable_mul_pow he he0 he1 hk hkC 0 a b
  have i1 := fun a b => intervalIntegrable_mul_pow he he0 he1 hk hkC 1 a b
  have i2 := fun a b => intervalIntegrable_mul_pow he he0 he1 hk hkC 2 a b
  simp only [pow_zero, mul_one, pow_one] at i0 i1
  rw [intervalIntegral.integral_interval_sub_left (i0 0 q) (i0 0 p),
    intervalIntegral.integral_interval_sub_left (i1 0 q) (i1 0 p),
    intervalIntegral.integral_interval_sub_left (i2 0 q) (i2 0 p)]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (i0 p q) ((i1 p q).const_mul _),
    ← intervalIntegral.integral_add ((i0 p q).sub ((i1 p q).const_mul _)) ((i2 p q).const_mul _)]
  congr 1
  funext u
  ring

/-- **(GB4): the driving noise is a martingale in every filtration in which the harmonic mean is**
(Aux. lemma 47, p. 228). Let `𝓕 ≤ 𝒢`. Let `X, Y` be bounded `𝓕`-martingales with brackets
`⟨X⟩ = ∫ e k²`, `⟨X, Y⟩ = ∫ e k`, `⟨Y⟩ = ∫ e` (the corresponding `X² − ⟨X⟩`, `XY − ⟨X, Y⟩`, `Y² − ⟨Y⟩`
are `𝓕`-martingales), with a continuous adapted coefficient `c ≤ |k| ≤ C` and a measurable weight
`0 ≤ e ≤ 1`. If `X` is a `𝒢`-martingale and `Y` is `𝒢`-adapted, then `Y` is a `𝒢`-martingale.

In the source `X` is the harmonic mean `M_t(z)` at a point above the hulls ((GB2) makes it a martingale
in the germ filtration), `Y` the Brownian motion `B`, and `dM = k dB` (GB3) gives the brackets; all stopped
at a localizing time (`e = 1_{[0, σ)}`). The left-endpoint sums `∑ k(tᵢ)⁻¹ ΔXᵢ` have `𝒢`-conditional mean
zero, and they converge to `Y_t − Y_s` in `L²`: their defects `ΔYᵢ − k(tᵢ)⁻¹ ΔXᵢ` are orthogonal in `𝓕` with
`E[defect²] = E ∫ e (1 − k/k(tᵢ))²` (`integral_sq_cell_eq`, `integral_sq_sum_cells_eq`), which tends to
zero by continuity of `k` (`tendsto_sum_integral_freeze`). This is the source's "the same sums converge in
probability to the stochastic integral in either filtration", without a stochastic integral. -/
theorem martingale_of_bracket_freeze [IsProbabilityMeasure P] {𝒢 : Filtration ℝ≥0 mΩ}
    (h𝓕𝒢 : ∀ t, 𝓕 t ≤ 𝒢 t) {X Y : ℝ≥0 → Ω → ℝ} {k e : ℝ → Ω → ℝ}
    (hX : Martingale X 𝓕 P) (hY : Martingale Y 𝓕 P)
    {K : ℝ} (hXb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (hYb : ∀ t, ∀ᵐ ω ∂P, |Y t ω| ≤ K)
    (hXX : Martingale (fun t ω => X t ω ^ 2 - ∫ u in (0 : ℝ)..t, e u ω * k u ω ^ 2) 𝓕 P)
    (hXY : Martingale (fun t ω => X t ω * Y t ω - ∫ u in (0 : ℝ)..t, e u ω * k u ω) 𝓕 P)
    (hYY : Martingale (fun t ω => Y t ω ^ 2 - ∫ u in (0 : ℝ)..t, e u ω) 𝓕 P)
    (hkc : ∀ ω, Continuous fun u => k u ω) (hka : ∀ p : ℝ≥0, StronglyMeasurable[𝓕 p] (k p))
    {c C : ℝ} (hc : 0 < c) (hkb : ∀ u ω, c ≤ |k u ω|) (hkC : ∀ u ω, |k u ω| ≤ C)
    (he : ∀ ω, Measurable fun u => e u ω) (he0 : ∀ u ω, 0 ≤ e u ω) (he1 : ∀ u ω, e u ω ≤ 1)
    (hXG : Martingale X 𝒢 P) (hYG : StronglyAdapted 𝒢 Y) :
    Martingale Y 𝒢 P := by
  refine ⟨hYG, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hY.integrable t)
    (fun A _ _ => (hY.integrable s).integrableOn) (fun A hA _ => ?_)
    (hYG s).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝒢.le s A hA
  -- notation for the partitions, weights, sums and defects
  set π : ℕ → ℕ → ℝ≥0 := fun n i => MathFin.unifPartIcc s t n i with hπ
  set l : ℕ → ℕ → Ω → ℝ := fun n i ω => (k (π n i) ω)⁻¹ with hl
  have hlm : ∀ n i, StronglyMeasurable[𝓕 (π n i)] (l n i) := fun n i =>
    (hka _).measurable.inv.stronglyMeasurable
  have hlb : ∀ n i ω, |l n i ω| ≤ c⁻¹ := fun n i ω => by
    simp only [hl, abs_inv]
    exact inv_anti₀ hc (hkb _ ω)
  set D : ℕ → ℕ → Ω → ℝ := fun n i ω => (Y (π n (i + 1)) ω - Y (π n i) ω)
    - l n i ω * (X (π n (i + 1)) ω - X (π n i) ω) with hD
  set R : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ Finset.range n, l n i ω * (X (π n (i + 1)) ω - X (π n i) ω) with hR
  have hπm : ∀ n, Monotone (π n) := fun n => MathFin.unifPartIcc_mono s t n
  have hsπ : ∀ n i, s ≤ π n i := fun n i => le_self_add
  -- (a) the Riemann sums have zero integral over `A`
  have hRA : ∀ n, ∫ ω in A, R n ω ∂P = 0 := by
    intro n
    rw [← integral_indicator hA']
    have hpt : A.indicator (R n) = fun ω => ∑ i ∈ Finset.range n,
        A.indicator (l n i) ω * (X (π n (i + 1)) ω - X (π n i) ω) := by
      funext ω
      by_cases hω : ω ∈ A
      · simp [hR, hω, Set.indicator_of_mem]
      · simp [hR, hω, Set.indicator_of_notMem]
    rw [hpt, integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => ?_
      refine integral_mul_increment_eq_zero hXG (hπm n (Nat.le_succ i))
        (((hlm n i).mono (h𝓕𝒢 _)).indicator (𝒢.mono (hsπ n i) A hA)) (C := c⁻¹)
        (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]; exact hlb n i ω
      · rw [Set.indicator_of_notMem hω, abs_zero]; exact inv_nonneg.2 hc.le
    · intro i _
      refine integrable_mul_increment hX _ _
        ((((hlm n i).mono (𝓕.le _)).indicator hA').aestronglyMeasurable) (C := c⁻¹)
        (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]; exact hlb n i ω
      · rw [Set.indicator_of_notMem hω, abs_zero]; exact inv_nonneg.2 hc.le
  -- measurability and bounds of the defects
  have hDm : ∀ n i, AEStronglyMeasurable (D n i) P := fun n i =>
    ((hY.integrable _).sub (hY.integrable _)).aestronglyMeasurable.sub
      (((hlm n i).mono (𝓕.le _)).aestronglyMeasurable.mul
        ((hX.integrable _).sub (hX.integrable _)).aestronglyMeasurable)
  have hDb : ∀ n i, ∀ᵐ ω ∂P, |D n i ω| ≤ 2 * K + c⁻¹ * (2 * K) := fun n i => by
    filter_upwards [hXb (π n i), hXb (π n (i + 1)), hYb (π n i), hYb (π n (i + 1))]
      with ω h1 h2 h3 h4
    calc |D n i ω| ≤ |Y (π n (i + 1)) ω - Y (π n i) ω|
          + |l n i ω| * |X (π n (i + 1)) ω - X (π n i) ω| := by
          simp only [hD]; rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 2 * K + c⁻¹ * (2 * K) := by
          have a1 : |Y (π n (i + 1)) ω - Y (π n i) ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          have a2 : |X (π n (i + 1)) ω - X (π n i) ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          have := inv_nonneg.2 hc.le
          gcongr
          exact hlb n i ω
  set S : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, D n i ω with hS
  have hSm : ∀ n, AEStronglyMeasurable (S n) P := fun n =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => hDm n i
  have hSb : ∀ n, ∀ᵐ ω ∂P, |S n ω| ≤ n * (2 * K + c⁻¹ * (2 * K)) := fun n => by
    filter_upwards [ae_all_iff.2 (hDb n)] with ω hω
    calc |S n ω| ≤ ∑ i ∈ Finset.range n, |D n i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, (2 * K + c⁻¹ * (2 * K)) := Finset.sum_le_sum fun i _ => hω i
      _ = n * (2 * K + c⁻¹ * (2 * K)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSL2 : ∀ n, MemLp (S n) 2 P := fun n =>
    MemLp.of_bound (hSm n) _ ((hSb n).mono fun ω h => by rwa [Real.norm_eq_abs])
  -- (c) the increment of `Y` over `A` is the integral of the defect sum
  have hYA : ∀ n, n ≠ 0 → ∫ ω in A, (Y t ω - Y s ω) ∂P = ∫ ω in A, S n ω ∂P := by
    intro n hn
    have hpt : (fun ω => Y t ω - Y s ω) = fun ω => S n ω + R n ω := by
      funext ω
      have htel := Finset.sum_range_sub (fun i => Y (π n i) ω) n
      simp only [hπ, MathFin.unifPartIcc_zero, MathFin.unifPartIcc_self hst hn] at htel
      have hsum : S n ω + R n ω
          = ∑ i ∈ Finset.range n, (Y (π n (i + 1)) ω - Y (π n i) ω) := by
        simp only [hS, hR, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hD]; ring
      rw [hsum]
      exact htel.symm
    have hRi : Integrable (R n) P := integrable_finsetSum _ fun i _ =>
      integrable_mul_increment hX _ _ ((hlm n i).mono (𝓕.le _)).aestronglyMeasurable
        (Eventually.of_forall (hlb n i))
    rw [hpt, integral_add ((hSL2 n).integrable one_le_two).integrableOn hRi.integrableOn, hRA n,
      add_zero]
  -- (b) the defect sums tend to zero in `L²`
  have hcell : ∀ n i, ∫ ω, D n i ω ^ 2 ∂P = ∫ ω, (((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω)
      - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω)
      - 2 * l n i ω * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω)
      + l n i ω ^ 2 * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω ^ 2)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω ^ 2)) ∂P := fun n i =>
    integral_sq_cell_eq hX hY hXX hXY hYY hXb hYb (hπm n (Nat.le_succ i)) (hlm n i) (hlb n i)
  set F : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n,
    ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2 with hF
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  set Bd : ℝ := (1 + c⁻¹ * C) ^ 2 with hBd
  -- the frozen integrand is bounded
  have hfb : ∀ n i ω u, e u ω * (1 - l n i ω * k u ω) ^ 2 ≤ Bd := by
    intro n i ω u
    have h1 : |l n i ω * k u ω| ≤ c⁻¹ * C := by
      rw [abs_mul]
      exact mul_le_mul (hlb n i ω) (hkC u ω) (abs_nonneg _) (inv_nonneg.2 hc.le)
    have h2 : (1 - l n i ω * k u ω) ^ 2 ≤ Bd := by
      rw [hBd, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by rw [abs_one]; linarith)) 2
    calc e u ω * (1 - l n i ω * k u ω) ^ 2 ≤ 1 * (1 - l n i ω * k u ω) ^ 2 :=
          mul_le_mul_of_nonneg_right (he1 u ω) (sq_nonneg _)
      _ ≤ Bd := by rw [one_mul]; exact h2
  have hcellb : ∀ n i ω, 0 ≤ ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ),
        e u ω * (1 - l n i ω * k u ω) ^ 2 ∧
      ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2
        ≤ Bd * (((t : ℝ) - s) / n) := by
    intro n i ω
    have hpq : ((π n i : ℝ≥0) : ℝ) ≤ (π n (i + 1) : ℝ≥0) := by exact_mod_cast hπm n (Nat.le_succ i)
    have hii : IntervalIntegrable (fun u => e u ω * (1 - l n i ω * k u ω) ^ 2) volume
        (π n i : ℝ) (π n (i + 1) : ℝ) := by
      refine (intervalIntegrable_const (c := Bd)).mono_fun
        ((he ω).mul ((measurable_const.sub (measurable_const.mul (hkc ω).measurable)).pow_const
          2)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
      show ‖e u ω * (1 - l n i ω * k u ω) ^ 2‖ ≤ ‖Bd‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (he0 u ω) (sq_nonneg _)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Bd)]
      exact hfb n i ω u
    refine ⟨intervalIntegral.integral_nonneg hpq fun u _ => mul_nonneg (he0 u ω) (sq_nonneg _),
      ?_⟩
    have h := intervalIntegral.integral_mono_on (μ := volume) hpq hii
      (intervalIntegrable_const (c := Bd)) fun u _ => hfb n i ω u
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    have hw := coe_unifPartIcc_succ_sub s t hst n i
    simp only [hπ] at h
    rw [hw] at h
    linarith
  -- the bracket integrals are measurable in `ω`
  have hG0 : ∀ q : ℝ≥0, AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..(q : ℝ), e u ω) P := by
    intro q
    have h := ((hY.integrable q).aestronglyMeasurable.pow 2).sub
      (hYY.integrable q).aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun ω => by simp)
  have hG1 : ∀ q : ℝ≥0, AEStronglyMeasurable
      (fun ω => ∫ u in (0 : ℝ)..(q : ℝ), e u ω * k u ω) P := by
    intro q
    have h := ((hX.integrable q).aestronglyMeasurable.mul (hY.integrable q).aestronglyMeasurable).sub
      (hXY.integrable q).aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun ω => by simp)
  have hG2 : ∀ q : ℝ≥0, AEStronglyMeasurable
      (fun ω => ∫ u in (0 : ℝ)..(q : ℝ), e u ω * k u ω ^ 2) P := by
    intro q
    have h := ((hX.integrable q).aestronglyMeasurable.pow 2).sub
      (hXX.integrable q).aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun ω => by simp)
  -- the cells in frozen form
  have hcellF : ∀ n i ω, (((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω)
      - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω)
      - 2 * l n i ω * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω)
      + l n i ω ^ 2 * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω ^ 2)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω ^ 2))
      = ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2 :=
    fun n i ω => bracket_cell_eq (he ω) (fun u => he0 u ω) (fun u => he1 u ω) (hkc ω)
      (fun u => hkC u ω) _ _ _
  have hcm : ∀ n i, AEStronglyMeasurable (fun ω =>
      ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2) P := by
    intro n i
    have hlm' : AEStronglyMeasurable (l n i) P := ((hlm n i).mono (𝓕.le _)).aestronglyMeasurable
    have h := (((hG0 (π n (i + 1))).sub (hG0 (π n i))).sub
      (((aestronglyMeasurable_const (b := (2 : ℝ))).mul hlm').mul
        ((hG1 (π n (i + 1))).sub (hG1 (π n i))))).add
      ((hlm'.pow 2).mul ((hG2 (π n (i + 1))).sub (hG2 (π n i))))
    exact h.congr (Eventually.of_forall fun ω => hcellF n i ω)
  have hci : ∀ n i, Integrable (fun ω =>
      ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2) P := by
    intro n i
    refine Integrable.of_bound (hcm n i) (Bd * (((t : ℝ) - s) / n))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hcellb n i ω).1]
    exact (hcellb n i ω).2
  -- `E[S n²] = E[F n]`
  have hSF : ∀ n, ∫ ω, S n ω ^ 2 ∂P = ∫ ω, F n ω ∂P := by
    intro n
    rw [integral_sq_sum_cells_eq hX hY hXb hYb (hπm n) (hlm n) (hlb n) n]
    simp only [hF]
    rw [integral_finsetSum _ fun i _ => hci n i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcell n i]
    exact integral_congr_ae (Eventually.of_forall fun ω => hcellF n i ω)
  -- dominated convergence for `F n`
  have hFlim : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ω : Ω, (0 : ℝ) ∂P := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => Bd * ((t : ℝ) - s))
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun i _ => hcm n i) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => (hcellb n i ω).1)]
      calc F n ω ≤ ∑ i ∈ Finset.range n, Bd * (((t : ℝ) - s) / n) :=
            Finset.sum_le_sum fun i _ => (hcellb n i ω).2
        _ ≤ Bd * ((t : ℝ) - s) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rcases Nat.eq_zero_or_pos n with hn | hn
            · subst hn; simp only [Nat.cast_zero, zero_mul]; positivity
            · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
              exact le_of_eq (by field_simp)
    · exact tendsto_sum_integral_freeze (hkc ω) hc (fun u => hkb u ω) (he ω) (fun u => he0 u ω)
        (fun u => he1 u ω) hst
  have hSlim : Tendsto (fun n => ∫ ω, (S n ω - 0) ^ 2 ∂P) atTop (𝓝 0) := by
    simp only [sub_zero]
    exact hFlim.congr fun n => (hSF n).symm
  have hlimA := LocalSets.tendsto_setIntegral_of_tendsto_integral_sq (f := fun _ => (0 : ℝ))
    (integrable_const _) (fun n => (hSL2 n).integrable one_le_two)
    (fun n => (hSL2 n).sub (memLp_const 0)) hSlim A
  simp only [integral_zero] at hlimA
  have hzero : ∫ ω in A, (Y t ω - Y s ω) ∂P = 0 := by
    refine tendsto_nhds_unique (f := fun _ : ℕ => ∫ ω in A, (Y t ω - Y s ω) ∂P)
      tendsto_const_nhds (hlimA.congr' ?_)
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (hYA n hn).symm
  rw [integral_sub (hY.integrable t).integrableOn (hY.integrable s).integrableOn] at hzero
  linarith

/-- **Removing a localization with an `L²` bound.** If martingales `Yₙ` for `𝒢`, bounded in `L²` at each
time uniformly in `n`, converge almost surely to `Y` at each time, then `Y` is a `𝒢`-martingale
(Vitali's theorem passes the martingale identities to the limit). -/
theorem martingale_of_tendsto_of_sq_bound [IsProbabilityMeasure P] {𝒢 : Filtration ℝ≥0 mΩ}
    {Y : ℝ≥0 → Ω → ℝ} {Yn : ℕ → ℝ≥0 → Ω → ℝ} (hYn : ∀ n, Martingale (Yn n) 𝒢 P)
    (hYnL2 : ∀ n t, MemLp (Yn n t) 2 P) (hbd : ∀ t, ∃ M, ∀ n, ∫ ω, Yn n t ω ^ 2 ∂P ≤ M)
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Yn n t ω) atTop (𝓝 (Y t ω)))
    (hYa : StronglyAdapted 𝒢 Y) (hYi : ∀ t, Integrable (Y t) P) : Martingale Y 𝒢 P := by
  refine ⟨hYa, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hYi t)
    (fun A _ _ => (hYi s).integrableOn) (fun A hA _ => ?_) (hYa s).aestronglyMeasurable).symm
  have hconv : ∀ r, Tendsto (fun n => ∫ ω in A, Yn n r ω ∂P) atTop (𝓝 (∫ ω in A, Y r ω ∂P)) := by
    intro r
    obtain ⟨M, hM⟩ := hbd r
    refine MathFin.tendsto_setIntegral_of_subseq_ae_of_sq_bound
      (fun n => hYnL2 n r) hM (memLp_one_iff_integrable.2 (hYi r)) (fun ns hns => ?_) A
    exact ⟨id, (hlim r).mono fun ω hω => hω.comp hns⟩
  exact tendsto_nhds_unique (hconv s) ((hconv t).congr fun n => ((hYn n).setIntegral_eq hst hA).symm)

/-- **Aux. lemma 47, Brownian conclusion (abstract form).** Let `𝓕 ≤ 𝒢`, where every `𝒢ₛ` contains the
measurable null sets, and let `B` be a Brownian motion adapted to `𝒢`. Suppose `B` is the almost sure
limit, at each time, of localized processes `Yₙ` (in the source, `B` stopped at the localizing times
`ρₙ ↑ ∞` of the Itô layer) such that, for each `n`, `Yₙ` and a localized harmonic mean `Xₙ` satisfy the
bracket hypotheses of `martingale_of_bracket_freeze` in `𝓕` ((GB3): `⟨Yₙ⟩ = ∫ eₙ`, `⟨Xₙ, Yₙ⟩ = ∫ eₙ kₙ`,
`⟨Xₙ⟩ = ∫ eₙ kₙ²`), `Yₙ` starts at `0`, and `Xₙ` is a `𝒢`-martingale ((GB2)). Then `B` is a Brownian motion
in `𝒢`: every increment `B_t − B_s` is independent of `𝒢ₛ`. -/
theorem isFilteredBrownianReal_of_localized_bracket [IsProbabilityMeasure P]
    {𝒢 : Filtration ℝ≥0 mΩ} (h𝓕𝒢 : ∀ t, 𝓕 t ≤ 𝒢 t)
    (hnull : ∀ s (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 s] N)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hBa : StronglyAdapted 𝒢 B)
    {X Y : ℕ → ℝ≥0 → Ω → ℝ} {k e : ℕ → ℝ → Ω → ℝ}
    (hX : ∀ n, Martingale (X n) 𝓕 P) (hY : ∀ n, Martingale (Y n) 𝓕 P)
    {K : ℕ → ℝ} (hXb : ∀ n t, ∀ᵐ ω ∂P, |X n t ω| ≤ K n) (hYb : ∀ n t, ∀ᵐ ω ∂P, |Y n t ω| ≤ K n)
    (hXX : ∀ n, Martingale (fun t ω => X n t ω ^ 2 - ∫ u in (0 : ℝ)..t, e n u ω * k n u ω ^ 2) 𝓕 P)
    (hXY : ∀ n, Martingale (fun t ω => X n t ω * Y n t ω - ∫ u in (0 : ℝ)..t, e n u ω * k n u ω) 𝓕 P)
    (hYY : ∀ n, Martingale (fun t ω => Y n t ω ^ 2 - ∫ u in (0 : ℝ)..t, e n u ω) 𝓕 P)
    (hkc : ∀ n ω, Continuous fun u => k n u ω) (hka : ∀ n (p : ℝ≥0), StronglyMeasurable[𝓕 p] (k n p))
    {c C : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hkb : ∀ n u ω, c n ≤ |k n u ω|)
    (hkC : ∀ n u ω, |k n u ω| ≤ C n)
    (he : ∀ n ω, Measurable fun u => e n u ω) (he0 : ∀ n u ω, 0 ≤ e n u ω)
    (he1 : ∀ n u ω, e n u ω ≤ 1) (hY0 : ∀ n, ∀ᵐ ω ∂P, Y n 0 ω = 0)
    (hXG : ∀ n, Martingale (X n) 𝒢 P) (hYG : ∀ n, StronglyAdapted 𝒢 (Y n))
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Y n t ω) atTop (𝓝 (B t ω))) :
    IsFilteredBrownianReal 𝒢 B P := by
  have hYnG : ∀ n, Martingale (Y n) 𝒢 P := fun n =>
    martingale_of_bracket_freeze h𝓕𝒢 (hX n) (hY n) (hXb n) (hYb n) (hXX n) (hXY n) (hYY n)
      (hkc n) (hka n) (hc n) (hkb n) (hkC n) (he n) (he0 n) (he1 n) (hXG n) (hYG n)
  have hL2 : ∀ n t, MemLp (Y n t) 2 P := fun n t =>
    MemLp.of_bound (hY n |>.integrable t).aestronglyMeasurable (K n)
      ((hYb n t).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hbd : ∀ t : ℝ≥0, ∃ M, ∀ n, ∫ ω, Y n t ω ^ 2 ∂P ≤ M := by
    intro t
    refine ⟨t, fun n => ?_⟩
    have hG : ∀ ω, ∫ u in (0 : ℝ)..(t : ℝ), e n u ω ≤ t := fun ω => by
      have hi := intervalIntegrable_mul_pow (he n ω) (fun u => he0 n u ω) (fun u => he1 n u ω)
        (hkc n ω) (fun u => hkC n u ω) 0 0 t
      simp only [pow_zero, mul_one] at hi
      have h := intervalIntegral.integral_mono_on (μ := volume) (NNReal.coe_nonneg t) hi
        (intervalIntegrable_const (c := (1 : ℝ))) (fun u _ => he1 n u ω)
      simpa using h
    have hGi : Integrable (fun ω => ∫ u in (0 : ℝ)..(t : ℝ), e n u ω) P := by
      have h := ((hY n).integrable t).aestronglyMeasurable.pow 2 |>.sub
        ((hYY n).integrable t).aestronglyMeasurable
      refine Integrable.of_bound (h.congr (Eventually.of_forall fun ω => by simp)) t
        (Eventually.of_forall fun ω => ?_)
      have h0 : 0 ≤ ∫ u in (0 : ℝ)..(t : ℝ), e n u ω :=
        intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun u _ => he0 n u ω
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hG ω
    have hmart := (hYY n).setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simp only [setIntegral_univ] at hmart
    rw [integral_sub (hL2 n t).integrable_sq hGi] at hmart
    have h0 : ∫ ω, (Y n 0 ω ^ 2 - ∫ u in (0 : ℝ)..((0 : ℝ≥0) : ℝ), e n u ω) ∂P = 0 := by
      refine integral_eq_zero_of_ae ((hY0 n).mono fun ω hω => ?_)
      simp [hω]
    rw [h0] at hmart
    have hle : ∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), e n u ω) ∂P ≤ t := by
      calc ∫ ω, (∫ u in (0 : ℝ)..(t : ℝ), e n u ω) ∂P ≤ ∫ _ω : Ω, (t : ℝ) ∂P :=
            integral_mono hGi (integrable_const _) hG
        _ = t := by simp
    linarith
  have hBm : Martingale B 𝒢 P :=
    martingale_of_tendsto_of_sq_bound hYnG hL2 hbd hlim hBa
      fun t => hB.toIsPreBrownianReal.integrable_eval t
  exact isFilteredBrownianReal_of_martingale_of_null hB hnull hBm

end Sec7

end InteractingSLE
