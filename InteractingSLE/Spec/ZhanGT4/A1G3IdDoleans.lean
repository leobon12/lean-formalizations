/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3IdDrift
import InteractingSLE.Spec.ZhanGT4.A1G3RowGirsanov

/-!
# Zhan's A.1 (G3): the Girsanov density removing the large curve's force points is the inverse martingale ratio

Packet PROVE-A1-G3ROW2. Source: the specification's proof of Theorem 2.2 (L488: Girsanov removal of force points) and
the `SLE_κ(ρ)` density (Lemma 2.1).

For the large (G3) curve, `SLE_κ(κ − 4, −4)`, PROVE-A1-G3ROW's `girsanov_removeAll_pathwise` changes the measure by the
Doléans density `Z_{T+1}` of the cut drift `θ = removeAllDrift …` (cut at a stopping time `S`), under which the driver
is `√κ` times a Brownian motion. This file identifies that density:

`Z_{T+1} = exp(−(log M_S − log M_0))` almost surely, `log M = g3LogMart`,

the inverse ratio of the `SLE_κ(κ − 4, −4)` martingale. Proof: A22's logarithmic Itô formula for the drifted log-field
`G3Field.ell` (`isDriftLogField_g3`) gives `ℓ(S) − ℓ(0) + (κ/2) ∫₀^S ℓ_x² = ∫ c dB` for the stopped coefficient `c`;
`c = −θ` off the single time `S` (`coef_eq_neg_removeAll`), so `∫ c dB = −∫ θ dB` (`stochIntegral_ae_eq_of_eq_off`,
`stochIntegral_neg_ae_eq`); `∫₀^{T+1} θ² = κ ∫₀^S ℓ_x²` (`quadInt_removeAll_eq`); and `ℓ(S) − ℓ(0)` is the decrement
of `g3LogMart` (`ell_sub_eq_neg_g3LogMart`, with the pair term from `sub_eq_mul_exp_of_force`).

* **`doleansDensity_removeAll_g3_ae_eq`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Id

open Girsanov G3Field

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin 2 → ℝ} {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {S : Ω → ℝ≥0} {δ R : ℝ} {T : ℝ≥0}

/-! ### Pathwise identities -/

/-- **The stopped coefficient of the logarithmic Itô formula** at times before `S`: `√κ ℓ_x(r, W_r)`. -/
theorem coef_of_lt (r : ℝ≥0) (ω : Ω) (hr : r < S ω) :
    seedEndCoef 0 (Ito.stopCoef (seedRestartDeriv 1 (ellX κ VL) (Real.sqrt κ) B (D κ W B) 0) (shiftBM B 0)
      (fun ω => S ω - 0)) r ω = Real.sqrt κ * (-cy κ / (W r ω - VL 1 r ω) - cx κ / (W r ω - VL 0 r ω)) := by
  simp only [seedEndCoef, zero_le, ite_true, Ito.stopCoef, hr, seedRestartDeriv, shiftField, shiftOff, shiftBM,
    pow_one, ellX, v, Strip.extPath, D, tsub_zero, zero_add, NNReal.coe_zero, Real.toNNReal_coe]
  ring_nf

/-- The stopped coefficient vanishes at and after `S`. -/
theorem coef_of_le (r : ℝ≥0) (ω : Ω) (hr : S ω ≤ r) :
    seedEndCoef 0 (Ito.stopCoef (seedRestartDeriv 1 (ellX κ VL) (Real.sqrt κ) B (D κ W B) 0) (shiftBM B 0)
      (fun ω => S ω - 0)) r ω = 0 := by
  have hr' : ¬ r - 0 < S ω - 0 := by simpa using hr
  simp only [seedEndCoef, zero_le, ite_true, Ito.stopCoef, hr', ite_false]

/-- **The removal drift before `S`**: `θ_r = κ^{−1/2}((κ − 4)/(W − V₀) − 4/(W − V₁))`. -/
theorem removeAll_of_lt (hδ : 0 < δ) {ω : Ω} (h : PathOn κ xL xR ρR W VL VR B ζ ω (S ω) δ) {r : ℝ≥0}
    (hr : r < S ω) :
    A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR r ω =
      (Real.sqrt κ)⁻¹ * ((κ - 4) / (W r ω - VL 0 r ω) + -4 / (W r ω - VL 1 r ω)) := by
  obtain ⟨-, -, -, hWc, hVLc, hVRc, -⟩ := h.path
  have hUc : ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := fun k => by
    cases k using Fin.addCases with
    | left i =>
      have e : allMarks VL VR (Fin.castAdd 0 i) = VL i := Fin.addCases_left (motive := fun _ => ℝ≥0 → Ω → ℝ) i
      rw [e]
      exact hVLc i
    | right i => exact i.elim0
  have hτζ : ((S ω : ℝ≥0) : ℝ≥0∞) ≤ ζ ω := h.lt.le
  have hlt : ((r : ℝ≥0) : ℝ≥0∞) < (S ω : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hr
  rw [show A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR = cutDrift
      (fun ω => (S ω : ℝ≥0∞)) ζ (shiftIntegrand κ (-1) δ (removedWeights ![κ - 4, -4] ρR Finset.univ Finset.univ))
      W (allMarks VL VR) from rfl,
    cutDrift_eq_of_lt (A1G3Row.continuous_shiftIntegrand_removeAll hδ) hτζ hWc hUc hlt]
  have e0 : recipCut δ (W r ω - VL 0 r ω) = (W r ω - VL 0 r ω)⁻¹ := recipCut_of_le hδ (h.gap r hr.le 0)
  have e1 : recipCut δ (W r ω - VL 1 r ω) = (W r ω - VL 1 r ω)⁻¹ := recipCut_of_le hδ (h.gap r hr.le 1)
  simp only [shiftIntegrand, addedDriftCut, Fin.sum_univ_add, removedWeights, allMarks, Fin.addCases_left,
    Fin.addCases_right, Finset.mem_univ, ite_true, Fin.sum_univ_two, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1]
  ring

/-- **The coefficient is minus the removal drift at every time other than `S`.** -/
theorem coef_eq_neg_removeAll (hκ : 0 < κ) (hδ : 0 < δ) {ω : Ω} (h : PathOn κ xL xR ρR W VL VR B ζ ω (S ω) δ)
    {r : ℝ≥0} (hr : r ≠ S ω) :
    seedEndCoef 0 (Ito.stopCoef (seedRestartDeriv 1 (ellX κ VL) (Real.sqrt κ) B (D κ W B) 0) (shiftBM B 0)
      (fun ω => S ω - 0)) r ω =
      -A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR r ω := by
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · rw [coef_of_lt r ω hlt, removeAll_of_lt hδ h hlt]
    have h0 := h.gap r hlt.le 0
    have h1 := h.gap r hlt.le 1
    have n0 : W r ω - VL 0 r ω ≠ 0 := fun he => by rw [he, abs_zero] at h0; linarith [h.pos]
    have n1 : W r ω - VL 1 r ω ≠ 0 := fun he => by rw [he, abs_zero] at h1; linarith [h.pos]
    have hss : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ.le
    simp only [cy, cx]
    set s := Real.sqrt κ with hs_def
    have hs : s ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
    have hk : κ = s * s := hss.symm
    rw [hk]
    field_simp
    ring
  · have h0 : A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR r ω = 0 :=
      cutDrift_eq_zero (show ((S ω : ℝ≥0) : ℝ≥0∞) < (r : ℝ≥0∞) from ENNReal.coe_lt_coe.2 hgt)
    rw [coef_of_le r ω hgt.le, h0, neg_zero]

/-- The square of the removal integrand before `S` is `κ ℓ_x²` at the driver. -/
theorem sq_removeAll_integrand_eq (hκ : 0 < κ) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((Real.sqrt κ)⁻¹ * ((κ - 4) / a + -4 / b)) ^ 2 = κ * (-cy κ / b - cx κ / a) ^ 2 := by
  have hss : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ.le
  simp only [cy, cx]
  set s := Real.sqrt κ with hs_def
  have hs : s ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hk : κ = s * s := hss.symm
  rw [hk]
  field_simp
  ring

/-- **The quadratic integral of the removal drift** up to `T + 1 ≥ S` is `κ ∫₀^S ℓ_x(u, W_u)²`. -/
theorem quadInt_removeAll_eq (hκ : 0 < κ) (hδ : 0 < δ)
    (hθp : IsStronglyProgressive 𝓕 (A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR))
    {C : ℝ} (hθb : ∀ t ω, |A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR t ω| ≤ C)
    {ω : Ω} (h : PathOn κ xL xR ρR W VL VR B ζ ω (S ω) δ) (hST : S ω ≤ T) :
    quadInt (A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR) (T + 1) ω =
      κ * ∫ u in (0 : ℝ)..(S ω : ℝ), ellX κ VL ω u (w W ω u) ^ 2 := by
  set θ := A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR with hθ
  have hθ2 : IsStronglyProgressive 𝓕 (fun u ω => θ u ω ^ 2) := fun t => (hθp t).pow 2
  have hθ2b : ∀ u ω, |θ u ω ^ 2| ≤ C ^ 2 := fun u ω => by
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hθb u ω) 2
  have hint := fun a b => intervalIntegrable_time hθ2 hθ2b ω a b
  have hST' : (S ω : ℝ) ≤ ((T + 1 : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_le_coe]
    exact hST.trans (le_add_of_nonneg_right zero_le_one)
  unfold quadInt
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (S ω)) (hint (S ω) ((T + 1 : ℝ≥0) : ℝ))]
  -- after `S` the drift vanishes
  have hafter : (∫ u in (S ω : ℝ)..((T + 1 : ℝ≥0) : ℝ), θ u.toNNReal ω ^ 2) = 0 := by
    rw [← intervalIntegral.integral_zero (a := (S ω : ℝ)) (b := ((T + 1 : ℝ≥0) : ℝ)) (μ := volume)]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_real (S ω : ℝ)] with u hu hmem
    rw [uIoc_of_le hST'] at hmem
    have hlt : (S ω : ℝ) < u := lt_of_le_of_ne hmem.1.le (Ne.symm hu)
    have hlt' : ((S ω : ℝ≥0) : ℝ≥0∞) < (u.toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ ((S ω).coe_nonneg.trans hlt.le)]
      exact hlt
    have h0 : θ u.toNNReal ω = 0 := cutDrift_eq_zero hlt'
    rw [h0]
    norm_num
  rw [hafter, add_zero]
  -- before `S`: the uncut integrand
  obtain ⟨-, -, -, hWc, hVLc, hVRc, -⟩ := h.path
  have hUc : ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := fun k => by
    cases k using Fin.addCases with
    | left i =>
      have e : allMarks VL VR (Fin.castAdd 0 i) = VL i := Fin.addCases_left (motive := fun _ => ℝ≥0 → Ω → ℝ) i
      rw [e]
      exact hVLc i
    | right i => exact i.elim0
  have hcomp := integral_comp_cutDrift_eq (A1G3Row.continuous_shiftIntegrand_removeAll (κ := κ)
    (ρL := ![κ - 4, -4]) (ρR := ρR) hδ) (fun z => z ^ 2) (τ := fun ω => (S ω : ℝ≥0∞)) (ζ := ζ) (W := W)
    (U := allMarks VL VR) h.lt.le hWc hUc (t := S ω) le_rfl
  change (∫ s in (0 : ℝ)..(S ω : ℝ), θ s.toNNReal ω ^ 2) = _ at hcomp
  rw [hcomp, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (S ω).coe_nonneg] at hu
  have hle : u.toNNReal ≤ S ω := Real.toNNReal_le_iff_le_coe.2 hu.2
  have e0 : recipCut δ (W u.toNNReal ω - VL 0 u.toNNReal ω) = (W u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ :=
    recipCut_of_le hδ (h.gap _ hle 0)
  have e1 : recipCut δ (W u.toNNReal ω - VL 1 u.toNNReal ω) = (W u.toNNReal ω - VL 1 u.toNNReal ω)⁻¹ :=
    recipCut_of_le hδ (h.gap _ hle 1)
  simp only [shiftIntegrand, addedDriftCut, Fin.sum_univ_add, removedWeights, allMarks, Fin.addCases_left,
    Fin.addCases_right, Finset.mem_univ, ite_true, Fin.sum_univ_two, Finset.univ_eq_empty, Finset.sum_empty,
    add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, e0, e1]
  have hrw : -(-1 / Real.sqrt κ) * ((κ - 4) * (W u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ +
      -4 * (W u.toNNReal ω - VL 1 u.toNNReal ω)⁻¹) =
      (Real.sqrt κ)⁻¹ * ((κ - 4) / (W u.toNNReal ω - VL 0 u.toNNReal ω) +
        -4 / (W u.toNNReal ω - VL 1 u.toNNReal ω)) := by
    simp only [div_eq_mul_inv]
    ring
  rw [hrw]
  exact sq_removeAll_integrand_eq hκ (a := W u.toNNReal ω - VL 0 u.toNNReal ω)
    (b := W u.toNNReal ω - VL 1 u.toNNReal ω) (h.ne hu 0) (h.ne hu 1)

/-- **The field's increment is the decrement of the martingale's logarithm**: along the driver,
`ℓ(S, W_S) − ℓ(0, W_0) = −(g3LogMart S − g3LogMart 0)` (the pair term by `sub_eq_mul_exp_of_force`). -/
theorem ell_sub_eq_neg_g3LogMart {ω : Ω} (h : PathOn κ xL xR ρR W VL VR B ζ ω (S ω) δ) (hxy : xL 0 ≠ xL 1) :
    ell κ W VL ω (S ω) (w W ω (S ω)) - ell κ W VL ω 0 (w W ω 0) =
      -(g3LogMart κ (W · ω) (VL 0 · ω) (VL 1 · ω) (S ω) - g3LogMart κ (W · ω) (VL 0 · ω) (VL 1 · ω) 0) := by
  obtain ⟨hw0, hvL0, -, hWc, hVLc, -, -, -, -, -, -, -, -, hLeq, -⟩ := h.path
  have hode := sub_eq_mul_exp_of_force hWc (hVLc 0) (hVLc 1) (fun t ht => hLeq t ht 0) (fun t ht => hLeq t ht 1)
    h.lt (fun r hr he => by
      have := h.gap r hr 0
      simp only at he
      rw [he, sub_self, abs_zero] at this
      linarith [h.pos])
    (fun r hr he => by
      have := h.gap r hr 1
      simp only at he
      rw [he, sub_self, abs_zero] at this
      linarith [h.pos]) (le_refl (S ω))
  have hlog : Real.log (VL 0 (S ω) ω - VL 1 (S ω) ω) = Real.log (xL 0 - xL 1) - I2 W VL ω (S ω) := by
    rw [hode, Real.log_mul (sub_ne_zero.2 hxy) (Real.exp_pos _).ne', Real.log_exp]
    rfl
  have hn1 : Real.log (W (S ω) ω - VL 1 (S ω) ω) = Real.log (VL 1 (S ω) ω - W (S ω) ω) := by
    rw [← neg_sub, Real.log_neg_eq_log]
  have hn1' : Real.log (0 - xL 1) = Real.log (xL 1 - 0) := by rw [← neg_sub, Real.log_neg_eq_log]
  simp only [ell, g3LogMart, I1, I2, w, v, Strip.extPath, Real.toNNReal_coe, Real.toNNReal_zero, hw0, hvL0,
    NNReal.coe_zero, intervalIntegral.integral_same, mul_zero, add_zero, sub_zero, zero_sub]
  rw [I2] at hlog
  simp only [v, w, Strip.extPath] at hlog
  rw [hlog, hn1]
  have hn1'' : Real.log (-xL 1) = Real.log (xL 1) := Real.log_neg_eq_log _
  rw [hn1'']
  simp only [cy, cx, cxy]
  ring

/-! ### The Doléans density -/

/-- **The Girsanov density removing the large G3 curve's force points is the inverse martingale ratio.** For an
integrated `SLE_κ(κ − 4, −4)` evolution with continuous Brownian paths at every sample, progressive driver and force
points, and a stopping time `S ≤ T` before the lifetime before which both force gaps lie in `[δ, R]` at every sample:
with `θ = removeAllDrift κ δ ![κ − 4, −4] ρR S ζ W VL VR`, almost surely
`doleansDensity P 𝓕 B θ (T + 1) = exp(−(g3LogMart S − g3LogMart 0))`. -/
theorem doleansDensity_removeAll_g3_ae_eq [IsProbabilityMeasure P] (hκ : 0 < κ) (hδ : 0 < δ)
    (hE : IsIntegratedSLEEvolution κ xL xR ![κ - 4, -4] ρR P 𝓕 W VL VR B ζ) (hBc : ∀ ω, Continuous (B · ω))
    (hp : ∀ ω, PathOn κ xL xR ρR W VL VR B ζ ω (S ω) δ) (hxy : xL 0 ≠ xL 1)
    (hR : ∀ ω (r : ℝ≥0), r ≤ S ω → ∀ i, |W r ω - VL i r ω| ≤ R) (hST : ∀ ω, S ω ≤ T)
    (hW : IsStronglyProgressive 𝓕 W) (hVL : ∀ i, IsStronglyProgressive 𝓕 (VL i))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    doleansDensity P 𝓕 B (A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR) (T + 1)
      =ᵐ[P] fun ω => Real.exp (-(g3LogMart κ (W · ω) (VL 0 · ω) (VL 1 · ω) (S ω) -
        g3LogMart κ (W · ω) (VL 0 · ω) (VL 1 · ω) 0)) := by
  obtain ⟨K, hF⟩ := isDriftLogField_g3 hκ hp hR hST hδ hW hVL hS
  obtain ⟨hBr, hWa, hVLa, hVRa, -⟩ := hE
  have hpre := isFilteredPreBrownian_of_isFilteredBrownianReal hBr
  have hσ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hρ : 0 < δ / 8 := by positivity
  have hlog := hF.seed_original_logIto hBr hBc hσ hρ hS (t := T + 1) bot_le
  obtain ⟨hcm, hcreg, C', -, hcb⟩ := hF.seed_original_coef_facts (P := P) hBc hσ hρ hS
  set θ := A1G3Row.removeAllDrift κ δ ![κ - 4, -4] ρR (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR with hθ
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (allMarks VL VR k) := fun k => by
    cases k using Fin.addCases with
    | left i =>
      have e : allMarks VL VR (Fin.castAdd 0 i) = VL i := Fin.addCases_left (motive := fun _ => ℝ≥0 → Ω → ℝ) i
      rw [e]
      exact hVLa i
    | right i => exact i.elim0
  have hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | ((S ω : ℝ≥0) : ℝ≥0∞) ≤ s} := fun s => by
    have := hS.measurableSet_le s
    convert this using 2 with ω
    simp only [ENNReal.coe_le_coe, WithTop.coe_le_coe]
  have hθp : IsStronglyProgressive 𝓕 θ := isStronglyProgressive_cutDrift
    (A1G3Row.continuous_shiftIntegrand_removeAll hδ) hWa hU hτ
  have hθb := abs_cutDrift_le (τ := fun ω => (S ω : ℝ≥0∞)) (ζ := ζ) (W := W) (U := allMarks VL VR)
    (A1G3Row.abs_shiftIntegrand_removeAll_le (κ := κ) (ρL := ![κ - 4, -4]) (ρR := ρR) hδ)
  have hθreg : IsRiemannRegular P θ := by
    refine isRiemannRegular_cutDrift (A1G3Row.continuous_shiftIntegrand_removeAll hδ) (fun ω => (hp ω).lt.le)
      (Eventually.of_forall fun ω => ⟨(hp ω).path.2.2.2.1, fun k => ?_⟩)
    cases k using Fin.addCases with
    | left i =>
      have e : allMarks VL VR (Fin.castAdd 0 i) = VL i := Fin.addCases_left (motive := fun _ => ℝ≥0 → Ω → ℝ) i
      rw [e]
      exact (hp ω).path.2.2.2.2.1 i
    | right i => exact i.elim0
  obtain ⟨M, hM⟩ : ∃ M, ∀ t ω, |θ t ω| ≤ M := ⟨_, hθb⟩
  have hnm : StronglyAdapted 𝓕 (fun s ω => -θ s ω) := fun s => ((hθp.stronglyAdapted) s).neg
  have hnb : ∀ s ω, |-θ s ω| ≤ M := fun s ω => by rw [abs_neg]; exact hM s ω
  have hnreg : IsRiemannRegular P (fun s ω => -θ s ω) := hθreg.mono fun ω hω => hω.mono fun _ hu => hu.neg
  have h1 := stochIntegral_ae_eq_of_eq_off hpre hBc hcm hnm hcb hnb hcreg hnreg (τ := S)
    (fun ω r hr => coef_eq_neg_removeAll hκ hδ (hp ω) hr) (T + 1)
  have h2 := stochIntegral_neg_ae_eq hpre hθp.stronglyAdapted hM hθreg (T + 1)
  have h3 := ZhanGT4.seedStochIntegral_zero_ae hpre hcm hcb hcreg
  filter_upwards [hlog, h1, h2, h3] with ω hl e1 e2 e3
  have hmin : min (T + 1) (S ω) = S ω := min_eq_right ((hST ω).trans (le_add_of_nonneg_right zero_le_one))
  have hmin' : min ((T + 1 : ℝ≥0) : ℝ) ((S ω : ℝ≥0) : ℝ) = S ω := by rw [← NNReal.coe_min, hmin]
  rw [hmin, hmin', e1, e2, e3] at hl
  simp only [driftDriver_eq, NNReal.coe_zero] at hl
  have hq := quadInt_removeAll_eq hκ hδ hθp hM (hp ω) (hST ω)
  have hd := ell_sub_eq_neg_g3LogMart (hp ω) hxy
  rw [doleansDensity]
  congr 1
  rw [Real.sq_sqrt hκ.le] at hl
  rw [hq]
  linarith

end InteractingSLE.ZhanGT4.A1G3Id
