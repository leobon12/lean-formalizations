/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.StripMaps
import InteractingSLE.Spec.Sec4.Heights
import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData

/-!
# §4.2: fields and flow lines on the strip, read in the exponential chart

Packet PROVE-SEC4-B2 (specification §4.2, `source/spec/p097-144.md` L472–L690, pp. 115–127).

The specification defines objects on a domain other than `ℍ` through a conformal map to `ℍ` and the coordinate
rule (1.4) (p. 2; p. 11, "one can use conformal maps to extend this definition to simply connected domains other
than `ℍ`"). All carriers of the project live on `ℍ` (`LQGMetric.DistOn upperHalfPlaneOpens`), so a field on the strip
`𝒮 = {0 < Im z < 1}` is represented by its image under the exponential chart of SEC4-A,

  `E(z) = e^{πz} − 1`  (`expChart`; lift `L_E = log π + π z`, so `arg E′ = π Im z`),

which maps `𝒮` onto `ℍ`, the lower line `ℝ` onto `(−1, ∞)` (`0 ↦ 0`), the upper line `ℝ + i` onto `(−∞, −1)`
(order reversed), the strip end `−∞` to `−1` and the end `+∞` to `∞`. By (1.4) the image of a strip field `h_𝒮` is
`h = h_𝒮 ∘ E⁻¹ − χ arg (E⁻¹)′ = h_𝒮 ∘ E⁻¹ + πχ Im E⁻¹`, whose boundary data are the lower data on `(−1, ∞)` and the
upper data plus `πχ` on `(−∞, −1)` (`stripHData`).

* `stripInv`: the inverse `w ↦ Log(w + 1)/π` of `E` on `closure ℍ \ {−1}`.
* `lowerLineH`, `upperLineH`: the images `(−1, ∞)` and `(−∞, −1)` of `∂_L𝒮` and `∂_U𝒮`.
* `stripHData κ bL bU`, `stripHJumps JL JU`: the transported boundary data and its jump set;
  `isPiecewiseConstantBoundaryData_stripHData`.
* `IsStripGFF`: a GFF on `𝒮` with lower data `bL` and upper data `bU`.
* `IsStripFlowLine`: the flow line from `0` (to the end `+∞`) of a strip field (frozen `IsFlowLine` of its image).
* `fig46Lower`, `fig46Upper`: the boundary data of Figure 4.6(a); `IsProp411Data`: the data class of
  Proposition 4.11 (Remarks 4.8 and 4.10).
* `firstUpperContact`: `T_top`, the first upper-boundary contact time of a flow path.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec4

/-! ### The exponential chart and its inverse on the closed strip -/

/-- The inverse of the exponential chart `E(z) = e^{πz} − 1`: `E⁻¹(w) = Log(w + 1)/π` (principal logarithm). It maps
`closure ℍ \ {−1}` onto the closed strip `{0 ≤ Im z ≤ 1}`. -/
def stripInv (w : ℂ) : ℂ := log (w + 1) / π

theorem stripInv_expChart {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ 1) : stripInv (expChart z) = z := by
  have hπ := Real.pi_pos
  have him : ((π : ℂ) * z).im = π * z.im := by simp
  have hlog : log (exp ((π : ℂ) * z)) = π * z :=
    log_exp (by rw [him]; nlinarith) (by rw [him]; nlinarith)
  simp only [stripInv, expChart, sub_add_cancel, hlog]
  field_simp

theorem expChart_stripInv {w : ℂ} (hw : w ≠ -1) : expChart (stripInv w) = w := by
  have hw1 : w + 1 ≠ 0 := fun h => hw (eq_neg_of_add_eq_zero_left h)
  simp only [expChart, stripInv]
  rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 Real.pi_pos.ne'), exp_log hw1, add_sub_cancel_right]

theorem im_stripInv_mem_Icc {w : ℂ} (hw : 0 ≤ w.im) : (stripInv w).im ∈ Icc (0 : ℝ) 1 := by
  have hπ := Real.pi_pos
  have hw1 : 0 ≤ (w + 1).im := by simpa using hw
  simp only [stripInv, div_ofReal_im, log_im]
  exact ⟨div_nonneg (arg_nonneg_iff.2 hw1) hπ.le, (div_le_one hπ).2 (arg_le_pi _)⟩

theorem stripInv_mem_strip {w : ℂ} (hw : w ∈ H) : stripInv w ∈ strip := by
  have hπ := Real.pi_pos
  have hw1 : w + 1 ∈ H := by simpa using DerivLog.add_ofReal_mem_H hw 1
  have ha := DerivLog.arg_mem_Ioo_of_mem_H hw1
  simp only [strip, mem_ofPred_eq, stripInv, div_ofReal_im, log_im]
  exact ⟨div_pos ha.1 hπ, (div_lt_one hπ).2 ha.2⟩

/-! ### The images of the two boundary lines -/

/-- The image `(−1, ∞)` of the lower boundary line `∂_L𝒮 = ℝ` under `E`. -/
def lowerLineH : Set ℂ := ((↑) : ℝ → ℂ) '' Ioi (-1)

/-- The image `(−∞, −1)` of the upper boundary line `∂_U𝒮 = ℝ + i` under `E`. -/
def upperLineH : Set ℂ := ((↑) : ℝ → ℂ) '' Iio (-1)

theorem expChart_ofReal (x : ℝ) : expChart x = ((Real.exp (π * x) - 1 : ℝ) : ℂ) := expChart_lower x

theorem expChart_ofReal_mem_lowerLineH (x : ℝ) : expChart x ∈ lowerLineH := by
  rw [expChart_ofReal]
  exact ⟨_, by simp only [mem_Ioi]; linarith [Real.exp_pos (π * x)], rfl⟩

theorem expChart_add_I_mem_upperLineH (x : ℝ) : expChart (x + I) ∈ upperLineH := by
  rw [expChart_upper]
  exact ⟨_, by simp only [mem_Iio]; linarith [Real.exp_pos (π * x)], rfl⟩

theorem disjoint_lowerLineH_upperLineH : Disjoint lowerLineH upperLineH := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have := ofReal_injective hxy
  simp only [mem_Ioi, mem_Iio] at hx hy
  linarith

theorem disjoint_H_lowerLineH : Disjoint H lowerLineH := by
  rw [Set.disjoint_right]
  rintro _ ⟨x, -, rfl⟩ hx
  simp [H] at hx

/-! ### Transported boundary data -/

/-- The boundary data on `∂ℍ` of the `E`-image of a strip field with lower data `bL` and upper data `bU` (each a
function of the real part): `bL(E⁻¹ y)` on `(−1, ∞)` and `bU(Re E⁻¹ y) + πχ` on `(−∞, −1)` (rule (1.4) with
`arg E′ = 0` on the lower line and `π` on the upper line, `ChartHeights.lean`). The value at `−1` is irrelevant. -/
def stripHData (κ : ℝ) (bL bU : ℝ → ℝ) (y : ℝ) : ℝ :=
  if -1 < y then bL (Real.log (y + 1) / π) else bU (Real.log (-y - 1) / π) + π * chiC κ

/-- The jump set of `stripHData`: the strip end `−1` and the images of the lower and upper jumps. -/
def stripHJumps (JL JU : Finset ℝ) : Finset ℝ :=
  insert (-1) (JL.image (fun x => Real.exp (π * x) - 1) ∪ JU.image (fun x => -Real.exp (π * x) - 1))

theorem stripHData_lower (κ : ℝ) (bL bU : ℝ → ℝ) (x : ℝ) :
    stripHData κ bL bU (Real.exp (π * x) - 1) = bL x := by
  have h : -1 < Real.exp (π * x) - 1 := by linarith [Real.exp_pos (π * x)]
  rw [stripHData, ite_eq_left h, sub_add_cancel, Real.log_exp, mul_div_cancel_left₀ _ Real.pi_pos.ne']

theorem stripHData_upper (κ : ℝ) (bL bU : ℝ → ℝ) (x : ℝ) :
    stripHData κ bL bU (-Real.exp (π * x) - 1) = bU x + π * chiC κ := by
  have h : ¬ (-1 < -Real.exp (π * x) - 1) := by linarith [Real.exp_pos (π * x)]
  rw [stripHData, ite_eq_right h, show -(-Real.exp (π * x) - 1) - 1 = Real.exp (π * x) by ring,
    Real.log_exp, mul_div_cancel_left₀ _ Real.pi_pos.ne']

theorem stripHData_of_lt {κ : ℝ} {bL bU : ℝ → ℝ} {y : ℝ} (hy : -1 < y) :
    stripHData κ bL bU y = bL (Real.log (y + 1) / π) := ite_eq_left hy

theorem stripHData_of_lt_neg_one {κ : ℝ} {bL bU : ℝ → ℝ} {y : ℝ} (hy : y < -1) :
    stripHData κ bL bU y = bU (Real.log (-y - 1) / π) + π * chiC κ := ite_eq_right (not_lt.2 hy.le)

/-- Piecewise-constant strip data transport to piecewise-constant data on `∂ℍ`. -/
theorem isPiecewiseConstantBoundaryData_stripHData (κ : ℝ) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hL : IsPiecewiseConstantBoundaryData bL JL) (hU : IsPiecewiseConstantBoundaryData bU JU) :
    IsPiecewiseConstantBoundaryData (stripHData κ bL bU) (stripHJumps JL JU) := by
  intro y hy
  simp only [stripHJumps, Finset.mem_insert, Finset.mem_union, Finset.mem_image, not_or] at hy
  obtain ⟨hy1, hyL, hyU⟩ := hy
  have hπ := Real.pi_pos
  rcases lt_or_gt_of_ne hy1 with hlt | hgt
  · -- upper part `y < −1`
    set x := Real.log (-y - 1) / π with hx
    have hpos : 0 < -y - 1 := by linarith
    have hxy : -Real.exp (π * x) - 1 = y := by
      rw [hx, mul_div_cancel₀ _ hπ.ne', Real.exp_log hpos]; ring
    have hxJ : x ∉ JU := fun h => hyU ⟨x, h, hxy⟩
    have hcont : ContinuousAt (fun y' : ℝ => Real.log (-y' - 1) / π) y := by
      have hf : ContinuousAt (fun y' : ℝ => -y' - 1) y := by fun_prop
      exact (ContinuousAt.comp (g := Real.log) (x := y) (Real.continuousAt_log hpos.ne') hf).div_const π
    have hev : ∀ᶠ y' in 𝓝 y, bU (Real.log (-y' - 1) / π) = bU x :=
      hcont.eventually (hU x hxJ)
    filter_upwards [hev, Iio_mem_nhds hlt] with y' hy' hy'lt
    rw [stripHData_of_lt_neg_one hy'lt, stripHData_of_lt_neg_one hlt, hy']
  · -- lower part `y > −1`
    set x := Real.log (y + 1) / π with hx
    have hpos : 0 < y + 1 := by linarith
    have hxy : Real.exp (π * x) - 1 = y := by
      rw [hx, mul_div_cancel₀ _ hπ.ne', Real.exp_log hpos]; ring
    have hxJ : x ∉ JL := fun h => hyL ⟨x, h, hxy⟩
    have hcont : ContinuousAt (fun y' : ℝ => Real.log (y' + 1) / π) y := by
      have hf : ContinuousAt (fun y' : ℝ => y' + 1) y := by fun_prop
      exact (ContinuousAt.comp (g := Real.log) (x := y) (Real.continuousAt_log hpos.ne') hf).div_const π
    have hev : ∀ᶠ y' in 𝓝 y, bL (Real.log (y' + 1) / π) = bL x :=
      hcont.eventually (hL x hxJ)
    filter_upwards [hev, Ioi_mem_nhds hgt] with y' hy' hy'lt
    rw [stripHData_of_lt hy'lt, stripHData_of_lt hgt, hy']

/-! ### GFFs and flow lines on the strip -/

/-- `h` is the `E`-image (rule (1.4)) of a GFF on the strip `𝒮` whose boundary data are `bL` on the lower line
`∂_L𝒮` and `bU` on the upper line `∂_U𝒮` (each locally constant off `JL`, resp. `JU`, read as functions of the real
part; Lemma 4.7: "let `h` be a GFF on `𝒮` whose boundary data is as depicted in Figure 4.6(a)"). -/
def IsStripGFF (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) : Prop :=
  IsGFFWithBoundaryData P h (stripHData κ bL bU) (stripHJumps JL JU : Set ℝ)

/-- `η` (lifetime `ζ`) is, in the chart `E`, the flow line from `0` towards the end `+∞` of the strip field whose
`E`-image is `h` (lower data `bL`, upper data `bU`): the frozen `IsFlowLine` (angle `0`, seed `0`) of `h` with the
transported data. The physical strip curve is `stripInv ∘ η`. -/
def IsStripFlowLine (κ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  IsFlowLine κ (stripHData κ bL bU) (stripHJumps JL JU) 0 0 P h η ζ

/-- `T_top`, the first time the flow path `η` (in the chart `E`) is on the upper line `∂_U𝒮`, as an extended time
(`⊤` if never). Lemma 4.7 ("first-segment stopping convention", pp. 116–117) concerns `η` on `[0, T_top]`. -/
def firstUpperContact (η : ℝ≥0 → ℂ) : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : η t ∈ upperLineH), (t : ℝ≥0∞)

theorem firstUpperContact_le {η : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : η t ∈ upperLineH) :
    firstUpperContact η ≤ t :=
  iInf₂_le t ht

theorem notMem_upperLineH_of_lt {η : ℝ≥0 → ℂ} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < firstUpperContact η) :
    η t ∉ upperLineH := fun h => (firstUpperContact_le h).not_gt ht

/-- `T_top > 0` for a flow path from `0` continuous at time `0` (the upper line `(−∞, −1)` is at distance `1` from
`0`): part of input (a) of Remark 4.8. -/
theorem firstUpperContact_pos {η : ℝ≥0 → ℂ} (h0 : η 0 = 0) (hc : ContinuousAt η 0) :
    0 < firstUpperContact η := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hc 1 one_pos
  set d : ℝ≥0 := ⟨δ, hδ.le⟩ with hd_def
  have hle : (d : ℝ≥0∞) ≤ firstUpperContact η := by
    refine le_iInf₂ fun t ht => ?_
    obtain ⟨x, hx, hxt⟩ := ht
    by_contra hlt
    have hlt' : (t : ℝ) < δ := by
      have := ENNReal.coe_lt_coe.1 (not_le.1 hlt)
      exact this
    have hd : dist t 0 < δ := by
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]; exact hlt'
    have h1 := hball hd
    rw [h0, dist_zero_right, ← hxt, Complex.norm_real, Real.norm_eq_abs] at h1
    have hx' : x < -1 := hx
    have : 1 < |x| := by rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hdpos : (0 : ℝ≥0) < d := by rw [← NNReal.coe_lt_coe]; exact hδ
  exact lt_of_lt_of_le (ENNReal.coe_pos.2 hdpos) hle
/-! ### The boundary data of Figure 4.6(a) and of Proposition 4.11 -/

/-- Lower data of Figure 4.6(a): `−λ` on `(−∞, 0)`, `λ` on `(0, ∞)`. -/
def fig46Lower (κ : ℝ) (x : ℝ) : ℝ := if x < 0 then -sleLambda κ else sleLambda κ

/-- Upper data of Figure 4.6(a), `z₀ = x₀ + i`: `−λ + πχ` left of `z₀`, `λ` right of `z₀`. -/
def fig46Upper (κ x₀ : ℝ) (x : ℝ) : ℝ := if x < x₀ then -sleLambda κ + π * chiC κ else sleLambda κ

theorem isPiecewiseConstantBoundaryData_ite_lt (c u v : ℝ) :
    IsPiecewiseConstantBoundaryData (fun x : ℝ => if x < c then u else v) {c} := by
  intro y hy
  have hyc : y ≠ c := by simpa using hy
  rcases lt_or_gt_of_ne hyc with h | h
  · filter_upwards [Iio_mem_nhds h] with z hz
    rw [ite_eq_left (show z < c from hz), ite_eq_left h]
  · filter_upwards [Ioi_mem_nhds h] with z hz
    rw [ite_eq_right (not_lt.2 (le_of_lt (show c < z from hz))), ite_eq_right (not_lt.2 h.le)]

theorem isPiecewiseConstantBoundaryData_fig46Lower (κ : ℝ) :
    IsPiecewiseConstantBoundaryData (fig46Lower κ) {0} :=
  isPiecewiseConstantBoundaryData_ite_lt 0 _ _

theorem isPiecewiseConstantBoundaryData_fig46Upper (κ x₀ : ℝ) :
    IsPiecewiseConstantBoundaryData (fig46Upper κ x₀) {x₀} :=
  isPiecewiseConstantBoundaryData_ite_lt x₀ _ _

/-- The boundary data class of Proposition 4.11 (Remarks 4.8 and 4.10), `z₀ = x₀ + i`: piecewise constant on both
lines with finitely many changes; on `∂_L𝒮` at most `−λ + πχ` left of `0` and at least `λ` right of `0`; on
`∂_U𝒮` at most `−λ` left of `z₀` and at least `λ + πχ` right of `z₀`. -/
def IsProp411Data (κ x₀ : ℝ) (bL bU : ℝ → ℝ) (JL JU : Finset ℝ) : Prop :=
  IsPiecewiseConstantBoundaryData bL JL ∧ IsPiecewiseConstantBoundaryData bU JU ∧
    (∀ x < 0, bL x ≤ -sleLambda κ + π * chiC κ) ∧ (∀ x, 0 < x → sleLambda κ ≤ bL x) ∧
    (∀ x < x₀, bU x ≤ -sleLambda κ) ∧ ∀ x, x₀ < x → sleLambda κ + π * chiC κ ≤ bU x

/-- Transported heights of Figure 4.6(a) (`q = e^{πx₀}`, so `E(z₀) = −1 − q`): `λ` on `[0, ∞)`, `−λ` on `(−1, 0)`,
`−λ + 2πχ` on `(−1 − q, −1)` and `λ + πχ` on `(−∞, −1 − q]` (the strip end `−1` excluded). -/
theorem stripHData_fig46 (κ x₀ : ℝ) {y : ℝ} (hy : y ≠ -1) :
    stripHData κ (fig46Lower κ) (fig46Upper κ x₀) y =
      if 0 ≤ y then sleLambda κ else if -1 < y then -sleLambda κ
      else if -1 - Real.exp (π * x₀) < y then -sleLambda κ + 2 * (π * chiC κ)
      else sleLambda κ + π * chiC κ := by
  have hπ := Real.pi_pos
  by_cases h1 : -1 < y
  · rw [stripHData_of_lt h1, fig46Lower, ite_eq_left h1]
    by_cases h0 : 0 ≤ y
    · rw [ite_eq_left h0, ite_eq_right (not_lt.2 (div_nonneg (Real.log_nonneg (by linarith)) hπ.le))]
    · rw [ite_eq_right h0, ite_eq_left (div_neg_of_neg_of_pos (Real.log_neg (by linarith) (by linarith)) hπ)]
  · have h1' : y < -1 := lt_of_le_of_ne (not_lt.1 h1) hy
    have hpos : 0 < -y - 1 := by linarith
    rw [stripHData_of_lt_neg_one h1', fig46Upper, ite_eq_right (show ¬ (0 ≤ y) by linarith), ite_eq_right h1]
    have hiff : Real.log (-y - 1) / π < x₀ ↔ -1 - Real.exp (π * x₀) < y := by
      rw [div_lt_iff₀ hπ, mul_comm x₀ π, Real.log_lt_iff_lt_exp hpos]
      constructor <;> intro h <;> linarith
    by_cases h2 : -1 - Real.exp (π * x₀) < y
    · rw [ite_eq_left (hiff.2 h2), ite_eq_left h2]; ring
    · rw [ite_eq_right (fun h => h2 (hiff.1 h)), ite_eq_right h2]

end Sec4

end InteractingSLE
