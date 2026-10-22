import HigherDimLQGContinuity.Frame.Energy
import HigherDimLQGContinuity.Frame.Coord

/-!
# Pairing frame VI: Bessel's inequality for geodesic-type measures

Packet N3 (NA4 Details (a) A2, item 10; blueprint Part C `c:lem-frame-bessel`).

Let `w_j = gramVec ψ_j = bandVecM κ₀ (0, ∞) (ψ_j⁺ dx) (ψ_j⁻ dx)` and `w_ν = bandVecM κ₀ (0, ∞) ν σ₁` (vectors of the
white-noise Hilbert space `L²(ℝ × ℝ^d)`, `κ₀ = HigherDimLFPP.bumpKernel d`). By HigherDimLFPP's isometry
`scaleCov_eq_logCov` (with the `LogPairable` facts of `Frame/Energy.lean`) and `Frame/Potential.lean`:
`⟪w_j, w_ν⟫ = logCov(ψ_j⁺, ψ_j⁻, ν, σ₁) = ∫ e_j dν` (`integral_frameE_eq_inner`), `‖w_ν‖² = logCov(ν, σ₁, ν, σ₁)`
(`norm_frameMeasVec_sq`), and `⟪w_i, w_j⟫ = ⟨ψ_i, ψ_j⟫₋ = δ_{ij} c_i` (HDLM's `inner_gramVec`). Bessel's inequality for
the orthonormal family `(w_j)_{c_j = 1}` (Mathlib's `Orthonormal.sum_inner_products_le`) and the energy bound give
`Σ_{j<n} (∫ e_j dν)² ≤ C_b (1 + (log B + 1)/σ + log(2 + S))`, `C_b = 2 + log 2 + |sphEnergy d|` (`frame_bessel`).
No linearity of `bandVecM` is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The Bessel constant `C_b = 2 + log 2 + |sphEnergy d|` (Part C `c:lem-frame-bessel`). -/
def frameCb (d : ℕ) : ℝ := 2 + Real.log 2 + |sphEnergy d|

theorem one_le_frameCb (d : ℕ) : 1 ≤ frameCb d := by
  have h1 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ |sphEnergy d| := abs_nonneg _
  unfold frameCb
  linarith

/-- The white-noise vector `w_ν = bandVecM κ₀ (0, ∞) ν σ₁`. -/
def frameMeasVec (d : ℕ) (ν : Measure (Rd d)) : HigherDimLFPP.WN d :=
  HigherDimLFPP.bandVecM (kappa0 d) (Ioi 0) ν (unitSphereProb d)

/-- `‖w_ν‖² = logCov(ν, σ₁, ν, σ₁)`. -/
theorem norm_frameMeasVec_sq (hd : 2 ≤ d) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    {S B σ : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B) (hsupp : ν (closedBall (0 : Rd d) S)ᶜ = 0)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ) :
    ‖frameMeasVec d ν‖ ^ 2 = HigherDimLFPP.logCov ν (unitSphereProb d) ν (unitSphereProb d) := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hP := frame_logPairable_self hd ν hσ hB hsupp hball
  obtain ⟨-, -, h⟩ := HigherDimLFPP.scaleCov_eq_logCov (HigherDimLFPP.isLFPPKernel_bumpKernel d)
    (by rw [probReal_univ, probReal_univ]) (by rw [probReal_univ, probReal_univ]) hP
  rw [← real_inner_self_eq_norm_sq, ← h]
  rfl

section Bessel

variable [NeZero d]

/-- `∫ e_j dν = ⟪w_j, w_ν⟫`. -/
theorem integral_frameE_eq_inner (hd : 2 ≤ d) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    {S B σ : ℝ} (hσ : 0 < σ) (hB : 0 ≤ B) (hsupp : ν (closedBall (0 : Rd d) S)ᶜ = 0)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ)
    (j : ℕ) :
    ∫ x, frameE d j x ∂ν = ⟪gramVec ⇑(frameGS d j), frameMeasVec d ν⟫ := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hP := frame_logPairable_posM hd (frameGS d j) ν hσ hB hsupp hball
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn (frameGS d j)
  have := isFiniteMeasure_posM hψ
  have := isFiniteMeasure_posM hψ.neg
  obtain ⟨-, -, h⟩ := HigherDimLFPP.scaleCov_eq_logCov (HigherDimLFPP.isLFPPKernel_bumpKernel d)
    (posM_real_univ_eq hψ (integral_frameGS j)) (by rw [probReal_univ, probReal_univ]) hP
  rw [frameE, integral_framePot_eq_logCov _ ν hP, ← h]
  rfl

/-- `⟪w_i, w_j⟫ = δ_{ij} c_i`. -/
theorem inner_gramVec_frameGS (i j : ℕ) :
    ⟪gramVec ⇑(frameGS d i), gramVec ⇑(frameGS d j)⟫ = if i = j then frameC d i else 0 := by
  obtain ⟨M, D, hi⟩ := exists_isBddSupp_testOn (frameGS d i)
  obtain ⟨M', D', hj⟩ := exists_isBddSupp_testOn (frameGS d j)
  rw [inner_gramVec hi (integral_frameGS i) hj (integral_frameGS j)]
  exact frameGS_orthonormal i j

/-- **Bessel's inequality for geodesic-type measures** (Part C `c:lem-frame-bessel`). -/
theorem frame_bessel (hd : 2 ≤ d) (ν : Measure (Rd d)) [IsProbabilityMeasure ν] {S B σ : ℝ}
    (hS : 1 ≤ S) (hB : 1 ≤ B) (hσ : 0 < σ) (hsupp : ν (closedBall (0 : Rd d) S)ᶜ = 0)
    (hball : ∀ z : Rd d, ∀ r : ℝ, 0 < r → r ≤ 1 / 2 → (ν (closedBall z r)).toReal ≤ B * r ^ σ)
    (n : ℕ) :
    ∑ j ∈ Finset.range n, (∫ x, frameE d j x ∂ν) ^ 2 ≤
      frameCb d * (1 + (Real.log B + 1) / σ + Real.log (2 + S)) := by
  classical
  have hB0 : (0 : ℝ) ≤ B := by linarith
  set wν := frameMeasVec d ν with hwν
  let w : ℕ → HigherDimLFPP.WN d := fun j => gramVec ⇑(frameGS d j)
  have hinner : ∀ j, ∫ x, frameE d j x ∂ν = ⟪w j, wν⟫ := fun j =>
    integral_frameE_eq_inner hd ν hσ hB0 hsupp hball j
  -- vectors with `c_j = 0` vanish
  have hzero : ∀ j, frameC d j ≠ 1 → w j = 0 := by
    intro j hj
    have hc : frameC d j = 0 := (frameC_mem j).resolve_right hj
    have h := inner_gramVec_frameGS (d := d) j j
    rw [ite_eq_left rfl, hc] at h
    exact inner_self_eq_zero.1 h
  -- Bessel's inequality for the orthonormal subfamily
  let J := {j : ℕ // frameC d j = 1}
  have hON : Orthonormal ℝ fun j : J => w j.1 := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := inner_gramVec_frameGS (d := d) i.1 j.1
    by_cases hij : i = j
    · rw [ite_eq_left hij, hij]
      have h' := inner_gramVec_frameGS (d := d) j.1 j.1
      rw [ite_eq_left rfl, j.2] at h'
      exact h'
    · have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      rw [ite_eq_right hij]
      rw [ite_eq_right hne] at h
      exact h
  have hbes := hON.sum_inner_products_le wν (s := (Finset.range n).subtype fun j => frameC d j = 1)
  have hsum : ∑ j ∈ Finset.range n, (∫ x, frameE d j x ∂ν) ^ 2 =
      ∑ j ∈ (Finset.range n).subtype (fun j => frameC d j = 1), ‖⟪w j.1, wν⟫‖ ^ 2 := by
    rw [Finset.sum_subtype_eq_sum_filter (fun j => ‖⟪w j, wν⟫‖ ^ 2)]
    rw [Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hinner, Real.norm_eq_abs, sq_abs]
    · intro j _ hj
      by_contra hc
      exact hj (by rw [hzero j hc, inner_zero_left, norm_zero, sq, mul_zero])
  rw [hsum]
  refine hbes.trans ?_
  rw [norm_frameMeasVec_sq hd ν hσ hB0 hsupp hball]
  refine (frame_logCov_self_le hd ν hS hB hσ hsupp hball).trans ?_
  -- arithmetic
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hX : 0 ≤ (Real.log B + 1) / σ := div_nonneg (by linarith [Real.log_nonneg hB]) hσ.le
  have hY : Real.log (S + 1) ≤ Real.log (2 + S) := Real.log_le_log (by linarith) (by linarith)
  have hY0 : 0 ≤ Real.log (S + 1) := Real.log_nonneg (by linarith)
  have hZ : 0 ≤ |sphEnergy d| := abs_nonneg _
  unfold frameCb
  nlinarith [mul_nonneg (add_nonneg hL.le hZ) hX, mul_nonneg (add_nonneg hL.le hZ) (hY0.trans hY),
    mul_nonneg (add_nonneg (add_nonneg zero_le_one hL.le) hZ) hX]

end Bessel

end HigherDimLQGContinuity
