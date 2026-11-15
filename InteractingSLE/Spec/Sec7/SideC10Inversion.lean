/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealInitial
import InteractingSLE.Spec.Sec2.MartingaleCoupling
import LQGMetric.Complex.HarmonicComp

/-!
# The initial finite-word mean through the compatible inversion

PROVE-SIDE-COLLAR2. The inherited inverse lift is exactly
`2πi - 2 Log z`, and the centering constant is exactly `-πχ`.
The already proved boundary limits, boundedness and harmonic uniqueness
give the interior finite-word formula. The flow-coordinate mean and its
identification with the physical conditional mean are separate inputs.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped Real
open QuantumZipper (H chiC)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Aux. 120's centered mean with its compatible inherited inverse lift. -/
def centeredReversedMean (κ : ℝ) (M : ℂ → ℝ) : ℂ → ℝ :=
  fun z => -coordChange (chiC κ) (fun w => -w⁻¹)
    (fun w => 2 * π * I - 2 * log w) M z - π * chiC κ

/-- The imaginary inverse lift is a bounded harmonic step extension. -/
theorem centeredReversedMean_eq_jumpExt (κ : ℝ) (M : ℂ → ℝ) (z : ℂ) :
    centeredReversedMean κ M z =
      -M (-z⁻¹) + (2 * π * chiC κ) * Impl.jumpExt 0 z - π * chiC κ := by
  simp only [centeredReversedMean, coordChange, Impl.jumpExt_eq,
    ofReal_zero, sub_zero, sub_im, mul_im, mul_re, ofReal_re, ofReal_im,
    I_re, I_im, re_ofNat, im_ofNat, log_im]
  field_simp
  ring

/-- Bounded harmonic flow means remain bounded and harmonic under the
actual compatible inversion and the prescribed common centering. -/
theorem centeredReversedMean_harmonic_bounded {κ : ℝ} {M : ℂ → ℝ}
    (hM : InnerProductSpace.HarmonicOnNhd M H)
    (hBound : ∃ C : ℝ, ∀ z ∈ H, |M z| ≤ C) :
    InnerProductSpace.HarmonicOnNhd (centeredReversedMean κ M) H ∧
      ∃ C : ℝ, ∀ z ∈ H, |centeredReversedMean κ M z| ≤ C := by
  have hInv : MapsTo (fun z : ℂ => -z⁻¹) H H :=
    Chart.isConformal_infinitySourceChart.2.1
  have hComp : InnerProductSpace.HarmonicOnNhd (fun z => M (-z⁻¹)) H :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hM
      (fun z hz => ((differentiableAt_id.inv (by
        intro h; have : (0 : ℝ) < z.im := hz; simp [h] at this)).neg).differentiableWithinAt)
      hInv
  have hEq : centeredReversedMean κ M = fun z =>
      -M (-z⁻¹) + (2 * π * chiC κ) * Impl.jumpExt 0 z - π * chiC κ :=
    funext (centeredReversedMean_eq_jumpExt κ M)
  rw [hEq]
  refine ⟨(hComp.neg.add (Impl.harmonicOnNhd_const_mul _
    (Impl.harmonicOnNhd_jumpExt 0))).sub (InnerProductSpace.harmonicOnNhd_const _), ?_⟩
  obtain ⟨C, hC⟩ := hBound
  refine ⟨C + |2 * π * chiC κ| + |π * chiC κ|, fun z hz => ?_⟩
  calc
    |-M (-z⁻¹) + (2 * π * chiC κ) * Impl.jumpExt 0 z - π * chiC κ|
        ≤ (|M (-z⁻¹)| + |2 * π * chiC κ| * |Impl.jumpExt 0 z|) + |π * chiC κ| := by
          calc
            _ ≤ |-M (-z⁻¹) + (2 * π * chiC κ) * Impl.jumpExt 0 z| + |π * chiC κ| :=
              abs_sub _ _
            _ ≤ _ := by grw [abs_add_le]; rw [abs_neg, abs_mul]
    _ ≤ _ := by
      grw [hC _ (hInv hz), Impl.abs_jumpExt_le 0 hz]
      rw [mul_one]

/-- A finite incoming angle word gives the exact bounded counterflow
extension, including every remote force mark. The cumulative weights are
matched to the incident flow angles at the inverted boundary coordinate. -/
theorem isBoundedHarmonicExtension_centeredReversedMean
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)
    (θ₁ θ₂ : ℝ → ℝ) {M : ℂ → ℝ}
    (hM : InnerProductSpace.HarmonicOnNhd M H)
    (hBound : ∃ C : ℝ, ∀ z ∈ H, |M z| ≤ C)
    (hHeight : ∀ x : ℝ, x ∉ forceJumpSet vL vR →
      Tendsto M (𝓝[H] (-((x : ℂ)⁻¹)))
        (𝓝 (cf92Lower κ (θ₁ (-x⁻¹)) (θ₂ (-x⁻¹)) (-x⁻¹))))
    (hLeft : ∀ x : ℝ, x ∉ forceJumpSet vL vR → x < 0 →
      ∑ a ∈ Finset.univ.filter (fun a => x < vL a), ρL a = cf95RhoL κ (θ₁ (-x⁻¹)))
    (hRight : ∀ x : ℝ, x ∉ forceJumpSet vL vR → 0 < x →
      ∑ a ∈ Finset.univ.filter (fun a => vR a ≤ x), ρR a = cf95RhoR κ (θ₂ (-x⁻¹))) :
    IsBoundedHarmonicExtension (forceBoundaryData (16 / κ) ρL ρR vL vR)
      (forceJumpSet vL vR) (centeredReversedMean κ M) := by
  obtain ⟨hHarm, hBdd⟩ := centeredReversedMean_harmonic_bounded hM hBound
  refine ⟨hHarm, hBdd, fun x hx => ?_⟩
  change Tendsto (fun z : ℂ => -coordChange (chiC κ) (fun w => -w⁻¹)
    (fun w => 2 * π * I - 2 * log w) M z - π * chiC κ) _ _
  have hx0 : x ≠ 0 := fun he => hx (he ▸ Set.mem_insert 0 _)
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have h := tendsto_centered_initial_height_neg hκ hneg (hHeight x hx)
    simpa only [centeredReversedMean, forceBoundaryData, ite_eq_left hneg,
      hLeft x hx hneg, sleLambda] using h
  · have h := tendsto_centered_initial_height_pos hκ hpos (hHeight x hx)
    simpa only [centeredReversedMean, forceBoundaryData,
      ite_eq_right (not_lt.2 hpos.le), hRight x hx hpos, sleLambda] using h

/-- The normalized finite-word identity holds throughout the half-plane,
by the existing uniqueness theorem, rather than only at boundary points. -/
theorem centeredReversedMean_eq_meanExt
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)
    (θ₁ θ₂ : ℝ → ℝ) {M : ℂ → ℝ}
    (hM : InnerProductSpace.HarmonicOnNhd M H)
    (hBound : ∃ C : ℝ, ∀ z ∈ H, |M z| ≤ C)
    (hHeight : ∀ x : ℝ, x ∉ forceJumpSet vL vR →
      Tendsto M (𝓝[H] (-((x : ℂ)⁻¹)))
        (𝓝 (cf92Lower κ (θ₁ (-x⁻¹)) (θ₂ (-x⁻¹)) (-x⁻¹))))
    (hLeft : ∀ x : ℝ, x ∉ forceJumpSet vL vR → x < 0 →
      ∑ a ∈ Finset.univ.filter (fun a => x < vL a), ρL a = cf95RhoL κ (θ₁ (-x⁻¹)))
    (hRight : ∀ x : ℝ, x ∉ forceJumpSet vL vR → 0 < x →
      ∑ a ∈ Finset.univ.filter (fun a => vR a ≤ x), ρR a = cf95RhoR κ (θ₂ (-x⁻¹))) :
    EqOn (centeredReversedMean κ M) (MartChar.meanExt (16 / κ) ρL ρR 0 vL vR) H := by
  have hMean := isBoundedHarmonicExtension_centeredReversedMean hκ ρL ρR vL vR
    θ₁ θ₂ hM hBound hHeight hLeft hRight
  have hExt := MartChar.isBoundedHarmonicExtension_meanExt (16 / κ) ρL ρR 0 vL vR
  simp only [sub_zero] at hExt
  exact Impl.eqOn_of_isBoundedHarmonicExtension
    (Impl.forceJumpSet_finite (Ito.weightWord ρL ρR) vL vR) hExt hMean

end InteractingSLE.Sec7.PocketStopSide
