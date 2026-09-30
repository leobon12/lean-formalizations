import QuantumZipper.Proofs.Thm18.G1Z3AddFun
import QuantumZipper.Proofs.LQG.WedgeCanonical2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z3 (D58), the wedge field at a fixed map

The wedge field `wedgeField (lateralPart x) A Q` has the same dyadic averages as
`x + ofFun (wedgeProfile x A Q)` except on the circles `‖z‖ = 2^{-k}` through the origin
(`WedgeCanon2.avgReg_wedgeField_eq`). Near a boundary segment whose image avoids `0` the pushed
semicircles stay away from `0`, so the two fields have the same pulled-back boundary
approximations there (`bdryApprox_coordChange_eq_of_avgReg_away`), and the fixed-map rule for
the free field transfers to the wedge field through `G1Z3.isVagueLimitOnR_coordChange_add_ofFun`
(Duplantier–Sheffield 2011, rule (5.1); the profile is continuous off `0`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z3

open GoodSample LocalRule CoordChange GaussTK

/-- The wedge profile is continuous on `Hbar` off the origin. -/
theorem continuousOn_wedgeProfile_ne {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F) {A : ℝ → ℝ} (hA : Continuous A) (Q : ℝ) :
    ContinuousOn (WedgeCan.wedgeProfile x A Q) (({0}ᶜ : Set ℂ) ∩ Hbar) := by
  have hne : ∀ z ∈ (({0}ᶜ : Set ℂ) ∩ Hbar), z ≠ 0 := fun z hz => hz.1
  have hrad : ContinuousOn (fun z : ℂ => radAvgReg x ‖z‖) (({0}ᶜ : Set ℂ) ∩ Hbar) :=
    ContinuousOn.congr (ContinuousOn.comp hG.1.1
        (continuousOn_const.prodMk continuous_norm.continuousOn)
        fun z hz => ⟨GaussTK.zero_mem_Hbar, norm_pos_iff.2 (hne z hz)⟩)
      fun z hz => hG.radAvgReg_eq (norm_pos_iff.2 (hne z hz))
  have hlogc : ContinuousOn (fun z : ℂ => -Real.log ‖z‖) (({0}ᶜ : Set ℂ) ∩ Hbar) := fun z hz =>
    ((Real.continuousAt_log (norm_ne_zero_iff.2 (hne z hz))).comp
      continuous_norm.continuousAt).neg.continuousWithinAt
  have hAc : ContinuousOn (fun z : ℂ => A (-Real.log ‖z‖)) (({0}ᶜ : Set ℂ) ∩ Hbar) :=
    hA.comp_continuousOn hlogc
  unfold WedgeCan.wedgeProfile
  exact (hrad.neg.add (continuousOn_const.mul hlogc)).add hAc

/-- The wedge field and `x + ofFun (wedgeProfile x A Q₀)` have the same boundary approximations
(their densities differ at most at `±2^{-k}`). -/
theorem bdryApprox_wedgeField_eq {γ Q₀ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    {A : ℝ → ℝ} (hA : Continuous A) (k : ℕ) :
    bdryApprox γ (wedgeField (lateralPart x) A Q₀) k =
      bdryApprox γ (x + ofFun (WedgeCan.wedgeProfile x A Q₀)) k := by
  unfold bdryApprox
  refine withDensity_congr_ae ?_
  have hfin : ({radius k, -radius k} : Set ℝ).Finite := toFinite _
  filter_upwards [hfin.countable.ae_notMem volume] with u hu
  have hne : ‖(u : ℂ)‖ ≠ radius k := by
    intro h
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    rcases abs_eq (radius_pos k).le |>.1 h with h1 | h1 <;> simp_all
  rw [WedgeCan.avgReg_wedgeField_eq hG hraw hA Q₀ (ofReal_mem_Hbar u) hne]

/-- Local boundary measure of the wedge field off `0`: on an open `J ⊆ ℝ \ {0}`, the global
boundary measure of the wedge field is `e^{γ/2·profile} ν_x` (rule (5.1)). -/
theorem qBoundaryMeasure_wedgeField_restrict {γ Q₀ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    {A : ℝ → ℝ} (hA : Continuous A)
    (hx : IsVagueLimitR (bdryApprox γ x) (qBoundaryMeasure γ x))
    (hW : IsVagueLimitR (bdryApprox γ (wedgeField (lateralPart x) A Q₀))
      (qBoundaryMeasure γ (wedgeField (lateralPart x) A Q₀)))
    {J : Set ℝ} (hJ : IsOpen J) (hJ0 : (0 : ℝ) ∉ J) :
    (qBoundaryMeasure γ (wedgeField (lateralPart x) A Q₀)).restrict J =
      ((qBoundaryMeasure γ x).withDensity fun u =>
        ENNReal.ofReal (Real.exp (γ / 2 * WedgeCan.wedgeProfile x A Q₀ u))).restrict J := by
  have hres : ∀ {νs : ℕ → Measure ℝ} {ν : Measure ℝ}, IsVagueLimitR νs ν →
      IsVagueLimitOnR J νs (ν.restrict J) := by
    intro νs ν h
    have := h.1
    refine ⟨?_, fun K hK _ => (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top,
      fun f hf hfc hfU => ?_⟩
    · rw [Measure.restrict_apply hJ.measurableSet.compl, compl_inter_self, measure_empty]
    · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
        image_eq_zero_of_notMem_tsupport fun h => ht (hfU h)]
      exact h.2 f hf hfc
  have h1 := isVagueLimitOnR_add_ofFun ⟨F, hG.1⟩ hJ (hres hx) isOpen_compl_singleton
    (fun t ht h0 => hJ0 (by
      have h0' : t = 0 := by simpa using h0
      exact h0' ▸ ht))
    (continuousOn_wedgeProfile_ne hG hA Q₀)
  have h2 := hres hW
  have e : bdryApprox γ (wedgeField (lateralPart x) A Q₀) =
      bdryApprox γ (x + ofFun (WedgeCan.wedgeProfile x A Q₀)) :=
    funext fun k => bdryApprox_wedgeField_eq hG hraw hA k
  rw [e] at h2
  rw [LocalRule.isVagueLimitOnR_unique hJ h2 h1, restrict_withDensity hJ.measurableSet]

end G1Z3
end Thm18Asm
end QuantumZipper
