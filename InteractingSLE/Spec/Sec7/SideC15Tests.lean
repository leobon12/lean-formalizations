/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Partition
import InteractingSLE.Spec.Sec7.SideC3Records

/-!
# R90a's ready tests and their unchanged canonical charts

PROVE-SIDE-COLLAR2. Restrict only the test event to a branch fibre; keep
the original outer labels, chart, rational seed and word shape. Every
positive-probability fibre is ready, and the complete chart (including
the principal-logarithm lift) agrees with the original chart there.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.SideC15 Sec7.PocketStopField

variable {Ω : Type} [MeasurableSpace Ω]

/-- R90a's literal refinement of the original test by its branch value. -/
def refineBranch (j : SideTest Ω) (n : Ω → ℤ) (k : ℤ) : SideTest Ω :=
  {j with event := branchEvent j.event n k}

omit [MeasurableSpace Ω] in
@[simp] theorem refineBranch_event (j : SideTest Ω) (n : Ω → ℤ) (k : ℤ) :
    (j.refineBranch n k).event = branchEvent j.event n k := rfl

/-- Every non-null walls-measurable branch piece satisfies all the original
readiness conditions. Neither the probability space nor the measure changes. -/
theorem refineBranch_ready {j : SideTest Ω} {d : WordObjects Ω}
    (hj : j.Ready d) {n : Ω → ℤ}
    (hn : Measurable[Sec7.PocketWordPerQ.wallsSigma d.measure d.rightWall (d.leftWall j.seed)] n)
    {k : ℤ} (hk : 0 < d.measure (branchEvent j.event n k)) :
    (j.refineBranch n k).Ready d := by
  rcases hj with ⟨hq, hGm, hGp, hcfg, hζ, hfin, hinf, hA, hAG, _, hJ, hψm, htwo⟩
  refine ⟨hq, hGm, hGp, hcfg, hζ, hfin, hinf,
    @measurableSet_branchEvent Ω (Sec7.PocketWordPerQ.wallsSigma d.measure d.rightWall (d.leftWall j.seed)) _ _ hA hn k, fun _ hω => hAG hω.1, hk, ?_, hψm, ?_⟩
  · cases hI : j.infinite <;>
      simp only [refineBranch, hI, Bool.false_eq_true, ↓reduceIte] at hJ ⊢ <;>
      exact fun ω hω => hJ ω hω.1
  · cases hI : j.twoLeft <;>
      simp only [refineBranch, hI, Bool.false_eq_true, ↓reduceIte] at htwo ⊢ <;>
      exact fun ω hω => htwo ω hω.1

/-- The refined chart is exactly the old chart at every retained sample,
including its canonical logarithm, inverse and lift. -/
theorem refineBranch_baseChart {j : SideTest Ω} (i : BothLow) (d : WordObjects Ω)
    {n : Ω → ℤ} {k : ℤ} {ω : Ω} (hω : ω ∈ (j.refineBranch n k).event) :
    ((j.refineBranch n k).target i d).baseChart ω = (j.target i d).baseChart ω := by
  unfold SideTarget.baseChart
  rw [target_event, target_domain, target_chart, target_event, target_domain, target_chart]
  change pChart (branchEvent j.event n k) _ j.chart ω = pChart j.event _ j.chart ω
  change ω ∈ branchEvent j.event n k at hω
  simp only [pChart, pLog, pFwd_of_mem hω, pInv_of_mem hω,
    pFwd_of_mem hω.1, pInv_of_mem hω.1]
  rfl

/-- Almost every sample of a ready test belongs to a positive-probability
ready refined test, with its own branch as the refinement label. -/
theorem ae_refineBranch_ready {j : SideTest Ω} {d : WordObjects Ω}
    (hj : j.Ready d) {n : Ω → ℤ}
    (hn : Measurable[Sec7.PocketWordPerQ.wallsSigma d.measure d.rightWall (d.leftWall j.seed)] n) :
    ∀ᵐ ω ∂d.measure, ω ∈ j.event →
      (j.refineBranch n (n ω)).Ready d ∧ ω ∈ (j.refineBranch n (n ω)).event := by
  filter_upwards [ae_mem_positive_branchEvent d.measure j.event n] with ω hω hA
  exact ⟨j.refineBranch_ready hj hn (hω hA), hA, rfl⟩

end InteractingSLE.Wire.Current.SideTest
