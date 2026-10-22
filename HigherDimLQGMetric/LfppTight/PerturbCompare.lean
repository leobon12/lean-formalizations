import HigherDimLQGMetric.LfppTight.ContinuousConvolution
import HigherDimLQGMetric.LfppTight.FieldContinuity
import HigherDimLQGMetric.ConvField.Shifts
import HigherDimLQGMetric.ConvField.ContBound
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.Frozen.LfppDist
import HigherDimLFPP.Paths.Compare

/-! Uniform comparison of LFPP metrics under a bounded continuous perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_ae_lfppDist_addFun_compare {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → DistRd d) (hg : IsWholeSpaceLGF g P)
    (f : Ω → C(Rd d, ℝ)) {ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∀ᵐ ω ∂P, (∀ z, |f ω z| ≤ M) → ∀ p : Rd d × Rd d,
      lfppDist κ ξ ε (addFun (g ω) (f ω)) p ≤
        Real.exp (|ξ| * (M * ∫ z : Rd d, |convKernel κ z|)) *
          lfppDist κ ξ ε (g ω) p ∧
      lfppDist κ ξ ε (g ω) p ≤
        Real.exp (|ξ| * (M * ∫ z : Rd d, |convKernel κ z|)) *
          lfppDist κ ξ ε (addFun (g ω) (f ω)) p := by
  let L : ℝ := ∫ z : Rd d, |convKernel κ z|
  have hcont := l6a_ae_continuous_convMollify hd κ hκ P g
    hg.isLGFPlusBddCont hε
  have hadd := l2b_ae_pairing_tendsto_wholeSpace d hd κ hκ P g hg
  filter_upwards [hcont, hadd] with ω hc ha hM p
  let φ : Rd d → ℝ := fun z => convMollify κ ε (addFun (g ω) (f ω)) z
  let ψ : Rd d → ℝ := fun z => convMollify κ ε (g ω) z
  let F : Rd d → ℝ := fun z => ∫ w : Rd d,
    convKernelEps κ ε (z - w) * f ω w
  have hF : Continuous F := l6a_continuous_conv_of_bddCont hd κ hκ hε (f ω) hM
  have hφeq : φ = fun z => ψ z + F z := by
    funext z
    obtain ⟨a, ha'⟩ := ha ε hε z
    exact l2b_convMollify_addFun_of_tendsto hd hκ hε ha' (f ω) M hM
  have hφ : Continuous φ := by rw [hφeq]; exact hc.add hF
  have hψ : Continuous ψ := hc
  have hbound (z : Rd d) : |F z| ≤ M * L :=
    l2b_abs_conv_ofCont_le_kernelL1 hd hκ hε (f ω) hM z
  have hφψ (z : Rd d) : |φ z - ψ z| ≤ M * L := by
    rw [hφeq]
    simpa only [add_sub_cancel_left] using hbound z
  have hψφ (z : Rd d) : |ψ z - φ z| ≤ M * L := by
    rw [abs_sub_comm]
    exact hφψ z
  constructor
  · exact HigherDimLFPP.lfppDistOn_le_exp_mul hφ hψ (fun z _ => hφψ z)
  · exact HigherDimLFPP.lfppDistOn_le_exp_mul hψ hφ (fun z _ => hψφ z)

end HigherDimLQGMetric
