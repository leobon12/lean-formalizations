import HigherDimLQGMetric.LfppTight.ContinuousConvolution
import HigherDimLQGMetric.ConvField.JointMain
import HigherDimLQGMetric.ConvField.WholeSpaceLimit
import HigherDimLQGMetric.ConvField.Shifts
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont

/-!
# Almost-sure continuity of the convolution of an LGF plus a bounded function

Normalize the whole-space LGF by its unit-sphere average and then use the
already established normalized-field continuity.  The bounded perturbation is
handled by continuity of ordinary convolution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_ae_continuous_convMollify {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, Continuous fun z => convMollify κ ε (h ω) z := by
  obtain ⟨_, f, _, hfbd, hb⟩ := hh
  let b : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hb' : IsWholeSpaceLGF b P := hb
  have hconv : ∀ᵐ ω ∂P, b ω ∈ convSet d := by
    filter_upwards [hb'.ae_continuousOn_sphereAvg hd] with ω hω
    exact ⟨_, hω.1 1 one_pos 0⟩
  let g : Ω → DistRd d := fun ω => addConst (b ω) (-sphereAvg (b ω) 1 0)
  have hg : IsNormalizedLGF g P := hb'.isNormalizedLGF_normalize (by omega) hconv
  have hcG := l2b_ae_convMollify_continuousOn d hd κ hκ P g hg
  have hlimG := l2b_ae_convMollify_tendsto d hd κ hκ P g hg
  have hlimB := l2b_ae_pairing_tendsto_wholeSpace d hd κ hκ P b hb'
  filter_upwards [hcG, hlimG, hlimB] with ω hcGω hlimGω hlimBω
  have hGc : Continuous fun z => convMollify κ ε (g ω) z := by
    have hp : Continuous fun z : Rd d => (ε, z) := continuous_const.prodMk continuous_id
    have hf := hcGω.comp_continuous hp (fun _ => ⟨hε, Set.mem_univ _⟩)
    simpa only [Function.comp_def, Prod.fst, Prod.snd] using hf
  obtain ⟨M, hM⟩ := hfbd ω
  have hfc : Continuous fun z => ∫ w : Rd d,
      convKernelEps κ ε (z - w) * f ω w :=
    l6a_continuous_conv_of_bddCont hd κ hκ hε (f ω) hM
  have hEq : ∀ z : Rd d,
      convMollify κ ε (h ω) z = convMollify κ ε (g ω) z +
        sphereAvg (b ω) 1 0 +
        ∫ w : Rd d, convKernelEps κ ε (z - w) * f ω w := by
    intro z
    have hbEq : addConst (g ω) (sphereAvg (b ω) 1 0) = b ω := by
      dsimp [g]
      simpa only [neg_neg] using (addConst_neg (b ω) (-sphereAvg (b ω) 1 0))
    have hhEq : addFun (b ω) (f ω) = h ω := by
      dsimp [b, addFun]
      abel
    have hB : convMollify κ ε (b ω) z =
        convMollify κ ε (g ω) z + sphereAvg (b ω) 1 0 := by
      calc
        convMollify κ ε (b ω) z =
            convMollify κ ε (addConst (g ω) (sphereAvg (b ω) 1 0)) z :=
          congrArg (fun q => convMollify κ ε q z) hbEq.symm
        _ = _ := l2b_convMollify_addConst_of_tendsto hd hκ hε (hlimGω ε hε z)
    rw [← hhEq]
    obtain ⟨a, ha⟩ := hlimBω ε hε z
    rw [l2b_convMollify_addFun_of_tendsto hd hκ hε ha (f ω) M hM]
    rw [hB]
  have hc : Continuous (fun z => convMollify κ ε (g ω) z + sphereAvg (b ω) 1 0 +
      ∫ w : Rd d, convKernelEps κ ε (z - w) * f ω w) :=
    (hGc.add continuous_const).add hfc
  exact hc.congr (fun z => (hEq z).symm)

end HigherDimLQGMetric
