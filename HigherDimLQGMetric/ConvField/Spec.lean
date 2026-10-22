import HigherDimLQGMetric.ConvField.WholeSpaceLimit
import HigherDimLQGMetric.Frozen.IsLGFPlusBddCont

/-! The exact statement of the frozen convolution characterization, proved without importing its theorem anchor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem convMollify_spec_proof :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) := by
  intro d hd κ hκ Ω _ P _ h hh ε hε
  obtain ⟨_, f, _, hfbd, hg⟩ := hh
  let g : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hglim := l2b_ae_pairing_tendsto_wholeSpace d hd κ hκ P g hg
  filter_upwards [hglim] with ω hω
  intro z
  obtain ⟨a, ha⟩ := hω ε hε z
  obtain ⟨M, hM⟩ := hfbd ω
  have hf := l2b_tendsto_pair_ofCont hd hκ hε (f ω) M hM z
  have ht : Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop
      (𝓝 (a + ∫ w : Rd d, convKernelEps κ ε (z - w) * f ω w)) := by
    convert ha.add hf using 1
    funext n
    dsimp [g]
    simp only [sub_apply, sub_add_cancel]
  rwa [l2b_convMollify_eq_of_tendsto ht]

end HigherDimLQGMetric
