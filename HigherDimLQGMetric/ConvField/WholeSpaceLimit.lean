import HigherDimLQGMetric.ConvField.RadialMain
import HigherDimLQGMetric.LGF.Normalized

/-! Improper convolution pairings for an unnormalized whole-space LGF. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l2b_ae_pairing_tendsto_wholeSpace (d : ℕ) (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
      ∃ a : ℝ, Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 a) := by
  have hconv : ∀ᵐ ω ∂P, h ω ∈ convSet d := by
    filter_upwards [hh.ae_continuousOn_sphereAvg hd] with ω hω
    exact ⟨_, hω.1 1 one_pos 0⟩
  let g : Ω → DistRd d := fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)
  have hg : IsNormalizedLGF g P := hh.isNormalizedLGF_normalize (by omega) hconv
  filter_upwards [l2b_ae_convMollify_tendsto d hd κ hκ P g hg]
    with ω hω
  intro ε hε z
  obtain ⟨a, ha⟩ : ∃ a : ℝ,
      Tendsto (fun n : ℕ => g ω (convTrunc κ ε z n)) atTop (𝓝 a) :=
    ⟨_, hω ε hε z⟩
  have hmass := (l2b_tendsto_integral_convTrunc hd hκ hε z).const_mul
    (sphereAvg (h ω) 1 0)
  refine ⟨a + sphereAvg (h ω) 1 0, ?_⟩
  convert ha.add hmass using 1
  · funext n
    dsimp [g]
    rw [addConst_apply]
    ring
  · simp

end HigherDimLQGMetric
