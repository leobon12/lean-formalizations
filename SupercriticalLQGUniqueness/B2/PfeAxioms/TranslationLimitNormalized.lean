import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationFiniteLFPP
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimit
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatTranslateVersion

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_recentered_translation_of_subseqLimit
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ,
      D (addConst (affineComp 1 z (h ω))
          (-circleAvg (h ω) 1 z)) p =
        ENNReal.ofReal (Real.exp (-(ξ : ℝ) * circleAvg (h ω) 1 z)) *
          D (h ω) (p.1 + z, p.2 + z) := by
  let g : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-circleAvg (h ω) 1 z)
  have hg : IsNormalizedWholePlaneGFF g P :=
    (B2.DG20Pt.dg20_heat_translate_normalized P h hh z 1 one_pos).1
  obtain ⟨Y, hY, hYeq⟩ :=
    B2.DG20Pt.dg20_exists_translated_heat_family P h hh X hX z
  have hE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ u : ℂ,
      Y (ε n) ω u = X (ε n) ω (u + z) - circleAvg (h ω) 1 z :=
    ae_all_iff.mpr fun n => hYeq (ε n)
  have hConvX := ae_normalizedLFPPMetric_tendsto ξ m ε D hD P h hh X hX
  have hConvY := ae_normalizedLFPPMetric_tendsto ξ m ε D hD P g hg Y hY
  filter_upwards [hE, hConvX, hConvY] with ω hEω hXω hYω
  let a : Ioi (0 : ℝ) :=
    ⟨Real.exp (-(ξ : ℝ) * circleAvg (h ω) 1 z), Real.exp_pos _⟩
  have hS : Tendsto
      (fun n => B2.LscTop.smulMetric a
        (translateMetric z (PfeWeyl.normalizedLFPPMetric
          (ξ : ℝ) (m (ε n)) (X (ε n) ω)))) atTop
      (𝓝 (B2.LscTop.smulMetric a (translateMetric z (D (h ω))))) :=
    B2.LscTop.tendsto_smulMetric tendsto_const_nhds
      (tendsto_translateMetric z hXω)
  have hEq : ∀ n,
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (Y (ε n) ω) =
        B2.LscTop.smulMetric a
          (translateMetric z (PfeWeyl.normalizedLFPPMetric
            (ξ : ℝ) (m (ε n)) (X (ε n) ω))) := by
    intro n
    apply LSCMetric.ext
    intro p
    simpa only [B2.LscTop.smulMetric_apply, translateMetric_apply, a] using
      normalizedLFPPMetric_translate_sub_const (ξ : ℝ) (m (ε n))
        (X (ε n) ω) (Y (ε n) ω) z (circleAvg (h ω) 1 z)
        (hEω n) p
  have hLimit : D (g ω) =
      B2.LscTop.smulMetric a (translateMetric z (D (h ω))) :=
    tendsto_nhds_unique hYω (by simpa only [hEq] using hS)
  intro p
  exact congrArg (fun G : LSCMetric => G p) hLimit

end SupercriticalLQGUniqueness.B2.PfeAxioms
