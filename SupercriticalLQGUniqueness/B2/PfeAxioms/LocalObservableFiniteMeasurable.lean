import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNormalizedEquality
import SupercriticalLQGUniqueness.B2.LscTop.Limits
import LQGMetric.Papers.DFGPS.L2_17CoreB

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric LQGMetric.DFGPS.L217

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem measurable_normalizedLFPPMetric_comp
    {Ω : Type} [MeasurableSpace Ω]
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    {X : Ω → C(ℂ, ℝ)} (hX : ∀ z, Measurable fun ω => X ω z) :
    Measurable fun ω => PfeWeyl.normalizedLFPPMetric ξ a (X ω) := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  letI : BorelSpace LSCFun := ⟨rfl⟩
  apply B2.LscTop.measurable_iff_toLSCFun.mpr
  have h := B2.LscTop.measurable_rescaledLFPPFun_comp ξ a hX
  convert h using 1
  funext ω
  apply Subtype.ext
  funext p
  exact PfeWeyl.normalizedLFPPMetric_toLSCFun ξ a (X ω) p

theorem measurable_normalizedLocalizedLFPPMetric
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    Measurable fun g : DistC =>
      PfeWeyl.normalizedLFPPMetric ξ a (locMollifyC ε hε g) := by
  apply measurable_normalizedLFPPMetric_comp ξ a
  intro z
  exact (continuous_eval_const z).measurable.comp
    (measurable_locMollifyC ε hε)

end SupercriticalLQGUniqueness.B2.PfeAxioms
