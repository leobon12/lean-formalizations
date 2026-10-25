import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsDG20Strong
import SupercriticalLQGUniqueness.B2.PfeAxioms.JointLSCLawPassage
import SupercriticalLQGUniqueness.B2.PfeAxioms.ContinuousLFPPMeasurable

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem exists_joint_lsc_limit_coupling_of_dg20LimitStrong
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hStrong : Inputs.DG20LimitStrong)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ (D : DistC → LSCMetric), SubseqLimit ξ m (ε ∘ φ) D →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → DistC),
          IsNormalizedWholePlaneGFF h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
            (∀ δ, IsHeatSmoothing P h δ (X δ)) →
            ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
              (_ : IsProbabilityMeasure P') (h' : Ω' → DistC)
              (L : Ω' → LSCMetric),
              IsNormalizedWholePlaneGFF h' P' ∧ Measurable L ∧
                P.map (fun ω => (h ω, (D (h ω)).toLSCFun)) =
                  P'.map (fun ω => (h' ω, (L ω).toLSCFun)) := by
  obtain ⟨φ, hφ, c, hc, hCouple⟩ := hStrong ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, ?_⟩
  intro D hD Ω _ P _ h hh X hX
  obtain ⟨Ω', M', P', hP', h', F, L, hLm, hh', hLaw, hLsc, _, _, hFc⟩ :=
    hCouple P h hh X hX
  let G : ℕ → Ω → C(ℂ × ℂ, EReal) := fun n ω =>
    B2.LscTop.rescaledLFPPMap (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)
  have hG : ∀ n, AEMeasurable (G n) P := fun n =>
    aemeasurable_rescaledLFPPMap_heat_version P h hh
      (ε (φ n)) (m (ε (φ n))) (ξ : ℝ)
      (X (ε (φ n))) (hX (ε (φ n)))
  have hGval (n : ℕ) (ω : Ω) :
      (G n ω : ℂ × ℂ → EReal) =
        rescaledLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω) := rfl
  have hSource : ∀ᵐ ω ∂P,
      LSCTendsto (fun n => (G n ω : ℂ × ℂ → EReal))
        (D (h ω)).toLSCFun.1 := by
    simpa only [hGval, Function.comp_apply] using
      (hD P h (LQGMetric.DFGPS.isGFFPlusBddCont_of_wp hh.1) X hX).1
  have hSourceMeas : AEMeasurable
      (fun ω => (D (h ω)).toLSCFun) P :=
    aemeasurable_lsc_limit_of_continuous_approximants P G hG
      (fun ω => D (h ω)) hSource
  have hLaw' : ∀ n, P'.map (fun ω => (h' ω, F n ω)) =
      P.map (fun ω => (h ω, (G n ω : ℂ × ℂ → EReal))) := by
    intro n
    simpa only [hGval] using hLaw n
  letI : MeasurableSpace Ω' := M'
  letI : IsProbabilityMeasure P' := hP'
  refine ⟨Ω', M', P', hP', h', L, hh', hLm, ?_⟩
  exact joint_lsc_limit_law_of_continuous_coupling P P' h h' hh.1 hh'.1.measurable
    G hG F hFc (fun ω => D (h ω)) hSourceMeas L hLm
    hLaw' hSource hLsc

end SupercriticalLQGUniqueness.B2.PfeAxioms
