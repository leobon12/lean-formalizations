import SupercriticalLQGUniqueness.B2.PfeAxioms.IdentifiedCouplingStrong
import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsDG20StrongSB

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 

theorem exists_identified_standardBorel_coupling
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hStrong : Inputs.DG20LimitStrongSB)
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
            ∃ (Ω' : Type) (_ : MeasurableSpace Ω')
              (_ : StandardBorelSpace Ω') (P' : Measure Ω')
              (_ : IsProbabilityMeasure P') (h' : Ω' → DistC)
              (L : Ω' → LSCMetric),
              IsNormalizedWholePlaneGFF h' P' ∧ Measurable L ∧
              P.map (fun ω => (h ω, (D (h ω)).toLSCFun)) =
                P'.map (fun ω => (h' ω, (L ω).toLSCFun)) ∧
              (∀ᵐ ω ∂P', L ω = D (h' ω)) ∧
              (∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
                (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
                  ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
                (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
                  ∃ (γ : ℝ → ℂ) (a b : ℝ),
                    (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
                      (L ω).len γ a b = (L ω).1 (u, v))) := by
  obtain ⟨φ, hφ, c, hc, hCouple⟩ := hStrong ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, ?_⟩
  intro D hD Ω _ P _ h hh X hX
  obtain ⟨Ω', M', SB', P', hP', h', F, L, hLm, hh', hLaw, hLsc, _, hGeom, hFc⟩ :=
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
  letI : StandardBorelSpace Ω' := SB'
  letI : IsProbabilityMeasure P' := hP'
  have hJoint := joint_lsc_limit_law_of_continuous_coupling P P' h h'
    hh.1 hh'.1.measurable G hG F hFc (fun ω => D (h ω))
    hSourceMeas L hLm hLaw' hSource hLsc
  have hCanonSource := ae_canonicalLSCLimit_eq ξ m (ε ∘ φ) D hD
    P h hh X hX
  have hCanonTarget : ∀ᵐ ω ∂P',
      canonicalLSCLimit ξ m (ε ∘ φ) (h' ω) = (D (h' ω)).toLSCFun := by
    let X' : Set.Ioi (0 : ℝ) → Ω' → C(ℂ, ℝ) := fun δ =>
      (exists_heatVersion hh' (δ : ℝ) δ.2).choose
    have hX' : ∀ δ, IsHeatSmoothing P' h' δ (X' δ) := fun δ =>
      (exists_heatVersion hh' (δ : ℝ) δ.2).choose_spec.2
    exact ae_canonicalLSCLimit_eq ξ m (ε ∘ φ) D hD
      P' h' hh' X' hX'
  have hCanonCoupled := ae_target_eq_canonical_of_joint_law P P' h h'
    hh.1.measurable hh'.1.measurable (fun ω => D (h ω)) L hLm
    (canonicalLSCLimit ξ m (ε ∘ φ))
    (measurable_canonicalLSCLimit ξ m (ε ∘ φ)) hCanonSource hJoint
  have hIdent : ∀ᵐ ω ∂P', L ω = D (h' ω) := by
    filter_upwards [hCanonTarget, hCanonCoupled] with ω hT hC
    apply B2.LscTop.toLSCFun_injective
    exact hC.symm.trans hT
  exact ⟨Ω', M', SB', P', hP', h', L, hh', hLm, hJoint, hIdent, hGeom⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
