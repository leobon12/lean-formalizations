import SupercriticalLQGUniqueness.B2.PfeAxioms.IdentifiedCouplingSkSB
import SupercriticalLQGUniqueness.B2.PfeAxioms.AnalyticImageTransfer
import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometrySubsequence
import SupercriticalLQGUniqueness.Exponent.HeatVersion

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem ae_geometry_of_dg20LimitSkSB
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkSB : Inputs.DG20LimitSkSB)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
      (∀ u v : ℂ, (D (h ω)).1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          (D (h ω)).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
            (D (h ω)).len γ a b = (D (h ω)).1 (u, v)) := by
  obtain ⟨φ, hφ, hCouple⟩ :=
    exists_identified_sk_standardBorel_coupling hSkSB ξ Q hQ m hm ε hε
  have hDφ : SubseqLimit ξ m (ε ∘ φ) D :=
    subseqLimit_comp_strictMono ξ m ε D hD φ hφ
  let X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ =>
    (exists_heatVersion hh (δ : ℝ) δ.2).choose
  have hX : ∀ δ, IsHeatSmoothing P h δ (X δ) := fun δ =>
    (exists_heatVersion hh (δ : ℝ) δ.2).choose_spec.2
  obtain ⟨Ω', M', SB', P', hP', h', L, hh', hLm, _hJoint, hIdent, hGeom⟩ :=
    hCouple D hDφ P h hh X hX
  letI : MeasurableSpace Ω' := M'
  letI : StandardBorelSpace Ω' := SB'
  letI : IsProbabilityMeasure P' := hP'
  have hLaw : P.map h = P'.map h' :=
    (normGFFLaw_eq_of_normalized P h hh).symm.trans
      (normGFFLaw_eq_of_normalized P' h' hh')
  have hTarget : ∀ᵐ ω ∂P',
      (D (h' ω)).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (D (h' ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
      (∀ u v : ℂ, (D (h' ω)).1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          (D (h' ω)).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
            (D (h' ω)).len γ a b = (D (h' ω)).1 (u, v)) := by
    filter_upwards [hIdent, hGeom] with ω hEq hG
    simpa only [← hEq] using hG
  exact ae_field_property_of_standardBorel_coupling P P' h h'
    hh.1.measurable hh'.1.measurable hLaw
    (fun g => (D g).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (D g).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
      (∀ u v : ℂ, (D g).1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          (D g).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
            (D g).len γ a b = (D g).1 (u, v))) hTarget

 
theorem limitLengthSpace0_of_dg20LimitSkSB
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkSB : Inputs.DG20LimitSkSB) : Inputs.LimitLengthSpace0 := by
  intro ξ Q hQ m ε D hm hε hD Ω _ P _ h hh
  filter_upwards [ae_geometry_of_dg20LimitSkSB hSkSB ξ Q hQ m hm ε hε
    D hD P h hh] with ω hGeom
  exact hGeom.1

 
theorem limitEuclideanControl0_of_dg20LimitSkSB
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkSB : Inputs.DG20LimitSkSB) : Inputs.LimitEuclideanControl0 := by
  intro ξ Q hQ m ε D hm hε hD Ω _ P _ h hh
  filter_upwards [ae_geometry_of_dg20LimitSkSB hSkSB ξ Q hQ m hm ε hε
    D hD P h hh] with ω hGeom
  exact hGeom.2.1

 

theorem ae_finiteGeodesics_of_dg20LimitSkSB
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkSB : Inputs.DG20LimitSkSB)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (h ω)).1 (u, v) < ∞ →
      ∃ (γ : ℝ → ℂ) (a b : ℝ),
        (D (h ω)).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
          (D (h ω)).len γ a b = (D (h ω)).1 (u, v) := by
  filter_upwards [ae_geometry_of_dg20LimitSkSB hSkSB ξ Q hQ m hm ε hε
    D hD P h hh] with ω hGeom
  exact hGeom.2.2

end SupercriticalLQGUniqueness.B2.PfeAxioms
