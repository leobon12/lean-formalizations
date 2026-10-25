import SupercriticalLQGUniqueness.B2.Final.OpenInputs3
import SupercriticalLQGUniqueness.B2.Final.Assembly2
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RProved
import SupercriticalLQGUniqueness.B2.Median.MedianPassage
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Iface
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdAcrossCoupled

 
















set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC IsGFFPlusCont IsGFFPlusBddCont)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 
theorem dg20Interfaces_proved : DG20Interfaces :=
  dg20Interfaces_of_lane DG20Conc.laneC2StarAt_proved.{0}
    DG20Conc.laneFineStar_indep_coarse_proved.{0}

 
theorem medianPassageOfGeometry_proved : MedianPassageOfGeometry :=
  fun _ _ hEC => Median.iface_medianPassage_of_limitEuclideanControl0 hEC

 



theorem dg20SmallAnnuliCoupling_of_split (h3a : DG20CouplingSmallAnnuli)
    (h3b : PfeS1SmallAnnuli) (h3c : PfePointCircles) : DG20SmallAnnuliCoupling := by
  intro hI ξ Q hQ m hm ε hε
  obtain ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hsa⟩ := h3a hI ξ Q hQ m hm ε hε
  let _ : MeasurableSpace Ω' := M'
  have : StandardBorelSpace Ω' := SB'
  have : IsProbabilityMeasure P' := hP'
  have hat : CoupledAcrossTails P' L :=
    PfeAxioms.dg20CoupledAcrossTailsInput_proved hI ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L hB
  refine ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN, L, hB, hsa, ?_⟩
  intro Φ hΦ hII
  obtain ⟨ψ₁, hψ₁, hsmall⟩ :=
    h3b hI ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L hB hsa hat Φ hΦ hII
  have hB₁ : DG20CouplingData ξ Q m (fun n => ε (φ₁ (ψ₁ n))) c V P' h'
      (fun n => hN (ψ₁ n)) L := hB.comp hψ₁
  have hsa₁ : CoupledSmallAnnuli ξ m (fun n => ε (φ₁ (ψ₁ n))) V P'
      (fun n => hN (ψ₁ n)) L := hsa.comp hψ₁
  obtain ⟨ψ₂, hψ₂, hpts⟩ := h3c hI ξ Q m (fun n => ε (φ₁ (ψ₁ n))) c V P' h'
    (fun n => hN (ψ₁ n)) L hB₁ hsa₁ hat Φ hΦ hII
  exact ⟨fun n => ψ₁ (ψ₂ n), hψ₁.comp hψ₂, PfeWeyl.normalizedSmallAnnuli_comp hsmall hψ₂, hpts⟩

 


theorem theorems_1_3_and_1_8i_of_remaining
    (h3a : DG20CouplingSmallAnnuli) (h3b : PfeS1SmallAnnuli) (h3c : PfePointCircles) :
    (∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1)) ∧
    (∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1)) :=
  theorems_1_3_and_1_8i_of_open_inputs DG20Conc.laneC2StarAt_proved.{0}
    DG20Conc.laneFineStar_indep_coarse_proved.{0} (dg20SmallAnnuliCoupling_of_split h3a h3b h3c)
    PfeAxioms.dg20CoupledAcrossTailsInput_proved PfeLocal.pfeL5ObsLocality_proved
    medianPassageOfGeometry_proved

 
theorem lfpp_tendstoInProbability_of_remaining (h : RemainingInputs) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1) :=
  (theorems_1_3_and_1_8i_of_remaining h.1 h.2.1 h.2.2).1

 
theorem exists_strongLQGMetric_lfppLimit_of_remaining (h : RemainingInputs) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1) :=
  (theorems_1_3_and_1_8i_of_remaining h.1 h.2.1 h.2.2).2

end SupercriticalLQGUniqueness.B2.Final
