import SupercriticalLQGUniqueness.B2.Final.PfeThm17Assembly
import SupercriticalLQGUniqueness.B2.Final.Discharged
import SupercriticalLQGUniqueness.B2.Iface.Limit
import SupercriticalLQGUniqueness.B2.Polylog.P6Closing
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RClosure
import SupercriticalLQGUniqueness.B2.QPos.QPosClosure
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatSection4Iface
import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometryTransferSkSB
import SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPNormalizer
import SupercriticalLQGUniqueness.Frozen.WeakLQGMetric_unique
import SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent

 






























set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC IsGFFPlusCont IsGFFPlusBddCont)

namespace SupercriticalLQGUniqueness.B2.Final

private theorem bddCont_to_cont {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (hh : IsGFFPlusBddCont h P) : IsGFFPlusCont h P := by
  rcases hh with ⟨hm, f, hf, _, hg⟩
  exact ⟨hm, f, hf, hg⟩

private def refEps (n : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨1 / ((n : ℝ) + 1), Set.mem_Ioi.mpr (by positivity)⟩

private theorem refEps_tendsto :
    Tendsto (fun n => (refEps n : ℝ)) atTop (𝓝 0) := by
  simpa only [refEps] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

 


theorem lfppLimitCore_of_ifaces2
    (hPfe : Iface.PfeThm17) (hPL : Iface.PLThm19Limit)
    (hMed : Iface.MedianPassage) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsWeakLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
          (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusBddCont h P →
            ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
              (∀ ε, IsHeatSmoothing P h ε (X ε)) →
              LSCTendstoInProbability P
                (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
                (fun ω => (D (h ω)).toLSCFun.1) := by
  intro ξ Q hQ
  let m₀ : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ) := fun ε =>
    Classical.choose (SupercriticalLQGUniqueness.existsUnique_isLFPPNormalizer ξ ε)
  have hm₀ : ∀ ε, IsLFPPNormalizer ξ ε (m₀ ε) := by
    intro ε
    exact (Classical.choose_spec (SupercriticalLQGUniqueness.existsUnique_isLFPPNormalizer ξ ε)).1
  obtain ⟨φ₀, hφ₀, D, c, hPfeD, hLim₀, _⟩ :=
    hPfe ξ m₀ hm₀ refEps refEps_tendsto
  have hD : IsWeakLQGMetric ξ Q D :=
    (hPL ξ Q hQ m₀ hm₀ (refEps ∘ φ₀) (refEps_tendsto.comp hφ₀.tendsto_atTop) D hLim₀ c
      hPfeD).2
  refine ⟨D, hD, ?_⟩
  intro m hm Ω _ P _ h hh X hX ε hε
  have hmEq : m = m₀ := by
    funext δ
    exact (Classical.choose_spec (SupercriticalLQGUniqueness.existsUnique_isLFPPNormalizer ξ δ)).2
      (m δ) (hm δ)
  subst m
  obtain ⟨φ, hφ, D', c', hPfeD', hLim', _⟩ := hPfe ξ m₀ hm₀ ε hε
  have hD' : IsWeakLQGMetric ξ Q D' :=
    (hPL ξ Q hQ m₀ hm₀ (ε ∘ φ) (hε.comp hφ.tendsto_atTop) D' hLim' c' hPfeD').2
  obtain ⟨C, hC, hscale⟩ := weakLQGMetric_unique ξ Q hQ D' D hD' hD
  have hC1 : C = 1 := hMed ξ m₀ hm₀ (refEps ∘ φ₀) (ε ∘ φ)
    (refEps_tendsto.comp hφ₀.tendsto_atTop) (hε.comp hφ.tendsto_atTop) D D'
    hLim₀ hLim' c c' hPfeD hPfeD' C hC hscale
  subst C
  have hscale' : ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (D' (h ω)).1 (u, v) = (D (h ω)).1 (u, v) := by
    filter_upwards [hscale P h (bddCont_to_cont P h hh)] with ω hω u v
    simpa using hω u v
  have hlimit : ∀ᵐ ω ∂P,
      (D' (h ω)).toLSCFun.1 = (D (h ω)).toLSCFun.1 := by
    filter_upwards [hscale'] with ω hω
    funext p
    exact congrArg (fun x : ℝ≥0∞ => (x : EReal)) (hω p.1 p.2)
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [(hLim' P h hh X hX).1, hlimit] with ω hconv heq
  simpa only [Function.comp_apply, heq] using hconv

 
theorem lfpp_tendstoInProbability_of_ifaces2
    (hPfe : Iface.PfeThm17) (hPL : Iface.PLThm19Limit)
    (hMed : Iface.MedianPassage) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1) := by
  intro ξ m hm Ω _ P _ h hh
  obtain ⟨Q, hQ, _⟩ := existsUnique_isLFPPExponent ξ
  obtain ⟨D, hD, hconv⟩ := lfppLimitCore_of_ifaces2 hPfe hPL hMed ξ Q hQ
  exact ⟨D ∘ h, hD.1.comp hh.1, hconv m hm P h hh⟩

 

theorem exists_strongLQGMetric_lfppLimit_of_ifaces2
    (hPfe : Iface.PfeThm17) (hPL : Iface.PLThm19Limit)
    (hMed : Iface.MedianPassage) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1) := by
  intro ξ Q hQ
  obtain ⟨D, hD, hconv⟩ := lfppLimitCore_of_ifaces2 hPfe hPL hMed ξ Q hQ
  exact ⟨D, iface_weakToStrong_proved ξ Q D hQ hD, hconv⟩

 
theorem dg20Interfaces_of_lane (hC2 : DG20LaneC2Star) (hInd : DG20LaneFineStarIndep) :
    DG20Interfaces := by
  have hEx : DG20Conc.LaneA4ExponentExists := fun ξ => (existsUnique_isLFPPExponent ξ).exists
  have hPos : Iface.DG20ExponentPositive := QPos.dg20ExponentPositive_proved
  have hRatio : Iface.DG20QuantileRatio :=
    DG20Conc.laneA4_dg20QuantileRatio_of_inputs hC2 hInd hEx hPos
  have hRel : Iface.DG20ExponentRelation :=
    DG20Conc.laneA4_dg20ExponentRelation_of_inputs hC2 hInd hEx hPos
  have hPerc : Iface.DG20PercEstimate' :=
    DG20Conc.laneA4_dg20PercEstimate_of_inputs hC2 hInd hEx hPos
  exact ⟨DG20Pt.dg20Section4_of_inputs hPerc hRel hPos, hPerc, hRatio, hRel, hPos,
    iface_lscTop_proved⟩

 
theorem iface_plThm19Limit_of_dg20Interfaces (hI : DG20Interfaces) : Iface.PLThm19Limit := by
  obtain ⟨_, hPerc, _, hRel, hPos, _⟩ := hI
  exact Polylog.iface_plThm19Limit_of_dg20 hPerc hRel hPos

 
theorem iface_medianPassage_of_open_inputs (hI : DG20Interfaces)
    (hMed : MedianPassageOfGeometry) : Iface.MedianPassage := by
  obtain ⟨hS4, hPerc, hRatio, hRel, hPos, hTop⟩ := id hI
  let _ : MeasurableSpace LSCFun := borel LSCFun
  have : BorelSpace LSCFun := ⟨rfl⟩
  have hSB := DG20Lim.dg20LimitSkSB_of_inputs hS4 hPerc hRatio hRel hPos hTop
  exact hMed hI (PfeAxioms.limitLengthSpace0_of_dg20LimitSkSB hSB)
    (PfeAxioms.limitEuclideanControl0_of_dg20LimitSkSB hSB)

 


theorem theorems_1_3_and_1_8i_of_open_inputs
    (hC2 : DG20LaneC2Star) (hInd : DG20LaneFineStarIndep)
    (hSA : DG20SmallAnnuliCoupling) (hAT : DG20CoupledAcrossTailsInput)
    (hLoc : PfeL5ObsLocality) (hMed : MedianPassageOfGeometry) :
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
              (fun ω => (D (h ω)).toLSCFun.1)) := by
  have hI := dg20Interfaces_of_lane hC2 hInd
  have hPfe := iface_pfeThm17_of_open_inputs hI hSA hAT hLoc
  have hPL := iface_plThm19Limit_of_dg20Interfaces hI
  have hM := iface_medianPassage_of_open_inputs hI hMed
  exact ⟨lfpp_tendstoInProbability_of_ifaces2 hPfe hPL hM,
    exists_strongLQGMetric_lfppLimit_of_ifaces2 hPfe hPL hM⟩

 
theorem theorems_1_3_and_1_8i_of_allOpenInputs (h : AllOpenInputs) :
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
              (fun ω => (D (h ω)).toLSCFun.1)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact theorems_1_3_and_1_8i_of_open_inputs h1 h2 h3 h4 h5 h6

 
theorem lfpp_tendstoInProbability_of_open_inputs (h : AllOpenInputs) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1) :=
  (theorems_1_3_and_1_8i_of_allOpenInputs h).1

 

theorem exists_strongLQGMetric_lfppLimit_of_open_inputs (h : AllOpenInputs) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1) :=
  (theorems_1_3_and_1_8i_of_allOpenInputs h).2




example (h : AllOpenInputs) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1) := by
  exact lfpp_tendstoInProbability_of_open_inputs h

example (h : AllOpenInputs) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1) := by
  exact exists_strongLQGMetric_lfppLimit_of_open_inputs h

end SupercriticalLQGUniqueness.B2.Final
