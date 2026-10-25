import SupercriticalLQGUniqueness.B2.PfeAxioms.S2ProdCoupling
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2CircProducer

 











set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
def IdentifiedDG20CouplingCirc (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (e : ℕ → Ioi (0 : ℝ)) (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric) : Prop :=
  IdentifiedDG20Coupling ξ m e V P' h' hN L ∧
    ∀ᵐ ω ∂P', ∀ O O' : B2.DG20Lim.RatCircle,
      Tendsto (fun n => setDistance
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))).1 O.toSet O'.toSet)
        atTop (𝓝 (setDistance (L ω).1 O.toSet O'.toSet))

 
theorem exists_normalizer_identified_coupling_circ
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate') (hRatio : DG20QuantileRatio)
    (hRel : DG20ExponentRelation) (hPos : DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ₁ : ℕ → ℕ, StrictMono φ₁ ∧
      ∃ c : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ₁ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ₁ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ₁ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        (∃ Λ : ℝ, 1 < Λ ∧
          ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
            Λ⁻¹ * (δ : ℝ) ^ Λ ≤
              (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              Λ * (δ : ℝ) ^ (-Λ)) ∧
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω')
          (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
          IdentifiedDG20CouplingCirc ξ m (ε ∘ φ₁) B2.DG20Lim.canonicalHeatVersion P' h' hN L := by
  letI : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  
  obtain ⟨φV, hφV, c, hc, Λ, hΛ, hV17⟩ := exists_real_axiomV_of_DG20LimitSkC hS4
    (dg20LimitSkC_of_dg20Inputs hS4 hPerc hRatio hRel hPos) ξ Q hQ m hm ε hε
  have hεV : Tendsto (fun n => (ε (φV n) : ℝ)) atTop (𝓝 0) := hε.comp hφV.tendsto_atTop
  
  obtain ⟨φS, hφS, -, -, hCouple⟩ := dg20LimitSkSBCirc_of_inputs hS4 hPerc hRatio hRel
    hPos ξ Q hQ m hm (fun n => ε (φV n)) hεV
  set V := B2.DG20Lim.canonicalHeatVersion with hVdef
  obtain ⟨Ω', M', SB', P', hP', h', hN, F, L, hLm, hh', hLaw, hField, hFc, hLsc, hRat, hGeom,
    hCirc⟩ :=
    hCouple normGFFLaw id normalized_canonical_model.2 V canonicalHeatVersion_isHeatSmoothing'
  letI : MeasurableSpace Ω' := M'
  letI : IsProbabilityMeasure P' := hP'
  set e : ℕ → Ioi (0 : ℝ) := fun n => ε (φV (φS n)) with he
  have hRm : ∀ n, Measurable fun g : DistC =>
      (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g)) := fun n =>
    measurable_id.prodMk (Measurable.of_eval fun p =>
      PfeWeyl.measurable_rescaledLFPP_comp (ξ : ℝ) (m (e n))
        (B2.DG20Lim.canonicalHeatVersion_measurable (e n)) p)
  
  have hLaw' : ∀ n, P'.map (fun ω => (hN n ω, F n ω)) =
      normGFFLaw.map (fun g : DistC => (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g))) :=
    fun n => hLaw n
  have hpairAE : ∀ n, AEMeasurable (fun ω => (hN n ω, F n ω)) P' := by
    intro n
    by_contra hnot
    have h0 := Measure.map_of_not_aemeasurable_of_ne_zero hnot (IsProbabilityMeasure.ne_zero P')
    rw [hLaw' n] at h0
    have h1 := congrArg (Measure.map Prod.fst) h0
    rw [Measure.map_map measurable_fst (hRm n), Measure.map_dirac' measurable_fst] at h1
    have h2 : (Prod.fst ∘ fun g : DistC => (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g))) =
        id := rfl
    rw [h2] at h1
    exact wholePlaneGFF_map_ne_dirac normGFFLaw id normalized_canonical_model.2.1 _ h1
  have hNae : ∀ n, AEMeasurable (hN n) P' := fun n => (hpairAE n).fst
  set hN' : ℕ → Ω' → DistC := fun n => (hNae n).mk (hN n) with hN'def
  have hN'm : ∀ n, Measurable (hN' n) := fun n => (hNae n).measurable_mk
  have hN'eq : ∀ᵐ ω ∂P', ∀ n, hN n ω = hN' n ω :=
    ae_all_iff.2 fun n => (hNae n).ae_eq_mk
  
  have hid : ∀ n, ∀ᵐ ω ∂P', F n ω = rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)) :=
    fun n => PfeWeyl.ae_eq_rescaledLFPP_of_joint_law (ξ : ℝ) (m (e n))
      (B2.DG20Lim.canonicalHeatVersion_measurable (e n)) P' (hN n) (F n) (hFc n) (hLaw n)
  have hidAll := ae_all_iff.2 hid
  
  have hNlaw : ∀ n, P'.map (hN' n) = normGFFLaw := by
    intro n
    rw [Measure.map_congr (hNae n).ae_eq_mk.symm]
    have h1 : (P'.map fun ω => (hN n ω, F n ω)).map Prod.fst = P'.map (hN n) :=
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hpairAE n)
    rw [← h1, hLaw' n, Measure.map_map measurable_fst (hRm n)]
    have h2 : (Prod.fst ∘ fun g : DistC => (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g))) =
        id := rfl
    rw [h2, Measure.map_id]
  refine ⟨φV ∘ φS, hφV.comp hφS, c, fun r hr => (hc r hr).comp hφS.tendsto_atTop,
    ⟨Λ, hΛ, hV17⟩, Ω', M', SB', P', hP', h', hN', L, ⟨⟨hh', hN'm, hNlaw, ?_, hLm, ?_, ?_, hGeom⟩, ?_⟩⟩
  · filter_upwards [hField, hN'eq] with ω hω heq
    simpa only [heq] using hω
  · filter_upwards [hLsc, hidAll, hN'eq] with ω hω hidω heq
    apply (PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto (ξ : ℝ) (fun n => m (e n))
      (fun n => V (e n) (hN' n ω)) (L ω)).2
    have hfun : (fun n => F n ω) = fun n => rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN' n ω)) :=
      funext fun n => by rw [hidω n, heq n]
    rw [← hfun]
    exact hω
  · filter_upwards [hRat, hidAll, hN'eq] with ω hω hidω heq
    intro u v hu hv
    exact (hω u v hu hv).congr fun n => by rw [hidω n, heq n]; rfl
  · filter_upwards [hCirc, hidAll, hN'eq] with ω hω hidω heq
    intro O O'
    refine (hω O O').congr fun n => ?_
    have hfun : (fun p => (F n ω p).toENNReal) =
        ⇑(PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN' n ω))) := by
      funext p
      rw [hidω n, heq n, ← PfeWeyl.normalizedLFPPMetric_toLSCFun, LSCMetric.toLSCFun_apply,
        EReal.toENNReal_coe]
    rw [hfun]
    rfl


 
theorem identifiedDG20CouplingCirc_comp {ξ : Ioi (0 : ℝ)} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hC : IdentifiedDG20CouplingCirc ξ m e V P' h' hN L) {ns : ℕ → ℕ} (hns : StrictMono ns) :
    IdentifiedDG20CouplingCirc ξ m (e ∘ ns) V P' h' (fun n => hN (ns n)) L := by
  obtain ⟨⟨hh', hNm, hNlaw, hField, hLm, hconv, hRat, hGeom⟩, hCirc⟩ := hC
  have ht := hns.tendsto_atTop
  refine ⟨⟨hh', fun n => hNm (ns n), fun n => hNlaw (ns n), ?_, hLm, ?_, ?_, hGeom⟩, ?_⟩
  · filter_upwards [hField] with ω hω using hω.comp ht
  · filter_upwards [hconv] with ω hω using hω.comp ht
  · filter_upwards [hRat] with ω hω using fun u v hu hv => (hω u v hu hv).comp ht
  · filter_upwards [hCirc] with ω hω using fun O O' => (hω O O').comp ht

theorem identifiedDG20Coupling_of_circ {ξ : Ioi (0 : ℝ)} {m : Ioi (0 : ℝ) → Ioi (0 : ℝ)}
    {e : ℕ → Ioi (0 : ℝ)} {V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {h' : Ω' → DistC} {hN : ℕ → Ω' → DistC} {L : Ω' → LSCMetric}
    (hC : IdentifiedDG20CouplingCirc ξ m e V P' h' hN L) :
    IdentifiedDG20Coupling ξ m e V P' h' hN L := hC.1

end SupercriticalLQGUniqueness.B2.PfeAxioms
