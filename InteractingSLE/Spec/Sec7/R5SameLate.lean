/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5SameRef
import InteractingSLE.Spec.Sec7.SideC3Records
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefLaw
import InteractingSLE.Spec.Sec7.PocketSideInCensusVersions

/-!
# Lemma R.5's old references on a late side test: heights at the counterflow hull

Packet PROVE-R5-SAMETIME. The late (both-low) analogue of `R5Same.ae_tendsto_harmRep_ref`: for a `Ready` side test
`j` and the actual old hull reference `j.capacityReference i d s` (the pocket exterior filled on the test event,
together with the counterflow hull at the original time `s`), every local-set mean of the reference has, almost
surely on the test event, at every point of the hull inside the pocket and along every approach whose image under the
ambient map `f_s` tends to a real non-jump point `x`, the reading `harmRep g + 𝔥₀ + χ arg f_s′ → β_s(x)` — the ambient
word at time `s` (the height part of `Wire.VisitReferenceHeightCoverPosExc`, read in the ambient lift).

* `measurable_hitting_of_disjoint`: hitting measurability from the avoidance events;
* `measurableSet_disjoint_eventFilled_empty`: the avoidance events of the filled pocket exterior;
* **`initialReference_facts`**: the late pocket exterior `eventFilled j.event domain ∅` is hitting-measurable,
  determined
  by the coupled centred field and local (the late raw reference law at time `0`,
  `raw_reference_law_at_original_time`);
* **`ae_tendsto_harmRep_capacityReference`**.

The inputs are exactly those of `Wire.Current.SideTest.raw_reference_law_at_original_time`. Ruling R48: nothing here
uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Same

open LocalSets WholeField Aux119Heights PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop
  PocketWordPerQ PocketCoord PocketJordan PocketStopSide PocketTraversal Lemma71C PocketUnionPt

section Hitting

variable {Ω : Type*}

/-- **Hitting measurability from the avoidance events** of the open subsets of `ℍ`. -/
theorem measurable_hitting_of_disjoint {𝒢 : MeasurableSpace Ω} {E : Ω → Set ℂ}
    (hE : ∀ V : Set ℂ, IsOpen V → V ⊆ H → MeasurableSet[𝒢] {ω | Disjoint (E ω) V}) :
    Measurable[𝒢, hittingSigma] E := by
  refine @measurable_generateFrom Ω (Set ℂ) 𝒢 _ _ ?_
  rintro _ ⟨V, hVo, hVH, rfl⟩
  have e : E ⁻¹' {S : Set ℂ | (S ∩ V).Nonempty} = {ω | Disjoint (E ω) V}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
  rw [e]
  exact (hE V hVo hVH).compl

/-- **The avoidance events of the filled pocket exterior** `eventFilled M C ∅` are events of any σ-algebra containing
the pocket-inclusion events on `M`. -/
theorem measurableSet_disjoint_eventFilled_empty {𝒢 : MeasurableSpace Ω} {M : Set Ω} {C : Ω → Set ℂ}
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝒢] {ω | ω ∈ M ∧ U ⊆ C ω})
    {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet[𝒢] {ω | Disjoint (eventFilled M C (fun _ => ∅) ω) U} := by
  rcases U.eq_empty_or_nonempty with hU | hU
  · have e : {ω | Disjoint (eventFilled M C (fun _ => ∅) ω) U} = univ := by
      ext ω
      simp only [hU, disjoint_empty, mem_ofPred_eq, mem_univ]
    rw [e]
    exact MeasurableSet.univ
  · have e : {ω | Disjoint (eventFilled M C (fun _ => ∅) ω) U} = {ω | ω ∈ M ∧ U ⊆ C ω} := by
      ext ω
      simp only [mem_ofPred_eq]
      by_cases hω : ω ∈ M
      · rw [eventFilled, ite_eq_left hω, extHullSet, union_empty]
        constructor
        · intro hd
          refine ⟨hω, fun z hz => ?_⟩
          by_contra hzC
          exact disjoint_left.1 hd ⟨hUH hz, hzC⟩ hz
        · rintro ⟨-, hUC⟩
          exact disjoint_left.2 fun z hz hzU => hz.2 (hUC hzU)
      · rw [eventFilled, ite_eq_right hω]
        simp only [hω, false_and, iff_false]
        obtain ⟨z, hz⟩ := hU
        exact fun hd => disjoint_left.1 hd (hUH hz) hz
    rw [e]
    exact hCin U hUo hUH

/-- The filled reference with a hull `K ⊆ ℍ` is the filled pocket exterior together with `K`. -/
theorem eventFilled_empty_union {M : Set Ω} {C K : Ω → Set ℂ} (hKH : ∀ ω, K ω ⊆ H) (ω : Ω) :
    eventFilled M C (fun _ => ∅) ω ∪ K ω = eventFilled M C K ω := by
  by_cases hω : ω ∈ M
  · rw [eventFilled, ite_eq_left hω, eventFilled, ite_eq_left hω, extHullSet, extHullSet]
    ext z
    simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_empty_iff_false, or_false]
    constructor
    · rintro (⟨hz, hzC⟩ | hzK)
      · exact ⟨hz, Or.inl hzC⟩
      · exact ⟨hKH ω hzK, Or.inr hzK⟩
    · rintro ⟨hz, hzC | hzK⟩
      · exact Or.inl ⟨hz, hzC⟩
      · exact Or.inr hzK
  · rw [eventFilled, ite_eq_right hω, eventFilled, ite_eq_right hω]
    exact union_eq_left.2 (hKH ω)

end Hitting

section Late

open Wire.Current Wire.Current.SideTest

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}

theorem event_subset_outerEvent (hj : j.Ready d) : j.event ⊆ j.outerEvent := by
  rcases hj with ⟨-, -, -, -, -, -, -, -, hAG, -⟩
  intro ω hω
  cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;> exact (hAG hω).1

/-- **The late pocket exterior** (the initial capacity reference `eventFilled j.event domain ∅`) is hitting-measurable,
determined by the coupled centred field, and local. The inputs are those of `raw_reference_law_at_original_time`. -/
theorem initialReference_facts [IsProbabilityMeasure d.measure] (hj : j.Ready d)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure) :
    Measurable[mΩ, hittingSigma] (eventFilled j.event (j.target i d).domain fun _ => ∅) ∧
      MeasurableSpace.comap (eventFilled j.event (j.target i d).domain fun _ => ∅) hittingSigma ≤
        aeSigma (MeasurableSpace.comap (j.target i d).zeroField inferInstance) d.measure ∧
      IsLocalSet (eventFilled j.event (j.target i d).domain fun _ => ∅) (j.target i d).zeroField d.measure := by
  obtain ⟨-, hloc, -⟩ := raw_reference_law_at_original_time hj hTransport hTranslate hu hh hCoupling hu' hKilled
    hLife hCont hStart hMeas hDetermined hLocal 0
  rw [target_event, original_filling_zero] at hloc
  have hRc : ∀ ω, Continuous (d.rightWall ω) := fun ω => hCont 0 ω
  have hLc : ∀ ω, Continuous (d.leftWall j.seed ω) := fun ω => hCont 1 ω
  have hRm : ∀ t, Measurable fun ω => d.rightWall ω t := fun t => hMeas 0 t
  have hLm : ∀ t, Measurable fun ω => d.leftWall j.seed ω t := fun t => hMeas 1 t
  have hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.rightWall ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω) :=
    fun t => hDetermined 0 t
  have hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => d.leftWall j.seed ω t) =ᵐ[d.measure] fun ω => f (centredField d.field d.originalMean ω) :=
    fun t => hDetermined 1 t
  have hsub := event_subset_outerEvent hj
  rcases hj with ⟨-, hGm, -, hG, -, -, -, hAm, -⟩
  have hRm' := measurable_right_wallsSigma (P := d.measure) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := d.measure) hRc hLc
  have hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[wallsSigma d.measure d.rightWall (d.leftWall j.seed)]
      {ω | ω ∈ j.event ∧ U ⊆ (j.target i d).domain ω} := fun U hUo hUH => by
    rw [target_domain]
    exact Lemma725RefMarks.measurableSet_subset_cfPocket hRm' hLm' hGm (fun ω hω => (hG ω hω).1) hAm hsub hUo hUH
  have hmE : Measurable[mΩ, hittingSigma] (eventFilled j.event (j.target i d).domain fun _ => ∅) :=
    measurable_hitting_of_disjoint fun V hVo hVH =>
      wallsSigma_le hRm hLm _ (measurableSet_disjoint_eventFilled_empty hCin hVo hVH)
  have hreg : ∀ᵐ ω ∂d.measure, (eventFilled j.event (j.target i d).domain fun _ => ∅) ω ⊆ H ∧
      IsOpen (H \ (eventFilled j.event (j.target i d).domain fun _ => ∅) ω) := by
    refine Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ j.event
    · rw [eventFilled, ite_eq_left hω, extHullSet, union_empty, target_domain]
      have hc := (hG ω (hsub hω)).1
      have hCH : cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) ⊆ H :=
        PocketJordan.image_negInv_subset_H hc.changePocket_subset_H
      have hCo : IsOpen (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)) :=
        isOpen_image_negInv' hc.isOpen_changePocket hc.changePocket_subset_H
      refine ⟨inter_subset_left, ?_⟩
      have e : H \ (H ∩ (cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))ᶜ) =
          cfPocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) := by
        ext z
        simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, not_and, not_not]
        exact ⟨fun hz => hz.2 hz.1, fun hz => ⟨hCH hz, fun _ => hz⟩⟩
      rw [e]
      exact hCo
    · rw [eventFilled, ite_eq_right hω, Set.sdiff_self]
      exact ⟨subset_rfl, isOpen_empty⟩
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (j.target i d).zeroField d.measure := by
    rw [target_zeroField]
    exact isZeroBoundaryGFF_centredField hCoupling hu'
  refine ⟨hmE, ?_, ((isLocalSet_tfae hh0 hmE hreg).out 1 4).1 ?_⟩
  · have hWle := wallsSigma_le_aeSigma (P := d.measure) hTransport hTranslate hu hu'.1 hdetR hdetL
    rw [target_zeroField]
    exact Theorem14.WalkBdry.hitting_comap_le_aeSigma fun U hUH => hWle _
      (measurableSet_disjoint_eventFilled_empty hCin U.isOpen hUH)
  · exact hloc.isAvoidanceLocal

/-- **R.5's late old reference at an original time keeps the ambient word at the counterflow hull**: for a `Ready`
side test and every local-set mean `g` of the actual old hull reference `j.capacityReference i d s`, almost surely on
the test event, at every point `z₀` of the counterflow hull inside the pocket and along every approach `F` (within `ℍ`
at `ξ`) staying in the reference complement whose image under the ambient map `f_s` tends to a real point `x` off the
jump set at time `s`: `harmRep g + 𝔥₀ + χ arg f_s′ → β_s(x)` (the force data at the centred positions at time `s`).
-/
theorem ae_tendsto_harmRep_capacityReference [IsProbabilityMeasure d.measure] (hj : j.Ready d)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure) (s : ℝ≥0) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (j.capacityReference i d s) (j.target i d).zeroField d.measure g) :
    ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ z₀ ∈ (j.target i d).domain ω ∩ regHull d.driver d.lifetime s ω,
      ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun a => d.forceL a s ω - d.driver s ω) (fun a => d.forceR a s ω - d.driver s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) → (∀ᶠ y in 𝓝[H] ξ, F y ∈ H \ j.capacityReference i d s ω) →
      Tendsto (fun y => fwdMap (fun t : ℝ => d.driver t.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ j.capacityReference i d s ω) (F y) + d.coupledMean (F y) +
          chiC i.kappa * (logDerivFwd (fun t : ℝ => d.driver t.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData i.kappa d.rhoL d.rhoR (fun a => d.forceL a s ω - d.driver s ω)
          (fun a => d.forceR a s ω - d.driver s ω) x)) := by
  obtain ⟨hEm, hEd, hEl⟩ := initialReference_facts hj hTransport hTranslate hu hh hCoupling hu' hKilled hLife hCont
    hStart hMeas hDetermined hLocal
  rw [target_zeroField] at hEd hEl hg
  have hsub := event_subset_outerEvent hj
  have hG : ∀ ω ∈ j.outerEvent, IsChangeConfigInc (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) :=
    fun ω hω => (hj.2.2.2.1 ω hω).1
  have hKH : ∀ ω, regHull d.driver d.lifetime s ω ⊆ H := fun ω z hz => hz.1
  have hunion : (fun ω => eventFilled j.event (j.target i d).domain (fun _ => ∅) ω ∪ regHull d.driver d.lifetime s ω) =
      j.capacityReference i d s := funext (eventFilled_empty_union hKH)
  have hg' : IsLocalSetMean (fun ω => eventFilled j.event (j.target i d).domain (fun _ => ∅) ω ∪
      regHull d.driver d.lifetime s ω) (centredField d.translatedField d.coupledMean) d.measure g := by
    rw [hunion]
    exact hg
  have hKm : Measurable[mΩ, hittingSigma] (regHull d.driver d.lifetime s) :=
    measurable_regHull (T := fun _ => s) hKilled measurable_const
  have hsζ : ∀ᵐ ω ∂d.measure, (s : ℝ≥0∞) < d.lifetime ω := by
    filter_upwards [hLife] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hKeq : ∀ᵐ ω ∂d.measure, regHull d.driver d.lifetime s ω = fwdHull (fun t : ℝ => d.driver t.toNNReal ω) s := by
    filter_upwards [hLife, hCoupling.1.2.2.2.2] with ω hζω hp
    have hcont : Continuous fun t => d.driver t ω := by
      rw [← continuousOn_univ]
      refine hp.2.2.2.1.mono fun t _ => ?_
      show ((t : ℝ≥0∞)) < d.lifetime ω
      rw [hζω]
      exact ENNReal.coe_lt_top
    exact regHull_eq hcont hζω s
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  filter_upwards [ae_tendsto_harmRep_unionMean hCoupling hκ hu' hKilled s hsζ hKm hKeq hEm hEd hEl hg']
    with ω hω hωA z₀ hz₀ F ξ x hx hF hFU hfF
  have hc := hG ω (hsub hωA)
  have hCo : IsOpen ((j.target i d).domain ω) := by
    rw [target_domain]
    exact isOpen_image_negInv' hc.isOpen_changePocket hc.changePocket_subset_H
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hCo z₀ hz₀.1
  have hball' : ∃ ρ > 0, eventFilled j.event (j.target i d).domain (fun _ => ∅) ω ∩ ball z₀ ρ ⊆
      regHull d.driver d.lifetime s ω := by
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    rw [eventFilled, ite_eq_left hωA, extHullSet, union_empty] at hz
    exact absurd (hball hz.2) hz.1.2
  have he := eventFilled_empty_union (M := j.event) (C := (j.target i d).domain) hKH ω
  have hcap : j.capacityReference i d s ω =
      eventFilled j.event (j.target i d).domain (fun _ => ∅) ω ∪ regHull d.driver d.lifetime s ω := he.symm
  rw [hcap] at hFU ⊢
  exact hω z₀ hz₀.2 hball' F ξ x hx hF hFU hfF

end Late

end InteractingSLE.Sec7.R5Same
