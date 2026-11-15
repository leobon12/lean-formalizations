/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerCPath1
import InteractingSLE.Spec.Restart.FCK2SourceWord
import InteractingSLE.Spec.Restart.FCK2TermClock
import InteractingSLE.Spec.Restart.RetFinGlue
import InteractingSLE.Spec.Restart.RetPlumbLine

/-!
# Theorem 1.5's corrected forward inputs: the Gaussian field for the first path

Packet PROVE-T15-FCKER3 (R82). The Gaussian field of `FCK2CapForwardInputsC` for the first canonical chart path,
proved from the per-cap kernels of Aux. 77 (`exists_fcBoxKernel_physical`), Aux. 79's word mean on the later boxes
(`ae_lineBox_mean_word_geom`, with the deterministic side orientation `IsFCLine.isFCSideSign`), the chart law at a
random capacity time (`Aux79.ae_condExp_cexp_chartTransport_eq_cfAt_rand`), the glued forward marks
(`hasFCK2CapForwardKernel_of_boxLaw`) and the physical readability of the clock and of the driver on the clock cuts
(`FCKerCRead`).

* `exists_measurable_good`, `measurable_fcPhysical_of_ae_eq`, `chart_measurability_fcPhysical`;
* `forceData_of_mean_eq` (FCKER2's "word condition");
* **`hasFCK2CapForwardKernel_path₁`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerC

open Sec6 LocalSets FCAux79 WholeField DomainMarkov DomainMarkov.K2 DomainMarkov.Aux79 Coupling RetAux79
  Sec7.PocketTraversal

universe u

section Helpers

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {α : Type*} [Zero α]

/-- A measurable almost sure event on which a property holds pointwise. -/
theorem exists_measurable_good {p : Ω → Prop} (h : ∀ᵐ ω ∂P, p ω) :
    ∃ G : Set Ω, MeasurableSet G ∧ (∀ᵐ ω ∂P, ω ∈ G) ∧ ∀ ω ∈ G, p ω := by
  refine ⟨(toMeasurable P {ω | p ω}ᶜ)ᶜ, (measurableSet_toMeasurable P _).compl, ?_, fun ω hω => ?_⟩
  · rw [ae_iff]
    have he : {ω | ¬ ω ∈ (toMeasurable P {ω | p ω}ᶜ)ᶜ} = toMeasurable P {ω | p ω}ᶜ := by
      ext ω
      simp only [mem_compl_iff, not_not, mem_ofPred_eq]
    rw [he, measure_toMeasurable]
    exact ae_iff.1 h
  · by_contra hn
    exact hω (subset_toMeasurable P _ hn)

/-- A measurable almost sure event is retained-measurable. -/
theorem measurableSet_retSigma_of_ae {d : PairData Ω} {G : Set Ω} (hG : MeasurableSet G)
    (h : ∀ᵐ ω ∂P, ω ∈ G) : MeasurableSet[retSigma d P] G := by
  refine measurableSet_retSigma_iff.2 ⟨hG, univ, MeasurableSet.univ, ?_⟩
  filter_upwards [h] with ω hω
  simp only [hω, mem_univ]

/-- A measurable function almost surely equal to a physical variable is a physical variable. -/
theorem measurable_fcPhysical_of_ae_eq {d : PairData Ω} {t : ℝ≥0} {β : Type*} [MeasurableSpace β]
    {f g : Ω → β} (hf : Measurable f) (hg : Measurable[fcPhysicalFiltration P d t] g) (h : f =ᵐ[P] g) :
    Measurable[fcPhysicalFiltration P d t] f := by
  intro B hB
  obtain ⟨G', hG', he⟩ := (hg hB).2
  refine ⟨hf hB, G', hG', ?_⟩
  refine EventuallyEq.trans ?_ he
  filter_upwards [h] with ω hω
  simp only [mem_preimage, hω]

omit mΩ in
/-- Indicators of chart coordinates agree when the charts agree. -/
theorem indicator_chart_congr {d d' : PairData Ω} {ω : Ω} (hω : d'.chart ω = d.chart ω) (z : ℂ)
    (f : Chart → ℂ → α) :
    ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => f (d.chart ω) z) ω =
      ({ω | z ∈ (d'.chart ω).dom}.indicator fun ω => f (d'.chart ω) z) ω := by
  have hm : ω ∈ {ω | z ∈ (d'.chart ω).dom} ↔ ω ∈ {ω | z ∈ (d.chart ω).dom} := by
    simp only [mem_ofPred_eq, hω]
  by_cases hz : ω ∈ {ω | z ∈ (d.chart ω).dom}
  · rw [indicator_of_mem hz, indicator_of_mem (hm.2 hz), hω]
  · rw [indicator_of_notMem hz, indicator_of_notMem fun h => hz (hm.1 h)]

/-- **The first-contact chart is measurable for the physical record** (it agrees on the good event with the chart
of `stopData d`, which is retained-measurable). -/
theorem chart_measurability_fcPhysical {d : PairData Ω} (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G)
    (t : ℝ≥0) :
    (∀ z, MeasurableSet[fcPhysicalFiltration P d t] {ω | z ∈ (d.chart ω).dom}) ∧
    (∀ z, Measurable[fcPhysicalFiltration P d t]
      ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).1 z)) ∧
    (∀ z, Measurable[fcPhysicalFiltration P d t]
      ({ω | z ∈ (d.chart ω).dom}.indicator fun ω => (d.chart ω).2.2 z)) := by
  have hR : retSigma d P ≤ fcPhysicalFiltration P d t := retSigma_le_fcPhysicalFiltration P d t
  have hdS := hd.isMeasGood_stopData hG
  obtain ⟨hS1, hS2, hS3⟩ := @PairData.IsMeasGood.chart_measurability Ω (retSigma d P) (stopData d) hdS
  obtain ⟨h1, h2, h3⟩ := hd.chart_measurability
  have hch : ∀ᵐ ω ∂P, (stopData d).chart ω = d.chart ω := hG.mono fun ω hω => chart_stopData_eq hd hω
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_⟩
  · refine measurableSet_fcPhysical_of_ae_eq (h1 z) (hR _ (hS1 z)) ?_
    filter_upwards [hch] with ω hω
    simp only [hω]
  · exact measurable_fcPhysical_of_ae_eq (h2 z) ((hS2 z).mono hR le_rfl)
      (hch.mono fun ω hω => indicator_chart_congr hω z fun c z => c.1 z)
  · exact measurable_fcPhysical_of_ae_eq (h3 z) ((hS3 z).mono hR le_rfl)
      (hch.mono fun ω hω => indicator_chart_congr hω z fun c z => c.2.2 z)

/-- The retained history is a physical variable at time `0`. -/
theorem measurable_retHist_fcPhysical {d : PairData Ω} (hd : d.IsMeasGood) :
    Measurable[fcPhysicalFiltration P d 0] (retHist d) := by
  have h : Measurable[MeasurableSpace.comap (fcPhysicalRecord d 0) inferInstance]
      fun ω => (fcPhysicalRecord d 0 ω).1 := measurable_fst.comp (comap_measurable _)
  exact h.mono (comap_fcPhysicalRecord_le hd P 0) le_rfl

omit mΩ in
/-- The live safe event of a test is its avoidance event at the clock value. -/
theorem mem_avoidSet_of_mem_lineSafe {Qc : ℝ≥0 → Ω → ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ≥0∞}
    {ψ : TestOn upperHalfPlaneOpens} {t : ℝ≥0} {ω : Ω} (h : ω ∈ lineSafe Qc W U (tsupport ψ) t) :
    ω ∈ DomainMarkov.avoidSet W U ψ (Qc t ω) := h

omit mΩ in
theorem isDrvReg_of_continuous {W : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ≥0∞} (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (ω : Ω) : DomainMarkov.Mean.IsDrvReg W U ω :=
  ⟨(hWc ω).continuousOn, hW0 ω⟩

end Helpers

/-- **The word condition** (FCKER2): on its type, a sorted word with the same harmonic mean as a sorted word `c`
has signed marks and its force data represent `c`'s boundary function shifted by `θχ`, off a finite set. -/
theorem forceData_of_mean_eq {κ θ : ℝ} (hκ : 0 < κ) {a : ForceWordType} {c B : BoundaryWord}
    (hB : B ∈ forceTypeSet κ θ a) (hc : c.IsSorted) (hBs : B.IsSorted)
    (he : ∀ φ : TestOn upperHalfPlaneOpens, (∫ z, c.mean z * φ z) = ∫ z, B.mean z * φ z) :
    (∀ i, FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR B i ≤ 0) ∧
      (∀ j, 0 ≤ FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR B j) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ x ∉ S, forceBoundaryData κ a.rhoL a.rhoR
        (FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR B) (FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR B) x =
          c.fn x + θ * chiC κ := by
  have ht := FCDet.isFlowType_of_mem_typeSet hB
  obtain ⟨hL, hR⟩ := RetAux79.isFlowType_signs ht
  refine ⟨hL, hR, {0} ∪ ((c.jumps ∪ B.jumps : Finset ℝ) : Set ℝ),
    (Set.finite_singleton 0).union (Finset.finite_toSet _), fun x hx => ?_⟩
  have hx0 : x ≠ 0 := fun h => hx (Or.inl h)
  have hxJ : x ∉ c.jumps ∪ B.jumps := fun h => hx (Or.inr h)
  rw [RetAux79.forceBoundaryData_zero_of_isFlowType ht x,
    Exist.forceBoundaryData_flowLine_seed hκ (BoundaryWord.isPiecewiseConstantBoundaryData B) 0 θ hx0
      (by rw [add_zero]; exact fun h => hxJ (Finset.mem_union_right _ h)),
    add_zero, RetAux79.word_fn_eq_of_mean_integrals hc hBs he x hxJ]

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : PairData Ω} {E : Set Ω}

/-- **The safe events of the canonical first continuation are physical events** on a physical event `F ⊆ E` of the
meeting branch on which the driver generates the canonical chart path: there, the line safe event is "alive at
`s₀ + t`" and "the compact set avoids the filling of the chart path on `[0, t]`". -/
theorem measurableSet_inter_lineSafe_fcPhysical (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G)
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    (hEr : MeasurableSet[retSigma d P] E) {F : Set Ω} (hF : MeasurableSet[fcPhysicalFiltration P d 0] F)
    (hFE : F ⊆ E) (hEM : E ⊆ meetSet d) {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hgood : ∀ ω ∈ F, IsGeneratingTrace (W · ω) (U ω) (γ ω) ∧
      (∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U ω → γ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
        U ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) (t : ℝ≥0) :
    MeasurableSet[fcPhysicalFiltration P d t] (F ∩ lineSafe (fcCapacityClock d E) W U C t) := by
  have he : F ∩ lineSafe (fcCapacityClock d E) W U C t =
      F ∩ (⋃ m : ℕ, lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω}) ∩
        {ω | Disjoint C (fillH (cPath d E d.s₀ d.η₁ d.ζ₁ ω '' Icc 0 t))} := by
    ext ω
    simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq, lineSafe]
    constructor
    · rintro ⟨hωF, hlt, hdis⟩
      obtain ⟨hgen, hγ, hU⟩ := hgood ω hωF
      have hωE := hFE hωF
      have hlive := (coe_fcCapacityClock_lt_cLife_iff hd hs hclk hωE t).1 (hU ▸ hlt)
      obtain ⟨m, hm⟩ := exists_mem_lineBox (hEM hωE) t
      refine ⟨⟨hωF, m, hm, hlive⟩, ?_⟩
      rwa [← fwdHull_eq_fillH_cPath hd hs hclk hωE hgen hγ hlt]
    · rintro ⟨⟨hωF, m, hm, hlive⟩, hdis⟩
      obtain ⟨hgen, hγ, hU⟩ := hgood ω hωF
      have hωE := hFE hωF
      have hlt : (fcCapacityClock d E t ω : ℝ≥0∞) < U ω :=
        hU ▸ (coe_fcCapacityClock_lt_cLife_iff hd hs hclk hωE t).2 hlive
      refine ⟨hωF, hlt, ?_⟩
      rwa [fwdHull_eq_fillH_cPath hd hs hclk hωE hgen hγ hlt]
  rw [he]
  refine ((fcPhysicalFiltration P d).mono (zero_le (a := t)) _ hF |>.inter
    (MeasurableSet.iUnion fun m => measurableSet_fcPhysicalLiveBox hd P t m)).inter ?_
  have hfill := @RetAux79.measurable_fillH_image_Icc_of_prefix Ω (fcPhysicalFiltration P d t)
    (fun ω => cPath d E d.s₀ d.η₁ d.ζ₁ ω) t (hs.continuous_cPath hd)
    fun _ hst => measurable_cPath_fcPhysical hd hG hs hEr hst
  exact RetAux79.measurableSet_disjoint_of_hitting hfill
    (fun ω => ⟨fillH_subset_H _, isOpen_H_diff_fillH
      (isCompact_Icc.image (hs.continuous_cPath hd ω)).isBounded⟩) hC hCH

end Safe

section Box

variable {Ω : Type u} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {d : PairData Ω} {E F : Set Ω}

/-- The pathwise facts of the canonical first continuation used on the boxes. -/
def IsBoxGood₁ (d : PairData Ω) (E : Set Ω) (x₁ x₂ : ℝ) (W : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ)
    (U : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsGeneratingTrace (W · ω) (U ω) (γ ω) ∧
    (∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U ω → γ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
    U ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω ∧ InjOn (γ ω) {r | (r : ℝ≥0∞) ≤ U ω} ∧
    IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁ ∧ IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂

theorem isFCLine_of_isBoxGood₁ (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) {ω : Ω} (hωE : ω ∈ E) (hg : IsBoxGood₁ d E x₁ x₂ W γ U ω) {t : ℝ≥0}
    (ht : 0 < t) (hlive : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω) :
    IsFCLine d ω x₁ x₂ t (fun s => W s ω) (γ ω) (U ω) (fcCapacityClock d E t ω) :=
  isFCLine_of_canon hd hs hclk hωE hg.2.2.2.2.1 hg.2.2.2.2.2 (hWc ω) (hW0 ω) hg.1 hg.2.2.2.1 hg.2.1
    hg.2.2.1 ht hlive

omit [IsProbabilityMeasure P] in
/-- **The kernel identity on a box**, in the chart of the canonical continuation (Aux. 77 at the line, from
`exists_fcBoxKernel_physical`, with the chart data `IsFCLine` supplied). -/
theorem ae_kernel_box_path₁ (hd : d.IsMeasGood) (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (hFE : F ⊆ E) (hFg : ∀ ω ∈ F, IsBoxGood₁ d E x₁ x₂ W γ U ω)
    {t : ℝ≥0} (ht : 0 < t) {m : ℕ} {B : Set Ω}
    (hB : ∀ ω ∈ B, ω ∈ lineBox d t m ∧ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω)
    {M : Ω → DistOn upperHalfPlaneOpens}
    (hker : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ lineBox d t m →
      ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
        IsFCLine d ω x₁ x₂ t W γ ζc Q →
        tsupport φ ⊆ d.inv ω '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) Q) →
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦] ω =
          Complex.exp (Complex.I * (M ω φ : ℂ) -
            (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
              (d.inv ω '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) Q)) φ φ : ℝ) : ℂ)))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ F ∩ B → (fcCapacityClock d E t ω : ℝ≥0∞) < U ω →
      tsupport φ ⊆ (d.chart ω).2.1 '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
        (fcCapacityClock d E t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((d.chart ω).2.1 ''
            (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) (fcCapacityClock d E t ω))) φ φ :
              ℝ) : ℂ)) := by
  filter_upwards [hker φ] with ω hk hω _ hsupp
  have hinv : (d.chart ω).2.1 = d.inv ω := by rw [PairData.chart_of_mem (hs.subset (hFE hω.1))]
  rw [hinv] at hsupp ⊢
  exact hk (hB ω hω.2).1 (hB ω hω.2).2 (fun s => W s ω) (γ ω) (U ω) (fcCapacityClock d E t ω)
    (isFCLine_of_isBoxGood₁ hd hs hclk hWc hW0 (hFE hω.1) (hFg ω hω.1) ht (hB ω hω.2).2) hsupp

omit [IsProbabilityMeasure P] in
/-- **Aux. 79's word mean on a box** for the canonical continuation, with the force data of the retained word on
its type (`forceData_of_mean_eq`). -/
theorem ae_mean_box_path₁ (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    [IsProbabilityMeasure P] (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ d.ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ d.ζ₂)
    (hd : d.IsMeasGood)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hJ : c₀.jumps = jumps) (hb₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (hFE : F ⊆ E) (hFg : ∀ ω ∈ F, IsBoxGood₁ d E x₁ x₂ W γ U ω)
    {β : Ω → BoundaryWord} {a : ForceWordType}
    (hFw : ∀ ω ∈ F, β ω ∈ forceTypeSet κ θ₁ a ∧ (β ω).IsSorted ∧ ∀ φ : TestOn upperHalfPlaneOpens,
      (∫ z, (d.word c₀ (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) ω).mean z * φ z) =
        ∫ z, (β ω).mean z * φ z)
    {t : ℝ≥0} (ht : 0 < t) {m : ℕ} {B : Set Ω}
    (hB : ∀ ω ∈ B, ω ∈ lineBox d t m ∧ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω)
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (centredField h u₀) P g) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ F ∩ B ∩ lineSafe (fcCapacityClock d E) W U (tsupport ψ) t →
      Chart.chartTransport (hd.isConformal_chart ω) 1 (θ₁ * chiC κ) (chiC κ) (g ω +
        SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (fcCapacityClock d E t ω)
          (bheProc κ a.rhoL a.rhoR W
            (geomLW W fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))
            (geomRW W fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω)) ω
            (fcCapacityClock d E t ω)) z * ψ z := by
  have hmw := ae_lineBox_mean_word_geom h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae hu₀ hc₀ hJ
    hb₀ (fun _ _ _ _ _ _ hl => hl.isFCSideSign hd hx) m t hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg a.rhoL a.rhoR W
    (fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))
    (fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))
  filter_upwards [hmw] with ω hw hω
  have hωE := hFE hω.1.1
  obtain ⟨hT, hsω, hwω⟩ := hFw ω hω.1.1
  obtain ⟨hxl, hxr, hdata⟩ := forceData_of_mean_eq hκ hT
    (hd.word_isSorted (hs.subset hωE) hc₀ (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ)) hsω hwω
  exact hw (hB ω hω.1.2).1 (γ ω) (U ω) (fcCapacityClock d E t ω)
    (isFCLine_of_isBoxGood₁ hd hs hclk hWc hW0 hωE (hFg ω hω.1.1) ht (hB ω hω.1.2).2) hxl hxr hdata ψ
    fun z hz => ⟨tsupport_subset_H ψ hz, fun hz' => Set.disjoint_left.1 hω.2.2 hz hz'⟩

/-- **The per-box Gaussian law of the canonical first continuation** at a positive physical line: given the box's
σ-algebra `𝒦` (containing the physical record), on the box, the live safe event of `ψ` and the type branch, the
transported field has the coupling characteristic functional at the clock value. -/
theorem ae_condExp_box_path₁ (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ d.ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ d.ζ₂)
    (hd : d.IsMeasGood) (hG : ∀ᵐ ω ∂P, ω ∈ d.G)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hJ : c₀.jumps = jumps) (hb₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hs : IsContSpec d E d.s₀ d.η₁ d.ζ₁)
    (hclk : ∀ ω ∈ E, IsClockOn (chartClock (cPath d E d.s₀ d.η₁ d.ζ₁ ω)) (d.ζ₁ ω - d.s₀ ω))
    {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞} (hWc : ∀ ω, Continuous (W · ω))
    (hW0 : ∀ ω, W 0 ω = 0) (hFE : F ⊆ E) (hFg : ∀ ω ∈ F, IsBoxGood₁ d E x₁ x₂ W γ U ω)
    {β : Ω → BoundaryWord} {a : ForceWordType}
    (hFw : ∀ ω ∈ F, β ω ∈ forceTypeSet κ θ₁ a ∧ (β ω).IsSorted ∧ ∀ φ : TestOn upperHalfPlaneOpens,
      (∫ z, (d.word c₀ (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) ω).mean z * φ z) =
        ∫ z, (β ω).mean z * φ z)
    {t : ℝ≥0} (ht : 0 < t) {m : ℕ} {B : Set Ω}
    (hB : ∀ ω ∈ B, ω ∈ lineBox d t m ∧ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω)
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (centredField h u₀) P g)
    (h𝒦 : 𝒦 ≤ mΩ) (h𝓖𝒦 : fcPhysicalFiltration P d t ≤ 𝒦)
    (hker : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ lineBox d t m →
      ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
        IsFCLine d ω x₁ x₂ t W γ ζc Q →
        tsupport φ ⊆ d.inv ω '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) Q) →
        P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦] ω =
          Complex.exp (Complex.I * ((g ω +
            SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
            (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
              (d.inv ω '' (H \ QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) Q)) φ φ : ℝ) : ℂ)))
    (ψ : TestOn upperHalfPlaneOpens)
    (hEset : MeasurableSet[𝒦] (F ∩ B ∩ lineSafe (fcCapacityClock d E) W U (tsupport ψ) t)) :
    ∀ᵐ ω ∂P, ω ∈ F → ω ∈ B → ω ∈ lineSafe (fcCapacityClock d E) W U (tsupport ψ) t →
      P[fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) ψ : ℂ)) |
        𝒦] ω =
        cfAt κ W (bheProc κ a.rhoL a.rhoR W
          (geomLW W fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))
          (geomRW W fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))) ψ 1
          (fcCapacityClock d E t) ω := by
  have hX : (fun ω => Complex.exp (Complex.I *
      (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) ψ : ℂ))) =
      fun ω => Complex.exp (Complex.I *
        (Chart.chartTransport (hd.isConformal_chart ω) 1 (θ₁ * chiC κ) (chiC κ) (h ω) ψ : ℂ)) := by
    funext ω
    rw [show hd.chartField κ h ω = Chart.chartTransport (hd.isConformal_chart ω) 1 0 (chiC κ) (h ω) from rfl,
      RetFin.flowField_chartTransport]
  rw [hX]
  have hchart := chart_measurability_fcPhysical (P := P) hd hG t
  have hconv := ae_condExp_cexp_chartTransport_eq_cfAt_rand (P := P) (𝒢 := 𝒦) h𝒦
    (c := fun ω => d.chart ω) (fun ω => hd.isConformal_chart ω)
    (fun z => h𝓖𝒦 _ (hchart.1 z)) (fun z => (hchart.2.1 z).mono h𝓖𝒦 le_rfl)
    (fun z => (hchart.2.2 z).mono h𝓖𝒦 le_rfl) hd.continuousOn_lift_chart hh.1
    (M := fun ω => g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)
    (θ₁ * chiC κ) (chiC κ) (fcCapacityClock d E t) (Mset := F ∩ B)
    (W := W) (ζ := U) (κ := κ) (ρL := a.rhoL) (ρR := a.rhoR)
    (VL := geomLW W fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))
    (VR := geomRW W fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω))
    (ae_kernel_box_path₁ hd hs hclk hWc hW0 hFE hFg ht hB hker) ψ hEset
    (ae_of_all P fun ω hω => ⟨hω.1, mem_avoidSet_of_mem_lineSafe hω.2, isDrvReg_of_continuous hWc hW0 ω⟩)
    (ae_mean_box_path₁ h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hae hu₀ hc₀ hJ hb₀ hs hclk hWc hW0 hFE
      hFg hFw ht hB hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg ψ)
  filter_upwards [hconv] with ω hω hF hBω hS
  exact hω ⟨⟨hF, hBω⟩, hS⟩

end Box

section Main

/-- **The Gaussian field of the corrected forward inputs for the first canonical chart path**
(`FCK2CapForwardInputsC.gaussian` for path 1), from Lemma 7.5, Lemma 7.7 and Aux. lemma 56 (the inputs of the
per-cap kernels and of the word mean). -/
theorem hasFCK2CapForwardKernel_path₁
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma d P] β)
    (hsort : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hmean : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞} (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂)
    {W₁ : ℝ≥0 → Ω → ℝ} (hm₁ : ∀ t, Measurable (W₁ t)) (hc₁ : ∀ ω, Continuous (W₁ · ω))
    (hz₁ : ∀ ω, W₁ 0 ω = 0) (hg₁ : ∀ᵐ ω ∂P, ω ∈ meetSet d → IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω))
    (a : ForceWordType) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    HasFCK2CapForwardKernel P (fcRetainedDriverFiltration P hd W₁ hm₁ q)
      {ω | ω ∈ fcTypeBranch κ θ₁ (meetSet d) β a ∧ ω ∈ avoidSet W₁ U₁ ψ q}
      (fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) ψ : ℂ)))
      (cfAt κ W₁ (bheProc κ a.rhoL a.rhoR W₁
        (geomLW W₁ (fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω)))
        (geomRW W₁ (fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω)))) ψ 1 (fun _ => q)) := by
  classical
  subst hζ₁ hζ₂
  obtain ⟨E, hEr, hEM, hME, hs, -, hclk, -⟩ :=
    exists_fcContEvent h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae
  have hG : ∀ᵐ ω ∂P, ω ∈ d.G := hae.mono fun ω h => h.1
  set hL : ℝ := -sleLambda κ - θ₂ * chiC κ with hhL
  set hR : ℝ := sleLambda κ - θ₁ * chiC κ with hhR
  obtain ⟨c₀, hc₀, hJ, hb₀⟩ := BoundaryWord.exists_fn_eq_strictMonoOn hb
  have hside := Sec7.SideHeightBox.isBoxSideLimit_of_flowLines h75 h77 h56 hκ hκ4 hb hx hθ hh
    hη₁ hη₂ hd rfl rfl hae hu₀
  have hword := isBoxMeanIdentification_word h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl
    hae hu₀ hc₀ hJ hb₀ hside
  have hweq := ae_mean_integrals_eq_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hu₀ hword hmean
  set xL : Ω → Fin a.nL → ℝ := fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω) with hxL
  set xR : Ω → Fin a.nR → ℝ := fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (β ω) with hxR
  have hcan := ae_canon_cGamma₁ hd hs hclk hcanon
  have hgood : ∀ᵐ ω ∂P, (ω ∈ E → IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
      ((∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U₁ ω → γ₁ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
        U₁ ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω) ∧ InjOn (γ₁ ω) {r | (r : ℝ≥0∞) ≤ U₁ ω}) ∧
      IsPathGood (d.η₁ ω) (d.ζ₁ ω) x₁ ∧ IsPathGood (d.η₂ ω) (d.ζ₂ ω) x₂ ∧
      (ω ∈ meetSet d → (β ω).IsSorted ∧ ∀ φ : TestOn upperHalfPlaneOpens,
        (∫ z, (d.word c₀ hL hR ω).mean z * φ z) = ∫ z, (β ω).mean z * φ z) ∧
      (ω ∈ meetSet d → ω ∈ E) := by
    filter_upwards [hg₁, hcan, ae_canon_injOn_closed_life h77 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae hcanon,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, hae, hsort, hweq, hME]
      with ω hgω hcω hiω hp₁ hp₂ ha hsω hwω hmω
    exact ⟨fun hω => ⟨hgω (hEM hω), hcω hω, (hiω (hEM hω)).1⟩,
      Sec7.SideHeightBox.isPathGood_congr hp₁ ha.2.1, Sec7.SideHeightBox.isPathGood_congr hp₂ ha.2.2,
      fun hm => ⟨hsω hm, hwω hm⟩, hmω⟩
  obtain ⟨Good, hGm, hGae, hGp⟩ := exists_measurable_good hgood
  set F : Set Ω := fcTypeBranch κ θ₁ (meetSet d) β a ∩ E ∩ Good with hFdef
  have hFr : MeasurableSet[retSigma d P] F :=
    (((hd.measurableSet_meetSet P).inter (hβ (measurableSet_forceTypeSet κ θ₁ a))).inter hEr).inter
      (measurableSet_retSigma_of_ae hGm hGae)
  have hF0 : MeasurableSet[fcPhysicalFiltration P d 0] F := retSigma_le_fcPhysicalFiltration P d 0 _ hFr
  have hFE : F ⊆ E := fun ω hω => hω.1.2
  have hFgood : ∀ ω ∈ F, IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
      (∀ q : ℝ≥0, (q : ℝ≥0∞) ≤ U₁ ω → γ₁ ω q = cGamma d E d.s₀ d.η₁ d.ζ₁ ω q) ∧
        U₁ ω = cLife d E d.s₀ d.η₁ d.ζ₁ ω := fun ω hω =>
    ⟨((hGp ω hω.2).1 hω.1.2).1, ((hGp ω hω.2).1 hω.1.2).2.1⟩
  refine hasFCK2CapForwardKernel_mono (S' := {ω | ω ∈ F ∧ ω ∈ avoidSet W₁ U₁ ψ q}) ?_ ?_
  · filter_upwards [hGae] with ω hωG hω
    exact ⟨⟨⟨hω.1, (hGp ω hωG).2.2.2.2 hω.1.1⟩, hωG⟩, hω.2⟩
  -- the per-cap kernels and their conditionings
  have hK := fun m : ℕ => exists_fcBoxKernel_physical h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl
    hae hu₀ m
  choose ηc₁ ηc₂ hcc₁ hcc₂ hmc₁ hmc₂ hag₁ hag₂ hker using hK
  choose g hgmean hgker using hker
  set big : ℝ≥0 → ℕ → MeasurableSpace Ω := fun t m =>
    shMarkedSigma (ηc₁ m) (ηc₂ m) (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m)
      (centredField h u₀) t ⊔ fcPhysicalFiltration P d t with hbig_def
  have hbig : ∀ t m, fcPhysicalFiltration P d t ≤ big t m := fun t m => le_sup_right
  have hbigm : ∀ t m, big t m ≤ mΩ := fun t m =>
    sup_le (shMarkedSigma_le (hcc₁ m) (hcc₂ m) (hmc₁ m) (hmc₂ m)
      ((measurable_cutLife m).comp hd.measζ₁) ((measurable_cutLife m).comp hd.measζ₂)
      (measurable_centredField hh.1 u₀) t) ((fcPhysicalFiltration P d).le t)
  set B : ℝ≥0 → ℕ → Set Ω := fun t => disjointed fun m : ℕ =>
    lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω} with hB_def
  have hBG : ∀ t m, MeasurableSet[fcPhysicalFiltration P d t] (B t m) := fun t m =>
    MeasurableSet.disjointed (fun k => measurableSet_fcPhysicalLiveBox hd P t k) m
  have hBsub : ∀ t m ω, ω ∈ B t m → ω ∈ lineBox d t m ∧ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω :=
    fun t m ω hω => disjointed_subset _ m hω
  have hchart := fun t => chart_measurability_fcPhysical (P := P) hd hG t
  -- the main reduction
  refine hasFCK2CapForwardKernel_of_boxLaw (𝓖 := fcPhysicalFiltration P d) hd hm₁
    (continuous_fcCapacityClock hd hs hclk) (monotone_fcCapacityClock hd hs hclk)
    (fcCapacityClock_zero hd hs hclk) (measurable_fcCapacityClock_fcPhysical hd hG hs hEr)
    (measurable_retHist_fcPhysical hd)
    (measurable_indicator_driver_fcPhysical hd hG hs hclk hEr hm₁ hc₁ hz₁
      (hg₁.mono fun ω h hω => h (hEM hω)) hcan) ψ q
    (fun t => measurableSet_inter_lineSafe_fcPhysical hd hG hs hclk hEr hF0 hFE hEM hFgood
      ψ.hasCompactSupport.isCompact (tsupport_subset_H ψ) t) ?_
    (ae_of_all P fun ω _ => FCDet.isForceReg_thr hz₁ hc₁ xL xR U₁ ω) B
    (fun t => disjoint_disjointed _) hBG ?_ big hbig hbigm ?_
  · -- reach
    refine ae_of_all P fun ω hω hq => ?_
    have hU := (hFgood ω hω).2.2
    exact exists_le_fcCapacityClock hd hs hclk (hFE hω) (hU ▸ hq)
  · -- cover
    intro t
    refine ae_of_all P fun ω hω hS => ?_
    have hU := (hFgood ω hω).2.2
    have hlive := (coe_fcCapacityClock_lt_cLife_iff hd hs hclk (hFE hω) t).1 (hU ▸ hS.1)
    obtain ⟨m, hm⟩ := exists_mem_lineBox (hEM (hFE hω)) t
    have hmem : ω ∈ ⋃ k, B t k := by
      rw [iUnion_disjointed]
      exact mem_iUnion.2 ⟨m, hm, hlive⟩
    exact mem_iUnion.1 hmem
  · -- the per-box law
    intro t ht m
    have hFg : ∀ ω ∈ F, IsBoxGood₁ d E x₁ x₂ W₁ γ₁ U₁ ω := fun ω hω =>
      ⟨(hFgood ω hω).1, (hFgood ω hω).2.1, (hFgood ω hω).2.2, ((hGp ω hω.2).1 (hFE hω)).2.2,
        (hGp ω hω.2).2.1, (hGp ω hω.2).2.2.1⟩
    have hFw : ∀ ω ∈ F, β ω ∈ forceTypeSet κ θ₁ a ∧ (β ω).IsSorted ∧ ∀ φ : TestOn upperHalfPlaneOpens,
        (∫ z, (d.word c₀ (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ) ω).mean z * φ z) =
          ∫ z, (β ω).mean z * φ z := fun ω hω =>
      ⟨hω.1.1.2, ((hGp ω hω.2).2.2.2.1 hω.1.1.1).1, ((hGp ω hω.2).2.2.2.1 hω.1.1.1).2⟩
    have hEset : MeasurableSet[big t m]
        (F ∩ B t m ∩ lineSafe (fcCapacityClock d E) W₁ U₁ (tsupport ψ) t) := by
      have he : F ∩ B t m ∩ lineSafe (fcCapacityClock d E) W₁ U₁ (tsupport ψ) t =
          (F ∩ lineSafe (fcCapacityClock d E) W₁ U₁ (tsupport ψ) t) ∩ B t m := by
        ext ω
        simp only [mem_inter_iff]
        tauto
      rw [he]
      exact hbig t m _ ((measurableSet_inter_lineSafe_fcPhysical hd hG hs hclk hEr hF0 hFE hEM hFgood
        ψ.hasCompactSupport.isCompact (tsupport_subset_H ψ) t).inter (hBG t m))
    exact ae_condExp_box_path₁ h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hG hae hu₀ hc₀ hJ hb₀ hs hclk hc₁ hz₁
      hFE hFg hFw ht (hBsub t m) (hcc₁ m) (hcc₂ m) (hmc₁ m) (hmc₂ m) (hag₁ m) (hag₂ m) (hgmean m t)
      (hbigm t m) (hbig t m) (fun φ => (hgker m t φ).mono fun ω hk hb hl W γ ζc Q hfc hsu =>
        hk hb hl W γ ζc Q hfc hsu) ψ hEset

end Main

end InteractingSLE.Restart.FCPlumb.FCKerC
