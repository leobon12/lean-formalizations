/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleWit

/-!
# Identification of a staged history of a GW2 schedule with the canonical construction

Packet PROVE-T14-TIP3. Proof of Proposition 1.1 of the shortcut note (ruling R52, `source/external/AstraIG1/
ig1_shortcuts_audited.txt` §1.2, "Choosing the switches"): "Every successful finite history has angles in `A` and times
in `Q`. By field determination and canonical consistency it is a member of the originally fixed countable family";
Lemma GB9 (p. 526): "its field-determined physical prefix is that same member of the fixed family".

For a GW2 schedule and a staged history `E` whose drivers are regular at every sample (the form produced by the landed
construction `Staged.exists_regular_isStagedHistory_of_inputs`; see ruling R51 for why some regularity of the pieces is
needed at all):

* **determination** (`ae_agree_wordDrv`): at a launch, the `k`-th piece is almost surely the field-determined
  flow-line driver of its explicit witnesses (`GW2ScheduleWit`), on its whole lifetime;
* **identification** (`ae_pastMap_eq_canon`, `ae_agree_canon`): almost surely, the retained past of `E` is the canonical
  one as long as the canonical pieces succeed, and every launched piece of `E` agrees with the canonical piece
  (`GW2ScheduleCanon`, a deterministic measurable function of the own times and the field) on its whole lifetime.

The canonical pieces depend on the own times only through a jointly measurable map (`measurable_canonDrive`), so this
identifies the pieces of *every* fixed schedule with one jointly measurable construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

open Exist Staged StagedLaw Restart LQGMetric

/-! ### From the conditional laws to the law -/

section Transfer

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **A measurable event holding almost surely under almost every conditional law at the points of a conditioning event
holds almost surely on that event.** -/
theorem ae_of_ae_condExpKernel_on (h𝒢 : 𝒢 ≤ mΩ) {L A : Set Ω} (hL : MeasurableSet[𝒢] L)
    (hA : MeasurableSet A) (h : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ A) :
    ∀ᵐ ω ∂P, ω ∈ L → ω ∈ A := by
  have hp : MeasurableSet {ω | ω ∈ L → ω ∈ A} := by
    have : {ω | ω ∈ L → ω ∈ A} = Lᶜ ∪ A := by ext ω; simp [imp_iff_not_or]
    rw [this]; exact (h𝒢 _ hL).compl.union hA
  have h1 : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ L → ω ∈ A := by
    filter_upwards [h, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL.compl] with ω₀ h0 hc
    by_cases hω₀ : ω₀ ∈ L
    · exact (h0 hω₀).mono fun ω hω _ => hω
    · exact (hc hω₀).mono fun ω (hω : ω ∈ Lᶜ) (hωL : ω ∈ L) => absurd hωL hω
  have h2 : ∀ᵐ ω₀ ∂(P.trim h𝒢), ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ L → ω ∈ A := by
    have hm : MeasurableSet[𝒢] {ω₀ | ¬ ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ L → ω ∈ A} := by
      have e : {ω₀ | ¬ ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ L → ω ∈ A} =
          {ω₀ | condExpKernel P 𝒢 ω₀ {ω | ω ∈ L → ω ∈ A}ᶜ ≠ 0} := by
        ext ω₀; simp only [mem_ofPred_eq, ae_iff, compl_ofPred]
      rw [e]
      exact (measurableSet_eq_fun (measurable_condExpKernel hp.compl) measurable_const).compl
    rw [ae_iff, trim_measurableSet_eq h𝒢 hm]
    exact ae_iff.1 h1
  have h3 := Measure.ae_comp_of_ae_ae hp h2
  rwa [condExpKernel_comp_trim] at h3

end Transfer

/-! ### Regular drivers agreeing at rational times -/

/-- Two drivers continuous before a common lifetime that agree at the rational times before it agree before it. -/
theorem eq_of_rat {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : ContinuousOn e.1 {t | (t : ℝ≥0∞) < e.2})
    (he' : ContinuousOn e'.1 {t | (t : ℝ≥0∞) < e.2})
    (hq : ∀ q : ℚ, ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) < e.2 → e.1 (q : ℝ).toNNReal = e'.1 (q : ℝ).toNNReal)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < e.2) : e.1 t = e'.1 t := by
  set U : Set ℝ≥0 := {s : ℝ≥0 | (s : ℝ≥0∞) < e.2} with hU
  have hopen : IsOpen U := isOpen_lt ENNReal.continuous_coe continuous_const
  have hsub : U ⊆ closure (U ∩ range fun q : ℚ => (q : ℝ).toNNReal) := fun s hs =>
    denseRange_rat_toNNReal.open_subset_closure_inter hopen hs
  have hEq : EqOn e.1 e'.1 (U ∩ range fun q : ℚ => (q : ℝ).toNNReal) := by
    rintro s ⟨hs, q, rfl⟩
    exact hq q hs
  exact hEq.of_subset_closure he he' inter_subset_left hsub ht

/-! ### Determination of a staged piece by its retained past -/

section Det

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (θ : ℕ → ℝ) (Δ : ℕ → ℝ≥0∞)
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) {b : ℝ → ℝ} {jumps : Finset ℝ}
  {spec : ExplSpec} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The field-determined driver, with the flow-line word written out. -/
theorem wordDrv_eq (θk : ℝ) (c : BoundaryWord) (f : DistOn upperHalfPlaneOpens) :
    wordDrv hκ h12p θk c f = drvOf (detCode (paramΦ h12p hκ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0))
      (((flowLineXL c.fn c.jumps 0, flowLineXR c.fn c.jumps 0),
        (flowLineRhoL κ c.fn c.jumps 0 θk, flowLineRhoR κ c.fn c.jumps 0 θk)),
        flowField 0 (θk * QuantumZipper.chiC κ) f)) := by
  simp only [wordDrv, stagedDrv, wNL, wNR, wPad, truncWord_padFL]

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Composition of a jointly measurable two-argument map with two measurable maps. -/
theorem measurable_comp_pair {α A B C : Type*} [MeasurableSpace α] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {F : A → B → C} (hF : Measurable fun p : A × B => F p.1 p.2) {f : α → A} {g : α → B}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => F (f x) (g x) :=
  hF.comp (hf.prodMk hg)

/-- The field-determined driver of the explicit witnesses of instruction `k`. -/
def witDrv (k : ℕ) (ω : Ω) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  wordDrv hκ h12p (θ k) (wWord θ βA c₀ κ b jumps spec E k ω) (wField κ b jumps spec h E k ω)

/-- Agreement of two drivers: same lifetime, and equal before it. -/
def Agree (e e' : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop := e.2 = e'.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < e.2 → e.1 t = e'.1 t

/-- Agreement at the rational times. -/
def AgreeRat (e e' : (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  e.2 = e'.2 ∧ ∀ q : ℚ, ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) < e.2 → e.1 (q : ℝ).toNNReal = e'.1 (q : ℝ).toNNReal

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurableSet_agreeRat {α : Type*} [MeasurableSpace α] {F G : α → (ℝ≥0 → ℝ) × ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) : MeasurableSet {a | AgreeRat (F a) (G a)} := by
  have hζF : Measurable fun a => (F a).2 := measurable_snd.comp hF
  have hζG : Measurable fun a => (G a).2 := measurable_snd.comp hG
  have e : {a | AgreeRat (F a) (G a)} = {a | (F a).2 = (G a).2} ∩
      ⋂ q : ℚ, ({a | ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) < (F a).2}ᶜ ∪
        {a | (F a).1 (q : ℝ).toNNReal = (G a).1 (q : ℝ).toNNReal}) := by
    ext a; simp only [AgreeRat, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [e]
  exact (measurableSet_eq_fun hζF hζG).inter (MeasurableSet.iInter fun q =>
    (measurableSet_lt measurable_const hζF).compl.union
      (measurableSet_eq_fun ((measurable_pi_apply _).comp (measurable_fst.comp hF))
        ((measurable_pi_apply _).comp (measurable_fst.comp hG))))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem AgreeRat.agree {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : AgreeRat e e') (he : IsRegularDriver e)
    (he' : IsRegularDriver e') : Agree e e' := by
  refine ⟨h.1, fun t ht => eq_of_rat he.1 ?_ h.2 ht⟩
  have := he'.1
  rwa [← h.1] at this

/-- **Determination**: at a launch of a GW2 schedule, a staged piece regular at every sample is almost surely the
field-determined flow-line driver of its explicit witnesses, on its whole lifetime (Theorem 1.2 through
`Staged.ae_detCode_eq`, under the regular conditional law given the retained past). -/
theorem ae_agree_witDrv (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {k : ℕ} (hk : k < spec.2.2.length) :
    ∀ᵐ ω ∂P, AllSucc Δ (fun j => E j ω) k →
      Agree (E k ω)
        (witDrv hκ h12p θ βA c₀ (κ := κ) (b := b) (jumps := jumps) (spec := spec) (h := h) (E := E) k ω) := by
  classical
  have hEm : ∀ j, Measurable (E j) := hE.1
  have hok : ∀ j, StageOK κ b jumps P h spec E j := hE.2.2.2
  have hW := stageWitness_all θ Δ βA c₀ hβA hκ hb hc₀J hc₀ hh hgw hprog hΔ hEm hreg hok k
  have hpm : Measurable (pastMap κ b jumps spec E k) :=
    measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hYm := measurable_wField (κ := κ) (spec := spec) hb hh.1 hEm hreg
  have hWm : Measurable (wWord θ βA c₀ κ b jumps spec E k) :=
    (measurable_pastWord βA c₀ spec.1 θ hβA.1 k).comp hpm
  have hΨm : Measurable (witDrv hκ h12p θ βA c₀ (κ := κ) (b := b) (jumps := jumps) (spec := spec) (h := h)
      (E := E) k) :=
    measurable_comp_pair (F := fun c f => wordDrv hκ h12p (θ k) c f) (measurable_wordDrv hκ h12p (θ k)) hWm (hYm k)
  have hL := measurableSet_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ E hk.le
  have hA := measurableSet_agreeRat (hEm k) hΨm
  have : StandardBorelSpace (PastData k) := inferInstance
  have : MeasurableSpace.CountablySeparated (PastData k) := inferInstance
  have hatom0 := ae_ae_eq_of_comap (P := P) hpm
  rw [← pastSigma_eq_comap] at hatom0
  have hmain := ae_of_ae_condExpKernel_on (P := P) h𝒢 hL hA (by
    filter_upwards [hok k, hW.2.2.1, hW.2.2.2, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL, hatom0,
      Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1] with ω₀ hok₀ hpath hgff hmem hatom hpathK hs₀
    have hs₀' : AllSucc Δ (fun j => E j ω₀) k := hs₀
    have hne := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => E j ω₀) hk).2 hs₀'
    have hl' := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun j => E j ω₀) hk).1 hs₀'
    obtain ⟨b', J', h', hb', hT', hfl⟩ := hok₀ _ _ hl'
    obtain ⟨hconf, hlift, -⟩ := hpath hne
    rw [chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs₀'] at hconf hlift
    set ν := condExpKernel P (pastSigma κ b jumps spec E k) ω₀ with hν
    have hmem' := hmem hs₀
    have hh'eq : h' = fun ω => Chart.chartTransport hconf 1 0 (QuantumZipper.chiC κ) (h ω) := funext fun ω =>
      (hT' ω).eq_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hlift)
    have hh'm : Measurable h' := by rw [hh'eq]; exact (Chart.measurable_chartTransport hconf 1 0 _).comp hh.1
    have hYh' : ∀ᵐ ω ∂ν, wField κ b jumps spec h E k ω = h' ω := by
      filter_upwards [hmem', hatom, hpathK] with ω hω hpω hpathω
      have hrun : ExplState.run κ b jumps spec (fun j => E j ω) k =
          ExplState.run κ b jumps spec (fun j => E j ω₀) k :=
        run_eq_of_readRec_eq spec (fun j _ => hreg j ω) (fun j _ => hreg j ω₀) fun i hi => congrFun hpω ⟨i, hi⟩
      have hneω := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => E j ω) hk).2 hω
      obtain ⟨-, -, hTω⟩ := hpathω hneω
      rw [hrun, chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs₀'] at hTω
      exact hTω.unique hconf (hT' ω)
    have hgff' := isGFFWithBoundaryData_congr_ae (hgff hne) hh'm hYh'
    set w := wWord θ βA c₀ κ b jumps spec E k ω₀ with hw
    obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := isFlowLineDriver_word hκ hgff' hb' hfl
    have hh'' : h'' = fun ω => flowField 0 (θ k * QuantumZipper.chiC κ) (h' ω) := by
      funext ω
      ext φ
      have e1 := htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
      have e2 := isTranslateAddConst_flowField 0 (θ k * QuantumZipper.chiC κ) (h' ω) φ φ
        (fun z => by rw [Complex.ofReal_zero, add_zero])
      rw [e1, e2]
    have hF := Theorem15.isOrderedForceWord_flowLine w.fn w.jumps 0
    have hΦ := (h12p κ hκ (flowLineNL w.fn w.jumps 0) (flowLineNR w.fn w.jumps 0)).choose_spec.2 _ _ _ _ hF hC
    have hdet := ae_detCode_eq hκ hF h13 hC hΦ
    filter_upwards [hdet, hatom, hYh'] with ω ⟨x₀, hx₀, hζx, hwx, hcode⟩ hpω hYω
    have hww : wWord θ βA c₀ κ b jumps spec E k ω = w := by
      simp only [hw, wWord, hpω]
    have hΨ : witDrv hκ h12p θ βA c₀ (κ := κ) (b := b) (jumps := jumps) (spec := spec) (h := h) (E := E) k ω =
        drvOf (dOf x₀) := by
      rw [← hcode, hh'']
      change wordDrv hκ h12p (θ k) (wWord θ βA c₀ κ b jumps spec E k ω) (wField κ b jumps spec h E k ω) = _
      rw [hww, hYω, wordDrv_eq]
      rfl
    rw [hΨ, drvOf_of_mem (dOf_mem_DSet hx₀)]
    refine ⟨hζx.symm, fun q hq => ?_⟩
    have hq' : ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) < (dOf x₀).1 := by
      change _ < Sec2.Assembly.cζ x₀; rw [hζx]; exact hq
    change (E k ω).1 (q : ℝ).toNNReal = drvPath (dOf x₀) (q : ℝ).toNNReal
    rw [drvPath_of_lt hq']
    exact ((hwx _ hq).1).symm)
  filter_upwards [hmain] with ω hω hs
  exact (hω hs).agree (hreg k ω) (isRegularDriver_wordDrv hκ h12p _ _ _)

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Canonical consistency**: on the success event, the canonical piece is the field-determined driver of the
explicit witnesses of the canonical family. -/
theorem canonFam_eq_witDrv (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {k : ℕ}
    (hk : k ≤ spec.2.2.length) {ω : Ω}
    (hs : AllSucc Δ (fun j => canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω) k) :
    canonFam hκ h12p βA c₀ θ Δ spec.1 h k ω =
      witDrv hκ h12p θ βA c₀ (κ := κ) (b := b) (jumps := jumps) (spec := spec) (h := h)
        (E := canonFam hκ h12p βA c₀ θ Δ spec.1 h) k ω := by
  have hpm := pastMap_of_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ
    (canonFam hκ h12p βA c₀ θ Δ spec.1 h) hk hs
  change canonDrive hκ h12p βA c₀ spec.1 θ Δ (h ω) k = wordDrv hκ h12p (θ k)
    (pastWord βA c₀ spec.1 θ k (pastMap κ b jumps spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k ω))
    (fieldChain κ spec.1 k (pastMap κ b jumps spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k ω) (h ω))
  rw [hpm]
  change _ = wordDrv hκ h12p (θ k)
    (pastWord βA c₀ spec.1 θ k fun i => canonRec hκ h12p βA c₀ spec.1 θ Δ (h ω) i)
    (fieldChain κ spec.1 k (fun i => canonRec hκ h12p βA c₀ spec.1 θ Δ (h ω) i) (h ω))
  rw [pastWord_canonRec, fieldChain_canonRec]
  rfl

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- Agreeing drivers have the same record at an own time before the lifetime. -/
theorem recOf_eq_of_agree {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : Agree e e') {t : ℝ≥0∞} (ht : t < e.2) :
    recOf t e = recOf t e' := by
  have hmin : min t e.2 = t := min_eq_left ht.le
  have hmin' : min t e'.2 = t := by rw [← h.1]; exact hmin
  have ht' : t ≠ ⊤ := ne_top_of_lt ht
  refine Prod.ext (funext fun q => ?_) (Prod.ext ?_ ?_)
  · change e.1 (min ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) (min t e.2)).toNNReal =
      e'.1 (min ((((q : ℝ).toNNReal : ℝ≥0)) : ℝ≥0∞) (min t e'.2)).toNNReal
    rw [hmin, hmin']
    refine h.2 _ ?_
    rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top ht' (min_le_right _ _))]
    exact lt_of_le_of_lt (min_le_right _ _) ht
  · change min t e.2 = min t e'.2
    rw [hmin, hmin']
  · change decide (e.2 ≤ t) = decide (e'.2 ≤ t)
    rw [h.1]

/-- **Identification with the canonical construction.** For a GW2 schedule, a staged history `E` regular at every
sample has, almost surely, the canonical retained past and the canonical success events as long as the canonical
pieces succeed. -/
theorem ae_pastMap_eq_canon (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k ≤ spec.2.2.length, ∀ᵐ ω ∂P, AllSucc Δ (fun j => canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω) k →
      AllSucc Δ (fun j => E j ω) k ∧
        pastMap κ b jumps spec E k ω = pastMap κ b jumps spec (canonFam hκ h12p βA c₀ θ Δ spec.1 h) k ω
  | 0, _ => Eventually.of_forall fun ω _ => ⟨allSucc_zero Δ _, funext fun i => i.elim0⟩
  | k + 1, hk1 => by
    set C := canonFam hκ h12p βA c₀ θ Δ spec.1 h with hCdef
    have hk : k < spec.2.2.length := hk1
    have ih := ae_pastMap_eq_canon h13 hβA hb hc₀J hc₀ hh hgw hprog hΔ hE hreg k hk.le
    have hdet := ae_agree_witDrv hκ h12p θ Δ βA c₀ h13 hβA hb hc₀J hc₀ hh hgw hprog hΔ hE hreg hk
    filter_upwards [ih, hdet] with ω hih hdω hsC1
    have hsC : AllSucc Δ (fun j => C j ω) k := hsC1.mono (Nat.le_succ k)
    obtain ⟨hsE, hpe⟩ := hih hsC
    have hagE := hdω hsE
    have hwit : witDrv hκ h12p θ βA c₀ (κ := κ) (b := b) (jumps := jumps) (spec := spec) (h := h) (E := E) k ω =
        C k ω := by
      rw [hCdef, canonFam_eq_witDrv hκ h12p θ Δ βA c₀ hgw hprog hΔ hk.le hsC]
      change wordDrv hκ h12p (θ k) (pastWord βA c₀ spec.1 θ k (pastMap κ b jumps spec E k ω))
          (fieldChain κ spec.1 k (pastMap κ b jumps spec E k ω) (h ω)) =
        wordDrv hκ h12p (θ k) (pastWord βA c₀ spec.1 θ k (pastMap κ b jumps spec C k ω))
          (fieldChain κ spec.1 k (pastMap κ b jumps spec C k ω) (h ω))
      rw [hpe]
    rw [hwit] at hagE
    have hlt : Δ k < (E k ω).2 := by rw [hagE.1]; exact (allSucc_succ.1 hsC1).2
    have hsE1 : AllSucc Δ (fun j => E j ω) (k + 1) := allSucc_succ.2 ⟨hsE, hlt⟩
    refine ⟨hsE1, ?_⟩
    rw [pastMap_of_allSucc hgw hprog hΔ E hk1 hsE1, pastMap_of_allSucc hgw hprog hΔ C hk1 hsC1]
    funext i
    rcases Nat.lt_succ_iff_lt_or_eq.1 i.2 with hi | hi
    · have := congrFun hpe ⟨i, hi⟩
      rw [pastMap_of_allSucc hgw hprog hΔ E hk.le hsE, pastMap_of_allSucc hgw hprog hΔ C hk.le hsC] at this
      exact this
    · have hik : (i : ℕ) = k := hi
      rw [hik]
      exact recOf_eq_of_agree hagE hlt

/-- **Every launched piece agrees with the canonical piece.** For a GW2 schedule and a staged history `E` regular at
every sample, almost surely: the pieces of `E` and of the canonical construction launch at the same instructions, and
each launched piece of `E` agrees with the canonical piece (same lifetime, same driver before it). -/
theorem ae_agree_canon (h13 : Theorem13Statement.{u}) (hβA : IsStopLaw.{u} κ βA)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) (hE : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, ∀ k < spec.2.2.length,
      (AllSucc Δ (fun j => E j ω) k ↔ AllSucc Δ (fun j => canonFam hκ h12p βA c₀ θ Δ spec.1 h j ω) k) ∧
      (AllSucc Δ (fun j => E j ω) k → Agree (E k ω) (canonFam hκ h12p βA c₀ θ Δ spec.1 h k ω)) := by
  set C := canonFam hκ h12p βA c₀ θ Δ spec.1 h with hCdef
  have hall : ∀ᵐ ω ∂P, ∀ k < spec.2.2.length, AllSucc Δ (fun j => C j ω) k →
      Agree (E k ω) (C k ω) := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : k < spec.2.2.length
    · filter_upwards [ae_pastMap_eq_canon hκ h12p θ Δ βA c₀ h13 hβA hb hc₀J hc₀ hh hgw hprog hΔ hE hreg k hk.le,
        ae_agree_witDrv hκ h12p θ Δ βA c₀ h13 hβA hb hc₀J hc₀ hh hgw hprog hΔ hE hreg hk] with ω hid hdet _ hsC
      obtain ⟨hsE, hpe⟩ := hid hsC
      have hag := hdet hsE
      rwa [show witDrv hκ h12p θ βA c₀ (κ := κ) (b := b) (jumps := jumps) (spec := spec) (h := h) (E := E) k ω =
          C k ω by
        rw [hCdef, canonFam_eq_witDrv hκ h12p θ Δ βA c₀ hgw hprog hΔ hk.le hsC]
        change wordDrv hκ h12p (θ k) (pastWord βA c₀ spec.1 θ k (pastMap κ b jumps spec E k ω))
            (fieldChain κ spec.1 k (pastMap κ b jumps spec E k ω) (h ω)) =
          wordDrv hκ h12p (θ k) (pastWord βA c₀ spec.1 θ k (pastMap κ b jumps spec C k ω))
            (fieldChain κ spec.1 k (pastMap κ b jumps spec C k ω) (h ω))
        rw [hpe]] at hag
    · exact Eventually.of_forall fun ω h' => absurd h' hk
  filter_upwards [hall] with ω hω
  have hiff : ∀ k ≤ spec.2.2.length, (AllSucc Δ (fun j => E j ω) k ↔ AllSucc Δ (fun j => C j ω) k) := by
    intro k hk
    induction k with
    | zero => exact iff_of_true (allSucc_zero Δ _) (allSucc_zero Δ _)
    | succ k ihk =>
      have hk' : k < spec.2.2.length := hk
      rw [allSucc_succ, allSucc_succ]
      constructor
      · rintro ⟨hE', hlt⟩
        have hC' := (ihk hk'.le).1 hE'
        refine ⟨hC', ?_⟩
        rw [← (hω k hk' hC').1]; exact hlt
      · rintro ⟨hC', hlt⟩
        refine ⟨(ihk hk'.le).2 hC', ?_⟩
        rw [(hω k hk' hC').1]; exact hlt
  exact fun k hk => ⟨hiff k hk.le, fun hs => hω k hk ((hiff k hk.le).1 hs)⟩

end Det

end GW2Schedule

end Theorem14

end InteractingSLE
