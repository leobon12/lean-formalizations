/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCPlumbAssembly2
import InteractingSLE.Spec.Restart.FCAux79SideSign
import InteractingSLE.Spec.Restart.FCLife

/-!
# Physical histories and driver inputs at first contact

The physical filtration retains the first-contact record and the later killed
histories. Keeping the killing records is essential when comparing finite caps.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open Sec6 LocalSets WholeField FCAux79 Sec2.Assembly DomainMarkov.K2

universe u

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The initial record together with the killed histories at the later physical line.
The first record also remembers the origin of the continuation clock. -/
def fcPhysicalRecord (d : PairData Ω) (t : ℝ≥0) (ω : Ω) :
    (KHist × KHist) × (KHist × KHist) :=
  (retHist d ω,
    (khistOf (pathCoord (d.η₁ ω)) (d.ζ₁ ω) (fcTime₁ d ω + t),
      khistOf (pathCoord (d.η₂ ω)) (d.ζ₂ ω) (fcTime₂ d ω)))

omit mΩ in
/-- Restriction of the later record recovers every earlier record. -/
theorem fcPhysicalRecord_restrict (d : PairData Ω) {s t : ℝ≥0} (hst : s ≤ t) (ω : Ω) :
    ((fcPhysicalRecord d t ω).1,
      (khistRestrict (fcPhysicalRecord d t ω).2.1
        ((fcPhysicalRecord d t ω).1.1.1.1 + s), (fcPhysicalRecord d t ω).2.2)) =
      fcPhysicalRecord d s ω := by
  change (retHist d ω, (khistRestrict (khistOf _ _ (fcTime₁ d ω + t))
    (fcTime₁ d ω + s), _)) = _
  rw [khistRestrict_khistOf (add_le_add le_rfl (ENNReal.coe_le_coe.2 hst))]
  rfl

omit mΩ in
theorem comap_fcPhysicalRecord_mono (d : PairData Ω) {s t : ℝ≥0} (hst : s ≤ t) :
    MeasurableSpace.comap (fcPhysicalRecord d s) inferInstance ≤
      MeasurableSpace.comap (fcPhysicalRecord d t) inferInstance := by
  let r := fun y : (KHist × KHist) × (KHist × KHist) =>
    (y.1, (khistRestrict y.2.1 (y.1.1.1.1 + s), y.2.2))
  have hr : Measurable r :=
    measurable_fst.prodMk
      ((measurable_khistRestrict.comp
        ((measurable_fst.comp measurable_snd).prodMk
          (((measurable_fst.comp measurable_fst).comp
            (measurable_fst.comp measurable_fst)).add measurable_const))).prodMk
        (measurable_snd.comp measurable_snd))
  have he : fcPhysicalRecord d s = r ∘ fcPhysicalRecord d t :=
    funext fun ω => (fcPhysicalRecord_restrict d hst ω).symm
  rw [he]
  exact (hr.comp (comap_measurable _)).comap_le

/-- The completed physical filtration of the first continuation. -/
def fcPhysicalFiltration (P : Measure Ω) (d : PairData Ω) : Filtration ℝ≥0 mΩ where
  seq t := mΩ ⊓ aeSigma (MeasurableSpace.comap (fcPhysicalRecord d t) inferInstance) P
  mono' _ _ hst := inf_le_inf_left mΩ
    (StagedEntrance.aeSigma_le_aeSigma
      ((comap_fcPhysicalRecord_mono d hst).trans (le_aeSigma _ P)))
  le' _ := inf_le_left

theorem retSigma_le_fcPhysicalFiltration (P : Measure Ω) (d : PairData Ω) (t : ℝ≥0) :
    retSigma d P ≤ fcPhysicalFiltration P d t := by
  apply inf_le_inf_left mΩ
  exact StagedEntrance.aeSigma_le_aeSigma
    ((measurable_fst.comp (comap_measurable (fcPhysicalRecord d t))).comap_le.trans
      (le_aeSigma _ P))

theorem measurable_fcPhysicalRecord {d : PairData Ω} (hd : d.IsMeasGood) (t : ℝ≥0) :
    Measurable (fcPhysicalRecord d t) := by
  have hτ₁ : Measurable (fcTime₁ d) :=
    Measurable.ite hd.measurableSet_E
      (measurable_coe_nnreal_ennreal.comp hd.measurable_s₀) measurable_const
  have hk : Measurable fun p : (ℚ≥0 → ℂ) × ℝ≥0∞ × ℝ≥0∞ => khistOf p.1 p.2.1 p.2.2 :=
    (measurable_histOf.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).prodMk
      (measurable_lifeRec.comp
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  have hp : Measurable fun ω => pathCoord (d.η₁ ω) :=
    Measurable.of_eval fun q => hd.meas₁ q
  have hh₁ := hk.comp (hp.prodMk
    (hd.measζ₁.prodMk (hτ₁.add (measurable_const (a := (t : ℝ≥0∞))))))
  exact hd.measurable_retHist.prodMk (hh₁.prodMk (measurable_snd.comp hd.measurable_retHist))

/-- A later box records that the first continuation has not yet been killed. -/
def fcPhysicalBoxSet (t : ℝ≥0) (m : ℕ) :
    Set ((KHist × KHist) × (KHist × KHist)) :=
  {y | y.1 ∈ boxSet m ∧ y.1.1.1.1 + t < m ∧ y.2.1.2 = ⊤}

omit mΩ in
theorem measurableSet_fcPhysicalBoxSet (t : ℝ≥0) (m : ℕ) :
    MeasurableSet (fcPhysicalBoxSet t m) := by
  have ht : Measurable fun y : (KHist × KHist) × (KHist × KHist) => y.1.1.1.1 :=
    (measurable_fst.comp measurable_fst).comp (measurable_fst.comp measurable_fst)
  have hk : Measurable fun y : (KHist × KHist) × (KHist × KHist) => y.2.1.2 :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  exact (measurable_fst (measurableSet_boxSet m)).inter
    ((measurableSet_lt (ht.add measurable_const) measurable_const).inter
      (hk (measurableSet_singleton ⊤)))

omit mΩ in
/-- The box read from the physical record has the intended physical-time description. -/
theorem preimage_fcPhysicalBoxSet (d : PairData Ω) (t : ℝ≥0) (m : ℕ) :
    fcPhysicalRecord d t ⁻¹' fcPhysicalBoxSet t m =
      lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω} := by
  ext ω
  by_cases hbox : ω ∈ meetBox d m
  · have hE := (mem_meetBox_iff.1 hbox).1
    change (retHist d ω ∈ boxSet m ∧ (retHist d ω).1.1.1 + t < m ∧
      lifeRec (d.ζ₁ ω) (fcTime₁ d ω + t) = ⊤) ↔ _
    rw [show retHist d ω ∈ boxSet m ↔ True from iff_true_intro hbox]
    have hτ : fcTime₁ d ω = (d.s₀ ω : ℝ≥0∞) := by simp [fcTime₁, hE]
    have hr : (retHist d ω).1.1.1 = (d.s₀ ω : ℝ≥0∞) := hτ
    rw [hr, hτ, ← ENNReal.coe_add, lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top]
    simp only [lineBox, mem_inter_iff, mem_ofPred_eq, hbox, true_and]
    exact and_congr_left fun _ => by norm_cast
  · simp only [fcPhysicalBoxSet, fcPhysicalRecord, mem_preimage, mem_ofPred_eq,
      show retHist d ω ∉ boxSet m from hbox, false_and, lineBox, mem_inter_iff,
      hbox]

theorem measurableSet_fcPhysicalLiveBox {d : PairData Ω} (hd : d.IsMeasGood)
    (P : Measure Ω) (t : ℝ≥0) (m : ℕ) :
    MeasurableSet[fcPhysicalFiltration P d t]
      (lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω}) := by
  rw [← preimage_fcPhysicalBoxSet]
  exact ⟨measurable_fcPhysicalRecord hd t (measurableSet_fcPhysicalBoxSet t m),
    le_aeSigma _ P _ ⟨_, measurableSet_fcPhysicalBoxSet t m, rfl⟩⟩

omit mΩ in
/-- Available histories before the finite cap agree, including the killing record. -/
theorem khist_eq_capped_of_available {f g fcap : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a m : ℝ≥0}
    (ham : a < m) (haζ : (a : ℝ≥0∞) ≤ ζ)
    (hfg : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ → f s = g s)
    (hcap : ∀ s, fcap s = g (capTime m ζ s)) :
    khistOf (pathCoord f) ζ a = khistOf (pathCoord fcap) (cutLife ζ m) a := by
  apply Prod.ext
  · apply histOf_congr
    intro q hq
    have hqζ : (q : ℝ≥0∞) ≤ ζ := hq.trans haζ
    change f q = fcap q
    rw [hcap, capTime_of_le m ζ
      (le_min hqζ (hq.trans (ENNReal.coe_le_coe.2 ham.le)))]
    exact hfg q hqζ
  · exact (RetAux79.lifeRec_cutLife_eq ham ζ).symm

/-- The capped record keeps both the initial mark and the later histories. -/
def fcCappedRecord (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (t : ℝ≥0) (ω : Ω) : (KHist × KHist) × (KHist × KHist) :=
  (fcHist η₁ η₂ ζ₁ ζ₂ ω, shHist η₁ η₂ ζ₁ ζ₂ t 0 ω)

omit mΩ in
/-- On a live physical box the complete physical and capped records coincide. -/
theorem fcPhysicalRecord_eq_capped {d : PairData Ω} {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    {ω : Ω} {m : ℕ} {t : ℝ≥0} (hbox : ω ∈ lineBox d t m)
    (hlife : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω)
    (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s)
    (ha₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hc₁ : ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hc₂ : ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    (heq : retHist d ω = fcHist ηc₁ ηc₂
      (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω) :
    fcPhysicalRecord d t ω = fcCappedRecord ηc₁ ηc₂
      (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) t ω := by
  obtain ⟨hE, -, ht, -, htζ⟩ := mem_meetBox_iff.1 hbox.1
  have e₁ : recFst (fullHist ηc₁ ηc₂ ω) = d.s₀ ω := by
    have he := congrArg (fun y : KHist × KHist => y.1.1.1) heq
    simpa only [retHist, fcHist, khistOf, histOf, fcTime₁, hE, ite_true] using he.symm
  have e₂ : recSnd (fullHist ηc₁ ηc₂ ω) = d.t₀ ω := by
    have he := congrArg (fun y : KHist × KHist => y.2.1.1) heq
    simpa only [retHist, fcHist, khistOf, histOf, fcTime₂, hE, ite_true] using he.symm
  apply Prod.ext heq
  simp only [fcPhysicalRecord, fcCappedRecord, shHist, fcTime₁, fcTime₂, hE,
    ite_true, e₁, e₂, ENNReal.coe_zero, add_zero, ← ENNReal.coe_add]
  exact Prod.ext (khist_eq_capped_of_available hbox.2 hlife.le ha₁ hc₁)
    (khist_eq_capped_of_available ht htζ.le ha₂ hc₂)

/-- The same live box is read from the physical and capped records; on it all
labelled histories and killing records agree almost surely. -/
theorem ae_fcPhysicalRecord_eq_capped {P : Measure Ω} {d : PairData Ω}
    (hd : d.IsMeasGood) {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (m : ℕ) (t : ℝ≥0)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s)) :
    ∀ᵐ ω ∂P,
      (fcPhysicalRecord d t ω ∈ fcPhysicalBoxSet t m ↔
        fcCappedRecord ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
          (fun ω => cutLife (d.ζ₂ ω) m) t ω ∈ fcPhysicalBoxSet t m) ∧
      (fcPhysicalRecord d t ω ∈ fcPhysicalBoxSet t m →
        fcPhysicalRecord d t ω = fcCappedRecord ηc₁ ηc₂
          (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) t ω) := by
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  filter_upwards [hcmp, hae, hag₁, hag₂] with ω hcmpω ha hc₁ω hc₂ω
  have he (hω : fcPhysicalRecord d t ω ∈ fcPhysicalBoxSet t m) :
      fcPhysicalRecord d t ω = fcCappedRecord ηc₁ ηc₂
        (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) t ω := by
    have hω' : ω ∈ lineBox d t m ∩
        {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω} :=
      (Set.ext_iff.1 (preimage_fcPhysicalBoxSet d t m) ω).1 hω
    exact fcPhysicalRecord_eq_capped hω'.1 hω'.2 ha.2.1 ha.2.2 hc₁ω hc₂ω
      (hcmpω.2 hω'.1.1)
  refine ⟨⟨fun hω => he hω ▸ hω, ?_⟩, he⟩
  rintro ⟨hinit, htime, hkill⟩
  have hbox : ω ∈ meetBox d m := hcmpω.1.mpr hinit
  have hE := (mem_meetBox_iff.1 hbox).1
  have heq := hcmpω.2 hbox
  have e₁ : recFst (fullHist ηc₁ ηc₂ ω) = d.s₀ ω := by
    have he₁ := congrArg (fun y : KHist × KHist => y.1.1.1) heq
    simpa only [retHist, fcHist, khistOf, histOf, fcTime₁, hE, ite_true] using he₁.symm
  change recFst (fullHist ηc₁ ηc₂ ω) + t < (m : ℝ≥0∞) at htime
  rw [e₁, ← ENNReal.coe_add] at htime
  have htm : d.s₀ ω + t < (m : ℝ≥0) := by exact_mod_cast htime
  change lifeRec (cutLife (d.ζ₁ ω) m) (recFst (fullHist ηc₁ ηc₂ ω) + t) = ⊤ at hkill
  rw [e₁, ← ENNReal.coe_add, lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top] at hkill
  have hζ := lt_of_lt_cutLife htm hkill
  exact (Set.ext_iff.1 (preimage_fcPhysicalBoxSet d t m) ω).2 ⟨⟨hbox, htm⟩, hζ⟩

/-- Concrete comparison of the physical filtration and the capped record. Their
join has the same completed trace on each live physical box, in both directions.
The statement concerns histories; field germs are a separate enlargement. -/
theorem fcPhysicalFiltration_trace_capped {P : Measure Ω} {d : PairData Ω}
    (hd : d.IsMeasGood) {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (m : ℕ) (t : ℝ≥0)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    (D : Set Ω)
    (hD : MeasurableSet[MeasurableSpace.comap
      (fcCappedRecord ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
        (fun ω => cutLife (d.ζ₂ ω) m) t) inferInstance ⊔ fcPhysicalFiltration P d t] D) :
    MeasurableSet[aeSigma (MeasurableSpace.comap
      (fcCappedRecord ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
        (fun ω => cutLife (d.ζ₂ ω) m) t) inferInstance) P]
      (D ∩ (lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω})) ∧
    MeasurableSet[aeSigma (fcPhysicalFiltration P d t) P]
      (D ∩ (lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω})) := by
  let F := fcCappedRecord ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
    (fun ω => cutLife (d.ζ₂ ω) m) t
  have hcmp := ae_fcPhysicalRecord_eq_capped hd hc₁ hc₂ m t hae hag₁ hag₂
  have hF : Measurable F :=
    (measurable_fcHist hm₁ hm₂ ((measurable_cutLife m).comp hd.measζ₁)
      ((measurable_cutLife m).comp hd.measζ₂)).prodMk
        (measurable_shHist hm₁ hm₂ ((measurable_cutLife m).comp hd.measζ₁)
          ((measurable_cutLife m).comp hd.measζ₂) t 0)
  have hfirst := measurableSet_aeSigma_inter_of_ae
    (Ψ := fcPhysicalRecord d t) (F := F) le_rfl
    (measurableSet_fcPhysicalBoxSet t m) hcmp D hD
  rw [preimage_fcPhysicalBoxSet] at hfirst
  refine ⟨hfirst, ?_⟩
  have hraw : MeasurableSpace.comap (fcPhysicalRecord d t) inferInstance ≤
      fcPhysicalFiltration P d t :=
    le_inf (measurable_fcPhysicalRecord hd t).comap_le (le_aeSigma _ P)
  have hreverse : ∀ᵐ ω ∂P, (F ω ∈ fcPhysicalBoxSet t m ↔
      fcPhysicalRecord d t ω ∈ fcPhysicalBoxSet t m) ∧
      (F ω ∈ fcPhysicalBoxSet t m → F ω = fcPhysicalRecord d t ω) := by
    filter_upwards [hcmp] with ω ⟨hm, he⟩
    exact ⟨hm.symm, fun hω => (he (hm.mpr hω)).symm⟩
  have hD' : MeasurableSet[fcPhysicalFiltration P d t ⊔
      (mΩ ⊓ aeSigma (MeasurableSpace.comap F inferInstance) P)] D :=
    (sup_le ((le_inf hF.comap_le (le_aeSigma _ P)).trans le_sup_right) le_sup_left) D hD
  have hsecond := measurableSet_aeSigma_inter_of_ae hraw
    (measurableSet_fcPhysicalBoxSet t m) hreverse D hD'
  apply measurableSet_aeSigma_of_ae_eq _ hsecond
  apply EventuallyEqSet.inter EventuallyEqSet.rfl
  rw [← preimage_fcPhysicalBoxSet]
  filter_upwards [hcmp] with ω hω using propext hω.1

/-- Recover the initial first-contact histories from a later pair of histories. -/
def recoverFCHist (y : KHist × KHist) : KHist × KHist :=
  (khistRestrict y.1 (recFst (y.1.1, y.2.1)),
    khistRestrict y.2 (recSnd (y.1.1, y.2.1)))

omit mΩ in
theorem measurable_recoverFCHist : Measurable recoverFCHist := by
  have hp : Measurable fun y : KHist × KHist => (y.1.1, y.2.1) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  exact (measurable_khistRestrict.comp
    (measurable_fst.prodMk (measurable_recFst.comp hp))).prodMk
      (measurable_khistRestrict.comp
        (measurable_snd.prodMk (measurable_recSnd.comp hp)))

omit mΩ in
/-- The initial mark is already contained in a later mark, including the no-contact branch. -/
theorem recoverFCHist_shHist {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {ω : Ω} (hc₁ : Continuous (η₁ ω)) (hc₂ : Continuous (η₂ ω))
    (hpair : ∃ σ₁ σ₂, IsFCPair (η₁ ω) (η₂ ω) σ₁ σ₂) (t : ℝ≥0) :
    recoverFCHist (shHist η₁ η₂ ζ₁ ζ₂ t 0 ω) = fcHist η₁ η₂ ζ₁ ζ₂ ω := by
  obtain ⟨σ₁, σ₂, hσ⟩ := hpair
  obtain ⟨h₁, h₂⟩ := fcLine_eq hc₁ hc₂ hσ
  have hpair' : IsFCPair (η₁ ω) (η₂ ω)
      (recFst (fullHist η₁ η₂ ω)) (recSnd (fullHist η₁ η₂ ω)) := by
    rw [h₁, h₂]
    exact hσ
  have hr := rec_eq hc₁ hc₂ hpair'
    (show recFst (fullHist η₁ η₂ ω) ≤ recFst (fullHist η₁ η₂ ω) + t from le_self_add)
    (show recSnd (fullHist η₁ η₂ ω) ≤ recSnd (fullHist η₁ η₂ ω) + (0 : ℝ≥0) by simp)
  have hr₁ : recFst ((shHist η₁ η₂ ζ₁ ζ₂ t 0 ω).1.1,
      (shHist η₁ η₂ ζ₁ ζ₂ t 0 ω).2.1) = recFst (fullHist η₁ η₂ ω) := hr.1
  have hr₂ : recSnd ((shHist η₁ η₂ ζ₁ ζ₂ t 0 ω).1.1,
      (shHist η₁ η₂ ζ₁ ζ₂ t 0 ω).2.1) = recSnd (fullHist η₁ η₂ ω) := hr.2
  change (khistRestrict (khistOf _ _ _) _, khistRestrict (khistOf _ _ _) _) = _
  rw [hr₁, hr₂, khistRestrict_khistOf le_self_add,
    khistRestrict_khistOf (show recSnd (fullHist η₁ η₂ ω) ≤
      recSnd (fullHist η₁ η₂ ω) + (0 : ℝ≥0) by simp)]
  rfl

/-- Adding the initial capped record adds no information modulo null sets. -/
theorem comap_fcCappedRecord_le_aeSigma_shHist {P : Measure Ω}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
    (hpair : ∀ᵐ ω ∂P, ∃ σ₁ σ₂, IsFCPair (η₁ ω) (η₂ ω) σ₁ σ₂) (t : ℝ≥0) :
    MeasurableSpace.comap (fcCappedRecord η₁ η₂ ζ₁ ζ₂ t) inferInstance ≤
      aeSigma (MeasurableSpace.comap (shHist η₁ η₂ ζ₁ ζ₂ t 0) inferInstance) P := by
  have hm : Measurable fun y : KHist × KHist => (recoverFCHist y, y) :=
    measurable_recoverFCHist.prodMk measurable_id
  rintro _ ⟨C, hC, rfl⟩
  refine ⟨shHist η₁ η₂ ζ₁ ζ₂ t 0 ⁻¹' ((fun y => (recoverFCHist y, y)) ⁻¹' C),
    ⟨_, hm hC, rfl⟩, ?_⟩
  filter_upwards [hpair] with ω hω
  have he := recoverFCHist_shHist (ζ₁ := ζ₁) (ζ₂ := ζ₂) (hc₁ ω) (hc₂ ω) hω t
  simp only [mem_preimage, fcCappedRecord, he]

/-- The capped marked kernel can be conditioned also on the completed physical
histories. Only the one-sided trace inclusion is needed for this enlargement. -/
theorem ae_condExp_shMarkedSigma_sup_physical {P : Measure Ω} [IsProbabilityMeasure P]
    {d : PairData Ω} (hd : d.IsMeasGood) {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ s, Measurable fun ω => ηc₁ ω s) (hm₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : Measurable h₀)
    (m : ℕ) (t : ℝ≥0)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    (hpair : ∀ᵐ ω ∂P, ∃ σ₁ σ₂, IsFCPair (ηc₁ ω) (ηc₂ ω) σ₁ σ₂)
    {X : Ω → ℂ} (hX : Integrable X P) :
    ∀ᵐ ω ∂P, ω ∈ lineBox d t m → ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω →
      P[X | shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
        (fun ω => cutLife (d.ζ₂ ω) m) h₀ t ⊔ fcPhysicalFiltration P d t] ω =
      P[X | shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
        (fun ω => cutLife (d.ζ₂ ω) m) h₀ t] ω := by
  let 𝒦 := shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m)
    (fun ω => cutLife (d.ζ₂ ω) m) h₀ t
  let _ : MeasurableSpace Ω := mΩ
  have h𝒦 : 𝒦 ≤ mΩ := shMarkedSigma_le hc₁ hc₂ hm₁ hm₂
    ((measurable_cutLife m).comp hd.measζ₁) ((measurable_cutLife m).comp hd.measζ₂) hh₀ t
  have hF : MeasurableSpace.comap (fcCappedRecord ηc₁ ηc₂
      (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) t) inferInstance ≤
      aeSigma 𝒦 P :=
    (comap_fcCappedRecord_le_aeSigma_shHist hc₁ hc₂ hpair t).trans
      (StagedEntrance.aeSigma_le_aeSigma (le_sup_right.trans (le_aeSigma _ P)))
  have hcmp := ae_fcPhysicalRecord_eq_capped hd hc₁ hc₂ m t hae hag₁ hag₂
  have htr : ∀ D, MeasurableSet[𝒦 ⊔ fcPhysicalFiltration P d t] D →
      MeasurableSet[aeSigma 𝒦 P]
        (D ∩ fcPhysicalRecord d t ⁻¹' fcPhysicalBoxSet t m) := by
    intro D hD
    have h := measurableSet_aeSigma_inter_of_ae hF
      (measurableSet_fcPhysicalBoxSet t m) hcmp D
      ((sup_le ((le_aeSigma 𝒦 P).trans le_sup_left) le_sup_right) _ hD)
    exact StagedEntrance.aeSigma_le_aeSigma le_rfl _ h
  have hh := ae_condExp_eq_of_trace (𝒦 := 𝒦) le_sup_left
    (sup_le h𝒦 ((fcPhysicalFiltration P d).le t)) htr hX
  rw [preimage_fcPhysicalBoxSet] at hh
  filter_upwards [hh] with ω hω hb hl using hω ⟨hb, hl⟩

/-- Countable gluing into the concrete physical filtration. If the identified
bounded characteristic functional is physical-measurable, the one-sided history
comparison and the tower property suffice: no comparison of two field-germ
sigma algebras is needed. The measurability of that identified functional is
an explicit premise, not inferred from the existence of capped means. -/
theorem ae_condExp_physical_of_capped_kernels {P : Measure Ω} [IsProbabilityMeasure P]
    {d : PairData Ω} (hd : d.IsMeasGood) {η₁ η₂ : Ω → ℝ≥0 → ℂ}
    (ηc₁ ηc₂ : ℕ → Ω → ℝ≥0 → ℂ)
    (hc₁ : ∀ m ω, Continuous (ηc₁ m ω)) (hc₂ : ∀ m ω, Continuous (ηc₂ m ω))
    (hm₁ : ∀ m s, Measurable fun ω => ηc₁ m ω s)
    (hm₂ : ∀ m s, Measurable fun ω => ηc₂ m ω s)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : Measurable h₀) (t : ℝ≥0)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω s = η₂ ω s)
    (hag₁ : ∀ m, ∀ᵐ ω ∂P, ∀ s, ηc₁ m ω s = η₁ ω (capTime m (d.ζ₁ ω) s))
    (hag₂ : ∀ m, ∀ᵐ ω ∂P, ∀ s, ηc₂ m ω s = η₂ ω (capTime m (d.ζ₂ ω) s))
    (hpair : ∀ m, ∀ᵐ ω ∂P, ∃ σ₁ σ₂, IsFCPair (ηc₁ m ω) (ηc₂ m ω) σ₁ σ₂)
    {X Y : Ω → ℂ} (hX : Integrable X P)
    (hY : StronglyMeasurable[fcPhysicalFiltration P d t] Y) (hYb : ∀ ω, ‖Y ω‖ ≤ 1)
    {A : Set Ω} (hA : MeasurableSet[fcPhysicalFiltration P d t] A)
    (hAlive : ∀ ω ∈ A, ω ∈ meetSet d ∧ ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω)
    (hker : ∀ m, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ lineBox d t m →
      P[X | shMarkedSigma (ηc₁ m) (ηc₂ m) (fun ω => cutLife (d.ζ₁ ω) m)
        (fun ω => cutLife (d.ζ₂ ω) m) h₀ t] ω = Y ω) :
    ∀ᵐ ω ∂P, ω ∈ A → P[X | fcPhysicalFiltration P d t] ω = Y ω := by
  have hlocal (m : ℕ) : ∀ᵐ ω ∂P, ω ∈ A ∩
      (lineBox d t m ∩ {ω | ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω}) →
      P[X | fcPhysicalFiltration P d t] ω = Y ω := by
    have hcomp := ae_condExp_shMarkedSigma_sup_physical hd (hc₁ m) (hc₂ m) (hm₁ m) (hm₂ m)
      hh₀ m t hae (hag₁ m) (hag₂ m) (hpair m) hX
    apply ae_condExp_eq_on_of_le le_sup_right
      (sup_le (shMarkedSigma_le (hc₁ m) (hc₂ m) (hm₁ m) (hm₂ m)
        ((measurable_cutLife m).comp hd.measζ₁) ((measurable_cutLife m).comp hd.measζ₂) hh₀ t)
        ((fcPhysicalFiltration P d).le t)) hX hY hYb
      (hA.inter (measurableSet_fcPhysicalLiveBox hd P t m))
    filter_upwards [hcomp, hker m] with ω he hk ⟨hωA, hωbox, hωlife⟩
    exact (he hωbox hωlife).trans (hk hωA hωbox)
  filter_upwards [ae_all_iff.2 hlocal] with ω hω hωA
  obtain ⟨m, hm⟩ := exists_mem_lineBox (hAlive ω hωA).1 t
  exact hω m ⟨hωA, hm, (hAlive ω hωA).2⟩

section FlowInputs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- The first-contact property needed to recover the initial capped mark is supplied
by Lemma 7.7, rather than assumed separately. -/
theorem ae_isFCPair_capped_flowLines (hL77 : Supp10.Lemma77Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (m : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) :
    ∀ᵐ ω ∂P, ∃ σ₁ σ₂, IsFCPair (ηc₁ ω) (ηc₂ ω) σ₁ σ₂ :=
  (ae_firstContact_capped hL77 hκ hκ4 hb hx hθ hh hη₁ hη₂ m hag₁ hag₂).mono
    fun _ hω => exists_isFCPair hω

/-- The active-component Gaussian kernel with the completed physical filtration
included in the conditioning. All history comparisons and the recovery of the
initial capped mark are discharged from the flow-line hypotheses. -/
theorem exists_fcBoxKernel_physical (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℕ) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ,
      (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ s, Measurable fun ω => ηc₁ ω s) ∧ (∀ s, Measurable fun ω => ηc₂ ω s) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s)) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) ∧
      ∀ t : ℝ≥0, ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (shUnion ηc₁ ηc₂ t 0) (centredField h u₀) P g ∧
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ lineBox d t m →
          ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω →
          ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0),
            IsFCLine d ω x₁ x₂ t W γ ζc Q →
            tsupport φ ⊆ d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) →
            P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) |
              shMarkedSigma ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m)
                (fun ω => cutLife (ζ₂ ω) m) (centredField h u₀) t ⊔
                  fcPhysicalFiltration P d t] ω =
              Complex.exp (Complex.I *
                ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
                  (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov
                    (d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q)) φ φ : ℝ) : ℂ)) := by
  subst hζ₁ hζ₂
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hag₁, hag₂, hline⟩ :=
    exists_fcBoxKernel hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd rfl rfl hae hu₀ m
  have hp := ae_isFCPair_capped_flowLines hL77 hκ hκ4 hb hx hθ hh hη₁ hη₂ m hag₁ hag₂
  refine ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hag₁, hag₂, fun t => ?_⟩
  obtain ⟨g, hg, hker⟩ := hline t
  refine ⟨g, hg, fun φ => ?_⟩
  have hcomp := ae_condExp_shMarkedSigma_sup_physical hd hc₁ hc₂ hm₁ hm₂
    (measurable_centredField hh.1 u₀) m t hae hag₁ hag₂ hp
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hh.1))
  filter_upwards [hcomp, hker φ] with ω he hk hbox hlife W γ ζc Q hl hsupp
  exact (he hbox hlife).trans (hk hbox W γ ζc Q hl hsupp)

end FlowInputs

/-- Exact remaining driver inputs. The branch cover permits random force types.
The safe-law fields are K2's stochastic hypotheses; `lifetime` is the geometric
collision/no-return identity. No canonical driver or path match is a field.

This is a conditional interface, not an assertion that the source hypotheses
already supply these data. In particular the preceding history comparison proves
a conditioning enlargement, not a common germ filtration or a threshold identity. -/
structure FCThresholdDriverInputs (P : Measure Ω) (κ θ : ℝ) (M : Set Ω)
    (β : Ω → BoundaryWord) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (Γ : Ω → ℝ≥0 → ℂ) (U : Ω → ℝ≥0∞) where
  filtration : Filtration ℝ≥0 mΩ
  driver : ℝ≥0 → Ω → ℝ
  driver_zero : ∀ ω, driver 0 ω = 0
  driver_continuous : ∀ ω, Continuous fun t => driver t ω
  driver_adapted : StronglyAdapted filtration driver
  word_measurable : Measurable[filtration 0] β
  branch : ℕ → Set Ω
  branch_measurable : ∀ i, MeasurableSet[filtration 0] (branch i)
  cover : ∀ ω, ω ∈ M → ∃ i, ω ∈ branch i
  nL : ℕ → ℕ
  nR : ℕ → ℕ
  rhoL : ∀ i, Fin (nL i) → ℝ
  rhoR : ∀ i, Fin (nR i) → ℝ
  word_type : ∀ i ω, ω ∈ branch i → β ω ∈ FCDet.typeSet κ θ (nL i) (nR i) (rhoL i) (rhoR i)
  integrable : ∀ i (φ : TestOn upperHalfPlaneOpens),
    Integrable (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ) (P.restrict (branch i))
  seed : ∀ i, ∀ᵐ ω ∂P, ω ∈ branch i →
    ¬ ForceWord.ThresholdCondition (rhoL i) (rhoR i) 0
      (FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
  safe_law : ∀ i, HasSafeLaw κ (rhoL i) (rhoR i) P filtration (branch i)
    (FCDet.thr (rhoL i) (rhoR i) driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))) driver
    (Sec7.PocketTraversal.geomLW driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω)))
    (Sec7.PocketTraversal.geomRW driver
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω)))
    (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  safe_members : ∀ i, HasSafeMembers P filtration (branch i)
    (FCDet.thr (rhoL i) (rhoR i) driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))) driver
    (fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω))
  lifetime : ∀ i, ∀ᵐ ω ∂P, ω ∈ branch i →
    U ω = FCDet.thr (rhoL i) (rhoR i) driver
      (fun ω => FCDet.typeXL κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω))
      (fun ω => FCDet.typeXR κ θ (nL i) (nR i) (rhoL i) (rhoR i) (β ω)) ω
  generating_trace : ∀ᵐ ω ∂P, ω ∈ M →
    IsGeneratingTrace (fun t => driver t ω) (U ω) (Γ ω)
  path_continuous : ∀ᵐ ω ∂P, ω ∈ M →
    ContinuousOn (Γ ω) {t | (t : ℝ≥0∞) ≤ U ω}

/-- The threshold driver readings follow from K2's exact inputs on countably many
force-type branches. This discharges the code-match part of `hDriverReading`;
the data in `FCThresholdDriverInputs` remain explicitly conditional. -/
theorem ae_driverReading_of_thresholdInputs {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} (hκ : 0 < κ) {M : Set Ω} {β : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (h : FCThresholdDriverInputs P κ θ M β Hc Γ U)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G) :
    ∀ᵐ ω ∂P, ω ∈ M → ∃ W : ℝ≥0 → ℝ,
      ContinuousOn W {t | (t : ℝ≥0∞) < U ω} ∧ W 0 = 0 ∧
      ContinuousOn (Γ ω) {t | (t : ℝ≥0∞) ≤ U ω} ∧
      IsGeneratingTrace W (U ω) (Γ ω) ∧
      IsDriverCodeMatch (G (β ω, Hc ω)) W (U ω) := by
  have hmatch (i : ℕ) := FCDet.ae_driverCodeMatch_of_hasSafeLaw_on hκ
    (h.branch_measurable i) h.word_measurable (h.word_type i)
    h.driver_zero h.driver_continuous h.driver_adapted hHc (h.integrable i)
    (h.seed i) (h.safe_law i) (h.safe_members i) hG
  have hmatches := ae_all_iff.2 hmatch
  have hlives := ae_all_iff.2 h.lifetime
  filter_upwards [hmatches, hlives, h.generating_trace, h.path_continuous]
    with ω hm hl htr hc hω
  obtain ⟨i, hi⟩ := h.cover ω hω
  refine ⟨fun t => h.driver t ω, (h.driver_continuous ω).continuousOn,
    h.driver_zero ω, hc hω, htr hω, ?_⟩
  rw [hl i hi]
  exact hm i hi

/-- The precise source-level construction still needed for the driver route.
It asks for K2 inputs for the actual canonical continuations, without assuming
either canonical code match. The lifetime field of each record is the remaining
collision-weight/no-return theorem, not a consequence of clock measurability. -/
def FirstContactThresholdDriverInputsStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    Nonempty (FCThresholdDriverInputs P κ θ₁ (meetSet d) β (hd.chartField κ h) γ₁ U₁) ∧
      Nonempty (FCThresholdDriverInputs P κ θ₂ (meetSet d) β (hd.chartField κ h) γ₂ U₂)

/-- Source-facing determination from the explicitly named remaining construction.
The path bridge, disintegration and canonical driver matching are all proved;
`hInputs` is not discharged by this theorem. -/
theorem firstContactCanonCondDetStatement_of_thresholdInputs
    (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u})
    (hDriverCode : CanonicalDriverCodeStatement)
    (hInputs : FirstContactThresholdDriverInputsStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} := by
  apply firstContactCanonCondDetStatement_of_driver_readings hL75 hL77 hA56 hDriverCode
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon G₁ G₂ hG₁ hG₂
  obtain ⟨⟨I₁⟩, ⟨I₂⟩⟩ := hInputs κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
  have hr₁ := ae_driverReading_of_thresholdInputs hκ (hd.measurable_chartField κ hh.1) I₁ hG₁
  have hr₂ := ae_driverReading_of_thresholdInputs hκ (hd.measurable_chartField κ hh.1) I₂ hG₂
  filter_upwards [hr₁, hr₂] with ω h₁ h₂ hω
  obtain ⟨W₁, hW₁⟩ := h₁ hω
  obtain ⟨W₂, hW₂⟩ := h₂ hω
  exact ⟨W₁, W₂, hW₁, hW₂⟩

end InteractingSLE.Restart.FCPlumb
