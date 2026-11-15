/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbL
import InteractingSLE.Spec.Restart.StagedEntrance

/-!
# Physical information for the retained continuation

Packet PROVE-RETPLUMB. The cap in `retHist76` does not affect observations before
either stopping line. Consequently the completed retained histories increase with
the cutoffs and define the physical filtration at `(u, r + t)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open Sec6 Sec7.Lemma76F LocalSets

/-- Before a finite cap, the capped time only reads the time and the lifetime. -/
theorem capTime_eq_min_of_le_cap {a m : ℝ≥0} (ham : a ≤ m) (ζ : ℝ≥0∞) :
    capTime m ζ a = (min (a : ℝ≥0∞) ζ).toNNReal := by
  have hma : min (a : ℝ≥0∞) ζ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have hzm : min ζ (m : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  apply ENNReal.coe_injective
  rw [capTime, ENNReal.coe_min, ENNReal.coe_toNNReal hzm,
    ENNReal.coe_toNNReal hma, ← min_assoc]
  exact min_eq_left ((min_le_left _ _).trans (ENNReal.coe_le_coe.2 ham))

/-- A killing record before the cap records the original lifetime. -/
theorem lifeRec_cutLife_eq {a m : ℝ≥0} (ham : a < m) (ζ : ℝ≥0∞) :
    lifeRec (cutLife ζ m) a = lifeRec ζ a := by
  by_cases hζm : ζ ≤ m
  · simp only [cutLife, hζm, ↓reduceIte]
  · have hζa : ¬ ζ ≤ a := fun h =>
      hζm (h.trans (ENNReal.coe_le_coe.2 ham.le))
    simp only [cutLife, hζm, ↓reduceIte, lifeRec, hζa, ite_self]

/-- The killed history through `a` is independent of a cap strictly larger than `a`. -/
theorem khist_capped_eq {a m m' : ℝ≥0} (ham : a < m) (ham' : a < m')
    (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) :
    khistOf (pathCoord fun t => η (capTime m ζ t)) (cutLife ζ m) a =
      khistOf (pathCoord fun t => η (capTime m' ζ t)) (cutLife ζ m') a := by
  apply Prod.ext
  · change histOf _ a = histOf _ a
    apply histOf_congr
    intro q hq
    have hqa : (q : ℝ≥0) ≤ a := ENNReal.coe_le_coe.1 hq
    change η (capTime m ζ q) = η (capTime m' ζ q)
    rw [capTime_eq_min_of_le_cap (hqa.trans ham.le),
      capTime_eq_min_of_le_cap (hqa.trans ham'.le)]
  · exact (lifeRec_cutLife_eq ham ζ).trans (lifeRec_cutLife_eq ham' ζ).symm

variable {Ω : Type*}

/-- Restricting a later retained history recovers the earlier retained history,
including its killing records, despite the change in the auxiliary cap. -/
theorem retHist76_restrict (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    {u r u' r' : ℝ≥0} (hu : u ≤ u') (hr : r ≤ r') (ω : Ω) :
    (khistRestrict (retHist76 η₁ η₂ ζ₁ ζ₂ u' r' ω).1 u,
      khistRestrict (retHist76 η₁ η₂ ζ₁ ζ₂ u' r' ω).2 r) =
        retHist76 η₁ η₂ ζ₁ ζ₂ u r ω := by
  change (khistRestrict (khistOf _ _ u') u, khistRestrict (khistOf _ _ r') r) = _
  rw [khistRestrict_khistOf (ENNReal.coe_le_coe.2 hu),
    khistRestrict_khistOf (ENNReal.coe_le_coe.2 hr)]
  exact Prod.ext
    (khist_capped_eq (hu.trans_lt (lt_capR_left u' r')) (lt_capR_left u r) _ _)
    (khist_capped_eq (hr.trans_lt (lt_capR_right u' r')) (lt_capR_right u r) _ _)

/-- Earlier retained histories are measurable functions of later retained histories. -/
theorem comap_retHist76_mono (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    {u r u' r' : ℝ≥0} (hu : u ≤ u') (hr : r ≤ r') :
    MeasurableSpace.comap (retHist76 η₁ η₂ ζ₁ ζ₂ u r) inferInstance ≤
      MeasurableSpace.comap (retHist76 η₁ η₂ ζ₁ ζ₂ u' r') inferInstance := by
  have hm : Measurable fun y : KHist × KHist =>
      (khistRestrict y.1 u, khistRestrict y.2 r) :=
    (measurable_khistRestrict.comp (measurable_fst.prodMk measurable_const)).prodMk
      (measurable_khistRestrict.comp (measurable_snd.prodMk measurable_const))
  have he : retHist76 η₁ η₂ ζ₁ ζ₂ u r =
      (fun y : KHist × KHist => (khistRestrict y.1 u, khistRestrict y.2 r)) ∘
        retHist76 η₁ η₂ ζ₁ ζ₂ u' r' :=
    funext fun ω => (retHist76_restrict η₁ η₂ ζ₁ ζ₂ hu hr ω).symm
  rw [he]
  exact (hm.comp (comap_measurable _)).comap_le

variable [mΩ : MeasurableSpace Ω]

/-- Completed physical information increases with both stopping parameters. -/
theorem retSigma76_mono (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    {u r u' r' : ℝ≥0} (hu : u ≤ u') (hr : r ≤ r') :
    retSigma76 P η₁ η₂ ζ₁ ζ₂ u r ≤ retSigma76 P η₁ η₂ ζ₁ ζ₂ u' r' := by
  refine inf_le_inf_left mΩ ?_
  exact StagedEntrance.aeSigma_le_aeSigma
    ((comap_retHist76_mono η₁ η₂ ζ₁ ζ₂ hu hr).trans (le_aeSigma _ P))

/-- Physical filtration of the second continuation: the completed retained histories
at the line `(u, r + t)`. -/
def retPhysFiltration (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq t := retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t)
  mono' _ _ hst := retSigma76_mono P η₁ η₂ ζ₁ ζ₂ le_rfl (add_le_add le_rfl hst)
  le' t := retSigma76_le P η₁ η₂ ζ₁ ζ₂ u (r + t)

theorem retPhysFiltration_apply (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u r t : ℝ≥0) :
    retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t = retSigma76 P η₁ η₂ ζ₁ ζ₂ u (r + t) := rfl

/-- An ambient measurable version of an observable of the retained history is
measurable for the completed physical information. -/
theorem measurable_retSigma76_of_ae_eq {P : Measure Ω}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {Y : Type*} [MeasurableSpace Y] {f g : Ω → Y} (hf : Measurable f)
    (hg : Measurable[MeasurableSpace.comap (retHist76 η₁ η₂ ζ₁ ζ₂ u r)
      inferInstance] g) (he : f =ᵐ[P] g) :
    Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] f :=
  fun _ hB => ⟨hf hB, WholeField.measurable_aeSigma_of_ae_eq' hg he hB⟩

/-- The first killing record is observable in the physical information. -/
theorem measurable_lifeRec_retSigma76_left (P : Measure Ω)
    (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (hζ₁ : Measurable ζ₁)
    (u r : ℝ≥0) :
    Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] fun ω => lifeRec (ζ₁ ω) u := by
  apply measurable_retSigma76_of_ae_eq
    (measurable_lifeRec.comp (hζ₁.prodMk measurable_const))
    (measurable_snd.comp (measurable_fst.comp (comap_measurable
      (retHist76 η₁ η₂ ζ₁ ζ₂ u r))))
  exact Eventually.of_forall fun ω => (lifeRec_cutLife_eq (lt_capR_left u r) (ζ₁ ω)).symm

/-- The second killing record is observable in the physical information. -/
theorem measurable_lifeRec_retSigma76_right (P : Measure Ω)
    (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (hζ₂ : Measurable ζ₂)
    (u r : ℝ≥0) :
    Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] fun ω => lifeRec (ζ₂ ω) r := by
  apply measurable_retSigma76_of_ae_eq
    (measurable_lifeRec.comp (hζ₂.prodMk measurable_const))
    (measurable_snd.comp (measurable_snd.comp (comap_measurable
      (retHist76 η₁ η₂ ζ₁ ζ₂ u r))))
  exact Eventually.of_forall fun ω => (lifeRec_cutLife_eq (lt_capR_right u r) (ζ₂ ω)).symm

/-- Both prefixes being alive is a retained-history event. -/
theorem measurableSet_retLive (P : Measure Ω) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂) (u r : ℝ≥0) :
    MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r]
      {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω} := by
  have he : {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω} =
      {ω | lifeRec (ζ₁ ω) u = ⊤} ∩ {ω | lifeRec (ζ₂ ω) r = ⊤} := by
    ext ω
    exact and_congr (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).symm
      (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).symm
  rw [he]
  exact ((measurable_lifeRec_retSigma76_left P η₁ η₂ ζ₁ ζ₂ hζ₁ u r)
    (measurableSet_singleton ⊤)).inter
      ((measurable_lifeRec_retSigma76_right P η₁ η₂ ζ₁ ζ₂ hζ₂ u r)
        (measurableSet_singleton ⊤))

end InteractingSLE.Restart.RetAux79
