/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndStop

/-!
# Lemma 4.7 in the chart `Q`: the image word before a counterflow time is known from the two stopped histories

Packet PROVE-CFRESTART5, item D3 (the Lemma 4.7 mirror of GLUECOND7's `CrossCondMartMarks`). On good glued samples,
every event of the raw image filtration `qRaw r`, intersected with `{t′ before contact, r < σ(t′)}` (`t′ ≤ t`
rational), is the preimage under the stopped-data map `stopD47 s t` of a Borel set of stopped data, and so is the
validity event `qAv φ t`. Since `stopD47 s t` is measurable for the marks `cfGlueMarks s t` and the good samples have
full measure, these are the hypotheses `hM1`, `hM3` of the passage (`marks47_inter`, `marks47_avoid`).

* `AvD47`, `measurableSet_AvD47`: the support-avoidance event read from stopped data (both hulls are hitting-measurable
  and relatively closed);
* **`isGoodD47_stopD`**: stopped data of good samples are good;
* `IsKilledCurve.exists_lt_capClock_lt`, `img_eq_stopD47` (the killed image word up to `r` is read from the stopped
  data), `isAway_iff_isAwayD47`, `qAnn_le_iff'`;
* **`exists_measurableSet_stopD47_iff`** (the Galmarino-type transfer, σ-induction over the generators of `qRaw r`);
* **`marks47_inter`**, **`marks47_avoid`**; **`isLocalMartingaleBefore_q_of_good`**: the martingale clause of the
  killed image word with the marks discharged.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar MartChar.RealFlow LocalSets
open CrossCond (cfGlueMarks)

/-! ### A capacity time below the clock at a pre-contact time -/

theorem IsKilledCurve.exists_lt_capClock_lt {γ : ℝ → ℂ} {P : Set ℝ} (hγ : IsKilledCurve γ P) {t' r : ℝ}
    (htP : t' ∈ P) (hr0 : 0 ≤ r) (hrc : r < capClock γ t') : ∃ S ∈ P, 0 < S ∧ S < t' ∧ r < capClock γ S := by
  have ht'0 : 0 < t' := by
    rcases (hγ.nonneg t' htP).eq_or_lt with h | h
    · rw [← h, hγ.capClock_zero] at hrc
      linarith
    · exact h
  obtain ⟨δ, hδ, hcδ⟩ := Metric.continuousWithinAt_iff.1 (hγ.continuousOn_capClock t' htP)
    (capClock γ t' - r) (by linarith)
  set S := max (t' / 2) (t' - δ / 2) with hSdef
  have hS0 : 0 < S := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hSt : S < t' := max_lt (by linarith) (by linarith)
  have hSP : S ∈ P := hγ.icc t' htP ⟨hS0.le, hSt.le⟩
  have hd : dist S t' < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · have := le_max_right (t' / 2) (t' - δ / 2)
      linarith
    · linarith
  have h := hcδ hSP hd
  rw [Real.dist_eq, abs_lt] at h
  exact ⟨S, hSP, hS0, hSt, by linarith [h.1]⟩

namespace Kill47

/-! ### The support-avoidance event read from stopped data -/

section Av

variable {nL nR : ℕ} {s : ℝ≥0} {t : ℚ}

/-- **The support-avoidance event read from stopped data**: `supp φ` misses both hulls (flow hull at `s`,
reflected counterflow hull at `t`) and lies in `ℍ`. -/
def AvD47 (s : ℝ≥0) (t : ℚ) (φ : TestOn upperHalfPlaneOpens) : Set (Y47 nL nR) :=
  {y | tsupport φ ⊆ H \ (hullAt s y.1 ∪ cfHullQ (t : ℝ).toNNReal y.2)}

theorem measurableSet_AvD47 (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet (AvD47 (nL := nL) (nR := nR) s t φ) := by
  have hU : Measurable[_, hittingSigma] fun y : Y47 nL nR => hullAt s y.1 ∪ cfHullQ (t : ℝ).toNNReal y.2 :=
    measurable_union_hitting ((measurable_hullAt s).comp measurable_fst)
      ((measurable_cfHullQ (t : ℝ).toNNReal).comp measurable_snd)
  have e : AvD47 (nL := nL) (nR := nR) s t φ = {_y | tsupport φ ⊆ H} ∩
      (fun y : Y47 nL nR => hullAt s y.1 ∪ cfHullQ (t : ℝ).toNNReal y.2) ⁻¹'
        {S : Set ℂ | Disjoint (tsupport φ) (relClosureH S)} := by
    ext y
    obtain ⟨hsub, hopen⟩ := CrossCond.union_relClosed s (t : ℝ).toNNReal y.1 y.2
    simp only [AvD47, mem_ofPred_eq, mem_inter_iff, mem_preimage, relClosureH_eq hsub hopen]
    constructor
    · intro h
      exact ⟨fun z hz => (h hz).1, Set.disjoint_left.2 fun z hz hzU => (h hz).2 hzU⟩
    · rintro ⟨h1, h2⟩ z hz
      exact ⟨h1 hz, fun hzU => Set.disjoint_left.1 h2 hz hzU⟩
  rw [e]
  exact (MeasurableSet.const _).inter
    (hU (measurableSet_disjoint_relClosureH φ.hasCompactSupport.isCompact φ.tsupport_subset))

end Av

/-! ### Good samples have good stopped data -/

section Good

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t : ℚ} {p : Ω × HistorySpace 0 0}

theorem isGoodD47_stopD (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) :
    IsGoodD47 s t (stopD47 W VL VR ζ s t p) := by
  have hg := hEg p hp
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  refine ⟨isKilledCurve_gammaD47_stopD ht hEg hp, fun q hq0 hqt => ?_, fun q hq0 hqt hq => ?_⟩
  · rw [mem_PcD47_stopD_iff hp hg hqt, qgPre_of_mem hp,
      CrossCond.Word49.mem_preContact_iff_ball (histLine_cont hg) (isClosed_qObs hg) hq0]
    simp only [RatD47, mem_ofPred_eq]
    refine exists_congr fun m => forall_congr' fun u => imp_congr_right fun _ => imp_congr_right fun huq => ?_
    rw [alphaD47_stopD hg (huq.trans hqt), GD47_stopD]
  · have hqP := (mem_PcD47_stopD_iff hp hg hqt).1 hq
    exact (hγ.cont.mono (hγ.icc _ hqP)).congr fun u hu => gammaD47_stopD hp hg (hu.2.trans hqt)

theorem mem_AvD47_stopD_iff (φ : TestOn upperHalfPlaneOpens) :
    stopD47 W VL VR ζ s t p ∈ AvD47 s t φ ↔
      tsupport φ ⊆ H \ (hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ (t : ℝ).toNNReal p.2) := by
  simp only [AvD47, mem_ofPred_eq, stopD47, hullAt_flowStop, CrossCond.Word49.cfHullQ_cfStop]

/-- **The validity event in the chart, without the chart** (good sample before contact). -/
theorem isChartAvoid_capClock_iff47 (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) {u : ℝ≥0}
    (huP : (u : ℝ) ∈ qgPre W VL VR ζ s E p) (φ : TestOn upperHalfPlaneOpens) :
    Sec7.Lemma71D.IsChartAvoid (fun r => qW W VL VR ζ s E r p) (qT W VL VR ζ s E p : ℝ≥0∞) (fChart W VL VR ζ s p) φ
        (capClock (qgCurve W s E p) u).toNNReal ↔
      tsupport φ ⊆ H \ (hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ u p.2) := by
  unfold Sec7.Lemma71D.IsChartAvoid
  rw [fChart_inv_image_eq hEg hp huP]
  exact ⟨fun h => h.2, fun h => ⟨(isKilledCurve_qgCurve hEg p).lt_kcLife huP, h⟩⟩

end Good

/-! ### The image word before `t` from the stopped data -/

section Transfer

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t t' : ℚ} {p : Ω × HistorySpace 0 0}

/-- **The killed image word up to the image time `r` is read from the stopped data** (good sample, `t′ ≤ t` before
contact with `r < σ(t′)`). -/
theorem img_eq_stopD47 {mL mR : ℕ} (xL : Fin mL → ℝ) (xR : Fin mR → ℝ) (ht : 0 < t)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) (ht't : t' ≤ t) (htP : (t' : ℝ) ∈ qgPre W VL VR ζ s E p)
    {r : ℝ≥0} (hrc : (r : ℝ) < capClock (qgCurve W s E p) t') {r' : ℝ≥0} (hr' : r' ≤ r) :
    (r' : WithTop ℝ≥0) < kcLife (gammaD47 s (stopD47 W VL VR ζ s t p)) (PD47 t s (stopD47 W VL VR ζ s t p)) ∧
      (r' : WithTop ℝ≥0) < qT W VL VR ζ s E p ∧
      qW W VL VR ζ s E r' p = kcW (gammaD47 s (stopD47 W VL VR ζ s t p)) (PD47 t s (stopD47 W VL VR ζ s t p)) r' ∧
      (∀ i, qVL xL W VL VR ζ s E i r' p = kcVL (gammaD47 s (stopD47 W VL VR ζ s t p))
        (PD47 t s (stopD47 W VL VR ζ s t p)) (gXLD47 xL s (stopD47 W VL VR ζ s t p)) i r') ∧
      ∀ j, qVR xR W VL VR ζ s E j r' p = kcVR (gammaD47 s (stopD47 W VL VR ζ s t p))
        (PD47 t s (stopD47 W VL VR ζ s t p)) (gXRD47 xR s (stopD47 W VL VR ζ s t p)) j r' := by
  have hg := hEg p hp
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  have hγx := isKilledCurve_gammaD47_stopD (s := s) ht hEg hp
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  obtain ⟨S, hSP, hS0, hSt', hrS⟩ := hγ.exists_lt_capClock_lt htP r.coe_nonneg hrc
  have hSx : S ∈ PD47 t s (stopD47 W VL VR ζ s t p) := by
    rw [PD47_stopD hp hg]
    exact ⟨hSP, lt_of_lt_of_le hSt' ht't'⟩
  have hEq : EqOn (qgCurve W s E p) (gammaD47 s (stopD47 W VL VR ζ s t p)) (Icc 0 S) := fun u hu =>
    (gammaD47_stopD hp hg (hu.2.trans (hSt'.le.trans ht't'))).symm
  have hcc : ∀ u ∈ Icc 0 S, capClock (qgCurve W s E p) u = capClock (gammaD47 s (stopD47 W VL VR ζ s t p)) u :=
    fun u hu => WangWu.capClock_congr (hEq.mono (Icc_subset_Icc_right hu.2))
  obtain ⟨Wd, hWd, hWd0, -, -, -, hK⟩ := hγ.localDriver S hSP hS0
  have h1 := hγ.eqOn_kcPath_of_localDriver hSP hS0 hWd hWd0 (fun u hu => (hK u hu).2)
  have h2 := hγx.eqOn_kcPath_of_localDriver hSx hS0 hWd hWd0 (fun u hu => by
    rw [← hcc u hu, ← image_congr (hEq.mono (Icc_subset_Icc_right hu.2))]
    exact (hK u hu).2)
  have hcS := hcc S ⟨hS0.le, le_rfl⟩
  have hr'S : (r' : ℝ) ≤ capClock (qgCurve W s E p) S := (by exact_mod_cast hr' : (r' : ℝ) ≤ r).trans hrS.le
  have hr'S' : (r' : ℝ) ≤ capClock (gammaD47 s (stopD47 W VL VR ζ s t p)) S := hcS ▸ hr'S
  have hle : ∀ {c : ℝ}, (r' : ℝ) ≤ c → (r' : WithTop ℝ≥0) ≤ ((c.toNNReal : ℝ≥0) : WithTop ℝ≥0) := fun h =>
    WithTop.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le ((NNReal.coe_nonneg _).trans h)).2 h)
  have hlt : (r' : WithTop ℝ≥0) < qT W VL VR ζ s E p := lt_of_le_of_lt (hle hr'S) (hγ.lt_kcLife hSP)
  have hltx : (r' : WithTop ℝ≥0) < kcLife (gammaD47 s (stopD47 W VL VR ζ s t p))
      (PD47 t s (stopD47 W VL VR ζ s t p)) := lt_of_le_of_lt (hle hr'S') (hγx.lt_kcLife hSx)
  refine ⟨hltx, hlt, ?_, fun i => ?_, fun j => ?_⟩
  · rw [qW, kcW_eq_of_eqOn h1 hr'S, kcW_eq_of_eqOn h2 hr'S']
  · rw [qVL, kcVL_eq_neg_rightImg hWd h1 hr'S hlt, kcVL_eq_neg_rightImg hWd h2 hr'S' hltx, gXLD47_stopD xL hp hg]
  · rw [qVR, kcVR_eq_rightImg hWd h1 hr'S hlt, kcVR_eq_rightImg hWd h2 hr'S' hltx, gXRD47_stopD xR hp hg]

theorem isAway_iff_isAwayD47 (hg : IsGood47 W VL VR ζ p) {n : ℕ} {q : ℚ} (hqt : (q : ℝ) ≤ t) :
    IsAway W VL VR ζ s n p q ↔ IsAwayD47 s n (stopD47 W VL VR ζ s t p) q := by
  simp only [IsAway, IsAwayD47]
  refine and_congr_right fun _ => forall_congr' fun u => imp_congr_right fun _ => imp_congr_right fun huq => ?_
  rw [alphaD47_stopD hg (huq.trans hqt), GD47_stopD]

/-- The announcing events on `{t′ before contact, r < σ(t′)}`. -/
theorem qAnn_le_iff' (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hp : p ∈ E) (ht'0 : (0 : ℝ) ≤ t')
    {r : ℝ≥0} (hrc : (r : ℝ) < capClock (qgCurve W s E p) t') {r' : ℝ≥0} (hr' : r' ≤ r) (n : ℕ) :
    qAnn W VL VR ζ s E n p ≤ r' ↔ (∀ q : ℚ, (q : ℝ) < t' → IsAway W VL VR ζ s n p q →
      capClock (qgCurve W s E p) q ≤ r') ∧ ¬ IsAway W VL VR ζ s n p t' := by
  classical
  have hr'r : (r' : ℝ) ≤ r := by exact_mod_cast hr'
  simp only [qAnn, hp, ↓reduceIte]
  rw [ciSup_le_iff (bddAbove_awayCap hEg n hp)]
  constructor
  · intro h
    refine ⟨fun q hq ha => ?_, fun ha => ?_⟩
    · have := h q
      simp only [awayCap, ha, ↓reduceIte] at this
      rw [Real.toNNReal_le_iff_le_coe] at this
      exact this
    · have := h t'
      simp only [awayCap, ha, ↓reduceIte] at this
      rw [Real.toNNReal_le_iff_le_coe] at this
      linarith
  · rintro ⟨h1, h2⟩ q
    by_cases ha : IsAway W VL VR ζ s n p q
    · simp only [awayCap, ha, ↓reduceIte]
      rw [Real.toNNReal_le_iff_le_coe]
      by_cases hq : (q : ℝ) < t'
      · exact h1 q hq ha
      · exfalso
        refine h2 ⟨⟨ht'0, le_trans (not_lt.1 hq) ha.1.2⟩, fun u h3 h4 => ha.2 u h3 (h4.trans (not_lt.1 hq))⟩
    · simp only [awayCap, ha, ↓reduceIte]
      exact zero_le

end Transfer

/-! ### The σ-algebra induction -/

section Class

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t t' : ℚ}
  {mL mR : ℕ} {xL : Fin mL → ℝ} {xR : Fin mR → ℝ}

omit mΩ in
theorem exists_measurableSet_of_subtypeD47 {S : Set {y : Y47 nL nR // IsGoodD47 s t y}} (hS : MeasurableSet S) :
    ∃ C : Set (Y47 nL nR), MeasurableSet C ∧ ∀ x : {y : Y47 nL nR // IsGoodD47 s t y}, x ∈ S ↔ x.1 ∈ C := by
  obtain ⟨C, hC, rfl⟩ := hS
  exact ⟨C, hC, fun x => Iff.rfl⟩

/-- **The Galmarino-type transfer**: on the good samples with `t′` before contact and `r < σ(t′)`, every event of
the raw image filtration `qRaw r` is the preimage of a Borel set of stopped data (`t′ ≤ t`). -/
theorem exists_measurableSet_stopD47_iff (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (ht'0 : (0 : ℝ) ≤ t')
    (ht't : t' ≤ t) (r : ℝ≥0) {A : Set (Ω × HistorySpace 0 0)}
    (hA : MeasurableSet[qRaw xL xR W VL VR ζ s E r] A) :
    ∃ C : Set (Y47 nL nR), MeasurableSet C ∧ ∀ p, p ∈ E →
      (t' : ℝ) ∈ qgPre W VL VR ζ s E p → (r : ℝ) < capClock (qgCurve W s E p) t' →
      (p ∈ A ↔ stopD47 W VL VR ζ s t p ∈ C) := by
  classical
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  have hA' : MeasurableSet[MeasurableSpace.generateFrom (qGen xL xR W VL VR ζ s E r)] A :=
    (MeasurableSpace.measurableSet_inf.1 hA).1
  have hx : ∀ p : Ω × HistorySpace 0 0, p ∈ E → IsGoodD47 s t (stopD47 W VL VR ζ s t p) := fun p hp =>
    isGoodD47_stopD ht hEg hp
  refine MeasurableSpace.generateFrom_induction (qGen xL xR W VL VR ζ s E r)
    (fun A _ => ∃ C : Set (Y47 nL nR), MeasurableSet C ∧
      ∀ p, p ∈ E → (t' : ℝ) ∈ qgPre W VL VR ζ s E p →
        (r : ℝ) < capClock (qgCurve W s E p) t' → (p ∈ A ↔ stopD47 W VL VR ζ s t p ∈ C)) ?_ ?_ ?_ ?_ A hA'
  · rintro A ⟨r', hr', hcase⟩ -
    rcases hcase with ⟨B, hB, hWc | ⟨i, hVLc⟩ | ⟨j, hVRc⟩⟩ | hTc | ⟨n, hAnn⟩ | ⟨B, hB, hRev⟩
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD47 (measurable_kcW_gammaD47 (s := s) (t := t) r' hB)
      refine ⟨C, hC, fun p hp htP hrc => ?_⟩
      obtain ⟨-, -, hW', -, -⟩ := img_eq_stopD47 xL xR ht hEg hp ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopD47 W VL VR ζ s t p, hx p hp⟩)
      rw [hWc]
      simp only [mem_preimage]
      rw [← hW']
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD47
        (measurable_kcVL_gammaD47 (s := s) (t := t) xL i r' hB)
      refine ⟨C, hC, fun p hp htP hrc => ?_⟩
      obtain ⟨-, -, -, hVL', -⟩ := img_eq_stopD47 xL xR ht hEg hp ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopD47 W VL VR ζ s t p, hx p hp⟩)
      rw [hVLc]
      simp only [mem_preimage]
      rw [← hVL' i]
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD47
        (measurable_kcVR_gammaD47 (s := s) (t := t) xR j r' hB)
      refine ⟨C, hC, fun p hp htP hrc => ?_⟩
      obtain ⟨-, -, -, -, hVR'⟩ := img_eq_stopD47 xL xR ht hEg hp ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopD47 W VL VR ζ s t p, hx p hp⟩)
      rw [hVRc]
      simp only [mem_preimage]
      rw [← hVR' j]
    · refine ⟨univ, MeasurableSet.univ, fun p hp htP hrc => ?_⟩
      obtain ⟨-, hT, -⟩ := img_eq_stopD47 xL xR ht hEg hp ht't htP hrc hr'
      rw [hTc]
      exact ⟨fun _ => mem_univ _, fun _ => hT⟩
    · set S : Set {y : Y47 nL nR // IsGoodD47 s t y} := (⋂ q : ℚ, {x : {y : Y47 nL nR // IsGoodD47 s t y} |
          (q : ℝ) < t' → IsAwayD47 s n x.1 q →
            ({x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1}.indicator
              (fun x => capClock (gammaD47 s x.1) q) x) ≤ r'}) ∩
          {x : {y : Y47 nL nR // IsGoodD47 s t y} | ¬ IsAwayD47 s n x.1 t'} with hSdef
      have hSm : MeasurableSet S := by
        refine (MeasurableSet.iInter fun q => ?_).inter (measurable_subtype_coe (measurableSet_isAwayD47 n t')).compl
        by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t'
        · have e : {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) < t' → IsAwayD47 s n x.1 q →
              ({x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1}.indicator
                (fun x => capClock (gammaD47 s x.1) q) x) ≤ r'} =
              (Subtype.val ⁻¹' {y : Y47 nL nR | IsAwayD47 s n y q})ᶜ ∪
                {x | ({x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1}.indicator
                  (fun x => capClock (gammaD47 s x.1) q) x) ≤ r'} := by
            ext x
            simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, hq.2, true_imp_iff]
            tauto
          rw [e]
          exact (measurable_subtype_coe (measurableSet_isAwayD47 n q)).compl.union
            (measurableSet_le (measurable_indicator_capClock_gammaD47 q hq.1 (hq.2.le.trans ht't'))
              measurable_const)
        · have e : {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) < t' → IsAwayD47 s n x.1 q →
              ({x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1}.indicator
                (fun x => capClock (gammaD47 s x.1) q) x) ≤ r'} = univ := by
            ext x
            simp only [mem_ofPred_eq, mem_univ, iff_true]
            intro h1 h2
            exact absurd ⟨h2.1.1, h1⟩ hq
          rw [e]
          exact MeasurableSet.univ
      obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD47 hSm
      refine ⟨C, hC, fun p hp htP hrc => ?_⟩
      have hg := hEg p hp
      refine Iff.trans ?_ (hCS ⟨stopD47 W VL VR ζ s t p, hx p hp⟩)
      rw [hAnn]
      show qAnn W VL VR ζ s E n p ≤ r' ↔ _
      rw [qAnn_le_iff' hEg hp ht'0 hrc hr' n]
      have hcap : ∀ q : ℚ, (q : ℝ) ≤ t → capClock (qgCurve W s E p) q =
          capClock (gammaD47 s (stopD47 W VL VR ζ s t p)) q := fun q hqt =>
        WangWu.capClock_congr fun u hu => (gammaD47_stopD hp hg (hu.2.trans hqt)).symm
      have hind : ∀ q : ℚ, (q : ℝ) < t' → IsAwayD47 s n (stopD47 W VL VR ζ s t p) q →
          ({x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1}.indicator
            (fun x => capClock (gammaD47 s x.1) q)
            (⟨stopD47 W VL VR ζ s t p, hx p hp⟩ : {y : Y47 nL nR // IsGoodD47 s t y})) =
            capClock (qgCurve W s E p) q := fun q hq ha => by
        have hPc : (q : ℝ) ∈ PcD47 s (stopD47 W VL VR ζ s t p) :=
          ((hx p hp).rat q ha.1.1 (hq.le.trans ht't')).2 ⟨n, ha.2⟩
        rw [indicator_of_mem (show (⟨stopD47 W VL VR ζ s t p, hx p hp⟩ : {y : Y47 nL nR // IsGoodD47 s t y}) ∈
          {x : {y : Y47 nL nR // IsGoodD47 s t y} | (q : ℝ) ∈ PcD47 s x.1} from hPc), hcap q (hq.le.trans ht't')]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨mem_iInter.2 fun q hq ha => ?_, fun ha => h2 ((isAway_iff_isAwayD47 hg ht't').2 ha)⟩
        rw [hind q hq ha]
        exact h1 q hq ((isAway_iff_isAwayD47 hg (hq.le.trans ht't')).2 ha)
      · rintro ⟨h1, h2⟩
        refine ⟨fun q hq ha => ?_, fun ha => h2 ((isAway_iff_isAwayD47 hg ht't').1 ha)⟩
        have haY := (isAway_iff_isAwayD47 hg (hq.le.trans ht't')).1 ha
        have h := mem_iInter.1 h1 q hq haY
        rwa [hind q hq haY] at h
    · refine ⟨Prod.fst ⁻¹' B, measurable_fst hB, fun p _ _ _ => ?_⟩
      rw [hRev]
      rfl
  · exact ⟨∅, MeasurableSet.empty, fun p _ _ _ => Iff.rfl⟩
  · rintro A _ ⟨C, hC, hAC⟩
    exact ⟨Cᶜ, hC.compl, fun p hp htP hrc => not_congr (hAC p hp htP hrc)⟩
  · intro f _ hf
    choose C hC hfC using hf
    refine ⟨⋃ i, C i, MeasurableSet.iUnion hC, fun p hp htP hrc => ?_⟩
    simp only [mem_iUnion]
    exact exists_congr fun i => hfC i p hp htP hrc

end Class

/-! ### The two marks facts -/

section Marks

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t t' : ℚ}
  {μ : Measure (Ω × HistorySpace 0 0)} {mL mR : ℕ}

/-- **The image word before a counterflow time is known from the two stopped histories** (first marks fact). -/
theorem marks47_inter (xL : Fin mL → ℝ) (xR : Fin mR → ℝ) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hgood : ∀ᵐ p ∂μ, p ∈ E) (r : ℝ≥0) (ht'0 : (0 : ℝ) ≤ t') (ht't : t' ≤ t) {A : Set (Ω × HistorySpace 0 0)}
    (hA : MeasurableSet[qRaw xL xR W VL VR ζ s E r] A) :
    ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧ B' =ᵐ[μ]
      A ∩ {p | (t' : ℝ) ∈ qgPre W VL VR ζ s E p ∧ (r : ℝ) < capClock (qgCurve W s E p) t'} := by
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  obtain ⟨C, hC, hAC⟩ := exists_measurableSet_stopD47_iff ht hEg ht'0 ht't r hA
  obtain ⟨CSt, hCSt, hSt⟩ := exists_measurableSet_of_subtypeD47
    ((measurableSet_mem_PcD47 (nL := nL) (nR := nR) (s := s) (t := t) t' ht'0 ht't').inter
      (measurableSet_lt measurable_const (measurable_indicator_capClock_gammaD47 t' ht'0 ht't')))
  refine ⟨stopD47 W VL VR ζ s t ⁻¹' (C ∩ CSt), measurable_stopD47 s t (hC.inter hCSt), ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hgood] with p hp
  have hg := hEg p hp
  have hgY := isGoodD47_stopD (s := s) ht hEg hp
  have hStiff : ((t' : ℝ) ∈ qgPre W VL VR ζ s E p ∧ (r : ℝ) < capClock (qgCurve W s E p) t') ↔
      stopD47 W VL VR ζ s t p ∈ CSt := by
    refine Iff.trans ?_ (hSt ⟨stopD47 W VL VR ζ s t p, hgY⟩)
    simp only [mem_inter_iff, mem_ofPred_eq]
    have hiff := mem_PcD47_stopD_iff (s := s) hp hg ht't'
    have hcap : capClock (qgCurve W s E p) t' = capClock (gammaD47 s (stopD47 W VL VR ζ s t p)) t' :=
      WangWu.capClock_congr fun u hu => (gammaD47_stopD hp hg (hu.2.trans ht't')).symm
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hiff.2 h1
      refine ⟨h1', ?_⟩
      rw [indicator_of_mem (show (⟨stopD47 W VL VR ζ s t p, hgY⟩ : {y : Y47 nL nR // IsGoodD47 s t y}) ∈
        {x : {y : Y47 nL nR // IsGoodD47 s t y} | (t' : ℝ) ∈ PcD47 s x.1} from h1'), ← hcap]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨hiff.1 h1, ?_⟩
      rw [indicator_of_mem (show (⟨stopD47 W VL VR ζ s t p, hgY⟩ : {y : Y47 nL nR // IsGoodD47 s t y}) ∈
        {x : {y : Y47 nL nR // IsGoodD47 s t y} | (t' : ℝ) ∈ PcD47 s x.1} from h1), ← hcap] at h2
      exact h2
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
  by_cases hS : (t' : ℝ) ∈ qgPre W VL VR ζ s E p ∧ (r : ℝ) < capClock (qgCurve W s E p) t'
  · rw [← hAC p hp hS.1 hS.2]
    exact ⟨fun h => ⟨h.1, hS⟩, fun h => ⟨h.1, hStiff.1 hS⟩⟩
  · exact ⟨fun h => absurd (hStiff.2 h.2) hS, fun h => absurd h.2 hS⟩

/-- **The validity event is known from the two stopped histories** (second marks fact). -/
theorem marks47_avoid (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hgood : ∀ᵐ p ∂μ, p ∈ E)
    (φ : TestOn upperHalfPlaneOpens) :
    ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ s (t : ℝ).toNNReal] B' ∧
      B' =ᵐ[μ] qAv W VL VR ζ s E φ (t : ℝ).toNNReal := by
  have ht0 : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
  have htt : (((t : ℝ).toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht0
  obtain ⟨CPc, hCPc, hPc⟩ := exists_measurableSet_of_subtypeD47
    (measurableSet_mem_PcD47 (nL := nL) (nR := nR) (s := s) (t := t) t ht0 le_rfl)
  refine ⟨stopD47 W VL VR ζ s t ⁻¹' (CPc ∩ AvD47 s t φ), measurable_stopD47 s t (hCPc.inter (measurableSet_AvD47 φ)),
    ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hgood] with p hp
  have hg := hEg p hp
  have hgY := isGoodD47_stopD (s := s) ht hEg hp
  have hiff := mem_PcD47_stopD_iff (s := s) (t := t) hp hg (le_refl (t : ℝ))
  have hC : stopD47 W VL VR ζ s t p ∈ CPc ↔ (t : ℝ) ∈ PcD47 s (stopD47 W VL VR ζ s t p) :=
    (hPc ⟨stopD47 W VL VR ζ s t p, hgY⟩).symm
  simp only [mem_preimage, mem_inter_iff, qAv, mem_ofPred_eq, htt, hC]
  by_cases htP : (t : ℝ) ∈ qgPre W VL VR ζ s E p
  · have htP' : (((t : ℝ).toNNReal : ℝ≥0) : ℝ) ∈ qgPre W VL VR ζ s E p := by rwa [htt]
    have hav := isChartAvoid_capClock_iff47 hEg hp htP' φ
    rw [htt] at hav
    rw [hav, mem_AvD47_stopD_iff]
    exact ⟨fun h => ⟨hp, htP, h.2⟩, fun h => ⟨hiff.2 htP, h.2.2⟩⟩
  · exact ⟨fun h => absurd (hiff.1 h.1) htP, fun h => absurd h.2.1 htP⟩

end Marks

/-! ### The martingale clause and the word entrance of the counterflow's image word -/

section Final

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The martingale clause of the counterflow's killed image word** (item D3, PROVE-CFRESTART4's hypothesis `hmart`),
given that almost every glued sample is good. -/
theorem isLocalMartingaleBefore_q_of_good (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      IsGood47 W VL VR ζ p) {s : ℝ≥0} (hs : 0 < s) :
    ∀ z ∈ H, IsLocalMartingaleBefore (qFilt (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s
        (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
      (fun p => min (QuantumZipper.swallowTime (wpath (qW W VL VR ζ s (glueGood47 (glueMeasure P k
          (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ)) p) z : WithTop ℝ≥0)
        (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p))
      (coupProc (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
        (qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
        (qVL (qxL κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
        (qVR (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ)) z) :=
  isLocalMartingaleBefore_q hκ hκ4 hF h44 hC hcf hlaw k hk hae hs
    (fun r _ _ ht'0 ht't ht _ hA => marks47_inter _ _ ht isGood47_of_mem_glueGood47 (ae_mem_glueGood47 hae) r
      ht'0 ht't hA)
    (fun _ ht φ => marks47_avoid ht isGood47_of_mem_glueGood47 (ae_mem_glueGood47 hae) φ)

/-- **The word entrance of the counterflow's killed image word** (items D3 + D4): on `μ ⊗ P₀` there is a Brownian
motion of the product filtration driving, almost surely, the integrated `SLE_{16/κ}(ρ′)` equations of the killed image
word on `[0, qT)` (weights `iwL`, `iwR`), given that almost every glued sample is good. -/
theorem exists_isWordEntrance_q (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hae : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      IsGood47 W VL VR ζ p) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration (qFilt (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR) W VL VR ζ s
        (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ))
        𝓦) Bi ((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀) ∧
      (∀ p, Continuous fun t => Bi t p) ∧
      ∀ᵐ p ∂((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀),
        Sec7.Aux117.IsWordEntrance (16 / κ)
          (fun i => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) i 0 p.1)
          (fun j => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) j 0 p.1)
          (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
          (fun t => qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) t p.1)
          (fun i t => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) i t p.1)
          (fun j t => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) j t p.1) (fun t => Bi t p)
          (qT W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p.1 : ℝ≥0∞) := by
  have hxo := isOrderedForceWord_qx κ ρL ρR xL xR
  exact exists_isWordEntrance_of_mart47 hC.2.2.2.1 hxo.2.1 hxo.1 hxo.2.2.2 hxo.2.2.1 hs hae (by positivity)
    (isLocalMartingaleBefore_q_of_good hκ hκ4 hF h44 hC hcf hlaw k hk hae hs)

end Final

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
