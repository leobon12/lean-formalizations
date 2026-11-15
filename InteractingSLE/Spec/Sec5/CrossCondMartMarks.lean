/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondMartMarksY

/-!
# The image word before a forward time is known from the two stopped histories: `ImgMarks49Statement` (general `κ`)

Packet PROVE-GLUECOND7 (Astra's E.2 and E.6; the general-`κ` form of PROVE-WW-B19's `ImgChartConstMarks`). On good
glued samples (`p ∈ E` with a good flow path), every event of the raw image filtration `imgRaw r`, intersected with
`{t' before contact, r < σ(t')}` (`t' ≤ t` rational), is the preimage under the stopped-data map `stopD t s` of a Borel
set of stopped data, and so is the forward validity event `cfAv φ t`. Since `stopD t s` is measurable for the marks
`cfGlueMarks t s` and the good samples have full measure, this is `ImgMarks49Statement`.

* `AvD`, `measurableSet_AvD`: the support-avoidance event read from stopped data (the flow line through rational times,
  the filled obstacle through the hitting σ-algebra);
* **`isGoodD_stopD`**: stopped data of good samples are good;
* `mem_AvD_iff`, `cfChart_inv_image_eq'`, `isChartAvoid_capClock_iff'`;
* `img_eq_stopD`, `isAway_iff_isAwayD`, `imgAnn_le_iff'`;
* **`exists_measurableSet_stopD_iff`** (the Galmarino-type transfer), `exists_marks_ae_eq_inter`,
  `exists_marks_ae_eq_avoid`, **`imgMarks49Statement`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q
open ImgDrv MartChar
open Sec7.Lemma71C (capClock)
open LocalSets

namespace Word49

/-! ### The support-avoidance event read from stopped data -/

section Av

variable {nL nR : ℕ} {s : ℝ≥0} {t : ℚ}

/-- **The support-avoidance event read from stopped data**: `supp φ ⊆ ℍ`, the flow line on `[0, t]` stays uniformly
away from `supp φ` at rational times, and the obstacle misses `supp φ`. -/
def AvD (s : ℝ≥0) (t : ℚ) (φ : TestOn upperHalfPlaneOpens) : Set (Y49 nL nR) :=
  {y | tsupport φ ⊆ H ∧ (∃ m : ℕ, ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ t →
      ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (alphaD y u) (tsupport φ)) ∧ Disjoint (tsupport φ) (GD s y)}

theorem measurableSet_disjoint_GD (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet {y : Y49 nL nR | Disjoint (tsupport φ) (GD s y)} := by
  have e : {y : Y49 nL nR | Disjoint (tsupport φ) (GD s y)} =
      GD s ⁻¹' {S : Set ℂ | Disjoint (tsupport φ) (relClosureH S)} := by
    ext y
    obtain ⟨hsub, hopen⟩ := cfHullQ_relClosed s y.2
    simp only [mem_ofPred_eq, mem_preimage, GD, relClosureH_eq hsub hopen]
  rw [e]
  exact measurable_GD s (measurableSet_disjoint_relClosureH φ.hasCompactSupport.isCompact φ.tsupport_subset)

theorem measurableSet_AvD (φ : TestOn upperHalfPlaneOpens) : MeasurableSet (AvD (nL := nL) (nR := nR) s t φ) := by
  have e : AvD (nL := nL) (nR := nR) s t φ = {_y | tsupport φ ⊆ H} ∩ ((⋃ m : ℕ, ⋂ u : ℚ,
      {y : Y49 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ t → ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (alphaD y u) (tsupport φ)}) ∩
      {y : Y49 nL nR | Disjoint (tsupport φ) (GD s y)}) := by
    ext y
    simp only [AvD, mem_ofPred_eq, mem_inter_iff, mem_iUnion, mem_iInter]
  rw [e]
  refine (MeasurableSet.const _).inter ((MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u => ?_).inter
    (measurableSet_disjoint_GD φ))
  by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ t
  · simp only [hc.1, hc.2, forall_const]
    exact measurableSet_le measurable_const (continuous_infEDist.measurable.comp (measurable_alphaD u))
  · have e : {y : Y49 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ t →
        ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (alphaD y u) (tsupport φ)} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hc
    rw [e]
    exact MeasurableSet.univ

/-- The support-avoidance event of good stopped data. -/
theorem mem_AvD_iff {y : Y49 nL nR} (hy : IsGoodD s t y) (ht0 : (0 : ℝ) ≤ t) (φ : TestOn upperHalfPlaneOpens) :
    y ∈ AvD s t φ ↔ tsupport φ ⊆ H \ (alphaD y '' Ioc 0 t ∪ GD s y) := by
  have hA := forall_notMem_iff_rat_infEDist (isClosed_tsupport φ) ht0 hy.alphaCont
  rw [AvD, mem_ofPred_eq, ← hA]
  constructor
  · rintro ⟨hKH, hα, hG⟩ z hz
    refine ⟨hKH hz, ?_⟩
    rintro (⟨u, hu, rfl⟩ | hzG)
    · exact hα u (Ioc_subset_Icc_self hu) hz
    · exact Set.disjoint_left.1 hG hz hzG
  · intro h
    refine ⟨fun z hz => (h hz).1, fun u hu hz => ?_, Set.disjoint_left.2 fun z hz hzG => (h hz).2 (Or.inr hzG)⟩
    rcases hu.1.eq_or_lt with h0 | h0
    · have := (h hz).1
      rw [← h0, hy.alpha0] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exact (h hz).2 (Or.inl ⟨u, ⟨h0, hu.2⟩, rfl⟩)

end Av

/-! ### Good samples have good stopped data -/

section Good

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t : ℚ} {p : Ω × HistorySpace 0 0}

theorem isGoodD_stopD (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) : IsGoodD s t (stopD W VL VR ζ t s p) := by
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
  have hgood := hEg p hp
  have hα : IsProperArc (seedLine ζ W p.1) := hgood.1
  have hGc : IsClosed (cfHullQ s p.2) := closed_cfHullQ_of_good hgood
  have hγ := isKilledArc_gCurve hEg p
  refine ⟨isKilledArc_gammaD_stopD ht hEg hp hg, fun q hq0 hqt => ?_, fun q hq0 hqt hq => ?_, ?_, ?_,
    fun u hu => ?_, ?_⟩
  · rw [mem_PcD_stopD_iff hp hg hqt, gPre_of_mem hp, mem_preContact_iff_ball hα.cont hGc hq0]
    simp only [RatD, mem_ofPred_eq]
    refine exists_congr fun m => forall_congr' fun u => imp_congr_right fun _ => imp_congr_right fun huq => ?_
    rw [alphaD_stopD hg (huq.trans hqt), GD_stopD]
  · have hqP := (mem_PcD_stopD_iff hp hg hqt).1 hq
    exact (hγ.cont.mono (hγ.icc _ hqP)).congr fun u hu => gammaD_stopD hp hg (hu.2.trans hqt)
  · exact (hα.cont.mono Icc_subset_Ici_self).congr fun u hu => alphaD_stopD hg hu.2
  · rw [alphaD_stopD hg ht']
    exact hα.zero
  · rw [alphaD_stopD hg hu.2]
    exact hα.mem_H u hu.1
  · rw [GD_stopD]
    exact hGc

/-- The image identification on a good sample before contact, at any real pre-contact time `u`. -/
theorem cfChart_inv_image_eq' (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (hp : p ∈ E) {u : ℝ}
    (huP : u ∈ gPre s ζ W E p) :
    (cfChart s p.2).2.1 '' (H \ fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) u).toNNReal : ℝ≥0) : ℝ)) =
      H \ (seedLine ζ W p.1 '' Ioc 0 u ∪ cfHullQ s p.2) := by
  obtain ⟨hα, -, -, -, hGeq⟩ := hEg p hp
  set Wβ := cfDrv0 s p.2 with hWβdef
  have hWβc : Continuous Wβ := continuous_cfDrv0 s p.2
  have hWβ0 : Wβ 0 = 0 := cfDrv0_zero s p.2
  have hP : gPre s ζ W E p = preContact (seedLine ζ W p.1) (cfHullQ s p.2) := gPre_of_mem hp
  have hγ : gCurve s ζ W E p = imgCurve Wβ s (seedLine ζ W p.1) := gCurve_of_mem hp
  have huP' : u ∈ preContact (seedLine ζ W p.1) (cfHullQ s p.2) := hP ▸ huP
  have hAsub : seedLine ζ W p.1 '' Ioc 0 u ⊆ H \ negInv '' fwdHull Wβ s := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨hα.mem_H v hv.1, ?_⟩
    rw [← hGeq]
    exact huP'.2 v ⟨hv.1.le, hv.2⟩
  have hγimg : gCurve s ζ W E p '' Ioc 0 u = revChart Wβ s '' (seedLine ζ W p.1 '' Ioc 0 u) := by
    rw [hγ, image_image]
    exact image_congr fun v hv => imgCurve_of_pos hv.1
  have hkill : IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := isKilledArc_gCurve hEg p
  have hcap0 : 0 ≤ capClock (gCurve s ζ W E p) u := hkill.capClock_nonneg huP
  have hhull : fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) u).toNNReal : ℝ≥0) : ℝ) = revChart Wβ s '' (seedLine ζ W p.1 '' Ioc 0 u) := by
    rw [Real.coe_toNNReal _ hcap0, ← hγimg]
    exact hkill.fwdHull_eq_of_eqOn_chainDrv (fun S hS r hr => (hkill.kW_eq_chainDrv hS).2 r hr) huP
  rw [cfChart_inv, hhull, revChartInv_image_H_diff_union hWβc hWβ0 s.coe_nonneg hAsub, hGeq]

/-- **The forward validity event in the chart, without the chart** (good sample before contact). -/
theorem isChartAvoid_capClock_iff' (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (hp : p ∈ E) {u : ℝ}
    (huP : u ∈ gPre s ζ W E p) (φ : TestOn upperHalfPlaneOpens) :
    Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W E r p) (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ
        (capClock (gCurve s ζ W E p) u).toNNReal ↔
      tsupport φ ⊆ H \ (seedLine ζ W p.1 '' Ioc 0 u ∪ cfHullQ s p.2) := by
  have hkill : IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := isKilledArc_gCurve hEg p
  unfold Sec7.Lemma71D.IsChartAvoid
  rw [cfChart_inv_image_eq' hEg hp huP]
  exact ⟨fun h => h.2, fun h => ⟨hkill.lt_kLife huP, h⟩⟩

end Good

/-! ### The image word before `t` from the stopped data -/

section Transfer

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t t' : ℚ} {p : Ω × HistorySpace 0 0}

/-- **The killed image word up to the image time `r` is read from the stopped data** (good sample, `t' ≤ t` before
contact with `r < σ(t')`). -/
theorem img_eq_stopD (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (hp : p ∈ E) (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) (ht't : t' ≤ t) (htP : (t' : ℝ) ∈ gPre s ζ W E p)
    {r : ℝ≥0} (hrc : (r : ℝ) < capClock (gCurve s ζ W E p) t') {r' : ℝ≥0} (hr' : r' ≤ r) :
    (r' : WithTop ℝ≥0) < kLife (gammaD s (stopD W VL VR ζ t s p)) (PD t s (stopD W VL VR ζ t s p)) ∧
      (r' : WithTop ℝ≥0) < imgT s ζ W E p ∧
      imgW s ζ W E r' p = kW (gammaD s (stopD W VL VR ζ t s p)) (PD t s (stopD W VL VR ζ t s p)) r' ∧
      (∀ i, imgVL xL s ζ W E i r' p = kVL (gammaD s (stopD W VL VR ζ t s p)) (PD t s (stopD W VL VR ζ t s p))
        (gXLD xL s (stopD W VL VR ζ t s p)) i r') ∧
      ∀ j, imgVR xR s ζ W E j r' p = kVR (gammaD s (stopD W VL VR ζ t s p)) (PD t s (stopD W VL VR ζ t s p))
        (gXRD xR s (stopD W VL VR ζ t s p)) j r' := by
  have hγ := isKilledArc_gCurve hEg p
  have hγx := isKilledArc_gammaD_stopD (VL := VL) (VR := VR) ht hEg hp hg
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  obtain ⟨S, hSP, hS0, hSt', hrS⟩ := hγ.exists_lt_capClock_lt htP r.coe_nonneg hrc
  have hSx : S ∈ PD t s (stopD W VL VR ζ t s p) := by
    rw [PD_stopD hp hg]
    exact ⟨hSP, lt_of_lt_of_le hSt' ht't'⟩
  have hEq : EqOn (gCurve s ζ W E p) (gammaD s (stopD W VL VR ζ t s p)) (Icc 0 S) := fun u hu =>
    (gammaD_stopD hp hg (hu.2.trans (hSt'.le.trans ht't'))).symm
  have hcS := capClock_congr hEq
  have hr'S : (r' : ℝ) ≤ capClock (gCurve s ζ W E p) S := (by exact_mod_cast hr' : (r' : ℝ) ≤ r).trans hrS.le
  have hle : ∀ {γ₀ : ℝ → ℂ}, (r' : ℝ) ≤ capClock γ₀ S →
      (r' : WithTop ℝ≥0) ≤ (((capClock γ₀ S).toNNReal : ℝ≥0) : WithTop ℝ≥0) := fun h =>
    WithTop.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le ((NNReal.coe_nonneg _).trans h)).2 h)
  refine ⟨lt_of_le_of_lt (hle (hcS ▸ hr'S)) (hγx.lt_kLife hSx), lt_of_le_of_lt (hle hr'S) (hγ.lt_kLife hSP),
    kW_eq_of_eqOn hγ hγx hSP hSx hS0 hEq hr'S, fun i => ?_, fun j => ?_⟩
  · show kVL _ _ (gXL xL s E p) i r' = _
    rw [← gXLD_stopD (VL := VL) (VR := VR) (W := W) (ζ := ζ) (t := t) xL hp]
    exact kVL_eq_of_eqOn hγ hγx hSP hSx hS0 hEq _ i hr'S
  · show kVR _ _ (gXR xR s E p) j r' = _
    rw [← gXRD_stopD (VL := VL) (VR := VR) (W := W) (ζ := ζ) (t := t) xR hp]
    exact kVR_eq_of_eqOn hγ hγx hSP hSx hS0 hEq _ j hr'S

theorem isAway_iff_isAwayD (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {n : ℕ} {q : ℚ} (hqt : (q : ℝ) ≤ t) :
    IsAway s ζ W n p q ↔ IsAwayD s n (stopD W VL VR ζ t s p) q := by
  simp only [IsAway, IsAwayD]
  refine and_congr_right fun _ => forall_congr' fun u => imp_congr_right fun _ => imp_congr_right fun huq => ?_
  rw [alphaD_stopD hg (huq.trans hqt), GD_stopD]

/-- The announcing events on `{t' before contact, r < σ(t')}`. -/
theorem imgAnn_le_iff' (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (hp : p ∈ E) (ht'0 : (0 : ℝ) ≤ t')
    {r : ℝ≥0} (hrc : (r : ℝ) < capClock (gCurve s ζ W E p) t') {r' : ℝ≥0} (hr' : r' ≤ r) (n : ℕ) :
    imgAnn s ζ W E n p ≤ r' ↔ (∀ q : ℚ, (q : ℝ) < t' → IsAway s ζ W n p q →
      capClock (gCurve s ζ W E p) q ≤ r') ∧ ¬ IsAway s ζ W n p t' := by
  classical
  have hr'r : (r' : ℝ) ≤ r := by exact_mod_cast hr'
  simp only [imgAnn, hp, ↓reduceIte]
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
    by_cases ha : IsAway s ζ W n p q
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
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

omit mΩ in
theorem exists_measurableSet_of_subtypeD {S : Set {y : Y49 nL nR // IsGoodD s t y}} (hS : MeasurableSet S) :
    ∃ C : Set (Y49 nL nR), MeasurableSet C ∧ ∀ x : {y : Y49 nL nR // IsGoodD s t y}, x ∈ S ↔ x.1 ∈ C := by
  obtain ⟨C, hC, rfl⟩ := hS
  exact ⟨C, hC, fun x => Iff.rfl⟩

/-- **The Galmarino-type transfer**: on the good samples with `t'` before contact and `r < σ(t')`, every event of the
raw image filtration `imgRaw r` is the preimage of a Borel set of stopped data (`t' ≤ t`). -/
theorem exists_measurableSet_stopD_iff (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (ht'0 : (0 : ℝ) ≤ t')
    (ht't : t' ≤ t) (r : ℝ≥0) {A : Set (Ω × HistorySpace 0 0)}
    (hA : MeasurableSet[imgRaw xL xR s ζ W E r] A) :
    ∃ C : Set (Y49 nL nR), MeasurableSet C ∧ ∀ p, p ∈ E → Aux50Hit.IsGoodPath W VL VR ζ p.1 →
      (t' : ℝ) ∈ gPre s ζ W E p → (r : ℝ) < capClock (gCurve s ζ W E p) t' →
      (p ∈ A ↔ stopD W VL VR ζ t s p ∈ C) := by
  classical
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  have hA' : MeasurableSet[MeasurableSpace.generateFrom (imgGen xL xR s ζ W E r)] A :=
    (MeasurableSpace.measurableSet_inf.1 hA).1
  have hx : ∀ p : Ω × HistorySpace 0 0, p ∈ E → Aux50Hit.IsGoodPath W VL VR ζ p.1 →
      IsGoodD s t (stopD W VL VR ζ t s p) := fun p hp hg => isGoodD_stopD ht hEg hp hg
  refine MeasurableSpace.generateFrom_induction (imgGen xL xR s ζ W E r)
    (fun A _ => ∃ C : Set (Y49 nL nR), MeasurableSet C ∧
      ∀ p, p ∈ E → Aux50Hit.IsGoodPath W VL VR ζ p.1 → (t' : ℝ) ∈ gPre s ζ W E p →
        (r : ℝ) < capClock (gCurve s ζ W E p) t' → (p ∈ A ↔ stopD W VL VR ζ t s p ∈ C)) ?_ ?_ ?_ ?_ A hA'
  · rintro A ⟨r', hr', hcase⟩ -
    rcases hcase with ⟨B, hB, hWc | ⟨i, hVLc⟩ | ⟨j, hVRc⟩⟩ | hTc | ⟨n, hAnn⟩ | ⟨B, hB, hRev⟩
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD
        ((measurableSet_lt_kLife_gammaD (s := s) (t := t) r').inter (measurable_indicator_kW_gammaD r' hB))
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      obtain ⟨hlt, -, hW', -, -⟩ := img_eq_stopD (VL := VL) (VR := VR) xL xR ht hEg hp hg ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopD W VL VR ζ t s p, hx p hp hg⟩)
      rw [hWc]
      simp only [mem_inter_iff, mem_preimage]
      rw [indicator_of_mem (show (⟨stopD W VL VR ζ t s p, hx p hp hg⟩ : {y : Y49 nL nR // IsGoodD s t y}) ∈
        {x : {y : Y49 nL nR // IsGoodD s t y} | (r' : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}
          from hlt), ← hW']
      exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD
        ((measurableSet_lt_kLife_gammaD (s := s) (t := t) r').inter (measurable_indicator_kVL_gammaD xL i r' hB))
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      obtain ⟨hlt, -, -, hVL', -⟩ := img_eq_stopD (VL := VL) (VR := VR) xL xR ht hEg hp hg ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopD W VL VR ζ t s p, hx p hp hg⟩)
      rw [hVLc]
      simp only [mem_inter_iff, mem_preimage]
      rw [indicator_of_mem (show (⟨stopD W VL VR ζ t s p, hx p hp hg⟩ : {y : Y49 nL nR // IsGoodD s t y}) ∈
        {x : {y : Y49 nL nR // IsGoodD s t y} | (r' : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}
          from hlt), ← hVL' i]
      exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD
        ((measurableSet_lt_kLife_gammaD (s := s) (t := t) r').inter (measurable_indicator_kVR_gammaD xR j r' hB))
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      obtain ⟨hlt, -, -, -, hVR'⟩ := img_eq_stopD (VL := VL) (VR := VR) xL xR ht hEg hp hg ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopD W VL VR ζ t s p, hx p hp hg⟩)
      rw [hVRc]
      simp only [mem_inter_iff, mem_preimage]
      rw [indicator_of_mem (show (⟨stopD W VL VR ζ t s p, hx p hp hg⟩ : {y : Y49 nL nR // IsGoodD s t y}) ∈
        {x : {y : Y49 nL nR // IsGoodD s t y} | (r' : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}
          from hlt), ← hVR' j]
      exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩
    · refine ⟨univ, MeasurableSet.univ, fun p hp hg htP hrc => ?_⟩
      obtain ⟨-, hT, -⟩ := img_eq_stopD (VL := VL) (VR := VR) xL xR ht hEg hp hg ht't htP hrc hr'
      rw [hTc]
      exact ⟨fun _ => mem_univ _, fun _ => hT⟩
    · set S : Set {y : Y49 nL nR // IsGoodD s t y} := (⋂ q : ℚ, {x : {y : Y49 nL nR // IsGoodD s t y} |
          (q : ℝ) < t' → IsAwayD s n x.1 q → ({x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1}.indicator
            (fun x => capClock (gammaD s x.1) q) x) ≤ r'}) ∩
          {x : {y : Y49 nL nR // IsGoodD s t y} | ¬ IsAwayD s n x.1 t'} with hSdef
      have hSm : MeasurableSet S := by
        refine (MeasurableSet.iInter fun q => ?_).inter (measurable_subtype_coe (measurableSet_isAwayD n t')).compl
        by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t'
        · have e : {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) < t' → IsAwayD s n x.1 q →
              ({x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1}.indicator
                (fun x => capClock (gammaD s x.1) q) x) ≤ r'} =
              (Subtype.val ⁻¹' {y : Y49 nL nR | IsAwayD s n y q})ᶜ ∪
                {x | ({x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1}.indicator
                  (fun x => capClock (gammaD s x.1) q) x) ≤ r'} := by
            ext x
            simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, hq.2, true_imp_iff]
            tauto
          rw [e]
          exact (measurable_subtype_coe (measurableSet_isAwayD n q)).compl.union
            (measurableSet_le (measurable_indicator_capClock_gammaD q hq.1 (hq.2.le.trans ht't'))
              measurable_const)
        · have e : {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) < t' → IsAwayD s n x.1 q →
              ({x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1}.indicator
                (fun x => capClock (gammaD s x.1) q) x) ≤ r'} = univ := by
            ext x
            simp only [mem_ofPred_eq, mem_univ, iff_true]
            intro h1 h2
            exact absurd ⟨h2.1.1, h1⟩ hq
          rw [e]
          exact MeasurableSet.univ
      obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtypeD hSm
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      refine Iff.trans ?_ (hCS ⟨stopD W VL VR ζ t s p, hx p hp hg⟩)
      rw [hAnn]
      show imgAnn s ζ W E n p ≤ r' ↔ _
      rw [imgAnn_le_iff' hEg hp ht'0 hrc hr' n]
      have hcap : ∀ q : ℚ, (q : ℝ) ≤ t → capClock (gCurve s ζ W E p) q =
          capClock (gammaD s (stopD W VL VR ζ t s p)) q := fun q hqt =>
        capClock_congr fun u hu => (gammaD_stopD hp hg (hu.2.trans hqt)).symm
      have hind : ∀ q : ℚ, (q : ℝ) < t' → IsAwayD s n (stopD W VL VR ζ t s p) q →
          ({x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1}.indicator
            (fun x => capClock (gammaD s x.1) q)
            (⟨stopD W VL VR ζ t s p, hx p hp hg⟩ : {y : Y49 nL nR // IsGoodD s t y})) =
            capClock (gCurve s ζ W E p) q := fun q hq ha => by
        have hPc : (q : ℝ) ∈ PcD s (stopD W VL VR ζ t s p) :=
          ((hx p hp hg).rat q ha.1.1 (hq.le.trans ht't')).2 ⟨n, ha.2⟩
        rw [indicator_of_mem (show (⟨stopD W VL VR ζ t s p, hx p hp hg⟩ : {y : Y49 nL nR // IsGoodD s t y}) ∈
          {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1} from hPc), hcap q (hq.le.trans ht't')]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨mem_iInter.2 fun q hq ha => ?_, fun ha => h2 ((isAway_iff_isAwayD hg ht't').2 ha)⟩
        rw [hind q hq ha]
        exact h1 q hq ((isAway_iff_isAwayD hg (hq.le.trans ht't')).2 ha)
      · rintro ⟨h1, h2⟩
        refine ⟨fun q hq ha => ?_, fun ha => h2 ((isAway_iff_isAwayD hg ht't').1 ha)⟩
        have haY := (isAway_iff_isAwayD hg (hq.le.trans ht't')).1 ha
        have h := mem_iInter.1 h1 q hq haY
        rwa [hind q hq haY] at h
    · refine ⟨Prod.snd ⁻¹' B, measurable_snd hB, fun p _ _ _ _ => ?_⟩
      rw [hRev]
      rfl
  · exact ⟨∅, MeasurableSet.empty, fun p _ _ _ _ => Iff.rfl⟩
  · rintro A _ ⟨C, hC, hAC⟩
    exact ⟨Cᶜ, hC.compl, fun p hp hg htP hrc => not_congr (hAC p hp hg htP hrc)⟩
  · intro f _ hf
    choose C hC hfC using hf
    refine ⟨⋃ i, C i, MeasurableSet.iUnion hC, fun p hp hg htP hrc => ?_⟩
    simp only [mem_iUnion]
    exact exists_congr fun i => hfC i p hp hg htP hrc

end Class

/-! ### `ImgMarks49Statement` -/

section Marks

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {E : Set (Ω × HistorySpace 0 0)} {s : ℝ≥0} {t t' : ℚ}
  {μ : Measure (Ω × HistorySpace 0 0)}

/-- First component of `ImgMarks49Statement`, for any measure under which the good samples have full measure. -/
theorem exists_marks_ae_eq_inter (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ht : 0 < t)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (hgood : ∀ᵐ p ∂μ, p ∈ E ∧ Aux50Hit.IsGoodPath W VL VR ζ p.1) (r : ℝ≥0)
    (ht'0 : (0 : ℝ) ≤ t') (ht't : t' ≤ t) {A : Set (Ω × HistorySpace 0 0)}
    (hA : MeasurableSet[imgRaw xL xR s ζ W E r] A) :
    ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧ B' =ᵐ[μ]
      A ∩ {p | (t' : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) t'} := by
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  obtain ⟨C, hC, hAC⟩ := exists_measurableSet_stopD_iff (VL := VL) (VR := VR) ht hEg ht'0 ht't r hA
  obtain ⟨CSt, hCSt, hSt⟩ := exists_measurableSet_of_subtypeD
    ((measurableSet_mem_PcD (nL := nL) (nR := nR) (s := s) (t := t) t' ht'0 ht't').inter
      (measurableSet_lt measurable_const (measurable_indicator_capClock_gammaD t' ht'0 ht't')))
  refine ⟨stopD W VL VR ζ t s ⁻¹' (C ∩ CSt), measurable_stopD t s (hC.inter hCSt), ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hgood] with p ⟨hp, hg⟩
  have hgY := isGoodD_stopD (VL := VL) (VR := VR) ht hEg hp hg
  have hStiff : ((t' : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) t') ↔
      stopD W VL VR ζ t s p ∈ CSt := by
    refine Iff.trans ?_ (hSt ⟨stopD W VL VR ζ t s p, hgY⟩)
    simp only [mem_inter_iff, mem_ofPred_eq]
    have hiff := mem_PcD_stopD_iff (VL := VL) (VR := VR) (s := s) hp hg ht't'
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hiff.2 h1
      refine ⟨h1', ?_⟩
      rw [indicator_of_mem (show (⟨stopD W VL VR ζ t s p, hgY⟩ : {y : Y49 nL nR // IsGoodD s t y}) ∈
        {x : {y : Y49 nL nR // IsGoodD s t y} | (t' : ℝ) ∈ PcD s x.1} from h1'),
        ← capClock_congr fun u hu => (gammaD_stopD hp hg (hu.2.trans ht't')).symm]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨hiff.1 h1, ?_⟩
      rw [indicator_of_mem (show (⟨stopD W VL VR ζ t s p, hgY⟩ : {y : Y49 nL nR // IsGoodD s t y}) ∈
        {x : {y : Y49 nL nR // IsGoodD s t y} | (t' : ℝ) ∈ PcD s x.1} from h1),
        ← capClock_congr fun u hu => (gammaD_stopD hp hg (hu.2.trans ht't')).symm] at h2
      exact h2
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
  by_cases hS : (t' : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) t'
  · rw [← hAC p hp hg hS.1 hS.2]
    exact ⟨fun h => ⟨h.1, hS⟩, fun h => ⟨h.1, hStiff.1 hS⟩⟩
  · exact ⟨fun h => absurd (hStiff.2 h.2) hS, fun h => absurd h.2 hS⟩

/-- Second component of `ImgMarks49Statement`. -/
theorem exists_marks_ae_eq_avoid (ht : 0 < t) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (hgood : ∀ᵐ p ∂μ, p ∈ E ∧ Aux50Hit.IsGoodPath W VL VR ζ p.1) (φ : TestOn upperHalfPlaneOpens) :
    ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧ B' =ᵐ[μ] cfAv s ζ W E φ (t : ℝ).toNNReal := by
  have ht0 : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
  have htt : (((t : ℝ).toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht0
  obtain ⟨CPc, hCPc, hPc⟩ := exists_measurableSet_of_subtypeD
    (measurableSet_mem_PcD (nL := nL) (nR := nR) (s := s) (t := t) t ht0 le_rfl)
  refine ⟨stopD W VL VR ζ t s ⁻¹' (CPc ∩ AvD s t φ), measurable_stopD t s (hCPc.inter (measurableSet_AvD φ)), ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hgood] with p ⟨hp, hg⟩
  have hgY := isGoodD_stopD (VL := VL) (VR := VR) ht hEg hp hg
  have hiff := mem_PcD_stopD_iff (VL := VL) (VR := VR) (t := t) (s := s) hp hg (le_refl (t : ℝ))
  have hC : stopD W VL VR ζ t s p ∈ CPc ↔ (t : ℝ) ∈ PcD s (stopD W VL VR ζ t s p) :=
    (hPc ⟨stopD W VL VR ζ t s p, hgY⟩).symm
  simp only [mem_preimage, mem_inter_iff, cfAv, mem_ofPred_eq, htt, hC]
  by_cases htP : (t : ℝ) ∈ gPre s ζ W E p
  · have hav := isChartAvoid_capClock_iff' hEg hp htP φ
    have hA : seedLine ζ W p.1 '' Ioc 0 t = alphaD (stopD W VL VR ζ t s p) '' Ioc 0 t :=
      image_congr fun u hu => (alphaD_stopD hg hu.2).symm
    rw [hA, ← GD_stopD (VL := VL) (VR := VR) (t := t), ← mem_AvD_iff hgY ht0 φ] at hav
    rw [hav]
    exact ⟨fun h => ⟨hp, htP, h.2⟩, fun h => ⟨hiff.2 htP, h.2.2⟩⟩
  · exact ⟨fun h => absurd (hiff.1 h.1) htP, fun h => absurd h.2.1 htP⟩

end Marks

/-- **`ImgMarks49Statement` holds.** -/
theorem imgMarks49Statement : ImgMarks49Statement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  have hEg : ∀ p ∈ glueGood μ s ζ W, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := (ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC).mono fun ω hω => hω.1
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hgood : ∀ᵐ p ∂μ, p ∈ glueGood μ s ζ W ∧ Aux50Hit.IsGoodPath W VL VR ζ p.1 := by
    filter_upwards [ae_mem_glueGood hae, ae_glue_fst (μ := P) k hXm (Aux50Hit.ae_isGoodPath hC.1 hζ)]
      with p h1 h2
    exact ⟨h1, h2⟩
  refine ⟨fun r t' t ht'0 ht't ht A hA => ?_, fun t ht φ => ?_⟩
  · exact exists_marks_ae_eq_inter xL xR ht hEg hgood r ht'0 ht't hA
  · exact exists_marks_ae_eq_avoid ht hEg hgood φ

/-- **The chart clause at fixed image times from the mean identification alone** (any junction weights). -/
theorem imgChartConst49Statement_of_ident {cL cR : ℝ → ℝ → ℝ} (hMI : MeanIdent49Statement.{u} cL cR) :
    ImgChartConst49Statement.{u} cL cR :=
  imgChartConst49Statement_of_ident_marks hMI imgMarks49Statement

/-- **The corrected martingale clause of the image word (junction weights `cL6`, `cR6`) from the mean identification
alone.** -/
theorem imageWord49FiltCStatement_of_ident (hMI : MeanIdent49Statement.{u} cL6 cR6) :
    ImageWord49FiltCStatement.{u} :=
  imageWord49FiltCStatement_of_ident_marks hMI imgMarks49Statement

end Word49

end InteractingSLE.Sec5.CrossCond
