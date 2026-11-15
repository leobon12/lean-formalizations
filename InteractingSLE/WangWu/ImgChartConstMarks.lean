/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConstMarksY

/-!
# The image word before a forward time is known from the two stopped histories: `ImgMarksStatement`

Packet PROVE-WW-B19 (Astra's follow-up note, E.2 and E.6: "R and a mapped stopped prefix recover its original
geometric prefix ... The capacity clock is adapted to σ(R, γ[0,t])"). On the good glued samples (`p ∈ E` with a good
forward path), every event of the raw image filtration `imgRaw r`, intersected with `{t' before contact, r < σ(t')}`
(`t' ≤ t`), is the preimage under the stopped data map `stopData t s` of a Borel set of stopped data, and so is the
forward validity event at `t`. Since `stopData t s` is measurable for the marks `twoSlitMarks t s` and the good set
has full measure, this is `ImgMarksStatement`, hence (`imgChartConstStatement_of_marks`) `ImgChartConstStatement`.

* `forall_notMem_iff_rat_infEDist`, `forall_negInv_notMem_iff_rat_infEDist`: avoidance of a closed/compact set along
  a curve through rational times;
* `AvY`, `measurableSet_AvY`: the support-avoidance event read from stopped data;
* **`isGoodY_stopData`**: stopped data of good samples are good;
* **`exists_measurableSet_stopData_iff`**: the Galmarino-type transfer for `imgRaw r` on `{t' before contact,
  r < σ(t')}`;
* **`imgMarksStatement`**, **`imgChartConstStatement`**, **`reverseTipContactStatement`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open Sec7.Lemma71C ImgWord LawUnique Sec4 ChartConst MartChar.RealFlow WholeField LocalSets Coupling

/-! ### Avoidance through rational times -/

section Avoid

/-- A continuous curve on `[0, b]` avoids a closed set iff its rational positions stay uniformly away from it. -/
theorem forall_notMem_iff_rat_infEDist {α : ℝ → ℂ} {K : Set ℂ} (hK : IsClosed K) {b : ℚ} (hb : (0 : ℝ) ≤ b)
    (hα : ContinuousOn α (Icc 0 b)) :
    (∀ u ∈ Icc (0 : ℝ) b, α u ∉ K) ↔
      ∃ m : ℕ, ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ b → ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (α u) K := by
  have hf : ContinuousOn (fun u => infEDist (α u) K) (Icc 0 b) := continuous_infEDist.comp_continuousOn hα
  constructor
  · intro h
    obtain ⟨u₀, hu₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hb) hf
    have hpos : 0 < infEDist (α u₀) K := by
      rw [infEDist_pos_iff_notMem_closure, hK.closure_eq]
      exact h u₀ hu₀
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    refine ⟨m, fun u h0 hb' => ?_⟩
    have h1 : ((m : ℝ≥0∞) + 1)⁻¹ ≤ (m : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    exact h1.trans (hm.le.trans (hmin ⟨h0, hb'⟩))
  · rintro ⟨m, hm⟩ u hu huK
    have hε : (0 : ℝ≥0∞) < ((m : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    have h0 : infEDist (α u) K = 0 := infEDist_zero_of_mem huK
    have hev : ∀ᶠ v in 𝓝[Icc 0 b] u, infEDist (α v) K < ((m : ℝ≥0∞) + 1)⁻¹ :=
      (hf u hu).eventually (Iio_mem_nhds (show infEDist (α u) K < ((m : ℝ≥0∞) + 1)⁻¹ by rw [h0]; exact hε))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨q, hq, hqd⟩ := exists_rat_mem_Icc_near (a := 0) (b := b) (by simpa using hu) hδ
    have hq' : (q : ℝ) ∈ Icc (0 : ℝ) b := by simpa using hq
    have h2 := hball ⟨by rw [mem_ball, Real.dist_eq]; exact hqd, hq'⟩
    exact absurd (hm q hq'.1 hq'.2) (not_le.2 h2)

/-- The reflected slit `R(β((0, s]))` (closed) avoids a compact set iff its rational positions stay uniformly away. -/
theorem forall_negInv_notMem_iff_rat_infEDist {β : ℝ → ℂ} (hβ : IsProperArc β) {s : ℚ} {K : Set ℂ}
    (hK : IsCompact K) (hG : IsClosed (negInv '' (β '' Ioc 0 s))) :
    (∀ v ∈ Ioc (0 : ℝ) s, negInv (β v) ∉ K) ↔
      ∃ m : ℕ, ∀ v : ℚ, (0 : ℝ) < v → (v : ℝ) ≤ s → ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (negInv (β v)) K := by
  constructor
  · intro h
    rcases K.eq_empty_or_nonempty with hK0 | hKne
    · exact ⟨0, fun v _ _ => by rw [hK0, infEDist_empty]; exact le_top⟩
    have hf : ContinuousOn (fun z => infEDist z (negInv '' (β '' Ioc 0 s))) K := continuous_infEDist.continuousOn
    obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hf
    have hpos : 0 < infEDist z₀ (negInv '' (β '' Ioc 0 s)) := by
      rw [infEDist_pos_iff_notMem_closure, hG.closure_eq]
      rintro ⟨_, ⟨v, hv, rfl⟩, e⟩
      exact h v hv (e ▸ hz₀)
    obtain ⟨m, hm⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    refine ⟨m, fun v hv0 hvs => ?_⟩
    have h1 : ((m : ℝ≥0∞) + 1)⁻¹ ≤ (m : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    refine le_infEDist.2 fun z hz => ?_
    have hmem : negInv (β v) ∈ negInv '' (β '' Ioc 0 s) := ⟨β v, ⟨v, ⟨hv0, hvs⟩, rfl⟩, rfl⟩
    have h2 := infEDist_le_edist_of_mem (x := z) hmem
    rw [edist_comm] at h2
    exact h1.trans (hm.le.trans ((hmin hz).trans h2))
  · rintro ⟨m, hm⟩ v hv hvK
    have hε : (0 : ℝ≥0∞) < ((m : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    have h0 : infEDist (negInv (β v)) K = 0 := infEDist_zero_of_mem hvK
    have hβv : β v ≠ 0 := ne_zero_of_mem_H (hβ.mem_H v hv.1)
    have hc : ContinuousWithinAt (fun w => infEDist (negInv (β w)) K) (Ioc 0 s) v :=
      continuous_infEDist.continuousAt.comp_continuousWithinAt ((continuousAt_negInv hβv).comp_continuousWithinAt
        ((hβ.cont v hv.1.le).mono fun _ hx => le_of_lt hx.1))
    have hev : ∀ᶠ w in 𝓝[Ioc 0 s] v, infEDist (negInv (β w)) K < ((m : ℝ≥0∞) + 1)⁻¹ :=
      hc.eventually (Iio_mem_nhds (show infEDist (negInv (β v)) K < ((m : ℝ≥0∞) + 1)⁻¹ by rw [h0]; exact hε))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨q, hq, hqd⟩ := exists_rat_mem_Ioc_near (a := 0) (b := s) (by simpa using hv) hδ
    have hq' : (q : ℝ) ∈ Ioc (0 : ℝ) s := by simpa using hq
    have h2 := hball ⟨by rw [mem_ball, Real.dist_eq]; exact hqd, hq'⟩
    exact absurd (hm q hq'.1 hq'.2) (not_le.2 h2)

end Avoid

/-! ### The support-avoidance event read from stopped data -/

namespace ChartConst

/-- **The support-avoidance event read from stopped data**: `supp φ ⊆ ℍ`, the forward line on `[0, t]` and the
reflected reverse slit stay uniformly away from `supp φ` at rational times. -/
def AvY (s t : ℚ) (φ : TestOn upperHalfPlaneOpens) : Set YSp :=
  {y | tsupport φ ⊆ H ∧ (∃ m : ℕ, ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ t →
      ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (alphaY y u) (tsupport φ)) ∧
    ∃ m : ℕ, ∀ v : ℚ, (0 : ℝ) < v → (v : ℝ) ≤ s →
      ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (negInv (frzLine s y.2 v)) (tsupport φ)}

end ChartConst

theorem measurableSet_AvY (s t : ℚ) (φ : TestOn upperHalfPlaneOpens) : MeasurableSet (AvY s t φ) := by
  have e : AvY s t φ = {_y | tsupport φ ⊆ H} ∩ ((⋃ m : ℕ, ⋂ u : ℚ, {y : YSp | (0 : ℝ) ≤ u → (u : ℝ) ≤ t →
      ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (alphaY y u) (tsupport φ)}) ∩
    ⋃ m : ℕ, ⋂ v : ℚ, {y : YSp | (0 : ℝ) < v → (v : ℝ) ≤ s →
      ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (negInv (frzLine s y.2 v)) (tsupport φ)}) := by
    ext y; simp [AvY]
  rw [e]
  refine (MeasurableSet.const _).inter ((MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u => ?_).inter
    (MeasurableSet.iUnion fun m => MeasurableSet.iInter fun v => ?_))
  · by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ t
    · simp only [hc.1, hc.2, forall_const]
      exact measurableSet_le measurable_const (continuous_infEDist.measurable.comp (measurable_alphaY u))
    · have e : {y : YSp | (0 : ℝ) ≤ u → (u : ℝ) ≤ t →
          ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (alphaY y u) (tsupport φ)} = univ := by
        ext y
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h1 h2
        exact absurd ⟨h1, h2⟩ hc
      rw [e]
      exact MeasurableSet.univ
  · by_cases hc : (0 : ℝ) < v ∧ (v : ℝ) ≤ s
    · simp only [hc.1, hc.2, forall_const]
      exact measurableSet_le measurable_const (continuous_infEDist.measurable.comp
        (measurable_negInv.comp ((measurable_frzLine s v).comp measurable_snd)))
    · have e : {y : YSp | (0 : ℝ) < v → (v : ℝ) ≤ s →
          ((m : ℝ≥0∞) + 1)⁻¹ ≤ infEDist (negInv (frzLine s y.2 v)) (tsupport φ)} = univ := by
        ext y
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        intro h1 h2
        exact absurd ⟨h1, h2⟩ hc
      rw [e]
      exact MeasurableSet.univ

/-! ### Good samples have good stopped data -/

section Good

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : Set (Ω × HistorySpace 1 1)} {s t : ℚ} {p : Ω × HistorySpace 1 1}

theorem isGoodY_stopData (hs : 0 < s) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) : IsGoodY s t (stopData W VL VR ζ t s p) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
  obtain ⟨hG, hβ, hGc⟩ := glueG_eq hs (hEg p hp)
  have hα := (hEg p hp).1
  have hγ := isKilledArc_gCurve hs hEg p
  refine ⟨isKilledArc_gammaY_stopData hs ht hEg hp hg, fun q hq0 hqt => ?_, fun q hq0 hqt hq => ?_,
    ?_, ?_, fun u hu => ?_, ?_, ?_⟩
  · rw [mem_PcY_stopData_iff hs hEg hp hg hqt, gPre_of_mem hp, hG]
    rw [hG] at hGc
    rw [mem_preContact_iff_rat hα hβ hGc hq0 hs']
    simp only [RatY, mem_ofPred_eq]
    refine exists_congr fun m => forall₂_congr fun u v => imp_congr_right fun hu0 => imp_congr_right fun huq => ?_
    rw [alphaY_stopData (s := s) hg (huq.trans hqt)]
    simp only [ChartConst.stopData, frzLine_revStop]
  · have hqP := (mem_PcY_stopData_iff hs hEg hp hg hqt).1 hq
    exact (hγ.cont.mono (hγ.icc _ hqP)).congr fun u hu => gammaY_stopData hs hEg hp hg (hu.2.trans hqt)
  · exact (hα.cont.mono Icc_subset_Ici_self).congr fun u hu => alphaY_stopData hg hu.2
  · rw [alphaY_stopData hg ht']
    exact hα.zero
  · rw [alphaY_stopData hg hu.2]
    exact hα.mem_H u hu.1
  · show IsProperArc (frzLine s (revStop s p.2))
    rw [frzLine_revStop]
    exact hβ
  · rw [GY_stopData hs hEg hp]
    exact hGc

/-- The support-avoidance event of good stopped data. -/
theorem mem_AvY_iff {y : YSp} (hy : IsGoodY s t y) (ht0 : (0 : ℝ) ≤ t) (φ : TestOn upperHalfPlaneOpens) :
    y ∈ AvY s t φ ↔ tsupport φ ⊆ H \ (alphaY y '' Ioc 0 t ∪ GY s y) := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport.isCompact
  have hA := forall_notMem_iff_rat_infEDist (isClosed_tsupport φ) ht0 hy.alphaCont
  have hB := forall_negInv_notMem_iff_rat_infEDist hy.beta hK hy.gClosed
  rw [AvY, mem_ofPred_eq, ← hA, ← hB]
  constructor
  · rintro ⟨hKH, hα, hβ⟩ z hz
    refine ⟨hKH hz, ?_⟩
    rintro (⟨u, hu, rfl⟩ | ⟨_, ⟨v, hv, rfl⟩, rfl⟩)
    · exact hα u (Ioc_subset_Icc_self hu) hz
    · exact hβ v hv hz
  · intro h
    refine ⟨fun z hz => (h hz).1, fun u hu hz => ?_, fun v hv hz => (h hz).2 (Or.inr ⟨_, ⟨v, hv, rfl⟩, rfl⟩)⟩
    rcases hu.1.eq_or_lt with h0 | h0
    · have := (h hz).1
      rw [← h0, hy.alpha0] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exact (h hz).2 (Or.inl ⟨u, ⟨h0, hu.2⟩, rfl⟩)

/-- **The forward validity event in the chart, without the chart** (good sample before contact). -/
theorem isChartAvoid_capClock_iff (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E) {u : ℝ}
    (huP : u ∈ gPre s ζ W E p) (φ : TestOn upperHalfPlaneOpens) :
    Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W E r p) (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ
        (capClock (gCurve s ζ W E p) u).toNNReal ↔
      tsupport φ ⊆ H \ (seedLine ζ W p.1 '' Ioc 0 u ∪ negInv '' histHull s p.2) := by
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  obtain ⟨hα, hβ, -⟩ := hEg p hp
  obtain ⟨hWβc, hWβ0, -, -, hGeq, -, -⟩ := trace_of_mem_betaSet hs hβ
  set A := seedLine ζ W p.1 '' Ioc 0 u with hAdef
  set Wβ := Ito.rpath (frzDrive s p.2) with hWβdef
  have hγ : gCurve s ζ W E p = imgCurve Wβ s (seedLine ζ W p.1) := gCurve_of_mem hp
  have huP' : u ∈ preContact (seedLine ζ W p.1) (negInv '' histHull s p.2) := gPre_of_mem hp ▸ huP
  have hAsub : A ⊆ H \ negInv '' fwdHull Wβ s := by
    rw [← hGeq]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨hα.mem_H v hv.1, huP'.2 v ⟨hv.1.le, hv.2⟩⟩
  have hγimg : gCurve s ζ W E p '' Ioc 0 u = revChart Wβ s '' A := by
    rw [hγ, hAdef, image_image]
    refine image_congr fun v hv => ?_
    simp only [imgCurve, not_le.2 hv.1, ↓reduceIte]
  have hkill : IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := isKilledArc_gCurve hs hEg p
  have hcap0 : 0 ≤ capClock (gCurve s ζ W E p) u := hkill.capClock_nonneg huP
  have hhull : fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) u).toNNReal : ℝ≥0) : ℝ) = revChart Wβ s '' A := by
    rw [Real.coe_toNNReal _ hcap0, ← hγimg]
    exact hkill.fwdHull_eq_of_eqOn_chainDrv (fun S hS r hr => (hkill.kW_eq_chainDrv hS).2 r hr) huP
  have hset : (imgChart s p.2).2.1 '' (H \ fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) u).toNNReal : ℝ≥0) : ℝ)) = H \ (A ∪ negInv '' histHull s p.2) := by
    simp only [imgChart]
    rw [revDrv0_of_mem hs hβ, hhull, revChartInv_image_H_diff hWβc hWβ0 hs' hAsub, hGeq]
  have hlt : (((capClock (gCurve s ζ W E p) u).toNNReal : ℝ≥0) : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) :=
    hkill.lt_kLife huP
  unfold Sec7.Lemma71D.IsChartAvoid
  rw [hset]
  exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩

end Good

/-! ### The image word before `t` from the stopped data -/

section Transfer

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : Set (Ω × HistorySpace 1 1)} {s t t' : ℚ} {p : Ω × HistorySpace 1 1}

/-- **The killed image word up to the image time `r` is read from the stopped data** (good sample, `t' ≤ t` before
contact with `r < σ(t')`). -/
theorem img_eq_stopData (hs : 0 < s) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E)
    (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) (ht't : t' ≤ t) (htP : (t' : ℝ) ∈ gPre s ζ W E p) {r : ℝ≥0}
    (hrc : (r : ℝ) < capClock (gCurve s ζ W E p) t') {r' : ℝ≥0} (hr' : r' ≤ r) :
    (r' : WithTop ℝ≥0) < kLife (gammaY s (stopData W VL VR ζ t s p)) (PY t s (stopData W VL VR ζ t s p)) ∧
      (r' : WithTop ℝ≥0) < imgT s ζ W E p ∧
      imgW s ζ W E r' p = kW (gammaY s (stopData W VL VR ζ t s p)) (PY t s (stopData W VL VR ζ t s p)) r' ∧
      (∀ i, imgVL s ζ W E i r' p = kVL (gammaY s (stopData W VL VR ζ t s p)) (PY t s (stopData W VL VR ζ t s p))
        (gXLY s (stopData W VL VR ζ t s p)) i r') ∧
      ∀ j, imgVR s ζ W E j r' p = kVR (gammaY s (stopData W VL VR ζ t s p)) (PY t s (stopData W VL VR ζ t s p))
        (gXRY s (stopData W VL VR ζ t s p)) j r' := by
  have hγ := isKilledArc_gCurve hs hEg p
  have hγx := isKilledArc_gammaY_stopData (VL := VL) (VR := VR) hs ht hEg hp hg
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  obtain ⟨S, hSP, hS0, hSt', hrS⟩ := hγ.exists_lt_capClock_lt htP r.coe_nonneg hrc
  have hSx : S ∈ PY t s (stopData W VL VR ζ t s p) := by
    rw [PY_stopData hs hEg hp hg]
    exact ⟨hSP, lt_of_lt_of_le hSt' ht't'⟩
  have hEq : EqOn (gCurve s ζ W E p) (gammaY s (stopData W VL VR ζ t s p)) (Icc 0 S) := fun u hu =>
    (gammaY_stopData hs hEg hp hg (hu.2.trans (hSt'.le.trans ht't'))).symm
  have hcS := capClock_congr hEq
  have hr'S : (r' : ℝ) ≤ capClock (gCurve s ζ W E p) S := (by exact_mod_cast hr' : (r' : ℝ) ≤ r).trans hrS.le
  have hle : ∀ {γ₀ : ℝ → ℂ}, (r' : ℝ) ≤ capClock γ₀ S →
      (r' : WithTop ℝ≥0) ≤ (((capClock γ₀ S).toNNReal : ℝ≥0) : WithTop ℝ≥0) := fun h =>
    WithTop.coe_le_coe.2 ((Real.le_toNNReal_iff_coe_le ((NNReal.coe_nonneg _).trans h)).2 h)
  refine ⟨lt_of_le_of_lt (hle (hcS ▸ hr'S)) (hγx.lt_kLife hSx), lt_of_le_of_lt (hle hr'S) (hγ.lt_kLife hSP),
    kW_eq_of_eqOn hγ hγx hSP hSx hS0 hEq hr'S, fun i => ?_, fun j => ?_⟩
  · show kVL _ _ (gXL s E p) i r' = _
    rw [← gXLY_stopData (VL := VL) (VR := VR) (W := W) (ζ := ζ) (t := t) hp]
    exact kVL_eq_of_eqOn hγ hγx hSP hSx hS0 hEq _ i hr'S
  · show kVR _ _ (gXR s E p) j r' = _
    rw [← gXRY_stopData (VL := VL) (VR := VR) (W := W) (ζ := ζ) (t := t) hp]
    exact kVR_eq_of_eqOn hγ hγx hSP hSx hS0 hEq _ j hr'S

theorem isAway_iff_isAwayY (hg : Aux50Hit.IsGoodPath W VL VR ζ p.1) {n : ℕ} {q : ℚ} (hqt : (q : ℝ) ≤ t) :
    IsAway s ζ W n p q ↔ IsAwayY s n (stopData W VL VR ζ t s p) q := by
  simp only [IsAway, IsAwayY]
  refine and_congr_right fun _ => forall₂_congr fun u v => imp_congr_right fun _ => imp_congr_right fun huq => ?_
  rw [alphaY_stopData (s := s) hg (huq.trans hqt)]
  simp only [ChartConst.stopData, frzLine_revStop]

/-- The announcing events on `{t' before contact, r < σ(t')}`. -/
theorem imgAnn_le_iff (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (hp : p ∈ E) (ht'0 : (0 : ℝ) ≤ t')
    {r : ℝ≥0} (hrc : (r : ℝ) < capClock (gCurve s ζ W E p) t') {r' : ℝ≥0}
    (hr' : r' ≤ r) (n : ℕ) :
    imgAnn s ζ W E n p ≤ r' ↔ (∀ q : ℚ, (q : ℝ) < t' → IsAway s ζ W n p q →
      capClock (gCurve s ζ W E p) q ≤ r') ∧ ¬ IsAway s ζ W n p t' := by
  classical
  have hr'r : (r' : ℝ) ≤ r := by exact_mod_cast hr'
  simp only [imgAnn, hp, ↓reduceIte]
  rw [ciSup_le_iff (bddAbove_awayCap hs hEg n hp)]
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
        refine h2 ⟨⟨ht'0, le_trans (not_lt.1 hq) ha.1.2⟩, fun u v h3 h4 h5 h6 => ha.2 u v h3
          (h4.trans (not_lt.1 hq)) h5 h6⟩
    · simp only [awayCap, ha, ↓reduceIte]
      exact zero_le

end Transfer

/-! ### The σ-algebra induction -/

section Class

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : Set (Ω × HistorySpace 1 1)} {s t t' : ℚ}

omit mΩ in
theorem exists_measurableSet_of_subtype {S : Set {y : YSp // IsGoodY s t y}} (hS : MeasurableSet S) :
    ∃ C : Set YSp, MeasurableSet C ∧ ∀ x : {y : YSp // IsGoodY s t y}, x ∈ S ↔ x.1 ∈ C := by
  obtain ⟨C, hC, rfl⟩ := hS
  exact ⟨C, hC, fun x => Iff.rfl⟩

/-- **The Galmarino-type transfer**: on the good samples with `t'` before contact and `r < σ(t')`, every event of the
raw image filtration `imgRaw r` is the preimage of a Borel set of stopped data (`t' ≤ t`). -/
theorem exists_measurableSet_stopData_iff (hs : 0 < s) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    (ht'0 : (0 : ℝ) ≤ t') (ht't : t' ≤ t) (r : ℝ≥0) {A : Set (Ω × HistorySpace 1 1)}
    (hA : MeasurableSet[imgRaw s ζ W E r] A) :
    ∃ C : Set YSp, MeasurableSet C ∧ ∀ p, p ∈ E → Aux50Hit.IsGoodPath W VL VR ζ p.1 →
      (t' : ℝ) ∈ gPre s ζ W E p → (r : ℝ) < capClock (gCurve s ζ W E p) t' →
      (p ∈ A ↔ stopData W VL VR ζ t s p ∈ C) := by
  classical
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  have hA' : MeasurableSet[MeasurableSpace.generateFrom (imgGen s ζ W E r)] A :=
    (MeasurableSpace.measurableSet_inf.1 hA).1
  have hx : ∀ p : Ω × HistorySpace 1 1, p ∈ E → Aux50Hit.IsGoodPath W VL VR ζ p.1 →
      IsGoodY s t (stopData W VL VR ζ t s p) := fun p hp hg => isGoodY_stopData hs ht hEg hp hg
  refine MeasurableSpace.generateFrom_induction (imgGen s ζ W E r) (fun A _ => ∃ C : Set YSp, MeasurableSet C ∧
    ∀ p, p ∈ E → Aux50Hit.IsGoodPath W VL VR ζ p.1 → (t' : ℝ) ∈ gPre s ζ W E p →
      (r : ℝ) < capClock (gCurve s ζ W E p) t' → (p ∈ A ↔ stopData W VL VR ζ t s p ∈ C)) ?_ ?_ ?_ ?_ A hA'
  · rintro A ⟨r', hr', hcase⟩ -
    rcases hcase with ⟨B, hB, hWc | ⟨i, hVLc⟩ | ⟨j, hVRc⟩⟩ | hTc | ⟨n, hAnn⟩ | ⟨B, hB, hRev⟩
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtype
        ((measurableSet_lt_kLife_gammaY (t := t) hs r').inter (measurable_indicator_kW_gammaY hs r' hB))
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      obtain ⟨hlt, -, hW', -, -⟩ := img_eq_stopData (VL := VL) (VR := VR) hs ht hEg hp hg ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopData W VL VR ζ t s p, hx p hp hg⟩)
      rw [hWc]
      simp only [mem_inter_iff, mem_preimage]
      rw [indicator_of_mem (show (⟨stopData W VL VR ζ t s p, hx p hp hg⟩ : {y : YSp // IsGoodY s t y}) ∈
        {x : {y : YSp // IsGoodY s t y} | (r' : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)} from hlt), ← hW']
      exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtype
        ((measurableSet_lt_kLife_gammaY (t := t) hs r').inter (measurable_indicator_kVL_gammaY hs i r' hB))
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      obtain ⟨hlt, -, -, hVL', -⟩ := img_eq_stopData (VL := VL) (VR := VR) hs ht hEg hp hg ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopData W VL VR ζ t s p, hx p hp hg⟩)
      rw [hVLc]
      simp only [mem_inter_iff, mem_preimage]
      rw [indicator_of_mem (show (⟨stopData W VL VR ζ t s p, hx p hp hg⟩ : {y : YSp // IsGoodY s t y}) ∈
        {x : {y : YSp // IsGoodY s t y} | (r' : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)} from hlt),
        ← hVL' i]
      exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩
    · obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtype
        ((measurableSet_lt_kLife_gammaY (t := t) hs r').inter (measurable_indicator_kVR_gammaY hs j r' hB))
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      obtain ⟨hlt, -, -, -, hVR'⟩ := img_eq_stopData (VL := VL) (VR := VR) hs ht hEg hp hg ht't htP hrc hr'
      refine Iff.trans ?_ (hCS ⟨stopData W VL VR ζ t s p, hx p hp hg⟩)
      rw [hVRc]
      simp only [mem_inter_iff, mem_preimage]
      rw [indicator_of_mem (show (⟨stopData W VL VR ζ t s p, hx p hp hg⟩ : {y : YSp // IsGoodY s t y}) ∈
        {x : {y : YSp // IsGoodY s t y} | (r' : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)} from hlt),
        ← hVR' j]
      exact ⟨fun h => ⟨hlt, h⟩, fun h => h.2⟩
    · refine ⟨univ, MeasurableSet.univ, fun p hp hg htP hrc => ?_⟩
      obtain ⟨-, hT, -⟩ := img_eq_stopData (VL := VL) (VR := VR) hs ht hEg hp hg ht't htP hrc hr'
      rw [hTc]
      exact ⟨fun _ => mem_univ _, fun _ => hT⟩
    · set S : Set {y : YSp // IsGoodY s t y} := (⋂ q : ℚ, {x : {y : YSp // IsGoodY s t y} | (q : ℝ) < t' →
          IsAwayY s n x.1 q → ({x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1}.indicator
            (fun x => capClock (gammaY s x.1) q) x) ≤ r'}) ∩
          {x : {y : YSp // IsGoodY s t y} | ¬ IsAwayY s n x.1 t'} with hSdef
      have hSm : MeasurableSet S := by
        refine (MeasurableSet.iInter fun q => ?_).inter (measurable_subtype_coe (measurableSet_isAwayY n t')).compl
        by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t'
        · have e : {x : {y : YSp // IsGoodY s t y} | (q : ℝ) < t' → IsAwayY s n x.1 q →
              ({x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1}.indicator
                (fun x => capClock (gammaY s x.1) q) x) ≤ r'} =
              (Subtype.val ⁻¹' {y : YSp | IsAwayY s n y q})ᶜ ∪
                {x | ({x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1}.indicator
                  (fun x => capClock (gammaY s x.1) q) x) ≤ r'} := by
            ext x
            simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, hq.2, true_imp_iff]
            tauto
          rw [e]
          exact (measurable_subtype_coe (measurableSet_isAwayY n q)).compl.union
            (measurableSet_le (measurable_indicator_capClock_gammaY hs q hq.1 (hq.2.le.trans ht't'))
              measurable_const)
        · have e : {x : {y : YSp // IsGoodY s t y} | (q : ℝ) < t' → IsAwayY s n x.1 q →
              ({x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1}.indicator
                (fun x => capClock (gammaY s x.1) q) x) ≤ r'} = univ := by
            ext x
            simp only [mem_ofPred_eq, mem_univ, iff_true]
            intro h1 h2
            exact absurd ⟨h2.1.1, h1⟩ hq
          rw [e]
          exact MeasurableSet.univ
      obtain ⟨C, hC, hCS⟩ := exists_measurableSet_of_subtype hSm
      refine ⟨C, hC, fun p hp hg htP hrc => ?_⟩
      refine Iff.trans ?_ (hCS ⟨stopData W VL VR ζ t s p, hx p hp hg⟩)
      rw [hAnn]
      show imgAnn s ζ W E n p ≤ r' ↔ _
      rw [imgAnn_le_iff hs hEg hp ht'0 hrc hr' n]
      have hcap : ∀ q : ℚ, (q : ℝ) ≤ t → capClock (gCurve s ζ W E p) q =
          capClock (gammaY s (stopData W VL VR ζ t s p)) q := fun q hqt =>
        capClock_congr fun u hu => (gammaY_stopData hs hEg hp hg (hu.2.trans hqt)).symm
      have hind : ∀ q : ℚ, (q : ℝ) < t' → IsAwayY s n (stopData W VL VR ζ t s p) q →
          ({x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1}.indicator (fun x => capClock (gammaY s x.1) q)
            (⟨stopData W VL VR ζ t s p, hx p hp hg⟩ : {y : YSp // IsGoodY s t y})) =
            capClock (gCurve s ζ W E p) q := fun q hq ha => by
        have hPc : (q : ℝ) ∈ PcY s (stopData W VL VR ζ t s p) :=
          ((hx p hp hg).rat q ha.1.1 (hq.le.trans ht't')).2 ⟨n, ha.2⟩
        rw [indicator_of_mem (show (⟨stopData W VL VR ζ t s p, hx p hp hg⟩ : {y : YSp // IsGoodY s t y}) ∈
          {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1} from hPc), hcap q (hq.le.trans ht't')]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨mem_iInter.2 fun q hq ha => ?_, fun ha => h2 ((isAway_iff_isAwayY hg ht't').2 ha)⟩
        rw [hind q hq ha]
        exact h1 q hq ((isAway_iff_isAwayY hg (hq.le.trans ht't')).2 ha)
      · rintro ⟨h1, h2⟩
        refine ⟨fun q hq ha => ?_, fun ha => h2 ((isAway_iff_isAwayY hg ht't').1 ha)⟩
        have haY := (isAway_iff_isAwayY hg (hq.le.trans ht't')).1 ha
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

/-! ### `ImgMarksStatement` -/

section Marks

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {E : Set (Ω × HistorySpace 1 1)} {s t t' : ℚ} {μ : Measure (Ω × HistorySpace 1 1)}

/-- First component of `ImgMarksStatement`, for any measure under which the good samples have full measure. -/
theorem exists_marks_ae_eq_inter (hs : 0 < s) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    (hgood : ∀ᵐ p ∂μ, p ∈ E ∧ Aux50Hit.IsGoodPath W VL VR ζ p.1) (r : ℝ≥0) (ht'0 : (0 : ℝ) ≤ t')
    (ht't : t' ≤ t) {A : Set (Ω × HistorySpace 1 1)} (hA : MeasurableSet[imgRaw s ζ W E r] A) :
    ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[μ]
      A ∩ {p | (t' : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) t'} := by
  have ht't' : (t' : ℝ) ≤ t := by exact_mod_cast ht't
  obtain ⟨C, hC, hAC⟩ := exists_measurableSet_stopData_iff (VL := VL) (VR := VR) hs ht hEg ht'0 ht't r hA
  obtain ⟨CSt, hCSt, hSt⟩ := exists_measurableSet_of_subtype ((measurableSet_mem_PcY (s := s) t' ht'0 ht't').inter
    (measurableSet_lt measurable_const (measurable_indicator_capClock_gammaY hs t' ht'0 ht't')))
  refine ⟨stopData W VL VR ζ t s ⁻¹' (C ∩ CSt), measurable_stopData t s (hC.inter hCSt), ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hgood] with p ⟨hp, hg⟩
  have hgY := isGoodY_stopData (VL := VL) (VR := VR) hs ht hEg hp hg
  have hStiff : ((t' : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) t') ↔
      stopData W VL VR ζ t s p ∈ CSt := by
    refine Iff.trans ?_ (hSt ⟨stopData W VL VR ζ t s p, hgY⟩)
    simp only [mem_inter_iff, mem_ofPred_eq]
    have hiff := mem_PcY_stopData_iff (VL := VL) (VR := VR) hs hEg hp hg ht't'
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := hiff.2 h1
      refine ⟨h1', ?_⟩
      rw [indicator_of_mem (show (⟨stopData W VL VR ζ t s p, hgY⟩ : {y : YSp // IsGoodY s t y}) ∈
        {x : {y : YSp // IsGoodY s t y} | (t' : ℝ) ∈ PcY s x.1} from h1'),
        ← capClock_congr fun u hu => (gammaY_stopData hs hEg hp hg (hu.2.trans ht't')).symm]
      exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨hiff.1 h1, ?_⟩
      rw [indicator_of_mem (show (⟨stopData W VL VR ζ t s p, hgY⟩ : {y : YSp // IsGoodY s t y}) ∈
        {x : {y : YSp // IsGoodY s t y} | (t' : ℝ) ∈ PcY s x.1} from h1),
        ← capClock_congr fun u hu => (gammaY_stopData hs hEg hp hg (hu.2.trans ht't')).symm] at h2
      exact h2
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
  by_cases hS : (t' : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) t'
  · rw [← hAC p hp hg hS.1 hS.2]
    exact ⟨fun h => ⟨h.1, hS⟩, fun h => ⟨h.1, hStiff.1 hS⟩⟩
  · exact ⟨fun h => absurd (hStiff.2 h.2) hS, fun h => absurd h.2 hS⟩

/-- Second component of `ImgMarksStatement`. -/
theorem exists_marks_ae_eq_avoid (hs : 0 < s) (ht : 0 < t) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    (hgood : ∀ᵐ p ∂μ, p ∈ E ∧ Aux50Hit.IsGoodPath W VL VR ζ p.1) (φ : TestOn upperHalfPlaneOpens) :
    ∃ B', MeasurableSet[twoSlitMarks W VL VR ζ t s] B' ∧ B' =ᵐ[μ]
      {p | (t : ℝ) ∈ gPre s ζ W E p ∧ Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W E r p)
        (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ (capClock (gCurve s ζ W E p) t).toNNReal} := by
  have ht0 : (0 : ℝ) ≤ t := by exact_mod_cast ht.le
  obtain ⟨CPc, hCPc, hPc⟩ := exists_measurableSet_of_subtype (measurableSet_mem_PcY (s := s) (t := t) t ht0 le_rfl)
  refine ⟨stopData W VL VR ζ t s ⁻¹' (CPc ∩ AvY s t φ), measurable_stopData t s (hCPc.inter (measurableSet_AvY s t φ)),
    ?_⟩
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hgood] with p ⟨hp, hg⟩
  have hgY := isGoodY_stopData (VL := VL) (VR := VR) hs ht hEg hp hg
  have hiff := mem_PcY_stopData_iff (VL := VL) (VR := VR) hs hEg hp hg (le_refl (t : ℝ))
  simp only [mem_preimage, mem_inter_iff]
  rw [← hPc ⟨stopData W VL VR ζ t s p, hgY⟩]
  show (_ ∧ _) ↔ _
  by_cases htP : (t : ℝ) ∈ gPre s ζ W E p
  · have hav := isChartAvoid_capClock_iff hs hEg hp htP φ
    have hA : seedLine ζ W p.1 '' Ioc 0 t = alphaY (stopData W VL VR ζ t s p) '' Ioc 0 t :=
      image_congr fun u hu => (alphaY_stopData hg hu.2).symm
    rw [hA, ← GY_stopData (VL := VL) (VR := VR) (t := t) hs hEg hp, ← mem_AvY_iff hgY ht0 φ] at hav
    rw [hav]
    exact ⟨fun h => ⟨htP, h.2⟩, fun h => ⟨hiff.2 htP, h.2⟩⟩
  · exact ⟨fun h => absurd (hiff.1 h.1) htP, fun h => absurd h.1 htP⟩

end Marks

/-- **`ImgMarksStatement` holds.** -/
theorem imgMarksStatement : ImgMarksStatement.{u} := by
  intro rL rR hL hR Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ h₂ hC₂ hlaw k _ hk s hs
  have hEg : ∀ p ∈ glueGood (glueMeasure P k h hC.2.1) s ζ W, IsGlueGood s ζ W p := fun p hp =>
    isGlueGood_of_mem_glueGood p hp
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1).mono
      fun ω hω => hω.1
  have hgood : ∀ᵐ p ∂(glueMeasure P k h hC.2.1), p ∈ glueGood (glueMeasure P k h hC.2.1) s ζ W ∧
      Aux50Hit.IsGoodPath W VL VR ζ p.1 := by
    filter_upwards [ae_mem_glueGood (ae_isGlueGood hL hR hC hC₂ hlaw k hk hs),
      ae_glue_fst (μ := P) k hC.2.1 (Aux50Hit.ae_isGoodPath hC.1 hζ)] with p h1 h2
    exact ⟨h1, h2⟩
  refine ⟨fun r t' t ht'0 ht't ht A hA => ?_, fun t ht φ => ?_⟩
  · exact exists_marks_ae_eq_inter hs ht hEg hgood r (by exact_mod_cast ht'0) ht't hA
  · exact exists_marks_ae_eq_avoid hs ht hEg hgood φ

/-- **PROVE-WW-B18's named input `ImgChartConstStatement` holds** (steps R1–R6 of the contact step; Astra's follow-up
note, Part E). -/
theorem imgChartConstStatement : ImgChartConstStatement.{u} :=
  imgChartConstStatement_of_marks imgMarksStatement

/-- **The contact step `ReverseTipContactStatement` holds** (κ = 4, Wang–Wu Proposition 4.18). -/
theorem reverseTipContactStatement : ReverseTipContactStatement.{u} :=
  reverseTipContactStatement_of_chartConst imgChartConstStatement

end InteractingSLE.WangWu
