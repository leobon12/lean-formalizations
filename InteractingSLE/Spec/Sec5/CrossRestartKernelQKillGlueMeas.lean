/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQKillGlue
import InteractingSLE.Spec.Sec5.CrossCondWordMeas

/-!
# Lemma 4.7 in the chart `Q`: the killed image word of the counterflow is measurable

Packet PROVE-CFRESTART4, item D1 (measurability on the glued space; the Lemma 4.7 mirror of GLUECOND5's
`CrossCondWordMeas`). The flow chart is read through the **regularized** flow driver `fReg` (the regularized driver of
the flow history stopped at `q`, recentred; continuous and measurable for every sample, equal to the flow driver on
`[0, q]` on good samples). With a measurable set `E` of good samples (`Kill47.IsGood47`):

* `measurable_qgCurve`: the positions of the image curve `Ψ ∘ α` are measurable;
* `measurableSet_mem_qgPre`: the rational pre-contact events are measurable (`G = R(K_q)` is hitting-measurable and
  closed on good samples);
* `measurable_indicator_capClock_qgCurve`: the capacity clock at rational times is measurable on its pre-contact event;
* **`measurableSet_lt_qT`**, **`measurable_qW`**: the killing events and the killed image driver are measurable.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord (vRay)
open LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q
open CrossCond.Word49 (psiL psiR junL junR mem_preContact_iff_ball measurableSet_disjoint_ball)

namespace Kill47

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {q : ℝ≥0} {p : Ω × HistorySpace 0 0}

/-! ### The regularized flow driver -/

/-- **The regularized flow driver**: the regularized driver of the flow history stopped at `q`, recentred at `0`. -/
def fReg (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (q : ℝ≥0)
    (p : Ω × HistorySpace 0 0) (r : ℝ) : ℝ :=
  Ito.rpath (Sec4.regPath (Sec4.stopHistory (Aux50Hit.cstop q) (killedHistory W VL VR ζ p.1))) r -
    Ito.rpath (Sec4.regPath (Sec4.stopHistory (Aux50Hit.cstop q) (killedHistory W VL VR ζ p.1))) 0

theorem continuous_fReg : Continuous (fReg W VL VR ζ q p) := (Sec4.continuous_rpath_regPath _).sub continuous_const

theorem fReg_zero : fReg W VL VR ζ q p 0 = 0 := sub_self _

theorem fReg_toNNReal (r : ℝ) : fReg W VL VR ζ q p ((r.toNNReal : ℝ≥0) : ℝ) = fReg W VL VR ζ q p r := by
  simp only [fReg, Ito.rpath, Real.toNNReal_coe]

/-- On good samples the regularized flow driver is the flow driver on `[0, q]`. -/
theorem eqOn_fReg (hg : IsGood47 W VL VR ζ p) : EqOn (fReg W VL VR ζ q p) (fDrv W p) (Icc 0 (q : ℝ)) := by
  intro r hr
  have h1 := Aux50Hit.eqOn_rpath_regPath_stopHistory hg.1 (Aux50Hit.cstop q) hr
  have h0 := Aux50Hit.eqOn_rpath_regPath_stopHistory hg.1 (Aux50Hit.cstop q) ⟨le_rfl, q.coe_nonneg⟩
  rw [fReg, h1, h0]
  simp only [fDrv, Ito.rpath, Real.toNNReal_zero, hg.1.2.1, sub_zero]

theorem revChart_fReg (hg : IsGood47 W VL VR ζ p) (z : ℂ) :
    revChart (fReg W VL VR ζ q p) q z = revChart (fDrv W p) q z := by
  unfold revChart
  rw [Ito.fwdMap_congr_of_eqOn (eqOn_fReg hg)]

theorem imgCurve_fReg (hg : IsGood47 W VL VR ζ p) (α : ℝ → ℂ) (u : ℝ) :
    imgCurve (fReg W VL VR ζ q p) q α u = imgCurve (fDrv W p) q α u := by
  unfold imgCurve
  split_ifs
  · rfl
  · exact revChart_fReg hg _

theorem rightImg_fReg (hg : IsGood47 W VL VR ζ p) (x : ℝ) :
    rightImg (fReg W VL VR ζ q p) x q = rightImg (fDrv W p) x q :=
  Sec7.Lemma71B.rightImg_congr (continuous_fDrv hg) q.coe_nonneg (eqOn_fReg hg) x

theorem rightImg_neg_fReg (hg : IsGood47 W VL VR ζ p) (x : ℝ) :
    rightImg (fun r => -fReg W VL VR ζ q p r) x q = rightImg (fun r => -fDrv W p r) x q :=
  Sec7.Lemma71B.rightImg_congr (show Continuous fun r => -fDrv W p r from (continuous_fDrv hg).neg) q.coe_nonneg
    (fun r hr => by simp only [eqOn_fReg hg hr]) x

theorem fReg_q (hg : IsGood47 W VL VR ζ p) : fReg W VL VR ζ q p q = fDrv W p q :=
  eqOn_fReg hg ⟨q.coe_nonneg, le_rfl⟩

theorem psiL_fReg (hg : IsGood47 W VL VR ζ p) (x : ℝ) :
    psiL (fReg W VL VR ζ q p) q x = psiL (fDrv W p) q x := by
  simp only [psiL, rightImg_fReg hg, fReg_q hg]

theorem psiR_fReg (hg : IsGood47 W VL VR ζ p) (x : ℝ) :
    psiR (fReg W VL VR ζ q p) q x = psiR (fDrv W p) q x := by
  simp only [psiR, rightImg_neg_fReg hg, fReg_q hg]

theorem junL_fReg (hg : IsGood47 W VL VR ζ p) : junL (fReg W VL VR ζ q p) q = junL (fDrv W p) q := by
  simp only [junL, rightImg_fReg hg, fReg_q hg]

theorem junR_fReg (hg : IsGood47 W VL VR ζ p) : junR (fReg W VL VR ζ q p) q = junR (fDrv W p) q := by
  simp only [junR, rightImg_neg_fReg hg, fReg_q hg]

/-- On good samples the obstacle is closed in `ℂ`. -/
theorem isClosed_qObs (hg : IsGood47 W VL VR ζ p) : IsClosed (qObs W VL VR ζ q p) := by
  rw [qObs_of_good hg]
  obtain ⟨-, ⟨η, hη, hηH, -⟩, -⟩ := id hg
  exact GlueCond.isClosed_image_negInv_fwdHull ((continuous_flow hg).comp continuous_real_toNNReal) hη
    ENNReal.coe_lt_top fun r hr _ => hηH r hr

theorem qObs_subset_H (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (q : ℝ≥0) (p : Ω × HistorySpace 0 0) : qObs W VL VR ζ q p ⊆ H :=
  fun _ ⟨_, hw, e⟩ => e ▸ WangWu.negInv_mem_H ((hullAt_relClosed q _).1 hw)

/-! ### Measurability on the glued space -/

section Meas

variable [MeasurableSpace Ω] {E : Set (Ω × HistorySpace 0 0)}

theorem measurable_stopFlow (hX : IsMeasurableKilledDriving W VL VR ζ) (q : ℝ≥0) :
    Measurable fun p : Ω × HistorySpace 0 0 => Sec4.stopHistory (Aux50Hit.cstop q) (killedHistory W VL VR ζ p.1) :=
  (Sec4.measurable_stopHistory (Aux50Hit.measurable_cstop q)).comp ((measurable_killedHistory hX).comp measurable_fst)

theorem measurable_fReg_apply (hX : IsMeasurableKilledDriving W VL VR ζ) (r : ℝ) :
    Measurable fun p : Ω × HistorySpace 0 0 => fReg W VL VR ζ q p r := by
  have h : ∀ r : ℝ, Measurable fun p : Ω × HistorySpace 0 0 =>
      Ito.rpath (Sec4.regPath (Sec4.stopHistory (Aux50Hit.cstop q) (killedHistory W VL VR ζ p.1))) r :=
    fun r => (Sec4.measurable_regPath_apply r.toNNReal).comp (measurable_stopFlow hX q)
  exact (h r).sub (h 0)

/-- The obstacle is hitting-measurable. -/
theorem measurable_qObs (hX : IsMeasurableKilledDriving W VL VR ζ) (q : ℝ≥0) :
    Measurable[_, hittingSigma] (qObs W VL VR ζ q) :=
  measurable_image_negInv.comp ((measurable_hullAt q).comp ((measurable_killedHistory hX).comp measurable_fst))

omit [MeasurableSpace Ω] in
open scoped Classical in
theorem qgCurve_eq (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (p : Ω × HistorySpace 0 0) (u : ℝ) :
    qgCurve W q E p u = if p ∈ E then (if u ≤ 0 then 0 else
      negInv (fwdMap (fReg W VL VR ζ q p) q (negInv (histLine p.2 u)))) else vRay u := by
  by_cases hp : p ∈ E
  · rw [qgCurve_of_mem hp, ← imgCurve_fReg (VL := VL) (VR := VR) (ζ := ζ) (q := q) (hEg p hp)]
    simp only [hp, ↓reduceIte]
    rfl
  · simp only [qgCurve, hp, ↓reduceIte]

/-- **The positions of the image curve are measurable.** -/
theorem measurable_qgCurve (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (u : ℝ) : Measurable fun p => qgCurve W q E p u := by
  classical
  simp_rw [qgCurve_eq (VL := VL) (VR := VR) (ζ := ζ) hEg _ u]
  refine Measurable.ite hE ?_ measurable_const
  by_cases hu : u ≤ 0
  · simp only [hu, ↓reduceIte]
    exact measurable_const
  · simp only [hu, ↓reduceIte]
    have hy : Measurable fun p : Ω × HistorySpace 0 0 => negInv (histLine p.2 u) :=
      measurable_negInv.comp ((measurable_histLine u).comp measurable_snd)
    have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun p : Ω × HistorySpace 0 0 => fReg W VL VR ζ q p)
      (fun p => continuous_fReg) (fun t => measurable_fReg_apply hX t) (fun p => fReg_zero)
      (τ := fun _ => (q : ℝ)) measurable_const (fun _ => q.coe_nonneg) hy).1
    exact measurable_negInv.comp h

/-- **The rational pre-contact events are measurable.** -/
theorem measurableSet_mem_qgPre (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (r : ℚ) : MeasurableSet {p | (r : ℝ) ∈ qgPre W VL VR ζ q E p} := by
  classical
  by_cases hr : (0 : ℝ) ≤ r
  · set T : Set (Ω × HistorySpace 0 0) := ⋃ m : ℕ, ⋂ u : ℚ,
        ({_p | (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ r}ᶜ ∪
          {p | Disjoint (ball (histLine p.2 u) (1 / ((m : ℝ) + 1))) (qObs W VL VR ζ q p)}) with hTdef
    have heq : {p | (r : ℝ) ∈ qgPre W VL VR ζ q E p} = (E ∩ T) ∪ Eᶜ := by
      ext p
      by_cases hp : p ∈ E
      · have hg := hEg p hp
        have hαc : ContinuousOn (histLine p.2) (Ici 0) := (CfRegQ.reg_of_mem_goodCfSet hg.2.2.1.1).2.2.2.2.1
        simp only [mem_ofPred_eq, qgPre_of_mem hp, mem_preContact_iff_ball hαc (isClosed_qObs hg) hr, mem_union,
          mem_inter_iff, hp, true_and, mem_compl_iff, not_true_eq_false, or_false, hTdef, mem_iUnion,
          mem_iInter]
        constructor
        · rintro ⟨m, hm⟩
          refine ⟨m, fun u => ?_⟩
          by_cases hu : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ r
          · exact Or.inr (hm u hu.1 hu.2)
          · exact Or.inl hu
        · rintro ⟨m, hm⟩
          refine ⟨m, fun u hu0 hur => ?_⟩
          rcases hm u with h | h
          · exact absurd ⟨hu0, hur⟩ h
          · exact h
      · simp only [mem_ofPred_eq, qgPre, hp, ↓reduceIte, mem_Ici, mem_union, mem_inter_iff, false_and,
          mem_compl_iff, not_false_eq_true, or_true, iff_true]
        exact hr
    rw [heq]
    refine (hE.inter (MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u =>
      (MeasurableSet.const _).compl.union ?_)).union hE.compl
    exact measurableSet_disjoint_ball ((measurable_histLine u).comp measurable_snd)
      (measurable_qObs hX q) (qObs_subset_H W VL VR ζ q) _
  · have heq : {p | (r : ℝ) ∈ qgPre W VL VR ζ q E p} = ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hmem
      by_cases hp : p ∈ E
      · rw [qgPre_of_mem hp] at hmem; exact hr hmem.1
      · simp only [qgPre, hp, ↓reduceIte, mem_Ici] at hmem; exact hr hmem
    rw [heq]
    exact MeasurableSet.empty

/-- **The capacity clock at a rational time is measurable on its pre-contact event.** -/
theorem measurable_indicator_capClock_qgCurve (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (r : ℚ) :
    Measurable ({p | (r : ℝ) ∈ qgPre W VL VR ζ q E p}.indicator fun p => capClock (qgCurve W q E p) r) := by
  classical
  set A := {p | (r : ℝ) ∈ qgPre W VL VR ζ q E p} with hAdef
  have hA : MeasurableSet A := measurableSet_mem_qgPre hX hE hEg r
  have hK := isKilledCurve_qgCurve (q := q) hEg
  set Γ : Ω × HistorySpace 0 0 → ℝ≥0 → ℂ := fun p t =>
    if p ∈ A then qgCurve W q E p (min (t : ℝ) r) else 0 with hΓdef
  have hΓc : ∀ p, Continuous (Γ p) := by
    intro p
    by_cases hp : p ∈ A
    · simp only [hΓdef, hp, ↓reduceIte]
      have hr0 : (0 : ℝ) ≤ r := (hK p).nonneg _ hp
      refine ((hK p).cont.mono ((hK p).icc _ hp)).comp_continuous
        ((NNReal.continuous_coe.min continuous_const)) fun t => ⟨le_min t.coe_nonneg hr0, min_le_right _ _⟩
    · simp only [hΓdef, hp, ↓reduceIte]
      exact continuous_const
  have hΓm : ∀ t, Measurable fun p => Γ p t := fun t =>
    Measurable.ite hA (measurable_qgCurve hX hE hEg _) measurable_const
  have hmeas := Restart.measurable_hcapHit_image hΓc hΓm (r : ℝ).toNNReal
  have heq : A.indicator (fun p => capClock (qgCurve W q E p) r) =
      A.indicator fun p => (WholeField.hcapHit (Γ p '' Icc 0 (r : ℝ).toNNReal)).toReal / 2 := by
    refine indicator_congr fun p hp => ?_
    have hr0 : (0 : ℝ) ≤ r := (hK p).nonneg _ hp
    have himg : qgCurve W q E p '' Icc 0 r = Γ p '' Icc 0 (r : ℝ).toNNReal := by
      rw [Sec7.Lemma71E.image_Icc_real_eq hr0]
      refine image_congr fun t ht => ?_
      have htr : (t : ℝ) ≤ r := by
        have := ht.2
        rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0] at this
      simp only [hΓdef, hp, ↓reduceIte, min_eq_left htr]
    have h0 : (Γ p 0).im ≤ 0 := by
      simp only [hΓdef, hp, ↓reduceIte, NNReal.coe_zero, min_eq_left hr0, (hK p).zero, Complex.zero_im,
        le_refl]
    rw [Restart.hcapHit_image_eq (hΓc p).continuousOn h0, ← himg]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (qgCurve W q E p '' Icc 0 r)) := by
      have := (hK p).capClock_nonneg hp
      rw [capClock] at this
      linarith
    rw [ENNReal.toReal_ofReal hnn, capClock]
  rw [heq]
  exact ((ENNReal.measurable_toReal.comp hmeas).div_const _).indicator hA

/-- **The events `{t < qT}` are measurable.** -/
theorem measurableSet_lt_qT (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (t : ℝ≥0) :
    MeasurableSet {p | (t : WithTop ℝ≥0) < qT W VL VR ζ q E p} :=
  measurableSet_lt_kcLife (isKilledCurve_qgCurve hEg) (measurableSet_mem_qgPre hX hE hEg)
    (measurable_indicator_capClock_qgCurve hX hE hEg) t

/-- **The killed image driver is measurable at every time.** -/
theorem measurable_qW (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (t : ℝ≥0) : Measurable (qW W VL VR ζ q E t) :=
  measurable_kcW (isKilledCurve_qgCurve hEg) (measurableSet_mem_qgPre hX hE hEg)
    (measurable_indicator_capClock_qgCurve hX hE hEg) (fun r => measurable_qgCurve hX hE hEg r) t

/-- The real Loewner flow of `sg · fReg` is measurable in the glued sample. -/
theorem measurable_rightImg_fReg (hX : IsMeasurableKilledDriving W VL VR ζ) (sg x : ℝ) :
    Measurable fun p : Ω × HistorySpace 0 0 => rightImg (fun r => sg * fReg W VL VR ζ q p r) x q := by
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have h := Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c)
    (W := fun r p => sg * fReg W VL VR ζ q p r)
    (fun r => (measurable_fReg_apply hX r).const_mul sg)
    (fun p => (continuous_fReg.comp NNReal.continuous_coe).const_smul sg) (x := fun _ => x) measurable_const q
  have e : ∀ p : Ω × HistorySpace 0 0, Bessel.realPath (fun r p => sg * fReg W VL VR ζ q p r) p =
      fun r => sg * fReg W VL VR ζ q p r :=
    fun p => funext fun r => by simp only [Bessel.realPath, fReg_toNNReal]
  simp_rw [e] at h
  exact h

theorem measurable_rightImg_fReg_one (hX : IsMeasurableKilledDriving W VL VR ζ) (x : ℝ) :
    Measurable fun p : Ω × HistorySpace 0 0 => rightImg (fReg W VL VR ζ q p) x q := by
  have := measurable_rightImg_fReg (q := q) hX 1 x
  simpa only [one_mul] using this

theorem measurable_rightImg_neg_fReg (hX : IsMeasurableKilledDriving W VL VR ζ) (x : ℝ) :
    Measurable fun p : Ω × HistorySpace 0 0 => rightImg (fun r => -fReg W VL VR ζ q p r) x q := by
  have := measurable_rightImg_fReg (q := q) hX (-1) x
  simpa only [neg_one_mul] using this

theorem measurable_psiL_fReg (hX : IsMeasurableKilledDriving W VL VR ζ) (x : ℝ) :
    Measurable fun p : Ω × HistorySpace 0 0 => psiL (fReg W VL VR ζ q p) q x := by
  unfold psiL
  split_ifs
  · exact measurable_const
  · exact measurable_const.div ((measurable_rightImg_fReg_one hX _).sub (measurable_fReg_apply hX q))

theorem measurable_psiR_fReg (hX : IsMeasurableKilledDriving W VL VR ζ) (x : ℝ) :
    Measurable fun p : Ω × HistorySpace 0 0 => psiR (fReg W VL VR ζ q p) q x := by
  unfold psiR
  split_ifs
  · exact measurable_const
  · exact measurable_const.div ((measurable_rightImg_neg_fReg hX _).neg.sub (measurable_fReg_apply hX q))

theorem measurable_junL_fReg (hX : IsMeasurableKilledDriving W VL VR ζ) :
    Measurable fun p : Ω × HistorySpace 0 0 => junL (fReg W VL VR ζ q p) q :=
  measurable_const.div ((measurable_rightImg_fReg_one hX 0).sub (measurable_fReg_apply hX q))

theorem measurable_junR_fReg (hX : IsMeasurableKilledDriving W VL VR ζ) :
    Measurable fun p : Ω × HistorySpace 0 0 => junR (fReg W VL VR ζ q p) q :=
  measurable_const.div ((measurable_rightImg_neg_fReg hX 0).neg.sub (measurable_fReg_apply hX q))

theorem measurable_qgXL {m : ℕ} (x : Fin m → ℝ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) : Measurable fun p : Ω × HistorySpace 0 0 => qgXL x W q E p := by
  classical
  have e : (fun p : Ω × HistorySpace 0 0 => qgXL x W q E p) = fun p => if p ∈ E then
      (Fin.snoc (fun i => psiL (fReg W VL VR ζ q p) q (x i)) (junL (fReg W VL VR ζ q p) q) : Fin (m + 1) → ℝ)
      else fun _ => 0 := by
    funext p
    by_cases hp : p ∈ E
    · simp only [qgXL, hp, ↓reduceIte, psiL_fReg (hEg p hp), junL_fReg (hEg p hp)]
    · simp only [qgXL, hp, ↓reduceIte]
  rw [e]
  refine Measurable.ite hE ?_ measurable_const
  exact CrossCond.Word49.measurable_snoc (measurable_pi_iff.2 fun i => measurable_psiL_fReg hX (x i))
    (measurable_junL_fReg hX)

theorem measurable_qgXR {m : ℕ} (x : Fin m → ℝ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) : Measurable fun p : Ω × HistorySpace 0 0 => qgXR x W q E p := by
  classical
  have e : (fun p : Ω × HistorySpace 0 0 => qgXR x W q E p) = fun p => if p ∈ E then
      (Fin.snoc (fun j => psiR (fReg W VL VR ζ q p) q (x j)) (junR (fReg W VL VR ζ q p) q) : Fin (m + 1) → ℝ)
      else fun _ => 0 := by
    funext p
    by_cases hp : p ∈ E
    · simp only [qgXR, hp, ↓reduceIte, psiR_fReg (hEg p hp), junR_fReg (hEg p hp)]
    · simp only [qgXR, hp, ↓reduceIte]
  rw [e]
  refine Measurable.ite hE ?_ measurable_const
  exact CrossCond.Word49.measurable_snoc (measurable_pi_iff.2 fun j => measurable_psiR_fReg hX (x j))
    (measurable_junR_fReg hX)

/-- **The images of the left marks are measurable at every time.** -/
theorem measurable_qVL {m : ℕ} (x : Fin m → ℝ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (i : Fin (m + 1)) (t : ℝ≥0) :
    Measurable (qVL x W VL VR ζ q E i t) :=
  measurable_kcVL (isKilledCurve_qgCurve hEg) (measurableSet_mem_qgPre hX hE hEg)
    (measurable_indicator_capClock_qgCurve hX hE hEg) (fun r => measurable_qgCurve hX hE hEg r)
    (measurable_qgXL x hX hE hEg) i t

/-- **The images of the right marks are measurable at every time.** -/
theorem measurable_qVR {m : ℕ} (x : Fin m → ℝ) (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (j : Fin (m + 1)) (t : ℝ≥0) :
    Measurable (qVR x W VL VR ζ q E j t) :=
  measurable_kcVR (isKilledCurve_qgCurve hEg) (measurableSet_mem_qgPre hX hE hEg)
    (measurable_indicator_capClock_qgCurve hX hE hEg) (fun r => measurable_qgCurve hX hE hEg r)
    (measurable_qgXR x hX hE hEg) j t

end Meas

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
