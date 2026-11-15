/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvData

/-!
# Initial image marks as measurable functions of the stopped record

Packet PROVE-CFCHART2. On records with separated junctions use the transported marks, and
on the remaining records use zero. The latter is a measurable regularization; good flow
records have separated junctions at every positive time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfConv

open LawUnique CfGiven CfChart Exist Exist.Staged Exist.StagedLaw
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
open CrossCond.Word49 MartChar.RealFlow

/-- Both junction gaps are separated from the driver. -/
def RecordGaps (s : ℝ≥0) (r : RecData) : Prop :=
  0 < rightImg (rdrv r) 0 s - rdrv r s ∧ -rightImg (fun t => -rdrv r t) 0 s - rdrv r s < 0

theorem measurable_rightImg_rdrv (s : ℝ≥0) (sg x : ℝ) :
    Measurable fun r : RecData => rightImg (fun t => sg * rdrv r t) x s := by
  let 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace RecData) :=
    Filtration.const ℝ≥0 inferInstance le_rfl
  have h := Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕)
    (W := fun t r => sg * rdrv r t) (fun t => (measurable_rdrv_apply t).const_mul sg)
    (fun r => ((continuous_rdrv r).comp NNReal.continuous_coe).const_smul sg)
    (x := fun _ => x) measurable_const s
  have he : ∀ r : RecData, InteractingSLE.Bessel.realPath (fun t r => sg * rdrv r t) r =
      fun t => sg * rdrv r t := fun r => funext fun t => by
    simp only [InteractingSLE.Bessel.realPath, rdrv, Real.toNNReal_coe]
  simp_rw [he] at h
  exact h

theorem measurableSet_recordGaps (s : ℝ≥0) : MeasurableSet {r : RecData | RecordGaps s r} := by
  have hL : Measurable fun r : RecData => rightImg (rdrv r) 0 s := by
    simpa only [one_mul] using measurable_rightImg_rdrv s 1 0
  have hR : Measurable fun r : RecData => rightImg (fun t => -rdrv r t) 0 s := by
    simpa only [neg_one_mul] using measurable_rightImg_rdrv s (-1) 0
  exact (measurableSet_lt measurable_const (hL.sub (measurable_rdrv_apply s))).inter
    (measurableSet_lt (hR.neg.sub (measurable_rdrv_apply s)) measurable_const)

theorem measurable_psiL_rdrv (s : ℝ≥0) (x : ℝ) : Measurable fun r : RecData => psiL (rdrv r) s x := by
  unfold psiL
  split_ifs
  · exact measurable_const
  · have h := measurable_rightImg_rdrv s 1 (-1 / x)
    simp only [one_mul] at h
    exact measurable_const.div (h.sub (measurable_rdrv_apply s))

theorem measurable_psiR_rdrv (s : ℝ≥0) (x : ℝ) : Measurable fun r : RecData => psiR (rdrv r) s x := by
  unfold psiR
  split_ifs
  · exact measurable_const
  · have h := measurable_rightImg_rdrv s (-1) (1 / x)
    simp only [neg_one_mul] at h
    exact measurable_const.div (h.neg.sub (measurable_rdrv_apply s))

theorem measurable_junL_rdrv (s : ℝ≥0) : Measurable fun r : RecData => junL (rdrv r) s := by
  have h := measurable_rightImg_rdrv s 1 0
  simp only [one_mul] at h
  exact measurable_const.div (h.sub (measurable_rdrv_apply s))

theorem measurable_junR_rdrv (s : ℝ≥0) : Measurable fun r : RecData => junR (rdrv r) s := by
  have h := measurable_rightImg_rdrv s (-1) 0
  simp only [neg_one_mul] at h
  exact measurable_const.div (h.neg.sub (measurable_rdrv_apply s))

open scoped Classical in
/-- Left marks, with an everywhere ordered measurable version. -/
def recordXL {n : ℕ} (s : ℝ≥0) (x : Fin n → ℝ) (r : RecData) : Fin (n + 1) → ℝ :=
  if RecordGaps s r then Fin.snoc (fun i => psiL (rdrv r) s (x i)) (junL (rdrv r) s) else fun _ => 0

open scoped Classical in
/-- Right marks, with an everywhere ordered measurable version. -/
def recordXR {n : ℕ} (s : ℝ≥0) (x : Fin n → ℝ) (r : RecData) : Fin (n + 1) → ℝ :=
  if RecordGaps s r then Fin.snoc (fun i => psiR (rdrv r) s (x i)) (junR (rdrv r) s) else fun _ => 0

theorem measurable_recordXL {n : ℕ} (s : ℝ≥0) (x : Fin n → ℝ) : Measurable (recordXL s x) := by
  classical
  apply Measurable.ite (measurableSet_recordGaps s) _ measurable_const
  exact measurable_snoc (measurable_pi_iff.2 fun i => measurable_psiL_rdrv s (x i))
    (measurable_junL_rdrv s)

theorem measurable_recordXR {n : ℕ} (s : ℝ≥0) (x : Fin n → ℝ) : Measurable (recordXR s x) := by
  classical
  apply Measurable.ite (measurableSet_recordGaps s) _ measurable_const
  exact measurable_snoc (measurable_pi_iff.2 fun i => measurable_psiR_rdrv s (x i))
    (measurable_junR_rdrv s)

theorem recordXL_nonpos {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, x i ≤ 0) (s : ℝ≥0) (r : RecData)
    (i : Fin (n + 1)) : recordXL s x r i ≤ 0 := by
  classical
  by_cases hg : RecordGaps s r
  · rw [recordXL, ite_eq_left hg]
    exact snoc_le (fun i => psiL_nonpos (continuous_rdrv r) s.coe_nonneg hg.1 (hx i))
      ((junL_le_psiL (continuous_rdrv r) s.coe_nonneg hg.1 le_rfl).trans
        (psiL_nonpos (continuous_rdrv r) s.coe_nonneg hg.1 le_rfl)) i
  · simp only [recordXL, ite_eq_right hg, le_refl]

theorem recordXR_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (s : ℝ≥0) (r : RecData)
    (i : Fin (n + 1)) : 0 ≤ recordXR s x r i := by
  classical
  by_cases hg : RecordGaps s r
  · rw [recordXR, ite_eq_left hg]
    exact le_snoc (fun i => psiR_nonneg (continuous_rdrv r) s.coe_nonneg hg.2 (hx i))
      ((psiR_nonneg (continuous_rdrv r) s.coe_nonneg hg.2 le_rfl).trans
        (psiR_le_junR (continuous_rdrv r) s.coe_nonneg hg.2 le_rfl)) i
  · simp only [recordXR, ite_eq_right hg, le_refl]

theorem antitone_recordXL {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, x i ≤ 0) (ha : Antitone x)
    (s : ℝ≥0) (r : RecData) : Antitone (recordXL s x r) := by
  classical
  by_cases hg : RecordGaps s r
  · rw [recordXL, ite_eq_left hg]
    exact antitone_snoc (fun i j hij => psiL_mono (continuous_rdrv r) s.coe_nonneg hg.1 (hx i) (ha hij))
      (fun i => junL_le_psiL (continuous_rdrv r) s.coe_nonneg hg.1 (hx i))
  · rw [recordXL, ite_eq_right hg]
    exact antitone_const

theorem monotone_recordXR {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hm : Monotone x)
    (s : ℝ≥0) (r : RecData) : Monotone (recordXR s x r) := by
  classical
  by_cases hg : RecordGaps s r
  · rw [recordXR, ite_eq_left hg]
    exact monotone_snoc (fun i j hij => psiR_mono (continuous_rdrv r) s.coe_nonneg hg.2 (hx i) (hm hij))
      (fun i => psiR_le_junR (continuous_rdrv r) s.coe_nonneg hg.2 (hx i))
  · rw [recordXR, ite_eq_right hg]
    exact monotone_const

section GoodRecord

variable {Z : Type*} {nL nR : ℕ} {W : ℝ≥0 → Z → ℝ}
  {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ} {ζ : Z → ℝ≥0∞}
  {s : ℝ≥0} {p : Z × HistorySpace 0 0}

/-- On the prefix interval, the record driver agrees with the physical flow driver. -/
theorem eqOn_rdrv_fDrv (hg : IsGood47 W VL VR ζ p)
    (he : IsRegularDriver ((fun t => W t p.1), ζ p.1)) :
    EqOn (rdrv (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1))) (fDrv W p) (Icc 0 (s : ℝ)) := by
  have hlt : (s : ℝ≥0∞) < ζ p.1 := by rw [hg.1.1]; exact ENNReal.coe_lt_top
  have hgood := isDrvGood_recOf_of_lt he hlt
  intro r hr
  exact rdrv_recOf_eq he hgood (ne_top_of_lt (lt_of_le_of_lt (min_le_left _ _) ENNReal.coe_lt_top))
    (by simpa only [rtime_recOf_coe, min_eq_left hlt.le, ENNReal.toNNReal_coe] using hr.2)

/-- The two junctions of every positive good prefix have separated gaps in the recorded driver. -/
theorem recordGaps_recOf (hg : IsGood47 W VL VR ζ p)
    (he : IsRegularDriver ((fun t => W t p.1), ζ p.1)) (hs : 0 < s) :
    RecordGaps s (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1)) := by
  have hr := eqOn_rdrv_fDrv (s := s) hg he
  have hL := Sec7.Lemma71B.rightImg_congr (continuous_fDrv hg) s.coe_nonneg hr 0
  have hR := Sec7.Lemma71B.rightImg_congr (continuous_fDrv hg).neg s.coe_nonneg
    (fun t ht => congrArg Neg.neg (hr ht)) 0
  unfold RecordGaps
  rw [hL, hR, hr ⟨s.coe_nonneg, le_rfl⟩]
  exact junction_gaps hg hs

/-- The everywhere regular left marks agree with the coarse image marks on good samples. -/
theorem recordXL_recOf {m : ℕ} (x : Fin m → ℝ) {E : Set (Z × HistorySpace 0 0)}
    (hg : IsGood47 W VL VR ζ p) (he : IsRegularDriver ((fun t => W t p.1), ζ p.1))
    (hs : 0 < s) (hp : p ∈ E) :
    recordXL s x (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1)) = qgXL x W s E p := by
  classical
  have hr := eqOn_rdrv_fDrv (s := s) hg he
  have hL := fun x => Sec7.Lemma71B.rightImg_congr (continuous_fDrv hg) s.coe_nonneg hr x
  simp only [recordXL, ite_eq_left (recordGaps_recOf hg he hs), qgXL, ite_eq_left hp,
    psiL, junL, hL, hr ⟨s.coe_nonneg, le_rfl⟩]

/-- The everywhere regular right marks agree with the coarse image marks on good samples. -/
theorem recordXR_recOf {m : ℕ} (x : Fin m → ℝ) {E : Set (Z × HistorySpace 0 0)}
    (hg : IsGood47 W VL VR ζ p) (he : IsRegularDriver ((fun t => W t p.1), ζ p.1))
    (hs : 0 < s) (hp : p ∈ E) :
    recordXR s x (recOf (s : ℝ≥0∞) ((fun t => W t p.1), ζ p.1)) = qgXR x W s E p := by
  classical
  have hr := eqOn_rdrv_fDrv (s := s) hg he
  have hR := fun x => Sec7.Lemma71B.rightImg_congr (continuous_fDrv hg).neg s.coe_nonneg
    (fun t ht => congrArg Neg.neg (hr ht)) x
  simp only [recordXR, ite_eq_left (recordGaps_recOf hg he hs), qgXR, ite_eq_left hp,
    psiR, junR, hR, hr ⟨s.coe_nonneg, le_rfl⟩]
  rfl

end GoodRecord

end InteractingSLE.Sec5.CfConv
