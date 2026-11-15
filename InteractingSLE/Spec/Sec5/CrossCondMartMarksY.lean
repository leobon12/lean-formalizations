/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondMartStop

/-!
# The image word read from good stopped data is measurable (general `κ`)

Packet PROVE-GLUECOND7. The general-`κ` form of PROVE-WW-B19's `ImgChartConstMarksY`, with the obstacle the filled
counterflow hull `R(K′_s)` (`cfHullQ`, hitting-measurable) instead of a simple reverse slit: pre-contact at a rational
time is read through balls around the rational positions of the flow line that miss the obstacle
(`mem_preContact_iff_ball`, `measurableSet_disjoint_ball`, PROVE-GLUECOND5).

* `RatD`, `IsAwayD`, `IsGoodD` (good stopped data, no measurability claimed);
* `measurable_alphaD`, `measurable_gammaD`, `measurableSet_RatD`, `measurableSet_isAwayD`;
* on the subtype of good stopped data: `measurableSet_mem_PcD`, `measurableSet_mem_PD`,
  `measurable_indicator_capClock_gammaD`, `measurableSet_lt_kLife_gammaD`, **`measurable_indicator_kW_gammaD`**,
  **`measurable_indicator_kVL_gammaD`**, **`measurable_indicator_kVR_gammaD`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q
open ImgDrv MartChar
open Sec7.Lemma71C (capClock)
open Sec7.Lemma71E Restart MartChar.RealFlow LocalSets

namespace Word49

section Defs

variable {nL nR : ℕ}

/-- The rational pre-contact condition read from stopped data. -/
def RatD (s : ℝ≥0) (q : ℚ) : Set (Y49 nL nR) :=
  {y | ∃ m : ℕ, ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q → Disjoint (ball (alphaD y u) (1 / ((m : ℝ) + 1))) (GD s y)}

/-- The away condition of the announcing times, read from stopped data. -/
def IsAwayD (s : ℝ≥0) (n : ℕ) (y : Y49 nL nR) (q : ℚ) : Prop :=
  ((0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n) ∧ ∀ u : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
    Disjoint (ball (alphaD y u) (1 / ((n : ℝ) + 1))) (GD s y)

/-- **Good stopped data** (no measurability claimed): the image curve is a killed arc before `t`, the rational
pre-contact times up to `t` are given by `RatD`, the image curve is continuous on each pre-contact prefix, the flow line
is a continuous curve from `0` into `ℍ` on `[0, t]`, and the obstacle is closed. -/
structure IsGoodD (s : ℝ≥0) (t : ℚ) (y : Y49 nL nR) : Prop where
  killed : IsKilledArc (gammaD s y) (PD t s y)
  rat : ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ t → ((q : ℝ) ∈ PcD s y ↔ y ∈ RatD s q)
  cont : ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ t → (q : ℝ) ∈ PcD s y → ContinuousOn (gammaD s y) (Icc 0 q)
  alphaCont : ContinuousOn (alphaD y) (Icc 0 t)
  alpha0 : alphaD y 0 = 0
  alphaH : ∀ u ∈ Ioc (0 : ℝ) t, alphaD y u ∈ H
  gClosed : IsClosed (GD s y)

end Defs

section Y

variable {nL nR : ℕ} {s : ℝ≥0} {t : ℚ}

theorem measurable_alphaD (u : ℝ) : Measurable fun y : Y49 nL nR => alphaD y u :=
  (LP.measurable_traceAt _).comp (measurable_pi_iff.2 fun r => (Sec4.measurable_regPath_apply r).comp measurable_fst)

theorem measurable_GD (s : ℝ≥0) : Measurable[_, hittingSigma] (GD (nL := nL) (nR := nR) s) :=
  (measurable_cfHullQ s).comp measurable_snd

theorem GD_subset_H (y : Y49 nL nR) : GD s y ⊆ H := (cfHullQ_relClosed s y.2).1

theorem measurable_gammaD (q : ℝ) : Measurable fun y : Y49 nL nR => gammaD s y q := by
  by_cases hq : q ≤ 0
  · simp only [gammaD, imgCurve, hq, ↓reduceIte]
    exact measurable_const
  · simp only [gammaD, imgCurve, hq, ↓reduceIte, revChart]
    have hy : Measurable fun y : Y49 nL nR => negInv (alphaD y q) := measurable_negInv.comp (measurable_alphaD q)
    have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun y : Y49 nL nR => cfDrv0 s y.2)
      (fun y => continuous_cfDrv0 s y.2) (fun u => (measurable_cfDrv0_apply' s u).comp measurable_snd)
      (fun y => cfDrv0_zero s y.2) (τ := fun _ => (s : ℝ)) measurable_const (fun _ => s.coe_nonneg) hy).1
    exact measurable_negInv.comp h

theorem measurableSet_disjoint_ball_alphaD (u : ℝ) (ρ : ℝ) :
    MeasurableSet {y : Y49 nL nR | Disjoint (ball (alphaD y u) ρ) (GD s y)} :=
  measurableSet_disjoint_ball (measurable_alphaD u) (measurable_GD s) GD_subset_H ρ

theorem measurableSet_RatD (q : ℚ) : MeasurableSet (RatD (nL := nL) (nR := nR) s q) := by
  have e : RatD (nL := nL) (nR := nR) s q = ⋃ m : ℕ, ⋂ u : ℚ, {y : Y49 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
      Disjoint (ball (alphaD y u) (1 / ((m : ℝ) + 1))) (GD s y)} := by
    ext y
    simp only [RatD, mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [e]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u => ?_
  by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q
  · simp only [hc.1, hc.2, forall_const]
    exact measurableSet_disjoint_ball_alphaD _ _
  · have e : {y : Y49 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
        Disjoint (ball (alphaD y u) (1 / ((m : ℝ) + 1))) (GD s y)} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hc
    rw [e]
    exact MeasurableSet.univ

theorem measurableSet_isAwayD (n : ℕ) (q : ℚ) : MeasurableSet {y : Y49 nL nR | IsAwayD s n y q} := by
  have e : {y : Y49 nL nR | IsAwayD s n y q} = {_y | (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n} ∩ ⋂ u : ℚ,
      {y : Y49 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q → Disjoint (ball (alphaD y u) (1 / ((n : ℝ) + 1))) (GD s y)} := by
    ext y
    simp only [IsAwayD, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [e]
  refine MeasurableSet.const _ |>.inter (MeasurableSet.iInter fun u => ?_)
  by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q
  · simp only [hc.1, hc.2, forall_const]
    exact measurableSet_disjoint_ball_alphaD _ _
  · have e : {y : Y49 nL nR | (0 : ℝ) ≤ u → (u : ℝ) ≤ q →
        Disjoint (ball (alphaD y u) (1 / ((n : ℝ) + 1))) (GD s y)} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hc
    rw [e]
    exact MeasurableSet.univ

theorem measurable_gXLD (xL : Fin nL → ℝ) (s : ℝ≥0) : Measurable fun y : Y49 nL nR => gXLD xL s y :=
  measurable_snoc (measurable_pi_iff.2 fun i => (measurable_psiL s (xL i)).comp measurable_snd)
    ((measurable_junL s).comp measurable_snd)

theorem measurable_gXRD (xR : Fin nR → ℝ) (s : ℝ≥0) : Measurable fun y : Y49 nL nR => gXRD xR s y :=
  measurable_snoc (measurable_pi_iff.2 fun j => (measurable_psiR s (xR j)).comp measurable_snd)
    ((measurable_junR s).comp measurable_snd)

end Y

/-! ### On the good stopped data -/

section Good

variable {nL nR : ℕ} {s : ℝ≥0} {t : ℚ}

/-- The rational pre-contact events (up to `t`) of good stopped data are measurable. -/
theorem measurableSet_mem_PcD (q : ℚ) (hq0 : (0 : ℝ) ≤ q) (hqt : (q : ℝ) ≤ t) :
    MeasurableSet {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1} := by
  have e : {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1} = Subtype.val ⁻¹' RatD s q := by
    ext x
    exact x.2.rat q hq0 hqt
  rw [e]
  exact measurable_subtype_coe (measurableSet_RatD q)

/-- The rational pre-contact events before `t` of good stopped data are measurable. -/
theorem measurableSet_mem_PD (q : ℚ) :
    MeasurableSet {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PD t s x.1} := by
  by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t
  · have e : {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PD t s x.1} =
        {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1} := by
      ext x
      simp only [PD, mem_ofPred_eq, mem_inter_iff, mem_Iio, hq.2, and_true]
    rw [e]
    exact measurableSet_mem_PcD q hq.1 hq.2.le
  · have e : {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PD t s x.1} = ∅ := by
      ext x
      simp only [PD, PcD, preContact, mem_ofPred_eq, mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h0, -⟩, h1⟩
      exact hq ⟨h0, h1⟩
    rw [e]
    exact MeasurableSet.empty

/-- The capacity clock of good stopped data at a rational pre-contact time up to `t` is measurable. -/
theorem measurable_indicator_capClock_gammaD (q : ℚ) (hq0 : (0 : ℝ) ≤ q) (hqt : (q : ℝ) ≤ t) :
    Measurable ({x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1}.indicator
      fun x => capClock (gammaD s x.1) q) := by
  classical
  set A := {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1} with hAdef
  have hA : MeasurableSet A := measurableSet_mem_PcD q hq0 hqt
  set Γ : {y : Y49 nL nR // IsGoodD s t y} → ℝ≥0 → ℂ := fun x r =>
    if x ∈ A then gammaD s x.1 (min (r : ℝ) q) else 0 with hΓdef
  have hΓc : ∀ x, Continuous (Γ x) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [hΓdef, hx, ↓reduceIte]
      exact (x.2.cont q hq0 hqt hx).comp_continuous (NNReal.continuous_coe.min continuous_const)
        fun r => ⟨le_min r.coe_nonneg hq0, min_le_right _ _⟩
    · simp only [hΓdef, hx, ↓reduceIte]
      exact continuous_const
  have hΓm : ∀ r, Measurable fun x => Γ x r := fun r =>
    Measurable.ite hA ((measurable_gammaD _).comp measurable_subtype_coe) measurable_const
  have hmeas := measurable_hcapHit_image hΓc hΓm (q : ℝ).toNNReal
  have heq : A.indicator (fun x => capClock (gammaD s x.1) q) =
      A.indicator fun x => (WholeField.hcapHit (Γ x '' Icc 0 (q : ℝ).toNNReal)).toReal / 2 := by
    refine indicator_congr fun x hx => ?_
    have himg : gammaD s x.1 '' Icc 0 q = Γ x '' Icc 0 (q : ℝ).toNNReal := by
      rw [Sec7.Lemma71E.image_Icc_real_eq hq0]
      refine image_congr fun r hr => ?_
      have hrq : (r : ℝ) ≤ q := by
        have := hr.2
        rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0] at this
      simp only [hΓdef, hx, ↓reduceIte, min_eq_left hrq]
    have h0 : (Γ x 0).im ≤ 0 := by
      simp only [hΓdef, hx, ↓reduceIte, NNReal.coe_zero, min_eq_left hq0, gammaD, imgCurve, le_refl,
        Complex.zero_im]
    rw [hcapHit_image_eq (hΓc x).continuousOn h0, ← himg]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (gammaD s x.1 '' Icc 0 q)) := by
      rw [himg, ConformalImage.hcapSet_eq (isHPHull_fillH_image (hΓc x).continuousOn h0)]
      exact HPHull.hcap_nonneg _
    rw [ENNReal.toReal_ofReal hnn, capClock]
  rw [heq]
  exact ((ENNReal.measurable_toReal.comp hmeas).div_const _).indicator hA

theorem measurable_indicator_capClock_gammaD_PD (q : ℚ) :
    Measurable ({x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PD t s x.1}.indicator
      fun x => capClock (gammaD s x.1) q) := by
  by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t
  · have e : {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PD t s x.1} =
        {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PcD s x.1} := by
      ext x
      simp only [PD, mem_ofPred_eq, mem_inter_iff, mem_Iio, hq.2, and_true]
    rw [e]
    exact measurable_indicator_capClock_gammaD q hq.1 hq.2.le
  · have e : {x : {y : Y49 nL nR // IsGoodD s t y} | (q : ℝ) ∈ PD t s x.1} = ∅ := by
      ext x
      simp only [PD, PcD, preContact, mem_ofPred_eq, mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h0, -⟩, h1⟩
      exact hq ⟨h0, h1⟩
    rw [e, indicator_empty]
    exact measurable_const

theorem measurableSet_lt_kLife_gammaD (r : ℝ≥0) :
    MeasurableSet {x : {y : Y49 nL nR // IsGoodD s t y} |
      (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)} :=
  measurableSet_lt_kLife (fun x => x.2.killed) measurableSet_mem_PD measurable_indicator_capClock_gammaD_PD r

/-- **The killed driver read from good stopped data is measurable.** -/
theorem measurable_indicator_kW_gammaD (r : ℝ≥0) :
    Measurable ({x : {y : Y49 nL nR // IsGoodD s t y} |
      (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
        fun x => kW (gammaD s x.1) (PD t s x.1) r) :=
  measurable_indicator_kW_of_base (fun x => x.2.killed) measurableSet_mem_PD
    measurable_indicator_capClock_gammaD_PD (fun q => (measurable_gammaD q).comp measurable_subtype_coe) r

end Good

/-! ### The image marks read from good stopped data -/

section Marks

variable {nL nR : ℕ} {s : ℝ≥0} {t : ℚ}

/-- The killed driver read from good stopped data, frozen after `r` (on `{r < kLife}`; `0` elsewhere). -/
def frzKD (s : ℝ≥0) (t : ℚ) (r : ℝ≥0) : ℝ≥0 → {y : Y49 nL nR // IsGoodD s t y} → ℝ :=
  open scoped Classical in
  fun u x => if (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1) then
    kW (gammaD s x.1) (PD t s x.1) (min u r) else 0

theorem frzKD_props (r : ℝ≥0) :
    (∀ u, Measurable (frzKD (nL := nL) (nR := nR) s t r u)) ∧
      (∀ x, Continuous fun u => frzKD (nL := nL) (nR := nR) s t r u x) ∧
      ∀ x : {y : Y49 nL nR // IsGoodD s t y}, (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1) →
        EqOn (kPath (gammaD s x.1) (PD t s x.1)) (Bessel.realPath (frzKD s t r) x) (Icc 0 r) := by
  classical
  refine ⟨fun u => ?_, fun x => ?_, fun x ht v hv => ?_⟩
  · have e : frzKD (nL := nL) (nR := nR) s t r u = {x : {y : Y49 nL nR // IsGoodD s t y} | (r : WithTop ℝ≥0) <
        kLife (gammaD s x.1) (PD t s x.1)}.indicator ({x : {y : Y49 nL nR // IsGoodD s t y} |
          ((min u r : ℝ≥0) : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
            fun x => kW (gammaD s x.1) (PD t s x.1) (min u r)) := by
      funext x
      by_cases hx : (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)
      · have hx' : ((min u r : ℝ≥0) : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1) :=
          lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u r)) hx
        rw [indicator_of_mem (show x ∈ {x : {y : Y49 nL nR // IsGoodD s t y} | (r : WithTop ℝ≥0) <
          kLife (gammaD s x.1) (PD t s x.1)} from hx), indicator_of_mem (show x ∈
          {x : {y : Y49 nL nR // IsGoodD s t y} | ((min u r : ℝ≥0) : WithTop ℝ≥0) <
            kLife (gammaD s x.1) (PD t s x.1)} from hx')]
        simp only [frzKD, hx, ↓reduceIte]
      · rw [indicator_of_notMem (show x ∉ {x : {y : Y49 nL nR // IsGoodD s t y} | (r : WithTop ℝ≥0) <
          kLife (gammaD s x.1) (PD t s x.1)} from hx)]
        simp only [frzKD, hx, ↓reduceIte]
    rw [e]
    exact (measurable_indicator_kW_gammaD _).indicator (measurableSet_lt_kLife_gammaD r)
  · by_cases ht : (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)
    · simp only [frzKD, ht, ↓reduceIte]
      exact (x.2.killed.continuousOn_kW).comp_continuous (continuous_id.min continuous_const)
        fun u => lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u r)) ht
    · simp only [frzKD, ht, ↓reduceIte]
      exact continuous_const
  · have hrt : v.toNNReal ≤ r := by rw [Real.toNNReal_le_iff_le_coe]; exact hv.2
    simp only [Bessel.realPath, frzKD, ht, ↓reduceIte, min_eq_left hrt]
    rfl

/-- **The images of the right marks read from good stopped data are measurable.** -/
theorem measurable_indicator_kVR_gammaD (xR : Fin nR → ℝ) (j : Fin (nR + 1)) (r : ℝ≥0) :
    Measurable ({x : {y : Y49 nL nR // IsGoodD s t y} |
      (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
        fun x => kVR (gammaD s x.1) (PD t s x.1) (gXRD xR s x.1) j r) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzKD_props (nL := nL) (nR := nR) (s := s) (t := t) r
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace {y : Y49 nL nR // IsGoodD s t y}) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun x => rightImg (Bessel.realPath (frzKD s t r) x) (gXRD xR s x.1 j) r :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) hm hc
      (((measurable_pi_apply j).comp (measurable_gXRD xR s)).comp measurable_subtype_coe) r
  have heq : ({x : {y : Y49 nL nR // IsGoodD s t y} |
      (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
        fun x => kVR (gammaD s x.1) (PD t s x.1) (gXRD xR s x.1) j r) =
      {x : {y : Y49 nL nR // IsGoodD s t y} | (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
        fun x => rightImg (Bessel.realPath (frzKD s t r) x) (gXRD xR s x.1 j) r := by
    refine indicator_congr fun x hx => ?_
    rw [kVR_of_lt _ _ hx, kVRr, kImg]
    exact Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath hc x) r.coe_nonneg (hEq x hx) _
  rw [heq]
  exact hR.indicator (measurableSet_lt_kLife_gammaD r)

/-- **The images of the left marks read from good stopped data are measurable.** -/
theorem measurable_indicator_kVL_gammaD (xL : Fin nL → ℝ) (i : Fin (nL + 1)) (r : ℝ≥0) :
    Measurable ({x : {y : Y49 nL nR // IsGoodD s t y} |
      (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
        fun x => kVL (gammaD s x.1) (PD t s x.1) (gXLD xL s x.1) i r) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzKD_props (nL := nL) (nR := nR) (s := s) (t := t) r
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace {y : Y49 nL nR // IsGoodD s t y}) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun x => rightImg (Bessel.realPath (fun u x => -frzKD s t r u x) x) (-gXLD xL s x.1 i) r :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) (fun u => (hm u).neg)
      (fun x => (hc x).neg) (((measurable_pi_apply i).comp (measurable_gXLD xL s)).comp measurable_subtype_coe).neg r
  have heq : ({x : {y : Y49 nL nR // IsGoodD s t y} |
      (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
        fun x => kVL (gammaD s x.1) (PD t s x.1) (gXLD xL s x.1) i r) =
      {x : {y : Y49 nL nR // IsGoodD s t y} | (r : WithTop ℝ≥0) < kLife (gammaD s x.1) (PD t s x.1)}.indicator
        fun x => -rightImg (Bessel.realPath (fun u x => -frzKD s t r u x) x) (-gXLD xL s x.1 i) r := by
    refine indicator_congr fun x hx => ?_
    rw [kVL_of_lt _ _ hx, kVLr, kImg, neg_inj]
    refine Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath (fun x => (hc x).neg) x) r.coe_nonneg
      (fun v hv => ?_) _
    show -kPath _ _ v = -frzKD s t r v.toNNReal x
    rw [hEq x hx hv]
    rfl
  rw [heq]
  exact hR.neg.indicator (measurableSet_lt_kLife_gammaD r)

end Marks

end Word49

end InteractingSLE.Sec5.CrossCond
