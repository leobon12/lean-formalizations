/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConstStop

/-!
# The image word read from stopped data is measurable (on the good stopped data)

Packet PROVE-WW-B19, for the named input `ImgMarksStatement`. On the space `YSp` of the two stopped histories:

* `measurable_alphaY`, `measurable_gammaY`: the positions of the forward line and of its image read from stopped data
  are measurable (as PROVE-WW-B17's `measurable_gCurve`);
* `RatY`, `measurableSet_RatY`: the rational pre-contact condition (`mem_preContact_iff_rat`); `IsAwayY`,
  `measurableSet_isAwayY`;
* `IsGoodY s t y` (no measurability claimed): the image curve read from `y` is a killed arc before `t`, its pre-contact
  times up to `t` are given by `RatY`, and it is continuous on each pre-contact prefix;
* on the subtype of good stopped data: `measurableSet_mem_PcY`, `measurable_indicator_capClock_gammaY`, and the killed
  word read from stopped data: **`measurable_indicator_kW_gammaY`**, `measurableSet_lt_kLife_gammaY`,
  **`measurable_indicator_kVL_gammaY`**, **`measurable_indicator_kVR_gammaY`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open Sec7.Lemma71C Sec7.Lemma71E Restart ImgWord LawUnique Sec4 ChartConst MartChar.RealFlow

namespace ChartConst

/-- The rational pre-contact condition read from stopped data. -/
def RatY (s q : ℚ) : Set YSp :=
  {y | ∃ m : ℕ, ∀ u v : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
    1 / ((m : ℝ) + 1) ≤ ‖alphaY y u - negInv (frzLine s y.2 v)‖}

/-- The away condition of the announcing times, read from stopped data. -/
def IsAwayY (s : ℚ) (n : ℕ) (y : YSp) (q : ℚ) : Prop :=
  ((0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n) ∧ ∀ u v : ℚ, (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
    1 / ((n : ℝ) + 1) ≤ ‖alphaY y u - negInv (frzLine s y.2 v)‖

/-- **Good stopped data** (no measurability claimed): the image curve is a killed arc before `t`, the rational
pre-contact times up to `t` are given by `RatY`, the curve is continuous on each pre-contact prefix, the forward line
is a continuous curve from `0` into `ℍ` on `[0, t]`, and the reverse slit is a simple proper arc with closed
reflection. -/
structure IsGoodY (s t : ℚ) (y : YSp) : Prop where
  killed : IsKilledArc (gammaY s y) (PY t s y)
  rat : ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ t → ((q : ℝ) ∈ PcY s y ↔ y ∈ RatY s q)
  cont : ∀ q : ℚ, (0 : ℝ) ≤ q → (q : ℝ) ≤ t → (q : ℝ) ∈ PcY s y → ContinuousOn (gammaY s y) (Icc 0 q)
  alphaCont : ContinuousOn (alphaY y) (Icc 0 t)
  alpha0 : alphaY y 0 = 0
  alphaH : ∀ u ∈ Ioc (0 : ℝ) t, alphaY y u ∈ H
  beta : IsProperArc (frzLine s y.2)
  gClosed : IsClosed (GY s y)

end ChartConst

section Y

variable {s t : ℚ}

theorem measurable_alphaY (u : ℝ) : Measurable fun y : YSp => alphaY y u :=
  (LP.measurable_traceAt _).comp (measurable_pi_iff.2 fun r => (measurable_regPath_apply r).comp measurable_fst)

theorem measurable_gammaY (hs : 0 < s) (q : ℝ) : Measurable fun y : YSp => gammaY s y q := by
  by_cases hq : q ≤ 0
  · simp only [gammaY, imgCurve, hq, ↓reduceIte]
    exact measurable_const
  · simp only [gammaY, imgCurve, hq, ↓reduceIte, revChart]
    have hy : Measurable fun y : YSp => negInv (alphaY y q) := measurable_negInv.comp (measurable_alphaY q)
    have h := (Exist.StagedLaw.measurable_fwdMap_param (W := fun y : YSp => revDrv0 s y.2)
      (fun y => continuous_revDrv0 y.2) (fun t => (measurable_revDrv0_apply t).comp measurable_snd)
      (fun y => by simp [revDrv0]) (τ := fun _ => (s : ℝ)) measurable_const (fun _ => by exact_mod_cast hs.le)
      hy).1
    exact measurable_negInv.comp h

theorem measurable_norm_alphaY_sub (u v : ℝ) :
    Measurable fun y : YSp => ‖alphaY y u - negInv (frzLine s y.2 v)‖ :=
  ((measurable_alphaY u).sub (measurable_negInv.comp ((measurable_frzLine s v).comp measurable_snd))).norm

theorem measurableSet_RatY (q : ℚ) : MeasurableSet (RatY s q) := by
  have e : RatY s q = ⋃ m : ℕ, ⋂ u : ℚ, ⋂ v : ℚ, {y : YSp | (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v →
      (v : ℝ) ≤ s → 1 / ((m : ℝ) + 1) ≤ ‖alphaY y u - negInv (frzLine s y.2 v)‖} := by
    ext y; simp [RatY]
  rw [e]
  refine MeasurableSet.iUnion fun m => MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => ?_
  by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q ∧ (0 : ℝ) < v ∧ (v : ℝ) ≤ s
  · obtain ⟨h1, h2, h3, h4⟩ := hc
    simp only [h1, h2, h3, h4, forall_const]
    exact measurableSet_le measurable_const (measurable_norm_alphaY_sub _ _)
  · have e : {y : YSp | (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
        1 / ((m : ℝ) + 1) ≤ ‖alphaY y u - negInv (frzLine s y.2 v)‖} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2 h3 h4
      exact absurd ⟨h1, h2, h3, h4⟩ hc
    rw [e]
    exact MeasurableSet.univ

theorem measurableSet_isAwayY (n : ℕ) (q : ℚ) : MeasurableSet {y : YSp | IsAwayY s n y q} := by
  have e : {y : YSp | IsAwayY s n y q} = {_y | (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ n} ∩ ⋂ u : ℚ, ⋂ v : ℚ,
      {y : YSp | (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
        1 / ((n : ℝ) + 1) ≤ ‖alphaY y u - negInv (frzLine s y.2 v)‖} := by
    ext y; simp [IsAwayY]
  rw [e]
  refine MeasurableSet.const _ |>.inter (MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => ?_)
  by_cases hc : (0 : ℝ) ≤ u ∧ (u : ℝ) ≤ q ∧ (0 : ℝ) < v ∧ (v : ℝ) ≤ s
  · obtain ⟨h1, h2, h3, h4⟩ := hc
    simp only [h1, h2, h3, h4, forall_const]
    exact measurableSet_le measurable_const (measurable_norm_alphaY_sub _ _)
  · have e : {y : YSp | (0 : ℝ) ≤ u → (u : ℝ) ≤ q → (0 : ℝ) < v → (v : ℝ) ≤ s →
        1 / ((n : ℝ) + 1) ≤ ‖alphaY y u - negInv (frzLine s y.2 v)‖} = univ := by
      ext y
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2 h3 h4
      exact absurd ⟨h1, h2, h3, h4⟩ hc
    rw [e]
    exact MeasurableSet.univ

end Y

/-! ### On the good stopped data -/

section Good

variable {s t : ℚ}

/-- The rational pre-contact events (up to `t`) of good stopped data are measurable. -/
theorem measurableSet_mem_PcY (q : ℚ) (hq0 : (0 : ℝ) ≤ q) (hqt : (q : ℝ) ≤ t) :
    MeasurableSet {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1} := by
  have e : {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1} = Subtype.val ⁻¹' RatY s q := by
    ext x
    exact x.2.rat q hq0 hqt
  rw [e]
  exact measurable_subtype_coe (measurableSet_RatY q)

/-- The rational pre-contact events before `t` of good stopped data are measurable. -/
theorem measurableSet_mem_PY (q : ℚ) :
    MeasurableSet {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PY t s x.1} := by
  by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t
  · have e : {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PY t s x.1} =
        {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1} := by
      ext x
      simp only [PY, mem_ofPred_eq, mem_inter_iff, mem_Iio, hq.2, and_true]
    rw [e]
    exact measurableSet_mem_PcY q hq.1 hq.2.le
  · have e : {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PY t s x.1} = ∅ := by
      ext x
      simp only [PY, PcY, preContact, mem_ofPred_eq, mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h0, -⟩, h1⟩
      exact hq ⟨h0, h1⟩
    rw [e]
    exact MeasurableSet.empty

/-- The capacity clock of good stopped data at a rational pre-contact time up to `t` is measurable. -/
theorem measurable_indicator_capClock_gammaY (hs : 0 < s) (q : ℚ) (hq0 : (0 : ℝ) ≤ q) (hqt : (q : ℝ) ≤ t) :
    Measurable ({x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1}.indicator
      fun x => capClock (gammaY s x.1) q) := by
  classical
  set A := {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1} with hAdef
  have hA : MeasurableSet A := measurableSet_mem_PcY q hq0 hqt
  set Γ : {y : YSp // IsGoodY s t y} → ℝ≥0 → ℂ := fun x r =>
    if x ∈ A then gammaY s x.1 (min (r : ℝ) q) else 0 with hΓdef
  have hΓc : ∀ x, Continuous (Γ x) := by
    intro x
    by_cases hx : x ∈ A
    · simp only [hΓdef, hx, ↓reduceIte]
      exact (x.2.cont q hq0 hqt hx).comp_continuous (NNReal.continuous_coe.min continuous_const)
        fun r => ⟨le_min r.coe_nonneg hq0, min_le_right _ _⟩
    · simp only [hΓdef, hx, ↓reduceIte]
      exact continuous_const
  have hΓm : ∀ r, Measurable fun x => Γ x r := fun r =>
    Measurable.ite hA ((measurable_gammaY hs _).comp measurable_subtype_coe) measurable_const
  have hmeas := measurable_hcapHit_image hΓc hΓm (q : ℝ).toNNReal
  have heq : A.indicator (fun x => capClock (gammaY s x.1) q) =
      A.indicator fun x => (WholeField.hcapHit (Γ x '' Icc 0 (q : ℝ).toNNReal)).toReal / 2 := by
    refine indicator_congr fun x hx => ?_
    have himg : gammaY s x.1 '' Icc 0 q = Γ x '' Icc 0 (q : ℝ).toNNReal := by
      rw [image_Icc_real_eq hq0]
      refine image_congr fun r hr => ?_
      have hrq : (r : ℝ) ≤ q := by
        have := hr.2
        rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0] at this
      simp only [hΓdef, hx, ↓reduceIte, min_eq_left hrq]
    have h0 : (Γ x 0).im ≤ 0 := by
      simp only [hΓdef, hx, ↓reduceIte, NNReal.coe_zero, min_eq_left hq0, gammaY, imgCurve, le_refl,
        Complex.zero_im]
    rw [hcapHit_image_eq (hΓc x).continuousOn h0, ← himg]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (gammaY s x.1 '' Icc 0 q)) := by
      rw [himg, ConformalImage.hcapSet_eq (isHPHull_fillH_image (hΓc x).continuousOn h0)]
      exact HPHull.hcap_nonneg _
    rw [ENNReal.toReal_ofReal hnn, capClock]
  rw [heq]
  exact ((ENNReal.measurable_toReal.comp hmeas).div_const _).indicator hA

end Good

/-! ### The killed word read from good stopped data -/

section Word

variable {s t : ℚ}

theorem measurable_indicator_capClock_gammaY_PY (hs : 0 < s) (q : ℚ) :
    Measurable ({x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PY t s x.1}.indicator
      fun x => capClock (gammaY s x.1) q) := by
  by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) < t
  · have e : {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PY t s x.1} =
        {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PcY s x.1} := by
      ext x
      simp only [PY, mem_ofPred_eq, mem_inter_iff, mem_Iio, hq.2, and_true]
    rw [e]
    exact measurable_indicator_capClock_gammaY hs q hq.1 hq.2.le
  · have e : {x : {y : YSp // IsGoodY s t y} | (q : ℝ) ∈ PY t s x.1} = ∅ := by
      ext x
      simp only [PY, PcY, preContact, mem_ofPred_eq, mem_inter_iff, mem_Iio, mem_empty_iff_false, iff_false]
      rintro ⟨⟨h0, -⟩, h1⟩
      exact hq ⟨h0, h1⟩
    rw [e, indicator_empty]
    exact measurable_const

theorem measurableSet_lt_kLife_gammaY (hs : 0 < s) (r : ℝ≥0) :
    MeasurableSet {x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)} :=
  measurableSet_lt_kLife (fun x => x.2.killed) measurableSet_mem_PY
    (measurable_indicator_capClock_gammaY_PY hs) r

/-- **The killed driver read from good stopped data is measurable.** -/
theorem measurable_indicator_kW_gammaY (hs : 0 < s) (r : ℝ≥0) :
    Measurable ({x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
      fun x => kW (gammaY s x.1) (PY t s x.1) r) :=
  measurable_indicator_kW_of_base (fun x => x.2.killed) measurableSet_mem_PY
    (measurable_indicator_capClock_gammaY_PY hs) (fun q => (measurable_gammaY hs q).comp measurable_subtype_coe) r

theorem measurable_gXLY (s : ℚ) : Measurable fun y : YSp => gXLY s y := by
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · simp only [gXLY, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact measurable_const
  · simp only [gXLY, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact measurable_const.div ((measurable_frzVR s).comp measurable_snd)

theorem measurable_gXRY (s : ℚ) : Measurable fun y : YSp => gXRY s y := by
  refine measurable_pi_iff.2 fun j => ?_
  fin_cases j
  · simp only [gXRY, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact measurable_const
  · simp only [gXRY, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact measurable_const.div ((measurable_frzVL s).comp measurable_snd)

/-- The killed driver read from good stopped data, frozen after `r` (on `{r < kLife}`; `0` elsewhere). -/
private def frzK (s t : ℚ) (r : ℝ≥0) : ℝ≥0 → {y : YSp // IsGoodY s t y} → ℝ :=
  open scoped Classical in
  fun u x => if (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1) then kW (gammaY s x.1) (PY t s x.1) (min u r)
    else 0

private theorem frzK_props (hs : 0 < s) (r : ℝ≥0) :
    (∀ u, Measurable (frzK s t r u)) ∧ (∀ x, Continuous fun u => frzK s t r u x) ∧
      ∀ x : {y : YSp // IsGoodY s t y}, (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1) →
        EqOn (kPath (gammaY s x.1) (PY t s x.1)) (Bessel.realPath (frzK s t r) x) (Icc 0 r) := by
  classical
  refine ⟨fun u => ?_, fun x => ?_, fun x ht v hv => ?_⟩
  · have e : frzK s t r u = {x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) <
        kLife (gammaY s x.1) (PY t s x.1)}.indicator ({x : {y : YSp // IsGoodY s t y} |
          ((min u r : ℝ≥0) : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
            fun x => kW (gammaY s x.1) (PY t s x.1) (min u r)) := by
      funext x
      by_cases hx : (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)
      · have hx' : ((min u r : ℝ≥0) : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1) :=
          lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u r)) hx
        rw [indicator_of_mem (show x ∈ {x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) <
          kLife (gammaY s x.1) (PY t s x.1)} from hx), indicator_of_mem (show x ∈ {x : {y : YSp // IsGoodY s t y} |
          ((min u r : ℝ≥0) : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)} from hx')]
        simp only [frzK, hx, ↓reduceIte]
      · rw [indicator_of_notMem (show x ∉ {x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) <
          kLife (gammaY s x.1) (PY t s x.1)} from hx)]
        simp only [frzK, hx, ↓reduceIte]
    rw [e]
    exact (measurable_indicator_kW_gammaY hs _).indicator (measurableSet_lt_kLife_gammaY hs r)
  · by_cases ht : (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)
    · simp only [frzK, ht, ↓reduceIte]
      exact (x.2.killed.continuousOn_kW).comp_continuous (continuous_id.min continuous_const)
        fun u => lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u r)) ht
    · simp only [frzK, ht, ↓reduceIte]
      exact continuous_const
  · have hrt : v.toNNReal ≤ r := by rw [Real.toNNReal_le_iff_le_coe]; exact hv.2
    simp only [Bessel.realPath, frzK, ht, ↓reduceIte, min_eq_left hrt]
    rfl

/-- **The images of the right marks read from good stopped data are measurable.** -/
theorem measurable_indicator_kVR_gammaY (hs : 0 < s) (j : Fin 2) (r : ℝ≥0) :
    Measurable ({x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
      fun x => kVR (gammaY s x.1) (PY t s x.1) (gXRY s x.1) j r) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzK_props (t := t) hs r
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace {y : YSp // IsGoodY s t y}) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun x => rightImg (Bessel.realPath (frzK s t r) x) (gXRY s x.1 j) r :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) hm hc
      (((measurable_pi_apply j).comp (measurable_gXRY s)).comp measurable_subtype_coe) r
  have heq : ({x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
      fun x => kVR (gammaY s x.1) (PY t s x.1) (gXRY s x.1) j r) =
      {x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
        fun x => rightImg (Bessel.realPath (frzK s t r) x) (gXRY s x.1 j) r := by
    refine indicator_congr fun x hx => ?_
    rw [kVR_of_lt _ _ hx, kVRr, kImg]
    exact Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath hc x) r.coe_nonneg (hEq x hx) _
  rw [heq]
  exact hR.indicator (measurableSet_lt_kLife_gammaY hs r)

/-- **The images of the left marks read from good stopped data are measurable.** -/
theorem measurable_indicator_kVL_gammaY (hs : 0 < s) (i : Fin 2) (r : ℝ≥0) :
    Measurable ({x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
      fun x => kVL (gammaY s x.1) (PY t s x.1) (gXLY s x.1) i r) := by
  classical
  obtain ⟨hm, hc, hEq⟩ := frzK_props (t := t) hs r
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace {y : YSp // IsGoodY s t y}) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun x => rightImg (Bessel.realPath (fun u x => -frzK s t r u x) x) (-gXLY s x.1 i) r :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) (fun u => (hm u).neg)
      (fun x => (hc x).neg) (((measurable_pi_apply i).comp (measurable_gXLY s)).comp measurable_subtype_coe).neg r
  have heq : ({x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
      fun x => kVL (gammaY s x.1) (PY t s x.1) (gXLY s x.1) i r) =
      {x : {y : YSp // IsGoodY s t y} | (r : WithTop ℝ≥0) < kLife (gammaY s x.1) (PY t s x.1)}.indicator
        fun x => -rightImg (Bessel.realPath (fun u x => -frzK s t r u x) x) (-gXLY s x.1 i) r := by
    refine indicator_congr fun x hx => ?_
    rw [kVL_of_lt _ _ hx, kVLr, kImg, neg_inj]
    refine Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath (fun x => (hc x).neg) x) r.coe_nonneg
      (fun v hv => ?_) _
    show -kPath _ _ v = -frzK s t r v.toNNReal x
    rw [hEq x hx hv]
    rfl
  rw [heq]
  exact hR.neg.indicator (measurableSet_lt_kLife_gammaY hs r)

end Word

end InteractingSLE.WangWu
