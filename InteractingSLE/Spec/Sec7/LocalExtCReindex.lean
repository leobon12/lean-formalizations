/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtBStep7
import InteractingSLE.Spec.Sec2.AddMarksFlow

/-!
# Aux. lemma 55, (R3): the original stopped history is a measurable function of the two-seed history

Packet PROVE-LOCEXT-C (re-indexing R3 of `planning/handoffs/PROVE-LOCEXT-B.md`). Specification p. 247: "Every right mark in
`J` has `V^j_t ≥ x_j > 8r` and every left mark has `V^j_t ≤ x_j < −8r`. Their distances from the driver are at least
`7r` through `S`. They cannot collide during this interval." p. 251: "The stop uses only the driver, hull, and `r` …
All actual force coordinates then follow measurably from this driver and their initial data."

Through the local stop `S` of Aux. 55, the original history of an ordered force word is recovered from the
**two-seed history** (the driver and the two merged seed marks):

* the seed marks of a side (initial position `0`) all coincide with the merged seed mark of that side
  (`vL_eq_vL_of_xL_eq_zero`);
* every distant mark is the Loewner flow `U' = 2/(U − W)` of its initial position, which (at distance `≥ 7r` from the
  driver) is the flow with the cut drift `Sec2.leftMarkDrift r` / `Sec2.rightMarkDrift r`, read from the rational
  samples of the driver by the Euler scheme of `Sec2.AddMarksFlow` (`sampleFlow`, `sampleFlow_eq`).

Main declarations:

* `sampleFlow F y x t`: the mark `U' = F(U − w)`, `U 0 = y`, from rational samples `x` of the driver;
  `measurable_sampleFlow` (jointly in the samples and the time) and **`sampleFlow_eq`** (it is the solution);
* `twoSeedProj xL xR : DrivingHist nL nR → TwoSeedHist`: the two-seed history read off an original history (the
  merged seed mark of a nonempty seed side; the driver value on an empty side, a coordinate no reconstruction reads);
* `seedProj xL xR : TwoSeedHist → TwoSeedHist`: the same normalization of the empty sides on a two-seed history;
* `reindexHist xL xR r : TwoSeedHist → DrivingHist nL nR`: the re-indexing map; `measurable_reindexHist`,
  `reindexHist_seedProj`, `seedProj_twoSeedProj`;
* **`reindexHist_twoSeedProj_stoppedHistory`**: on the good event, the original history stopped at the local stop is
  `reindexHist (twoSeedProj ·)` of itself (R3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7

/-! ### Marks read from rational samples of the driver -/

section Sample

/-- The Euler approximation of level `n` of `U' = F(U − w)`, `U 0 = y`, reading the driver `w` at the dyadic
rationals `k / 2ⁿ` from its rational samples `x`. -/
def sampleEuler (F : ℝ → ℝ) (y : ℝ) (n : ℕ) (x : ℚ≥0 → ℝ) (t : ℝ) : ℝ :=
  Sec2.eulerAt F y n (fun k => x ((k : ℚ≥0) / 2 ^ n)) t

/-- **The mark read from rational samples**: the `limsup` of the Euler approximations of `U' = F(U − w)`, `U 0 = y`,
whose driver is read from its rational samples `x`. -/
def sampleFlow (F : ℝ → ℝ) (y : ℝ) (x : ℚ≥0 → ℝ) (t : ℝ) : ℝ :=
  limsup (fun n => sampleEuler F y n x t) atTop

theorem measurable_sampleEuler {F : ℝ → ℝ} (hF : Measurable F) (y : ℝ) (n : ℕ) :
    Measurable fun p : (ℚ≥0 → ℝ) × ℝ => sampleEuler F y n p.1 p.2 := by
  -- the Euler values at a countable index, jointly measurable in the samples and the index
  have hX : ∀ j : ℕ, Measurable fun x : ℚ≥0 → ℝ => x ((j : ℚ≥0) / 2 ^ n) := fun j => measurable_pi_apply _
  have hE : Measurable fun q : (ℚ≥0 → ℝ) × ℕ =>
      Sec2.eulerSeq F y (1 / 2 ^ n) (fun j => q.1 ((j : ℚ≥0) / 2 ^ n)) q.2 :=
    measurable_from_prod_countable_left fun k =>
      Sec2.measurable_eulerSeq_aux hF y (1 / 2 ^ n) k fun j _ => hX j
  have hw : Measurable fun q : (ℚ≥0 → ℝ) × ℕ => q.1 ((q.2 : ℚ≥0) / 2 ^ n) :=
    measurable_from_prod_countable_left fun k => hX k
  have hk : Measurable fun p : (ℚ≥0 → ℝ) × ℝ => (p.1, Girsanov.stepIdx n p.2) :=
    measurable_fst.prodMk ((Girsanov.measurable_stepIdx n).comp measurable_snd)
  have hg : Measurable fun p : (ℚ≥0 → ℝ) × ℝ => ((Girsanov.grid n (Girsanov.stepIdx n p.2) : ℝ≥0) : ℝ) := by
    have : Measurable fun k : ℕ => ((Girsanov.grid n k : ℝ≥0) : ℝ) := measurable_from_nat
    exact this.comp ((Girsanov.measurable_stepIdx n).comp measurable_snd)
  unfold sampleEuler Sec2.eulerAt
  exact (hE.comp hk).add ((measurable_snd.sub hg).mul (hF.comp ((hE.comp hk).sub (hw.comp hk))))

/-- `sampleFlow` is jointly measurable in the samples and the time. -/
theorem measurable_sampleFlow {F : ℝ → ℝ} (hF : Measurable F) (y : ℝ) :
    Measurable fun p : (ℚ≥0 → ℝ) × ℝ => sampleFlow F y p.1 p.2 :=
  Measurable.limsup fun n => measurable_sampleEuler hF y n

theorem coe_natCast_div_two_pow (k n : ℕ) : ((((k : ℚ≥0) / 2 ^ n : ℚ≥0)) : ℝ) = (k : ℝ) / 2 ^ n := by
  push_cast
  ring

/-- **The mark read from samples is the solution**: if `w` is continuous on `[0, t]`, `u` is a continuous solution of
`u = y + ∫ F(u − w)` on `[0, t]` (`F` Lipschitz), and the samples `x` agree with `w` at the rationals of `[0, t]`, then
`sampleFlow F y x t = u t`. -/
theorem sampleFlow_eq {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzWith K F) {y t : ℝ} (ht : 0 ≤ t) {w u : ℝ → ℝ}
    (hwc : ContinuousOn w (Icc 0 t)) (huc : ContinuousOn u (Icc 0 t))
    (hu : ∀ s ∈ Icc (0 : ℝ) t, u s = y + ∫ r in (0 : ℝ)..s, F (u r - w r))
    {x : ℚ≥0 → ℝ} (hx : ∀ q : ℚ≥0, (q : ℝ) ≤ t → x q = w q) : sampleFlow F y x t = u t := by
  have hT := Sec2.tendsto_eulerAt hF ht hwc huc hu (wk := fun n k => x ((k : ℚ≥0) / 2 ^ n)) fun n k hk => by
    have e := coe_natCast_div_two_pow k n
    rw [hx _ (by rw [e]; exact hk), e]
  exact hT.limsup_eq

end Sample

/-! ### The two-seed history of an original history, and the re-indexing map -/

section Reindex

variable {nL nR : ℕ}

open Classical in
/-- The merged seed coordinate of one side: the common value of the marks started at `0` (`v i` for a seed index `i`)
if the side has one, and the driver value `w` otherwise. -/
def seedVal {n : ℕ} (x : Fin n → ℝ) (v : Fin n → ℝ) (w : ℝ) : ℝ :=
  if h : ∃ i, x i = 0 then v h.choose else w

theorem measurable_seedVal {n : ℕ} (x : Fin n → ℝ) :
    Measurable fun p : (Fin n → ℝ) × ℝ => seedVal x p.1 p.2 := by
  by_cases h : ∃ i, x i = 0
  · simp only [seedVal, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [seedVal, h, ↓reduceDIte]
    exact measurable_snd

theorem seedVal_of_eq_zero {n : ℕ} {x : Fin n → ℝ} {v : Fin n → ℝ} {w : ℝ} (hv : ∀ i j, x i = 0 → x j = 0 → v i = v j)
    {i : Fin n} (hi : x i = 0) : seedVal x v w = v i := by
  have h : ∃ i, x i = 0 := ⟨i, hi⟩
  simp only [seedVal, h, ↓reduceDIte]
  exact hv _ _ h.choose_spec hi

/-- **The two-seed history read off an original history**: the time, the driver, and on each side the merged seed
coordinate (`seedVal`). -/
def twoSeedProj (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (y : DrivingHist nL nR) : TwoSeedHist :=
  (y.1, fun q => ((y.2 q).1, fun _ => seedVal xL (y.2 q).2.1 (y.2 q).1, fun _ => seedVal xR (y.2 q).2.2 (y.2 q).1))

open Classical in
/-- The normalization of the empty seed sides of a two-seed history (their coordinate is replaced by the driver value,
as in `twoSeedProj`). -/
def seedProj (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (y : TwoSeedHist) : TwoSeedHist :=
  (y.1, fun q => ((y.2 q).1, fun _ => if ∃ i, xL i = 0 then (y.2 q).2.1 0 else (y.2 q).1,
    fun _ => if ∃ j, xR j = 0 then (y.2 q).2.2 0 else (y.2 q).1))

open Classical in
/-- **The re-indexing map (R3)**: from a two-seed history `y = (σ, (y_q))`, the original history whose driver is that of
`y`, whose seed marks are the merged seed marks of `y`, and whose distant marks are the Loewner flows of their initial
positions under the driver (cut drifts at level `r`), at the stopped times `q ∧ σ`. -/
def reindexHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (r : ℝ) (y : TwoSeedHist) : DrivingHist nL nR :=
  (y.1, fun q =>
    ((y.2 q).1,
      fun i => if xL i = 0 then (y.2 q).2.1 0 else
        sampleFlow (Sec2.leftMarkDrift r) (xL i) (fun q' => (y.2 q').1)
          ((min (q : ℝ≥0) (y.1.untopD q) : ℝ≥0) : ℝ),
      fun j => if xR j = 0 then (y.2 q).2.2 0 else
        sampleFlow (Sec2.rightMarkDrift r) (xR j) (fun q' => (y.2 q').1)
          ((min (q : ℝ≥0) (y.1.untopD q) : ℝ≥0) : ℝ)))

theorem measurable_twoSeedProj (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Measurable (twoSeedProj xL xR) := by
  unfold twoSeedProj
  refine measurable_fst.prodMk (Measurable.of_eval fun q => ?_)
  have hq : Measurable fun y : DrivingHist nL nR => y.2 q := (measurable_pi_apply q).comp measurable_snd
  refine hq.fst.prodMk ((Measurable.of_eval fun _ => ?_).prodMk (Measurable.of_eval fun _ => ?_))
  · exact (measurable_seedVal xL).comp (hq.snd.fst.prodMk hq.fst)
  · exact (measurable_seedVal xR).comp (hq.snd.snd.prodMk hq.fst)

theorem measurable_reindexHist (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {r : ℝ} (hr : 0 < r) :
    Measurable (reindexHist xL xR r) := by
  classical
  unfold reindexHist
  refine measurable_fst.prodMk (Measurable.of_eval fun q => ?_)
  have hq : ∀ q' : ℚ≥0, Measurable fun y : TwoSeedHist => y.2 q' := fun q' =>
    (measurable_pi_apply q').comp measurable_snd
  have hx : Measurable fun y : TwoSeedHist => fun q' : ℚ≥0 => (y.2 q').1 :=
    Measurable.of_eval fun q' => (hq q').fst
  have ht : Measurable fun y : TwoSeedHist => ((min (q : ℝ≥0) (y.1.untopD q) : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp ((measurable_const.min (WithTop.measurable_untopD _)).comp measurable_fst)
  refine (hq q).fst.prodMk ((Measurable.of_eval fun i => ?_).prodMk (Measurable.of_eval fun j => ?_))
  · by_cases hi : xL i = 0
    · simp only [hi, ↓reduceIte]
      exact (measurable_pi_apply 0).comp (hq q).snd.fst
    · simp only [hi, ↓reduceIte]
      have hF : Measurable (Sec2.leftMarkDrift r) := (Sec2.lipschitzWith_leftMarkDrift hr).continuous.measurable
      have h2 := (measurable_sampleFlow hF (xL i)).comp (hx.prodMk ht)
      exact h2
  · by_cases hj : xR j = 0
    · simp only [hj, ↓reduceIte]
      exact (measurable_pi_apply 0).comp (hq q).snd.snd
    · simp only [hj, ↓reduceIte]
      have hF : Measurable (Sec2.rightMarkDrift r) := (Sec2.lipschitzWith_rightMarkDrift hr).continuous.measurable
      have h2 := (measurable_sampleFlow hF (xR j)).comp (hx.prodMk ht)
      exact h2

/-- The re-indexing map reads the seed coordinate of a side only if that side has a seed. -/
theorem reindexHist_seedProj (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (r : ℝ) (y : TwoSeedHist) :
    reindexHist xL xR r (seedProj xL xR y) = reindexHist xL xR r y := by
  classical
  refine Prod.ext rfl (funext fun q => ?_)
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) (funext fun j => ?_))
  · by_cases hi : xL i = 0
    · have h : ∃ i, xL i = 0 := ⟨i, hi⟩
      simp only [reindexHist, seedProj, hi, h, ↓reduceIte]
    · simp only [reindexHist, seedProj, hi, ↓reduceIte]
  · by_cases hj : xR j = 0
    · have h : ∃ j, xR j = 0 := ⟨j, hj⟩
      simp only [reindexHist, seedProj, hj, h, ↓reduceIte]
    · simp only [reindexHist, seedProj, hj, ↓reduceIte]

theorem seedProj_twoSeedProj (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (y : DrivingHist nL nR) :
    seedProj xL xR (twoSeedProj xL xR y) = twoSeedProj xL xR y := by
  classical
  refine Prod.ext rfl (funext fun q => Prod.ext rfl (Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)))
  · by_cases h : ∃ i, xL i = 0
    · simp only [seedProj, twoSeedProj, h, ↓reduceIte]
    · simp only [seedProj, twoSeedProj, h, ↓reduceIte, seedVal, ↓reduceDIte]
  · by_cases h : ∃ j, xR j = 0
    · simp only [seedProj, twoSeedProj, h, ↓reduceIte]
    · simp only [seedProj, twoSeedProj, h, ↓reduceIte, seedVal, ↓reduceDIte]

theorem measurable_seedProj (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Measurable (seedProj xL xR) := by
  classical
  unfold seedProj
  refine measurable_fst.prodMk (Measurable.of_eval fun q => ?_)
  have hq : Measurable fun y : TwoSeedHist => y.2 q := (measurable_pi_apply q).comp measurable_snd
  refine hq.fst.prodMk ((Measurable.of_eval fun _ => ?_).prodMk (Measurable.of_eval fun _ => ?_))
  · by_cases h : ∃ i, xL i = 0
    · simp only [h, ↓reduceIte]; exact (measurable_pi_apply 0).comp hq.snd.fst
    · simp only [h, ↓reduceIte]; exact hq.fst
  · by_cases h : ∃ j, xR j = 0
    · simp only [h, ↓reduceIte]; exact (measurable_pi_apply 0).comp hq.snd.snd
    · simp only [h, ↓reduceIte]; exact hq.fst

end Reindex

/-! ### (R3) on the good event -/

section Good

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {r : ℝ} {ω : Ω}

theorem coe_nnratCast_eq (q : ℚ≥0) : (((q : ℝ≥0)) : ℝ) = (q : ℝ) := rfl

theorem toNNReal_nnratCast (q : ℚ≥0) : ((q : ℝ)).toNNReal = (q : ℝ≥0) := by
  rw [← coe_nnratCast_eq, Real.toNNReal_coe]

/-- Through the local stop the driver stays in `[−r/4, r/4]` (at every time `≤ s` with `s ≤ S`, `s < ζ`). -/
theorem abs_W_le_of_le (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hr : IsSeedRadius xL xR r) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) (W · ω)) (hsζ : (s : ℝ≥0∞) < ζ ω) {u : ℝ≥0} (hus : u ≤ s) :
    |W u ω| ≤ r / 4 :=
  abs_le_of_le_localStopPath hg.continuousOn_W hg.W_zero hr.1.le ((WithTop.coe_le_coe.2 hus).trans hs)
    (lt_of_le_of_lt (by exact_mod_cast hus) hsζ)

/-- **A distant left mark through the stop is the flow read from the samples of the driver.** -/
theorem sampleFlow_eq_vL (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {i : Fin nL} (hi : xL i ≠ 0) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) (W · ω)) (hsζ : (s : ℝ≥0∞) < ζ ω) {t : ℝ≥0} (hts : t ≤ s)
    {x : ℚ≥0 → ℝ} (hx : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ s → x q = W q ω) :
    sampleFlow (Sec2.leftMarkDrift r) (xL i) x t = VL i t ω := by
  have hp := hg.isSLEPathUpTo
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hts) hsζ
  have hsub : ∀ u ∈ Icc (0 : ℝ) t, u.toNNReal ∈ {v : ℝ≥0 | (v : ℝ≥0∞) < ζ ω} := fun u hu =>
    toNNReal_lt_of_mem_Icc htζ hu
  have hwc : ContinuousOn (fun u : ℝ => W u.toNNReal ω) (Icc 0 t) :=
    hg.continuousOn_W.comp continuous_real_toNNReal.continuousOn hsub
  have huc : ContinuousOn (fun u : ℝ => VL i u.toNNReal ω) (Icc 0 t) :=
    (hp.continuousOn_vL i).comp continuous_real_toNNReal.continuousOn hsub
  have hle : ∀ u : ℝ, u ∈ Icc (0 : ℝ) t → u.toNNReal ≤ s := fun u hu =>
    (Real.toNNReal_le_iff_le_coe.2 hu.2).trans hts
  have hu : ∀ u ∈ Icc (0 : ℝ) t, VL i u.toNNReal ω =
      xL i + ∫ v in (0 : ℝ)..u, Sec2.leftMarkDrift r (VL i v.toNNReal ω - W v.toNNReal ω) := by
    intro u hu
    have h1 := hp.vL_eq (hsub u hu) i
    rw [Real.coe_toNNReal u hu.1] at h1
    rw [h1]
    congr 1
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hu.1] at hv
    have hv' : v ∈ Icc (0 : ℝ) t := ⟨hv.1, hv.2.trans hu.2⟩
    have h7 := seven_mul_le_sub_vL hp hF hr hi (hsub v hv') (abs_W_le_of_le hg hr hs hsζ (hle v hv'))
    rw [Sec2.leftMarkDrift_of_le (by linarith [hr.1])]
  have hx' : ∀ q : ℚ≥0, (q : ℝ) ≤ t → x q = W (q : ℝ).toNNReal ω := by
    intro q hq
    rw [toNNReal_nnratCast]
    exact hx q ((by rw [← NNReal.coe_le_coe, coe_nnratCast_eq]; exact hq : (q : ℝ≥0) ≤ t).trans hts)
  have h := sampleFlow_eq (Sec2.lipschitzWith_leftMarkDrift hr.1) t.coe_nonneg hwc huc hu hx'
  rw [h, Real.toNNReal_coe]

/-- **A distant right mark through the stop is the flow read from the samples of the driver.** -/
theorem sampleFlow_eq_vR (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {j : Fin nR} (hj : xR j ≠ 0) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) (W · ω)) (hsζ : (s : ℝ≥0∞) < ζ ω) {t : ℝ≥0} (hts : t ≤ s)
    {x : ℚ≥0 → ℝ} (hx : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ s → x q = W q ω) :
    sampleFlow (Sec2.rightMarkDrift r) (xR j) x t = VR j t ω := by
  have hp := hg.isSLEPathUpTo
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hts) hsζ
  have hsub : ∀ u ∈ Icc (0 : ℝ) t, u.toNNReal ∈ {v : ℝ≥0 | (v : ℝ≥0∞) < ζ ω} := fun u hu =>
    toNNReal_lt_of_mem_Icc htζ hu
  have hwc : ContinuousOn (fun u : ℝ => W u.toNNReal ω) (Icc 0 t) :=
    hg.continuousOn_W.comp continuous_real_toNNReal.continuousOn hsub
  have huc : ContinuousOn (fun u : ℝ => VR j u.toNNReal ω) (Icc 0 t) :=
    (hp.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hsub
  have hle : ∀ u : ℝ, u ∈ Icc (0 : ℝ) t → u.toNNReal ≤ s := fun u hu =>
    (Real.toNNReal_le_iff_le_coe.2 hu.2).trans hts
  have hu : ∀ u ∈ Icc (0 : ℝ) t, VR j u.toNNReal ω =
      xR j + ∫ v in (0 : ℝ)..u, Sec2.rightMarkDrift r (VR j v.toNNReal ω - W v.toNNReal ω) := by
    intro u hu
    have h1 := hp.vR_eq (hsub u hu) j
    rw [Real.coe_toNNReal u hu.1] at h1
    rw [h1]
    congr 1
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le hu.1] at hv
    have hv' : v ∈ Icc (0 : ℝ) t := ⟨hv.1, hv.2.trans hu.2⟩
    have h7 := seven_mul_le_vR_sub hp hF hr hj (hsub v hv') (abs_W_le_of_le hg hr hs hsζ (hle v hv'))
    rw [Sec2.rightMarkDrift_of_le (by linarith [hr.1])]
  have hx' : ∀ q : ℚ≥0, (q : ℝ) ≤ t → x q = W (q : ℝ).toNNReal ω := by
    intro q hq
    rw [toNNReal_nnratCast]
    exact hx q ((by rw [← NNReal.coe_le_coe, coe_nnratCast_eq]; exact hq : (q : ℝ≥0) ≤ t).trans hts)
  have h := sampleFlow_eq (Sec2.lipschitzWith_rightMarkDrift hr.1) t.coe_nonneg hwc huc hu hx'
  rw [h, Real.toNNReal_coe]

/-- **(R3): the original history stopped at the local stop is a measurable function of its two-seed history.** On the
good event, `reindexHist (twoSeedProj 𝒳_S) = 𝒳_S` for the stopped history `𝒳_S` of the completed driving state at the
capped local stop `S = capStop r G ζ W` of a seed radius `r`. -/
theorem reindexHist_twoSeedProj_stoppedHistory (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hω : ω ∈ G) :
    reindexHist xL xR r (twoSeedProj xL xR (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) ω)) =
      stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) ω := by
  have hg := hG ω hω
  have hp := hg.isSLEPathUpTo
  have hcap : capStop r G ζ W ω = localStopPath r (ζ ω) (W · ω) := by
    rw [capStop_eq_localStop hG hF hr hseed hω, localStop_of_mem hω]
  have hlt : (localStopPath r (ζ ω) (W · ω) : ℝ≥0∞) < ζ ω := localStopPath_lt hg.1 hF hr hseed hg.2
  obtain ⟨s, hs⟩ : ∃ s : ℝ≥0, localStopPath r (ζ ω) (W · ω) = s :=
    WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top localStopPath_le_stopHorizon) |>.imp
      fun _ h => h.symm
  have hsζ : (s : ℝ≥0∞) < ζ ω := by
    have h := hlt
    rw [hs] at h
    exact h
  have hsle : (s : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) (W · ω) := hs.ge
  have hcs : capStop r G ζ W ω = s := hcap.trans hs
  have htζ : ∀ q : ℚ≥0, ((min (q : ℝ≥0) s : ℝ≥0) : ℝ≥0∞) < ζ ω := fun q =>
    lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hsζ
  have hY : ∀ q : ℚ≥0, (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) ω).2 q =
      (W (min (q : ℝ≥0) s) ω, fun i => VL i (min (q : ℝ≥0) s) ω, fun j => VR j (min (q : ℝ≥0) s) ω) := by
    intro q
    simp only [stoppedHistory, stopAt_of_eq_coe hcs, completedState, ite_eq_left (htζ q), drivingState]
  have hY1 : (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) ω).1 = s := hcs
  have hx : ∀ q' : ℚ≥0, (q' : ℝ≥0) ≤ s →
      (fun q'' : ℚ≥0 => (twoSeedProj xL xR
        (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) ω)).2 q'' |>.1) q' = W q' ω := by
    intro q' hq'
    simp only [twoSeedProj, hY, min_eq_left hq']
  refine Prod.ext rfl (funext fun q => ?_)
  have hmin : (min (q : ℝ≥0) (((twoSeedProj xL xR
      (stoppedHistory (completedState W VL VR ζ) (capStop r G ζ W) ω)).1).untopD q)) = min (q : ℝ≥0) s := by
    simp only [twoSeedProj, hY1, WithTop.untopD_coe]
  refine Prod.ext ?_ (Prod.ext (funext fun i => ?_) (funext fun j => ?_))
  · simp only [reindexHist, twoSeedProj, hY]
  · by_cases hi : xL i = 0
    · simp only [reindexHist, hi, ↓reduceIte]
      simp only [twoSeedProj, hY]
      exact seedVal_of_eq_zero (fun a b ha hb => vL_eq_vL_of_xL_eq_zero hp ha hb (htζ q)) hi
    · simp only [reindexHist, hi, ↓reduceIte]
      rw [hmin, sampleFlow_eq_vL hg hF hr hi hsle hsζ (min_le_right _ _) hx, hY]
  · by_cases hj : xR j = 0
    · simp only [reindexHist, hj, ↓reduceIte]
      simp only [twoSeedProj, hY]
      exact seedVal_of_eq_zero (fun a b ha hb => vR_eq_vR_of_xR_eq_zero hp ha hb (htζ q)) hj
    · simp only [reindexHist, hj, ↓reduceIte]
      rw [hmin, sampleFlow_eq_vR hg hF hr hj hsle hsζ (min_le_right _ _) hx, hY]

end Good

end LocalExt

end InteractingSLE
