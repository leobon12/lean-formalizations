/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordRef
import InteractingSLE.Spec.Sec2.MartingaleFinalGeom

/-!
# The pocket word's force coordinates as geometric images of random marks

Packet PROVE-STRIPSYS10 (specification §7.4.1: Aux. lemmas 121–122, pp. 388–391, and the proof of Lemma 7.25, p. 414;
the coordinates of `Sec7.PocketWord.pocketWordEvolution_of_aux122`).

In the pocket chart the force coordinates of the relative traversal are the images of the initial boundary marks
(the seeds at `0⁻`, `0⁺` and the angle-change points of the two incoming sides, Aux. lemmas 119–121) under the real
Loewner flow of the relative driver. PROVE-SEC2-MART2 proved every deterministic property of such geometric images for
deterministic marks (`MartChar.geomL`, `MartChar.geomR`). This file writes them for **random** initial marks
`xL ω`, `xR ω` (measurable at time `0`), and proves the hypotheses that `pocketWordEvolution_of_aux122` asks of the
coordinates:

* `measurable_rightImg_realPath_of_measurable`: adaptedness with a random `𝓕₀`-measurable start
  (`MartChar.measurable_rightImg_realPath` with the start inside the countable description);
* `geomLW`, `geomRW`, and for every `ω`: seeds, signs, order with the driver, force paths, monotonicity in time and
  index, merging, and **left–right separation at positive times** (from `RealFlow.rightImg_add_rightImg_neg_ge`:
  `V^R_t − V^L_t ≥ 4√t`);
* **`pocketWordEvolution_of_geom`**: `Lemma725Ref.PocketWordEvolution` from a continuous adapted relative driver with a
  generating trace on every finite interval, random `𝓕₀`-measurable ordered marks with the seeds at `0`, the common
  phase, and the two martingale inputs (R.5 with Aux. lemmas 27–29). These four inputs (driver, marks, phase, means)
  are what remains of the pocket coordinates.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE.Sec7.PocketTraversal

open MartChar MartChar.RealFlow

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-! ### Adaptedness with a random start -/

/-- **The geometric image of a random `𝓕₀`-measurable start is adapted** (`MartChar.measurable_rightImg_realPath`
with a random start: the event `{x < q}` of its countable description is `𝓕_t`-measurable). -/
theorem measurable_rightImg_realPath_of_measurable (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hWc : ∀ ω, Continuous (W · ω)) {x : Ω → ℝ} (hx : Measurable[𝓕 0] x) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => rightImg (Bessel.realPath W ω) (x ω) t := by
  refine measurable_of_Iio (mδ := 𝓕 t) fun c => ?_
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hset : (fun ω => rightImg (Bessel.realPath W ω) (x ω) t) ⁻¹' Iio c
      = ⋃ q : ℚ, ⋃ n : ℕ, {ω : Ω | x ω < q} ∩
        {ω | ∀ s ∈ Icc 0 (t : ℝ), ε n ≤ regFlow (Bessel.realPath W ω) (ε n) q s} ∩
        {ω | Bessel.realPath W ω t + regFlow (Bessel.realPath W ω) (ε n) q t < c} := by
    ext ω
    have hw := Bessel.continuous_realPath hWc ω
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hV
      obtain ⟨y, hxy, hy, hlt⟩ := exists_lt_of_rightImg_lt hw t.coe_nonneg hV
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + (c - gImg (Bessel.realPath W ω) y t)
        by linarith)
      have hq : Alive (Bessel.realPath W ω) q t := hy.of_le hw hq1.le t.coe_nonneg
      have hgq := abs_gImg_sub_le hw t.coe_nonneg hy hq
      obtain ⟨n, hn⟩ := (alive_iff_regFlow hw t.coe_nonneg).1 hq
      refine ⟨q, n, ⟨hxy.trans hq1, hn⟩, ?_⟩
      rw [← cflow_eq_regFlow hw (hε0 n) hn ⟨t.coe_nonneg, le_rfl⟩]
      have := le_abs_self (gImg (Bessel.realPath W ω) (q : ℝ) t - gImg (Bessel.realPath W ω) y t)
      rw [abs_of_pos (sub_pos.2 hq1)] at hgq
      simp only [gImg] at this hgq hlt hq2 ⊢
      linarith
    · rintro ⟨q, n, ⟨hxq, hn⟩, hlt⟩
      have hq : Alive (Bessel.realPath W ω) q t := ⟨_, isPosSol_regFlow hw (hε0 n) hn⟩
      refine (rightImg_le_gImg hw t.coe_nonneg hxq hq).trans_lt ?_
      rw [gImg, cflow_eq_regFlow hw (hε0 n) hn ⟨t.coe_nonneg, le_rfl⟩]
      exact hlt
  rw [hset]
  have hxt : Measurable[𝓕 t] x := hx.mono (𝓕.mono (show (0 : ℝ≥0) ≤ t from zero_le)) le_rfl
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun n => ?_
  refine ((measurableSet_lt hxt measurable_const).inter
    (measurableSet_forall_le_regFlow hWa hWc (hε0 n) q t)).inter ?_
  have h1 : Measurable[𝓕 t] fun ω => Bessel.realPath W ω t := by
    simp only [Bessel.realPath, Real.toNNReal_coe]
    exact hWa t
  exact measurableSet_lt (h1.add (measurable_regFlow_realPath hWa hWc (hε0 n) q t))
    measurable_const

/-! ### The geometric images of random marks -/

variable {nL nR : ℕ}

/-- **The right force coordinates**: `V^{j,R}_t(ω) = rightImg (W·ω) (x^R_j(ω)) t`. -/
def geomRW (W : ℝ≥0 → Ω → ℝ) (xR : Ω → Fin nR → ℝ) : Fin nR → ℝ≥0 → Ω → ℝ :=
  fun j t ω => rightImg (Bessel.realPath W ω) (xR ω j) t

/-- **The left force coordinates**, by reflection: `V^{i,L}_t(ω) = −rightImg (−W·ω) (−x^L_i(ω)) t`. -/
def geomLW (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) : Fin nL → ℝ≥0 → Ω → ℝ :=
  fun i t ω => -rightImg (Bessel.realPath (fun t ω => -W t ω) ω) (-xL ω i) t

theorem stronglyAdapted_geomRW (hWa : StronglyAdapted 𝓕 W) (hWc : ∀ ω, Continuous (W · ω))
    {xR : Ω → Fin nR → ℝ} (hx : Measurable[𝓕 0] xR) (j : Fin nR) : StronglyAdapted 𝓕 (geomRW W xR j) :=
  fun t => (measurable_rightImg_realPath_of_measurable (fun t => (hWa t).measurable) hWc
    ((measurable_pi_apply j).comp hx) t).stronglyMeasurable

theorem stronglyAdapted_geomLW (hWa : StronglyAdapted 𝓕 W) (hWc : ∀ ω, Continuous (W · ω))
    {xL : Ω → Fin nL → ℝ} (hx : Measurable[𝓕 0] xL) (i : Fin nL) : StronglyAdapted 𝓕 (geomLW W xL i) :=
  fun t => (measurable_rightImg_realPath_of_measurable (fun t => (hWa t).measurable.neg)
    (fun ω => (hWc ω).neg) ((measurable_pi_apply i).comp hx).neg t).neg.stronglyMeasurable

section Pathwise

variable (hWc : ∀ ω, Continuous (W · ω))
include hWc

theorem isForcePath_geomRW (xR : Ω → Fin nR → ℝ) (ω : Ω) (j : Fin nR) :
    IsForcePath (fun t => W t ω) (fun t => geomRW W xR j t ω) := by
  have h := isForcePath_rightImg (Bessel.continuous_realPath hWc ω) (xR ω j)
  simp only [realPath_coe] at h
  exact h

theorem isForcePath_geomLW (xL : Ω → Fin nL → ℝ) (ω : Ω) (i : Fin nL) :
    IsForcePath (fun t => W t ω) (fun t => geomLW W xL i t ω) := by
  have hWc' : ∀ ω, Continuous fun t => -W t ω := fun ω => (hWc ω).neg
  have h := (isForcePath_rightImg (Bessel.continuous_realPath hWc' ω) (-xL ω i)).neg
  simp only [realPath_coe, neg_neg] at h
  exact h

theorem le_geomRW (xR : Ω → Fin nR → ℝ) (ω : Ω) (t : ℝ≥0) (j : Fin nR) : W t ω ≤ geomRW W xR j t ω := by
  have h := le_rightImg (Bessel.continuous_realPath hWc ω) (xR ω j) t.coe_nonneg
  rw [realPath_coe] at h
  exact h

theorem geomLW_le (xL : Ω → Fin nL → ℝ) (ω : Ω) (t : ℝ≥0) (i : Fin nL) : geomLW W xL i t ω ≤ W t ω := by
  have hc : ∀ ω, Continuous fun t => -W t ω := fun ω => (hWc ω).neg
  have h := le_rightImg (Bessel.continuous_realPath hc ω) (-xL ω i) t.coe_nonneg
  rw [realPath_coe] at h
  simp only [geomLW]
  linarith

theorem geomRW_zero (hW0 : ∀ ω, W 0 ω = 0) {xR : Ω → Fin nR → ℝ} {ω : Ω} {j : Fin nR} (hx : 0 ≤ xR ω j) :
    geomRW W xR j 0 ω = xR ω j := by
  have hw0 : Bessel.realPath W ω 0 = 0 := by simp [Bessel.realPath, hW0 ω]
  simp only [geomRW, NNReal.coe_zero]
  exact rightImg_zero (Bessel.continuous_realPath hWc ω) hw0 hx

theorem geomLW_zero (hW0 : ∀ ω, W 0 ω = 0) {xL : Ω → Fin nL → ℝ} {ω : Ω} {i : Fin nL} (hx : xL ω i ≤ 0) :
    geomLW W xL i 0 ω = xL ω i := by
  have hc : ∀ ω, Continuous fun t => -W t ω := fun ω => (hWc ω).neg
  have hw0 : Bessel.realPath (fun t ω => -W t ω) ω 0 = 0 := by simp [Bessel.realPath, hW0 ω]
  simp only [geomLW, NNReal.coe_zero]
  rw [rightImg_zero (Bessel.continuous_realPath hc ω) hw0 (by linarith), neg_neg]

theorem monotone_geomRW (xR : Ω → Fin nR → ℝ) (ω : Ω) (j : Fin nR) :
    Monotone fun t => geomRW W xR j t ω := fun a _ hab =>
  rightImg_mono_time (Bessel.continuous_realPath hWc ω) _ a.coe_nonneg hab

theorem antitone_geomLW (xL : Ω → Fin nL → ℝ) (ω : Ω) (i : Fin nL) :
    Antitone fun t => geomLW W xL i t ω := fun a b hab => by
  have hc : ∀ ω, Continuous fun t => -W t ω := fun ω => (hWc ω).neg
  simp only [geomLW, neg_le_neg_iff]
  exact rightImg_mono_time (Bessel.continuous_realPath hc ω) _ a.coe_nonneg hab

theorem monotone_index_geomRW {xR : Ω → Fin nR → ℝ} {ω : Ω} (hx : Monotone (xR ω)) (t : ℝ≥0) :
    Monotone fun j => geomRW W xR j t ω := fun _ _ hjk =>
  rightImg_mono_index (Bessel.continuous_realPath hWc ω) t.coe_nonneg (hx hjk)

theorem antitone_index_geomLW {xL : Ω → Fin nL → ℝ} {ω : Ω} (hx : Antitone (xL ω)) (t : ℝ≥0) :
    Antitone fun i => geomLW W xL i t ω := fun _ _ hik => by
  have hc : ∀ ω, Continuous fun t => -W t ω := fun ω => (hWc ω).neg
  simp only [geomLW, neg_le_neg_iff]
  exact rightImg_mono_index (Bessel.continuous_realPath hc ω) t.coe_nonneg (neg_le_neg (hx hik))

theorem geomRW_merge (xR : Ω → Fin nR → ℝ) (ω : Ω) (j k : Fin nR) (s t : ℝ≥0) (hst : s ≤ t)
    (heq : geomRW W xR j s ω = geomRW W xR k s ω) : geomRW W xR j t ω = geomRW W xR k t ω :=
  rightImg_eq_of_eq' (Bessel.continuous_realPath hWc ω) s.coe_nonneg hst heq

theorem geomLW_merge (xL : Ω → Fin nL → ℝ) (ω : Ω) (i k : Fin nL) (s t : ℝ≥0) (hst : s ≤ t)
    (heq : geomLW W xL i s ω = geomLW W xL k s ω) : geomLW W xL i t ω = geomLW W xL k t ω := by
  have hc : ∀ ω, Continuous fun t => -W t ω := fun ω => (hWc ω).neg
  simp only [geomLW, neg_inj] at heq ⊢
  exact rightImg_eq_of_eq' (Bessel.continuous_realPath hc ω) s.coe_nonneg hst heq

/-- **Left and right coordinates are separated at positive times** (`V^R_t − V^L_t ≥ 4√t`, specification p. 37:
"Left and right groups are strictly separated at positive times"), so they never meet the driver together. -/
theorem geom_sep (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (i : Fin nL)
    (j : Fin nR) (hL : geomLW W xL i t ω = W t ω) : geomRW W xR j t ω ≠ W t ω := by
  intro hR
  have h := rightImg_add_rightImg_neg_ge (Bessel.continuous_realPath hWc ω) (xR ω j) (-xL ω i) t.coe_nonneg
  have hneg : (fun s => -Bessel.realPath W ω s) = Bessel.realPath (fun t ω => -W t ω) ω := rfl
  rw [hneg] at h
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 (by exact_mod_cast ht)
  simp only [geomLW, geomRW] at hL hR
  linarith

end Pathwise

/-! ### Lemma 7.25's pocket-word evolution from the geometric coordinates -/

open PocketWord MartChar PhaseSel in
/-- **Lemma 7.25's pocket-word evolution from a relative driver and random marks** (`pocketWordEvolution_of_aux122`
with the force coordinates the geometric images of the marks). On a standard Borel probability space with a
right-continuous filtration: a continuous adapted relative driver `W` with `W 0 = 0` and a generating trace on every
finite interval; random `𝓕₀`-measurable marks with the seeds at `0`, the other left marks negative and the other right
marks positive, ordered in the index; a common phase `d_t ∈ 2πχℤ`; and the two martingale inputs `hmart`, `hcont` for
the geometric coordinates. -/
theorem pocketWordEvolution_of_geom {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL) (hLd : rL < κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < κ / 2 - 4) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hρL : ρL 0 = rL) (hρR : ρR 0 = rR) {Ω : Type v} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hxLm : Measurable[𝓕 0] xL) (hxRm : Measurable[𝓕 0] xR)
    (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0)
    (hxLd : ∀ ω (i : Fin nL), xL ω i.succ < 0) (hxRd : ∀ ω (j : Fin nR), 0 < xR ω j.succ)
    (hxLi : ∀ ω, Antitone (xL ω)) (hxRi : ∀ ω, Monotone (xR ω))
    {d : ℝ≥0 → Ω → ℝ} (hd : ∀ (t : ℝ≥0) ω, 0 < t → ∃ n : ℤ, d t ω = n * phaseStep κ)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => geomLW W xL i t ω - W t ω) (fun j => geomRW W xR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean κ (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T'))
    (htr : ∀ ω (T : ℝ≥0), ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η) :
    Lemma725Ref.PocketWordEvolution.{v} κ rL rR := by
  have hWc' : ∀ ω, Continuous (W · ω) := hWc
  refine pocketWordEvolution_of_aux122 hκ hL hLd hR hRd hρL hρR (VL := geomLW W xL) (VR := geomRW W xR)
    (fun ω => ?_) (fun ω => ?_) (fun ω i => ?_) (fun ω j => ?_) hW0 hWc hWa
    (stronglyAdapted_geomLW hWa hWc' hxLm) (stronglyAdapted_geomRW hWa hWc' hxRm)
    (fun ω t i => geomLW_le hWc' xL ω t i) (fun ω t j => le_geomRW hWc' xR ω t j)
    (isForcePath_geomLW hWc' xL) (isForcePath_geomRW hWc' xR) (antitone_geomLW hWc' xL)
    (monotone_geomRW hWc' xR) (fun ω t => antitone_index_geomLW hWc' (hxLi ω) t)
    (fun ω t => monotone_index_geomRW hWc' (hxRi ω) t) (fun ω i j s t hst => geomLW_merge hWc' xL ω i j s t hst)
    (fun ω i j s t hst => geomRW_merge hWc' xR ω i j s t hst) (fun ω t ht i j => geom_sep hWc' xL xR ω t ht i j)
    hd hmart hcont htr
  · rw [geomLW_zero hWc' hW0 (le_of_eq (hseedL ω)), hseedL ω]
  · rw [geomRW_zero hWc' hW0 (le_of_eq (hseedR ω).symm), hseedR ω]
  · rw [geomLW_zero hWc' hW0 (hxLd ω i).le]
    exact hxLd ω i
  · rw [geomRW_zero hWc' hW0 (hxRd ω j).le]
    exact hxRd ω j

end InteractingSLE.Sec7.PocketTraversal
