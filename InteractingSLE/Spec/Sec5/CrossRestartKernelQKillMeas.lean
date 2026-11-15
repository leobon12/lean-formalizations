/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQKill
import InteractingSLE.Spec.Sec7.PocketTraversalMeas
import InteractingSLE.Spec.Sec7.Lemma71EPrefix
import InteractingSLE.Spec.Sec7.PocketTraversalCoords

/-!
# Lemma 4.7 in the chart `Q`: the killed word of a random killed curve is measurable

Packet PROVE-CFRESTART4, item D1 (measurability). For a family of killed (possibly non-simple) curves
(`KernelQ.IsKilledCurve`) whose rational pre-killing events, rational capacity clocks and rational positions are
measurable, this file proves (the non-simple form of WangWu's `ReverseContactMartPrefix` and of GLUECOND5's
`CrossCondWordMeas`; the driver formula is `Sec7.PocketTraversal.measurable_indicator_segDrv_of_isDrivenCurve`):

* `kcInv` (the inverse capacity clock inside `P`), `IsKilledCurve.kcInv_spec`, `IsKilledCurve.kcprefix_nonempty_iff`
  (a prefix meets a closed set iff rational times of `P` approach it);
* **`measurableSet_lt_kcLife`**, `measurableSet_kcPrefix`;
* **`measurable_kcW`**, **`measurable_kcVR`**, **`measurable_kcVL`**: the killed word is measurable at every time.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock capLife capInv segDrv segDriver)
open Sec7.PocketTraversal (IsDrivenCurve capTrace)
open WangWu.ImgWord (IsLocCont kImg)
open Restart (dyadicSquare isClosed_dyadicSquare)
open Sec7.Lemma71E (nonempty_dyadicSquare)
open MartChar.RealFlow (rightImg)

/-- **The inverse capacity clock inside `P`.** -/
def kcInv (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ) : ℝ := kcTime P (capInv (kcCurve γ P) r)

variable {γ : ℝ → ℂ} {P : Set ℝ}

namespace IsKilledCurve

variable (hγ : IsKilledCurve γ P)
include hγ

theorem kcInv_mem (r : ℝ) : kcInv γ P r ∈ P := hγ.kcTime_mem (Sec7.Lemma71C.capInv_nonneg _ r)

theorem kcInv_spec {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) < kcLife γ P) :
    kcInv γ P r ∈ P ∧ capClock γ (kcInv γ P r) = r := by
  obtain ⟨h0, hc⟩ := hγ.isDrivenCurve.capInv_spec r.coe_nonneg (lt_kcLife_iff_ofReal.1 hr)
  refine ⟨hγ.kcInv_mem r, ?_⟩
  rw [kcInv, ← hγ.capClock_kcCurve h0, hc]

theorem image_capInv_eq (r : ℝ) :
    kcCurve γ P '' Icc 0 (capInv (kcCurve γ P) r) = γ '' Icc 0 (kcInv γ P r) :=
  hγ.image_kcCurve_Icc (Sec7.Lemma71C.capInv_nonneg _ r)

/-- **The prefix meets a closed set, through rational times** (before the terminal capacity). -/
theorem kcprefix_nonempty_iff {r : ℝ≥0} (hr : (r : WithTop ℝ≥0) < kcLife γ P) {Q : Set ℂ} (hQ : IsClosed Q)
    (hQne : Q.Nonempty) :
    (Q ∩ γ '' Icc 0 (kcInv γ P r)).Nonempty ↔
      ∀ j : ℕ, ∃ q : ℚ, (q : ℝ) ∈ P ∧ capClock γ q < r + 1 / ((j : ℝ) + 1) ∧
        infDist (γ q) Q < 1 / ((j : ℝ) + 1) := by
  obtain ⟨hu0, hur⟩ := hγ.kcInv_spec hr
  have hle_iff : ∀ t ∈ P, (t ≤ kcInv γ P r ↔ capClock γ t ≤ r) := fun t ht => by
    have := (hγ.strictMonoOn_capClock.le_iff_le ht hu0).symm
    rwa [hur] at this
  constructor
  · rintro ⟨z, hzQ, t, ht, rfl⟩ j
    have htP : t ∈ P := hγ.icc _ hu0 ht
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hcc := hγ.continuousOn_capClock t htP
    have hgc := hγ.cont t htP
    have h1 : ∀ᶠ s in 𝓝[P] t, capClock γ s < r + 1 / ((j : ℝ) + 1) := by
      have := (hle_iff t htP).1 ht.2
      exact hcc.eventually (gt_mem_nhds (by linarith))
    have h2 : ∀ᶠ s in 𝓝[P] t, dist (γ s) (γ t) < 1 / ((j : ℝ) + 1) :=
      hgc.eventually (ball_mem_nhds _ hj)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
    obtain ⟨S', hS', htS'⟩ := hγ.exists_gt t htP
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min (t + δ) S' by
      exact lt_min (by linarith) htS')
    have hqP : (q : ℝ) ∈ P := hγ.icc S' hS' ⟨(hγ.nonneg t htP).trans hq1.le, hq2.le.trans (min_le_right _ _)⟩
    have hqI : (q : ℝ) ∈ ball t δ ∩ P := by
      refine ⟨?_, hqP⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      have := min_le_left (t + δ) S'
      constructor <;> linarith
    obtain ⟨hq3, hq4⟩ := hδs hqI
    exact ⟨q, hqP, hq3, lt_of_le_of_lt (infDist_le_dist_of_mem hzQ) hq4⟩
  · intro h
    choose q hqP hqc hqd using h
    obtain ⟨S, hS, hrS⟩ := hγ.lt_kcLife_iff_exists.1 hr
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt (show 0 < capClock γ S - r by linarith)
    have hqS : ∀ j, j₀ ≤ j → ((q j : ℚ) : ℝ) ∈ Icc (0 : ℝ) S := by
      intro j hj
      refine ⟨hγ.nonneg _ (hqP j), ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have h1 := hγ.strictMonoOn_capClock hS (hqP j) hlt
      have h2 : 1 / ((j : ℝ) + 1) ≤ 1 / ((j₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
      linarith [hqc j]
    obtain ⟨t, ht, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).tendsto_subseq
      (x := fun i => ((q (i + j₀) : ℚ) : ℝ)) fun i => hqS _ (Nat.le_add_left _ _)
    have htP : t ∈ P := hγ.icc S hS ht
    have hφmono : Tendsto (fun i => φ i + j₀) atTop atTop :=
      tendsto_atTop_mono (fun i => Nat.le_add_right _ _) hφ.tendsto_atTop
    have hεlim : Tendsto (fun i => 1 / (((φ i + j₀ : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono
    have hlim' : Tendsto (fun i => ((q (φ i + j₀) : ℚ) : ℝ)) atTop (𝓝[P] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => hqP _⟩
    have hct : capClock γ t ≤ r := by
      have hc := (hγ.continuousOn_capClock t htP).tendsto.comp hlim'
      refine le_of_tendsto_of_tendsto' hc (by simpa using (tendsto_const_nhds (x := (r : ℝ))).add hεlim)
        fun i => (hqc _).le
    have hgt : γ t ∈ Q := by
      have hd := ((continuous_infDist_pt Q).tendsto (γ t)).comp ((hγ.cont t htP).tendsto.comp hlim')
      have h0 : infDist (γ t) Q = 0 :=
        le_antisymm (le_of_tendsto_of_tendsto' hd hεlim fun i => (hqd _).le) infDist_nonneg
      exact (hQ.mem_iff_infDist_zero hQne).2 h0
    exact ⟨γ t, hgt, t, ⟨ht.1, (hle_iff t htP).2 hct⟩, rfl⟩

/-- `{r < kcLife}` through rational times in `P`. -/
theorem lt_kcLife_iff_rat (r : ℝ≥0) :
    (r : WithTop ℝ≥0) < kcLife γ P ↔ ∃ q : ℚ, (q : ℝ) ∈ P ∧ (r : ℝ) < capClock γ q := by
  constructor
  · intro h
    obtain ⟨S, hS, hrS⟩ := hγ.lt_kcLife_iff_exists.1 h
    have hS0 : 0 < S := by
      refine lt_of_le_of_ne (hγ.nonneg S hS) fun he => ?_
      rw [← he, hγ.capClock_zero] at hrS
      exact absurd hrS (not_lt.2 r.coe_nonneg)
    have hcc : ContinuousWithinAt (capClock γ) (Icc 0 S) S :=
      (hγ.continuousOn_capClock.mono (hγ.icc S hS)) S ⟨hS0.le, le_rfl⟩
    have hev : ∀ᶠ u in 𝓝[Icc 0 S] S, (r : ℝ) < capClock γ u := hcc.eventually (lt_mem_nhds hrS)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (S - δ) < S from max_lt hS0 (by linarith))
    have hqI : (q : ℝ) ∈ Icc 0 S := ⟨(le_max_left _ _).trans hq1.le, hq2.le⟩
    refine ⟨q, hγ.icc S hS hqI, hδs ⟨?_, hqI⟩⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have := le_max_right 0 (S - δ)
    constructor <;> linarith
  · rintro ⟨q, hq, hrq⟩
    exact hγ.lt_kcLife_iff_exists.2 ⟨q, hq, hrq⟩

end IsKilledCurve

/-! ### Families of killed curves -/

section Family

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}

/-- **`{r < kcLife}` is measurable** for a family of killed curves with measurable rational pre-killing events and
clocks. -/
theorem measurableSet_lt_kcLife (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q)) (r : ℝ≥0) :
    MeasurableSet {ω | (r : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} := by
  have heq : {ω | (r : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} =
      ⋃ q : ℚ, {ω | (q : ℝ) ∈ P ω} ∩ {ω | (r : ℝ) <
        ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q) ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    rw [(hγ ω).lt_kcLife_iff_rat r]
    refine exists_congr fun q => and_congr_right fun hq => ?_
    rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from hq)]
  rw [heq]
  exact MeasurableSet.iUnion fun q => (hP q).inter (measurableSet_lt measurable_const (hc q))

/-- **The killed prefix events are measurable.** -/
theorem measurableSet_kcPrefix (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) (r : ℝ≥0) (n : ℕ) (k : ℤ × ℤ) :
    MeasurableSet {ω | (r : WithTop ℝ≥0) < kcLife (γ ω) (P ω) ∧
      (dyadicSquare n k ∩ γ ω '' Icc 0 (kcInv (γ ω) (P ω) r)).Nonempty} := by
  have heq : {ω | (r : WithTop ℝ≥0) < kcLife (γ ω) (P ω) ∧
      (dyadicSquare n k ∩ γ ω '' Icc 0 (kcInv (γ ω) (P ω) r)).Nonempty} =
      {ω | (r : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} ∩
        ⋂ j : ℕ, ⋃ q : ℚ, {ω | (q : ℝ) ∈ P ω} ∩
          {ω | ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q) ω < r + 1 / ((j : ℝ) + 1)} ∩
          {ω | infDist (γ ω q) (dyadicSquare n k) < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
    refine and_congr_right fun hr => ?_
    rw [(hγ ω).kcprefix_nonempty_iff hr (isClosed_dyadicSquare n k) (nonempty_dyadicSquare n k)]
    refine forall_congr' fun j => exists_congr fun q => ?_
    constructor
    · rintro ⟨hq, h1, h2⟩
      refine ⟨⟨hq, ?_⟩, h2⟩
      rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from hq)]
      exact h1
    · rintro ⟨⟨hq, h1⟩, h2⟩
      rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from hq)] at h1
      exact ⟨hq, h1, h2⟩
  rw [heq]
  refine (measurableSet_lt_kcLife hγ hP hc r).inter (MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q => ?_)
  exact ((hP q).inter (measurableSet_lt (hc q) measurable_const)).inter
    (measurableSet_lt ((continuous_infDist_pt _).measurable.comp (hm q)) measurable_const)

/-- **The killed driver at a fixed capacity time is measurable on `{s < kcLife}`** (the driver formula of
`Sec7.PocketTraversal`, through the time-changed driven curves). -/
theorem measurable_indicator_kcW (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) (s : ℝ≥0) :
    Measurable ({ω | (s : WithTop ℝ≥0) < kcLife (γ ω) (P ω)}.indicator fun ω => kcW (γ ω) (P ω) s) := by
  set E := {ω | (s : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} with hEdef
  have hE : MeasurableSet E := measurableSet_lt_kcLife hγ hP hc s
  have hpre : ∀ r : ℝ, 0 ≤ r → r ≤ (s : ℝ) → ∀ (n : ℕ) (k : ℤ × ℤ), MeasurableSet (E ∩ {ω | (dyadicSquare n k ∩
      kcCurve (γ ω) (P ω) '' Icc 0 (capInv (kcCurve (γ ω) (P ω)) r)).Nonempty}) := by
    intro r hr0 hrs n k
    have hle : r.toNNReal ≤ s := by rw [Real.toNNReal_le_iff_le_coe]; exact hrs
    have heq : E ∩ {ω | (dyadicSquare n k ∩
        kcCurve (γ ω) (P ω) '' Icc 0 (capInv (kcCurve (γ ω) (P ω)) r)).Nonempty} =
        E ∩ {ω | ((r.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kcLife (γ ω) (P ω) ∧
          (dyadicSquare n k ∩ γ ω '' Icc 0 (kcInv (γ ω) (P ω) (r.toNNReal : ℝ≥0))).Nonempty} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, (hγ ω).image_capInv_eq, Real.coe_toNNReal _ hr0, hEdef]
      exact and_congr_right fun hs => ⟨fun h => ⟨lt_of_le_of_lt (WithTop.coe_le_coe.2 hle) hs, h⟩,
        fun h => h.2⟩
    rw [heq]
    exact hE.inter (measurableSet_kcPrefix hγ hP hc hm _ n k)
  have h := Sec7.PocketTraversal.measurable_indicator_segDrv_of_isDrivenCurve (γ := fun ω => kcCurve (γ ω) (P ω))
    s.coe_nonneg (E := E) (fun ω _ => (hγ ω).isDrivenCurve) hE (fun ω hω => lt_kcLife_iff_ofReal.1 hω) hpre
  convert h using 1
  funext ω
  by_cases hω : ω ∈ E
  · rw [indicator_of_mem hω, indicator_of_mem hω, kcW_of_lt hω]
    rfl
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]

/-- **The killed driver is measurable at every time.** -/
theorem measurable_kcW (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) (t : ℝ≥0) :
    Measurable fun ω => kcW (γ ω) (P ω) t := by
  convert measurable_indicator_kcW hγ hP hc hm t using 1
  funext ω
  by_cases ht : (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)
  · rw [indicator_of_mem (show ω ∈ {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} from ht)]
  · rw [indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} from ht)]
    simp only [kcW, ht, ↓reduceIte]

open scoped Classical in
/-- The killed driver frozen after `t` (on `{t < kcLife}`; `0` elsewhere). -/
def kcFrz (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (t : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun u ω => if (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω) then kcW (γ ω) (P ω) (min u t) else 0

theorem kcFrz_props (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) (t : ℝ≥0) :
    (∀ u, Measurable (kcFrz γ P t u)) ∧ (∀ ω, Continuous fun u => kcFrz γ P t u ω) ∧
      ∀ ω, (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω) →
        EqOn (kcPath (γ ω) (P ω)) (Bessel.realPath (kcFrz γ P t) ω) (Icc 0 t) := by
  classical
  refine ⟨fun u => Measurable.ite (measurableSet_lt_kcLife hγ hP hc t) (measurable_kcW hγ hP hc hm _)
    measurable_const, fun ω => ?_, fun ω ht r hr => ?_⟩
  · by_cases ht : (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)
    · simp only [kcFrz, ht, ↓reduceIte]
      refine ((hγ ω).continuousOn_kcW).comp_continuous (continuous_id.min continuous_const)
        fun u => lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u t)) ht
    · simp only [kcFrz, ht, ↓reduceIte]
      exact continuous_const
  · have hrt : r.toNNReal ≤ t := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp only [Bessel.realPath, kcFrz, ht, ↓reduceIte, min_eq_left hrt]
    rfl

/-- **The images of right marks are measurable at every time** (measurable marks). -/
theorem measurable_kcVR (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) {n : ℕ} {xR : Ω → Fin n → ℝ} (hxR : Measurable xR) (j : Fin n)
    (t : ℝ≥0) : Measurable fun ω => kcVR (γ ω) (P ω) (xR ω) j t := by
  classical
  obtain ⟨hfm, hfc, hEq⟩ := kcFrz_props hγ hP hc hm t
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun ω => rightImg (Bessel.realPath (kcFrz γ P t) ω) (xR ω j) t :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) hfm hfc
      ((measurable_pi_apply j).comp hxR) t
  have heq : (fun ω => kcVR (γ ω) (P ω) (xR ω) j t) = {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)}.indicator
      fun ω => rightImg (Bessel.realPath (kcFrz γ P t) ω) (xR ω j) t := by
    funext ω
    by_cases ht : (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)
    · rw [indicator_of_mem (show ω ∈ {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} from ht),
        kcVR_of_lt _ _ ht, kcVRr, kImg]
      exact Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath hfc ω) t.coe_nonneg (hEq ω ht) _
    · rw [indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} from ht)]
      simp only [kcVR, ht, ↓reduceIte]
  rw [heq]
  exact hR.indicator (measurableSet_lt_kcLife hγ hP hc t)

/-- **The images of left marks are measurable at every time** (measurable marks). -/
theorem measurable_kcVL (hγ : ∀ ω, IsKilledCurve (γ ω) (P ω))
    (hP : ∀ q : ℚ, MeasurableSet {ω | (q : ℝ) ∈ P ω})
    (hc : ∀ q : ℚ, Measurable ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q))
    (hm : ∀ q : ℚ, Measurable fun ω => γ ω q) {n : ℕ} {xL : Ω → Fin n → ℝ} (hxL : Measurable xL) (i : Fin n)
    (t : ℝ≥0) : Measurable fun ω => kcVL (γ ω) (P ω) (xL ω) i t := by
  classical
  obtain ⟨hfm, hfc, hEq⟩ := kcFrz_props hγ hP hc hm t
  let 𝓕c : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
    ⟨fun _ => inferInstance, monotone_const, fun _ => le_rfl⟩
  have hR : Measurable fun ω => rightImg (Bessel.realPath (fun u ω => -kcFrz γ P t u ω) ω) (-xL ω i) t :=
    Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓕c) (fun u => (hfm u).neg)
      (fun ω => (hfc ω).neg) ((measurable_pi_apply i).comp hxL).neg t
  have heq : (fun ω => kcVL (γ ω) (P ω) (xL ω) i t) = {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)}.indicator
      fun ω => -rightImg (Bessel.realPath (fun u ω => -kcFrz γ P t u ω) ω) (-xL ω i) t := by
    funext ω
    by_cases ht : (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)
    · rw [indicator_of_mem (show ω ∈ {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} from ht),
        kcVL_of_lt _ _ ht, kcVLr, kImg, neg_inj]
      refine Sec7.Lemma71B.rightImg_congr (Bessel.continuous_realPath (fun ω => (hfc ω).neg) ω) t.coe_nonneg
        (fun r hr => ?_) _
      show -kcPath _ _ r = -kcFrz γ P t r.toNNReal ω
      rw [hEq ω ht hr]
      rfl
    · rw [indicator_of_notMem (show ω ∉ {ω | (t : WithTop ℝ≥0) < kcLife (γ ω) (P ω)} from ht)]
      simp only [kcVL, ht, ↓reduceIte]
  rw [heq]
  exact hR.neg.indicator (measurableSet_lt_kcLife hγ hP hc t)

end Family

end InteractingSLE.Sec5.CrossRestart.KernelQ
