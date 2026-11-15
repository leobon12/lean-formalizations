/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb4Restart
import InteractingSLE.Spec.Sec7.ContinuityProbGaps
import InteractingSLE.Spec.Sec2.Assembly2Pathwise

/-!
# §7.3, Aux. lemma 103: finite-time continuity from band traces (pathwise)

Packet PROVE-SEC7-C4. The pathwise half of Aux. lemma 103 (`source/spec/p337-384.md` L292–L305, p. 349–350): "At
`U = 2/3`, switch to the right band […]. Continue alternating. […] Every new phase is pulled back through the
continuously extended inverse map of the preceding finite continuous prefix, so the resulting traces join at their
tips. The switches cannot accumulate in finite time. […] There is hence a final band covering a neighborhood of any
such endpoint, and the bounded-drift comparison on that band supplies continuity through the endpoint itself."

Here the alternating band sequence is replaced by bands started at every rational time (`ae_band_rational`), and the
non-accumulation by a continuous induction (the infimum of the times without a trace): near every time `t₀ < ζ` one
side of the force groups stays `2δ`-far from the driver on a neighbourhood of `t₀` (the cross-gap is positive,
`side_dichotomy`), so the band started at a rational time just before `t₀` passes `t₀`; near a finite lifetime the
same holds by the left limits of the state.

* `exists_isGeneratingTrace_top`: gluing traces on `[0, t]` for all `t` into one on `[0, ∞)`;
* `le_horizonR_shift`, `le_horizonL_shift`, `good_of_shift`: one band step and the join at its start
  (`IsGeneratingTraceIcc.join`);
* `BandTraces`: the band traces from every rational time (the conclusion of `ae_band_rational`);
* `side_dichotomy`, `exists_band_nhds`, `exists_good_gt`, `good_of_lt`, `good_lifetime`;
* **`exists_isGeneratingTrace_of_bandTraces`**: a solution path of an ordered word with the band traces, a separated
  start or an initial trace, and left limits of the state at a finite positive lifetime, has a continuous generating
  trace on `[0, ζ]` (on `[0, ∞)` when `ζ = ∞`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Band

open RandRestart

variable {nL nR : ℕ}

/-! ### Gluing traces on `[0, t]` for every finite `t` -/

/-- **Gluing.** If the driver has a generating trace on `[0, t]` for every finite `t`, it has one on `[0, ∞)`. -/
theorem exists_isGeneratingTrace_top {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hloc : ∀ t : ℝ≥0, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w t η) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η := by
  classical
  have hwt : ∀ t : ℝ≥0, ContinuousOn w {s | (s : ℝ≥0∞) < (t : ℝ≥0∞)} := fun t => hw.continuousOn
  let η : ℝ≥0 → ℂ := fun t => (hloc t).choose t
  have hηeq : ∀ t s : ℝ≥0, s ≤ t → η s = (hloc t).choose s := by
    intro t s hst
    exact IsGeneratingTrace.eq_of_le (hloc s).choose_spec
      ((hloc t).choose_spec.mono_horizon (by exact_mod_cast hst)) (hwt s) hw0 le_rfl
  refine ⟨η, (hloc 0).choose_spec.1, ?_, fun t _ => ?_⟩
  · refine continuousOn_univ.2 ?_ |>.mono (subset_univ _)
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have hc : ContinuousOn η (Iic (t₀ + 1)) :=
      ((hloc (t₀ + 1)).choose_spec.2.1.mono fun s hs => show (s : ℝ≥0∞) ≤ ((t₀ + 1 : ℝ≥0) : ℝ≥0∞) by
        exact_mod_cast hs).congr fun s hs => hηeq (t₀ + 1) s hs
    exact hc.continuousAt (Iic_mem_nhds (lt_add_one t₀))
  · have himg : η '' Icc 0 t = (hloc (t + 1)).choose '' Icc 0 t :=
      image_congr fun s hs => hηeq (t + 1) s (hs.2.trans (le_add_of_nonneg_right zero_le_one))
    rw [himg]
    exact (hloc (t + 1)).choose_spec.2.2 t (by exact_mod_cast lt_add_one t)

/-! ### One band step -/

section Step

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem shiftNN_zero {w : ℝ≥0 → ℝ} (hw0 : w 0 = 0) : shiftNN w 0 = w := by
  funext s
  simp only [shiftNN, zero_add, hw0, sub_zero]

/-- A lower bound for the right-band horizon after `q`: no right mark within `2δ` on `[q, u)`. -/
theorem le_horizonR_shift {δ : ℝ} {n : ℕ} {q : ℝ≥0} {u : ℝ≥0∞} (hu : u ≤ ζ)
    (hun : u ≤ n) (hgap : ∀ s : ℝ≥0, q ≤ s → (s : ℝ≥0∞) < u → ∀ j, 2 * δ < vR j s - w s) :
    u - q ≤ horizonR δ n (shiftNN w q) (shiftMarks vR w q) (ζ - q) := by
  refine le_min (le_hitTime fun s hs _ => ?_) (le_min ((tsub_le_self).trans hun) (tsub_le_tsub_right hu _))
  rintro ⟨j, hj⟩
  have hs' : ((q + s : ℝ≥0) : ℝ≥0∞) < u := by
    rw [ENNReal.coe_add]
    exact lt_tsub_iff_left.1 hs
  have := hgap (q + s) le_self_add hs' j
  simp only [shiftMarks, shiftNN] at hj
  linarith

/-- A lower bound for the left-band horizon after `q`. -/
theorem le_horizonL_shift {δ : ℝ} {n : ℕ} {q : ℝ≥0} {u : ℝ≥0∞} (hu : u ≤ ζ)
    (hun : u ≤ n) (hgap : ∀ s : ℝ≥0, q ≤ s → (s : ℝ≥0∞) < u → ∀ i, 2 * δ < w s - vL i s) :
    u - q ≤ horizonL δ n (shiftNN w q) (shiftMarks vL w q) (ζ - q) := by
  refine le_min (le_hitTime fun s hs _ => ?_) (le_min ((tsub_le_self).trans hun) (tsub_le_tsub_right hu _))
  rintro ⟨i, hi⟩
  have hs' : ((q + s : ℝ≥0) : ℝ≥0∞) < u := by
    rw [ENNReal.coe_add]
    exact lt_tsub_iff_left.1 hs
  have := hgap (q + s) le_self_add hs' i
  simp only [shiftMarks, shiftNN] at hi
  linarith

/-- **Extending a trace through a band.** If the shifted driver after `q` has a trace up to some horizon at least
`u − q`, and the driver has a trace beyond `q` (or `q = 0`), then the driver has a trace on `[0, u]`. -/
theorem good_of_shift (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {q : ℝ≥0} {u h : ℝ≥0∞}
    (hqu : (q : ℝ≥0∞) ≤ u) (hu : u ≤ ζ) (hh : u - q ≤ h) (htr : TraceEvent (shiftNN w q) h)
    (hprev : q = 0 ∨ ∃ s : ℝ≥0, q < s ∧ (s : ℝ≥0∞) ≤ ζ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w s η) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w u η := by
  obtain ⟨η₂, hη₂, -⟩ := htr
  have hη₂' := hη₂.mono_horizon hh
  rcases hprev with rfl | ⟨s, hqs, hsζ, η₁, hη₁⟩
  · rw [shiftNN_zero hw0] at hη₂'
    refine ⟨η₂, ?_⟩
    simpa using hη₂'
  · have hIcc : IsGeneratingTraceIcc w q η₁ :=
      IsGeneratingTrace.isGeneratingTraceIcc hη₁ (hw.mono fun t ht => lt_of_lt_of_le ht hsζ) hw0 (by exact_mod_cast hqs)
    have hqu' : (q : ℝ≥0∞) + (u - q) = u := add_tsub_cancel_of_le hqu
    have hwc : ContinuousOn w {t | (t : ℝ≥0∞) < q + (u - q)} := by
      rw [hqu']
      exact hw.mono fun t ht => lt_of_lt_of_le ht hu
    have := (hIcc.join hwc hw0 hη₂').1
    rw [hqu'] at this
    exact ⟨_, this⟩

end Step

/-! ### Covering `[0, ζ]` by bands -/

section Cover

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Band traces from every rational time** (the conclusion of `ae_band_rational`, for one path; from the time `0`
only when `S0`, the separation of the start, holds). -/
def BandTraces (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (S0 : Prop) : Prop :=
  ∀ q : ℚ, ∀ δ : ℚ, 0 < δ → ∀ n : ℕ, (0 < Real.toNNReal q ∨ S0) → ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < ζ →
    TraceEvent (shiftNN w (Real.toNNReal q))
      (horizonR δ n (shiftNN w (Real.toNNReal q)) (shiftMarks vR w (Real.toNNReal q)) (ζ - Real.toNNReal q)) ∧
    TraceEvent (shiftNN w (Real.toNNReal q))
      (horizonL δ n (shiftNN w (Real.toNNReal q)) (shiftMarks vL w (Real.toNNReal q)) (ζ - Real.toNNReal q))

/-- At a time before the lifetime the driver is separated from all right marks or from all left marks (the
cross-gap is positive, `crossGap_le`). -/
theorem side_dichotomy (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    {t : ℝ≥0} (ht0 : 0 < t ∨ ∀ i j, xL i < xR j) (ht : (t : ℝ≥0∞) < ζ) :
    (∀ j, 0 < vR j t - w t) ∨ ∀ i, 0 < w t - vL i t := by
  by_contra hcon
  simp only [not_or, not_forall, not_lt] at hcon
  obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := hcon
  have h2 : vL i t < vR j t := by
    rcases ht0 with ht0 | hsep
    · exact IsIntegratedSLEPath.vL_lt_vR_of_pos hp hF ht0 ht i j
    · have h1 := hp.isForcePath.crossGap_le i j (zero_le : (0 : ℝ≥0) ≤ t) ht
      rw [hp.isForcePath.vR_zero j, hp.isForcePath.vL_zero i] at h1
      linarith [hsep i j]
  linarith

/-- **A neighbourhood of `t₀` on which one side stays `2δ`-far from the driver.** -/
theorem exists_band_nhds (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    {t₀ : ℝ≥0} (ht0 : 0 < t₀ ∨ ∀ i j, xL i < xR j) (ht₀ : (t₀ : ℝ≥0∞) < ζ) :
    ∃ ε > (0 : ℝ), ∃ δ : ℚ, 0 < δ ∧
      ((∀ s : ℝ≥0, dist s t₀ < ε → (s : ℝ≥0∞) < ζ ∧ ∀ j, 2 * (δ : ℝ) < vR j s - w s) ∨
        (∀ s : ℝ≥0, dist s t₀ < ε → (s : ℝ≥0∞) < ζ ∧ ∀ i, 2 * (δ : ℝ) < w s - vL i s)) := by
  have hf := hp.isForcePath
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hmem : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} ∈ 𝓝 t₀ := hopen.mem_nhds ht₀
  have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {s | (s : ℝ≥0∞) < ζ} → ContinuousAt f t₀ :=
    fun hf' => hf'.continuousAt hmem
  rcases side_dichotomy hp hF ht0 ht₀ with hR | hL
  · obtain ⟨c, hc, hcj⟩ := Sec2.Assembly.exists_pos_forall_lt _ hR
    have hev : ∀ᶠ s : ℝ≥0 in 𝓝 t₀, (s : ℝ≥0∞) < ζ ∧ ∀ j, c / 2 < vR j s - w s :=
      Filter.Eventually.and hmem (Filter.eventually_all.2 fun j =>
        (hca ((hf.continuousOn_vR j).sub hf.continuousOn_w)).eventually
          (Ioi_mem_nhds (show c / 2 < vR j t₀ - w t₀ by linarith [hcj j])))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨δ, hδ0, hδc⟩ := exists_rat_btwn (show (0 : ℝ) < c / 4 by positivity)
    refine ⟨ε, hε, δ, by exact_mod_cast hδ0, Or.inl fun s hs => ⟨(hball hs).1, fun j => ?_⟩⟩
    linarith [(hball hs).2 j]
  · obtain ⟨c, hc, hci⟩ := Sec2.Assembly.exists_pos_forall_lt _ hL
    have hev : ∀ᶠ s : ℝ≥0 in 𝓝 t₀, (s : ℝ≥0∞) < ζ ∧ ∀ i, c / 2 < w s - vL i s :=
      Filter.Eventually.and hmem (Filter.eventually_all.2 fun i =>
        (hca (hf.continuousOn_w.sub (hf.continuousOn_vL i))).eventually
          (Ioi_mem_nhds (show c / 2 < w t₀ - vL i t₀ by linarith [hci i])))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨δ, hδ0, hδc⟩ := exists_rat_btwn (show (0 : ℝ) < c / 4 by positivity)
    refine ⟨ε, hε, δ, by exact_mod_cast hδ0, Or.inr fun s hs => ⟨(hball hs).1, fun i => ?_⟩⟩
    linarith [(hball hs).2 i]

/-- **One band step.** If the driver has a trace on `[0, s]` for every `s < t₀ < ζ`, it has one on `[0, u]` for
some `u > t₀`. -/
theorem exists_good_gt (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    (hband : BandTraces w vL vR ζ (∀ i j, xL i < xR j)) {t₀ : ℝ≥0} (ht0 : 0 < t₀ ∨ ∀ i j, xL i < xR j)
    (ht₀ : (t₀ : ℝ≥0∞) < ζ)
    (hprev : ∀ s : ℝ≥0, s < t₀ → ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w s η) :
    ∃ u : ℝ≥0∞, (t₀ : ℝ≥0∞) < u ∧ u ≤ ζ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w u η := by
  have hf := hp.isForcePath
  obtain ⟨ε, hε, δ, hδ, hside⟩ := exists_band_nhds hp hF ht0 ht₀
  -- the restart time `q < t₀` (or `q = 0 = t₀`)
  obtain ⟨q, hq0, hqt, hqε, hq, hqpos⟩ : ∃ q : ℚ, (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ t₀ ∧ (t₀ : ℝ) - ε < q ∧
      ((q : ℝ) = 0 ∨ (q : ℝ) < t₀) ∧ (0 < t₀ → (0 : ℝ) < q) := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
    · refine ⟨0, by simp, by simp, ?_, Or.inl (by simp), fun h => absurd h (by rw [← h0]; exact lt_irrefl 0)⟩
      rw [← h0]
      simp only [NNReal.coe_zero, zero_sub, Rat.cast_zero, Left.neg_neg_iff]
      exact hε
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max ((t₀ : ℝ) - ε) 0 < t₀ from
        max_lt (by linarith) (by exact_mod_cast h0))
      exact ⟨q, (le_max_right _ _).trans hq1.le, hq2.le, (le_max_left _ _).trans_lt hq1, Or.inr hq2,
        fun _ => (le_max_right _ _).trans_lt hq1⟩
  set q' : ℝ≥0 := Real.toNNReal q with hq'def
  have hq'q : (q' : ℝ) = q := Real.coe_toNNReal _ hq0
  have hq't : q' ≤ t₀ := by rw [← NNReal.coe_le_coe, hq'q]; exact hqt
  have hq'ζ : (q' : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hq't) ht₀
  have hS : 0 < q' ∨ ∀ i j, xL i < xR j := by
    rcases ht0 with ht0 | hsep
    · left
      rw [← NNReal.coe_pos, hq'q]
      exact hqpos ht0
    · exact Or.inr hsep
  -- the target time `u`
  set e : ℝ≥0 := Real.toNNReal (ε / 2) with he
  have he0 : (e : ℝ) = ε / 2 := Real.coe_toNNReal _ (by positivity)
  set u : ℝ≥0∞ := min ((t₀ + e : ℝ≥0) : ℝ≥0∞) ζ with hu
  set n : ℕ := ⌈(t₀ + e : ℝ≥0)⌉₊ with hn
  have hun : u ≤ n := (min_le_left _ _).trans (by
    rw [← ENNReal.coe_natCast]
    exact_mod_cast Nat.le_ceil _)
  have hqu : (q' : ℝ≥0∞) ≤ u := le_min (by exact_mod_cast hq't.trans le_self_add) hq'ζ.le
  have ht₀u : (t₀ : ℝ≥0∞) < u := lt_min (by
    have : t₀ < t₀ + e := lt_add_of_pos_right _ (by rw [← NNReal.coe_pos, he0]; positivity)
    exact_mod_cast this) ht₀
  have hdist : ∀ s : ℝ≥0, q' ≤ s → (s : ℝ≥0∞) < u → dist s t₀ < ε := by
    intro s hqs hsu
    have hs1 : (s : ℝ) < t₀ + ε / 2 := by
      have : s < t₀ + e := by exact_mod_cast hsu.trans_le (min_le_left _ _)
      have := NNReal.coe_lt_coe.2 this
      rw [NNReal.coe_add, he0] at this
      exact this
    have hs2 : (q : ℝ) ≤ s := by rw [← hq'q]; exact_mod_cast hqs
    rw [NNReal.dist_eq, abs_lt]
    constructor <;> linarith
  have hprev' : q' = 0 ∨ ∃ s : ℝ≥0, q' < s ∧ (s : ℝ≥0∞) ≤ ζ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w s η := by
    rcases hq with hq | hq
    · left
      rw [← NNReal.coe_eq_zero, hq'q, hq]
    · right
      have hlt : q' < t₀ := by rw [← NNReal.coe_lt_coe, hq'q]; exact hq
      obtain ⟨s, hs1, hs2⟩ := exists_between hlt
      exact ⟨s, hs1, (lt_trans (by exact_mod_cast hs2) ht₀).le, hprev s hs2⟩
  refine ⟨u, ht₀u, min_le_right _ _, ?_⟩
  rcases hside with hR | hL
  · have hh := le_horizonR_shift (vR := vR) (w := w) (δ := (δ : ℝ)) (q := q') (min_le_right _ _) hun
      fun s hqs hsu j => (hR s (hdist s hqs hsu)).2 j
    exact good_of_shift hf.continuousOn_w hf.w_zero hqu (min_le_right _ _) hh (hband q δ hδ n hS hq'ζ).1 hprev'
  · have hh := le_horizonL_shift (vL := vL) (w := w) (δ := (δ : ℝ)) (q := q') (min_le_right _ _) hun
      fun s hqs hsu i => (hL s (hdist s hqs hsu)).2 i
    exact good_of_shift hf.continuousOn_w hf.w_zero hqu (min_le_right _ _) hh (hband q δ hδ n hS hq'ζ).2 hprev'

/-- **Traces on every `[0, t]`, `t < ζ`** (the band covering of Aux. lemma 103, by continuous induction). -/
theorem good_of_lt (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    (hband : BandTraces w vL vR ζ (∀ i j, xL i < xR j))
    (hstart : (∀ i j, xL i < xR j) ∨ ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ε η)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w t η := by
  by_contra hcon
  set S : Set ℝ≥0 := {s | (s : ℝ≥0∞) < ζ ∧ ¬ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w s η} with hS
  have hSne : S.Nonempty := ⟨t, ht, hcon⟩
  set T := sInf S with hT
  have hbdd : BddBelow S := OrderBot.bddBelow S
  have hTle : T ≤ t := csInf_le hbdd ⟨ht, hcon⟩
  have hTζ : (T : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hTle) ht
  have hbelow : ∀ s : ℝ≥0, s < T → ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w s η := by
    intro s hs
    by_contra hn
    exact (not_le.2 hs) (csInf_le hbdd ⟨lt_of_le_of_lt (by exact_mod_cast hs.le) hTζ, hn⟩)
  have hT0 : 0 < T ∨ ∀ i j, xL i < xR j := by
    rcases hstart with hsep | ⟨ε, hε, η₀, hη₀⟩
    · exact Or.inr hsep
    · left
      refine lt_of_lt_of_le hε (le_csInf hSne fun s hs => ?_)
      by_contra hlt
      exact hs.2 ⟨η₀, hη₀.mono_horizon (by exact_mod_cast (not_le.1 hlt).le)⟩
  obtain ⟨u, hTu, -, η, hη⟩ := exists_good_gt hp hF hband hT0 hTζ hbelow
  obtain ⟨s, hsS, hsu⟩ : ∃ s ∈ S, (s : ℝ≥0∞) < u := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hTu with ⟨r, hTr, hru⟩
    obtain ⟨s, hsS, hsr⟩ := (csInf_lt_iff hbdd hSne).1 (show T < r by exact_mod_cast hTr)
    exact ⟨s, hsS, lt_trans (by exact_mod_cast hsr) hru⟩
  exact hsS.2 ⟨η, hη.mono_horizon hsu.le⟩

/-- **The trace up to and including a finite positive lifetime**, from the left limits of the state there (one
side is separated from the driver near the lifetime, since the cross-gaps stay positive). -/
theorem good_lifetime (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hF : IsOrderedForceWord xL xR)
    (hband : BandTraces w vL vR ζ (∀ i j, xL i < xR j))
    (hstart : (∀ i j, xL i < xR j) ∨ ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ε η) {T : ℝ≥0} (hT : 0 < T) (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ}
    {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀))) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η := by
  have hf := hp.isForcePath
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hlt : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hTζ]
    exact_mod_cast ht
  have hw₀ : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hvL₀ : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp hlim))
  have hvR₀ : ∀ j, Tendsto (fun t => vR j t) (𝓝[<] T) (𝓝 (vR₀ j)) := fun j =>
    ((continuous_apply j).tendsto _).comp ((continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp hlim))
  -- the limit state: no left and right mark both at the driver
  have hside : (∀ j, 0 < vR₀ j - w₀) ∨ ∀ i, 0 < w₀ - vL₀ i := by
    by_contra hcon
    simp only [not_or, not_forall, not_lt] at hcon
    obtain ⟨⟨j, hj⟩, ⟨i, hi⟩⟩ := hcon
    obtain ⟨t₁, ht₁0, ht₁T⟩ := exists_between hT
    have ht₁ζ : (t₁ : ℝ≥0∞) < ζ := by rw [← hTζ]; exact_mod_cast ht₁T
    have hD1 := IsIntegratedSLEPath.vL_lt_vR_of_pos hp hF ht₁0 ht₁ζ i j
    have hD : vR j t₁ - vL i t₁ ≤ vR₀ j - vL₀ i := by
      refine ge_of_tendsto ((hvR₀ j).sub (hvL₀ i)) ?_
      filter_upwards [hlt, Ioo_mem_nhdsLT ht₁T] with t ht ht'
      exact hf.crossGap_le i j ht'.1.le ht
    have hL : vL₀ i ≤ w₀ := le_of_tendsto_of_tendsto (hvL₀ i) hw₀ (by
      filter_upwards [hlt] with t ht
      exact hf.vL_le_w ht i)
    have hR : w₀ ≤ vR₀ j := le_of_tendsto_of_tendsto hw₀ (hvR₀ j) (by
      filter_upwards [hlt] with t ht
      exact hf.w_le_vR ht j)
    linarith
  set n : ℕ := ⌈T⌉₊ with hn
  have hζn : ζ ≤ n := by
    rw [← hTζ, ← ENNReal.coe_natCast]
    exact_mod_cast Nat.le_ceil _
  have hmem0 : ∀ {P : ℝ≥0 → Prop}, (∀ᶠ t in 𝓝[<] T, P t) → ∃ l : ℝ≥0, l < T ∧ ∀ t, l < t → t < T → P t := by
    intro P hP
    obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT).1 hP
    exact ⟨l, hl, fun t h1 h2 => hsub ⟨h1, h2⟩⟩
  -- a rational restart time in `(l, T)` and the trace beyond it
  have hrest : ∀ l : ℝ≥0, l < T → ∃ q : ℚ, l < Real.toNNReal q ∧ Real.toNNReal q < T ∧
      ∃ s : ℝ≥0, Real.toNNReal q < s ∧ (s : ℝ≥0∞) ≤ ζ ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w s η := by
    intro l hl
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (l : ℝ) < T by exact_mod_cast hl)
    have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg l).trans hq1.le
    have hq'q : (Real.toNNReal q : ℝ) = q := Real.coe_toNNReal _ hq0
    have h1 : l < Real.toNNReal q := by rw [← NNReal.coe_lt_coe, hq'q]; exact hq1
    have h2 : Real.toNNReal q < T := by rw [← NNReal.coe_lt_coe, hq'q]; exact hq2
    obtain ⟨s, hs1, hs2⟩ := exists_between h2
    have hsζ : (s : ℝ≥0∞) < ζ := by rw [← hTζ]; exact_mod_cast hs2
    exact ⟨q, h1, h2, s, hs1, hsζ.le, good_of_lt hp hF hband hstart hsζ⟩
  have hqζ : ∀ q : ℚ, Real.toNNReal q < T → ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < ζ := fun q h => by
    rw [← hTζ]; exact_mod_cast h
  rcases hside with hR | hL
  · obtain ⟨c, hc, hcj⟩ := Sec2.Assembly.exists_pos_forall_lt _ hR
    have hev : ∀ᶠ t in 𝓝[<] T, ∀ j, c / 2 < vR j t - w t := Filter.eventually_all.2 fun j =>
      ((hvR₀ j).sub hw₀).eventually (Ioi_mem_nhds (show c / 2 < vR₀ j - w₀ by linarith [hcj j]))
    obtain ⟨l, hl, hgap⟩ := hmem0 hev
    obtain ⟨q, hlq, hqT, hprev⟩ := hrest l hl
    obtain ⟨δ, hδ0, hδc⟩ := exists_rat_btwn (show (0 : ℝ) < c / 4 by positivity)
    have hδ : (0 : ℚ) < δ := by exact_mod_cast hδ0
    have hh := le_horizonR_shift (vR := vR) (w := w) (δ := (δ : ℝ)) (q := Real.toNNReal q) (u := ζ) le_rfl hζn
      fun s hqs hsζ j => by
        have hsT : s < T := by rw [← hTζ] at hsζ; exact_mod_cast hsζ
        linarith [hgap s (lt_of_lt_of_le hlq hqs) hsT j]
    exact good_of_shift hf.continuousOn_w hf.w_zero (hqζ q hqT).le le_rfl hh
      (hband q δ hδ n (Or.inl (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ l) hlq)) (hqζ q hqT)).1 (Or.inr hprev)
  · obtain ⟨c, hc, hci⟩ := Sec2.Assembly.exists_pos_forall_lt _ hL
    have hev : ∀ᶠ t in 𝓝[<] T, ∀ i, c / 2 < w t - vL i t := Filter.eventually_all.2 fun i =>
      (hw₀.sub (hvL₀ i)).eventually (Ioi_mem_nhds (show c / 2 < w₀ - vL₀ i by linarith [hci i]))
    obtain ⟨l, hl, hgap⟩ := hmem0 hev
    obtain ⟨q, hlq, hqT, hprev⟩ := hrest l hl
    obtain ⟨δ, hδ0, hδc⟩ := exists_rat_btwn (show (0 : ℝ) < c / 4 by positivity)
    have hδ : (0 : ℚ) < δ := by exact_mod_cast hδ0
    have hh := le_horizonL_shift (vL := vL) (w := w) (δ := (δ : ℝ)) (q := Real.toNNReal q) (u := ζ) le_rfl hζn
      fun s hqs hsζ i => by
        have hsT : s < T := by rw [← hTζ] at hsζ; exact_mod_cast hsζ
        linarith [hgap s (lt_of_lt_of_le hlq hqs) hsT i]
    exact good_of_shift hf.continuousOn_w hf.w_zero (hqζ q hqT).le le_rfl hh
      (hband q δ hδ n (Or.inl (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ l) hlq)) (hqζ q hqT)).2 (Or.inr hprev)

/-- **Finite-time continuity from the band traces** (Aux. lemma 103 for a separated start, pathwise): a solution
path of a separated word whose state has left limits at a finite positive lifetime, and whose driver has the band
traces from every rational time, has a continuous generating trace on `[0, ζ]` (on `[0, ∞)` when `ζ = ∞`). -/
theorem exists_isGeneratingTrace_of_bandTraces (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) (hband : BandTraces w vL vR ζ (∀ i j, xL i < xR j))
    (hstart : (∀ i j, xL i < xR j) ∨ ∃ ε : ℝ≥0, 0 < ε ∧ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ε η)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀))) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η := by
  have hf := hp.isForcePath
  rcases eq_or_ne ζ ⊤ with htop | htop
  · have hc : Continuous w := by
      rw [← continuousOn_univ]
      exact hf.continuousOn_w.mono fun t _ => by rw [htop]; exact ENNReal.coe_lt_top
    rw [htop]
    exact exists_isGeneratingTrace_top hc hf.w_zero fun t =>
      good_of_lt hp hF hband hstart (by rw [htop]; exact ENNReal.coe_lt_top)
  rcases eq_or_ne ζ 0 with h0 | h0
  · refine ⟨fun _ => 0, rfl, continuousOn_const, fun t ht => ?_⟩
    rw [h0] at ht
    exact absurd ht (not_lt.2 bot_le)
  set T := ζ.toNNReal with hTdef
  have hTζ : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal htop
  have hT : 0 < T := by
    have : (0 : ℝ≥0∞) < (T : ℝ≥0∞) := by rw [hTζ]; exact pos_iff_ne_zero.2 h0
    exact_mod_cast this
  obtain ⟨w₀, vL₀, vR₀, hl⟩ := hlim T hT hTζ
  exact good_lifetime hp hF hband hstart hT hTζ hl

end Cover

end Band

end Sec7

end InteractingSLE
