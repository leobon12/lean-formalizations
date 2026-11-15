/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowProb2Hull
import QuantumZipper.Proofs.Thm11.ForwardTamed
import QuantumZipper.Proofs.Thm11.ForwardClock
import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Proofs.GFF.K3.C5Kernel
import QuantumZipper.Proofs.Zipper.F1Side
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Aux. lemma 126: the measurable coding of the stopped-trace event

Packet PROVE-T14-IN. This file proves the named input `Sec7.StoppedTraceCodingStatement` of PROVE-SEC7-D2
(Aux. lemma 126's proof, pp. 399–400: "Existence of a continuous extension is a countable uniform continuity
condition, and equality of its filled hulls with the driving hulls can be checked at rational times by their
complements and a countable rational planar basis. This gives standard Borel versions of the curve and the relevant
continuous-trace event").

The deterministic characterization `exists_isGeneratingTrace_iff_traceCond` (`CounterflowProb2Hull.lean`) reduces
the event to the countable conditions `TraceCond`. This file makes every ingredient measurable in the rational-time
values `f : ℚ≥0 → ℝ` of the driver:

* `extQ`: a measurable extension `(ℚ≥0 → ℝ) → (ℝ≥0 → ℝ)` that returns `w` on the restriction of a continuous `w`;
* `regQ`: the same, followed by QuantumZipper's continuous regularization `G1Pkg.regB`, so that every sample path is
  continuous, as QuantumZipper's measurability lemmas for hulls require;
* `disjoint_closedBall_fwdHull_iff`: a closed disc in `ℍ` misses `K_q` iff for some `k` the `1/(k+1)`-tamed forward
  flows of its rational points keep imaginary part at least `2/(k+1)` at all rational times up to `q`. This is the
  "countable rational planar basis" for the complement of the hull. QuantumZipper's tamed flows are measurable in the
  driver (`measurable_tamed_drive`);
* `lt_bufferedStop_iff`: "`p < S_r(w)`" for a rational `p` is a countable condition on the rational values of `w`.

Main result: `stoppedTraceCodingStatement`. With it, Lemma 7.25's trace part needs three named inputs, not four
(`lemma725TraceStatement_of_three`).
-/

set_option autoImplicit false

universe u v

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal NNRat

open QuantumZipper (H fwdHull fwdMap tamedZ drive)

namespace InteractingSLE

namespace Sec7

namespace Coding

/-- A predicate `p → q a` with a constant premise is measurable when `q` is (under the premise). -/
theorem measurable_imp_const {α : Type*} [MeasurableSpace α] {p : Prop} {q : α → Prop}
    (h : p → Measurable q) : Measurable fun a => p → q a := by
  by_cases hp : p
  · simpa [hp] using h hp
  · simp only [hp, false_implies]
    exact measurable_const

/-! ### Rational points of a closed disc -/

theorem closedBall_subset_H {c : ℂ} {ε : ℝ} (hcε : ε < c.im) : closedBall c ε ⊆ H := by
  intro x hx
  rw [mem_closedBall] at hx
  have h1 := Complex.abs_im_le_norm (x - c)
  rw [← Complex.dist_eq, Complex.sub_im] at h1
  have h2 := (abs_le.1 (h1.trans hx)).1
  show 0 < x.im
  linarith

/-- Rational points of a closed disc of positive radius are dense in it. -/
theorem exists_ratPt_mem_closedBall {c z : ℂ} {ε r : ℝ} (hε : 0 < ε) (hz : z ∈ closedBall c ε)
    (hr : 0 < r) : ∃ y : ℚ × ℚ, ratPt y ∈ closedBall c ε ∧ dist z (ratPt y) < r := by
  have hcl : z ∈ closure (ball c ε) := by rw [closure_ball c hε.ne']; exact hz
  obtain ⟨x, hx, hzx⟩ := Metric.mem_closure_iff.1 hcl (r / 2) (half_pos hr)
  rw [mem_ball] at hx
  obtain ⟨y, hy⟩ := exists_dist_ratPt_lt x (lt_min (half_pos hr) (sub_pos.2 hx))
  refine ⟨y, ?_, ?_⟩
  · rw [mem_closedBall]
    have h1 := dist_triangle (ratPt y) x c
    rw [dist_comm] at hy
    linarith [min_le_right (r / 2) (ε - dist x c)]
  · linarith [dist_triangle z x (ratPt y), min_le_left (r / 2) (ε - dist x c)]

/-- A closed disc in `ℍ` lies in `K_q` iff its rational points do. -/
theorem closedBall_subset_fwdHull_iff {W : ℝ → ℝ} (hW : Continuous W) {q : ℝ} (hq : 0 ≤ q) {c : ℂ}
    {ε : ℝ} (hε : 0 < ε) (hcε : ε < c.im) :
    closedBall c ε ⊆ fwdHull W q ↔ ∀ y : ℚ × ℚ, ratPt y ∈ closedBall c ε → ratPt y ∈ fwdHull W q := by
  refine ⟨fun h y hy => h hy, fun h z hz => ?_⟩
  by_contra hzK
  obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hq) z
    ⟨closedBall_subset_H hcε hz, hzK⟩
  obtain ⟨y, hy, hzy⟩ := exists_ratPt_mem_closedBall hε hz hδ
  exact (hδb (by rw [mem_ball, dist_comm]; exact hzy)).2 (h y hy)

/-! ### The tamed-flow criterion for a disc to miss the hull -/

/-- Stability of the tamed flow in its starting point. -/
theorem dist_tamedZ_le {W : ℝ → ℝ} (hW : Continuous W) {c : ℝ} (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T)
    (a a' : ℂ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (tamedZ W c a t) (tamedZ W c a' t) ≤ dist a a' * Real.exp (4 * T / c ^ 2) := by
  have h := QuantumZipper.tamedUnc_stability (W' := W) hc hT (QuantumZipper.tamedUnc_zero hW hc a)
    (QuantumZipper.tamedUnc_hasDerivWithinAt hW hc hT a) (QuantumZipper.tamedUnc_zero hW hc a')
    (QuantumZipper.tamedUnc_hasDerivWithinAt hW hc hT a') (ε := 0) (fun r _ => by simp) t ht
  rw [add_zero] at h
  simp only [QuantumZipper.tamedZ]
  rw [dist_sub_right]
  exact h

/-- Rational times are dense in `[0, q]` for a rational `q ≥ 0`. -/
theorem Icc_subset_closure_ratReal (q₀ : ℚ≥0) :
    Icc (0 : ℝ) ((q₀ : ℝ≥0) : ℝ) ⊆
      closure {s : ℝ | ∃ r : ℚ, (r : ℝ) = s ∧ 0 ≤ s ∧ s ≤ ((q₀ : ℝ≥0) : ℝ)} := by
  intro x hx
  have hq : ((q₀ : ℝ≥0) : ℝ) = ((q₀ : ℚ) : ℝ) := by norm_cast
  rcases eq_or_lt_of_le hx.2 with hxq | hxq
  · exact subset_closure ⟨q₀, by rw [hxq, hq], hx.1, hx.2⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min (lt_add_of_pos_right x hε) hxq)
    refine ⟨r, ⟨r, rfl, by linarith [hx.1], (hr2.trans_le (min_le_right _ _)).le⟩, ?_⟩
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
    linarith [min_le_left (x + ε) ((q₀ : ℝ≥0) : ℝ)]

/-- **A rational closed disc misses `K_q` iff its rational points stay tamed-high up to `q`.** For a continuous
driver, a closed disc `B̄(c, ε) ⊂ ℍ` misses the hull at a rational time `q` iff for some `k` the `1/(k+1)`-tamed
forward flows of the rational points of the disc have imaginary part at least `2/(k+1)` at every rational time in
`[0, q]`. -/
theorem disjoint_closedBall_fwdHull_iff {W : ℝ → ℝ} (hW : Continuous W) {q₀ : ℚ≥0} {c : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hcε : ε < c.im) :
    Disjoint (closedBall c ε) (fwdHull W ((q₀ : ℝ≥0) : ℝ)) ↔
      ∃ k : ℕ, ∀ y : ℚ × ℚ, ratPt y ∈ closedBall c ε → ∀ s : ℚ, 0 ≤ (s : ℝ) → (s : ℝ) ≤ ((q₀ : ℝ≥0) : ℝ) →
        2 * (1 / ((k : ℝ) + 1)) ≤ (tamedZ W (1 / ((k : ℝ) + 1)) (ratPt y) s).im := by
  set q : ℝ := ((q₀ : ℝ≥0) : ℝ) with hqdef
  have hq0 : 0 ≤ q := NNReal.coe_nonneg _
  constructor
  · intro hdisj
    have hsub : closedBall c ε ⊆ H \ fwdHull W q := fun z hz =>
      ⟨closedBall_subset_H hcε hz, fun hzK => Set.disjoint_left.1 hdisj hz hzK⟩
    have hφ : ContinuousOn (fun z => (fwdMap W q z).im) (closedBall c ε) :=
      (Complex.continuous_im.comp_continuousOn
        (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hq0).continuousOn).mono hsub
    obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall c ε).exists_isMinOn
      ⟨c, mem_closedBall_self hε.le⟩ hφ
    obtain ⟨u₀, hu₀⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hq0 (hsub hx₀).1 (hsub hx₀).2
    have hm : 0 < (fwdMap W q x₀).im := by
      rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu₀ ⟨hq0, le_rfl⟩]
      exact QuantumZipper.FwdClock.sol_im_pos hW (hsub hx₀).1 hu₀ ⟨hq0, le_rfl⟩
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hm)
    have hk0 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    refine ⟨k, fun y hy s hs0 hsq => ?_⟩
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hq0 (hsub hy).1 (hsub hy).2
    have hanti := (QuantumZipper.K3.im_fwdMap_antitoneOn hW (hsub hy).1 ⟨u, hu⟩).1
    have hbound : ∀ s' ∈ Icc (0 : ℝ) q, 2 * (1 / ((k : ℝ) + 1)) ≤ (u s').im := by
      intro s' hs'
      have e1 : u s' = fwdMap W s' (ratPt y) := (QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu hs').symm
      have h1 : (fwdMap W q (ratPt y)).im ≤ (fwdMap W s' (ratPt y)).im :=
        hanti hs' ⟨hq0, le_rfl⟩ hs'.2
      have h2 : (fwdMap W q x₀).im ≤ (fwdMap W q (ratPt y)).im := isMinOn_iff.1 hmin _ hy
      rw [e1]
      linarith
    have heq := QuantumZipper.tamedZ_eq_of_isForwardSol hW hk0 hq0 hu
      (fun s' hs' => by linarith [hbound s' hs']) s ⟨hs0, hsq⟩
    rw [heq]
    exact hbound s ⟨hs0, hsq⟩
  · rintro ⟨k, hk⟩
    set c' : ℝ := 1 / ((k : ℝ) + 1) with hc'
    have hc'0 : 0 < c' := by positivity
    have hIm : ∀ a b : ℂ, |a.im - b.im| ≤ dist a b := fun a b => by
      rw [Complex.dist_eq, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
    -- rational starting points, all times in `[0, q]`
    have h1a : ∀ y : ℚ × ℚ, ratPt y ∈ closedBall c ε → ∀ s ∈ Icc (0 : ℝ) q,
        2 * c' ≤ (tamedZ W c' (ratPt y) s).im := by
      intro y hy s hs
      have hcont := QuantumZipper.continuousOn_tamedZ hW hc'0 hq0 (ratPt y)
      have hcl : IsClosed {z : ℂ | 2 * c' ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
      have hsubI : {s : ℝ | ∃ r : ℚ, (r : ℝ) = s ∧ 0 ≤ s ∧ s ≤ q} ⊆ Icc 0 q := fun s ⟨_, _, h0, h1⟩ => ⟨h0, h1⟩
      have hmem := ((hcont s hs).mono hsubI).mem_closure_image (Icc_subset_closure_ratReal q₀ hs)
      refine hcl.closure_subset_iff.2 ?_ hmem
      rintro _ ⟨s', ⟨r, rfl, h0, hq'⟩, rfl⟩
      exact hk y hy r h0 hq'
    -- all starting points of the disc
    have h1b : ∀ z ∈ closedBall c ε, ∀ s ∈ Icc (0 : ℝ) q, 2 * c' ≤ (tamedZ W c' z s).im := by
      intro z hz s hs
      by_contra hlt
      push Not at hlt
      have hgap : 0 < 2 * c' - (tamedZ W c' z s).im := by linarith
      have hL : 0 < Real.exp (4 * q / c' ^ 2) := Real.exp_pos _
      obtain ⟨y, hy, hzy⟩ := exists_ratPt_mem_closedBall hε hz (div_pos hgap hL)
      have h1 := h1a y hy s hs
      have h2 := dist_tamedZ_le hW hc'0 hq0 z (ratPt y) hs
      have h4 : dist z (ratPt y) * Real.exp (4 * q / c' ^ 2) < 2 * c' - (tamedZ W c' z s).im := by
        rwa [lt_div_iff₀ hL] at hzy
      linarith [(abs_le.1 (hIm (tamedZ W c' z s) (tamedZ W c' (ratPt y) s))).1]
    -- every point of the disc survives past `q`
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have hcontq := QuantumZipper.continuousOn_tamedZ hW hc'0 (show (0 : ℝ) ≤ q + 1 by linarith) z
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousOn_iff.1 hcontq q ⟨hq0, by linarith⟩ c' hc'0
    have hmin0 : 0 < min (δ / 2) 1 := lt_min (half_pos hδ) one_pos
    set q' : ℝ := q + min (δ / 2) 1 with hq'
    have hqq' : q < q' := by linarith
    have him : ∀ s ∈ Icc (0 : ℝ) q', c' ≤ (tamedZ W c' z s).im := by
      intro s hs
      by_cases hsq : s ≤ q
      · have := h1b z hz s ⟨hs.1, hsq⟩
        linarith
      · push Not at hsq
        have hs1 : s ∈ Icc (0 : ℝ) (q + 1) := ⟨hs.1, by linarith [hs.2, min_le_right (δ / 2) 1]⟩
        have hd : dist s q < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [hs.2, min_le_left (δ / 2) 1]
        have h1 := hδb s hs1 hd
        have h2 := h1b z hz q ⟨hq0, le_rfl⟩
        linarith [(abs_le.1 (hIm (tamedZ W c' z s) (tamedZ W c' z q))).1]
    have hsol := QuantumZipper.isForwardSol_tamedZ hW hc'0 (by linarith : (0 : ℝ) ≤ q') him
    have hsw : ENNReal.ofReal q' ≤ QuantumZipper.swallowTime W z :=
      le_sSup ⟨q', ⟨by linarith, _, hsol⟩, rfl⟩
    have hlt : ENNReal.ofReal q < ENNReal.ofReal q' :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hqq'
    exact absurd (lt_of_lt_of_le hlt hsw) (not_lt.2 hzK.2)

/-! ### The buffered stop at rational times -/

/-- The countable form of "`p < S_r(w)`" in the rational values `f` of the driver: `p < r²/64` and `|f| ≤ r/4 − 1/(m+1)`
at the rational times up to `p`, for some `m`. -/
def AvailQ (r : ℝ) (f : ℚ≥0 → ℝ) (p : ℚ≥0) : Prop :=
  ((p : ℝ≥0) : ℝ) < r ^ 2 / 64 ∧ ∃ m : ℕ, ∀ t : ℚ≥0, t ≤ p → |f t| ≤ r / 4 - 1 / ((m : ℝ) + 1)

/-- **The buffered stop (FS11.1) at a rational time**, countably: for a continuous `w`, `p < S_r(w)` iff
`AvailQ r w p`. -/
theorem lt_bufferedStop_iff {r : ℝ} (hr : 0 < r) {w : ℝ≥0 → ℝ} (hw : Continuous w) (p : ℚ≥0) :
    ((p : ℝ≥0) : ℝ≥0∞) < Dilation.bufferedStop r w ↔ AvailQ r (fun q : ℚ≥0 => w q) p := by
  unfold Dilation.bufferedStop AvailQ
  rw [lt_min_iff, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    ENNReal.ofReal_coe_nnreal]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun ⟨m, hm⟩ => ?_⟩
  · have hlt : ∀ t : ℝ≥0, t ≤ (p : ℝ≥0) → |w t| < r / 4 := by
      intro t ht
      by_contra hge
      push Not at hge
      have := lt_of_lt_of_le h (iInf₂_le t hge)
      exact absurd (ENNReal.coe_lt_coe.1 this) (not_lt.2 ht)
    obtain ⟨x₁, hx₁, hmax⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (p : ℝ≥0))).exists_isMaxOn
      ⟨0, le_rfl, bot_le⟩ (continuous_abs.comp hw).continuousOn
    have hM := hlt x₁ hx₁.2
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hM)
    refine ⟨m, fun t ht => ?_⟩
    have := isMaxOn_iff.1 hmax (t : ℝ≥0) ⟨bot_le, by exact_mod_cast ht⟩
    simp only [Function.comp_apply] at this
    linarith
  · have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hall : ∀ t ∈ Icc (0 : ℝ≥0) (p : ℝ≥0), |w t| ≤ r / 4 - 1 / ((m : ℝ) + 1) := by
      intro t ht
      have hcl : IsClosed {x : ℝ≥0 | |w x| ≤ r / 4 - 1 / ((m : ℝ) + 1)} :=
        isClosed_le (continuous_abs.comp hw) continuous_const
      refine hcl.closure_subset_iff.2 ?_ (Icc_subset_closure_ratTimesLE ⟨p, rfl⟩ ht)
      rintro _ ⟨t', ht', rfl⟩
      exact hm t' (by exact_mod_cast ht')
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuous_iff.1 hw (p : ℝ≥0) _ hm0
    refine lt_of_lt_of_le (b := (((p : ℝ≥0) + (δ / 2).toNNReal : ℝ≥0) : ℝ≥0∞))
      (ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ (Real.toNNReal_pos.2 (half_pos hδ))))
      (le_iInf₂ fun t ht => ?_)
    by_contra hlt
    push Not at hlt
    have hlt' := ENNReal.coe_lt_coe.1 hlt
    by_cases htp : t ≤ (p : ℝ≥0)
    · have := hall t ⟨bot_le, htp⟩
      linarith
    · push Not at htp
      have hd : dist t (p : ℝ≥0) < δ := by
        have h1 : (t : ℝ) < ((p : ℝ≥0) : ℝ) + δ / 2 := by
          have := NNReal.coe_lt_coe.2 hlt'
          rwa [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this
        have h2 : ((p : ℝ≥0) : ℝ) < t := NNReal.coe_lt_coe.2 htp
        rw [NNReal.dist_eq, abs_of_pos (by linarith)]
        linarith
      have h1 := hδb t hd
      rw [Real.dist_eq] at h1
      have h2 := hall (p : ℝ≥0) ⟨bot_le, le_rfl⟩
      have h3 := abs_sub_abs_le_abs_sub (w t) (w (p : ℝ≥0))
      linarith

theorem measurable_availQ (r : ℝ) (p : ℚ≥0) : Measurable fun f : ℚ≥0 → ℝ => AvailQ r f p := by
  refine measurable_const.and (Measurable.exists fun m => Measurable.forall fun t =>
    measurable_imp_const fun _ => ?_)
  exact measurableSet_setOfPred.1
    (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply t)) measurable_const)

/-! ### A measurable extension from rational times -/

theorem exists_seq_tendsto_nnrat (t : ℝ≥0) :
    ∃ u : ℕ → ℚ≥0, Tendsto (fun n => (u n : ℝ≥0)) atTop (𝓝 t) := by
  have hex : ∀ n : ℕ, ∃ q : ℚ≥0, t < (q : ℝ≥0) ∧ (q : ℝ≥0) < t + (1 / ((n : ℝ) + 1)).toNNReal :=
    fun n => exists_nnrat_btwn (lt_add_of_pos_right _ (Real.toNNReal_pos.2 (by positivity)))
  choose u hu1 hu2 using hex
  refine ⟨u, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (t : ℝ) < ((u n : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 (hu1 n)
  have h2 : ((u n : ℝ≥0) : ℝ) < t + 1 / ((n : ℝ) + 1) := by
    have := NNReal.coe_lt_coe.2 (hu2 n)
    rwa [NNReal.coe_add, Real.coe_toNNReal _ (by positivity)] at this
  have h3 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    gcongr
  rw [NNReal.dist_eq, abs_of_pos (by linarith)]
  linarith

/-- A sequence of rational times converging to `t`. -/
def apxQ (t : ℝ≥0) : ℕ → ℚ≥0 := (exists_seq_tendsto_nnrat t).choose

theorem tendsto_apxQ (t : ℝ≥0) : Tendsto (fun n => (apxQ t n : ℝ≥0)) atTop (𝓝 t) :=
  (exists_seq_tendsto_nnrat t).choose_spec

/-- **The measurable extension of rational-time values**: `extQ f t = lim_n f (q_n(t))` for rational `q_n(t) → t`. -/
def extQ (f : ℚ≥0 → ℝ) (t : ℝ≥0) : ℝ := limUnder atTop fun n => f (apxQ t n)

theorem measurable_extQ : Measurable extQ :=
  measurable_pi_iff.2 fun t =>
    (StronglyMeasurable.limUnder fun n => (measurable_pi_apply (apxQ t n)).stronglyMeasurable).measurable

/-- `extQ` recovers a continuous path from its rational-time values. -/
theorem extQ_restrict {w : ℝ≥0 → ℝ} (hw : Continuous w) : extQ (fun q : ℚ≥0 => w q) = w :=
  funext fun t => ((hw.tendsto t).comp (tendsto_apxQ t)).limUnder_eq

/-- The continuous regularization of `extQ f`: every path is continuous and vanishes at `0`, and it is the
original path for the restriction of a continuous path vanishing at `0`. -/
def regQ (t : ℝ≥0) (f : ℚ≥0 → ℝ) : ℝ := QuantumZipper.Thm18Asm.G1Pkg.regB t (extQ f)

theorem measurable_regQ (t : ℝ≥0) : Measurable (regQ t) :=
  (QuantumZipper.Thm18Asm.G1Pkg.regB_measurable t).comp measurable_extQ

theorem continuous_regQ (f : ℚ≥0 → ℝ) : Continuous fun t => regQ t f :=
  QuantumZipper.Thm18Asm.G1Pkg.regB_continuous (extQ f)

theorem drive_regQ {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    drive 1 regQ (fun q : ℚ≥0 => w q) = fun s : ℝ => w s.toNNReal := by
  funext s
  have h := congrFun (QuantumZipper.Thm18Asm.G1Pkg.drive_regB (κ := 1) hw hw0) s
  simp only [QuantumZipper.drive, Real.sqrt_one, one_mul] at h ⊢
  rw [regQ, extQ_restrict hw]
  exact h

/-! ### Measurability of the countable trace conditions -/

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

theorem measurable_closedBall_subset_fwdHull (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ r, Measurable (B r)) {q : ℝ} (hq : 0 ≤ q) {c : ℂ} {ε : ℝ} (hε : 0 < ε) (hcε : ε < c.im) :
    Measurable fun ω => closedBall c ε ⊆ fwdHull (drive 1 B ω) q := by
  have e : (fun ω => closedBall c ε ⊆ fwdHull (drive 1 B ω) q) =
      fun ω => ∀ y : ℚ × ℚ, ratPt y ∈ closedBall c ε → ratPt y ∈ fwdHull (drive 1 B ω) q :=
    funext fun ω => propext (closedBall_subset_fwdHull_iff
      (QuantumZipper.NonSwallow.continuous_drive_ns hBc 1 ω) hq hε hcε)
  rw [e]
  refine Measurable.forall fun y => measurable_imp_const fun _ => ?_
  exact measurableSet_setOfPred.1 ((QuantumZipper.NonSwallow.measurableSet_fwdHull_prod hBm hBc 1 hq).preimage
    (measurable_const.prodMk measurable_id))

theorem measurable_disjoint_closedBall_fwdHull (hBc : ∀ ω, Continuous fun t => B t ω)
    (hBm : ∀ r, Measurable (B r)) (q₀ : ℚ≥0) {c : ℂ} {ε : ℝ} (hε : 0 < ε) (hcε : ε < c.im) :
    Measurable fun ω => Disjoint (closedBall c ε) (fwdHull (drive 1 B ω) ((q₀ : ℝ≥0) : ℝ)) := by
  have e : (fun ω => Disjoint (closedBall c ε) (fwdHull (drive 1 B ω) ((q₀ : ℝ≥0) : ℝ))) =
      fun ω => ∃ k : ℕ, ∀ y : ℚ × ℚ, ratPt y ∈ closedBall c ε → ∀ s : ℚ, 0 ≤ (s : ℝ) →
        (s : ℝ) ≤ ((q₀ : ℝ≥0) : ℝ) →
          2 * (1 / ((k : ℝ) + 1)) ≤ (tamedZ (drive 1 B ω) (1 / ((k : ℝ) + 1)) (ratPt y) s).im :=
    funext fun ω => propext (disjoint_closedBall_fwdHull_iff
      (QuantumZipper.NonSwallow.continuous_drive_ns hBc 1 ω) hε hcε)
  rw [e]
  refine Measurable.exists fun k => Measurable.forall fun y => measurable_imp_const fun _ =>
    Measurable.forall fun s => measurable_imp_const fun hs0 => measurable_imp_const fun _ => ?_
  have hm := (QuantumZipper.measurable_tamed_drive 1 (c := 1 / ((k : ℝ) + 1)) (by positivity) B hBc hs0
    (fun r _ => hBm r)).1
  exact measurableSet_setOfPred.1 (measurableSet_le measurable_const
    (Complex.measurable_im.comp (hm.comp (measurable_const.prodMk measurable_id))))

end Meas

/-! ### The coding -/

/-- **Aux. lemma 126's measurable coding of the stopped-trace event** (named input of PROVE-SEC7-D2): for every
`r > 0` there is a measurable set `G` of rational-time values whose members are exactly the restrictions of the
continuous drivers vanishing at `0` that have a generating trace through the buffered stop `S_r`. -/
theorem stoppedTraceCodingStatement : StoppedTraceCodingStatement := by
  intro r hr
  set W : (ℚ≥0 → ℝ) → ℝ → ℝ := fun f => drive 1 regQ f with hWdef
  set τ : (ℚ≥0 → ℝ) → ℝ≥0 → ℂ := fun f p => LP.traceAt p (extQ f) with hτdef
  refine ⟨{f | TraceCond (W f) (τ f) (AvailQ r f)}, ?_, fun w hw hw0 => ?_⟩
  · have hτm : ∀ p : ℝ≥0, Measurable fun f => τ f p := fun p =>
      (LP.measurable_traceAt p).comp measurable_extQ
    have hHm : ∀ p : ℝ≥0, Measurable fun f => τ f p ∈ H := fun p =>
      (measurable_mem.2 QuantumZipper.isOpen_H.measurableSet).comp (hτm p)
    have hKm : ∀ (p : ℝ≥0) (q : ℚ≥0), Measurable fun f => τ f p ∈ fwdHull (W f) ((q : ℝ≥0) : ℝ) :=
      fun p q => measurableSet_setOfPred.1
        ((QuantumZipper.NonSwallow.measurableSet_fwdHull_prod measurable_regQ continuous_regQ 1
          (NNReal.coe_nonneg _)).preimage ((hτm p).prodMk measurable_id))
    refine measurableSet_setOfPred.2 (Measurable.and ?_ ?_)
    · refine Measurable.forall fun m => Measurable.exists fun k => Measurable.forall fun p : ℚ≥0 =>
        Measurable.forall fun p' : ℚ≥0 => (measurable_availQ r p).imp ((measurable_availQ r p').imp
          (measurable_imp_const fun _ => ?_))
      exact measurableSet_setOfPred.1 (measurableSet_le ((hτm p).dist (hτm p')) measurable_const)
    · refine Measurable.forall fun q => (measurable_availQ r q).imp (Measurable.and ?_ ?_)
      · exact Measurable.forall fun p : ℚ≥0 => measurable_imp_const fun _ => (hHm p).imp (hKm p q)
      · refine Measurable.forall fun ε => Measurable.forall fun c => measurable_imp_const fun hε =>
          measurable_imp_const fun hc => ?_
        have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
        have hcε : (ε : ℝ) < (ratPt c).im := by rw [ratPt_im]; linarith
        refine (Measurable.forall fun p : ℚ≥0 => measurable_imp_const fun _ => measurableSet_setOfPred.1
          (measurableSet_lt measurable_const (measurable_const.dist (hτm p)))).imp
          ((measurable_closedBall_subset_fwdHull continuous_regQ measurable_regQ (NNReal.coe_nonneg _)
            hε' hcε).or (measurable_disjoint_closedBall_fwdHull continuous_regQ measurable_regQ q hε' hcε))
  · have hS : Dilation.bufferedStop r w ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
    have hW : W (fun q : ℚ≥0 => w q) = fun s : ℝ => w s.toNNReal := drive_regQ hw hw0
    have hτ : τ (fun q : ℚ≥0 => w q) = fun p => LP.traceAt p w := by
      simp only [hτdef, extQ_restrict hw]
    have hL : AvailQ r (fun q : ℚ≥0 => w q) =
        fun p : ℚ≥0 => ((p : ℝ≥0) : ℝ≥0∞) < Dilation.bufferedStop r w :=
      funext fun p => propext (lt_bufferedStop_iff hr hw p).symm
    show TraceCond (W fun q : ℚ≥0 => w q) (τ fun q : ℚ≥0 => w q) (AvailQ r fun q : ℚ≥0 => w q) ↔ _
    rw [hW, hτ, hL, exists_isGeneratingTrace_iff_traceCond hw hw0 hS]

/-- **Aux. lemma 126, the stopped transfer** (`Aux126StoppedTraceStatement`) from the change of measure (one two-seed
evolution with a stopped trace) and the existence of a Jacobi diffusion; the measurable coding is
`stoppedTraceCodingStatement`. -/
theorem aux126StoppedTraceStatement_of_girsanov (hJ : JacobiDiffusionExistsStatement)
    (hGir : Aux126GirsanovStatement.{v}) : Aux126StoppedTraceStatement.{u, v} :=
  aux126StoppedTraceStatement_of_inputs hJ stoppedTraceCodingStatement hGir

/-- **Lemma 7.25, finite-time continuity** (p. 413), `LP.Lemma725TraceStatement`, from three named inputs: the
existence of a Jacobi diffusion, the reference of Lemma 7.25 (Aux. lemmas 130, 125, 127) and the change of measure of
Aux. lemma 126. The fourth input of PROVE-SEC7-D2, the measurable coding, is `stoppedTraceCodingStatement`. -/
theorem lemma725TraceStatement_of_three (hJ : JacobiDiffusionExistsStatement)
    (hRef : Lemma725ReferenceStatement.{v}) (hGir : Aux126GirsanovStatement.{v}) :
    LP.Lemma725TraceStatement.{u} :=
  lemma725TraceStatement_of_girsanov hJ hRef hGir stoppedTraceCodingStatement

end Coding

end Sec7

end InteractingSLE
