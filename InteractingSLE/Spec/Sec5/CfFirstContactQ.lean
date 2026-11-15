/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfAvoidLeftQFree

/-!
# Proposition 5.1 in the chart `Q`: excursions of the counterflow into the left side of the flow line

Packet PROVE-CFBARRIER3. PROVE-CFAVOID reduced `Cond44Ref.Prop51QStatement` (no counterflow point at a rational time
lies on the left side `L` of the flow line `γ = η_{θ₂}`) to the restart input `CfAvoidLeftQ.CfFirstContactQStatement`,
and showed the two equivalent given the counterflow's regularity (`CfLineRegularQStatement`). The landed lemma
`CfAvoidLeftQ.not_hitsLeftPartAlong_of_eventually` shows that every hit of the left part forces the counterflow into
`L` itself. So the restart input is a statement about **excursions of the counterflow `c` into the open set `L`**: if
`c(q) ∈ L` at a rational time `q`, then `c` must leave `L` (or end at `0` from inside `L`), and its first exit point
after `q` is approached from inside `L`.

This file splits that statement into two named inputs of different nature and proves the splitting.

* **`CfExitNewStatement`** (the *local barrier*, the field-level input; Lemma 5.4's pattern with the curves exchanged,
  Astra's C.2 as template). For rational data `t, q, z₀ = x₀ + i y₀, r`: almost surely the window event
  `ExitWindow` fails. That event says: the flow line after time `t` avoids the closed ball `B̄(z₀, 2r)`; the past
  `c((0, q])` meets `B̄(z₀, 2r)` only off `∂L` (no old contact with the flow line or with `ℝ₋` near the window); and
  from `c(q) ∈ L ∩ B(z₀, r)` the counterflow stays in `L ∩ B(z₀, r)` until it reaches `∂L`, or until the end of its
  life. Inside `B̄(z₀, 2r)` every boundary arc then carries identified data: the left side of `γ(0, t]`, `ℝ₋`, their
  junction `0⁻`, and the counterflow's own past sides. This is exactly the configuration of the local comparison
  (Aux. 61–62 at `κ′ = 16/κ > 4`) with the landed finite-word barriers (GB7a for every `κ`, the junction barrier).
* **`CfExitOldStatement`** (*no return to an old point*): almost surely, an excursion of `c` in `L` that is running
  at a rational time `q` does not end at a point that `c` visited before `q`. This is the configuration the local
  comparison does not cover: at an old contact point the conditional boundary data is not identified.

* **`CfReturnStatement`** (weaker than `CfExitOldStatement`, `cfReturnStatement_of_cfExitOld`): only an old exit
  point that the counterflow first reached from *outside* `L` is excluded. An old exit point first reached from inside
  `L` is a new exit point for a rational restart time just before its first visit, so the local barrier covers it
  (`exists_exitWindow_of_returnFree`). The residual configuration: the counterflow first reaches a point of `∂L` from
  the right side of the flow line (or along `∂L`), later enters `L` through another contact point, and returns to the
  first point from inside `L`.

**`prop51QStatement_of_return`**: `CfLineRegularQStatement → CfExitNewStatement → CfReturnStatement →
Prop51QStatement`, and **`cfFirstContactQStatement_of_return`** (the restart input itself); the corollaries
`prop51QStatement_of_exit`, `cfFirstContactQStatement_of_exit`, `cfAvoidLeftQStatement_of_exit` use
`CfExitOldStatement`. The countable localization (B4 of PROVE-CFBARRIER) is proved here: an exit point `y` not
visited before `q` has positive distance from the past `c((0, q])` (the counterflow starts at `∞`), which gives a
rational window around `y`, a later rational restart time inside the excursion, and a rational flow-line time after
which the flow line has left the window.

All three inputs are consequences of Proposition 5.1 (`cfExitNewStatement_of_prop51Q`, `cfExitOldStatement_of_prop51Q`,
`cfReturnStatement_of_prop51Q`), so none can be false if Proposition 5.1 holds; given the counterflow's regularity,
`CfExitNewStatement ∧ CfReturnStatement` is equivalent to it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC fwdHull fwdMap)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CfFirstContactQ

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique Cond44Ref Prop51Q CfAvoidLeftQ

/-! ### The window event and the old-exit event -/

/-- **The local exit event in a window.** For a flow line `γ` (on `ℝ≥0`), a counterflow line `c` with lifetime `Z`, a
flow-line time `t`, a restart time `q`, a centre `z₀` and a radius `r`, with `L` the left side of `γ`:

1. the flow line after time `t` stays off the closed ball `B̄(z₀, 2r)`;
2. no point of the past `c((0, q])` in `B̄(z₀, 2r)` lies on the boundary of `L` (no old contact near the window);
3. either the counterflow stays in `L ∩ B(z₀, r)` from `q` to an alive time `b > q` with `c(b) ∉ L` (an exit from
   `L` inside the window), or it stays in `L ∩ B(z₀, r)` from the alive time `q` to the end of its life. -/
def ExitWindow (γ : ℝ≥0 → ℂ) (c : ℝ → ℂ) (Z : ℝ≥0∞) (t q : ℝ) (z₀ : ℂ) (r : ℝ) : Prop :=
  (∀ s : ℝ≥0, t ≤ s → γ s ∉ closedBall z₀ (2 * r)) ∧
    (∀ v ∈ Ioc 0 q, c v ∈ closedBall z₀ (2 * r) → c v ∉ frontier (leftSideOf (range γ))) ∧
    ((∃ b ∈ aliveSet Z, q < b ∧ (∀ v ∈ Ico q b, c v ∈ leftSideOf (range γ) ∩ ball z₀ r) ∧
        c b ∉ leftSideOf (range γ)) ∨
      (q ∈ aliveSet Z ∧ ∀ v ∈ aliveSet Z, q ≤ v → c v ∈ leftSideOf (range γ) ∩ ball z₀ r))

/-- **No return to an old point.** If the counterflow stays in the left side `L` of `γ` from time `q` to an alive time
`b > q` and `c(b) ∉ L`, then `c(b)` is not a point visited by `c` at a time in `(0, q]`. -/
def OldExitFree (γ : ℝ≥0 → ℂ) (c : ℝ → ℂ) (Z : ℝ≥0∞) (q : ℝ) : Prop :=
  ∀ b ∈ aliveSet Z, q < b → (∀ v ∈ Ico q b, c v ∈ leftSideOf (range γ)) → c b ∉ leftSideOf (range γ) →
    ∀ v ∈ Ioc 0 q, c v ≠ c b

/-- **No return to a point first reached from outside `L`.** If the counterflow stays in the left side `L` of `γ` from
time `q` to an alive time `b > q` with `c(b) ∉ L`, and `v₁ ≤ q` is the first time at which `c` visits `c(b)`, then `c`
reached `c(b)` at time `v₁` from inside `L`: it was in `L` on a whole interval `(v₁ − ε, v₁)`. (Weaker than
`OldExitFree`, which forbids every earlier visit of `c(b)`.) -/
def ReturnFree (γ : ℝ≥0 → ℂ) (c : ℝ → ℂ) (Z : ℝ≥0∞) (q : ℝ) : Prop :=
  ∀ b ∈ aliveSet Z, q < b → (∀ v ∈ Ico q b, c v ∈ leftSideOf (range γ)) → c b ∉ leftSideOf (range γ) →
    ∀ v₁ ∈ Ioc 0 q, c v₁ = c b → (∀ v ∈ Ioo 0 v₁, c v ≠ c b) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ Ioo (v₁ - ε) v₁, c v ∈ leftSideOf (range γ)

theorem OldExitFree.returnFree {γ : ℝ≥0 → ℂ} {c : ℝ → ℂ} {Z : ℝ≥0∞} {q : ℝ} (h : OldExitFree γ c Z q) :
    ReturnFree γ c Z q := fun b hb hqb hall hbL v₁ hv₁ he _ => absurd he (h b hb hqb hall hbL v₁ hv₁)

theorem aliveSet_top : aliveSet ⊤ = Ioi 0 := by
  ext u
  simp [aliveSet, ENNReal.ofReal_lt_top]

/-! ### The deterministic core -/

section Core

variable {c : ℝ → ℂ}

/-- **The past stays away from a point it does not visit.** If `c` is continuous on `(0, ∞)`, tends to `∞` at `0⁺`
and does not visit `y` on `(0, q]`, then `c((0, q])` has positive distance from `y`. -/
theorem exists_pos_le_norm_sub (hc : ContinuousOn c (Ioi 0))
    (hc0 : Tendsto (fun v => ‖c v‖) (𝓝[>] 0) atTop) {q : ℝ} (hq : 0 < q) {y : ℂ}
    (hy : ∀ v ∈ Ioc 0 q, c v ≠ y) : ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Ioc 0 q, δ ≤ ‖c v - y‖ := by
  have hev : ∀ᶠ v in 𝓝[>] (0 : ℝ), ‖y‖ + 1 < ‖c v‖ := hc0.eventually (eventually_gt_atTop _)
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set ε := min (ε₀ / 2) q with hεdef
  have hε : 0 < ε := lt_min (half_pos hε₀) hq
  have hεq : ε ≤ q := min_le_right _ _
  have hsmall : ∀ v, 0 < v → v < ε → ‖y‖ + 1 < ‖c v‖ := fun v hv hvε => by
    refine hball ⟨?_, hv⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hv]
    exact hvε.trans_le ((min_le_left _ _).trans (half_le_self hε₀.le))
  have hcont : ContinuousOn (fun v => ‖c v - y‖) (Icc ε q) :=
    ((hc.mono fun v hv => (hε.trans_le hv.1 : (0 : ℝ) < v)).sub continuousOn_const).norm
  obtain ⟨v₀, hv₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hεq) hcont
  have hpos : 0 < ‖c v₀ - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (hy v₀ ⟨hε.trans_le hv₀.1, hv₀.2⟩))
  refine ⟨min 1 ‖c v₀ - y‖, lt_min one_pos hpos, fun v hv => ?_⟩
  by_cases hvε : v < ε
  · have h1 := hsmall v hv.1 hvε
    have h2 : ‖c v‖ - ‖y‖ ≤ ‖c v - y‖ := norm_sub_norm_le _ _
    exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (hmin ⟨not_lt.1 hvε, hv.2⟩)

/-- A rational point within `ε` of a complex number. -/
theorem exists_rat_norm_sub_lt (y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ y₀ : ℚ, ‖(⟨x₀, y₀⟩ : ℂ) - y‖ < ε := by
  obtain ⟨x₀, hx₀⟩ := exists_rat_btwn (show y.re - ε / 2 < y.re + ε / 2 by linarith)
  obtain ⟨y₀, hy₀⟩ := exists_rat_btwn (show y.im - ε / 2 < y.im + ε / 2 by linarith)
  refine ⟨x₀, y₀, (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_⟩
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 : |(x₀ : ℝ) - y.re| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith [hx₀.2], by linarith [hx₀.1]⟩
  have h2 : |(y₀ : ℝ) - y.im| < ε / 2 := abs_sub_lt_iff.2 ⟨by linarith [hy₀.2], by linarith [hy₀.1]⟩
  linarith

/-- A rational flow-line time after which a proper flow line has left a given closed ball. -/
theorem exists_rat_forall_notMem_closedBall {γ : ℝ≥0 → ℂ}
    (hγ : Tendsto (fun s : ℝ => ‖γ s.toNNReal‖) atTop atTop) (z₀ : ℂ) (ρ : ℝ) :
    ∃ t : ℚ, 0 < t ∧ ∀ s : ℝ≥0, (t : ℝ) ≤ s → γ s ∉ closedBall z₀ ρ := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hγ.eventually (eventually_gt_atTop (‖z₀‖ + ρ)))
  obtain ⟨t, ht⟩ := exists_rat_gt (max T 0)
  refine ⟨t, by exact_mod_cast (le_max_right _ _).trans_lt ht, fun s hs hmem => ?_⟩
  have h1 := hT s ((le_max_left _ _).trans (ht.le.trans hs))
  rw [Real.toNNReal_coe] at h1
  have h2 : ‖γ s‖ - ‖z₀‖ ≤ ‖γ s - z₀‖ := norm_sub_norm_le _ _
  rw [mem_closedBall, dist_eq_norm] at hmem
  linarith

/-- **The countable localization of an excursion** (deterministic). Let `c` be continuous on `(0, ∞)`, tend to `∞`
at `0⁺` and to `0` at `∞`, and never vanish; let `γ` be a proper flow line with open left side `L`. If `c(q) ∈ L` at a
time `q > 0` and the excursion of `c` in `L` running at `q` does not end at a point visited before `q`, then some
rational window event `ExitWindow γ c ⊤ t q' z₀ r` holds (`z₀ = x₀ + i y₀`, all data rational and positive). -/
theorem exists_exitWindow {γ : ℝ≥0 → ℂ} (hc : ContinuousOn c (Ioi 0))
    (hc0 : Tendsto (fun v => ‖c v‖) (𝓝[>] 0) atTop) (hcT : Tendsto c atTop (𝓝 0))
    (hcne : ∀ v, 0 < v → c v ≠ 0) (hγ : Tendsto (fun s : ℝ => ‖γ s.toNNReal‖) atTop atTop)
    (hL : IsOpen (leftSideOf (range γ))) {q : ℝ} (hq : 0 < q) (hcq : c q ∈ leftSideOf (range γ))
    (hold : OldExitFree γ c ⊤ q) :
    ∃ t q' x₀ y₀ r : ℚ, 0 < t ∧ 0 < q' ∧ 0 < r ∧ ExitWindow γ c ⊤ t q' ⟨x₀, y₀⟩ r := by
  set L := leftSideOf (range γ) with hLdef
  have hfrL : ∀ z ∈ L, z ∉ frontier L := fun z hz hfr => by
    rw [hL.frontier_eq] at hfr
    exact hfr.2 hz
  set B := {v | q ≤ v ∧ c v ∉ L} with hBdef
  by_cases hB : B.Nonempty
  · -- the first exit time `b` from `L` after `q`
    set b := sInf B with hbdef
    have hBb : BddBelow B := ⟨q, fun v hv => hv.1⟩
    have hqb : q ≤ b := le_csInf hB fun v hv => hv.1
    have hb0 : 0 < b := hq.trans_le hqb
    have hcb : ContinuousAt c b := hc.continuousAt (Ioi_mem_nhds hb0)
    have hbelow : ∀ v, q ≤ v → v < b → c v ∈ L := fun v hqv hvb => by
      by_contra hv
      exact absurd (csInf_le hBb ⟨hqv, hv⟩) (not_le.2 hvb)
    have hbL : c b ∉ L := by
      intro hbL
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcb.preimage_mem_nhds (hL.mem_nhds hbL))
      obtain ⟨w, hwB, hwb⟩ := exists_lt_of_csInf_lt hB (show b < b + ε by linarith)
      have hbw : b ≤ w := csInf_le hBb hwB
      refine hwB.2 (hball ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hqb' : q < b := lt_of_le_of_ne hqb fun h => hbL (h ▸ hcq)
    -- `c(b)` is not an old point; the past stays at distance `δ` from it
    have hnew : ∀ v ∈ Ioc 0 q, c v ≠ c b :=
      hold b (by rw [aliveSet_top]; exact hb0) hqb' (fun v hv => hbelow v hv.1 hv.2) hbL
    obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_sub hc hc0 hq hnew
    obtain ⟨r, hr0, hrδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ / 4 by linarith)
    obtain ⟨x₀, y₀, hz₀⟩ := exists_rat_norm_sub_lt (c b) (half_pos hr0)
    set z₀ : ℂ := ⟨x₀, y₀⟩ with hz₀def
    -- a rational restart time `q'` after which the excursion stays in `B(z₀, r)`
    obtain ⟨ε, hε, hεb⟩ := Metric.mem_nhds_iff.1 (hcb.preimage_mem_nhds (Metric.ball_mem_nhds (c b) (half_pos hr0)))
    obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (show max q (b - ε) < b from max_lt hqb' (by linarith))
    have hqq' : q < q' := (le_max_left _ _).trans_lt hq'1
    have hbq' : b - ε < q' := (le_max_right _ _).trans_lt hq'1
    have hin : ∀ v ∈ Ico (q' : ℝ) b, c v ∈ ball z₀ r := fun v hv => by
      have hv' : c v ∈ ball (c b) (r / 2) := hεb (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hv.1, hv.2])
      rw [Metric.mem_ball, dist_eq_norm] at hv' ⊢
      calc ‖c v - z₀‖ = ‖(c v - c b) + (c b - z₀)‖ := by ring_nf
        _ ≤ ‖c v - c b‖ + ‖c b - z₀‖ := norm_add_le _ _
        _ < r / 2 + r / 2 := by rw [norm_sub_rev (c b)] at *; linarith [hz₀]
        _ = r := by ring
    obtain ⟨t, ht0, ht⟩ := exists_rat_forall_notMem_closedBall hγ z₀ (2 * r)
    refine ⟨t, q', x₀, y₀, r, ht0, by exact_mod_cast hq.trans hqq', by exact_mod_cast hr0, ht, ?_, Or.inl ?_⟩
    · -- the past near the window is off `∂L`
      intro v hv hvB
      by_cases hvq : v ≤ q
      · exfalso
        have h1 := hδle v ⟨hv.1, hvq⟩
        rw [mem_closedBall, dist_eq_norm] at hvB
        have h2 : ‖c v - c b‖ ≤ ‖c v - z₀‖ + ‖z₀ - c b‖ := by
          calc ‖c v - c b‖ = ‖(c v - z₀) + (z₀ - c b)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        linarith
      · exact hfrL _ (hbelow v (not_le.1 hvq).le (hv.2.trans_lt hq'2))
    · refine ⟨b, by rw [aliveSet_top]; exact hb0, hq'2, fun v hv => ⟨hbelow v (hqq'.le.trans hv.1) hv.2, hin v hv⟩,
        hbL⟩
  · -- the counterflow stays in `L` from `q` on: it ends at `0` from inside `L`
    have hstay : ∀ v, q ≤ v → c v ∈ L := fun v hqv => by
      by_contra hv
      exact hB ⟨v, hqv, hv⟩
    obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_sub hc hc0 hq (y := 0) fun v hv => hcne v hv.1
    obtain ⟨r, hr0, hrδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ / 4 by linarith)
    obtain ⟨M, hM⟩ := eventually_atTop.1 (hcT.eventually (Metric.ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < r by
      exact_mod_cast hr0)))
    obtain ⟨q', hq'⟩ := exists_rat_gt (max q M)
    have hqq' : q < q' := (le_max_left _ _).trans_lt hq'
    obtain ⟨t, ht0, ht⟩ := exists_rat_forall_notMem_closedBall hγ 0 (2 * r)
    have hz : ((⟨(0 : ℚ), (0 : ℚ)⟩ : ℂ)) = 0 := Complex.ext (by simp) (by simp)
    refine ⟨t, q', 0, 0, r, ht0, by exact_mod_cast hq.trans hqq', by exact_mod_cast hr0, ?_, ?_, Or.inr ?_⟩
    · rw [hz]
      exact ht
    · intro v hv hvB
      by_cases hvq : v ≤ q
      · exfalso
        have h1 := hδle v ⟨hv.1, hvq⟩
        rw [hz, mem_closedBall, dist_zero_right] at hvB
        rw [sub_zero] at h1
        linarith
      · exact hfrL _ (hstay v (not_le.1 hvq).le)
    · rw [aliveSet_top, hz]
      refine ⟨hq.trans hqq', fun v _ hv => ⟨hstay v (hqq'.le.trans hv), hM v ?_⟩⟩
      exact (le_max_right _ _).trans (hq'.le.trans hv)

/-- **The countable localization with the weaker return input** (deterministic). As `exists_exitWindow`, with
`ReturnFree` in place of `OldExitFree`: if the excursion running at `q` ends at a point `y` that `c` first visited at
`v₁ ≤ q` from inside `L`, then `y` is a new exit point for a rational restart time just before `v₁`. -/
theorem exists_exitWindow_of_returnFree {γ : ℝ≥0 → ℂ} (hc : ContinuousOn c (Ioi 0))
    (hc0 : Tendsto (fun v => ‖c v‖) (𝓝[>] 0) atTop) (hcT : Tendsto c atTop (𝓝 0))
    (hcne : ∀ v, 0 < v → c v ≠ 0) (hγ : Tendsto (fun s : ℝ => ‖γ s.toNNReal‖) atTop atTop)
    (hL : IsOpen (leftSideOf (range γ))) {q : ℝ} (hq : 0 < q) (hcq : c q ∈ leftSideOf (range γ))
    (hret : ReturnFree γ c ⊤ q) :
    ∃ t q' x₀ y₀ r : ℚ, 0 < t ∧ 0 < q' ∧ 0 < r ∧ ExitWindow γ c ⊤ t q' ⟨x₀, y₀⟩ r := by
  set L := leftSideOf (range γ) with hLdef
  by_cases hold : OldExitFree γ c ⊤ q
  · exact exists_exitWindow hc hc0 hcT hcne hγ hL hq hcq hold
  simp only [OldExitFree, not_forall, not_not, exists_prop] at hold
  obtain ⟨b, hb, hqb, hall, hbL, v, hv, hvb⟩ := hold
  rw [aliveSet_top] at hb
  -- the first visit `v₁` of `y = c(b)`
  set y := c b with hydef
  obtain ⟨ε₀, hε₀, hε₀le⟩ : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ u ∈ Ioo 0 ε₀, c u ≠ y := by
    have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), ‖y‖ + 1 < ‖c u‖ := hc0.eventually (eventually_gt_atTop _)
    obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    refine ⟨ε₀, hε₀, fun u hu he => ?_⟩
    have h1 : ‖y‖ + 1 < ‖c u‖ :=
      hball ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu.1]; exact hu.2, hu.1⟩
    rw [he] at h1
    linarith
  set A := {u | u ∈ Icc (min ε₀ v / 2) q ∧ c u = y} with hAdef
  have hmin0 : 0 < min ε₀ v / 2 := half_pos (lt_min hε₀ hv.1)
  have hvA : v ∈ A := ⟨⟨(half_le_self (lt_min hε₀ hv.1).le).trans (min_le_right _ _), hv.2⟩, hvb⟩
  have hAc : IsClosed A := by
    have hcI : ContinuousOn c (Icc (min ε₀ v / 2) q) := hc.mono fun u hu => hmin0.trans_le hu.1
    exact hcI.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hAb : BddBelow A := ⟨min ε₀ v / 2, fun u hu => hu.1.1⟩
  set v₁ := sInf A with hv₁def
  have hv₁A : v₁ ∈ A := hAc.csInf_mem ⟨v, hvA⟩ hAb
  have hv₁0 : 0 < v₁ := hmin0.trans_le hv₁A.1.1
  have hv₁q : v₁ ≤ q := hv₁A.1.2
  have hfirst : ∀ u ∈ Ioo 0 v₁, c u ≠ y := fun u hu he => by
    by_cases hu0 : u < min ε₀ v / 2
    · exact hε₀le u ⟨hu.1, hu0.trans_le ((half_le_self (lt_min hε₀ hv.1).le).trans (min_le_left _ _))⟩ he
    · exact absurd (csInf_le hAb ⟨⟨not_lt.1 hu0, hu.2.le.trans hv₁q⟩, he⟩) (not_le.2 hu.2)
  -- `v₁` is reached from inside `L`
  obtain ⟨ε, hε, hεL⟩ := hret b (by rw [aliveSet_top]; exact hb) hqb hall hbL v₁ ⟨hv₁0, hv₁q⟩ hv₁A.2 hfirst
  obtain ⟨q₁, hq₁1, hq₁2⟩ := exists_rat_btwn (show max (v₁ - ε) 0 < v₁ from max_lt (by linarith) hv₁0)
  have hq₁0 : (0 : ℝ) < q₁ := (le_max_right _ _).trans_lt hq₁1
  have hq₁L : c q₁ ∈ L := hεL q₁ ⟨(le_max_left _ _).trans_lt hq₁1, hq₁2⟩
  have hv₁L : c v₁ ∉ L := by rw [hv₁A.2]; exact hbL
  refine exists_exitWindow hc hc0 hcT hcne hγ hL hq₁0 hq₁L ?_
  -- the excursion running at `q₁` ends at `v₁`, a point not visited before
  intro b' _ hq₁b' hall' hb'L u hu
  have hb'v₁ : b' = v₁ := by
    rcases lt_trichotomy b' v₁ with hlt | heq | hgt
    · exact absurd (hεL b' ⟨by linarith [(le_max_left (v₁ - ε) 0).trans_lt hq₁1], hlt⟩) hb'L
    · exact heq
    · exact absurd (hall' v₁ ⟨hq₁2.le, hgt⟩) hv₁L
  rw [hb'v₁, hv₁A.2]
  exact hfirst u ⟨hu.1, hu.2.trans_lt hq₁2⟩

end Core

/-! ### The two named inputs -/

/-- **Named input: the local exit barrier** (Lemma 5.4's pattern with the two curves exchanged, at `κ′ = 16/κ > 4`;
Astra's follow-up Part C.2 as template). Same setting as `Cond44Ref.Prop51QStatement`. For positive rationals `t` (a
flow-line time), `q` (a counterflow restart time), `r` (a radius) and a rational centre `z₀ = x₀ + i y₀`, almost surely
on the glued space the window event `ExitWindow` fails: if the flow line after `t` and the counterflow's past before `q`
leave the boundary of the left side `L` of the flow line untouched in `B̄(z₀, 2r)`, the counterflow started from
`c(q) ∈ L ∩ B(z₀, r)` does not reach `∂L` (or the end of its life) before leaving `B(z₀, r)`.

Inside `B̄(z₀, 2r)` the conditional boundary data given the flow-line prefix `γ(0, t]` and the counterflow prefix
`c((0, q])` are identified on every arc (the left side of `γ`, `ℝ₋`, their junction `0⁻`, the counterflow's own past
sides; Proposition 3.8, the landed union law `CrossCond.ae_condExp_cfGlue` at the deterministic times `t`, `q`), so the
local comparison (Aux. 61–62) with a finite-word reference applies there, and the reference does not reach the left
side of `γ` or `ℝ₋` (Lemma GB7a for every `κ`, `GB7aAbove4.gb7aEvol_right_any`) nor `0⁻` (the junction barrier,
`CfJunction.ae_trace_ne_junction_right`). -/
def CfExitNewStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ t q : ℚ, 0 < t → 0 < q → ∀ x₀ y₀ r : ℚ, 0 < r →
            ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
              ¬ ExitWindow (η p.1) (revLine p.2) p.2.1 t q ⟨x₀, y₀⟩ r

/-- **Named input: no return to an old point** (the configuration the local comparison does not cover). Same setting as
`Cond44Ref.Prop51QStatement`. For each positive rational `q`, almost surely on the glued space, an excursion of the
counterflow in the left side `L` of the flow line that is running at time `q` does not end at a point that the
counterflow visited at a time in `(0, q]` (`OldExitFree`). At such a point the counterflow's past touches `∂L` (from
either side), and the conditional boundary data near it are not identified by Proposition 3.8. -/
def CfExitOldStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ q : ℚ, 0 < q →
            ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
              OldExitFree (η p.1) (revLine p.2) p.2.1 q

/-- **Named input: no return to a boundary point first reached from outside `L`** (weaker than
`CfExitOldStatement`; the residual configuration of the restart argument). Same setting as
`Cond44Ref.Prop51QStatement`. For each positive rational `q`, almost surely on the glued space, an excursion of the
counterflow in the left side `L` of the flow line that is running at time `q` and ends at a point `y` visited before
`q` reached `y` for the first time from inside `L` (`ReturnFree`). The remaining configuration is a counterflow that
first reaches a point of `∂L` from outside `L` (from the right side of the flow line, or along `∂L`), later enters `L`
(through another contact point), and returns to the first point from inside `L`. -/
def CfReturnStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    sleLambda κ - θ₁ * chiC κ ≤ b → sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a →
    ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) ((({0} : Finset ℝ)) : Set ℝ)),
      IsFlowLine κ (Sec7.prop74Data a b) {0} 0 θ₂ P h η ζ →
      ∀ {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
        (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
        IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
        P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂ →
        ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
          P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
          ∀ q : ℚ, 0 < q →
            ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
                ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
              ReturnFree (η p.1) (revLine p.2) p.2.1 q

/-! ### Proposition 5.1 in the chart `Q` from the two inputs -/

/-- The counterflow line of a regular history: continuous on `(0, ∞)`, tending to `∞` at `0⁺` and to `0` at `∞`,
never `0`. -/
theorem revLine_props {y : HistorySpace 0 0} (hβ : IsLoewnerTrace (Prop411Q.cfDrv y) (histLine y))
    (hne : ∀ u : ℝ, 0 < u → histLine y u ≠ 0) (htend : Tendsto (fun u => ‖histLine y u‖) atTop atTop) :
    ContinuousOn (revLine y) (Ioi 0) ∧ Tendsto (fun v => ‖revLine y v‖) (𝓝[>] 0) atTop ∧
      Tendsto (revLine y) atTop (𝓝 0) ∧ ∀ v, 0 < v → revLine y v ≠ 0 := by
  have hnorm : ∀ v, ‖revLine y v‖ = ‖histLine y v‖⁻¹ := fun v => by simp [revLine, negInv]
  refine ⟨?_, ?_, ?_, fun v hv h0 => hne v hv ?_⟩
  · exact ((hβ.2.1.mono fun v (hv : (0 : ℝ) < v) => mem_Ici.2 hv.le).inv₀ fun v hv => hne v hv).neg
  · have hcont : Tendsto (histLine y) (𝓝[>] 0) (𝓝 0) := by
      have := (hβ.2.1 0 (mem_Ici.2 le_rfl)).tendsto.mono_left (nhdsWithin_mono _ fun v (hv : (0 : ℝ) < v) =>
        mem_Ici.2 hv.le)
      rwa [hβ.1] at this
    have hpos : Tendsto (fun v => ‖histLine y v‖) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by simpa using hcont.norm,
        eventually_nhdsWithin_of_forall fun v (hv : (0 : ℝ) < v) => norm_pos_iff.2 (hne v hv)⟩
    exact (tendsto_inv_nhdsGT_zero.comp hpos).congr fun v => (hnorm v).symm
  · exact tendsto_zero_iff_norm_tendsto_zero.2 ((tendsto_inv_atTop_zero.comp htend).congr fun v => (hnorm v).symm)
  · have : ‖histLine y v‖⁻¹ = 0 := by rw [← hnorm, h0, norm_zero]
    exact norm_eq_zero.1 (inv_eq_zero.1 this)

/-- **Proposition 5.1 in the chart `Q` from the local exit barrier and the return input** (given the counterflow's
regularity). -/
theorem prop51QStatement_of_return (hreg : CfLineRegularQStatement.{u}) (hnew : CfExitNewStatement.{u})
    (hret : CfReturnStatement.{u}) : Prop51QStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44₂ := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm₂ := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44₂
  set X := fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) with hXdef
  have hXm : Measurable X := (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have hfl' := ae_glue_fst (μ := P) k hXm (ae_exists_isLoewnerTrace_of_isFlowLine hκ hκ4.le hadm₂ hfl)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hnewG : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ i : ℚ × ℚ × ℚ × ℚ × ℚ, 0 < i.1 → 0 < i.2.1 → 0 < i.2.2.2.2 →
      ¬ ExitWindow (η p.1) (revLine p.2) p.2.1 i.1 i.2.1 ⟨i.2.2.1, i.2.2.2.1⟩ i.2.2.2.2 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : 0 < i.1 ∧ 0 < i.2.1 ∧ 0 < i.2.2.2.2
    · filter_upwards [hnew κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk i.1 i.2.1 hi.1
        hi.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2 hi.2.2] with p hp
      exact fun _ _ _ => hp
    · exact Eventually.of_forall fun p h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ hi
  have holdG : ∀ᵐ p ∂(glueMeasure P k X hXm), ∀ q : ℚ, 0 < q → ReturnFree (η p.1) (revLine p.2) p.2.1 q := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · filter_upwards [hret κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk q hq] with p hp
      exact fun _ => hp
    · exact Eventually.of_forall fun p h => absurd h hq
  filter_upwards [hfl', hregG, hnewG, holdG] with p hp1 hp2 hp3 hp4 s
  obtain ⟨-, -, -, -, hγ⟩ := hp1
  obtain ⟨hy, -, -, hβ, hne, htend⟩ := hp2
  obtain ⟨hc, hc0, hcT, hcne⟩ := revLine_props hβ hne htend
  have hL : IsOpen (leftSideOf (range (η p.1))) := by
    rw [← arcRange_toNNReal]
    exact Cond44Ref.isOpen_leftSideOf_arcRange hγ
  unfold cfPts
  split_ifs with hs
  · intro hmem
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs.1
    have hret' : ReturnFree (η p.1) (revLine p.2) ⊤ s := hy ▸ hp4 s hs.1
    obtain ⟨t, q', x₀, y₀, r, ht, hq', hr, hW⟩ :=
      exists_exitWindow_of_returnFree hc hc0 hcT hcne hγ.tendsto hL hs0 hmem hret'
    exact hp3 ⟨t, q', x₀, y₀, r⟩ ht hq' hr (hy ▸ hW)
  · exact fun h0 => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h0.1.1)

/-- The no-return input implies the return input. -/
theorem cfReturnStatement_of_cfExitOld (hold : CfExitOldStatement.{u}) : CfReturnStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk q hq
  filter_upwards [hold κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk q hq] with p hp
  exact hp.returnFree

/-- **Proposition 5.1 in the chart `Q` from the local exit barrier and the no-return input** (given the counterflow's
regularity). -/
theorem prop51QStatement_of_exit (hreg : CfLineRegularQStatement.{u}) (hnew : CfExitNewStatement.{u})
    (hold : CfExitOldStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_return hreg hnew (cfReturnStatement_of_cfExitOld hold)

/-- **The restart input `CfFirstContactQStatement` from the local exit barrier and the return input** (given the
counterflow's regularity). -/
theorem cfFirstContactQStatement_of_return (hreg : CfLineRegularQStatement.{u}) (hnew : CfExitNewStatement.{u})
    (hret : CfReturnStatement.{u}) : CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_prop51Q hreg (prop51QStatement_of_return hreg hnew hret)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs at `16/κ`, the local exit barrier and the return
input.** -/
theorem prop51QStatement_of_partA_of_return (hA : PartAInputsSixteenDiv) (hnew : CfExitNewStatement.{u})
    (hret : CfReturnStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_return (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hnew hret

/-- **The restart input `CfFirstContactQStatement` from the local exit barrier and the no-return input** (given the
counterflow's regularity). -/
theorem cfFirstContactQStatement_of_exit (hreg : CfLineRegularQStatement.{u}) (hnew : CfExitNewStatement.{u})
    (hold : CfExitOldStatement.{u}) : CfFirstContactQStatement.{u} :=
  cfFirstContactQStatement_of_prop51Q hreg (prop51QStatement_of_exit hreg hnew hold)

/-- **The whole-life input `CfAvoidLeftQStatement` from the two inputs** (given the counterflow's regularity). -/
theorem cfAvoidLeftQStatement_of_exit (hreg : CfLineRegularQStatement.{u}) (hnew : CfExitNewStatement.{u})
    (hold : CfExitOldStatement.{u}) : CfAvoidLeftQStatement.{u} :=
  cfAvoidLeftQStatement_of_prop51Q hreg (prop51QStatement_of_exit hreg hnew hold)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs at `16/κ` and the two inputs.** -/
theorem prop51QStatement_of_partA_of_exit (hA : PartAInputsSixteenDiv) (hnew : CfExitNewStatement.{u})
    (hold : CfExitOldStatement.{u}) : Prop51QStatement.{u} :=
  prop51QStatement_of_exit (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hnew hold

/-! ### Both inputs are consequences of Proposition 5.1 -/

/-- At an alive positive time the completed-range points are the counterflow points. -/
theorem cfPts_eq_revLine {y : HistorySpace 0 0} {q : ℚ} (hq : 0 < q) (hqA : (q : ℝ) ∈ aliveSet y.1) :
    cfPts y q = revLine y q := by
  unfold cfPts
  split_ifs with hc
  · rfl
  · exact absurd ⟨hq, hqA.2⟩ hc

/-- **The local exit barrier is implied by Proposition 5.1**: an excursion into `L` never starts. -/
theorem cfExitNewStatement_of_prop51Q (h51 : Prop51QStatement.{u}) : CfExitNewStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk t q ht hq x₀ y₀ r hr
  filter_upwards [h51 κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk] with p hp
  rintro ⟨-, -, hex⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rcases hex with ⟨b', hb', hqb, hall, -⟩ | ⟨hqA, hall⟩
  · have hqA : (q : ℝ) ∈ aliveSet p.2.1 := ⟨hq0, ofReal_lt_of_le_of_mem_aliveSet hqb.le hb'⟩
    exact hp q (by rw [cfPts_eq_revLine hq hqA]; exact (hall q ⟨le_rfl, hqb⟩).1)
  · exact hp q (by rw [cfPts_eq_revLine hq hqA]; exact (hall q hqA le_rfl).1)

/-- **The no-return input is implied by Proposition 5.1**: an excursion into `L` never starts. -/
theorem cfExitOldStatement_of_prop51Q (h51 : Prop51QStatement.{u}) : CfExitOldStatement.{u} := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk q hq
  filter_upwards [h51 κ hκ hκ4 a b θ₁ θ₂ h12 hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk] with p hp
  intro b' hb' hqb hall _
  have hqA : (q : ℝ) ∈ aliveSet p.2.1 := ⟨by exact_mod_cast hq, ofReal_lt_of_le_of_mem_aliveSet hqb.le hb'⟩
  exact absurd (hall q ⟨le_rfl, hqb⟩) (by rw [← cfPts_eq_revLine hq hqA]; exact hp q)

/-- **The return input is implied by Proposition 5.1.** -/
theorem cfReturnStatement_of_prop51Q (h51 : Prop51QStatement.{u}) : CfReturnStatement.{u} :=
  cfReturnStatement_of_cfExitOld (cfExitOldStatement_of_prop51Q h51)

end InteractingSLE.Sec5.CfFirstContactQ
