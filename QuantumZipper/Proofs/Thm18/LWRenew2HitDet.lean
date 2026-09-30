import QuantumZipper.Proofs.Thm18.LWRenew2HitAdapt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWS-0′-HIT, part 2: deterministic hitting criterion through rational times

For a path `γ` continuous on `[0,v]` and a set `K`, the path meets `closure K` at some time of
`[σ,v]` iff for every `n` some rational time `q ∈ [0,v]` with `σ < q + 1/(n+1)` has
`γ q` within `1/(n+1)` of a point of `K` (`hit_iff_rat`). This is the countable reduction in the
classical proof that the hitting time of a closed set by a continuous adapted process is a stopping
time (Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Problem 1.2.7; Revuz–Yor,
*Continuous Martingales and Brownian Motion*, Prop. I.4.5); the formulation with the slack
`σ < q + 1/(n+1)` (so that the start time `σ` need not be rational) is own elementary bookkeeping.
-/

noncomputable section

open Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- **Rational hitting criterion** (deterministic). -/
theorem hit_iff_rat {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {v σ : ℝ}
    (hγ : ContinuousOn γ (Icc 0 v)) (K : Set X) :
    (∃ s ∈ Icc σ v, 0 ≤ s ∧ γ s ∈ closure K) ↔
      ∀ n : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc 0 v ∧ σ < q + 1 / ((n : ℝ) + 1) ∧
        ∃ z ∈ K, dist (γ q) z < 1 / ((n : ℝ) + 1) := by
  constructor
  · rintro ⟨s, ⟨hσs, hsv⟩, hs0, hsK⟩ n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsI : s ∈ Icc 0 v := ⟨hs0, hsv⟩
    obtain ⟨δ, hδ, hδp⟩ :=
      Metric.continuousWithinAt_iff.1 (hγ s hsI) (1 / ((n : ℝ) + 1) / 2) (by positivity)
    obtain ⟨z, hzK, hz⟩ := Metric.mem_closure_iff.1 hsK (1 / ((n : ℝ) + 1) / 2) (by positivity)
    set η := min δ (1 / ((n : ℝ) + 1)) with hη
    have hη0 : 0 < η := lt_min hδ hε
    obtain ⟨q, hq0, hqv, hqs⟩ : ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ v ∧ |(q : ℝ) - s| < η := by
      by_cases hs : 0 < s
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hs (by linarith : s - η < s))
        refine ⟨q, (le_max_left _ _).trans hq1.le, hq2.le.trans hsv, ?_⟩
        rw [abs_lt]
        constructor
        · linarith [(le_max_right 0 (s - η)).trans_lt hq1]
        · linarith
      · have hs' : s = 0 := le_antisymm (not_lt.1 hs) hs0
        refine ⟨0, by simp, by simpa [hs'] using hsv.trans' hs0.ge.le |>.trans' le_rfl, ?_⟩
        simp [hs', hη0]
    refine ⟨q, ⟨hq0, hqv⟩, ?_, z, hzK, ?_⟩
    · have := (abs_lt.1 (lt_of_lt_of_le hqs (min_le_right _ _))).1
      linarith
    · have h1 := hδp ⟨hq0, hqv⟩ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hqs (min_le_left _ _))
      calc dist (γ q) z ≤ dist (γ q) (γ s) + dist (γ s) z := dist_triangle _ _ _
        _ < 1 / ((n : ℝ) + 1) / 2 + 1 / ((n : ℝ) + 1) / 2 := add_lt_add h1 hz
        _ = 1 / ((n : ℝ) + 1) := by ring
  · intro h
    choose q hqI hσq z hzK hz using h
    obtain ⟨s, hsI, φ, hφ, hlim⟩ :=
      isCompact_Icc.tendsto_subseq (x := fun n => ((q n : ℚ) : ℝ)) hqI
    have hinv : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).comp hφ.tendsto_atTop
    refine ⟨s, ⟨?_, hsI.2⟩, hsI.1, ?_⟩
    · have h1 := hlim.add hinv
      rw [add_zero] at h1
      exact ge_of_tendsto h1 (Eventually.of_forall fun k => (hσq (φ k)).le)
    · rw [Metric.mem_closure_iff]
      intro ε hε
      have hγlim : Tendsto (fun k => γ (q (φ k))) atTop (𝓝 (γ s)) :=
        (hγ s hsI).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => hqI (φ k)⟩)
      obtain ⟨k1, hk1⟩ := Metric.tendsto_atTop.1 hγlim (ε / 2) (by positivity)
      obtain ⟨k2, hk2⟩ := Metric.tendsto_atTop.1 hinv (ε / 2) (by positivity)
      set k := max k1 k2
      have a1 := hk1 k (le_max_left _ _)
      have a2 : 1 / ((φ k : ℝ) + 1) < ε / 2 := by
        have := hk2 k (le_max_right _ _)
        rw [Real.dist_eq, sub_zero] at this
        exact (abs_lt.1 this).2
      refine ⟨z (φ k), hzK _, ?_⟩
      calc dist (γ s) (z (φ k)) ≤ dist (γ s) (γ (q (φ k))) + dist (γ (q (φ k))) (z (φ k)) :=
            dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (by rw [dist_comm]; exact a1) ((hz _).trans a2)
        _ = ε := by ring

end LWFar
end Thm18Asm
end QuantumZipper
