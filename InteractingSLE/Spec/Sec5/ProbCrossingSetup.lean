/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.ProbCrossingPath
import InteractingSLE.Spec.Sec5.ProbCutDrift

/-!
# Lemma 5.10: the drift `U`, the Girsanov integrand on the marks, and the parameters

Packet PROVE-SEC5-B (specification §5.2, Lemma 5.10, `source/spec/p097-144.md` L922–L959).

* `otherDrift`: Lemma 5.10's `U = ∑_{i ≤ k} ρ^{i,L}/(W − V^{i,L}) + ∑_{2 ≤ i ≤ ℓ} ρ^{i,R}/(W − V^{i,R})`, the
  drift of every force point except the first right one (with the integrated force convention: the value at a
  collision is irrelevant, collisions occupy a Lebesgue-null set of times);
* `crossF`: the Girsanov integrand `crossIntegrand` as a function of the time, the driver and all marks
  (`Girsanov.allMarks`), measurable (`measurable_crossF`) and continuous away from collisions and from the
  switching time (`continuousAt_crossF`);
* `exists_crossing_params`: a lower bound `ρ_* > −2` and a bound `ρ_max` on a compact `J ⊂ (−2, ∞)`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

variable {nL nR : ℕ}

/-- **Lemma 5.10's `U`**: the drift of the force points other than the first right one. -/
def otherDrift (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ) (vL : Fin nL → ℝ)
    (vR : Fin (nR + 1) → ℝ) : ℝ :=
  (∑ i, ρL i / (w - vL i)) + ∑ i : Fin nR, ρR i.succ / (w - vR i.succ)

/-- The left marks in a vector indexed like `Girsanov.allMarks`. -/
def markL (u : Fin (nL + (nR + 1)) → ℝ) (i : Fin nL) : ℝ := u (Fin.castAdd (nR + 1) i)

/-- The right marks in a vector indexed like `Girsanov.allMarks`. -/
def markR (u : Fin (nL + (nR + 1)) → ℝ) (i : Fin (nR + 1)) : ℝ := u (Fin.natAdd nL i)

/-- The Girsanov integrand of the proof of Lemma 5.10 as a function of time, driver and marks. -/
def crossF (κ C : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) (g : ℝ) (s : ℝ≥0) (t : ℝ≥0) (w : ℝ)
    (u : Fin (nL + (nR + 1)) → ℝ) : ℝ :=
  crossIntegrand κ C (ρR 0) g s t w (markR u 0) (otherDrift ρL ρR w (markL u) (markR u))

theorem measurable_otherDrift_pair (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) :
    Measurable fun p : ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
      otherDrift ρL ρR p.1 (markL p.2) (markR p.2) := by
  unfold otherDrift markL markR
  refine Measurable.add (Finset.measurable_sum _ fun i _ => ?_) (Finset.measurable_sum _ fun i _ => ?_)
  · exact measurable_const.div (measurable_fst.sub ((measurable_pi_apply _).comp measurable_snd))
  · exact measurable_const.div (measurable_fst.sub ((measurable_pi_apply _).comp measurable_snd))

theorem measurable_crossF (κ C : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) {g : ℝ} (hg : 0 < g)
    (s : ℝ≥0) : Measurable (uncurry3 (crossF κ C ρL ρR g s)) := by
  have hO : Measurable fun p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
      otherDrift ρL ρR p.2.1 (markL p.2.2) (markR p.2.2) :=
    (measurable_otherDrift_pair ρL ρR).comp measurable_snd
  have h1 : Measurable fun p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
      clampAbs (C / Real.sqrt κ) (otherDrift ρL ρR p.2.1 (markL p.2.2) (markR p.2.2) / Real.sqrt κ) :=
    (continuous_clampAbs _).measurable.comp (hO.div_const _)
  have h2 : Measurable fun p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
      ρR 0 / Real.sqrt κ * Girsanov.recipCut (g / 2) (p.2.1 - markR p.2.2 0) :=
    measurable_const.mul ((Girsanov.continuous_recipCut (half_pos hg)).measurable.comp
      (measurable_snd.fst.sub ((measurable_pi_apply _).comp measurable_snd.snd)))
  have hS : MeasurableSet {p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) | s ≤ p.1} :=
    measurable_fst measurableSet_Ici
  have h3 : Measurable fun p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
      if s ≤ p.1 then ρR 0 / Real.sqrt κ * Girsanov.recipCut (g / 2) (p.2.1 - markR p.2.2 0)
      else 0 := Measurable.ite hS h2 measurable_const
  exact h1.add h3

theorem abs_crossF_le {κ C : ℝ} (hC : 0 ≤ C) {ρL : Fin nL → ℝ} {ρR : Fin (nR + 1) → ℝ} {ρmax : ℝ}
    (hρ : |ρR 0| ≤ ρmax) {g : ℝ} (hg : 0 < g) (s t : ℝ≥0) (w : ℝ) (u : Fin (nL + (nR + 1)) → ℝ) :
    |crossF κ C ρL ρR g s t w u| ≤ C / Real.sqrt κ + ρmax / Real.sqrt κ * (g / 2)⁻¹ := by
  refine (abs_crossIntegrand_le hC hg _ _ _ _ _).trans (add_le_add le_rfl ?_)
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 (half_pos hg).le)
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg κ)]
  exact div_le_div_of_nonneg_right hρ (Real.sqrt_nonneg κ)

/-- **Continuity of the integrand** away from the switching time and from collisions of the driver with the
marks of `U`. -/
theorem continuousAt_crossF (κ C : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (nR + 1) → ℝ) {g : ℝ} (hg : 0 < g)
    (s : ℝ≥0) {t : ℝ≥0} {w : ℝ} {u : Fin (nL + (nR + 1)) → ℝ} (hts : t ≠ s)
    (hL : ∀ i, w ≠ markL u i) (hR : ∀ i, w ≠ markR u i) :
    ContinuousAt (uncurry3 (crossF κ C ρL ρR g s)) (t, w, u) := by
  have hO : ContinuousAt (fun p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
      otherDrift ρL ρR p.2.1 (markL p.2.2) (markR p.2.2)) (t, w, u) := by
    unfold otherDrift
    refine ContinuousAt.add ?_ ?_
    · refine tendsto_finsetSum _ fun i _ => ?_
      refine continuousAt_const.div (continuousAt_snd.fst.sub
        ((continuous_apply _).continuousAt.comp continuousAt_snd.snd)) ?_
      exact sub_ne_zero.2 (hL i)
    · refine tendsto_finsetSum _ fun i _ => ?_
      refine continuousAt_const.div (continuousAt_snd.fst.sub
        ((continuous_apply _).continuousAt.comp continuousAt_snd.snd)) ?_
      exact sub_ne_zero.2 (hR i.succ)
  have h1 := (continuous_clampAbs (C / Real.sqrt κ)).continuousAt.comp (hO.div_const (Real.sqrt κ))
  have h2 : ContinuousAt (fun p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
      if s ≤ p.1 then ρR 0 / Real.sqrt κ * Girsanov.recipCut (g / 2) (p.2.1 - markR p.2.2 0)
      else 0) (t, w, u) := by
    rcases lt_or_gt_of_ne hts with hlt | hgt
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [continuousAt_fst.eventually (gt_mem_nhds hlt)] with p hp
      simp [not_le.2 hp]
    · have hc : ContinuousAt (fun p : ℝ≥0 × ℝ × (Fin (nL + (nR + 1)) → ℝ) =>
          ρR 0 / Real.sqrt κ * Girsanov.recipCut (g / 2) (p.2.1 - markR p.2.2 0)) (t, w, u) :=
        (continuousAt_const.mul ((Girsanov.continuous_recipCut (half_pos hg)).continuousAt.comp
          (continuousAt_snd.fst.sub ((continuous_apply _).continuousAt.comp continuousAt_snd.snd))))
      refine hc.congr ?_
      filter_upwards [continuousAt_fst.eventually (lt_mem_nhds hgt)] with p hp
      simp [hp.le]
  exact h1.add h2

/-- **Parameters of a compact `J ⊂ (−2, ∞)`**: a lower bound `ρ_* > −2` and a bound `ρ_max ≥ 0`. -/
theorem exists_crossing_params {J : Set ℝ} (hJ : IsCompact J) (hJ2 : J ⊆ Set.Ioi (-2)) :
    ∃ ρlo ρmax : ℝ, -2 < ρlo ∧ 0 ≤ ρmax ∧ ∀ ρ ∈ J, ρlo ≤ ρ ∧ |ρ| ≤ ρmax := by
  rcases J.eq_empty_or_nonempty with hJe | hJne
  · exact ⟨0, 0, by norm_num, le_rfl, fun ρ hρ => by simp [hJe] at hρ⟩
  · obtain ⟨R, hR⟩ := hJ.exists_bound_of_continuousOn continuousOn_id
    refine ⟨sInf J, max R 0, hJ2 (hJ.sInf_mem hJne), le_max_right _ _, fun ρ hρ =>
      ⟨csInf_le hJ.bddBelow hρ, ?_⟩⟩
    have := hR ρ hρ
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

end Sec5

end InteractingSLE
