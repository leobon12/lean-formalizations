import HigherDimLQGMetric.Bilip.GoodScalesAE

/-!
# Proposition 3.13: global comparison of jointly local metrics

The larger-shell event is an a.s. measurable representative of the comparison
event. Its eventual occurrence on every dyadic grid, together with the sphere
chain, compares the metrics everywhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric Filter
open HigherDimLFPP (Rd)
open scoped ENNReal

theorem l7d_bilip : L7d_bilip := by
  classical
  intro d hd
  obtain ⟨p, hp, hp1, hgood⟩ := bilip_goodScales_ae_eventually hd
  refine ⟨p, hp, hp1, ?_⟩
  intro ξ Ω mΩ P hProb h D₁ D₂ hh hxi C hC hprob
  let Q (z : Rd d) (r : ℝ) (hr : 0 < r) :=
    bilipOuterEvent_aeLocal hd hxi z hr C
  let E : Rd d → ℝ → Set Ω := fun z r =>
    if hr : 0 < r then Classical.choose (Q z r hr) else ∅
  have hEm (z : Rd d) (r : ℝ) (hr : 0 < r) :
      MeasurableSet[
        fieldSigmaRd (fun ω => l7b_recenter (h ω) r z)
          (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
        famSigmaRd (rescFam ξ h D₁ z r)
          (shellOpen z ((1 / 4) * r) (4 * r)) ⊔
        famSigmaRd (rescFam ξ h D₂ z r)
          (shellOpen z ((1 / 4) * r) (4 * r))] (E z r) := by
    dsimp [E]
    rw [dite_eq_left hr]
    exact (Classical.choose_spec (Q z r hr)).1
  have hEq (z : Rd d) (r : ℝ) (hr : 0 < r) :
      {ω | bilipOuterEvent (D₁ ω) (D₂ ω) z r C} =ᵐ[P] E z r := by
    dsimp [E]
    rw [dite_eq_left hr]
    exact (Classical.choose_spec (Q z r hr)).2
  have hpE (z : Rd d) (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal p ≤ P (E z r) := by
    have hsub : {ω | internalDiamRd (D₂ ω) (sphere z r)
        (shellOpen z (r / 2) (2 * r)) ≤ ENNReal.ofReal C *
          infPairs (D₁ ω).1 (sphere z (r / 2)) (sphere z r)} ⊆
        {ω | bilipOuterEvent (D₁ ω) (D₂ ω) z r C} := by
      intro ω hω
      exact bilip_outerEvent_of_inner (D₁ ω) (D₂ ω) z hr hω
    calc
      ENNReal.ofReal p ≤ P {ω | internalDiamRd (D₂ ω) (sphere z r)
          (shellOpen z (r / 2) (2 * r)) ≤ ENNReal.ofReal C *
            infPairs (D₁ ω).1 (sphere z (r / 2)) (sphere z r)} := hprob z r hr
      _ ≤ P {ω | bilipOuterEvent (D₁ ω) (D₂ ω) z r C} := measure_mono hsub
      _ = P (E z r) := measure_congr (hEq z r hr)
  have hCover : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
        ball (0 : Rd d) (1 / sharpMesh n),
        ∃ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k ∧
          1 / 2 ^ k ≤ sharpMesh n ∧ ω ∈ E w (1 / 2 ^ k) :=
    hgood ξ P h D₁ D₂ hh hxi E hEm hpE
  let F (n : ℕ) : Finset (Rd d) :=
    shellGridBox d
      (⌈(1 / sharpMesh n) / ((sharpMesh n) ^ 2 / (10 * d))⌉₊ + 1)
      ((sharpMesh n) ^ 2 / (10 * d))
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hF (n : ℕ) :
      gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
        ball (0 : Rd d) (1 / sharpMesh n) ⊆ (F n : Set (Rd d)) := by
    apply grid_ball_subset_shellGridBox
    · exact div_pos (sq_pos_of_pos (sharpMesh_pos n)) (by positivity)
    · exact (one_div_pos.mpr (sharpMesh_pos n)).le
  have hEqAll : ∀ᵐ ω ∂P,
      ∀ n : ℕ, ∀ w : {x : Rd d // x ∈ F n}, ∀ k : ℕ,
        (ω ∈ E w.1 (1 / 2 ^ k)) ↔
          bilipOuterEvent (D₁ ω) (D₂ ω) w.1 (1 / 2 ^ k) C := by
    apply ae_all_iff.2
    intro n
    apply ae_all_iff.2
    intro w
    apply ae_all_iff.2
    intro k
    have hk : 0 < (1 / 2 ^ k : ℝ) := by positivity
    filter_upwards [hEq w.1 (1 / 2 ^ k) hk] with ω hω
    exact (Iff.of_eq hω).symm
  have hOuterCover : ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
        ball (0 : Rd d) (1 / sharpMesh n),
        ∃ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k ∧
          1 / 2 ^ k ≤ sharpMesh n ∧
          bilipOuterEvent (D₁ ω) (D₂ ω) w (1 / 2 ^ k) C := by
    filter_upwards [hCover, hEqAll] with ω hcov heq
    filter_upwards [hcov] with n hn
    intro w hw
    obtain ⟨k, hklo, hkhi, hmem⟩ := hn w hw
    exact ⟨k, hklo, hkhi, (heq n ⟨w, hF n hw⟩ k).mp hmem⟩
  filter_upwards [hxi.2.2.1, hOuterCover] with ω hlen hgrid
  exact bilip_compare_of_eventual_grids hd (D₁ ω) (D₂ ω) hlen.1 hC hgrid

end HigherDimLQGMetric
