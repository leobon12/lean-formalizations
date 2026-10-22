import HigherDimLQGMetric.Sec4.Lemma44

/-!
# Deterministic comparisons for [1] Lemma 4.5 (packet L9b)

Lower bounds of distances between `B_δ(0)` and `B_δ(2e₁)` by across distances of `A_{1/2,1}(0)` and upper bounds of
the distance from `0` to `2e₁` (both on `∂B_1(e₁)`) by sphere diameters, for the weak metric and for the LFPP of a
continuous field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn PcwJoined lfppLength)

variable {d : ℕ}

/-- a path from `B_{r/2}(u)` to the outside of `B_r(u)` has internal length at least the across distance -/
theorem l9b_acrossDist_le_internal (D₀ : ContMetric d) (V : Set (Rd d)) {u x y : Rd d} {r : ℝ}
    (hx : ‖x - u‖ < r / 2) (hy : r ≤ ‖y - u‖) : acrossDist D₀ u (r / 2) r ≤ D₀.internal V x y := by
  rw [D₀.internal_eq_iInf_len]
  refine le_iInf fun P => le_iInf fun hP => le_iInf fun hP0 => le_iInf fun hP1 => le_iInf fun _ => ?_
  have hcont : ContinuousOn (fun t => ‖P t - u‖) (Icc 0 1) := (hP.sub continuousOn_const).norm
  have hr0 : 0 < r := by have := norm_nonneg (x - u); linarith
  have hmem : r ∈ Icc ((fun t => ‖P t - u‖) 0) ((fun t => ‖P t - u‖) 1) := by
    simp only [hP0, hP1]
    exact ⟨by linarith, hy⟩
  obtain ⟨b, hb, hbu⟩ := intermediate_value_Icc zero_le_one hcont hmem
  have hPa : ‖P 0 - u‖ < r / 2 := by rw [hP0]; exact hx
  calc acrossDist D₀ u (r / 2) r ≤ D₀.len P 0 b :=
        l9b_acrossDist_le_len D₀ hb.1 (hP.mono (Icc_subset_Icc le_rfl hb.2)) hPa hbu
    _ ≤ D₀.len P 0 1 := D₀.len_mono P le_rfl hb.2

theorem l9b_acrossDist_le_setDistIn (D₀ : ContMetric d) (V : Set (Rd d)) {u : Rd d} {r : ℝ}
    {A B : Set (Rd d)} (hA : ∀ x ∈ A, ‖x - u‖ < r / 2) (hB : ∀ y ∈ B, r ≤ ‖y - u‖) :
    acrossDist D₀ u (r / 2) r ≤ setDistIn D₀ V A B :=
  le_iInf₂ fun x hx => le_iInf₂ fun y hy => l9b_acrossDist_le_internal D₀ V (hA x hx) (hB y hy)

/-- internal distances between points of a sphere are bounded by the sphere diameter -/
theorem l9b_internal_le_sphereDiam (D₀ : ContMetric d) {V : Set (Rd d)} {u x y : Rd d} {r : ℝ}
    (hV : ann u (r / 2) (2 * r) ⊆ V) (hx : x ∈ sphere u r) (hy : y ∈ sphere u r) :
    D₀.internal V x y ≤ sphereDiam D₀ u r :=
  (D₀.internal_anti hV x y).trans (le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl))

/-- the LFPP analogue -/
theorem l9b_fieldDistIn_le_lfppDiam (hd : 2 ≤ d) {ξ : ℝ} {ψ : Rd d → ℝ} (hψ : Continuous ψ)
    {V : Set (Rd d)} {u x y : Rd d} {r : ℝ} (hr : 0 < r) (hV : ann u (r / 2) (2 * r) ⊆ V)
    (hx : x ∈ sphere u r) (hy : y ∈ sphere u r) :
    fieldDistIn ξ ψ V x y ≤
      ENNReal.ofReal (DGZ.lfppDiam ξ ψ (sphere u r) (ann u (r / 2) (2 * r))) := by
  have hSA : sphere u r ⊆ ann u (r / 2) (2 * r) := l9b_sphere_subset_ann (by linarith) (by linarith)
  have hAo : IsOpen (ann u (r / 2) (2 * r)) := isOpen_ann _ _ _
  have hAc : IsPreconnected (ann u (r / 2) (2 * r)) :=
    (config_isConnected_ann hd u (by positivity) (by linarith)).2
  have hj : PcwJoined (ann u (r / 2) (2 * r)) x y :=
    DGZ.pcwJoined_of_isPreconnected hAo hAc (hSA hx) (hSA hy)
  have hbdd := DGZ.bddAbove_lfppDiam_of_isCompact hAo hAc hψ ξ (isCompact_sphere u r) hSA
    subset_rfl
  calc fieldDistIn ξ ψ V x y ≤ fieldDistIn ξ ψ (ann u (r / 2) (2 * r)) x y := fieldDistIn_mono hV
    _ = ENNReal.ofReal (lfppDistOn ξ ψ (ann u (r / 2) (2 * r)) x y) := fieldDistIn_eq_ofReal hψ hj
    _ ≤ _ := ENNReal.ofReal_le_ofReal (DGZ.lfppDistOn_le_lfppDiam hbdd hx hy)

/-- the LFPP set distance from `B̄_{1/2}(0)` to the outside of `B_1(0)` dominates the internal set distance
between the spheres in `A_{1/3,3}(0)` -/
theorem l9b_lfppSetDist_le_fieldSetDistIn {ξ : ℝ} {ψ : Rd d → ℝ} (hψ : Continuous ψ)
    (W A B : Set (Rd d)) (hA : ∀ x ∈ A, ‖x‖ ≤ 1 / 2) (hB : ∀ y ∈ B, 1 ≤ ‖y‖) :
    ENNReal.ofReal (DGZ.lfppSetDist ξ ψ (ann 0 (1 / 3) 3) (sphere 0 (1 / 2)) (sphere 0 1)) ≤
      fieldSetDistIn ξ ψ W A B := by
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  by_cases hj : PcwJoined W x y
  · rw [fieldDistIn_eq_ofReal hψ hj]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsh := DGZ.isShellPair_ball (0 : Rd d) (show (1 / 2 : ℝ) < 1 by norm_num)
    have hV : closedBall (0 : Rd d) 1 \ ball 0 (1 / 2) ⊆ ann 0 (1 / 3) 3 := by
      intro v hv
      have h1 : ‖v‖ ≤ 1 := by rw [← dist_zero_right]; exact hv.1
      have h2 : 1 / 2 ≤ ‖v‖ := by rw [← dist_zero_right]; exact not_lt.1 hv.2
      refine ⟨?_, ?_⟩ <;> simp only [sub_zero] <;> linarith
    have := hsh.lfppSetDist_le_lfppDistOn (ξ := ξ) hψ hV
      (by rw [mem_closedBall, dist_zero_right]; exact hA x hx)
      (by rw [mem_ball, dist_zero_right, not_lt]; exact hB y hy) hj
    rwa [closedBall_sdiff_ball, closedBall_sdiff_ball] at this
  · rw [fieldDistIn_eq_top hj]
    exact le_top

end HigherDimLQGMetric
