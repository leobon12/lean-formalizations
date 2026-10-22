import HigherDimLQGMetric.Sec10.LocalTransfer

/-! A compact family containing all locally controlled Weyl metrics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Topology Metric Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Compactness of Weyl metrics with a compact pure family and deterministic local weight
bounds. The weight is bounded independently on each Euclidean ball. -/
theorem s8a_exists_localCompact_of_bounds
    {K : Set C(Rd d × Rd d, ℝ)} (hK : IsCompact K) (hKn : K.Nonempty)
    (hKm : K ⊆ {M | IsContinuousMetric M}) (C : ℕ → ℝ) :
    ∃ T : Set C(Rd d × Rd d, ℝ), IsCompact T ∧
      T ⊆ {E | IsContinuousMetric E} ∧
      ∀ (M : ContMetric d), M.1 ∈ K → M.IsLength →
        ∀ (ξ : ℝ) (w : C(Rd d, ℝ)),
          (∀ (n : ℕ) z, z ∈ ball (0 : Rd d) (n + 2) →
            -C n ≤ ξ * w z ∧ ξ * w z ≤ C n) →
          ∀ E : C(Rd d × Rd d, ℝ), IsContinuousMetric E →
            (∀ x y, ENNReal.ofReal (E (x, y)) = weylScale ξ w M x y) →
              E ∈ T := by
  let ρ : ℕ → ℝ := fun n => Classical.choose (s8a_exists_uniform_sphere_gap hK hKm n)
  have hρ : ∀ n, 0 < ρ n ∧ ∀ M ∈ K,
      ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ z ∈ sphere (0 : Rd d) (n + 2), ρ n ≤ M (x, z) := by
    intro n
    exact Classical.choose_spec (s8a_exists_uniform_sphere_gap hK hKm n)
  let lmb : ℕ → ℕ → ℝ := fun n m =>
    Classical.choose (s8a_exists_ball_offdiag_gap hK hKm n m)
  have hlmb : ∀ n m, 0 < lmb n m ∧ ∀ M ∈ K,
      ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ y ∈ closedBall (0 : Rd d) (n + 2),
        1 / ((m : ℝ) + 1) ≤ ‖y - x‖ → lmb n m ≤ M (x, y) := by
    intro n m
    exact Classical.choose_spec (s8a_exists_ball_offdiag_gap hK hKm n m)
  let η : ℕ → ℕ → ℝ := fun n m =>
    min (ρ n) ((1 / ((m : ℝ) + 1)) / Real.exp (C n))
  have hη : ∀ n m, 0 < η n m := by
    intro n m
    exact lt_min (hρ n).1 (div_pos (by positivity) (Real.exp_pos _))
  let δ : ℕ → ℕ → ℝ := fun n m =>
    Classical.choose (s8a_exists_supEnvelope_modulus hK hKn hKm n (hη n m))
  have hδ : ∀ n m, 0 < δ n m ∧
      ∀ x ∈ closedBall (0 : Rd d) n,
      ∀ y ∈ closedBall (0 : Rd d) n,
        ‖x - y‖ ≤ δ n m → s8a_supEnvelope K (x, y) < η n m := by
    intro n m
    exact Classical.choose_spec (s8a_exists_supEnvelope_modulus hK hKn hKm n (hη n m))
  let k : ℕ → ℕ → ℕ := fun n m =>
    Classical.choose (exists_nat_one_div_lt
      (mul_pos (Real.exp_pos (-C n)) (lt_min (hlmb n m).1 (hρ n).1)))
  have hk : ∀ n m, 1 / (((k n m : ℕ) : ℝ) + 1) <
      Real.exp (-C n) * min (lmb n m) (ρ n) := by
    intro n m
    exact Classical.choose_spec (exists_nat_one_div_lt
      (mul_pos (Real.exp_pos (-C n)) (lt_min (hlmb n m).1 (hρ n).1)))
  let T := s8a_localModulusSet (d := d) δ k
  have hT : IsCompact T := s8a_localModulusSet_isCompact δ k (fun n m => (hδ n m).1)
  have hTm : T ⊆ {E | IsContinuousMetric E} := s8a_localModulusSet_metric δ k
  refine ⟨T, hT, hTm, ?_⟩
  intro M hM hMl ξ w hw E hE heq
  change E ∈ metricAlgSet_select (d := d) ∩
    (⋂ n, ⋂ m, s8a_upperModSet δ n m) ∩
    (⋂ n, ⋂ m, metricSepSet_select n m (k n m))
  refine ⟨⟨⟨hE.self_eq_zero, hE.symm, hE.triangle⟩, ?_⟩, ?_⟩
  · apply mem_iInter.mpr
    intro n
    apply mem_iInter.mpr
    intro m x hx y hy hxy
    have hMsmall : M.1 (x, y) < ρ n := by
      calc M.1 (x, y) ≤ s8a_supEnvelope K (x, y) := s8a_le_supEnvelope hK hM _
        _ < η n m := (hδ n m).2 x hx y hy hxy
        _ ≤ ρ n := min_le_left _ _
    have hweight : ∀ z ∈ ball (0 : Rd d) (n + 2), ξ * w z ≤ C n :=
      fun z hz => (hw n z hz).2
    have hup := s8a_weylScale_upper_of_ball hM hMl (hρ n).1 (hρ n).2
      hweight hx hMsmall
    rw [← heq] at hup
    have hreal : E (x, y) ≤ Real.exp (C n) * M.1 (x, y) :=
      (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (Real.exp_pos _).le (M.nonneg x y))).1 hup
    have henv := s8a_le_supEnvelope hK hM (x, y)
    have hbound : E (x, y) < Real.exp (C n) * η n m := by
      exact (hreal.trans (mul_le_mul_of_nonneg_left henv (Real.exp_pos _).le)).trans_lt
        (mul_lt_mul_of_pos_left ((hδ n m).2 x hx y hy hxy) (Real.exp_pos _))
    have hηb : Real.exp (C n) * η n m ≤ 1 / ((m : ℝ) + 1) := by
      dsimp [η]
      have := min_le_right (ρ n) ((1 / ((m : ℝ) + 1)) / Real.exp (C n))
      calc Real.exp (C n) * min (ρ n) ((1 / ((m : ℝ) + 1)) / Real.exp (C n))
          ≤ Real.exp (C n) * ((1 / ((m : ℝ) + 1)) / Real.exp (C n)) :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = _ := by field_simp
    exact (hbound.trans_le hηb).le
  · apply mem_iInter.mpr
    intro n
    apply mem_iInter.mpr
    intro m x hx y hxy
    have hweight : ∀ z ∈ ball (0 : Rd d) (n + 2),
        -C n ≤ ξ * w z := fun z hz => (hw n z hz).1
    have hlow := s8a_weylScale_sep_lower hM hMl (hρ n).2 (hlmb n m).2
      hweight hx (by simpa only [norm_sub_rev] using hxy)
    rw [← heq] at hlow
    have hreal : Real.exp (-C n) * min (lmb n m) (ρ n) ≤ E (x, y) :=
      (ENNReal.ofReal_le_ofReal_iff (s8a_metricFn_nonneg hE x y)).1 hlow
    exact (hk n m).le.trans hreal

end HigherDimLQGMetric
