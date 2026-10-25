import SupercriticalLQGUniqueness.B2.DG20Lim.Diagonal

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private def δ (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

private theorem δ_pos (m : ℕ) : 0 < δ m := by
  unfold δ
  positivity

private theorem δ_tendsto : Tendsto δ atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

 
theorem exists_shrinking_ratCircles (z : ℂ) :
    ∃ O : ℕ → RatCircle,
      (∀ m, (O m).Surrounds z ∧ (O m).closedDisk ⊆ ball z (δ m)) ∧
      Tendsto (fun m => ((O m).radius : ℝ)) atTop (nhds 0) := by
  have hs : ∀ m, ∃ O : RatCircle,
      O.Surrounds z ∧ O.closedDisk ⊆ ball z (δ m) ∧ (O.radius : ℝ) < δ m := by
    intro m
    exact exists_ratCircle_surrounding_small z (δ_pos m)
  choose O hO hsmall hr using hs
  refine ⟨O, fun m => ⟨hO m, hsmall m⟩, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds δ_tendsto
  · intro m
    change (0 : ℝ) ≤ ((O m).radius : ℝ)
    exact_mod_cast (O m).radius_nonneg
  · intro m
    exact (hr m).le

 

theorem RData.exists_pointDist_recovery (R : RData)
    (D : ℕ → LQGMetric.ContMetric)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (nhds (R.across O P)))
    (z w : ℂ) :
    ∃ zn wn : ℕ → ℂ,
      Tendsto zn atTop (nhds z) ∧ Tendsto wn atTop (nhds w) ∧
        Tendsto (fun n => ENNReal.ofReal ((D n).1 (zn n, wn n)))
          atTop (nhds (R.DfromR z w)) := by
  by_cases hzw : z = w
  · subst w
    refine ⟨fun _ => z, fun _ => z, tendsto_const_nhds, tendsto_const_nhds, ?_⟩
    have hzero : ∀ n, (D n).1 (z, z) = 0 := fun n => (D n).2.self_eq_zero z
    simp only [hzero, ENNReal.ofReal_zero, R.DfromR_self]
    exact tendsto_const_nhds
  obtain ⟨O, hO, hrO⟩ := exists_shrinking_ratCircles z
  obtain ⟨P, hP, hrP⟩ := exists_shrinking_ratCircles w
  have hlim : Tendsto (fun m => R.across (O m) (P m)) atTop
      (nhds (R.DfromR z w)) :=
    R.tendsto_across_shrinking hzw O P
      (Eventually.of_forall fun m => (hO m).1)
      (Eventually.of_forall fun m => (hP m).1) hrO hrP
  let e := ENNReal.orderIsoUnitIntervalBirational.toHomeomorph
  have hlim' : Tendsto (fun m => e (R.across (O m) (P m))) atTop
      (nhds (e (R.DfromR z w))) := (e.continuous.tendsto _).comp hlim
  have hconv' : ∀ m, Tendsto
      (fun n => e (LQGMetric.Blueprint.setDist (D n) (O m).toSet (P m).toSet))
      atTop (nhds (e (R.across (O m) (P m)))) := by
    intro m
    exact (e.continuous.tendsto _).comp (hcircle (O m) (P m))
  obtain ⟨k, hk, hkdist'⟩ := exists_tendsto_diagonal
    (fun n m => e (LQGMetric.Blueprint.setDist (D n) (O m).toSet (P m).toSet))
    (fun m => e (R.across (O m) (P m))) (e (R.DfromR z w)) hconv' hlim'
  have hkdist : Tendsto
      (fun n => LQGMetric.Blueprint.setDist (D n) (O (k n)).toSet (P (k n)).toSet)
      atTop (nhds (R.DfromR z w)) := by
    have h := (e.symm.continuous.tendsto (e (R.DfromR z w))).comp hkdist'
    simpa only [Function.comp_def, e.symm_apply_apply] using h
  have hmins : ∀ n m, ∃ u ∈ (O m).toSet, ∃ v ∈ (P m).toSet,
      ENNReal.ofReal ((D n).1 (u, v)) =
        LQGMetric.Blueprint.setDist (D n) (O m).toSet (P m).toSet := by
    intro n m
    exact exists_circleDist_minimizers (D n) (O m) (P m)
  choose u hu v hv heq using hmins
  let zn : ℕ → ℂ := fun n => u n (k n)
  let wn : ℕ → ℂ := fun n => v n (k n)
  have hδk : Tendsto (fun n => δ (k n)) atTop (nhds 0) := δ_tendsto.comp hk
  have hzn : Tendsto zn atTop (nhds z) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hev : ∀ᶠ n in atTop, δ (k n) < ε :=
      (tendsto_order.1 hδk).2 ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    exact (mem_ball.mp ((hO (k n)).2
      ((O (k n)).toSet_subset_closedDisk (hu n (k n))))).trans (hN n hn)
  have hwn : Tendsto wn atTop (nhds w) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hev : ∀ᶠ n in atTop, δ (k n) < ε :=
      (tendsto_order.1 hδk).2 ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    exact (mem_ball.mp ((hP (k n)).2
      ((P (k n)).toSet_subset_closedDisk (hv n (k n))))).trans (hN n hn)
  refine ⟨zn, wn, hzn, hwn, ?_⟩
  have heq' : (fun n => ENNReal.ofReal ((D n).1 (zn n, wn n))) =
      (fun n => LQGMetric.Blueprint.setDist (D n) (O (k n)).toSet (P (k n)).toSet) := by
    funext n
    exact heq n (k n)
  rw [heq']
  exact hkdist

end SupercriticalLQGUniqueness.B2.DG20Lim
