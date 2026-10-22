import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Amplify.Geodesic
import HigherDimLQGContinuity.Improve.SmallDistance

/-!
# The escape estimate supplies the source barrier

The diameter in the escape premise dominates the source unit distance.
Thus a lower bound on that distance turns relative escape into the absolute
barrier used in the forcing count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open scoped ENNReal

/-- On the relative escape event, a lower bound for the unit distance gives
the absolute barrier between the two outer spheres. -/
theorem q11_escape_barrier {d : ℕ} (hd : 1 ≤ d) (G : ContMetric d)
    {u M K S : ℝ} (hu : 0 < u) (hM : 0 ≤ M)
    (hK : 8 * M / u ≤ K) (hunit : u ≤ G.1 (0, e₁ d))
    (hesc : ENNReal.ofReal K * diamIn G (ball 0 8) (ball 0 4) <
      setDistIn G univ (sphere 0 8) (sphere 0 (4 * S))) :
    ENNReal.ofReal (8 * M) < setDistIn G univ (sphere 0 8) (sphere 0 (4 * S)) := by
  have hK0 : 0 ≤ K := (div_nonneg (by positivity) hu.le).trans hK
  have hKu : 8 * M ≤ K * u := by
    have h := (div_le_iff₀ hu).mp hK
    nlinarith only [h]
  have hzero : (0 : Rd d) ∈ ball 0 4 := mem_ball_self (by norm_num)
  have hone : e₁ d ∈ ball (0 : Rd d) 4 := by
    rw [mem_ball, dist_zero_right, HigherDimLFPP.norm_e₁ hd]
    norm_num
  have hdiam : ENNReal.ofReal u ≤ diamIn G (ball 0 8) (ball 0 4) :=
    (ENNReal.ofReal_le_ofReal hunit).trans (p7_ofReal_le_diamIn G hzero hone)
  have hmul : ENNReal.ofReal (K * u) ≤ ENNReal.ofReal K * diamIn G (ball 0 8) (ball 0 4) := by
    rw [ENNReal.ofReal_mul hK0]
    exact mul_le_mul_of_nonneg_left hdiam bot_le
  exact ((ENNReal.ofReal_le_ofReal hKu).trans hmul).trans_lt hesc

/-- The uniform inverse crossing moment and relative escape estimate give an
absolute barrier beyond a deterministic radius. -/
theorem q11_barrier_prob {d : ℕ} (hd : 3 ≤ d) {ξbar s M ε : ℝ}
    (hs : 0 < s) (hM : 0 < M) (hε : 0 < ε)
    (hU : UniformEstimates d ξbar s) :
    ∃ S : ℝ, 4 ≤ S ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d s {g | ¬ ENNReal.ofReal (8 * M) <
            setDistIn (rho D g) univ (sphere 0 8) (sphere 0 (4 * S))} ≤
              ENNReal.ofReal ε := by
  obtain ⟨Kinv, hKinv, hsmall⟩ := q11_small_distance_prob (by omega) hs hU
  let u : ℝ := ε / (2 * Kinv)
  have hu : 0 < u := by dsimp [u]; positivity
  let K : ℝ := max 1 (8 * M / u)
  have hK : 1 ≤ K := le_max_left _ _
  have hK' : 8 * M / u ≤ K := le_max_right _ _
  obtain ⟨pesc, hpesc, hesc⟩ := hU.escape
  obtain ⟨CK, hCK⟩ := hesc K hK
  let C' : ℝ := max CK 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let S : ℝ := max 4 ((2 * C' / ε) ^ pesc⁻¹)
  have hS4 : 4 ≤ S := le_max_left _ _
  have hS : 0 < S := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hS4
  have hCS : CK * S ^ (-pesc) ≤ ε / 2 := by
    have hpow : 2 * C' / ε ≤ S ^ pesc := by
      calc 2 * C' / ε = ((2 * C' / ε) ^ pesc⁻¹) ^ pesc :=
            (Real.rpow_inv_rpow (by positivity) hpesc.ne').symm
        _ ≤ S ^ pesc := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hpesc.le
    have hpoly : C' / S ^ pesc ≤ ε / 2 := by
      rw [div_le_iff₀ (Real.rpow_pos_of_pos hS pesc)]
      rw [div_le_iff₀ hε] at hpow
      nlinarith only [hpow]
    calc CK * S ^ (-pesc) ≤ C' * S ^ (-pesc) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hS.le _)
      _ = C' / S ^ pesc := by rw [Real.rpow_neg hS.le]; ring
      _ ≤ ε / 2 := hpoly
  refine ⟨S, hS4, ?_⟩
  intro ξ hξ D hD
  let Bsmall : Set (DistRd d) := {g | (rho D g).1 (0, e₁ d) < u}
  let Besc : Set (DistRd d) := {g | ¬ ENNReal.ofReal K *
    diamIn (rho D g) (ball 0 8) (ball 0 4) <
      setDistIn (rho D g) univ (sphere 0 8) (sphere 0 (4 * S))}
  have hsub : {g | ¬ ENNReal.ofReal (8 * M) <
      setDistIn (rho D g) univ (sphere 0 8) (sphere 0 (4 * S))} ⊆
      Bsmall ∪ Besc := by
    intro g hg
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    have hunit : u ≤ (rho D g).1 (0, e₁ d) := le_of_not_gt hnot.1
    exact hg (q11_escape_barrier (by omega) (rho D g) hu hM.le hK' hunit
      (not_not.mp hnot.2))
  have hsmall' : pinLaw d s Bsmall ≤ ENNReal.ofReal (ε / 2) := by
    have h := hsmall ξ hξ D hD u hu
    convert h using 1
    dsimp [u]
    field_simp
  have hesc' : pinLaw d s Besc ≤ ENNReal.ofReal (ε / 2) := by
    have h := (hCK ξ hξ D hD 4 S (by norm_num) hS4).trans
      (ENNReal.ofReal_le_ofReal hCS)
    simpa only [Besc, show (2 : ℝ) * 4 = 8 by norm_num, mul_comm S 4] using h
  calc
    pinLaw d s {g | ¬ ENNReal.ofReal (8 * M) <
      setDistIn (rho D g) univ (sphere 0 8) (sphere 0 (4 * S))}
        ≤ pinLaw d s (Bsmall ∪ Besc) := measure_mono hsub
    _ ≤ pinLaw d s Bsmall + pinLaw d s Besc := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hsmall' hesc'
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end HigherDimLQGContinuity
