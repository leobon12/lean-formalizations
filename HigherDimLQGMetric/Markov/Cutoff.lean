import HigherDimLQGMetric.Markov.Riesz
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth cutoffs separated from an exterior point

An exterior logarithmic kernel is smooth near the bounded interior set. A cutoff equal to one
on the closure of the interior and zero near the exterior point turns it into a globally
smooth compact Cameron–Martin shift.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Metric TopologicalSpace
open HigherDimLFPP (Rd)
open scoped Topology

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- A compact smooth cutoff equal to one on `V̄` and zero near `x ∉ V̄`. -/
theorem markov_exists_cutoff (V : Opens (Rd d))
    (hVb : Bornology.IsBounded (V : Set (Rd d)))
    {x : Rd d} (hx : x ∈ extOpen V) :
    ∃ χ : Rd d → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ y ∈ closure (V : Set (Rd d)), χ y = 1) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ ball x ε, χ y = 0) := by
  let K : Set (Rd d) := closure (V : Set (Rd d))
  have hKc : IsClosed K := isClosed_closure
  obtain ⟨R, hR, hKR⟩ := hVb.closure.exists_pos_norm_lt
  have hxK : x ∉ K := hx
  have hnhds : Kᶜ ∈ 𝓝 x := hKc.isOpen_compl.mem_nhds hxK
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let U : Set (Rd d) := ball 0 R ∩ (closedBall x (ε / 2))ᶜ
  have hUo : IsOpen U := isOpen_ball.inter isClosed_closedBall.isOpen_compl
  have hKU : K ⊆ U := by
    intro y hy
    refine ⟨by simpa only [mem_ball, dist_zero_right] using hKR y hy, ?_⟩
    have hdist : ε ≤ dist x y := by
      apply le_of_not_gt
      intro hlt
      have hyball : y ∈ ball x ε := by
        simpa only [mem_ball, dist_comm] using hlt
      exact (hball hyball) hy
    exact by
      change y ∉ closedBall x (ε / 2)
      simp only [mem_closedBall, not_le]
      have hdist' : ε ≤ dist y x := by simpa only [dist_comm] using hdist
      linarith
  obtain ⟨χ, hχ, _, hsupp, hχ1⟩ :=
    (exists_contDiff_support_eq_eq_one_iff (n := ⊤) hUo hKc hKU)
  have hχc : HasCompactSupport χ := by
    rw [HasCompactSupport]
    have hc : tsupport χ ⊆ closedBall (0 : Rd d) R := by
      rw [tsupport, hsupp]
      exact closure_minimal (fun y hy => ball_subset_closedBall hy.1) isClosed_closedBall
    exact (isCompact_closedBall (0 : Rd d) R).of_isClosed_subset (isClosed_tsupport χ) hc
  refine ⟨χ, hχ, hχc, (fun y hy => (hχ1 y).mp hy), ε / 2, by positivity, ?_⟩
  intro y hy
  by_contra hn
  have hys : y ∈ Function.support χ := hn
  rw [hsupp] at hys
  exact hys.2 (ball_subset_closedBall hy)

/-- The singular logarithmic kernel becomes globally smooth after multiplication by a cutoff
that vanishes near its pole. -/
theorem markov_contDiff_cutLog (x : Rd d) {χ : Rd d → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hzero : ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ ball x ε, χ y = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : Rd d => χ y * (-Real.log ‖x - y‖)) := by
  obtain ⟨ε, hε, hχ0⟩ := hzero
  refine contDiff_iff_contDiffAt.mpr fun y => ?_
  by_cases hy : y = x
  · subst y
    have heq : (fun y : Rd d => χ y * (-Real.log ‖x - y‖)) =ᶠ[𝓝 x]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with y hy
      simp [hχ0 y hy]
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hsub : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : Rd d => x - q) y := by fun_prop
    have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : Rd d => Real.log ‖x - q‖) y :=
      (hsub.norm ℝ hne).log (norm_ne_zero_iff.mpr hne)
    exact hχ.contDiffAt.mul hlog.neg

theorem markov_hasCompactSupport_cutLog (x : Rd d) {χ : Rd d → ℝ}
    (hχ : HasCompactSupport χ) :
    HasCompactSupport (fun y : Rd d => χ y * (-Real.log ‖x - y‖)) :=
  hχ.mul_right

/-- If the normalizing test is supported in `V`, every recentered interior generator remains
supported in `V`. -/
theorem markov_insideTest_tsupport (V : Opens (Rd d)) {ρ : TestRd d}
    (hρ : ∫ x, ρ x = 1) (hρV : tsupport (ρ : Rd d → ℝ) ⊆ V)
    (φ : TestOn V) :
    tsupport ((markovInsideTest V hρ φ).1 : Rd d → ℝ) ⊆ V := by
  have hφV : tsupport ((testIncl V φ) : Rd d → ℝ) ⊆ V := by
    rw [coe_testIncl]
    exact φ.tsupport_subset
  change tsupport (fun y : Rd d => (testIncl V φ) y -
    (∫ x, (testIncl V φ) x) • ρ y) ⊆ V
  exact (tsupport_sub _ _).trans (union_subset hφV
    ((tsupport_smul_subset_right (fun _ => ∫ x, (testIncl V φ) x) ρ).trans hρV))

/-- A compact shift whose pairing with interior mean-zero tests is the formal covariance with
the field normalized at `ρ` and evaluated at the exterior point `x`. -/
def markovCutKernel {d : ℕ} (ρ : TestRd d) (χ : Rd d → ℝ) (x y : Rd d) : ℝ :=
  χ y * (-Real.log ‖x - y‖ - markovLogPot ρ y)

theorem markov_contDiff_cutKernel (hd : 1 ≤ d) (ρ : TestRd d) (x : Rd d)
    {χ : Rd d → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hzero : ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ ball x ε, χ y = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (markovCutKernel ρ χ x) := by
  have h1 := markov_contDiff_cutLog x hχ hzero
  have h2 := hχ.mul (markov_contDiff_logPot hd ρ)
  have he : markovCutKernel ρ χ x =
      (fun y => χ y * (-Real.log ‖x - y‖)) -
        (fun y => χ y * markovLogPot ρ y) := by
    funext y
    simp only [markovCutKernel, Pi.sub_apply]
    ring
  rw [he]
  exact h1.sub h2

theorem markov_hasCompactSupport_cutKernel (ρ : TestRd d) (x : Rd d)
    {χ : Rd d → ℝ} (hχ : HasCompactSupport χ) :
    HasCompactSupport (markovCutKernel ρ χ x) := hχ.mul_right

end HigherDimLQGMetric
