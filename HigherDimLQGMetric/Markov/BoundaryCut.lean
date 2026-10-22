import HigherDimLQGMetric.Markov.MainCore
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Smooth compact cutoffs exhausting either side of a null frontier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- A compact set inside an open set has a smooth compact cutoff supported in that open set,
equal to one on the compact set and between zero and one everywhere. -/
theorem markov_exists_compactCutoff (U : Opens (Rd d)) (K : Compacts (Rd d))
    (hKU : (K : Set (Rd d)) ⊆ U) :
    ∃ χ : TestRd d,
      tsupport (χ : Rd d → ℝ) ⊆ U ∧
      (∀ x ∈ K, χ x = 1) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) := by
  have hKc : IsCompact (K : Set (Rd d)) := K.isCompact
  have hUnhds : (U : Set (Rd d)) ∈ 𝓝ˢ (K : Set (Rd d)) :=
    U.isOpen.mem_nhdsSet.mpr hKU
  obtain ⟨U₀, hU₀o, hKU₀, hU₀U⟩ := hKc.exists_isOpen_closure_subset hUnhds
  obtain ⟨R, hR, hKR⟩ := hKc.isBounded.exists_pos_norm_lt
  let W : Set (Rd d) := U₀ ∩ ball 0 R
  have hWo : IsOpen W := hU₀o.inter isOpen_ball
  have hKW : (K : Set (Rd d)) ⊆ W := by
    intro x hx
    exact ⟨hKU₀ hx, by simpa only [mem_ball, dist_zero_right] using hKR x hx⟩
  have hWc : IsCompact (closure W) :=
    (isCompact_closedBall (0 : Rd d) R).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ball_subset_closedBall hx.2) isClosed_closedBall)
  have hWU : closure W ⊆ U :=
    (closure_mono inter_subset_left).trans hU₀U
  obtain ⟨χ, hχd, hχr, hχs, hχ1⟩ :=
    (exists_contDiff_support_eq_eq_one_iff (n := ⊤) hWo hKc.isClosed hKW)
  have hχc : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    rw [tsupport, hχs]
    exact hWc
  let θ : TestRd d :=
    { toFun := χ
      contDiff' := hχd
      hasCompactSupport' := hχc
      tsupport_subset' := subset_univ _ }
  refine ⟨θ, ?_, ?_, ?_⟩
  · change tsupport χ ⊆ U
    rw [tsupport, hχs]
    exact hWU
  · intro x hx
    exact (hχ1 x).mp hx
  · intro x
    exact hχr (mem_range_self x)

/-- A fixed choice of smooth compact cutoff for each compact exhaustion level. -/
def markovExhaustCut (U : Opens (Rd d)) (n : ℕ) : TestRd d :=
  Classical.choose (markov_exists_compactCutoff U (exhaustK U n) (exhaustK_subset U n))

theorem markovExhaustCut_support (U : Opens (Rd d)) (n : ℕ) :
    tsupport (markovExhaustCut U n : Rd d → ℝ) ⊆ U :=
  (Classical.choose_spec
    (markov_exists_compactCutoff U (exhaustK U n) (exhaustK_subset U n))).1

theorem markovExhaustCut_one (U : Opens (Rd d)) (n : ℕ)
    (x : Rd d) (hx : x ∈ exhaustK U n) : markovExhaustCut U n x = 1 :=
  (Classical.choose_spec
    (markov_exists_compactCutoff U (exhaustK U n) (exhaustK_subset U n))).2.1 x hx

theorem markovExhaustCut_range (U : Opens (Rd d)) (n : ℕ) (x : Rd d) :
    0 ≤ markovExhaustCut U n x ∧ markovExhaustCut U n x ≤ 1 :=
  (Classical.choose_spec
    (markov_exists_compactCutoff U (exhaustK U n) (exhaustK_subset U n))).2.2 x

theorem markovExhaustCut_zero (U : Opens (Rd d)) (n : ℕ)
    (x : Rd d) (hx : x ∉ U) : markovExhaustCut U n x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun ht => hx (markovExhaustCut_support U n ht))

/-- The exhaustion cutoffs are eventually one at every point of their open set. -/
theorem markovExhaustCut_eventually_one (U : Opens (Rd d))
    (x : Rd d) (hx : x ∈ U) :
    ∀ᶠ n : ℕ in atTop, markovExhaustCut U n x = 1 := by
  obtain ⟨N, hN⟩ := exists_exhaustK_superset U isCompact_singleton
    (singleton_subset_iff.mpr hx)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply markovExhaustCut_one U n x
  exact exhaustK_mono U hn (hN (mem_singleton x))

end HigherDimLQGMetric
