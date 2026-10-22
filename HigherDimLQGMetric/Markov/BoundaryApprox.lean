import HigherDimLQGMetric.Markov.BoundaryCut

/-! Test approximation away from a Lebesgue-null frontier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped RealInnerProductSpace Topology
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- Product of two compactly supported smooth tests. -/
def markovTestMul (φ ψ : TestRd d) : TestRd d :=
  { toFun := fun x => φ x * ψ x
    contDiff' := φ.contDiff.mul ψ.contDiff
    hasCompactSupport' := φ.hasCompactSupport.mul_right
    tsupport_subset' := subset_univ _ }

@[simp] theorem markovTestMul_apply (φ ψ : TestRd d) (x : Rd d) :
    markovTestMul φ ψ x = φ x * ψ x := rfl

theorem markovTestMul_tsupport_right (φ ψ : TestRd d) :
    tsupport (markovTestMul φ ψ : Rd d → ℝ) ⊆ tsupport (ψ : Rd d → ℝ) := by
  change tsupport ((fun x => φ x * ψ x) : Rd d → ℝ) ⊆ tsupport (ψ : Rd d → ℝ)
  exact tsupport_mul_subset_right

/-- The part of a test function left after cutting it into its interior and exterior parts. -/
def markovBoundaryError (V : Opens (Rd d)) (φ : TestRd d) (n : ℕ) : TestRd d :=
  φ - markovTestMul φ (markovExhaustCut V n) -
    markovTestMul φ (markovExhaustCut (extOpen V) n)

@[simp] theorem markovBoundaryError_apply (V : Opens (Rd d))
    (φ : TestRd d) (n : ℕ) (x : Rd d) :
    markovBoundaryError V φ n x =
      φ x * (1 - markovExhaustCut V n x - markovExhaustCut (extOpen V) n x) := by
  simp only [markovBoundaryError, sub_apply, markovTestMul_apply]
  ring

theorem markovBoundaryError_abs_le (V : Opens (Rd d))
    (φ : TestRd d) (n : ℕ) (x : Rd d) :
    |markovBoundaryError V φ n x| ≤ |φ x| := by
  let a := markovExhaustCut V n x
  let b := markovExhaustCut (extOpen V) n x
  have ha := markovExhaustCut_range V n x
  have hb := markovExhaustCut_range (extOpen V) n x
  have hsum : a + b ≤ 1 := by
    by_cases hx : x ∈ V
    · have hb0 : b = 0 := markovExhaustCut_zero (extOpen V) n x
        (fun hxo => hxo (subset_closure hx))
      dsimp [b] at hb0
      linarith
    · have ha0 : a = 0 := markovExhaustCut_zero V n x hx
      dsimp [a] at ha0
      linarith
  have hc : 0 ≤ 1 - a - b ∧ 1 - a - b ≤ 1 := by
    constructor <;> linarith [ha.1, hb.1]
  rw [markovBoundaryError_apply, abs_mul]
  have hca : |1 - a - b| ≤ 1 := by
    rw [abs_of_nonneg hc.1]
    exact hc.2
  exact mul_le_of_le_one_right (abs_nonneg _) hca

theorem markovBoundaryError_eventually_zero (V : Opens (Rd d))
    (φ : TestRd d) (x : Rd d)
    (hx : x ∈ (V : Set (Rd d)) ∪ (extOpen V : Set (Rd d))) :
    ∀ᶠ n : ℕ in atTop, markovBoundaryError V φ n x = 0 := by
  rcases hx with hx | hx
  · filter_upwards [markovExhaustCut_eventually_one V x hx] with n hn
    have hη0 : markovExhaustCut (extOpen V) n x = 0 :=
      markovExhaustCut_zero (extOpen V) n x
        (fun hxo => hxo (subset_closure hx))
    simp [markovBoundaryError_apply, hn, hη0]
  · filter_upwards [markovExhaustCut_eventually_one (extOpen V) x hx] with n hn
    have hχ0 : markovExhaustCut V n x = 0 :=
      markovExhaustCut_zero V n x (fun hxV => hx (subset_closure hxV))
    simp [markovBoundaryError_apply, hn, hχ0]

/-- Under a null-frontier condition, the (L^1) norm of the boundary error tends to zero. -/
theorem markovBoundaryError_L1_tendsto_zero (V : Opens (Rd d))
    (φ : TestRd d) (hnull : volume (frontier (V : Set (Rd d))) = 0) :
    Tendsto (fun n => ∫ x, |markovBoundaryError V φ n x|) atTop (𝓝 0) := by
  have hfront : ∀ᵐ x : Rd d ∂volume,
      x ∈ (V : Set (Rd d)) ∪ (extOpen V : Set (Rd d)) := by
    rw [ae_iff]
    have he : ((V : Set (Rd d)) ∪ (extOpen V : Set (Rd d)))ᶜ =
        frontier (V : Set (Rd d)) := by
      ext x
      rw [V.isOpen.frontier_eq]
      change x ∉ (V : Set (Rd d)) ∪ (closure (V : Set (Rd d)))ᶜ ↔
        x ∈ closure (V : Set (Rd d)) \ (V : Set (Rd d))
      simp only [mem_union, mem_compl_iff, not_or, not_not, Set.mem_sdiff]
      tauto
    change volume (((V : Set (Rd d)) ∪ (extOpen V : Set (Rd d)))ᶜ) = 0
    rw [he]
    exact hnull
  have hlim : ∀ᵐ x : Rd d ∂volume,
      Tendsto (fun n => |markovBoundaryError V φ n x|) atTop (𝓝 0) := by
    filter_upwards [hfront] with x hx
    have he := markovBoundaryError_eventually_zero V φ x hx
    exact tendsto_const_nhds.congr' (by
      filter_upwards [he] with n hn
      simp [hn])
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => |markovBoundaryError V φ n x|) volume :=
    (continuous_abs.comp (markovBoundaryError V φ n).continuous).measurable.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x : Rd d ∂volume,
      ‖|markovBoundaryError V φ n x|‖ ≤ |φ x| :=
    ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_abs] using
      markovBoundaryError_abs_le V φ n x
  have hdom : Integrable (fun x : Rd d => |φ x|) := (integrable_testOn φ).abs
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun x : Rd d => |φ x|) hmeas hdom hbound hlim

end HigherDimLQGMetric
