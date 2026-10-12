import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

/-! The compact-domain subsequence step for normalized local power primitives. -/

open scoped NNReal Topology BoundedContinuousFunction
open Filter

namespace BouRabeeGwynne

/-- On one compact inner ball, bounded primitives with one Lipschitz constant
have a convergent subsequence, and the limit retains the same constant. -/
theorem meshOnly_compact_lipschitz_subsequence {X : Type*}
    [PseudoMetricSpace X] [CompactSpace X] (f : ℕ → X →ᵇ ℝ)
    (C : ℝ≥0) (M : ℝ) (hlip : ∀ n, LipschitzWith C (f n))
    (hbound : ∀ n x, |f n x| ≤ M) :
    ∃ g : X →ᵇ ℝ, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      Tendsto (f ∘ σ) atTop (𝓝 g) ∧ LipschitzWith C g ∧
      ∀ x, Tendsto (fun n => f (σ n) x) atTop (𝓝 (g x)) := by
  have hin : ∀ (g : X →ᵇ ℝ) (x : X), g ∈ Set.range f → g x ∈ Set.Icc (-M) M := by
    rintro g x ⟨n, rfl⟩
    exact abs_le.mp (hbound n x)
  have hequi : Equicontinuous ((↑) : Set.range f → X → ℝ) := by
    apply UniformEquicontinuous.equicontinuous
    apply LipschitzWith.uniformEquicontinuous _ C
    rintro ⟨g, n, rfl⟩
    exact hlip n
  have hcompact := BoundedContinuousFunction.arzela_ascoli
    (Set.Icc (-M) M) isCompact_Icc (Set.range f) hin hequi
  obtain ⟨g, _, σ, hσ, ht⟩ := hcompact.tendsto_subseq (x := f)
    (fun n => subset_closure (Set.mem_range_self n))
  have hpoint (x : X) : Tendsto (fun n => f (σ n) x) atTop (𝓝 (g x)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.tendsto g).comp ht
  refine ⟨g, σ, hσ, ht, ?_, hpoint⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact le_of_tendsto ((hpoint x).dist (hpoint y))
    (Eventually.of_forall fun n => (hlip (σ n)).dist_le_mul x y)

end BouRabeeGwynne
