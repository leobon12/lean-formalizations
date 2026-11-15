/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BrReidx

/-!
# The kernel loss of a moving candidate

Packet PROVE-GW2-BUF (round 18; the kernel bound). `Q n a k` is the event that candidate `a` is good from version `k`
on: measurable and increasing in `k`. One re-indexing `ψ a m ≥ m` (monotone, independent of `n`) makes the loss of
ANY selected candidate `sel n m` vanish under the conditional law. The loss is the event that the candidate is good
from some version on but not from `ψ (sel n m) m`.

* **`exists_reindex_kernel_loss`**: `GW2Bh.exists_reindex_uniform` and `GW2Bh.ae_eventually_kernel_le`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

/-- **One re-indexing makes the kernel loss of every selected candidate vanish.** -/
theorem exists_reindex_kernel_loss {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (Q : ℕ → ℕ → ℕ → Set Ω)
    (hQ : ∀ n a k, MeasurableSet (Q n a k)) (hmono : ∀ n a, Monotone (Q n a)) :
    ∃ ψ : ℕ → ℕ → ℕ, (∀ a, Monotone (ψ a)) ∧ (∀ a m, m ≤ ψ a m) ∧
      ∀ᵐ ω₀ ∂P, ∀ (sel : ℕ → ℕ → ℕ) (n : ℕ) {ε : ℝ≥0∞}, 0 < ε → ∀ᶠ m in atTop,
        condExpKernel P 𝒢 ω₀ ({ξ | ∃ k, ξ ∈ Q n (sel n m) k} \ Q n (sel n m) (ψ (sel n m) m)) ≤ ε := by
  obtain ⟨ψ, hψm, hψle, hψ⟩ := exists_reindex_uniform (μ := P) Q hQ hmono
  refine ⟨ψ, hψm, hψle, ?_⟩
  set B : ℕ → ℕ → ℕ → Set Ω := fun n a m => {ξ | ∃ k, ξ ∈ Q n a k} \ Q n a (ψ a m) with hBdef
  have hB : ∀ n a m, MeasurableSet (B n a m) := fun n a m => by
    have : {ξ | ∃ k, ξ ∈ Q n a k} = ⋃ k, Q n a k := by ext ξ; simp
    simp only [hBdef]
    rw [this]
    exact (MeasurableSet.iUnion fun k => hQ n a k).diff (hQ n a _)
  have hgood : ∀ᵐ ξ ∂P, ∀ n, ∀ᶠ m in atTop, ∀ a, ξ ∉ B n a m := by
    filter_upwards [hψ] with ξ hξ n
    filter_upwards [hξ n] with m hm a hmem
    exact hmem.2 (hm a hmem.1)
  filter_upwards [ae_eventually_kernel_le h𝒢 B hB hgood] with ω₀ hω₀ sel n ε hε
  exact hω₀ sel n hε

end InteractingSLE.Theorem14.GW2Bh
