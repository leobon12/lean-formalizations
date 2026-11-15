/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdoReidx
import InteractingSLE.Spec.Supplement.GW2BnLoss
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# The near losses uniformly over candidates and buffers: re-indexing and the kernel bound

Packet PROVE-GW2-BUF (round 15). The near candidate `nearCandidate l ω n m` changes with `m`. Each candidate's good
event (the near exit before the lower cap of its version `k`) holds eventually in `k`. The lossy near facts need this
eventually in `m` simultaneously for the selected candidate. The version index cannot depend on the buffer index `n`.

* **`exists_reindex_uniform`**: increasing measurable good events `G n a k` under a finite measure. There is a
  re-indexing `ψ a m ≥ m`, monotone in `m`, independent of `n`, with: almost surely, for every `n`, eventually in `m`,
  every candidate `a` whose events eventually hold is good at `ψ a m`. Proof: SDE's `exists_reindex_eventually_all` on
  the pairs `(n, a)`, then `ψ a m = max_{n ≤ m} ψ' (n, a) m`.
* **`ae_eventually_kernel_le`**: if almost surely, for every `n`, eventually in `m`, every candidate is good at index
  `m`, then for `P`-a.e. `ω₀` under `condExpKernel P 𝒢 ω₀` the bad set of ANY selected candidate `a ω₀ n m` has
  measure `≤ ε` eventually in `m`, for every `ε > 0` (`GW2BnLoss`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

/-- **Re-indexing uniform in candidates and buffers** (versions independent of the buffer index). -/
theorem exists_reindex_uniform {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (G : ℕ → ℕ → ℕ → Set Ω) (hG : ∀ n a k, MeasurableSet (G n a k)) (hmono : ∀ n a, Monotone (G n a)) :
    ∃ ψ : ℕ → ℕ → ℕ, (∀ a, Monotone (ψ a)) ∧ (∀ a m, m ≤ ψ a m) ∧
      ∀ᵐ ω ∂μ, ∀ n, ∀ᶠ m in atTop, ∀ a, (∃ k, ω ∈ G n a k) → ω ∈ G n a (ψ a m) := by
  set E : ℕ → ℕ → Set Ω := fun b k => G (Nat.unpair b).1 (Nat.unpair b).2 k with hEdef
  obtain ⟨ψ', hψ'm, hψ'le, hae⟩ := GW2Sdo.exists_reindex_eventually_all (μ := μ) E (fun b k => hG _ _ k)
    (fun b => hmono _ _)
  set ψ : ℕ → ℕ → ℕ := fun a m => (Finset.range (m + 1)).sup fun n => ψ' (Nat.pair n a) m with hψdef
  have hle : ∀ a m n, n ≤ m → ψ' (Nat.pair n a) m ≤ ψ a m := fun a m n hn =>
    Finset.le_sup (f := fun n => ψ' (Nat.pair n a) m) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
  refine ⟨ψ, fun a m m' hmm' => ?_, fun a m => (hψ'le (Nat.pair 0 a) m).trans (hle a m 0 (Nat.zero_le m)), ?_⟩
  · refine Finset.sup_le fun n hn => ?_
    exact (hψ'm (Nat.pair n a) hmm').trans
      (hle a m' n ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)).trans hmm'))
  · filter_upwards [hae] with ω hω n
    filter_upwards [hω, eventually_ge_atTop n] with m hm hnm a ha
    have h1 := hm (Nat.pair n a) (by simpa [hEdef, Nat.unpair_pair] using ha)
    simp only [hEdef, Nat.unpair_pair] at h1
    exact hmono n a (hle a m n hnm) h1

/-- **The kernel bound for a selected candidate.** If almost surely, for every `n`, eventually in `m`, every candidate
is good at index `m` (the bad sets `B n a m` measurable), then for `P`-a.e. `ω₀`, under the conditional law at `ω₀`, the
bad set of any selection `a n m` has measure `≤ ε` eventually in `m`. -/
theorem ae_eventually_kernel_le {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (B : ℕ → ℕ → ℕ → Set Ω)
    (hB : ∀ n a m, MeasurableSet (B n a m)) (hgood : ∀ᵐ ξ ∂P, ∀ n, ∀ᶠ m in atTop, ∀ a, ξ ∉ B n a m) :
    ∀ᵐ ω₀ ∂P, ∀ (sel : ℕ → ℕ → ℕ) (n : ℕ) {ε : ℝ≥0∞}, 0 < ε →
      ∀ᶠ m in atTop, condExpKernel P 𝒢 ω₀ (B n (sel n m) m) ≤ ε := by
  filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hgood] with ω₀ hω₀ sel n ε hε
  set U : ℕ → Set Ω := fun m => ⋃ a, B n a m with hUdef
  have hUm : ∀ m, MeasurableSet (U m) := fun m => MeasurableSet.iUnion fun a => hB n a m
  have hev : ∀ᵐ ξ ∂(condExpKernel P 𝒢 ω₀), ∀ᶠ m in atTop, ξ ∉ U m := by
    filter_upwards [hω₀] with ξ hξ
    filter_upwards [hξ n] with m hm
    simp only [hUdef, mem_iUnion, not_exists]
    exact hm
  filter_upwards [eventually_measure_le hUm hev hε] with m hm
  exact (measure_mono (subset_iUnion (fun a => B n a m) (sel n m))).trans hm

end InteractingSLE.Theorem14.GW2Bh
