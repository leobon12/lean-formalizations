/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MzFacts

/-!
# A stopped index from events known to the marks up to null sets

Packet PROVE-SB2-LCMEAN, round 15 (item 4, gluing over the offset). The offset events `{relOff = o}` are pairwise
disjoint and each is, up to null sets, an event of the marks at stage `o + d`. Disjointifying representatives gives an
index `N` with `N = o + d + 1` almost surely on the `o`-th event, whose fibres are events of the shifted family
`stopFam 𝓜` (`stopFam 𝓜 0 = mΩ` for the remainder, `stopFam 𝓜 (n + 1) = 𝓜 n`), ready for `Mx.stopSigma`:

* `stopFam`;
* **`exists_stopIdx`**.

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Function

namespace InteractingSLE.Theorem14.SB.Mz

/-- The marks shifted by one, with all events at index `0` (the remainder). -/
@[instance_reducible]
def stopFam {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓜 : ℕ → MeasurableSpace Ω) : ℕ → MeasurableSpace Ω
  | 0 => mΩ
  | n + 1 => 𝓜 n

theorem stopFam_le {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓜 : ℕ → MeasurableSpace Ω} (h𝓜 : ∀ n, 𝓜 n ≤ mΩ) :
    ∀ n, stopFam 𝓜 n ≤ mΩ
  | 0 => le_rfl
  | n + 1 => h𝓜 n

/-- **A stopped index from pairwise disjoint events known to monotone marks up to null sets.** -/
theorem exists_stopIdx {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {𝓜 : ℕ → MeasurableSpace Ω}
    (h𝓜 : ∀ n, 𝓜 n ≤ mΩ) (hmono : Monotone 𝓜) {S : ℕ → Set Ω} (hdisj : Pairwise (Disjoint on S)) (d : ℕ)
    (hS : ∀ o, ∃ A, MeasurableSet[𝓜 (o + d)] A ∧ A =ᵐ[μ] S o) :
    ∃ N : Ω → ℕ, (∀ n, MeasurableSet[stopFam 𝓜 n] {ω | N ω = n}) ∧
      ∀ᵐ ω ∂μ, ∀ o, ω ∈ S o → N ω = o + d + 1 := by
  classical
  choose A hAm hAe using hS
  set A' : ℕ → Set Ω := fun o => A o \ ⋃ o' ∈ Finset.range o, A o' with hA'
  have hA'm : ∀ o, MeasurableSet[𝓜 (o + d)] (A' o) := fun o =>
    (hAm o).diff (Finset.measurableSet_biUnion _ fun o' ho' =>
      hmono (by have := Finset.mem_range.1 ho'; omega) _ (hAm o'))
  have hA'mΩ : ∀ o, MeasurableSet (A' o) := fun o => h𝓜 _ _ (hA'm o)
  have hA'disj : ∀ (o o' : ℕ) (ω : Ω), ω ∈ A' o → ω ∈ A' o' → o = o' := by
    intro o o' ω h h'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h'.2 (mem_iUnion₂.2 ⟨o, Finset.mem_range.2 hlt, h.1⟩)
    · exact h.2 (mem_iUnion₂.2 ⟨o', Finset.mem_range.2 hlt, h'.1⟩)
  set N : Ω → ℕ := fun ω => if h : ∃ o, ω ∈ A' o then Nat.find h + d + 1 else 0 with hN
  have hNo : ∀ ω o, ω ∈ A' o → N ω = o + d + 1 := by
    intro ω o hω
    have hex : ∃ o, ω ∈ A' o := ⟨o, hω⟩
    simp only [hN, hex, ↓reduceDIte]
    congr 2
    exact hA'disj _ _ ω (Nat.find_spec hex) hω
  refine ⟨N, fun n => ?_, ?_⟩
  · rcases n with _ | n
    · have e : {ω | N ω = 0} = (⋃ o, A' o)ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion, not_exists]
        constructor
        · intro h0 o hω
          rw [hNo ω o hω] at h0
          omega
        · intro h
          have hex : ¬ ∃ o, ω ∈ A' o := fun ⟨o, ho⟩ => h o ho
          simp only [hN, hex, ↓reduceDIte]
      rw [e]
      exact (MeasurableSet.iUnion hA'mΩ).compl
    · by_cases hn : d ≤ n
      · have e : {ω | N ω = n + 1} = A' (n - d) := by
          ext ω
          simp only [mem_ofPred_eq]
          constructor
          · intro h
            by_cases hex : ∃ o, ω ∈ A' o
            · obtain ⟨o, ho⟩ := hex
              rw [hNo ω o ho] at h
              have : o = n - d := by omega
              rw [← this]
              exact ho
            · simp only [hN, hex, ↓reduceDIte] at h
              omega
          · intro h
            rw [hNo ω _ h]
            omega
        rw [e]
        show MeasurableSet[𝓜 n] (A' (n - d))
        have := hA'm (n - d)
        rwa [Nat.sub_add_cancel hn] at this
      · have e : {ω | N ω = n + 1} = ∅ := by
          ext ω
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro h
          by_cases hex : ∃ o, ω ∈ A' o
          · obtain ⟨o, ho⟩ := hex
            rw [hNo ω o ho] at h
            omega
          · simp only [hN, hex, ↓reduceDIte] at h
            omega
        rw [e]
        exact @MeasurableSet.empty Ω (stopFam 𝓜 (n + 1))
  · -- almost surely the `o`-th event lies in the `o`-th representative and in no earlier one
    have h1 : ∀ᵐ ω ∂μ, ∀ o, (ω ∈ A o ↔ ω ∈ S o) := by
      refine ae_all_iff.2 fun o => ?_
      filter_upwards [hAe o] with ω hω
      exact Iff.of_eq hω
    filter_upwards [h1] with ω hω o hSo
    refine hNo ω o ⟨(hω o).2 hSo, fun h => ?_⟩
    obtain ⟨o', ho', hA⟩ := mem_iUnion₂.1 h
    have hlt := Finset.mem_range.1 ho'
    exact Set.disjoint_left.1 (hdisj (ne_of_lt hlt)) ((hω o').1 hA) hSo

end InteractingSLE.Theorem14.SB.Mz
