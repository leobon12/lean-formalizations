import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Real
import Mathlib.Order.Interval.Set.Basic

/-!
# [S] §6: first exits, last entries and visits of curves

Packet S6a. Generic facts for curves `Q : ℝ → X` continuous on a compact interval in a topological space:

* `exists_first_exit`: a curve starting in an open set `A` that leaves it has a first exit time, at which it
  is on `frontier A`, and before which it stays in `A`;
* `exists_last_entry`: the time-reversed statement (last time outside `A` before ending in `A`);
* `exists_last_visit`: the last visit to `closure V` before a time at which the curve is outside
  `closure V`; from that time on the curve avoids the open set `V` (it cannot sit in `V` at the visit,
  otherwise it would stay in `V` a little longer);
* `exists_first_visit`: the time-reversed statement.

All helpers live in the namespace `HigherDimLQGMetric.S6a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

namespace S6a

open Set Filter Topology

variable {X : Type*} [TopologicalSpace X]

/-- **First exit.** A curve on `[a, b]` starting in the open set `A` and leaving it at time `t` has a first
exit time `τ ∈ [a, t]`: `Q τ ∈ frontier A` and `Q s ∈ A` for `s ∈ [a, τ)`. -/
theorem exists_first_exit {A : Set X} (hA : IsOpen A) {Q : ℝ → X} {a b : ℝ}
    (hQ : ContinuousOn Q (Icc a b)) (ha : Q a ∈ A) {t : ℝ} (ht : t ∈ Icc a b) (htA : Q t ∉ A) :
    ∃ τ ∈ Icc a t, Q τ ∈ frontier A ∧ ∀ s ∈ Ico a τ, Q s ∈ A := by
  set S : Set ℝ := Icc a t ∩ Q ⁻¹' Aᶜ with hSdef
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hSc : IsClosed S :=
    (hQ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hA.isClosed_compl
  have hSne : S.Nonempty := ⟨t, ⟨⟨ht.1, le_rfl⟩, htA⟩⟩
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  have hτS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hbefore : ∀ s ∈ Ico a (sInf S), Q s ∈ A := by
    intro s hs
    by_contra hns
    have hle : sInf S ≤ s := csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hτS.1.2⟩, hns⟩
    exact absurd hs.2 (not_lt.2 hle)
  refine ⟨sInf S, hτS.1, ?_, hbefore⟩
  rw [hA.frontier_eq]
  refine ⟨?_, hτS.2⟩
  have haτ : a < sInf S := by
    rcases hτS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      exact hτS.2 (h ▸ ha)
  have hcont : ContinuousWithinAt Q (Ico a (sInf S)) (sInf S) :=
    (hQ (sInf S) (hsub hτS.1)).mono (fun s hs => hsub ⟨hs.1, hs.2.le.trans hτS.1.2⟩)
  have hmem : sInf S ∈ closure (Ico a (sInf S)) := by
    rw [closure_Ico haτ.ne]
    exact ⟨haτ.le, le_rfl⟩
  have himg : Q '' Ico a (sInf S) ⊆ A := by
    rintro _ ⟨s, hs, rfl⟩
    exact hbefore s hs
  exact closure_mono himg (hcont.mem_closure_image hmem)

/-- **Last entry.** A curve on `[a, b]` ending in the open set `A` and outside it at time `t` has a last
time `τ ∈ [t, b]` outside `A`: `Q τ ∈ frontier A` and `Q s ∈ A` for `s ∈ (τ, b]`. -/
theorem exists_last_entry {A : Set X} (hA : IsOpen A) {Q : ℝ → X} {a b : ℝ}
    (hQ : ContinuousOn Q (Icc a b)) (hb : Q b ∈ A) {t : ℝ} (ht : t ∈ Icc a b) (htA : Q t ∉ A) :
    ∃ τ ∈ Icc t b, Q τ ∈ frontier A ∧ ∀ s ∈ Ioc τ b, Q s ∈ A := by
  set S : Set ℝ := Icc t b ∩ Q ⁻¹' Aᶜ with hSdef
  have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
  have hSc : IsClosed S :=
    (hQ.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc hA.isClosed_compl
  have hSne : S.Nonempty := ⟨t, ⟨⟨le_rfl, ht.2⟩, htA⟩⟩
  have hSbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  have hτS : sSup S ∈ S := hSc.csSup_mem hSne hSbdd
  have hafter : ∀ s ∈ Ioc (sSup S) b, Q s ∈ A := by
    intro s hs
    by_contra hns
    have hle : s ≤ sSup S := le_csSup hSbdd ⟨⟨hτS.1.1.trans hs.1.le, hs.2⟩, hns⟩
    exact absurd hs.1 (not_lt.2 hle)
  refine ⟨sSup S, hτS.1, ?_, hafter⟩
  rw [hA.frontier_eq]
  refine ⟨?_, hτS.2⟩
  have hτb : sSup S < b := by
    rcases hτS.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      exact hτS.2 (h ▸ hb)
  have hcont : ContinuousWithinAt Q (Ioc (sSup S) b) (sSup S) :=
    (hQ (sSup S) (hsub hτS.1)).mono (fun s hs => hsub ⟨hτS.1.1.trans hs.1.le, hs.2⟩)
  have hmem : sSup S ∈ closure (Ioc (sSup S) b) := by
    rw [closure_Ioc hτb.ne]
    exact ⟨le_rfl, hτb.le⟩
  have himg : Q '' Ioc (sSup S) b ⊆ A := by
    rintro _ ⟨s, hs, rfl⟩
    exact hafter s hs
  exact closure_mono himg (hcont.mem_closure_image hmem)

/-- **Last visit.** For a curve on `[a, t]` from `closure V` to a point outside `closure V` (`V` open), the
last visit `s` to `closure V` satisfies `Q τ ∉ V` for all `τ ∈ [s, t]`. -/
theorem exists_last_visit {V : Set X} (hV : IsOpen V) {Q : ℝ → X} {a t : ℝ}
    (hQ : ContinuousOn Q (Icc a t)) (hat : a ≤ t) (ha : Q a ∈ closure V) (ht : Q t ∉ closure V) :
    ∃ s ∈ Icc a t, Q s ∈ closure V ∧ ∀ τ ∈ Icc s t, Q τ ∉ V := by
  set S : Set ℝ := Icc a t ∩ Q ⁻¹' closure V with hSdef
  have hSc : IsClosed S := hQ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hSne : S.Nonempty := ⟨a, ⟨⟨le_rfl, hat⟩, ha⟩⟩
  have hSbdd : BddAbove S := ⟨t, fun x hx => hx.1.2⟩
  have hsS : sSup S ∈ S := hSc.csSup_mem hSne hSbdd
  have hst : sSup S < t := by
    rcases hsS.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      exact ht (h ▸ hsS.2)
  refine ⟨sSup S, hsS.1, hsS.2, ?_⟩
  intro τ hτ hτV
  rcases hτ.1.lt_or_eq with hsτ | hsτ
  · have hτS : τ ∈ S := ⟨⟨hsS.1.1.trans hτ.1, hτ.2⟩, subset_closure hτV⟩
    exact absurd (le_csSup hSbdd hτS) (not_le.2 hsτ)
  · -- `Q (sSup S) ∈ V`: points just after `sSup S` are in `V`, contradicting maximality
    rw [← hsτ] at hτV
    have hnhds : Q ⁻¹' V ∈ 𝓝[Icc a t] (sSup S) := hQ _ hsS.1 (hV.mem_nhds hτV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hnhds
    set τ' := min (sSup S + ε / 2) t with hτ'def
    have hsτ' : sSup S < τ' := lt_min (by linarith) hst
    have hτ't : τ' ≤ t := min_le_right _ _
    have hτ'mem : τ' ∈ Metric.ball (sSup S) ε ∩ Icc a t := by
      refine ⟨?_, ⟨hsS.1.1.trans hsτ'.le, hτ't⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      have := min_le_left (sSup S + ε / 2) t
      linarith
    have hτ'S : τ' ∈ S := ⟨⟨hsS.1.1.trans hsτ'.le, hτ't⟩, subset_closure (hball hτ'mem)⟩
    exact absurd (le_csSup hSbdd hτ'S) (not_le.2 hsτ')

/-- **First visit.** For a curve on `[t, b]` from a point outside `closure V` to `closure V` (`V` open), the
first visit `s` to `closure V` satisfies `Q τ ∉ V` for all `τ ∈ [t, s]`. -/
theorem exists_first_visit {V : Set X} (hV : IsOpen V) {Q : ℝ → X} {t b : ℝ}
    (hQ : ContinuousOn Q (Icc t b)) (htb : t ≤ b) (hb : Q b ∈ closure V) (ht : Q t ∉ closure V) :
    ∃ s ∈ Icc t b, Q s ∈ closure V ∧ ∀ τ ∈ Icc t s, Q τ ∉ V := by
  set S : Set ℝ := Icc t b ∩ Q ⁻¹' closure V with hSdef
  have hSc : IsClosed S := hQ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closure
  have hSne : S.Nonempty := ⟨b, ⟨⟨htb, le_rfl⟩, hb⟩⟩
  have hSbdd : BddBelow S := ⟨t, fun x hx => hx.1.1⟩
  have hsS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hts : t < sInf S := by
    rcases hsS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      exact ht (h ▸ hsS.2)
  refine ⟨sInf S, hsS.1, hsS.2, ?_⟩
  intro τ hτ hτV
  rcases hτ.2.lt_or_eq with hτs | hτs
  · have hτS : τ ∈ S := ⟨⟨hτ.1, hτ.2.trans hsS.1.2⟩, subset_closure hτV⟩
    exact absurd (csInf_le hSbdd hτS) (not_le.2 hτs)
  · -- `Q (sInf S) ∈ V`: points just before `sInf S` are in `V`, contradicting minimality
    rw [hτs] at hτV
    have hnhds : Q ⁻¹' V ∈ 𝓝[Icc t b] (sInf S) := hQ _ hsS.1 (hV.mem_nhds hτV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hnhds
    set τ' := max (sInf S - ε / 2) t with hτ'def
    have hτ's : τ' < sInf S := max_lt (by linarith) hts
    have htτ' : t ≤ τ' := le_max_right _ _
    have hτ'mem : τ' ∈ Metric.ball (sInf S) ε ∩ Icc t b := by
      refine ⟨?_, ⟨htτ', hτ's.le.trans hsS.1.2⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
      have := le_max_left (sInf S - ε / 2) t
      linarith
    have hτ'S : τ' ∈ S := ⟨⟨htτ', hτ's.le.trans hsS.1.2⟩, subset_closure (hball hτ'mem)⟩
    exact absurd (csInf_le hSbdd hτ'S) (not_le.2 hτ's)

end S6a

end HigherDimLQGMetric
