/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkRelMeas

/-!
# Measurability from dense good rational times, at one time

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). `Lk.measurable_of_dense_good` needs the
curves continuous on all of `ℝ≥0` and the good times dense everywhere. The relative curve of SB2(1) is continuous
and read at dense good times only before the remaining lifetime, so its reading is needed time by time:

* **`measurable_of_dense_good_at`**: if `ρ ω` is continuous **at** `t` for `ω` in a measurable event `M`, its values
  at the good indices are given by measurable `V i`, and the good times accumulate at `t` on `M`, then
  `ω ↦ ρ ω t` is measurable on `M`. The σ-algebra is arbitrary (e.g. a completed line σ-algebra).

The proof is that of `Lk.measurable_of_dense_good`, with continuity and density used at `t` only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace InteractingSLE.Theorem14.SB.Vc

open Lk

open scoped Classical in
/-- **Measurability from good rational times accumulating at `t`** (continuity at `t` only). -/
theorem measurable_of_dense_good_at {Ω : Type*} [MeasurableSpace Ω] {ρ : Ω → ℝ≥0 → ℂ} {V : ℕ → Ω → ℂ}
    {good : ℕ → Ω → Prop} (hgood : ∀ i, MeasurableSet {ω | good i ω}) (hV : ∀ i, Measurable (V i))
    {M : Set Ω} (hM : MeasurableSet M) {t : ℝ≥0} (hcont : ∀ ω ∈ M, ContinuousAt (ρ ω) t)
    (hval : ∀ ω ∈ M, ∀ i, good i ω → ρ ω (ratPt i) = V i ω)
    (hdense : ∀ ω ∈ M, ∀ ε : ℝ, 0 < ε → ∃ i, good i ω ∧ dist (ratPt i) t < ε) :
    Measurable fun ω => if ω ∈ M then ρ ω t else 0 := by
  classical
  set win : ℕ → ℕ → Ω → Prop := fun n i ω => good i ω ∧ dist (ratPt i) t < 1 / ((n : ℝ) + 1) with hwin
  have hwinm : ∀ n i, MeasurableSet {ω | win n i ω} := fun n i => by
    by_cases hd : dist (ratPt i) t < 1 / ((n : ℝ) + 1)
    · have e : {ω | win n i ω} = {ω | good i ω} := by
        ext ω; exact ⟨fun h => h.1, fun h => ⟨h, hd⟩⟩
      rw [e]; exact hgood i
    · have e : {ω | win n i ω} = ∅ := by
        ext ω; exact ⟨fun h => hd h.2, fun h => h.elim⟩
      rw [e]; exact MeasurableSet.empty
  set M' : Set Ω := {ω | ∀ n, ∃ i, win n i ω} with hM'
  have hM'm : MeasurableSet M' := by
    have : M' = ⋂ n, ⋃ i, {ω | win n i ω} := by ext ω; simp [hM']
    rw [this]; exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => hwinm n i
  have hMM' : M ⊆ M' := fun ω hω n => hdense ω hω _ (by positivity)
  set q : ℕ → Ω → ℕ → Prop := fun n ω i => ω ∉ M' ∨ win n i ω with hq
  have hqex : ∀ n ω, ∃ i, q n ω i := fun n ω => by
    by_cases hω : ω ∈ M'
    · obtain ⟨i, hi⟩ := hω n; exact ⟨i, Or.inr hi⟩
    · exact ⟨0, Or.inl hω⟩
  have hqm : ∀ n i, MeasurableSet {ω | q n ω i} := fun n i => hM'm.compl.union (hwinm n i)
  set idx : ℕ → Ω → ℕ := fun n ω => Nat.find (hqex n ω) with hidx
  have hidxm : ∀ n, Measurable (idx n) := fun n => measurable_find (hqex n) (hqm n)
  set F : ℕ → Ω → ℂ := fun n ω => V (idx n ω) ω with hF
  have hFm : ∀ n, Measurable (F n) := fun n => by
    intro s hs
    have e : F n ⁻¹' s = ⋃ i, idx n ⁻¹' {i} ∩ V i ⁻¹' s := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, hF]
      exact ⟨fun h => ⟨idx n ω, rfl, h⟩, fun ⟨i, hi, h⟩ => hi ▸ h⟩
    rw [e]
    exact MeasurableSet.iUnion fun i => (hidxm n (measurableSet_singleton i)).inter (hV i hs)
  have hlim : ∀ ω ∈ M, Tendsto (fun n => F n ω) atTop (𝓝 (ρ ω t)) := by
    intro ω hω
    have hspec : ∀ n, win n (idx n ω) ω := fun n => by
      rcases Nat.find_spec (hqex n ω) with h | h
      · exact absurd (hMM' hω) h
      · exact h
    have hconv : Tendsto (fun n => ratPt (idx n ω)) atTop (𝓝 t) := by
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => (hspec n).2.le) ?_)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (hcont ω hω).tendsto.comp hconv
    refine h1.congr fun n => ?_
    exact hval ω hω _ (hspec n).1
  set Gl : Ω → ℂ := fun ω => limUnder atTop fun n => F n ω with hGl
  have hGlm : Measurable Gl :=
    (StronglyMeasurable.limUnder fun n => (hFm n).stronglyMeasurable).measurable
  have e : (fun ω => if ω ∈ M then ρ ω t else 0) = fun ω => if ω ∈ M then Gl ω else 0 := by
    funext ω
    by_cases hω : ω ∈ M
    · simp only [hω, ↓reduceIte, hGl]
      exact ((hlim ω hω).limUnder_eq).symm
    · simp only [hω, ↓reduceIte]
  rw [e]
  exact Measurable.ite hM hGlm measurable_const

end InteractingSLE.Theorem14.SB.Vc
