/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBMeasLocal
import InteractingSLE.Spec.Supplement.GB6CoordBClock

/-!
# Gluing measurable local relative drivers

A countable family of compatible local choices glues measurably on the union
of its live intervals. This uses Mathlib's measurable piecewise extension;
there is no arbitrary uncountable measurable-choice step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A countable compatible family of measurable local drivers. The life can
be zero on the complement of a measurable geometric event. -/
structure DriverAtlas (d : ℕ → ℝ≥0 → Ω → ℝ) (l : ℕ → Ω → ℝ≥0∞) : Prop where
  measurable : ∀ n t, Measurable (d n t)
  life_measurable : ∀ n, Measurable (l n)
  continuous : ∀ n ω, ContinuousOn (d n · ω) {t | (t : ℝ≥0∞) < l n ω}
  zero : ∀ n ω, d n 0 ω = 0
  compatible : ∀ n k ω (t : ℝ≥0), (t : ℝ≥0∞) < l n ω → (t : ℝ≥0∞) < l k ω → d n t ω = d k t ω

/-- The lifetime of the union of the local driver charts. -/
def atlasLife (l : ℕ → Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := ⨆ n, l n ω

omit mΩ in
theorem lt_atlasLife_iff {l : ℕ → Ω → ℝ≥0∞} (t : ℝ≥0) (ω : Ω) :
    (t : ℝ≥0∞) < atlasLife l ω ↔ ∃ n, (t : ℝ≥0∞) < l n ω := by
  simp only [atlasLife, lt_iSup_iff]

/-- Compatible local measurable choices admit a measurable continuous gluing,
with zero start, on the full union of their lifetimes. -/
theorem exists_driver_of_atlas {d : ℕ → ℝ≥0 → Ω → ℝ} {l : ℕ → Ω → ℝ≥0∞}
    (h : DriverAtlas d l) : ∃ D : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (D t)) ∧
      (∀ n ω (t : ℝ≥0), (t : ℝ≥0∞) < l n ω → D t ω = d n t ω) ∧
      (∀ ω, ContinuousOn (D · ω) {t | (t : ℝ≥0∞) < atlasLife l ω}) ∧
      (∀ ω, D 0 ω = 0) ∧ Measurable (atlasLife l) ∧
      AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) (atlasLife l) D := by
  classical
  have hlocal : ∀ t : ℝ≥0, ∃ f : Ω → ℝ, Measurable f ∧
      (∀ n ω, (t : ℝ≥0∞) < l n ω → f ω = d n t ω) ∧
      (∀ ω, (∀ n, ¬ (t : ℝ≥0∞) < l n ω) → f ω = 0) := by
    intro t
    let E : ℕ → Set Ω := fun n => {ω | (t : ℝ≥0∞) < l n ω}
    have hE : ∀ n, MeasurableSet (E n) := fun n => measurableSet_lt measurable_const (h.life_measurable n)
    obtain ⟨f, hf, heq⟩ := exists_measurable_piecewise E hE (fun n => d n t) (fun n => h.measurable n t)
      (fun n k _ ω hω => h.compatible n k ω t hω.1 hω.2)
    refine ⟨(⋃ n, E n).indicator f, hf.indicator (MeasurableSet.iUnion hE), ?_, ?_⟩
    · intro n ω hω
      rw [indicator_of_mem (mem_iUnion.2 ⟨n, hω⟩)]
      exact heq n hω
    · intro ω hω
      exact indicator_of_notMem (fun hmem => by
        obtain ⟨n, hn⟩ := mem_iUnion.1 hmem
        exact hω n hn) _
  choose D hDm hDn hDoff using hlocal
  have hLm : Measurable (atlasLife l) := Measurable.iSup h.life_measurable
  refine ⟨D, hDm, (fun n ω t ht => hDn t n ω ht), ?_, ?_, hLm, ?_⟩
  · intro ω t ht
    obtain ⟨n, hn⟩ := (lt_atlasLife_iff t ω).1 ht
    have hopen : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < l n ω} :=
      isOpen_Iio.preimage ENNReal.continuous_coe
    have hc : ContinuousAt (d n · ω) t := (h.continuous n ω t hn).continuousAt (hopen.mem_nhds hn)
    have hnhood : ∀ᶠ u : ℝ≥0 in 𝓝 t, (u : ℝ≥0∞) < l n ω := hopen.mem_nhds hn
    exact (hc.congr_of_eventuallyEq (hnhood.mono fun u hu => hDn u n ω hu)).continuousWithinAt
  · intro ω
    by_cases ht : ∃ n, ((0 : ℝ≥0) : ℝ≥0∞) < l n ω
    · obtain ⟨n, hn⟩ := ht
      rw [hDn 0 n ω hn, h.zero n ω]
    · exact hDoff 0 ω (not_exists.1 ht)
  · intro t A hA
    exact (measurableSet_lt measurable_const hLm).inter (hDm t hA)

/-- The event-restricted canonical curves provide the atlas regularity facts;
only agreement on overlaps remains to be checked geometrically. -/
theorem driverAtlas_of_curves {Γ : ℕ → Ω → ℝ → ℂ} {E : ℕ → Set Ω}
    (hE : ∀ n, MeasurableSet (E n))
    (hΓ : ∀ n ω, ω ∈ E n → Sec7.PocketTraversal.IsDrivenCurve (Γ n ω))
    (hm : ∀ n u, 0 ≤ u → Measurable ((E n).indicator fun ω => Γ n ω u))
    (hcompat : ∀ n k ω (t : ℝ≥0), ω ∈ E n → ω ∈ E k →
      (t : ℝ≥0∞) < Sec7.Lemma71C.capLife (Γ n ω) →
      (t : ℝ≥0∞) < Sec7.Lemma71C.capLife (Γ k ω) →
      drivenDriver (Γ n) t ω = drivenDriver (Γ k) t ω) :
    DriverAtlas (fun n t => (E n).indicator (drivenDriver (Γ n) t))
      (fun n => (E n).indicator fun ω => Sec7.Lemma71C.capLife (Γ n ω)) := by
  refine ⟨fun n => measurable_indicator_drivenDriver (hE n) (hΓ n) (hm n),
    fun n => measurable_indicator_capLife (hE n) (hΓ n) (hm n), ?_, ?_, ?_⟩
  · intro n ω
    by_cases hω : ω ∈ E n
    · have he : (fun t => (E n).indicator (drivenDriver (Γ n) t) ω) =
          (fun t => drivenDriver (Γ n) t ω) := funext fun t => indicator_of_mem hω _
      rw [he, indicator_of_mem hω]
      exact continuousOn_drivenDriver (fun _ : Unit => hΓ n ω hω) ()
    · simp only [indicator_of_notMem hω, not_lt_zero, ofPred_false]
      exact continuousOn_empty _
  · intro n ω
    by_cases hω : ω ∈ E n
    · rw [indicator_of_mem hω]
      exact drivenDriver_zero (fun _ : Unit => hΓ n ω hω) ()
    · exact indicator_of_notMem hω _
  · intro n k ω t hn hk
    have hnE : ω ∈ E n := by
      by_contra hnot
      rw [indicator_of_notMem hnot] at hn
      exact not_lt_zero hn
    have hkE : ω ∈ E k := by
      by_contra hnot
      rw [indicator_of_notMem hnot] at hk
      exact not_lt_zero hk
    rw [indicator_of_mem hnE] at hn ⊢
    rw [indicator_of_mem hkE] at hk ⊢
    exact hcompat n k ω t hnE hkE hn hk

end InteractingSLE.Supp8.GB6.CoordB
