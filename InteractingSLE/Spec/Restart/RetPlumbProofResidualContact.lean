/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualStop

/-!
# Past contact measurability, including the real line

Packet PROVE-RETPLUMB. New contacts on `(a,b]` are a countable union of
contacts on compact windows `[q,b]`. Contacts with each retained prefix use
the landed two-path measurability theorem; contacts with the real line use
its closed-set version.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open Supp7

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Contacts with the union of two compact prefixes and the real line, on a
closed time window, are measurable. -/
theorem measurableSet_contact_window {F : Set Ω} (hF : MeasurableSet F)
    {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t)
    (hf₁ : ∀ t, Measurable fun ω => f₁ ω t)
    (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (q b u r : ℝ≥0) (hqb : q ≤ b)
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b))
    (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∃ s ≤ b - q,
      η ω (q + s) ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine}) := by
  have hc : ∀ ω ∈ F, ContinuousOn (fun s => η ω (q + s)) (Iic (b - q)) := by
    intro ω hω
    refine (hcη ω hω).comp (continuous_const.add continuous_id).continuousOn fun s hs => ?_
    change q + s ≤ b
    calc q + s ≤ q + (b - q) := add_le_add le_rfl hs
      _ = b := add_tsub_cancel_of_le hqb
  have h₁ := measurableSet_inter_exists_eq hF (fun s => hη (q + s)) hf₁
    measurable_const measurable_const hc hc₁
  have h₂ := measurableSet_inter_exists_eq hF (fun s => hη (q + s)) hf₂
    measurable_const measurable_const hc hc₂
  have hR := measurableSet_inter_exists_mem hF (fun s => hη (q + s))
    measurable_const hc isClosed_realLine (show realLine.Nonempty from ⟨0, rfl⟩)
  convert (h₁.union h₂).union hR using 1
  ext ω
  constructor
  · rintro ⟨hω, s, hs, (⟨t, ht, he⟩ | ⟨t, ht, he⟩) | hreal⟩
    · exact Or.inl (Or.inl ⟨hω, s, hs, t, ht.2, he.symm⟩)
    · exact Or.inl (Or.inr ⟨hω, s, hs, t, ht.2, he.symm⟩)
    · exact Or.inr ⟨hω, s, hs, hreal⟩
  · rintro ((⟨hω, s, hs, t, ht, he⟩ | ⟨hω, s, hs, t, ht, he⟩) | ⟨hω, s, hs, hreal⟩)
    · exact ⟨hω, s, hs, Or.inl (Or.inl ⟨t, ⟨zero_le, ht⟩, he.symm⟩)⟩
    · exact ⟨hω, s, hs, Or.inl (Or.inr ⟨t, ⟨zero_le, ht⟩, he.symm⟩)⟩
    · exact ⟨hω, s, hs, Or.inr hreal⟩

/-- New contacts through the current endpoint are measurable from measurable
continuous prefixes. The retained contact set includes the entire real line. -/
theorem measurableSet_contact_Ioc {F : Set Ω} (hF : MeasurableSet F)
    {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t)
    (hf₁ : ∀ t, Measurable fun ω => f₁ ω t)
    (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (a b u r : ℝ≥0)
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b))
    (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∃ s : ℝ≥0, a < s ∧ s ≤ b ∧
      η ω s ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine}) := by
  classical
  have heq : F ∩ {ω | ∃ s : ℝ≥0, a < s ∧ s ≤ b ∧
      η ω s ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine} =
      ⋃ q : ℚ, if a < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal ≤ b then
        F ∩ {ω | ∃ s ≤ b - (q : ℝ).toNNReal,
          η ω ((q : ℝ).toNNReal + s) ∈ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine}
      else ∅ := by
    ext ω
    constructor
    · rintro ⟨hω, s, has, hsb, hK⟩
      obtain ⟨q, haq, hqs⟩ := exists_rat_btwn (show (a : ℝ) < s from has)
      have hq0 : (0 : ℝ) ≤ q := a.2.trans haq.le
      have haq' : a < (q : ℝ).toNNReal := by
        change (a : ℝ) < ((q : ℝ).toNNReal : ℝ)
        rw [Real.coe_toNNReal _ hq0]
        exact haq
      have hqs' : (q : ℝ).toNNReal ≤ s := by
        change ((q : ℝ).toNNReal : ℝ) ≤ (s : ℝ)
        rw [Real.coe_toNNReal _ hq0]
        exact hqs.le
      apply mem_iUnion.2 ⟨q, ?_⟩
      rw [ite_eq_left ⟨haq', hqs'.trans hsb⟩]
      exact ⟨hω, s - (q : ℝ).toNNReal, tsub_le_tsub_right hsb _,
        by rwa [add_tsub_cancel_of_le hqs']⟩
    · intro hω
      obtain ⟨q, hq⟩ := mem_iUnion.1 hω
      split_ifs at hq with hvalid
      · obtain ⟨hω, s, hs, hK⟩ := hq
        refine ⟨hω, (q : ℝ).toNNReal + s,
          hvalid.1.trans_le le_self_add, ?_, hK⟩
        calc (q : ℝ).toNNReal + s ≤ (q : ℝ).toNNReal + (b - (q : ℝ).toNNReal) :=
            add_le_add le_rfl hs
          _ = b := add_tsub_cancel_of_le hvalid.2
      · exact hq.elim
  rw [heq]
  refine MeasurableSet.iUnion fun q => ?_
  split_ifs with hvalid
  · exact measurableSet_contact_window hF hη hf₁ hf₂ _ b u r hvalid.2 hcη hc₁ hc₂
  · exact MeasurableSet.empty

/-- Avoidance on the same interval is measurable, with no assumption that the
path avoids the initial contact at time `a`. -/
theorem measurableSet_noContact_Ioc {F : Set Ω} (hF : MeasurableSet F)
    {η f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t)
    (hf₁ : ∀ t, Measurable fun ω => f₁ ω t)
    (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (a b u r : ℝ≥0)
    (hcη : ∀ ω ∈ F, ContinuousOn (η ω) (Iic b))
    (hc₁ : ∀ ω ∈ F, ContinuousOn (f₁ ω) (Iic u))
    (hc₂ : ∀ ω ∈ F, ContinuousOn (f₂ ω) (Iic r)) :
    MeasurableSet (F ∩ {ω | ∀ s : ℝ≥0, a < s → s ≤ b →
      η ω s ∉ f₁ ω '' Icc 0 u ∪ f₂ ω '' Icc 0 r ∪ realLine}) := by
  convert hF.diff (measurableSet_contact_Ioc hF hη hf₁ hf₂ a b u r hcη hc₁ hc₂) using 1
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨hω, hn⟩
    exact ⟨hω, fun ⟨_, s, has, hsb, hK⟩ => hn s has hsb hK⟩
  · rintro ⟨hω, hn⟩
    exact ⟨hω, fun s has hsb hK => hn ⟨hω, s, has, hsb, hK⟩⟩

end InteractingSLE.Restart.RetAux79
