/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionContacts
import Mathlib.Basic.ENNReal.Operations

/-!
# Selected contact times and their lower-rectangle events (§7.2: (GR1), (GR2), (RU2))

Packet PROVE-SEC7-B. For the stopped curves `α₁|[0, T₁]`, `α₂|[0, T₂]` and a starting time `σ` of the
second curve, the later-contact relation is (supplement §3.2, p. 458; Theorem 7.9B, p. 308)
`C_σ = {(s, t) : s ≤ T₁, σ ≤ t ≤ T₂, s, t < ∞, α₁(s) = α₂(t)}` (`laterContactSet`), the selected
first-contact times are the infima `τᵢ` of its coordinate projections (`∞` when `C_σ = ∅`;
`contactInf₁`, `contactInf₂`), and `ζᵢ = τᵢ ∧ Tᵢ`. The marked-locality arguments of Lemma 7.7,
Theorem 7.9B and Aux. lemma 77 rest on three exact identities of events, proved here pointwise:

* **(GR2)** (p. 308) under common attained selection: `{ζ₁ ≤ s, ζ₂ ≤ t} = {T₁ ≤ s, T₂ ≤ t} ∪
  ({σ ≤ t} ∩ {α₁([0, s ∧ T₁]) ∩ α₂([σ, t ∧ T₂]) ≠ ∅})` (`selected_le_iff`);
* **(GR1)** (p. 283), its case `σ = 0` (`selected_le_iff_of_firstContact`);
* **(RU2)** (Aux. lemma 77, p. 288): `{(ζ₁ + s) ∧ T₁ ≤ u, ζ₂ ≤ v} = ({T₁ ≤ u} ∩ E(u, v)) ∪ E(u − s, v)`
  with `E(u, v) = {ζ₁ ≤ u, ζ₂ ≤ v}` and `E = ∅` at a negative coordinate (`advanced_le_iff`).

Common attained selection itself (the two infima attained at one contact) is the geometric content of
Lemma 7.7 and Theorem W8; deterministically it follows from increasing contact order
(`InteractingSLE.Sec7.exists_isFirstContact_of_contact_order`).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

variable {X : Type*}

/-- The later-contact relation `C_σ` (supplement §3.2, p. 458): finite parameters `s ≤ T₁` and
`σ ≤ t ≤ T₂` with `α₁(s) = α₂(t)`. For `σ = ∞` it is empty. -/
def laterContactSet (α₁ : ℝ≥0 → X) (T₁ : ℝ≥0∞) (α₂ : ℝ≥0 → X) (σ T₂ : ℝ≥0∞) :
    Set (ℝ≥0 × ℝ≥0) :=
  {p | (p.1 : ℝ≥0∞) ≤ T₁ ∧ σ ≤ p.2 ∧ (p.2 : ℝ≥0∞) ≤ T₂ ∧ α₁ p.1 = α₂ p.2}

/-- The infimum `τ₁` of the first coordinate projection of a contact relation (`∞` if empty). -/
def contactInf₁ (C : Set (ℝ≥0 × ℝ≥0)) : ℝ≥0∞ :=
  ⨅ p ∈ C, (p.1 : ℝ≥0∞)

/-- The infimum `τ₂` of the second coordinate projection of a contact relation (`∞` if empty). -/
def contactInf₂ (C : Set (ℝ≥0 × ℝ≥0)) : ℝ≥0∞ :=
  ⨅ p ∈ C, (p.2 : ℝ≥0∞)

theorem contactInf₁_le {C : Set (ℝ≥0 × ℝ≥0)} {p : ℝ≥0 × ℝ≥0} (hp : p ∈ C) :
    contactInf₁ C ≤ p.1 :=
  iInf₂_le p hp

theorem contactInf₂_le {C : Set (ℝ≥0 × ℝ≥0)} {p : ℝ≥0 × ℝ≥0} (hp : p ∈ C) :
    contactInf₂ C ≤ p.2 :=
  iInf₂_le p hp

theorem contactInf₁_empty : contactInf₁ ∅ = ⊤ := by
  simp only [contactInf₁, mem_empty_iff_false, not_false_eq_true, iInf_neg, iInf_top]

theorem contactInf₂_empty : contactInf₂ ∅ = ⊤ := by
  simp only [contactInf₂, mem_empty_iff_false, not_false_eq_true, iInf_neg, iInf_top]

/-- At a coordinatewise least contact `p`, the two selected infima are `p.1` and `p.2`. -/
theorem contactInf_eq_of_isLeast {C : Set (ℝ≥0 × ℝ≥0)} {p : ℝ≥0 × ℝ≥0} (hp : p ∈ C)
    (hle : ∀ q ∈ C, p.1 ≤ q.1 ∧ p.2 ≤ q.2) : contactInf₁ C = p.1 ∧ contactInf₂ C = p.2 :=
  ⟨le_antisymm (contactInf₁_le hp) (le_iInf₂ fun q hq => ENNReal.coe_le_coe.mpr (hle q hq).1),
    le_antisymm (contactInf₂_le hp) (le_iInf₂ fun q hq => ENNReal.coe_le_coe.mpr (hle q hq).2)⟩

/-- **(GR2)** (Theorem 7.9B, proof, p. 308; supplement §3.2, p. 459). Assume common attained
selection: whenever `C_σ` is nonempty, it has a coordinatewise least element (both first-contact
infima are attained at one contact). Then for deterministic `s, t`, with `ζᵢ = τᵢ ∧ Tᵢ`,
`{ζ₁ ≤ s, ζ₂ ≤ t} = {T₁ ≤ s, T₂ ≤ t} ∪ ({σ ≤ t} ∩ {α₁([0, s ∧ T₁]) ∩ α₂([σ, t ∧ T₂]) ≠ ∅})`. -/
theorem selected_le_iff {α₁ α₂ : ℝ≥0 → X} {T₁ T₂ σ : ℝ≥0∞}
    (hcommon : (laterContactSet α₁ T₁ α₂ σ T₂).Nonempty →
      ∃ p ∈ laterContactSet α₁ T₁ α₂ σ T₂,
        ∀ q ∈ laterContactSet α₁ T₁ α₂ σ T₂, p.1 ≤ q.1 ∧ p.2 ≤ q.2)
    (s t : ℝ≥0) :
    (contactInf₁ (laterContactSet α₁ T₁ α₂ σ T₂) ⊓ T₁ ≤ s ∧
        contactInf₂ (laterContactSet α₁ T₁ α₂ σ T₂) ⊓ T₂ ≤ t) ↔
      (T₁ ≤ s ∧ T₂ ≤ t) ∨
        (σ ≤ t ∧ (α₁ '' {u : ℝ≥0 | u ≤ s ∧ (u : ℝ≥0∞) ≤ T₁} ∩
          α₂ '' {v : ℝ≥0 | σ ≤ v ∧ v ≤ t ∧ (v : ℝ≥0∞) ≤ T₂}).Nonempty) := by
  set C := laterContactSet α₁ T₁ α₂ σ T₂ with hC
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · left
      rw [hCe, contactInf₁_empty, top_inf_eq] at h₁
      rw [hCe, contactInf₂_empty, top_inf_eq] at h₂
      exact ⟨h₁, h₂⟩
    · right
      obtain ⟨p, hp, hle⟩ := hcommon hCne
      obtain ⟨e₁, e₂⟩ := contactInf_eq_of_isLeast hp hle
      rw [e₁, inf_eq_left.mpr hp.1] at h₁
      rw [e₂, inf_eq_left.mpr hp.2.2.1] at h₂
      refine ⟨hp.2.1.trans h₂, α₁ p.1, ⟨p.1, ⟨ENNReal.coe_le_coe.mp h₁, hp.1⟩, rfl⟩,
        ⟨p.2, ⟨hp.2.1, ENNReal.coe_le_coe.mp h₂, hp.2.2.1⟩, hp.2.2.2.symm⟩⟩
  · rintro (⟨h₁, h₂⟩ | ⟨-, _, ⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩)
    · exact ⟨inf_le_right.trans h₁, inf_le_right.trans h₂⟩
    · have hmem : (u, v) ∈ C := ⟨hu.2, hv.1, hv.2.2, hvu.symm⟩
      exact ⟨inf_le_left.trans ((contactInf₁_le hmem).trans (ENNReal.coe_le_coe.mpr hu.1)),
        inf_le_left.trans ((contactInf₂_le hmem).trans (ENNReal.coe_le_coe.mpr hv.2.1))⟩

/-- **(GR1)** (Lemma 7.7, proof, p. 283): the case `σ = 0` of (GR2). Under the common-first-point
hypothesis, `{θ*₁ ≤ s, θ*₂ ≤ t} = {T₁ ≤ s, T₂ ≤ t} ∪ {α₁([0, s ∧ T₁]) ∩ α₂([0, t ∧ T₂]) ≠ ∅}`. -/
theorem selected_le_iff_of_firstContact {α₁ α₂ : ℝ≥0 → X} {T₁ T₂ : ℝ≥0∞}
    (hcommon : (laterContactSet α₁ T₁ α₂ 0 T₂).Nonempty →
      ∃ p ∈ laterContactSet α₁ T₁ α₂ 0 T₂,
        ∀ q ∈ laterContactSet α₁ T₁ α₂ 0 T₂, p.1 ≤ q.1 ∧ p.2 ≤ q.2)
    (s t : ℝ≥0) :
    (contactInf₁ (laterContactSet α₁ T₁ α₂ 0 T₂) ⊓ T₁ ≤ s ∧
        contactInf₂ (laterContactSet α₁ T₁ α₂ 0 T₂) ⊓ T₂ ≤ t) ↔
      (T₁ ≤ s ∧ T₂ ≤ t) ∨
        (α₁ '' {u : ℝ≥0 | u ≤ s ∧ (u : ℝ≥0∞) ≤ T₁} ∩
          α₂ '' {v : ℝ≥0 | v ≤ t ∧ (v : ℝ≥0∞) ≤ T₂}).Nonempty := by
  rw [selected_le_iff hcommon s t]
  have hset : {v : ℝ≥0 | (0 : ℝ≥0∞) ≤ v ∧ v ≤ t ∧ (v : ℝ≥0∞) ≤ T₂} =
      {v : ℝ≥0 | v ≤ t ∧ (v : ℝ≥0∞) ≤ T₂} := by
    ext v
    exact ⟨fun h => h.2, fun h => ⟨zero_le, h⟩⟩
  rw [hset]
  exact or_congr_right ⟨fun h => h.2, fun h => ⟨zero_le, h⟩⟩

/-- **(RU2)** (Aux. lemma 77, p. 288). With `E(u, v) = {ζ₁ ≤ u, ζ₂ ≤ v}` (empty at a negative
coordinate) and `ζ₁ ≤ T₁`: `{(ζ₁ + s) ∧ T₁ ≤ u, ζ₂ ≤ v} = ({T₁ ≤ u} ∩ E(u, v)) ∪ E(u − s, v)`,
including the case in which the first path terminates before its increment is completed. -/
theorem advanced_le_iff {ζ₁ ζ₂ T₁ : ℝ≥0∞} (hζ : ζ₁ ≤ T₁) (s u v : ℝ≥0) :
    ((ζ₁ + s) ⊓ T₁ ≤ u ∧ ζ₂ ≤ v) ↔
      (T₁ ≤ u ∧ ζ₁ ≤ u ∧ ζ₂ ≤ v) ∨ (s ≤ u ∧ ζ₁ ≤ ((u - s : ℝ≥0) : ℝ≥0∞) ∧ ζ₂ ≤ v) := by
  constructor
  · rintro ⟨h, hv⟩
    rcases inf_le_iff.mp h with h | h
    · have hsu : s ≤ u := ENNReal.coe_le_coe.mp (le_add_self.trans h)
      right
      refine ⟨hsu, ?_, hv⟩
      rw [ENNReal.coe_sub, ENNReal.le_sub_iff_add_le_right ENNReal.coe_ne_top
        (ENNReal.coe_le_coe.mpr hsu)]
      exact h
    · exact Or.inl ⟨h, hζ.trans h, hv⟩
  · rintro (⟨h, -, hv⟩ | ⟨hsu, h, hv⟩)
    · exact ⟨inf_le_right.trans h, hv⟩
    · refine ⟨inf_le_left.trans ?_, hv⟩
      rw [ENNReal.coe_sub, ENNReal.le_sub_iff_add_le_right ENNReal.coe_ne_top
        (ENNReal.coe_le_coe.mpr hsu)] at h
      exact h

end Sec7

end InteractingSLE
