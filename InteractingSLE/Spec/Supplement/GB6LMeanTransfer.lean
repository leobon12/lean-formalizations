/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitVNest
import InteractingSLE.Spec.Coupling.WFSLeafJointMarksAE

/-!
# GB6's union mean, part 2: transferring local-set means between marked local sets

Packet PROVE-GB6-LINEMEAN, the "mean transfer" of `planning/handoffs/PROVE-GB6-LINELOCAL.md` §4 (2). Let `A₁ ⊆ A₂`
(almost surely) be two local sets of a zero-boundary GFF `h`, `A₁` history-marked local for marks `𝒦`, `A₂` for marks
`ℳ ⊇ 𝒦` that record `A₁`, and `E ∈ 𝒦` an event on which `A₁ = A₂`. Then almost surely on `E` their local-set means
agree on every test supported off `A₂` (**`ae_eqOn_mean_of_marked`**).

Proof (nested uniqueness, `Aux61SlitV.ae_forall_apply_eq_of_le`): the decomposition of `h` given `germ(A₁) ∨ 𝒦`
(Aux. 18 with history, `Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal`) has the mean of `A₁` (compare with
`germ(A₁)`); adding the germ of `A₁` to the marks of `A₂` (R69,
`WFS.isHistoryAvoidanceLocal_sup_germSigma_of_ae_subset`), the decomposition given `germ(A₂) ∨ ℳ ∨ germ(A₁)` has
the mean of `A₂`; the first σ-algebra is contained in the second and `E` belongs to the first, so the two means
agree on `E`. No determination and no conditional independence are used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open QuantumZipper (H)
open LQGMetric (TestOn DistOn IsZeroBoundaryGFF)

universe u

namespace InteractingSLE.Supp8.GB6LMean

open LocalSets WholeField

variable {Ω : Type u} {𝒦 ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Local-set means of nested marked local sets agree where the sets agree.** -/
theorem ae_eqOn_mean_of_marked {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A₁ A₂ : Ω → Set ℂ}
    (hA₁m : Measurable[mΩ, hittingSigma] A₁) (hA₂m : Measurable[mΩ, hittingSigma] A₂)
    (hA₁c : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (h𝒦ℳ : 𝒦 ≤ ℳ) (hℳ : ℳ ≤ mΩ)
    (hloc₁ : IsHistoryAvoidanceLocal 𝒦 A₁ h P) (hloc₂ : IsHistoryAvoidanceLocal ℳ A₂ h P)
    (hA₁ℳ : Measurable[ℳ, hittingSigma] A₁) (hsub : ∀ᵐ ω ∂P, A₁ ω ⊆ A₂ ω)
    {E : Set Ω} (hE : MeasurableSet[𝒦] E) (hEq : ∀ᵐ ω ∂P, ω ∈ E → A₁ ω = A₂ ω)
    {g₁ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₁ : IsLocalSetMean A₁ h P g₁)
    (hg₂ : IsLocalSetMean A₂ h P g₂) :
    ∀ᵐ ω ∂P, ω ∈ E → ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g₂ ω φ = g₁ ω φ := by
  have hhm := hh.measurable
  have h𝒦 : 𝒦 ≤ mΩ := h𝒦ℳ.trans hℳ
  have hg₁₁ : germSigma A₁ h ≤ mΩ := germSigma_le hA₁m hhm
  have hg₂₂ : germSigma A₂ h ≤ mΩ := germSigma_le hA₂m hhm
  -- the decomposition of `A₁` given its germ and its marks
  obtain ⟨m₁, hm₁m, hm₁h, hm₁c⟩ := Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hA₁m h𝒦 hloc₁ hA₁c
  -- the decomposition of `A₂` given its germ, its marks and the germ of `A₁`
  have hloc₂' : IsHistoryAvoidanceLocal (ℳ ⊔ germSigma A₁ h) A₂ h P :=
    WFS.isHistoryAvoidanceLocal_sup_germSigma_of_ae_subset hh hℳ hA₂m hloc₂ hA₁ℳ hsub
  obtain ⟨m₂, hm₂m, hm₂h, hm₂c⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh hA₂m (sup_le hℳ hg₁₁) hloc₂' hA₂c
  -- `m₁ = g₁`
  have hO₁ : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → IsOpen (H \ A₁ ω) ∧ H \ A₁ ω ⊆ H := by
    filter_upwards [hA₁c] with ω hω _ using ⟨hω.2, sdiff_subset⟩
  have e₁ := Sec5.Aux61SlitV.ae_forall_apply_eq_of_le (𝒢 := germSigma A₁ h) (𝒥 := germSigma A₁ h ⊔ 𝒦)
    le_sup_left (sup_le hg₁₁ h𝒦) hhm hg₁.1 (hm₁m.mono le_sup_left le_rfl) hg₁.2.2 hm₁c MeasurableSet.univ
    (Eventually.of_forall fun _ _ => rfl) hO₁ (by filter_upwards [hg₁.2.1] with ω hω _ using hω)
    (by filter_upwards [hm₁h] with ω hω _ using hω)
  -- `m₂ = g₂`
  have hO₂ : ∀ᵐ ω ∂P, ω ∈ (univ : Set Ω) → IsOpen (H \ A₂ ω) ∧ H \ A₂ ω ⊆ H := by
    filter_upwards [hA₂c] with ω hω _ using ⟨hω.2, sdiff_subset⟩
  have e₂ := Sec5.Aux61SlitV.ae_forall_apply_eq_of_le (𝒢 := germSigma A₂ h)
    (𝒥 := germSigma A₂ h ⊔ (ℳ ⊔ germSigma A₁ h)) le_sup_left (sup_le hg₂₂ (sup_le hℳ hg₁₁)) hhm hg₂.1
    (hm₂m.mono le_sup_left le_rfl) hg₂.2.2 hm₂c MeasurableSet.univ (Eventually.of_forall fun _ _ => rfl) hO₂
    (by filter_upwards [hg₂.2.1] with ω hω _ using hω) (by filter_upwards [hm₂h] with ω hω _ using hω)
  -- `m₂ = m₁` on `E` (nested: `germ(A₁) ∨ 𝒦 ≤ germ(A₂) ∨ ℳ ∨ germ(A₁)`)
  have hnest : germSigma A₁ h ⊔ 𝒦 ≤ germSigma A₂ h ⊔ (ℳ ⊔ germSigma A₁ h) :=
    sup_le (le_sup_right.trans le_sup_right) (h𝒦ℳ.trans (le_sup_left.trans le_sup_right))
  have e₃ := Sec5.Aux61SlitV.ae_forall_apply_eq_of_le (𝒢 := germSigma A₁ h ⊔ 𝒦)
    (𝒥 := germSigma A₂ h ⊔ (ℳ ⊔ germSigma A₁ h)) hnest (sup_le hg₂₂ (sup_le hℳ hg₁₁)) hhm
    (hm₁m.mono le_sup_left le_rfl) (hm₂m.mono le_sup_left le_rfl) hm₁c hm₂c
    (show MeasurableSet[germSigma A₁ h ⊔ 𝒦] E from le_sup_right (α := MeasurableSpace Ω) E hE)
    (by filter_upwards [hEq] with ω hω hωE; rw [hω hωE]) (O := fun ω => H \ A₂ ω)
    (by filter_upwards [hA₂c] with ω hω _ using ⟨hω.2, sdiff_subset⟩)
    (by filter_upwards [hm₁h, hEq] with ω hω hωE hE'; rw [← hωE hE']; exact hω)
    (by filter_upwards [hm₂h] with ω hω _ using hω)
  filter_upwards [e₁, e₂, e₃, hEq] with ω h1 h2 h3 hωE hE' φ hφ
  have hφ₁ : tsupport φ ⊆ H \ A₁ ω := by rw [hωE hE']; exact hφ
  rw [← h2 trivial φ hφ, h3 hE' φ hφ, h1 trivial φ hφ₁]

end InteractingSLE.Supp8.GB6LMean
