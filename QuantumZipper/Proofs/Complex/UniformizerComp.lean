/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node U2)
-/
import QuantumZipper.Proofs.Complex.UniformizerTopo
import QuantumZipper.Proofs.Complex.HoloLog
import QuantumZipper.Proofs.Complex.RMTStep3
import QuantumZipper.Proofs.Complex.BasicsCayley

/-!
# Complementary components of the left component are unbounded (EXT-CA node U2)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "U", node U2.

* `not_isBounded_connectedComponentIn_compl_leftComponent`: for a simple chord `η` and
  `a ∉ leftComponent η`, the component of `a` in `(leftComponent η)ᶜ` is unbounded.
* `hasHoloSqrt_leftComponent`: hence (node H4) `HasHoloSqrt (leftComponent η)`, the input of the
  Riemann mapping theorem M4.
* `exists_conformal_H_leftComponent` (node U3): a holomorphic bijection `ψ : ℍ → D` with
  holomorphic inverse `φ : D → ℍ` (M4 composed with the Cayley transform).

## Sources

Elementary plane topology, following the blueprint's sketch of U2: the set
`E₀ = {Im ≤ 0} ∪ η[0,∞)` is connected, unbounded and disjoint from `D`; a point `a ∈ ℍ \ η`
outside `D` lies in a component `C` of `ℍ \ η` different from `D`, and `closure C ∪ E₀` is
connected (the frontier of `C` lies in `E₀`), unbounded and disjoint from `D`.  **Own elementary
proof** (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace QuantumZipper.CA.Uniformizer

variable {η : ℝ → ℂ}

/-- The lower half-plane is unbounded. -/
theorem not_isBounded_lowerHalf : ¬ Bornology.IsBounded {z : ℂ | z.im ≤ 0} := by
  rintro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  have h := hC (-((|C| + 1 : ℝ) : ℂ) * Complex.I) (by simp <;> linarith [abs_nonneg C])
  have : ‖-((|C| + 1 : ℝ) : ℂ) * Complex.I‖ = |C| + 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  rw [this] at h
  linarith [le_abs_self C]

/-- `E₀ = {Im ≤ 0} ∪ η[0,∞)` is preconnected. -/
theorem isPreconnected_lower_union_chordSet (hη : IsSimpleChord η) :
    IsPreconnected ({z : ℂ | z.im ≤ 0} ∪ chordSet η) :=
  (convex_halfSpace_im_le (r := 0)).isPreconnected.union 0 (by simp) (zero_mem_chordSet hη)
    (isPreconnected_Ici.image η hη.2.1)

theorem lower_union_chordSet_subset_compl (η : ℝ → ℂ) :
    {z : ℂ | z.im ≤ 0} ∪ chordSet η ⊆ (leftComponent η)ᶜ := by
  rintro z (hz | hz) hzD
  · have := leftComponent_subset_H η hzD
    simp only [H, mem_ofPred_eq] at this hz
    linarith
  · exact (leftComponent_subset_slitH η hzD).2 hz

/-- A preconnected unbounded subset of `Dᶜ` through `a` makes the component of `a` unbounded. -/
theorem not_isBounded_of_subset {D S : Set ℂ} {a : ℂ} (hS : IsPreconnected S) (haS : a ∈ S)
    (hSD : S ⊆ Dᶜ) (hSu : ¬ Bornology.IsBounded S) :
    ¬ Bornology.IsBounded (connectedComponentIn Dᶜ a) :=
  fun hb => hSu (hb.subset (hS.subset_connectedComponentIn haS hSD))

/-- **U2.** Every component of the complement of `leftComponent η` is unbounded. -/
theorem not_isBounded_connectedComponentIn_compl_leftComponent (hη : IsSimpleChord η) {a : ℂ}
    (ha : a ∉ leftComponent η) :
    ¬ Bornology.IsBounded (connectedComponentIn (leftComponent η)ᶜ a) := by
  set E₀ : Set ℂ := {z : ℂ | z.im ≤ 0} ∪ chordSet η with hE₀
  have hE₀c := isPreconnected_lower_union_chordSet hη
  have hE₀D := lower_union_chordSet_subset_compl η
  have hE₀u : ¬ Bornology.IsBounded E₀ :=
    fun hb => not_isBounded_lowerHalf (hb.subset subset_union_left)
  by_cases haE : a ∈ E₀
  · exact not_isBounded_of_subset hE₀c haE hE₀D hE₀u
  -- `a ∈ ℍ \ η`, in a component `C` of `ℍ \ η` disjoint from `D`
  have haΩ : a ∈ slitH η := by
    refine ⟨?_, fun h => haE (Or.inr h)⟩
    by_contra h
    exact haE (Or.inl (show a.im ≤ 0 from not_lt.1 h))
  have hΩ := isOpen_slitH hη
  set C := connectedComponentIn (slitH η) a with hCdef
  have hDC : Disjoint (leftComponent η) C := by
    rw [Set.disjoint_left]
    intro y hyD hyC
    apply ha
    rw [leftComponent_eq hη] at hyD ⊢
    rw [connectedComponentIn_eq hyD, ← connectedComponentIn_eq hyC]
    exact mem_connectedComponentIn haΩ
  have hDcl : Disjoint (leftComponent η) (closure C) :=
    hDC.closure_right (isOpen_leftComponent hη)
  -- `C` is not closed, so its closure meets `E₀`
  have hCH : C ⊆ H := (connectedComponentIn_subset _ _).trans sdiff_subset
  have hnc : ¬ IsClosed C := by
    intro hcl
    rcases isClopen_iff.1 ⟨hcl, hΩ.connectedComponentIn⟩ with h | h
    · have := mem_connectedComponentIn haΩ
      rw [← hCdef, h] at this
      exact this
    · have := hCH (h.symm ▸ mem_univ (0 : ℂ))
      simp [H] at this
  obtain ⟨w, hwc, hwC⟩ := not_subset.1 fun h => hnc (isClosed_of_closure_subset h)
  have hwE : w ∈ E₀ := by
    have hw0 : 0 ≤ w.im := closure_subset_Hbar hCH hwc
    by_cases hK : w ∈ chordSet η
    · exact Or.inr hK
    rcases hw0.eq_or_lt with h | h
    · exact Or.inl (show w.im ≤ 0 from h.symm.le)
    · exact absurd (mem_cc_of_mem_closure hΩ hwc ⟨h, hK⟩) hwC
  have hS : IsPreconnected (closure C ∪ E₀) :=
    (isPreconnected_connectedComponentIn.closure).union w hwc hwE hE₀c
  refine not_isBounded_of_subset hS (Or.inl (subset_closure (mem_connectedComponentIn haΩ)))
    ?_ fun hb => hE₀u (hb.subset subset_union_right)
  rintro z (hz | hz)
  · exact fun hzD => Set.disjoint_left.1 hDcl hzD hz
  · exact hE₀D hz

/-- **U2 ⇒ H4 input.** The left component has holomorphic square roots, so the Riemann mapping
theorem `riemann_mapping_of_hasHoloSqrt` (M4) applies to it. -/
theorem hasHoloSqrt_leftComponent (hη : IsSimpleChord η) : RMT.HasHoloSqrt (leftComponent η) :=
  RMT.hasHoloSqrt_of_unbounded_compl (isOpen_leftComponent hη) (isPreconnected_leftComponent hη)
    fun _ ha => not_isBounded_connectedComponentIn_compl_leftComponent hη ha

theorem ne_one_of_mem_ball {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rintro rfl
  simp at hw

/-- **U3.** There is a holomorphic bijection `ψ : ℍ → leftComponent η` with holomorphic inverse
`φ` (the Riemann mapping theorem M4, applicable by U2 + H4, composed with the Cayley transform). -/
theorem exists_conformal_H_leftComponent (hη : IsSimpleChord η) :
    ∃ ψ : ℂ → ℂ, BijOn ψ H (leftComponent η) ∧ DifferentiableOn ℂ ψ H ∧
      ∃ φ : ℂ → ℂ, BijOn φ (leftComponent η) H ∧ DifferentiableOn ℂ φ (leftComponent η) ∧
        LeftInvOn φ ψ H ∧ LeftInvOn ψ φ (leftComponent η) := by
  obtain ⟨φ₀, hφb, hφd, ψ₀, hψb, hψd, hinv⟩ := RMT.riemann_mapping_of_hasHoloSqrt
    (isOpen_leftComponent hη) (isPreconnected_leftComponent hη) (leftComponent_nonempty hη)
    (leftComponent_ne_univ η) (hasHoloSqrt_leftComponent hη)
  have hrinv : ∀ w ∈ ball (0 : ℂ) 1, φ₀ (ψ₀ w) = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hφb.surjOn hw
    rw [hinv hz]
  have hcay : BijOn cayleyInv (ball (0 : ℂ) 1) H :=
    bijOn_cayley_H.symm ⟨fun w hw => cayley_cayleyInv (ne_one_of_mem_ball hw),
      fun z hz => cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hz))⟩
  refine ⟨ψ₀ ∘ cayley, hψb.comp bijOn_cayley_H,
    hψd.comp (differentiableOn_cayley_Hbar.mono H_subset_Hbar) bijOn_cayley_H.mapsTo,
    cayleyInv ∘ φ₀, hcay.comp hφb,
    (differentiableOn_cayleyInv_closedBall.mono fun w hw =>
      ⟨ball_subset_closedBall hw, ne_one_of_mem_ball hw⟩).comp hφd hφb.mapsTo, ?_, ?_⟩
  · intro z hz
    simp only [Function.comp_apply]
    rw [hrinv _ (bijOn_cayley_H.mapsTo hz),
      cayleyInv_cayley (add_I_ne_zero_of_im_nonneg (le_of_lt hz))]
  · intro z hz
    simp only [Function.comp_apply]
    rw [cayley_cayleyInv (ne_one_of_mem_ball (hφb.mapsTo hz)), hinv hz]

end QuantumZipper.CA.Uniformizer
