/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkSplit
import InteractingSLE.Spec.Supplement.SBLuDense

/-!
# Lemma S3 reflected for SB2(2): no common open arc of the lower pieces with the upper history

Packet PROVE-T14-SB2LIFT (round 4). The geometric half of SB2(2) (`Lk.SB2LowerRelWalkStatement`, route P1–P4 of the
handoff) needs that the lifted pieces of the lower walk are driven curves and that their "good" times (physical point
in `D_A`, where the frozen chart is applied) are dense. Both fail exactly when an ordinary piece of the lower walk runs
along the retained upper history on a time interval. The source excludes this (supplement p. 631: "On every ordinary
piece the strict angle comparison excludes a common open arc with the other history, by the two exposed-height
identities in S3"); it is Lemma S3 with the roles of the two histories exchanged (`SB.S3Statement`, itself an unproved
named input, is the upper-flow form). This file states it:

* **`SB2LowerNoCommonArcStatement`** (named input): in SB2(2)'s setting, at almost every launch of the upper schedule,
  almost surely under the retained kernel, no ordinary piece of the lower walk maps a nonempty open time interval
  into the retained upper history (the piece's physical points are the boundary values of its launch chart along its
  chosen trace, `LuM.newPiece`'s description);
* **`interior_setOf_notMem_domain_eq_empty`** (deterministic): on an open time interval of a piece's tail, the times at
  which the physical point is outside `D_A = ℍ ∖ fill A` have empty interior, if the piece shares no open arc with `A`,
  its chart trace spends no time interval on `ℝ`, the chart maps `ℍ` into `ℍ`, and the tail's points of `ℍ` off `A` lie
  in `D_A` (Lemma S2's hull clause, `s2HullRight`). This gives the density of the good times of
  `measurable_of_dense_good` and the absence of real time-intervals of the lifted piece;
* `interior_setOf_lift_real_eq_empty`: a lift `γ` of the piece through the boundary map of a domain chart of `D_A` is
  real only at times when the piece is outside `D_A` (a real point maps outside `D_A`, `SB.g_ofReal_notMem`), so its
  real times have empty interior too — the hypothesis of SB2FIN's `FinRel.isDrivenCurve_relCurve_of_lt` on the stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Lu LuM Exist.Staged Exist.StagedLaw

/-- **Named input: Lemma S3 reflected for SB2(2)** (supplement p. 631). At almost every launch `k` of the upper
schedule and for every witness, almost surely under the retained kernel: for every launched piece `j` of the lower
walk and every nonempty open time interval `(s₁, s₂)` within its lifetime, the piece's physical points on it are not
all on the retained upper history `A = upperPrefix … k ω₀`. -/
def SB2LowerNoCommonArcStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ j : ℕ, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j ≠ none →
        ∀ s₁ s₂ : ℝ≥0, s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2 →
          ¬ (fun t => bdVal (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) j))
              (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) t)) '' Ioo s₁ s₂ ⊆
            upperPrefix κ b jumps E u l k ω₀

/-- **The times of a piece's tail outside the retained domain have empty interior** (deterministic). On an open time
set `I` where the physical piece `p` (continuous) is read from its chart trace `α` (`α t ∈ ℍ ⇒ p t ∈ ℍ`, `α` in `ℍ̄`):
if `p` shares no open arc with the closed set `A`, the real times of `α` have empty interior, and every point of `ℍ`
off `A` on `p(I)` lies in `ℍ ∖ fill A`, then the times at which `p` is outside `ℍ ∖ fill A` have empty interior. -/
theorem interior_setOf_notMem_domain_eq_empty {p α : ℝ≥0 → ℂ} {A : Set ℂ} (hA : IsClosed A) {I : Set ℝ≥0}
    (hI : IsOpen I) (hpc : ContinuousOn p I) (hαH : ∀ t ∈ I, 0 ≤ (α t).im)
    (hpα : ∀ t ∈ I, α t ∈ QuantumZipper.H → p t ∈ QuantumZipper.H)
    (htail : ∀ t ∈ I, p t ∈ QuantumZipper.H → p t ∉ A → p t ∈ QuantumZipper.H \ fillH A)
    (hR : interior {t | t ∈ I ∧ (α t).im = 0} = ∅)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, s₁ < s₂ → Ioo s₁ s₂ ⊆ I → ¬ p '' Ioo s₁ s₂ ⊆ A) :
    interior {t | t ∈ I ∧ p t ∉ QuantumZipper.H \ fillH A} = ∅ := by
  set X : Set ℝ≥0 := {t | t ∈ I ∧ p t ∈ A} with hX
  set Y : Set ℝ≥0 := {t | t ∈ I ∧ (α t).im = 0} with hY
  have hsub : {t | t ∈ I ∧ p t ∉ QuantumZipper.H \ fillH A} ⊆ X ∪ Y := by
    rintro t ⟨htI, hnot⟩
    by_cases hpH : p t ∈ QuantumZipper.H
    · by_cases hpA : p t ∈ A
      · exact Or.inl ⟨htI, hpA⟩
      · exact absurd (htail t htI hpH hpA) hnot
    · refine Or.inr ⟨htI, ?_⟩
      have hαn : α t ∉ QuantumZipper.H := fun h => hpH (hpα t htI h)
      have h1 : ¬ (0 < (α t).im) := hαn
      exact le_antisymm (not_lt.1 h1) (hαH t htI)
  -- the times in `I` off `A` form an open set
  have hopen : IsOpen (I ∩ p ⁻¹' Aᶜ) := hpc.isOpen_inter_preimage hI hA.isOpen_compl
  refine subset_empty_iff.1 fun t ht => ?_
  have hU := isOpen_interior (s := {t | t ∈ I ∧ p t ∉ QuantumZipper.H \ fillH A})
  set U := interior {t | t ∈ I ∧ p t ∉ QuantumZipper.H \ fillH A} with hUdef
  have hUsub : U ⊆ X ∪ Y := interior_subset.trans hsub
  have hUI : U ⊆ I := fun s hs => (interior_subset hs).1
  by_cases hoff : (U ∩ (I ∩ p ⁻¹' Aᶜ)).Nonempty
  · -- an open set of times off `A` inside `U` consists of real times of `α`
    have hV : IsOpen (U ∩ (I ∩ p ⁻¹' Aᶜ)) := hU.inter hopen
    have hVY : U ∩ (I ∩ p ⁻¹' Aᶜ) ⊆ Y := fun s hs => by
      rcases hUsub hs.1 with hx | hy
      · exact absurd hx.2 hs.2.2
      · exact hy
    have hVint : U ∩ (I ∩ p ⁻¹' Aᶜ) ⊆ interior Y := interior_maximal hVY hV
    rw [hR] at hVint
    obtain ⟨s, hs⟩ := hoff
    exact (hVint hs).elim
  · -- `U` lies in `A`'s times, so an open interval of times is mapped into `A`
    have hUX : U ⊆ X := fun s hs => by
      refine ⟨hUI hs, ?_⟩
      by_contra hn
      exact hoff ⟨s, hs, hUI hs, hn⟩
    obtain ⟨a, b, hab, hsubU⟩ := hU.exists_Ioo_subset ⟨t, ht⟩
    exact (hS3 a b hab (hsubU.trans hUI) fun z ⟨s, hs, hz⟩ => hz ▸ (hUX (hsubU hs)).2).elim

/-- **A lift of the piece is real only where the piece leaves the retained domain**, so its real times have empty
interior when those of the piece outside `D_A` do. -/
theorem interior_setOf_lift_real_eq_empty {A : Set ℂ} {c : Chart}
    (hD : IsDomainChart (QuantumZipper.H \ fillH A) c) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 QuantumZipper.H) {γ p : ℝ≥0 → ℂ} {I : Set ℝ≥0} (hγ : ∀ t ∈ I, g (γ t) = p t)
    (hI0 : interior {t | t ∈ I ∧ p t ∉ QuantumZipper.H \ fillH A} = ∅) :
    interior {t | t ∈ I ∧ (γ t).im = 0} = ∅ := by
  refine subset_empty_iff.1 (hI0 ▸ interior_mono fun t ht => ⟨ht.1, fun hpD => ?_⟩)
  have he : γ t = ((γ t).re : ℂ) := Complex.ext (by simp) (by simp [ht.2])
  have h1 := SB.g_ofReal_notMem hD hgc hgi (γ t).re
  rw [← he, hγ t ht.1] at h1
  exact h1 hpD

end InteractingSLE.Theorem14.SB.Lk
