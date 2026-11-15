/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KqDrv
import InteractingSLE.Spec.Supplement.SB2MfUnb
import InteractingSLE.Spec.Sec5.GlueCondTopo
import InteractingSLE.Spec.Supplement.WalkSideGeom
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# SB2(1)'s late (S) line mean, part 7: FIN's unbounded-component inputs

Packet PROVE-T14-SB2DRV (round 10), the inputs `hunbA`, `hunbK` of FIN's union mean
(`FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK`) in the coupling's coordinates (shifted by the seed `u`):

* `lowerUnion_image_add`, `isBounded_image_add`, **`forall_not_isBounded_component_translate`** (generic): the
  unbounded-component property of `S ∪ {Im ≤ 0}` is invariant under real translations;
* **`ae_unb_walkFill_translate`** (`hunbA`): almost surely, every component of the lower union of the translated walk
  fill is unbounded (on the launch event from `Mf.not_isBounded_lowerUnion_fillH_closure` and
  `WalkSide.not_isBounded_lowerUnion_stageSet`; off it the walk fill is `ℍ`);
* **`unb_fwdHull`** (`hunbK`): the same for the Loewner hull of any continuous driver at any time `t ≥ 0`
  (`isHPHull_fwdHull`, `GlueCond.not_isBounded_lowerUnion_of_isHPHull`).

**R48.** Theorems 1.2–1.3 are not used; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open LocalSets Exist.StagedLaw

/-! ### Translation invariance -/

/-- The lower union of a translated set is the translated lower union. -/
theorem lowerUnion_image_add (S : Set ℂ) (c : ℝ) :
    lowerUnion ((fun z : ℂ => z + c) '' S) = (fun z : ℂ => z + c) '' lowerUnion S := by
  ext z
  simp only [lowerUnion, mem_union, mem_image, mem_ofPred_eq]
  constructor
  · rintro (⟨w, hw, rfl⟩ | hz)
    · exact ⟨w, Or.inl hw, rfl⟩
    · refine ⟨z - c, Or.inr ?_, by ring⟩
      simpa using hz
  · rintro ⟨w, (hw | hw), rfl⟩
    · exact Or.inl ⟨w, hw, rfl⟩
    · exact Or.inr (by simpa using hw)

theorem isBounded_image_add {S : Set ℂ} (hS : Bornology.IsBounded S) (c : ℂ) :
    Bornology.IsBounded ((fun z : ℂ => z + c) '' S) :=
  (IsometryEquiv.addRight c).isometry.lipschitzWith.isBounded_image hS

/-- **The unbounded-component property of the lower union is invariant under real translations.** -/
theorem forall_not_isBounded_component_translate {S : Set ℂ}
    (h : ∀ z ∈ lowerUnion S, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion S) z)) (c : ℝ) :
    ∀ z ∈ lowerUnion ((fun z : ℂ => z + c) '' S),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion ((fun z : ℂ => z + c) '' S)) z) := by
  intro z hz hb
  rw [lowerUnion_image_add] at hz hb
  obtain ⟨w, hw, rfl⟩ := hz
  have e : (fun z : ℂ => z + c) '' connectedComponentIn (lowerUnion S) w =
      connectedComponentIn ((fun z : ℂ => z + c) '' lowerUnion S) (w + c) :=
    (Homeomorph.addRight (c : ℂ)).image_connectedComponentIn hw
  rw [← e] at hb
  have hb' := isBounded_image_add hb (-(c : ℂ))
  rw [image_image] at hb'
  simp only [add_neg_cancel_right, image_id'] at hb'
  exact h w hw hb'

theorem not_isBounded_component_univ (z : ℂ) :
    ¬ Bornology.IsBounded (connectedComponentIn (univ : Set ℂ) z) := by
  rw [isPreconnected_univ.connectedComponentIn (mem_univ z)]
  exact NormedSpace.unbounded_univ ℝ ℂ

/-- **`hunbK`**: the lower union of the Loewner hull of a continuous driver has unbounded components. -/
theorem unb_fwdHull {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    ∀ z ∈ lowerUnion (fwdHull w t), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull w t)) z) :=
  Sec5.GlueCond.not_isBounded_lowerUnion_of_isHPHull (isHPHull_fwdHull hw ht)

/-! ### The translated walk fill -/

section Walk

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **`hunbA`**: almost surely, the lower union of the translated walk fill has unbounded components. -/
theorem ae_unb_walkFill_translate (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {A' : Ω → Set ℂ}
    (hA'ae : ∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) (c : ℝ) :
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion ((fun z : ℂ => z + c) '' walkFill κ b jumps E k A' ω),
      ¬ Bornology.IsBounded
        (connectedComponentIn (lowerUnion ((fun z : ℂ => z + c) '' walkFill κ b jumps E k A' ω)) z) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hR := HP.pieces_regular _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  filter_upwards [hA'ae, EntranceUnion.ae_isBounded_stageSet HP, hR.ae_pieceRegular] with ω hA hbA hpr
  refine forall_not_isBounded_component_translate ?_ c
  by_cases hl : ω ∈ launchSet κ b jumps E (k + 1)
  · have hb : Bornology.IsBounded (A' ω) := by rw [hA]; exact hbA hl
    rw [walkFill, ite_eq_left hl, cptClosure, ite_eq_left hb, hA]
    refine Mf.not_isBounded_lowerUnion_fillH_closure
      (WalkLaw.stageSet_subset_H κ b jumps _ _ (k + 1) ω) (hbA hl) ?_
    exact WalkSide.not_isBounded_lowerUnion_stageSet _ _ ω (fun j c' θ' hlj => hpr j c' θ' hlj) (k + 1)
  · rw [walkFill, ite_eq_right hl]
    have e : lowerUnion H = univ := by
      ext z
      simp only [lowerUnion, mem_union, mem_univ, iff_true]
      by_cases hz : 0 < z.im
      · exact Or.inl hz
      · exact Or.inr (not_lt.1 hz)
    intro z _
    rw [e]
    exact not_isBounded_component_univ z

end Walk

end InteractingSLE.Theorem14.SB.Lv
