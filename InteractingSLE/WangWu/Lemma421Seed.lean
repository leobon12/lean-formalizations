/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Lemma421SeedArc
import InteractingSLE.WangWu.Cor48ChamberWalls
import InteractingSLE.WangWu.J7CondSeed
import InteractingSLE.Spec.Sec6.CondMeanLocality
import InteractingSLE.Spec.Restart.R1Flow

/-!
# Wang–Wu Lemma 4.21 for two seed lines of one field (`Lemma421SeedStatement`, (J2))

Packet PROVE-WW-B24. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Lemma 4.21
(text dump L1749–1757): "Two seed lines of different heights share no nontrivial subarc almost surely. […] Approach
the point from the same side. The local-set union boundary lemma then forces the union conditional mean to converge
both to `−λ − u₁` and to `−λ − u₂`, or both to `λ − u₁` and `λ − u₂`. The limits differ."

This file proves PROVE-WW-B23's named input `ChamberCond.Lemma421SeedStatement` **without** Proposition 4.19 (the
order of the two lines), so that `Chamber4.Chamber4JointStatement` needs only Proposition 4.19 and the chamber clause:

* `flowField_zero_neg_flowField`, `measurable_of_flowField`: the field `h` is recovered from `h + c`;
* **`seedLine_facts`**: for a nonnegative `κ = 4` two-seed coupling with the field `h + c`, a version `γ` of its seed
  line (a.s. equal to it and a proper arc) whose range is hitting-measurable, determined by the common centred field
  `h − u₀`, local for it (with `∩ ℍ`), and whose local-set mean has the side values `−λ − (u₀ + c)` (left) and
  `λ − (u₀ + c)` (right) (PROVE-WW-B22's `exists_seedVersion`, `seedWall_facts`);
* **`lemma421SeedStatement`**: `Lemma421SeedStatement`, by `WangWu.ae_interior_contact_eq_empty_sides` (Lemma 4.21
  approached from both sides of one line: same-side values differ since `u₁ ≠ u₂`, and the crossed alternative would
  make the two jumps `−2λ` and `+2λ`); the two ranges are conditionally independent given the field since both are
  field-determined;
* **`chamber4JointStatement_of_prop419_clause`**, **`twoSeedGraphInput_four_of_prop419_clause`**:
  `Chamber4JointStatement` and `LP.TwoSeedGraphInput 4` from Proposition 4.19 and the chamber clause (J5) only.

R48: nothing here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param`
result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.WangWu.ChamberCond

open SeedField SeedThree LocalSets
open Sec7.Lemma71I (realPath)

/-- The shift by `−c` undoes the shift by `c`: `(h + c) − c = h`. -/
theorem flowField_zero_neg_flowField (c : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Exist.flowField 0 (-c) (Exist.flowField 0 c f) = f := by
  ext φ
  rw [Exist.flowField_apply, Sec5.GlueCond.pushTest_shiftChart_zero, Exist.flowField_apply,
    Sec5.GlueCond.pushTest_shiftChart_zero]
  ring

/-- A field is measurable when one of its shifts `h + c` is. -/
theorem measurable_of_flowField {Ω : Type*} [MeasurableSpace Ω] {h : Ω → DistOn upperHalfPlaneOpens} {c : ℝ}
    (hm : Measurable fun ω => Exist.flowField 0 c (h ω)) : Measurable h := by
  have e : h = fun ω => Exist.flowField 0 (-c) (Exist.flowField 0 c (h ω)) :=
    funext fun ω => (flowField_zero_neg_flowField c (h ω)).symm
  rw [e]
  exact (Exist.measurable_flowField 0 (-c)).comp hm

/-- **One seed line as a random proper arc for the common centred field.** For a field `h` and an optional hull
coupling of the nonnegative `κ = 4` two-seed word `(ρL − c/λ; ρR + c/λ)` with the field `h + c` (`u₀` the bounded
harmonic extension of the data of `(ρL; ρR)`, `h − u₀` a zero-boundary GFF), there is a version `γ` of the seed line
(almost surely equal to it and a proper arc) whose range is hitting-measurable, determined by `h − u₀` and (with
`∩ ℍ`) local for it, and a version of its local-set mean with the side values `−λ − (u₀ + c)` on the left and
`λ − (u₀ + c)` on the right (PROVE-WW-B22's `SeedThree.exists_seedVersion` and `SeedThree.seedWall_facts`). -/
theorem seedLine_facts {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {rL rR c : ℝ} (hL : 0 ≤ rL - c / wwLambda)
    (hR : 0 ≤ rR + c / wwLambda) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - c / wwLambda)
      (fun _ => rR + c / wwLambda) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 c (h ω))) :
    ∃ γ : Ω → ℝ → ℂ, (∀ᵐ ω ∂P, γ ω = seedLine ζ W ω ∧ IsProperArc (γ ω)) ∧
      Measurable[mΩ, hittingSigma] (fun ω => arcRange (γ ω)) ∧
      LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
        (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
      IsLocalSet (fun ω => arcRange (γ ω) ∩ H) (WholeField.centredField h u₀) P ∧
      ∃ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (fun ω => arcRange (γ ω)) (WholeField.centredField h u₀) P g ∧
        (∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (γ ω) fun z => -wwLambda - (u₀ z + c)) ∧
        ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (γ ω) fun z => wwLambda - (u₀ z + c) := by
  obtain ⟨η, hη, hae⟩ := exists_seedVersion hhm hL hR hC hu₀.1
  obtain ⟨hm, hdet, hloc, hside⟩ :=
    seedWall_facts hL hR hu₀ hh0 hη hC (hae.mono fun ω hω => ⟨hω.1, hω.2.1⟩)
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 (measurable_inter_H hm) hloc
  have hg' := isLocalSetMean_inter_H_iff.1 hg
  exact ⟨fun ω => realPath (η ω), hae.mono fun ω hω => ⟨hω.2.1, hω.2.2.isProperArc⟩, hm, hdet, hloc, g, hg',
    hside g hg'⟩

/-- **Wang–Wu Lemma 4.21 for two seed lines of one field** (PROVE-WW-B23's named input `Lemma421SeedStatement`,
proved without Proposition 4.19): for two optional hull couplings of the nonnegative `κ = 4` words of heights
`u₁ ≠ u₂` with the fields `h + u₁`, `h + u₂`, almost surely the second seed line spends no time interval on the
range of the first. Both lines are local sets of the one field `h − u₀`, field-determined (hence conditionally
independent given it), and their means have the side values `∓λ − (u₀ + uᵢ)`; Lemma 4.21 approached from both sides
of one line (`WangWu.ae_interior_contact_eq_empty_sides`) applies. -/
theorem lemma421SeedStatement : Lemma421SeedStatement.{u} := by
  intro rL rR u₁ u₂ hne hL₁ hR₁ hL₂ hR₂ Ω mΩ P _ h 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hC₁ hC₂
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData 4 (fun _ : Fin 1 => rL)
    (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR
  have hhm : Measurable h := measurable_of_flowField hC₁.2.1
  -- the common centred field `h − u₀ = (h + u₁) − (u₀ + u₁)` is a zero-boundary GFF
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P := by
    have hu' := Sec5.GlueCond.isBoundedHarmonicExtension_add_const hu₀ u₁
    have hdata : (fun x => forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
        LP.twoSeedXR x + u₁) = forceBoundaryData 4 (fun _ : Fin 1 => rL - u₁ / wwLambda)
          (fun _ : Fin 1 => rR + u₁ / wwLambda) LP.twoSeedXL LP.twoSeedXR :=
      funext fun x => forceBoundaryData_twoSeed_four_add rL rR u₁ x
    rw [hdata] at hu'
    have := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData ⟨hC₁.2.1, hC₁.2.2.1⟩ hu'
    rwa [centredField_flowField_eq h hu₀.1 u₁] at this
  obtain ⟨γ₁, hγ₁, hm₁, hdet₁, hloc₁, g₁, hg₁, hl₁, hr₁⟩ := seedLine_facts hhm hL₁ hR₁ hu₀ hh0 hC₁
  obtain ⟨γ₂, hγ₂, hm₂, hdet₂, hloc₂, g₂, hg₂, hl₂, hr₂⟩ := seedLine_facts hhm hL₂ hR₂ hu₀ hh0 hC₂
  -- two field-determined ranges are conditionally independent given the field
  have hci : LQGMetric.CondIndepEv (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance)
      (MeasurableSpace.comap (fun ω => arcRange (γ₁ ω)) hittingSigma)
      (MeasurableSpace.comap (fun ω => arcRange (γ₂ ω)) hittingSigma) P :=
    LocalSets.condIndepEv_of_ae_measurableSet hh0.1.comap_le hdet₁ hdet₂
  have hl : 0 < wwLambda := wwLambda_pos
  have key := ae_interior_contact_eq_empty_sides hh0 hm₁ hm₂ hci hloc₁ hloc₂
    (by filter_upwards [hγ₁, hγ₂] with ω h₁ h₂; exact ⟨h₁.2, h₂.2⟩) hg₁ hg₂ hl₁ hr₁ hl₂ hr₂
    (fun z _ he => hne (by linarith)) (fun z _ he => hne (by linarith)) (fun z _ e₁ e₂ => by linarith)
  filter_upwards [key, hγ₁, hγ₂] with ω hω h₁ h₂
  rw [← h₁.1, ← h₂.1]
  exact hω.1

/-- **The seed three-line space of Proposition 4.24 from Proposition 4.19 alone** (`seedThreeSpaceStatement_of_prop419`
with Lemma 4.21 discharged by `lemma421SeedStatement`). Conditional helper. -/
theorem seedThreeSpaceStatement_of_prop419' (h419 : Prop419Statement.{u}) : SeedThreeSpaceStatement.{u} :=
  seedThreeSpaceStatement_of_prop419 h419 lemma421SeedStatement

/-- **`Chamber4.Chamber4JointStatement` from Proposition 4.19 and the chamber clause (J5)**
(`chamber4JointStatement_of_prop419` with Lemma 4.21 discharged by `lemma421SeedStatement`). Conditional helper. -/
theorem chamber4JointStatement_of_prop419_clause (h419 : Prop419Statement.{u}) (hcl : ChamberClauseStatement.{u}) :
    Chamber4.Chamber4JointStatement.{u} :=
  chamber4JointStatement_of_prop419 h419 lemma421SeedStatement hcl

/-- **`LP.TwoSeedGraphInput 4` from Proposition 4.19 and the chamber clause (J5)**
(`twoSeedGraphInput_four_of_prop419` with Lemma 4.21 discharged by `lemma421SeedStatement`). Conditional helper. -/
theorem twoSeedGraphInput_four_of_prop419_clause (h419 : Prop419Statement.{u}) (hcl : ChamberClauseStatement.{u}) :
    LP.TwoSeedGraphInput.{u} 4 :=
  twoSeedGraphInput_four_of_prop419 h419 lemma421SeedStatement hcl

end InteractingSLE.WangWu.ChamberCond
