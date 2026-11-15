/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J7CondMain
import InteractingSLE.WangWu.Prop419

/-!
# Wang–Wu at `κ = 4`: the seed three-line space from Proposition 4.19 and Lemma 4.21

Packet PROVE-WW-B23. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.24
(text dump L1816–1867): "Set `u₁ = −λ(ρR + 2) < 0`, `u₂ = λ(ρL + 2) > 0`. Choose `a, b` sufficiently large that the
seed lines at heights `u₁, 0, u₂` are all non-boundary-intersecting. By Propositions 4.18 and 4.19, these are simple,
continuous, transient, determined by the field, and ordered. […] The absence of common arcs guarantees a nonempty
chamber." Lemma 4.21 (L1749–1757): "Two seed lines of different heights share no nontrivial subarc almost surely."

This file reduces the (J1) input `SeedThreeSpaceStatement` of `J7CondMain` to Proposition 4.19
(`SeedField.Prop419Statement`, PROVE-WW-B20; being proved by PROVE-WW-B21) and Lemma 4.21 for two seed lines of one
field (**`Lemma421SeedStatement`**, named here; "share no nontrivial subarc" is stated as "the second line spends no
time interval on the range of the first", the hypothesis of WW-B22's `SeedThree.isSeedThreeSpace_of_seed`):

* **`seedThreeSpaceStatement_of_prop419`**: one field with the base weights `(ρL + 2; ρR + 2)` and its three seed lines
  at heights `u₂, u₁, 0` (`SeedField.exists_seedLineSpace`), ordered by Proposition 4.19
  (`SeedField.ae_isOrderedArcs_of_prop419`), with no common arc by Lemma 4.21, form a seed three-line space
  (`SeedThree.isSeedThreeSpace_of_seed`);
* **`chamber4JointStatement_of_prop419`**, **`twoSeedGraphInput_four_of_prop419`**: `Chamber4JointStatement` and
  `LP.TwoSeedGraphInput 4` from Proposition 4.19, Lemma 4.21 and the chamber clause (J5).

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal Real

open LQGMetric (DistOn)

universe u

namespace InteractingSLE.WangWu.ChamberCond

open SeedField SeedThree

/-- **Named input: Wang–Wu Lemma 4.21 for two seed lines of one field** ("Two seed lines of different heights share no
nontrivial subarc almost surely", L1749–1757). For two optional hull couplings of the nonnegative `κ = 4` words of
heights `u₁ ≠ u₂` with the fields `h + u₁`, `h + u₂` of one field `h`, almost surely the second seed line spends no
time interval on the range of the first. (Both seed lines are almost surely simple proper arcs,
`SeedField.ae_isProperArc_seedLine`, so this is the absence of a common nontrivial subarc.) -/
def Lemma421SeedStatement : Prop :=
  ∀ (rL rR u₁ u₂ : ℝ), u₁ ≠ u₂ → 0 ≤ rL - u₁ / wwLambda → 0 ≤ rR + u₁ / wwLambda → 0 ≤ rL - u₂ / wwLambda →
    0 ≤ rR + u₂ / wwLambda →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens)
      (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ)
      (ζ₁ : Ω → ℝ≥0∞)
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ)
      (ζ₂ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₁ / wwLambda)
        (fun _ => rR + u₁ / wwLambda) P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ (fun ω => Exist.flowField 0 u₁ (h ω)) →
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₂ / wwLambda)
        (fun _ => rR + u₂ / wwLambda) P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ (fun ω => Exist.flowField 0 u₂ (h ω)) →
      ∀ᵐ ω ∂P, interior {t ∈ Ici (0 : ℝ) | seedLine ζ₂ W₂ ω t ∈ arcRange (seedLine ζ₁ W₁ ω)} = ∅

/-- **The seed three-line space of Proposition 4.24 from Proposition 4.19 and Lemma 4.21** (see the module docstring).
Conditional helper. -/
theorem seedThreeSpaceStatement_of_prop419 (h419 : Prop419Statement.{u}) (h421 : Lemma421SeedStatement.{u}) :
    SeedThreeSpaceStatement.{u} := by
  intro ρL ρR hL hR
  have hl : 0 < wwLambda := wwLambda_pos
  have hl0 : wwLambda ≠ 0 := hl.ne'
  set rL : ℝ := ρL + 2 with hrL
  set rR : ℝ := ρR + 2 with hrR
  set u₁ : ℝ := -(wwLambda * (ρR + 2)) with hu₁def
  set u₂ : ℝ := wwLambda * (ρL + 2) with hu₂def
  have e₁ : u₁ / wwLambda = -rR := by rw [hu₁def, neg_div, mul_div_cancel_left₀ _ hl0]
  have e₂ : u₂ / wwLambda = rL := by rw [hu₂def, mul_div_cancel_left₀ _ hl0]
  have hrL0 : 0 < rL := by rw [hrL]; linarith
  have hrR0 : 0 < rR := by rw [hrR]; linarith
  have hu₁ : u₁ < 0 := by rw [hu₁def]; nlinarith
  have hu₂ : 0 < u₂ := by rw [hu₂def]; nlinarith
  -- the nonnegativity of the three words `u₂ (left wall), u₁ (right wall), 0 (middle)`
  have hLβ : 0 ≤ rL - u₂ / wwLambda := by rw [e₂, sub_self]
  have hRβ : 0 ≤ rR + u₂ / wwLambda := by rw [e₂]; linarith
  have hLα : 0 ≤ rL - u₁ / wwLambda := by rw [e₁]; linarith
  have hRα : 0 ≤ rR + u₁ / wwLambda := by rw [e₁, add_neg_cancel]
  have hLγ : 0 ≤ rL - 0 / wwLambda := by rw [zero_div, sub_zero]; exact hrL0.le
  have hRγ : 0 ≤ rR + 0 / wwLambda := by rw [zero_div, add_zero]; exact hrR0.le
  -- one field and its three seed lines
  obtain ⟨Ω, mΩ, P, hP, h, hh, hC⟩ := exists_seedLineSpace.{u} (rL := rL) (rR := rR) ![u₂, u₁, 0]
    (fun i => by fin_cases i <;> assumption) (fun i => by fin_cases i <;> assumption)
  obtain ⟨𝓕β, Wβ, VLβ, VRβ, Bβ, ζβ, hCβ⟩ := hC 0
  obtain ⟨𝓕α, Wα, VLα, VRα, Bα, ζα, hCα⟩ := hC 1
  obtain ⟨𝓕γ, Wγ, VLγ, VRγ, Bγ, ζγ, hCγ⟩ := hC 2
  have hCβ' : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₂ / wwLambda)
      (fun _ => rR + u₂ / wwLambda) P 𝓕β Wβ VLβ VRβ Bβ ζβ (fun ω => Exist.flowField 0 u₂ (h ω)) := hCβ
  have hCα' : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₁ / wwLambda)
      (fun _ => rR + u₁ / wwLambda) P 𝓕α Wα VLα VRα Bα ζα (fun ω => Exist.flowField 0 u₁ (h ω)) := hCα
  have hCγ' : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - 0 / wwLambda)
      (fun _ => rR + 0 / wwLambda) P 𝓕γ Wγ VLγ VRγ Bγ ζγ (fun ω => Exist.flowField 0 0 (h ω)) := hCγ
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData 4 (fun _ : Fin 1 => rL)
    (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR
  -- Proposition 4.19: the order; Lemma 4.21: no common arc of the middle line with a wall
  have hord := ae_isOrderedArcs_of_prop419 h419 hu₁ hu₂ hLβ hRα hCα' hCγ' hCβ'
  have hncα := h421 rL rR u₁ 0 hu₁.ne hLα hRα hLγ hRγ P h 𝓕α Wα VLα VRα Bα ζα 𝓕γ Wγ VLγ VRγ Bγ ζγ hCα' hCγ'
  have hncβ := h421 rL rR u₂ 0 hu₂.ne' hLβ hRβ hLγ hRγ P h 𝓕β Wβ VLβ VRβ Bβ ζβ 𝓕γ Wγ VLγ VRγ Bγ ζγ hCβ' hCγ'
  obtain ⟨β, α, γ, hS⟩ := isSeedThreeSpace_of_seed hu₁ hu₂ hLβ hRα hh hu₀ hCβ' hCα' hCγ' hord
    (hncα.and hncβ)
  exact ⟨Ω, mΩ, P, hP, h, u₀, β, α, γ, hS⟩

/-- **`Chamber4.Chamber4JointStatement` from Proposition 4.19, Lemma 4.21 and the chamber clause (J5)**
(`seedThreeSpaceStatement_of_prop419`, `chamber4JointStatement_of_clause`). Conditional helper. -/
theorem chamber4JointStatement_of_prop419 (h419 : Prop419Statement.{u}) (h421 : Lemma421SeedStatement.{u})
    (hcl : ChamberClauseStatement.{u}) : Chamber4.Chamber4JointStatement.{u} :=
  chamber4JointStatement_of_clause (seedThreeSpaceStatement_of_prop419 h419 h421) hcl

/-- **`LP.TwoSeedGraphInput 4` from Proposition 4.19, Lemma 4.21 and the chamber clause (J5)**
(`Chamber4.twoSeedGraphInput_four_of_joint`). Conditional helper. -/
theorem twoSeedGraphInput_four_of_prop419 (h419 : Prop419Statement.{u}) (h421 : Lemma421SeedStatement.{u})
    (hcl : ChamberClauseStatement.{u}) : LP.TwoSeedGraphInput.{u} 4 :=
  Chamber4.twoSeedGraphInput_four_of_joint (chamber4JointStatement_of_prop419 h419 h421 hcl)

end InteractingSLE.WangWu.ChamberCond
