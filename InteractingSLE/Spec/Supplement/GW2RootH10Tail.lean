/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH10Geometry
import InteractingSLE.Spec.Supplement.GW2RootW8Margins

/-!
# DS1 tails for the flow-line word under the GW2 height profiles

Continuation of PROVE-T14-GW2ROOT2. Angle convergence gives convergence of
the actual finite flow-line weight vectors. The preceding boundary-height
arguments prove their limiting inner partial sums, so the existing finite
DS1 tail theorem constructs the constants. Far attracting weights need not
be admissible, and no alternating-initial-word condition is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Finset Filter Topology

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH10

open QuantumZipper Supp12.DS2

/-- The left flow-line vector is continuous in the current angle. -/
theorem continuous_flowLineRhoL (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) :
    Continuous fun θ : ℝ => flowLineRhoL κ b J 0 θ := by
  apply continuous_pi
  intro i
  have hc : Continuous fun θ : ℝ => θ * chiC κ / sleLambda κ :=
    (continuous_id.mul continuous_const).div_const _
  have heq : (fun θ : ℝ => flowLineRhoL κ b J 0 θ i) =
      fun θ => flowLineRhoL κ b J 0 0 i +
        if (i : ℕ) = 0 then -(θ * chiC κ / sleLambda κ) else 0 :=
    funext fun θ => GW1Conn.flowLineRhoL_theta κ b J θ i
  rw [heq]
  by_cases hi : (i : ℕ) = 0
  · simp only [hi, ↓reduceIte]
    exact continuous_const.add (continuous_neg.comp hc)
  · simpa only [hi, ↓reduceIte, add_zero] using
      (continuous_const : Continuous fun _ : ℝ => flowLineRhoL κ b J 0 0 i)

/-- The right flow-line vector is continuous in the current angle. -/
theorem continuous_flowLineRhoR (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) :
    Continuous fun θ : ℝ => flowLineRhoR κ b J 0 θ := by
  apply continuous_pi
  intro i
  have hc : Continuous fun θ : ℝ => θ * chiC κ / sleLambda κ :=
    (continuous_id.mul continuous_const).div_const _
  have heq : (fun θ : ℝ => flowLineRhoR κ b J 0 θ i) =
      fun θ => flowLineRhoR κ b J 0 0 i +
        if (i : ℕ) = 0 then θ * chiC κ / sleLambda κ else 0 :=
    funext fun θ => GW1Conn.flowLineRhoR_theta κ b J θ i
  rw [heq]
  by_cases hi : (i : ℕ) = 0
  · simp only [hi, ↓reduceIte]
    exact continuous_const.add hc
  · simpa only [hi, ↓reduceIte, add_zero] using
      (continuous_const : Continuous fun _ : ℝ => flowLineRhoR κ b J 0 0 i)

/-- A tail approaching the upper extreme satisfies DS1 from the literal
old-angle/original-counterflow height profiles. -/
theorem exists_ds1_tail_top {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hOldL : ∀ y ∈ Set.Ioo (-3) 0, y ∉ J → b y ∈ oldLeftHeights κ)
    (hR : ∀ y, 0 < y → y ∉ J → b y ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧
        b y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    {cut : ℕ} (hnear : ∀ i : Fin (flowLineNL b J 0),
      (i : ℕ) < cut → -3 < flowLineXL b J 0 i)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (Real.pi / 2))) :
    ∃ Rw ε : ℝ, 0 < ε ∧
      IsDS1Word cut (flowLineNR b J 0 - 1) Rw ε
        (flowLineXL b J 0) (flowLineXR b J 0)
        (flowLineRhoL κ b J 0 (Real.pi / 2))
        (flowLineRhoR κ b J 0 (Real.pi / 2)) ∧
      ∃ N : ℕ, ∀ m ≥ N,
        IsDS1Word cut (flowLineNR b J 0 - 1) Rw ε
          (flowLineXL b J 0) (flowLineXR b J 0)
          (flowLineRhoL κ b J 0 (θs m)) (flowLineRhoR κ b J 0 (θs m)) := by
  obtain ⟨hL, hR'⟩ := strict_prefixes_top hκ hκ4 hb hOldL hR
  exact RootW8.exists_ds1_tail (Theorem15.isOrderedForceWord_flowLine b J 0)
    (fun i hi => hL i (hnear i hi)) (fun i _ => hR' i)
    ((continuous_flowLineRhoL κ b J).continuousAt.tendsto.comp hθ)
    ((continuous_flowLineRhoR κ b J).continuousAt.tendsto.comp hθ)

/-- The reflected DS1 tail approaching the lower extreme. -/
theorem exists_ds1_tail_bottom {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ y, y < 0 → y ∉ J → b y ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧
        b y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hOldR : ∀ y ∈ Set.Ioo 0 3, y ∉ J → b y ∈ oldRightHeights κ)
    {cut : ℕ} (hnear : ∀ i : Fin (flowLineNR b J 0),
      (i : ℕ) < cut → flowLineXR b J 0 i < 3)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (-(Real.pi / 2)))) :
    ∃ Rw ε : ℝ, 0 < ε ∧
      IsDS1Word (flowLineNL b J 0 - 1) cut Rw ε
        (flowLineXL b J 0) (flowLineXR b J 0)
        (flowLineRhoL κ b J 0 (-(Real.pi / 2)))
        (flowLineRhoR κ b J 0 (-(Real.pi / 2))) ∧
      ∃ N : ℕ, ∀ m ≥ N,
        IsDS1Word (flowLineNL b J 0 - 1) cut Rw ε
          (flowLineXL b J 0) (flowLineXR b J 0)
          (flowLineRhoL κ b J 0 (θs m)) (flowLineRhoR κ b J 0 (θs m)) := by
  obtain ⟨hL', hR⟩ := strict_prefixes_bottom hκ hκ4 hb hL hOldR
  exact RootW8.exists_ds1_tail (Theorem15.isOrderedForceWord_flowLine b J 0)
    (fun i _ => hL' i) (fun i hi => hR i (hnear i hi))
    ((continuous_flowLineRhoL κ b J).continuousAt.tendsto.comp hθ)
    ((continuous_flowLineRhoR κ b J).continuousAt.tendsto.comp hθ)

end InteractingSLE.Theorem14.GW2TipSystem.RootH10
