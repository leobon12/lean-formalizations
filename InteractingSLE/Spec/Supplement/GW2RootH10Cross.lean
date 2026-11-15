/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH10Tail
import InteractingSLE.Spec.Supplement.GW2RootW8Family
import InteractingSLE.Spec.Supplement.GW2TipStageWord

/-!
# Crossing estimates from literal joint-chart boundary profiles

Continuation of PROVE-T14-GW2ROOT2. The force vectors and positions are
those of the boundary datum itself. Ordered positions, separation, a far
cutoff, all limiting inner margins, angle convergence and extreme totals
are derived, rather than separate assumptions. The supplied evolutions,
boundary profiles, far heights and actual retained-law identification
remain mathematical inputs. This does not construct the root experiment.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH10

open QuantumZipper RootN4 Supp12.DSReach CS3Cross

/-- The upper-extreme crossing estimate for the actual flow-line word.
The sole admissibility requirement on original opposite groups is `S>-2`;
no bound is imposed on far attracting cumulatives. -/
theorem exists_crossing_top (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hOldL : ∀ y ∈ Set.Ioo (-3) 0, y ∉ J → b y ∈ oldLeftHeights κ)
    (hR : ∀ y, 0 < y → y ∉ J → b y ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧
        b y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hxm : flowLineXL b J 0 (GW2TipStage.lastL b J) ≤ -3)
    (hxp : 0 < flowLineXR b J 0 (GW2TipStage.lastR b J))
    (hfarL : ∀ y, y < flowLineXL b J 0 (GW2TipStage.lastL b J) → y ∉ J →
      b y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR b J 0 (GW2TipStage.lastR b J) < y → y ∉ J →
      b y = sleLambda (16 / κ) - Real.pi * chiC κ)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (Real.pi / 2)))
    (e : ℕ → EvolutionData.{u} (flowLineNL b J 0) (flowLineNR b J 0))
    (e₀ : EvolutionData.{u} (flowLineNL b J 0) (flowLineNR b J 0))
    (hE : ∀ m, (e m).IsEvolution κ
      (flowLineXL b J 0) (flowLineRhoL κ b J 0 (θs m))
      (flowLineXR b J 0) (flowLineRhoR κ b J 0 (θs m)))
    (hE₀ : e₀.IsEvolution κ
      (flowLineXL b J 0) (flowLineRhoL κ b J 0 (Real.pi / 2))
      (flowLineXR b J 0) (flowLineRhoR κ b J 0 (Real.pi / 2))) :
    ∃ cut : ℕ, cut ≤ flowLineNL b J 0 ∧
      (∀ i : Fin (flowLineNL b J 0), (i : ℕ) < cut →
        -3 < flowLineXL b J 0 i) ∧
      (∀ i : Fin (flowLineNL b J 0), cut ≤ (i : ℕ) →
        flowLineXL b J 0 i ≤ -3) ∧
      ∀ δ : ℝ≥0∞, 0 < δ → ∃ n : ℕ, ∀ᶠ m in atTop,
        1 - δ < (e m).P (reachEvent (n : ℝ≥0) leftTarget
          (leftBuf cut (flowLineNR b J 0) n)
          (e m).W (e m).VL (e m).VR (e m).lifetime) := by
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  obtain ⟨cut, hcut, hnear, hfar⟩ :=
    exists_antitone_cut (flowLineXL b J 0) hF.1 (-3)
  obtain ⟨η, hη, hsepL, hsepR⟩ := exists_positive_separation hF
  obtain ⟨hpL, hpR⟩ := strict_prefixes_top hκ hκ4 hb hOldL hR
  have hsL := (GW2TipStage.sum_flowLineRhoL_eq_of_far hκ hb
    (Real.pi / 2) hfarL).trans (GW2TipStage.totals_far_half_pi hκ).1
  have hsR := (GW2TipStage.sum_flowLineRhoR_eq_of_far hκ hb
    (Real.pi / 2) hfarR).trans (GW2TipStage.totals_far_half_pi hκ).2
  let q : RootW8.QualitativeFamily.{u} κ :=
    { nL := flowLineNL b J 0
      nR := flowLineNR b J 0
      hnL := by unfold flowLineNL; omega
      hnR := by unfold flowLineNR; omega
      xL := flowLineXL b J 0
      xR := flowLineXR b J 0
      ρLs := fun m => flowLineRhoL κ b J 0 (θs m)
      ρRs := fun m => flowLineRhoR κ b J 0 (θs m)
      ρL₀ := flowLineRhoL κ b J 0 (Real.pi / 2)
      ρR₀ := flowLineRhoR κ b J 0 (Real.pi / 2)
      sequence := e
      limit := e₀
      mL := cut
      mR := flowLineNR b J 0 - 1
      η := η
      goLeft := true
      hη := hη
      hxL0 := rfl
      hxR0 := rfl
      hxL := hsepL
      hxR := hsepR
      hF := hF
      hpsL := fun i hi => hpL i (hnear i hi)
      hpsR := fun i _ => hpR i
      hρL := (continuous_flowLineRhoL κ b J).continuousAt.tendsto.comp hθ
      hρR := (continuous_flowLineRhoR κ b J).continuousAt.tendsto.comp hθ
      hE := hE
      hE₀ := hE₀
      horientation := Or.inl ⟨rfl, rfl, hxp, hxm, hfar, hsL, hsR⟩ }
  exact ⟨cut, hcut, hnear, hfar,
    fun _ hδ => q.exists_buffer_eventually_lt h13 hκ hκ4 hδ⟩

/-- The lower-extreme counterpart, with no admissibility requirement on
far right attracting groups. The far cutoff and separation are constructed. -/
theorem exists_crossing_bottom (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hL : ∀ y, y < 0 → y ∉ J → b y ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧
        b y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hOldR : ∀ y ∈ Set.Ioo 0 3, y ∉ J → b y ∈ oldRightHeights κ)
    (hxm : flowLineXL b J 0 (GW2TipStage.lastL b J) < 0)
    (hxp : 3 ≤ flowLineXR b J 0 (GW2TipStage.lastR b J))
    (hfarL : ∀ y, y < flowLineXL b J 0 (GW2TipStage.lastL b J) → y ∉ J →
      b y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR b J 0 (GW2TipStage.lastR b J) < y → y ∉ J →
      b y = sleLambda (16 / κ) - Real.pi * chiC κ)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (-(Real.pi / 2))))
    (e : ℕ → EvolutionData.{u} (flowLineNL b J 0) (flowLineNR b J 0))
    (e₀ : EvolutionData.{u} (flowLineNL b J 0) (flowLineNR b J 0))
    (hE : ∀ m, (e m).IsEvolution κ
      (flowLineXL b J 0) (flowLineRhoL κ b J 0 (θs m))
      (flowLineXR b J 0) (flowLineRhoR κ b J 0 (θs m)))
    (hE₀ : e₀.IsEvolution κ
      (flowLineXL b J 0) (flowLineRhoL κ b J 0 (-(Real.pi / 2)))
      (flowLineXR b J 0) (flowLineRhoR κ b J 0 (-(Real.pi / 2)))) :
    ∃ cut : ℕ, cut ≤ flowLineNR b J 0 ∧
      (∀ i : Fin (flowLineNR b J 0), (i : ℕ) < cut →
        flowLineXR b J 0 i < 3) ∧
      (∀ i : Fin (flowLineNR b J 0), cut ≤ (i : ℕ) →
        3 ≤ flowLineXR b J 0 i) ∧
      ∀ δ : ℝ≥0∞, 0 < δ → ∃ n : ℕ, ∀ᶠ m in atTop,
        1 - δ < (e m).P (reachEvent (n : ℝ≥0) rightTarget
          (rightBuf (flowLineNL b J 0) cut n)
          (e m).W (e m).VL (e m).VR (e m).lifetime) := by
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  obtain ⟨cut, hcut, hnear, hfar⟩ :=
    exists_monotone_cut (flowLineXR b J 0) hF.2.2.1 3
  obtain ⟨η, hη, hsepL, hsepR⟩ := exists_positive_separation hF
  obtain ⟨hpL, hpR⟩ := strict_prefixes_bottom hκ hκ4 hb hL hOldR
  have hsL := (GW2TipStage.sum_flowLineRhoL_eq_of_far hκ hb
    (-(Real.pi / 2)) hfarL).trans (GW2TipStage.totals_far_neg_half_pi hκ).1
  have hsR := (GW2TipStage.sum_flowLineRhoR_eq_of_far hκ hb
    (-(Real.pi / 2)) hfarR).trans (GW2TipStage.totals_far_neg_half_pi hκ).2
  let q : RootW8.QualitativeFamily.{u} κ :=
    { nL := flowLineNL b J 0
      nR := flowLineNR b J 0
      hnL := by unfold flowLineNL; omega
      hnR := by unfold flowLineNR; omega
      xL := flowLineXL b J 0
      xR := flowLineXR b J 0
      ρLs := fun m => flowLineRhoL κ b J 0 (θs m)
      ρRs := fun m => flowLineRhoR κ b J 0 (θs m)
      ρL₀ := flowLineRhoL κ b J 0 (-(Real.pi / 2))
      ρR₀ := flowLineRhoR κ b J 0 (-(Real.pi / 2))
      sequence := e
      limit := e₀
      mL := flowLineNL b J 0 - 1
      mR := cut
      η := η
      goLeft := false
      hη := hη
      hxL0 := rfl
      hxR0 := rfl
      hxL := hsepL
      hxR := hsepR
      hF := hF
      hpsL := fun i _ => hpL i
      hpsR := fun i hi => hpR i (hnear i hi)
      hρL := (continuous_flowLineRhoL κ b J).continuousAt.tendsto.comp hθ
      hρR := (continuous_flowLineRhoR κ b J).continuousAt.tendsto.comp hθ
      hE := hE
      hE₀ := hE₀
      horientation := Or.inr ⟨rfl, rfl, hxm, hxp, hfar, hsR, hsL⟩ }
  exact ⟨cut, hcut, hnear, hfar,
    fun _ hδ => q.exists_buffer_eventually_lt h13 hκ hκ4 hδ⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootH10
