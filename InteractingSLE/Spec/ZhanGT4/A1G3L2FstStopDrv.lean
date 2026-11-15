/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2FstStopFacts

/-!
# Zhan's A.1 under R83, (G3), large-curve direction: the record facts of the image driver and the forces

Packet PROVE-A1-G3LAW2. In the setting of `A1G3L2FstStopFacts`: **`g3FstStop_hgW`** (A1-SEEDGEOM's
`exists_measurable_rDrvFst_of_stopped`) and **`g3FstStop_hgVL`** (the time-`0` word read at `τ ∧ S₁ᵐ`; afterwards
A1-FORCES's `exists_measurable_rForceFst_of_stopped` with the frozen-chart marks of the stopped small curve), both at
the stopped frozen time `τ ∧ S₁ᵐ` and swapped back to `τ` on `{r < cap}`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom A1MultiMark

section Drv

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {VL₁o : Fin 1 → ℝ≥0 → X → ℝ} {VR₁o : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞}
  {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y} {τ : X → ℝ≥0}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hlife : ∀ (k : ℕ) (_ : X) (y₀ : Y),
    (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀))
  (hgood : ∀ (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0}, 0 < σ → σ ≤ g3S₁ x y W₁ ζ₁ k x₀ →
    A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) σ (g3S₂ x y W₂ ζ₂ k y₀))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x' => (τ x' : WithTop ℝ≥0))
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ (∀ i t, VL₁o i t x' = VL₁ i t x') ∧
    (∀ j t, VR₁o j t x' = VR₁ j t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

/-- The product of the two stopped records of rectangle `m` (large direction). -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₁ m)))
  (IsStoppingTime.measurableSpace (hs₂ m))

/-- The masked caps of the large direction. -/
local notation "𝓢" => maskCap G₁ G₂ (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂)

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood hag₁ hag₂

/-- **`hgW`** (large direction). -/
theorem g3FstStop_hgW (m : ℕ) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧ ∀ z, r < (𝓢) (τ z.1) m z →
    rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁o ω) 0 W₂o (fun ω => lifeEnd (W₂o · ω) (VL₂o 0 · ω) (ζ₂o ω)) y W₁o τ r z =
      f z := by
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := g3FstStop_repl hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  obtain ⟨f, hf, hfe⟩ := exists_measurable_rDrvFst_of_stopped (𝓐 := (hτ.min (hs₁ m)).measurableSpace)
    (𝓑 := (hs₂ m).measurableSpace) (live := fun t ω => (t : ℝ≥0∞) < ζ₁o ω) (live' := fun _ _ => True)
    (xj := 0) (xk := y) (Wj := W₂o) (Wj' := fun t y' => W₂ (min t (g3S₂ x y W₂ ζ₂ m y')) y')
    (ζj := fun ω => lifeEnd (W₂o · ω) (VL₂o 0 · ω) (ζ₂o ω)) (ζj' := fun _ => ⊤) (Wk := W₁o)
    (Wk' := fun t x' => W₁ (min t (g3Fτ x y W₁ ζ₁ τ m x')) x') (ζk' := fun _ => ⊤) (τ := g3Fτ x y W₁ ζ₁ τ m)
    (cap := fun z => (𝓢) (τ z.1) m z) (T := fun z => (g3S₂ x y W₂ ζ₂ m z.2 : ℝ)) (measurable_g3Fτ hs₁ hτ m)
    MeasurableSet.univ (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const r
    (fun z hz => g3FstStop_loc hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood hag₁ hag₂ m r z hz)
  refine ⟨f, hf, fun z hz => ?_⟩
  rw [← hfe z hz]
  exact (cImg_congr_of_eq (τ := fun z : X × Y => τ z.1) (τ₀ := fun z : X × Y => g3Fτ x y W₁ ζ₁ τ m z.1)
    (g3FstStop_tau_eq hag₁ hag₂ hz)).2 r

/-- **`hgVL`** (large direction). -/
theorem g3FstStop_hgVL (m : ℕ) (i : Fin 4) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧
    ∀ z, r < (𝓢) (τ z.1) m z → g3FstVL y W₁o VL₁o VR₁o ζ₁o W₂o VL₂o ζ₂o (τ z.1) i r z = f z := by
  have hpvX : ∀ (U : ℝ≥0 → X → ℝ), IsStronglyProgressive (usualAugmentation 𝓕₁ P₁) U →
      Measurable[(hτ.min (hs₁ m)).measurableSpace] fun x' : X => U (g3Fτ x y W₁ ζ₁ τ m x') x' := fun U hU =>
    measurable_stoppedValue' hU (hτ.min (hs₁ m)) (T := g3Fτ x y W₁ ζ₁ τ m)
      (fun x' => by simp only [g3Fτ, WithTop.coe_min])
  have hpv : ∀ (U : ℝ≥0 → X → ℝ), IsStronglyProgressive (usualAugmentation 𝓕₁ P₁) U →
      Measurable[𝓡 m] fun z : X × Y => U (g3Fτ x y W₁ ζ₁ τ m z.1) z.1 := fun U hU =>
    (hpvX U hU).comp (@measurable_fst X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace)
  by_cases hr : r = 0
  · subst hr
    refine ⟨fun z => g3FstWord W₁ VL₁ VR₁ (g3Fτ x y W₁ ζ₁ τ m z.1) z.1 i, ?_, fun z hz => ?_⟩
    · fin_cases i
      · exact (hpv _ (h₁.progVR 1)).sub (hpv _ (h₁.progVR 2))
      · exact (hpv _ (h₁.progVR 0)).sub (hpv _ (h₁.progVR 2))
      · exact (hpv _ h₁.progW).sub (hpv _ (h₁.progVR 2))
      · exact (hpv _ (h₁.progVL 0)).sub (hpv _ (h₁.progVR 2))
    · obtain ⟨h1, -, -⟩ := g3FstStop_pos (g3Fst_hag₁ hag₁) hag₂ hz
      obtain ⟨hW₁a, hV₁a, hR₁a, -⟩ := hag₁ z.1 h1
      rw [g3FstVL_zero]
      show g3FstWord W₁o VL₁o VR₁o (τ z.1) z.1 i = g3FstWord W₁ VL₁ VR₁ (g3Fτ x y W₁ ζ₁ τ m z.1) z.1 i
      rw [← g3FstStop_tau_eq hag₁ hag₂ hz]
      simp only [g3FstWord, hW₁a, hV₁a, hR₁a]
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := g3FstStop_repl hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  have hp' : Measurable[(hτ.min (hs₁ m)).measurableSpace] fun x' : X =>
      largeG3Marks (y - 0) (W₁ · x') (fun i t => VL₁ i t x') (fun j t => VR₁ j t x') (g3Fτ x y W₁ ζ₁ τ m x') i := by
    fin_cases i
    · exact measurable_const.add (hpvX _ (h₁.progVR 1))
    · exact measurable_const.add (hpvX _ (h₁.progVR 0))
    · exact measurable_const.add (hpvX _ h₁.progW)
    · exact measurable_const.add (hpvX _ (h₁.progVL 0))
  obtain ⟨f, hf, hfe⟩ := exists_measurable_rForceFst_of_stopped (𝓐 := (hτ.min (hs₁ m)).measurableSpace)
    (𝓑 := (hs₂ m).measurableSpace) (live := fun t ω => (t : ℝ≥0∞) < ζ₁o ω) (live' := fun _ _ => True)
    (xj := 0) (xk := y) (Wj := W₂o) (Wj' := fun t y' => W₂ (min t (g3S₂ x y W₂ ζ₂ m y')) y')
    (ζj := fun ω => lifeEnd (W₂o · ω) (VL₂o 0 · ω) (ζ₂o ω)) (ζj' := fun _ => ⊤) (Wk := W₁o)
    (Wk' := fun t x' => W₁ (min t (g3Fτ x y W₁ ζ₁ τ m x')) x') (ζk' := fun _ => ⊤) (τ := g3Fτ x y W₁ ζ₁ τ m)
    (measurable_g3Fτ hs₁ hτ m) MeasurableSet.univ (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm
    measurable_const measurable_const
    (p := fun x' => largeG3Marks (y - 0) (W₁o · x') (fun i t => VL₁o i t x') (fun j t => VR₁o j t x')
      (g3Fτ x y W₁ ζ₁ τ m x') i) hp' (cap := fun z => (𝓢) (τ z.1) m z)
    (T := fun z => (g3S₂ x y W₂ ζ₂ m z.2 : ℝ)) r
    (fun z hz => g3FstStop_loc hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood hag₁ hag₂ m r z hz)
    (fun z hz => by
      obtain ⟨h1, -, -⟩ := g3FstStop_pos (g3Fst_hag₁ hag₁) hag₂ (zero_le.trans_lt hz)
      obtain ⟨hW₁a, hV₁a, hR₁a, -⟩ := hag₁ z.1 h1
      simp only [largeG3Marks, hW₁a, hV₁a, hR₁a])
  refine ⟨f, hf, fun z hz => ?_⟩
  have hτe := g3FstStop_tau_eq hag₁ hag₂ hz
  rw [← hfe z hz]
  unfold g3FstVL
  rw [ite_eq_right_of_eq_false _ _ (eq_false hr)]
  exact rForceFst_tau_congr (τ₁ := fun _ => τ z.1) hτe (by simp only [hτe]) r

end Drv

end InteractingSLE.ZhanGT4.A1G3L2
