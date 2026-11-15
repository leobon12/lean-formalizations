/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Prefix

/-!
# Rectangle measurability from a Brownian driving equation on the protected prefix

PROVE-ZHAN-GT4-A22. The original driving equation is required only before the
exits. A globally Brownian reference driver has the same frozen records there.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1EightSeed
open QuantumZipper (fwdHull)
open A1SeedField A2X A1Patch
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The actual field is measurable if the large driving equation holds only
on every protected prefix. No assertion about its post-lifetime path is needed. -/
theorem isFieldMeas_eight_of_prefixBrownian {P₁ : Measure X} {P₂ : Measure Y} [IsFiniteMeasure P₂]
    {κ p a : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    (𝓕₁ : Filtration ℝ≥0 mX) (𝓕₂ : Filtration ℝ≥0 mY) (S₁ : ℕ → X → ℝ≥0) (S₂ : ℕ → Y → ℝ≥0)
    (H₁ H₂ : ℕ → Set ℂ) (δ q dd Tm : ℕ → ℝ)
    (h₁ : ∀ m, IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (h₂ : ∀ m, IsStoppingTime 𝓕₂ fun y => (S₂ m y : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPair (H₁ m) (H₂ m) (δ m) p (q m) (dd m))
    (hP : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i s => VL₁ i s x) (fun i s => VR₁ i s x) (B₁ · x)
      (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    (hgood₁ : ∀ m x, (S₁ m x : ℝ≥0∞) < ζ₁ x ∧ 0 < (S₁ m x : ℝ) ∧ (S₁ m x : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁ m)
    (hsep₁ : ∀ x (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ x → VL₁ 0 s x ≠ W₁ s x ∧ VR₁ 0 s x ≠ W₁ s x)
    (hκ : 0 < κ) (B₂ : ℝ≥0 → Y → ℝ) (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂)
    (hB₂c : ∀ y, Continuous (B₂ · y)) (hB₂0 : ∀ y, B₂ 0 y = 0)
    (hW₂ : ∀ m y (u : ℝ≥0), u ≤ S₂ m y → W₂ u y = Real.sqrt κ * B₂ u y) (hS₂ : ∀ m y, 0 < S₂ m y)
    (hgood₂ : ∀ m y, (S₂ m y : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂ m)
    (hstoch : ∀ m y (t : ℝ), 0 < t → t ≤ S₂ m y → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓕₁ P₁ (kh κ) (fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y)) (S₁ m) B D) :
    ∀ m, IsFieldMeas (seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m))
      (fun _ : Unit => S₁ m) (fun _ : Unit => S₂ m) := by
  let V : ℝ≥0 → Y → ℝ := fun u y => Real.sqrt κ * B₂ u y
  have hf : ∀ m y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → frzPath W₂ p t y = frzPath V p t y :=
    fun m y t ht htS => frzPath_eq_of_prefix (hW₂ m y) p ht htS
  have hg : ∀ m y, (S₂ m y : ℝ) ≤ Tm m ∧ fwdHull (frzPath V p (S₂ m y) y) (S₂ m y) ⊆ H₂ m := by
    intro m y
    rw [← hf m y (S₂ m y) (S₂ m y).coe_nonneg le_rfl]
    exact hgood₂ m y
  have hc : ∀ m y (t : ℝ), 0 < t → t ≤ S₂ m y → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓕₁ P₁ (kh κ) (fun x => eightRec κ p W₁ VL₁ VR₁ V S₁ m t (x, y)) (S₁ m) B D := by
    intro m y t ht htS
    obtain ⟨B, D, h⟩ := hstoch m y t ht htS
    refine ⟨B, D, ?_⟩
    have he : (fun x => eightRec κ p W₁ VL₁ VR₁ V S₁ m t (x, y)) =
        fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y) := by
      funext x
      exact (eightRec_eq_of_second_prefix κ p W₁ VL₁ VR₁ S₁ m x (hW₂ m y) ht.le htS).symm
    rw [he]
    exact h
  have hm := isFieldMeas_eight_of_originalBrownian 𝓕₁ 𝓕₂ S₁ S₂ H₁ H₂ δ q dd Tm h₁ h₂ hpp
    hP hxL hxR hgood₁ hsep₁ hκ B₂ hB₂ hB₂c hB₂0 rfl hS₂ hg hc
  intro m
  refine (hm m).congr_on_unit fun ω s t _ _ ht htS => ?_
  have he := eightRec_eq_of_second_prefix κ p W₁ VL₁ VR₁ S₁ m ω.1
    (W := W₂) (V := V) (y := ω.2) (hW₂ m ω.2) ht htS
  simp only [seedHeightField, he]
  rfl

end InteractingSLE.ZhanGT4.A1EightSeed
