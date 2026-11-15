/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstEightDriver

/-!
# The concrete Eight field rows from original marginal data

Packet PROVE-ZHAN-GT4-A22. This provides the exact rectangle-wise Eight
field, with the zero first prefix included. No row, D9, source-version,
image-chain, compensating drift or density identity is assumed.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (fwdHull)

/-- Original Brownian large-curve data and integrated small-curve seeds
prove the actual Eight row martingale, continuity, boundedness and entrance. -/
theorem eight_row_facts_of_enclosures {X Y : Type*} [MeasurableSpace Y]
    {P : Measure Y} [IsFiniteMeasure P] {κ p δ q d Tm s : ℝ} {H₁ H₂ : Set ℂ}
    (hp : A1SeedField.IsProtectedPair H₁ H₂ δ p q d) (hκ : 0 < κ)
    (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
    (W₂ : ℝ≥0 → Y → ℝ) (S₁ : ℕ → X → ℝ≥0) (m : ℕ) (x : X) (T : Y → ℝ≥0)
    {a : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (hP : IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x) (fun i u => VL₁ i u x)
      (fun i u => VR₁ i u x) (B₁ · x) (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    (hLife : (S₁ m x : ℝ≥0∞) < ζ₁ x) (hS : 0 < (S₁ m x : ℝ))
    (hL : ∀ u : ℝ≥0, 0 < u → u ≤ S₁ m x → VL₁ 0 u x ≠ W₁ u x)
    (hR : ∀ u : ℝ≥0, 0 < u → u ≤ S₁ m x → VR₁ 0 u x ≠ W₁ u x)
    (hs : s ∈ Icc (0 : ℝ) (S₁ m x)) (hT : ∀ y, 0 < T y)
    (hSm : (S₁ m x : ℝ) ≤ Tm) (hTm : ∀ y, (T y : ℝ) ≤ Tm)
    (hK₁ : fwdHull (A1EightSeed.eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁)
    (hK₂ : ∀ y, fwdHull (A1EightSeed.frzPath W₂ p (T y) y) (T y) ⊆ H₂)
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Y›) (B : ℝ≥0 → Y → ℝ)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ y, Continuous (B · y)) (hB0 : ∀ y, B 0 y = 0)
    (hW₂ : W₂ = fun u y => Real.sqrt κ * B u y)
    (hStop : IsStoppingTime 𝓕 fun y => (T y : WithTop ℝ≥0)) :
    Martingale (fun (t : ℝ≥0) y =>
      seedHeightField (A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (min (t : ℝ) (T y))) 𝓕 P ∧
    (∀ y, Continuous fun t : ℝ≥0 =>
      seedHeightField (A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (min (t : ℝ) (T y))) ∧
    (∃ C : ℝ, ∀ (t : ℝ≥0) y,
      |seedHeightField (A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (min (t : ℝ) (T y))| ≤ C) ∧
    ∀ y, seedHeightField (A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s 0 = 1 := by
  by_cases hs0 : s = 0
  · subst s
    simp only [seedHeightField_zero_left]
    exact ⟨martingale_const 𝓕 P 1, fun _ => continuous_const,
      ⟨1, fun _ _ => by norm_num⟩, fun _ => True.intro⟩
  have hsp : s ∈ Ioc (0 : ℝ) (S₁ m x) := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
  have hkh : 0 < A2X.kh κ := div_pos (by norm_num) hκ
  have hkk : 16 / A2X.kh κ = κ := by unfold A2X.kh; field_simp
  have hWc := A1EightSeed.continuous_eightDrv (S₁ := S₁) (m := m) hP.2.2.2.1 hLife
  have hW0 := A1EightSeed.eightDrv_zero (S₁ := S₁) (m := m) hP.1
  have hEq := A1EightSeed.eightDrv_eqOn W₁ S₁ m x
  have hlo := A1SeedField.isSeedCoordinate_vL_of_path hP 0 hxL hLife hL hEq
  have hhi := A1SeedField.isSeedCoordinate_vR_of_path hP 0 hxR hLife hR hEq
  have hseed : ∀ i, IsSeedCoordinate (A1EightSeed.eightDrv W₁ S₁ m x)
      (A1EightSeed.eightMarks VL₁ VR₁ x i) (S₁ m x) := by
    intro i
    fin_cases i
    · exact hlo
    · exact hhi
  have hVI : ∀ i, A1EightSeed.eightMarks VL₁ VR₁ x i s ∈
      uIcc (Strip.extPath (VL₁ 0 · x) s) (Strip.extPath (VR₁ 0 · x) s) :=
    fun i => A1SeedField.seedPair_marks _ _ s i
  have hDriver : ∀ y, A1EightSeed.frzPath W₂ p (T y) y =
      seedStoppedDriver (Real.sqrt (16 / A2X.kh κ)) p B T y := by
    intro y
    rw [hkk, hW₂, seedStoppedDriver_eq_frzPath]
  have hf := seedStopped_row_facts_of_enclosures hp hkh (A1EightSeed.eightRR κ)
    (A1EightSeed.eightDrv W₁ S₁ m x) (Strip.extPath (VL₁ 0 · x)) (Strip.extPath (VR₁ 0 · x))
    (A1EightSeed.eightMarks VL₁ VR₁ x) (fun y => A1EightSeed.frzPath W₂ p (T y) y)
    𝓕 B T hS hT hsp hDriver hWc hW0 hK₁ hK₂ hlo hhi hseed hVI
    (A1SeedField.seedPair_injective hP 0 0 hLife hL hR s hsp) hSm hTm hB hBc hB0
    (mirrorSourceCharge_eightRR hkh.ne') hStop
  have hc₂ : ∀ y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc (0 : ℝ) (T y)) := by
    intro y
    rw [hW₂]
    exact (continuous_const.mul ((hBc y).comp continuous_real_toNNReal)).continuousOn
  have h0₂ : ∀ y, W₂ 0 y = 0 := by intro y; simp only [hW₂, hB0 y, mul_zero]
  have he := eightHeightField_eq_seedSView κ p W₁ VL₁ VR₁ W₂ S₁ m x T hc₂ h0₂ s
  have heq : (fun (t : ℝ≥0) y =>
      seedHeightField (A1EightSeed.eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) (x, y) s (min (t : ℝ) (T y))) =
      (fun (t : ℝ≥0) y => seedHeightField (fun v y => seedSView (A2X.kh κ) (A1EightSeed.eightRR κ)
        (A1EightSeed.eightDrv W₁ S₁ m x) (A1EightSeed.frzPath W₂ p (T y) y)
        (seedSrcClock (A1EightSeed.eightDrv W₁ S₁ m x) (S₁ m x) (A1EightSeed.frzPath W₂ p (T y) y))
        (seedSrcDriver (A1EightSeed.eightDrv W₁ S₁ m x) (S₁ m x) (A1EightSeed.frzPath W₂ p (T y) y))
        (A1EightSeed.eightMarks VL₁ VR₁ x) v) y s (min (t : ℝ) (T y))) := funext fun t => funext (he t)
  refine ⟨heq ▸ hf.1, ?_, ?_, ?_⟩
  · intro y
    exact (hf.2.1 y).congr fun t => (he t y).symm
  · obtain ⟨C, hC⟩ := hf.2.2.1
    exact ⟨C, fun t y => by rw [he t y]; exact hC t y⟩
  · intro y
    have he0 := he 0 y
    simp only [NNReal.coe_zero, min_eq_left (T y).coe_nonneg] at he0
    exact he0.trans (hf.2.2.2 y)

end InteractingSLE.ZhanGT4
