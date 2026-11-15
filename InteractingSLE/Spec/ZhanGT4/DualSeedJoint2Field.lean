/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Fixed
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Continuity

/-!
# Joint measurability of Eight's actual normalized seeded rectangle fields

PROVE-ZHAN-GT4-A22. Fixed-time product measurability is proved from the original
drivers and random hulls. Dyadic rounding and the two coordinate continuity
results then give the exact `A1Patch.IsFieldMeas` required by the assembly.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1EightSeed
open QuantumZipper (fwdHull)
open A1SeedField A2X A1Patch
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The actual Eight rectangle fields are measurable at measurable random times.
Columns are needed at every positive frozen height for continuity; all their
original inputs can be supplied by `A1Asm.isColumnStoch_eightRec_of_reg`. -/
theorem isFieldMeas_eight_of_originalBrownian {P₁ : Measure X} {P₂ : Measure Y} [IsFiniteMeasure P₂]
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
    (hW₂ : W₂ = fun u y => Real.sqrt κ * B₂ u y) (hS₂ : ∀ m y, 0 < S₂ m y)
    (hgood₂ : ∀ m y, (S₂ m y : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ p (S₂ m y) y) (S₂ m y) ⊆ H₂ m)
    (hstoch : ∀ m y (t : ℝ), 0 < t → t ≤ S₂ m y → ∃ B D : ℝ≥0 → X → ℝ,
      IsColumnStoch 𝓕₁ P₁ (kh κ) (fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y)) (S₁ m) B D) :
    ∀ m, IsFieldMeas (seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m))
      (fun _ : Unit => S₁ m) (fun _ : Unit => S₂ m) := by
  have : IsProbabilityMeasure P₂ := hB₂.isProbabilityMeasure'
  obtain ⟨y₀⟩ := nonempty_of_isProbabilityMeasure P₂
  have hc₂ : ∀ m y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc (0 : ℝ) (S₂ m y)) := by
    intro m y
    rw [hW₂]
    exact (continuous_const.mul ((hB₂c y).comp continuous_real_toNNReal)).continuousOn
  have h0₂ : ∀ y, W₂ 0 y = 0 := by intro y; simp only [hW₂, hB₂0 y, mul_zero]
  have hK₂ : ∀ m y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → fwdHull (frzPath W₂ p t y) t ⊆ H₂ m :=
    fun m y t ht htS => fwdHull_frzPath_subset (hc₂ m y) ht htS (hgood₂ m y).2
  have hne : ∀ m x (u : ℝ≥0), 0 < u → u ≤ S₁ m x →
      VL₁ 0 u x ≠ W₁ u x ∧ VR₁ 0 u x ≠ W₁ u x := fun m x u hu huS =>
    hsep₁ x u hu (lt_of_le_of_lt (ENNReal.coe_le_coe.2 huS) (hgood₁ m x).1)
  have hex : ∀ m x y (t : ℝ), 0 ≤ t → t ≤ S₂ m y → ∃ a W', OwnData (eightDrv W₁ S₁ m x)
      (fwdHull (frzPath W₂ p t y) t) (frzChart (frzPath W₂ p t y) t) (S₁ m x) a W' := fun m x y t ht htS =>
    exists_ownData_of_encl (continuous_eightDrv (hP x).2.2.2.1 (hgood₁ m x).1) (eightDrv_zero (hP x).1)
      (hgood₁ m x).2.1 (continuous_frzPath ((hc₂ m y).mono (Icc_subset_Icc_right htS)) ht)
      ht (hpp m).sep_pos (hpp m).sep (hgood₁ m x).2.2.2 (hK₂ m y t ht htS)
  intro m
  obtain ⟨B, D, hst⟩ := hstoch m y₀ (S₂ m y₀) (by exact_mod_cast hS₂ m y₀) le_rfl
  refine isFieldMeas_of_fixed_and_sepCont (fun s t hs ht => ?_) (fun ω t ht => ?_) (fun ω s hs => ?_)
  · exact measurable_eightHeightField_fixed (hpp m) hP hxL hxR
      (fun x => (hgood₁ m x).1) (fun x => (hgood₁ m x).2.1)
      (fun x u hu huS => (hne m x u hu huS).1) (fun x u hu huS => (hne m x u hu huS).2)
      (fun x => (hgood₁ m x).2.2.2) (fun y => (hgood₂ m y).2) (h₁ m) (h₂ m)
      B₂ hB₂ hB₂c hB₂0 hW₂ hst hs ht
  · by_cases ht0 : t = 0
    · subst t
      refine (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ))
        (Icc (0 : ℝ) (S₁ m ω.1))).congr fun s hs => ?_
      have he := normEll_eightRec_zero (κ := κ) (VL₁ := VL₁) (VR₁ := VR₁)
        ((hc₂ m ω.2).mono (Icc_subset_Icc_right (S₂ m ω.2).coe_nonneg))
        (h0₂ ω.2) (hex m ω.1 ω.2 0 le_rfl (S₂ m ω.2).coe_nonneg) hs.1 hs.2
      simp only [seedHeightField, he, sub_self, Real.exp_zero]
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    obtain ⟨B', D', hst'⟩ := hstoch m ω.2 t htpos ht.2
    have hrec := fun x => isSourceRecord_eightRec (κ := κ) (hP x) hxL hxR (hgood₁ m x).1 (hgood₁ m x).2.1
      (fun u hu huS => (hne m x u hu huS).1) (fun u hu huS => (hne m x u hu huS).2)
      ((hc₂ m ω.2).mono (Icc_subset_Icc_right ht.2)) (h0₂ ω.2) htpos
      (ht.2.trans (hgood₂ m ω.2).1) (hgood₁ m x).2.2.1 (hpp m).sep_pos (hpp m).sep
      (hgood₁ m x).2.2.2 (hK₂ m ω.2 t ht.1 ht.2)
    exact continuousOn_density_of_source_column (hpp m) (div_pos (by norm_num) hκ)
      hrec (h₁ m) hst' ω.1
  · apply continuousOn_of_continuous_stopped
    exact (eight_row_facts_of_enclosures (hpp m) hκ W₁ VL₁ VR₁ W₂ S₁ m ω.1 (S₂ m)
      (hP ω.1) hxL hxR (hgood₁ m ω.1).1 (hgood₁ m ω.1).2.1
      (fun u hu huS => (hne m ω.1 u hu huS).1) (fun u hu huS => (hne m ω.1 u hu huS).2)
      hs (hS₂ m) (hgood₁ m ω.1).2.2.1 (fun y => (hgood₂ m y).1)
      (hgood₁ m ω.1).2.2.2 (fun y => (hgood₂ m y).2)
      𝓕₂ B₂ hB₂ hB₂c hB₂0 hW₂ (h₂ m)).2.1 ω.2

end InteractingSLE.ZhanGT4.A1EightSeed
