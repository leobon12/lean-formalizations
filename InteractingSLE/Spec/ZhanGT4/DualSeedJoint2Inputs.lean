/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstEight
import InteractingSLE.Spec.ZhanGT4.A1EightSeedAssembly

/-!
# The measurable original inputs extracted from an Eight source column

PROVE-ZHAN-GT4-A22. Only one frozen column is used here. Its driver and its
original source and seed coordinates are independent of the frozen sample.
Thus their adaptedness supplies product-space inputs without any measurable
choice of the column Brownian motions as the other sample varies.
-/

set_option autoImplicit false
noncomputable section
open Complex Set MeasureTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (fwdMap)
open A1EightSeed

/-- The stochastic half of one Eight column makes all original driving and
masked source/seed observables measurable in the ambient first sigma algebra. -/
theorem eight_source_inputs_measurable {X Y : Type*} {mX : MeasurableSpace X}
    {𝓕 : Filtration ℝ≥0 mX} {P : Measure X} {κ p t : ℝ}
    {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {y : Y} {B D : ℝ≥0 → X → ℝ}
    (h : IsColumnStoch 𝓕 P (A2X.kh κ)
      (fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t (x, y)) (S₁ m) B D) :
    (∀ u : ℝ≥0, Measurable fun x => eightDrv W₁ S₁ m x u) ∧
    (∀ (u : ℝ≥0) k, Measurable ({x | u ≤ S₁ m x}.indicator fun x => eightMarks VL₁ VR₁ x k u)) ∧
    (∀ u : ℝ≥0, Measurable ({x | u ≤ S₁ m x}.indicator fun x =>
      (fwdMap (eightDrv W₁ S₁ m x) u p).re + eightDrv W₁ S₁ m x u)) ∧
    ∀ u : ℝ≥0, Measurable ({x | u ≤ S₁ m x}.indicator fun x =>
      (deriv (fwdMap (eightDrv W₁ S₁ m x) u) p).re) := by
  obtain ⟨hB, -, hDm, -, hdW, -, hV, hV₀, hG₀⟩ := h
  refine ⟨?_, fun u k => (hV u k).mono (𝓕.le u) le_rfl,
    fun u => (hV₀ u).mono (𝓕.le u) le_rfl, fun u => (hG₀ u).mono (𝓕.le u) le_rfl⟩
  intro u
  have he : (fun x => eightDrv W₁ S₁ m x u) = fun x => Real.sqrt (A2X.kh κ) * B u x + D u x := by
    funext x
    have hh := congrFun (hdW x) (u : ℝ)
    change eightDrv W₁ S₁ m x u = driftDriver (Real.sqrt (A2X.kh κ)) B D x u at hh
    simpa only [driftDriver, Real.toNNReal_coe] using hh
  rw [he]
  exact ((measurable_const.mul (hB.2.1 u)).add (hDm u)).mono (𝓕.le u) le_rfl

/-- Lift a measurable masked first observable to any smaller measurable
product event. The observable itself need not be measurable outside its mask. -/
theorem measurable_mask_prod_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {A : Set X} {G : Set (X × Y)} {f : X → ℝ}
    (hf : Measurable (A.indicator f)) (hG : MeasurableSet G)
    (hsub : ∀ ω ∈ G, ω.1 ∈ A) :
    Measurable (G.indicator fun ω => f ω.1) := by
  convert (hf.comp measurable_fst).indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Function.comp_apply, indicator_of_mem (hsub ω hω)]
  · simp only [indicator_of_notMem hω]

end InteractingSLE.ZhanGT4
