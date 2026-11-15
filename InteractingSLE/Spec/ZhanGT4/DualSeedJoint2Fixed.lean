/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Pair
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Inputs
import InteractingSLE.Spec.ZhanGT4.A1G3CalcDrift

/-!
# Fixed-time joint measurability of the actual Eight seeded field

PROVE-ZHAN-GT4-A22. Both paths and their protected exits vary. A single source
column supplies the original measurable inputs; the image observables follow
from the unique random-hull mapping-out map. Both zero sides are included.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (fwdMap fwdHull IsForwardSol)
open A1EightSeed

/-- The actual Eight field at each fixed pair of times is measurable on its
random protected rectangle. No joint measurability of `imgChain` is assumed. -/
theorem measurable_eightHeightField_fixed {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
    {κ p δ q dd : ℝ} {H₁ H₂ : Set ℂ}
    (hp : A1SeedField.IsProtectedPair H₁ H₂ δ p q dd)
    {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
    {W₂ : ℝ≥0 → Y → ℝ} {S₁ : ℕ → X → ℝ≥0} {m : ℕ} {T : Y → ℝ≥0}
    {a : ℝ} {xL : Fin 1 → ℝ} {xR : Fin 2 → ℝ} {ρL : Fin 1 → ℝ} {ρR : Fin 2 → ℝ}
    {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (hP : ∀ x, IsIntegratedSLEPath a xL xR ρL ρR (W₁ · x)
      (fun i u => VL₁ i u x) (fun i u => VR₁ i u x) (B₁ · x) (ζ₁ x))
    (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    (hLife : ∀ x, (S₁ m x : ℝ≥0∞) < ζ₁ x) (hS : ∀ x, 0 < (S₁ m x : ℝ))
    (hL : ∀ x (u : ℝ≥0), 0 < u → u ≤ S₁ m x → VL₁ 0 u x ≠ W₁ u x)
    (hR : ∀ x (u : ℝ≥0), 0 < u → u ≤ S₁ m x → VR₁ 0 u x ≠ W₁ u x)
    (hK₁ : ∀ x, fwdHull (eightDrv W₁ S₁ m x) (S₁ m x) ⊆ H₁)
    (hK₂ : ∀ y, fwdHull (frzPath W₂ p (T y) y) (T y) ⊆ H₂)
    (hStop₁ : IsStoppingTime 𝓕₁ fun x => (S₁ m x : WithTop ℝ≥0))
    (hStop₂ : IsStoppingTime 𝓕₂ fun y => (T y : WithTop ℝ≥0))
    (B₂ : ℝ≥0 → Y → ℝ) (hB₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂)
    (hBc : ∀ y, Continuous (B₂ · y)) (hB0 : ∀ y, B₂ 0 y = 0)
    (hW₂ : W₂ = fun u y => Real.sqrt κ * B₂ u y)
    {t₀ : ℝ} {y₀ : Y} {B D : ℝ≥0 → X → ℝ}
    (hcol : IsColumnStoch 𝓕₁ P₁ (A2X.kh κ)
      (fun x => eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t₀ (x, y₀)) (S₁ m) B D)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Measurable ({ω : X × Y | s ≤ S₁ m ω.1 ∧ t ≤ T ω.2}.indicator fun ω =>
      seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) ω s t) := by
  let V : Y → ℝ → ℝ := fun y => frzPath W₂ p (T y) y
  let G : Set (X × Y) := {ω | s ≤ S₁ m ω.1 ∧ t ≤ T ω.2}
  have hG : MeasurableSet G :=
    (measurableSet_le measurable_const
      ((measurable_coe_of_isStoppingTime hStop₁).comp measurable_fst)).inter
    (measurableSet_le measurable_const
      ((measurable_coe_of_isStoppingTime hStop₂).comp measurable_snd))
  obtain ⟨hWm, hZm, hV₀m, hG₀m⟩ := eight_source_inputs_measurable hcol
  have hWc : ∀ x, Continuous (eightDrv W₁ S₁ m x) := fun x =>
    continuous_eightDrv (S₁ := S₁) (m := m) (hP x).2.2.2.1 (hLife x)
  have hW0 : ∀ x, eightDrv W₁ S₁ m x 0 = 0 := fun x => eightDrv_zero (hP x).1
  have hVeq : ∀ y, V y = seedStoppedDriver (Real.sqrt κ) p B₂ T y := by
    intro y
    simp only [V, hW₂, seedStoppedDriver_eq_frzPath]
  have hVc : ∀ y, Continuous (V y) := by
    intro y
    rw [hVeq y]
    exact continuous_seedStoppedDriver hBc _ _ _ y
  have hVm : ∀ u : ℝ≥0, Measurable fun y => V y u := by
    intro u
    have hd := measurable_seedStoppedDrift hB₂.2.1 hBc hStop₂ (Real.sqrt κ) u
    have he : (fun y => V y u) = fun y =>
        Real.sqrt κ * B₂ u y + seedStoppedDrift (Real.sqrt κ) B₂ T u y + p := by
      funext y
      rw [hVeq y]
      simp only [seedStoppedDriver, seedStoppedDrift, Real.toNNReal_coe]
      ring
    rw [he]
    exact (((measurable_const.mul (hB₂.2.1 u)).add hd).add_const p).mono (𝓕₂.le u) le_rfl
  have hVn : ∀ y u, V y u = V y (u.toNNReal : ℝ) := by
    intro y u
    rw [hVeq y]
    simp only [seedStoppedDriver, Real.toNNReal_coe]
  have hV0 : ∀ y, V y 0 = p := by
    intro y
    exact frzPath_zero (by simp only [hW₂, hB0 y, mul_zero]) (T y).coe_nonneg
  have hKt : ∀ ω ∈ G, fwdHull (V ω.2) t ⊆ H₂ := fun ω hω =>
    (QuantumZipper.fwdHull_mono.1 hω.2).trans (hK₂ ω.2)
  have ho : ∀ ω ∈ G, OwnData (eightDrv W₁ S₁ m ω.1) (fwdHull (V ω.2) t)
      (frzChart (V ω.2) t) (S₁ m ω.1)
      (seedSrcClock (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (V ω.2) t)
      (seedSrcDriver (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (V ω.2) t) := fun ω hω =>
    seedSrcOwn_of_enclosures (hWc ω.1) (hW0 ω.1) (hS ω.1) (hVc ω.2) ht
      hp.sep_pos hp.sep (hK₁ ω.1) (hKt ω hω)
  have hv : ∀ ω ∈ G, ∃ v, IsForwardSol
      (seedSrcDriver (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (V ω.2) t)
      (V ω.2 t) (seedSrcClock (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (V ω.2) t (S₁ m ω.1)) v := by
    intro ω hω
    refine (ho ω hω).tip_alive_of_enclosures hp.hull₁ hp.hull₂ hp.sep_pos hp.sep
      (hVc ω.2) ht ?_ ?_ (hK₁ ω.1) (hKt ω hω)
    · rw [hW0 ω.1, hV0 ω.2]
      exact ne_of_lt (hp.prot_pos.trans hp.prot_lt)
    · rw [hV0 ω.2]
      exact hp.src
  obtain ⟨r, hr, hclear⟩ := exists_seed_clearance_of_enclosures hp.hull₁ hp.hull₂ hp.sep_pos hp.sep
  have hm : ∀ u ∈ Icc (0 : ℝ) s, Measurable (G.indicator fun ω =>
      (srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (V ω.2) t
        (A2X.kh κ) (eightRR κ) p (eightMarks VL₁ VR₁ ω.1)).normEll u) := by
    intro u hu
    have hsub : ∀ ω ∈ G, u.toNNReal ≤ S₁ m ω.1 := fun ω hω =>
      Real.toNNReal_le_iff_le_coe.2 (hu.2.trans hω.1)
    have hcu : (u.toNNReal : ℝ) = u := Real.coe_toNNReal _ hu.1
    refine measurable_srcRec_normEll_pair (W := eightDrv W₁ S₁ m) (V := V)
      (T := fun x => (S₁ m x : ℝ)) (Z := eightMarks VL₁ VR₁) (G := G) (s := u) (t := t)
      (A2X.kh κ) p (eightRR κ) hWc hVc hWm hVm
      (fun x v => (A1G3Calc.eightDrv_toNNReal W₁ S₁ m x v).symm) hVn hu.1 ht hG ho
      (fun ω hω => hu.2.trans hω.1) hv ?_ ?_ ?_ ?_
    · intro ω hω k
      have heq := eightDrv_eqOn W₁ S₁ m ω.1
      have hlo := A1SeedField.isSeedCoordinate_vL_of_path (hP ω.1) 0 hxL (hLife ω.1) (hL ω.1) heq
      have hhi := A1SeedField.isSeedCoordinate_vR_of_path (hP ω.1) 0 hxR (hLife ω.1) (hR ω.1) heq
      have hc := hclear _ _ _ _ (hWc ω.1)
        (closure_mono (hK₁ ω.1) (start_mem_closure_fwdHull (hWc ω.1) (hS ω.1)))
        (hK₁ ω.1) hlo hhi u ⟨hu.1, hu.2.trans hω.1⟩ _ (A1SeedField.seedPair_marks _ _ u k)
      exact ⟨r, hr, hc.mono_right (Set.image_mono (hKt ω hω))⟩
    · intro k
      simpa only [hcu] using measurable_mask_prod_fst (hZm u.toNNReal k) hG hsub
    · simpa only [hcu] using measurable_mask_prod_fst (hV₀m u.toNNReal) hG hsub
    · simpa only [hcu] using measurable_mask_prod_fst (hG₀m u.toNNReal) hG hsub
  have hc₂ : ∀ y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc (0 : ℝ) (T y)) := by
    intro y
    rw [hW₂]
    exact (continuous_const.mul ((hBc y).comp continuous_real_toNNReal)).continuousOn
  change Measurable (G.indicator fun ω =>
    seedHeightField (eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m) ω s t)
  convert (Real.measurable_exp.comp ((hm s ⟨hs, le_rfl⟩).sub (hm 0 ⟨le_rfl, hs⟩))).indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Function.comp_apply, Pi.sub_apply, seedHeightField]
    have he := srcRec_stopped_frozen_eq (eightDrv W₁ S₁ m ω.1) (Strip.extPath (W₂ · ω.2))
      (S₁ m ω.1) (A2X.kh κ) p (eightRR κ) (eightMarks VL₁ VR₁ ω.1) (hc₂ ω.2) ht hω.2
    change eightRec κ p W₁ VL₁ VR₁ W₂ S₁ m t ω =
      srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (V ω.2) t
        (A2X.kh κ) (eightRR κ) p (eightMarks VL₁ VR₁ ω.1) at he
    rw [he]
  · simp only [indicator_of_notMem hω]

end InteractingSLE.ZhanGT4
