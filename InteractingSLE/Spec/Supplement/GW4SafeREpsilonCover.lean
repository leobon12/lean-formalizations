/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeREpsilonWord
import InteractingSLE.Spec.Supplement.GW4SafeREpsilonRef
import InteractingSLE.Spec.Supplement.GW4SafeREpsilonBranch

/-!
# GW4: the actual cover outside the exposed seed interval

Every real coordinate strictly beyond the seed images is reached by a
surviving real characteristic. The physical exception set consists only
of the original height marks; all their incident fibers remain excluded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv logDerivFwd)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart Exist.StagedLaw Supp8.Q3Stop Sec7.PhaseSel Sec7.PocketTraversal
  Sec7.PocketStopSide Sec7.Aux119Heights LocalSets WholeField MartChar RealFlow

/-- The two real flow ranges cover the complement of the closed seed
interval. This constructs the characteristic, without an access hypothesis. -/
theorem exists_surviving_real_outside_seed_interval {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {t ξ : ℝ} (ht : 0 ≤ t)
    (hξ : ξ < -rightImg (fun s => -W s) 0 t - W t ∨
      rightImg W 0 t - W t < ξ) :
    ∃ (x : ℝ) (a : ℝ → ℂ), QuantumZipper.IsForwardSol W x t a ∧ (a t).re = ξ := by
  rcases hξ with hξ | hξ
  · obtain ⟨x, -, hx, hImg⟩ := FCAux79.exists_alive_gImg_eq hW.neg ht
      (show rightImg (fun s => -W s) 0 t < -ξ - W t by linarith)
    obtain ⟨a, ha, hat⟩ := FCAux79.exists_isForwardSol_of_alive hW.neg
      (by simp only [Pi.neg_apply, hW0, neg_zero]) ht hx
    refine ⟨-x, fun s => -a s, ?_, ?_⟩
    · simpa only [Pi.neg_apply, neg_neg, Complex.ofReal_neg] using
        QuantumZipper.RS.isForwardSol_neg ha
    · simp only [hat, Complex.neg_re, Complex.ofReal_re, Pi.neg_apply]
      linarith
  · obtain ⟨x, -, hx, hImg⟩ := FCAux79.exists_alive_gImg_eq hW ht
      (show rightImg W 0 t < ξ + W t by linarith)
    obtain ⟨a, ha, hat⟩ := FCAux79.exists_isForwardSol_of_alive hW hW0 ht hx
    refine ⟨x, a, ha, ?_⟩
    rw [hat, Complex.ofReal_re, hImg]
    ring

/-- All nonexposed component accesses, away from the original physical
marks and current force jumps, satisfy `ComponentRealAccess` outright. -/
theorem componentRealAccess_outside_seed_interval {Ω : Type*} {k : ℝ} (hk : 0 < k)
    {c₀ : BoundaryWord} {F : Frame} {X : Ω → DistOn upperHalfPlaneOpens}
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (d : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {ω : Ω}
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) {ξ : ℝ}
    (hJump : ξ ∉ componentLineJumps k c₀ F X Wd GT R V t ω)
    (hOutside : ξ ∉ Ioo
      (componentVL k c₀ X R V (componentSeedL k c₀)
        (lineClock F Wd GT V t ω).toNNReal ω - R (lineClock F Wd GT V t ω).toNNReal ω)
      (componentVR k c₀ X R V (componentSeedR k c₀)
        (lineClock F Wd GT V t ω).toNNReal ω - R (lineClock F Wd GT V t ω).toNNReal ω))
    (hPhysical : extendFrom H (componentLineChart F Wd GT R V t ω).2.1 (ξ : ℂ) ∉
      Complex.ofReal '' (c₀.jumps : Set ℝ)) :
    ComponentRealAccess k c₀ F X Wd GT R V d t ω ξ := by
  let q := (lineClock F Wd GT V t ω).toNNReal
  have hW : Continuous (wpath R ω) := hRc.comp continuous_real_toNNReal
  have hW0 : wpath R ω 0 = 0 := by simpa only [wpath, Real.toNNReal_zero] using hR0
  have hL : componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω =
      -rightImg (fun s => -wpath R ω s) 0 q - wpath R ω q := by
    have h0 : typedXL k (wordType k c₀) c₀ (componentSeedL k c₀) = 0 := by
      rw [typedXL_self_eq]
      exact Sec4.flowLineXL_zero _ _
    rw [componentVL_eq_geom k c₀ X R V hRc hR0]
    change -rightImg (fun s => -wpath R ω s)
      (-typedXL k (wordType k c₀) c₀ (componentSeedL k c₀)) q - R q ω = _
    rw [h0, neg_zero]
    simp only [wpath, Real.toNNReal_coe]
  have hR : componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω =
      rightImg (wpath R ω) 0 q - wpath R ω q := by
    have h0 : typedXR k (wordType k c₀) c₀ (componentSeedR k c₀) = 0 := by
      rw [typedXR_self_eq]
      exact Sec4.flowLineXR_zero _ _
    rw [componentVR_eq_geom k c₀ X R V hRc hR0]
    change rightImg (wpath R ω)
      (typedXR k (wordType k c₀) c₀ (componentSeedR k c₀)) q - R q ω = _
    rw [h0]
    simp only [wpath, Real.toNNReal_coe]
  have hNeL : ξ ≠ componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω :=
    fun he => hJump (Or.inr (Or.inl ⟨componentSeedL k c₀, he.symm⟩))
  have hNeR : ξ ≠ componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω :=
    fun he => hJump (Or.inr (Or.inr ⟨componentSeedR k c₀, he.symm⟩))
  have hSides : ξ < -rightImg (fun s => -wpath R ω s) 0 q - wpath R ω q ∨
      rightImg (wpath R ω) 0 q - wpath R ω q < ξ := by
    rw [← hL, ← hR]
    by_contra h
    push Not at h
    exact hOutside ⟨lt_of_le_of_ne h.1 hNeL.symm, lt_of_le_of_ne h.2 hNeR⟩
  obtain ⟨x, a, ha, hξ⟩ := exists_surviving_real_outside_seed_interval hW hW0 q.coe_nonneg hSides
  have hLanding : extendFrom H (componentLineChart F Wd GT R V t ω).2.1 (ξ : ℂ) = (x : ℂ) := by
    apply extendFrom_eq
    · rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact Sec7.Aux29Cor.real_mem_Hbar ξ
    · have h := tendsto_inverse_of_surviving_real hW hW0 q.coe_nonneg ha
      rw [hξ] at h
      exact h.mono_right nhdsWithin_le_nhds
  have hx : x ∉ c₀.jumps := fun hx =>
    hPhysical (hLanding ▸ mem_image_of_mem Complex.ofReal hx)
  rw [← hξ]
  exact componentRealAccess_of_surviving_real hk d t hRc hR0 hx ha (hξ ▸ hJump)

end InteractingSLE.Theorem14.GW4Fix
