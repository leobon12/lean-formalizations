/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Factors
import InteractingSLE.Spec.ZhanGT4.DualJointMeas
import InteractingSLE.Spec.ZhanGT4.DualSeedInstAccess

/-!
# Joint measurability of source records from measurable continuous drivers

PROVE-ZHAN-GT4-A22. The driving processes need not be Brownian. The existing
ODE/hull measurability results apply with parameter one to their nonnegative
time restrictions. In particular no measurability of `imgChain` is assumed.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (H fwdMap fwdHull drive IsForwardSol)

/-- Source records of two measurable continuous driver families have measurable
normalized logarithms on a protected event. Real source/seed measurability and
the geometric clearance and tip aliveness are the explicit local inputs. -/
theorem measurable_srcRec_normEll_pair {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (κ p : ℝ) (rr : Fin n → ℝ) {W : X → ℝ → ℝ} {V : Y → ℝ → ℝ}
    (hWc : ∀ x, Continuous (W x)) (hVc : ∀ y, Continuous (V y))
    (hWm : ∀ r : ℝ≥0, Measurable fun x => W x r)
    (hVm : ∀ r : ℝ≥0, Measurable fun y => V y r)
    (hWn : ∀ x u, W x u = W x (u.toNNReal : ℝ))
    (hVn : ∀ y u, V y u = V y (u.toNNReal : ℝ))
    {T : X → ℝ} {G : Set (X × Y)} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hG : MeasurableSet G) {Z : X → Fin n → ℝ → ℝ}
    (hown : ∀ ω ∈ G, OwnData (W ω.1) (fwdHull (V ω.2) t) (frzChart (V ω.2) t)
      (T ω.1) (seedSrcClock (W ω.1) (T ω.1) (V ω.2) t)
      (seedSrcDriver (W ω.1) (T ω.1) (V ω.2) t))
    (hmem : ∀ ω ∈ G, s ≤ T ω.1)
    (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (seedSrcDriver (W ω.1) (T ω.1) (V ω.2) t)
      (V ω.2 t) (seedSrcClock (W ω.1) (T ω.1) (V ω.2) t (T ω.1)) v)
    (hcl : ∀ ω ∈ G, ∀ m, ∃ ρ > 0,
      Disjoint (ball (Z ω.1 m s : ℂ) ρ) (imgHull (W ω.1) (fwdHull (V ω.2) t) s))
    (hZ : ∀ m, Measurable (G.indicator fun ω => Z ω.1 m s))
    (hV₀ : Measurable (G.indicator fun ω => (fwdMap (W ω.1) s p).re + W ω.1 s))
    (hG₀ : Measurable (G.indicator fun ω => (deriv (fwdMap (W ω.1) s) p).re)) :
    Measurable (G.indicator fun ω =>
      (A1EightSeed.srcRec (W ω.1) (T ω.1) (V ω.2) t κ rr p (Z ω.1)).normEll s) := by
  have hWD : (fun x => drive 1 (fun r x => W x r) x) = W := by
    funext x u
    simp only [drive, Real.sqrt_one, one_mul]
    exact (hWn x u).symm
  have hVD : (fun y => drive 1 (fun r y => V y r) y) = V := by
    funext y u
    simp only [drive, Real.sqrt_one, one_mul]
    exact (hVn y u).symm
  have hWcN : ∀ x, Continuous fun r : ℝ≥0 => W x r :=
    fun x => (hWc x).comp NNReal.continuous_coe
  have hVcN : ∀ y, Continuous fun r : ℝ≥0 => V y r :=
    fun y => (hVc y).comp NNReal.continuous_coe
  have hhit : ∀ L : Set ℂ, IsCompact L → L ⊆ H →
      MeasurableSet {y | (L ∩ fwdHull (V y) t).Nonempty} := by
    intro L hL hLH
    rw [← hVD]
    exact measurableSet_hit_drive hVcN ht (fun r _ => hVm r) hL hLH
  have hfwd : ∀ z ∈ H, Measurable fun y => fwdMap (V y) t z := by
    intro z hz
    rw [← hVD]
    exact measurable_fwdMap_drive_at hVcN hVm ht hz
  have hVt : Measurable fun y => V y t := by
    simp_rw [hVn _ t]
    exact hVm _
  have hM : ∀ u ∈ Icc (0 : ℝ) s,
      FrzMeasR (fun ω : X × Y => W ω.1)
        (fun ω => seedSrcDriver (W ω.1) (T ω.1) (V ω.2) t)
        (fun ω => seedSrcClock (W ω.1) (T ω.1) (V ω.2) t)
        (hull2 V t) (chart2 V t) (fun ω => T ω.1) G u := by
    intro u hu
    have ho : ∀ ω ∈ G, OwnData (drive 1 (fun r x => W x r) ω.1)
        (hull2 V t ω) (chart2 V t ω) (T ω.1)
        (seedSrcClock (W ω.1) (T ω.1) (V ω.2) t)
        (seedSrcDriver (W ω.1) (T ω.1) (V ω.2) t) := by
      intro ω hω
      rw [congrFun hWD ω.1, show chart2 V t ω = frzChart (V ω.2) t from rfl]
      exact hown ω hω
    have hm := frzMeasR_pair hWcN hu.1 (fun r _ => hWm r) hhit hG ho
      (fun ω hω => ⟨hu.1, hu.2.trans (hmem ω hω)⟩)
    simpa only [hWD] using hm
  exact measurable_seed_normEll_random_hull hs hM
    (markSeq_tip hhit hfwd hVt hVc ht hG) hv hcl (fun _ => rfl) (fun _ => rfl) hZ hV₀ hG₀

end InteractingSLE.ZhanGT4
