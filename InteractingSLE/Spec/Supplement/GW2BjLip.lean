/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.MartingaleFinalImage

/-!
# Stability of the regularized real Loewner flow in the driver (near facts, piece 1)

Packet PROVE-GW2-BUF (round 7; the image-state measurability needed by the near stops, decision D12 pending). The
image state `GW2Sdg.imgState` is built from GB6's real flow (`MartChar.RealFlow`), whose values are positive solutions
chosen by `Classical.choice`. Its measurability in the path goes through the regularized flow `regFlow w ε y`, the
solution of a Lipschitz ODE. Gronwall (`dist_le_of_approx_trajectories_ODE`) gives:

* `gronwallBound_zero_le`: `gronwallBound 0 K (K δ) t ≤ δ e^{K t}`;
* **`abs_lipUnc_sub_le`**: two drivers `δ`-close on `[0, T]` give `lipUnc` solutions `δ e^{K t}`-close;
* **`abs_regFlow_sub_le`**: the regularized flow from `y` at level `ε` is `δ (1 + e^{(2/ε²) t})`-close.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open OneForce MartChar.RealFlow

/-- The Gronwall bound from equal starts with error `K δ`. -/
theorem gronwallBound_zero_le {K : ℝ≥0} {δ t : ℝ} (hδ : 0 ≤ δ) :
    gronwallBound 0 K (K * δ) t ≤ δ * Real.exp (K * t) := by
  by_cases hK : (K : ℝ) = 0
  · rw [hK, gronwallBound_K0]
    simp only [zero_mul, zero_add, Real.exp_zero, mul_one]
    exact hδ
  · rw [gronwallBound_of_K_ne_0 hK]
    simp only [zero_mul, zero_add]
    rw [mul_div_cancel_left₀ _ hK]
    have h1 : 0 ≤ Real.exp (K * t) := (Real.exp_pos _).le
    nlinarith

/-- **Two close drivers give close `lipUnc` solutions.** -/
theorem abs_lipUnc_sub_le {f : ℝ → ℝ} {K : ℝ≥0} {M : ℝ} (hf : LipschitzWith K f) (hM : ∀ y, |f y| ≤ M)
    {w w' : ℝ → ℝ} (hw : Continuous w) (hw' : Continuous w') {T δ : ℝ} (hT : 0 ≤ T) (hδ0 : 0 ≤ δ)
    (hδ : ∀ t ∈ Icc 0 T, |w t - w' t| ≤ δ) (x : ℝ) :
    ∀ t ∈ Icc 0 T, |lipUnc f x w t - lipUnc f x w' t| ≤ δ * Real.exp (K * t) := by
  have h : LipData f w := ⟨⟨K, hf⟩, ⟨M, hM⟩, hw⟩
  have h' : LipData f w' := ⟨⟨K, hf⟩, ⟨M, hM⟩, hw'⟩
  have hd := lipUnc_hasDerivWithinAt h hT x
  have hd' := lipUnc_hasDerivWithinAt h' hT x
  have key := dist_le_of_approx_trajectories_ODE (v := fun t y => f (y + w t)) (K := K)
    (f := lipUnc f x w) (g := lipUnc f x w') (f' := fun t => f (lipSol f x w t))
    (g' := fun t => f (lipSol f x w' t)) (a := 0) (b := T) (εf := 0) (εg := K * δ) (δ := 0)
    (fun t => lipschitzWith_shift hf (w t))
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => Bessel.hasDerivWithinAt_Ici_of_Icc (hd t (Ico_subset_Icc_self ht)) ht)
    (fun t _ => by simp only [lipSol, dist_self, le_refl])
    (fun t ht => (hd' t ht).continuousWithinAt)
    (fun t ht => Bessel.hasDerivWithinAt_Ici_of_Icc (hd' t (Ico_subset_Icc_self ht)) ht)
    (fun t ht => by
      have h1 := hf.dist_le_mul (lipSol f x w' t) (lipUnc f x w' t + w t)
      have h2 : dist (lipSol f x w' t) (lipUnc f x w' t + w t) = |w t - w' t| := by
        rw [Real.dist_eq, lipSol, abs_sub_comm]
        congr 1
        ring
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hδ t (Ico_subset_Icc_self ht)) K.2))
    (by rw [lipUnc_zero h, lipUnc_zero h', dist_self])
  intro t ht
  have h3 := key t ht
  rw [zero_add, sub_zero, Real.dist_eq] at h3
  exact h3.trans (gronwallBound_zero_le hδ0)

/-- **The regularized flow is stable in the driver.** -/
theorem abs_regFlow_sub_le {w w' : ℝ → ℝ} (hw : Continuous w) (hw' : Continuous w') {ε : ℝ} (hε : 0 < ε)
    {T δ : ℝ} (hT : 0 ≤ T) (hδ0 : 0 ≤ δ) (hδ : ∀ t ∈ Icc 0 T, |w t - w' t| ≤ δ) (y : ℝ) :
    ∀ t ∈ Icc 0 T, |regFlow w ε y t - regFlow w' ε y t| ≤
      δ * (1 + Real.exp ((2 / ε ^ 2).toNNReal * t)) := by
  intro t ht
  have hδ' : ∀ t ∈ Icc 0 T, |(fun s => -w s) t - (fun s => -w' s) t| ≤ δ := fun s hs => by
    simp only
    rw [show -w s - -w' s = -(w s - w' s) by ring, abs_neg]
    exact hδ s hs
  have h1 := abs_lipUnc_sub_le (Bessel.lipschitzWith_regDrift zero_le_two hε)
    (Bessel.abs_regDrift_le zero_le_two hε) hw.neg hw'.neg hT hδ0 hδ' y t ht
  have he : regFlow w ε y t - regFlow w' ε y t =
      (lipUnc (Bessel.regDrift 2 ε) y (fun s => -w s) t - lipUnc (Bessel.regDrift 2 ε) y (fun s => -w' s) t) -
        (w t - w' t) := by
    simp only [regFlow, lipSol]
    ring
  rw [he]
  have h2 := abs_sub (lipUnc (Bessel.regDrift 2 ε) y (fun s => -w s) t -
    lipUnc (Bessel.regDrift 2 ε) y (fun s => -w' s) t) (w t - w' t)
  have h3 := hδ t ht
  exact h2.trans ((add_le_add h1 h3).trans (le_of_eq (by ring)))

end InteractingSLE.Theorem14.GW2Bh
