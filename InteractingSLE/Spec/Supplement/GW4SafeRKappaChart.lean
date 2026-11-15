/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaCollar

/-! # GW4: persistent seed collars in an arbitrary initial physical chart -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PocketStopSide MartChar.RealFlow

/-- An incident own collar and its transition pull back through any
conformal initial chart, with exactly zero inherited lift increment. -/
theorem own_collar_pullback {B : Chart} (hB : B.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {p q x ξ r : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hr : 0 < r)
    (hcol : (Chart.id.loewner W p).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((Chart.id.loewner W q).dom : Set ℂ))
    (htr : Tendsto (fun z => (Chart.id.loewner W p).1 ((Chart.id.loewner W q).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))) :
    (B.loewner W p).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ ((B.loewner W q).dom : Set ℂ) ∧
    Tendsto (fun z => (B.loewner W p).1 ((B.loewner W q).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
    Tendsto (fun z => (B.loewner W q).2.2 ((B.loewner W q).2.1 z) -
      (B.loewner W p).2.2 ((B.loewner W q).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hDom : ((Chart.id.loewner W q).dom : Set ℂ) = H \ fwdHull W q := by
    rw [(Chart.isConformal_id.loewner hW hW0 (hp.trans hpq)).coe_dom]
    exact QuantumZipper.RS.image_fwdMapInv_H hW hW0 (hp.trans hpq)
  have hcolB : (B.loewner W p).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ ((B.loewner W q).dom : Set ℂ) := by
    rw [dom_own_stage_as_initial_inverse_image hB hW hW0 (hp.trans hpq)]
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨fwdMapInv W p v, hDom ▸ hcol ⟨v, hv, rfl⟩, rfl⟩
  have htrB : Tendsto (fun z => (B.loewner W p).1 ((B.loewner W q).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) := by
    refine htr.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    change fwdMap W p (fwdMapInv W q z) = fwdMap W p (B.1 (B.2.1 (fwdMapInv W q z)))
    rw [hB.2.2 _ (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 (hp.trans hpq) hz)]
  exact ⟨hcolB, htrB, tendsto_own_stage_lift_sub_zero hB hW hW0 hp hpq hr hcolB htrB⟩

/-- One old seed coordinate and its incident collar survive a full
neighborhood of any positive current capacity in the physical chart. -/
theorem exists_persistent_seed_collar {B : Chart} (hB : B.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 < q) :
    ∃ p x : ℝ, 0 < p ∧ p < q ∧
      x ∈ Ioo (-rightImg (fun r => -W r) 0 p - W p) (rightImg W 0 p - W p) ∧
      ∀ᶠ u : ℝ in 𝓝 q, p < u ∧ ∃ ξ ∈ Ioo
        (-rightImg (fun r => -W r) 0 u - W u) (rightImg W 0 u - W u),
        ∃ r : ℝ, 0 < r ∧
          (B.loewner W p).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ ((B.loewner W u).dom : Set ℂ) ∧
          Tendsto (fun z => (B.loewner W p).1 ((B.loewner W u).2.1 z))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun z => (B.loewner W u).2.2 ((B.loewner W u).2.1 z) -
            (B.loewner W p).2.2 ((B.loewner W u).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨p, x, T, a, hp, hpq, hx, -, ha, hnear⟩ := exists_persistent_seed_characteristic hW hW0 hq
  refine ⟨p, x, hp, hpq, hx, ?_⟩
  filter_upwards [hnear] with u hu
  obtain ⟨r, hr, hcol, htr, -⟩ := exists_own_collar_of_restart_surviving_real hW hW0 hp.le hu.1.le
    (Aux25.isForwardSol_mono ha hu.2.1.le)
  exact ⟨hu.1, (a (u - p)).re, hu.2.2, r, hr,
    own_collar_pullback hB hW hW0 hp.le hu.1.le hr hcol htr⟩

end InteractingSLE.Theorem14.GW4Fix
