/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTwoDirMart

/-!
# Continuity of the normalised density in the frozen height

Packet PROVE-ZHAN-GT4-A15 (A14's "What remains" 2, first step). The `s`-view of A14 freezes curve `2` at a height `y`
and chooses image data per height, so continuity of its density in `y` is not visible in that view. By the (D6)
agreement (`TwoViewRect.normLog_eq`) the normalised density equals the `t`-view one, in which `y` is the own time of the
growing curve; there `ℓ` is continuous along the driver (`FrzData.continuousOn_ell_driver`). Hence the `s`-view
normalised density is continuous in the frozen height (`TwoViewRect.continuousOn_normLog_sEll_height`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- **`ℓ = log M̃` is continuous along the driver** on the whole horizon of a frozen configuration (other tip and marks
alive, marks distinct from each other and from the other tip). -/
theorem FrzData.continuousOn_ell_driver {n : ℕ} (d : FrzData n) {A : Set ℂ} {T : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') {v₀ : ℝ → ℂ} (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀) {v : Fin n → ℝ → ℂ}
    (hv : ∀ m, IsForwardSol d.W' (d.ζ m) (d.a T) (v m)) (hζ₀ : ∀ m, d.ζ m ≠ d.ζ₀) (hζ : Function.Injective d.ζ) :
    ContinuousOn (fun t => d.ell t (d.W t)) (Icc 0 T) := by
  have hLT := d.continuousOn_LT h hv₀ hv hζ₀ hζ
  have hLS : ContinuousOn (fun t => d.LS t (d.W t)) (Icc 0 T) := by
    unfold FrzData.LS
    refine continuousOn_dualLogSpace (h.continuousOn_frzA 0) (h.continuousOn_frzA 1)
      (d.continuousOn_A20 h hv₀) (fun m => d.continuousOn_B0 h hv m) (fun t ht => (h.frzA_one_pos ht).ne')
      (fun t ht => ?_) (fun t ht m => ?_)
    · have := h.frzImg_sub_ne_zero hv₀ ht
      intro h0; apply this
      show frzImg d.W' d.a d.ζ₀ t - frzA d.W d.W' d.a d.φ 0 t = 0
      have : frzA d.W d.W' d.a d.φ 0 t - d.A20 t = 0 := h0
      simp only [FrzData.A20] at this; linarith
    · have := h.frzImg_sub_ne_zero (hv m) ht
      intro h0; apply this
      have : frzA d.W d.W' d.a d.φ 0 t - d.B0 t m = 0 := h0
      simp only [FrzData.B0] at this; linarith
  exact hLT.add hLS

namespace TwoViewRect

variable {n : ℕ} {W₁ W₂ : ℝ → ℝ} {X Y : ℝ} {as Ws bt Wt : ℝ → ℝ → ℝ} (h : TwoViewRect W₁ W₂ X Y as Ws bt Wt)
include h

/-- The `t`-view `ℓ` at curve-`1` height `u` is continuous in the curve-`2` time on `[0, Y]`. -/
theorem continuousOn_tEll {κ : ℝ} (r p : Fin n → ℝ) (hY : 0 < Y)
    (hM : TwoViewMarks W₁ W₂ X Y as Ws bt Wt p)
    (hne : ∀ u ∈ Icc (0 : ℝ) X, ∀ m, frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u m ≠ W₁ u - W₂ 0)
    (hinj : ∀ u ∈ Icc (0 : ℝ) X, Function.Injective (frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u))
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) X) : ContinuousOn (fun y => tEll κ r W₁ W₂ bt Wt p u y) (Icc 0 Y) := by
  obtain ⟨T, hYT, ht, w, hw⟩ := h.tOwn u hu
  have ht' := ht.restrict hY hYT
  have hbY := ht.toImgData.mapsTo_clock_Icc ⟨hY.le, hYT⟩
  have hv₀ := Ito.isForwardSol_of_le hw hbY.1 hbY.2
  have hmk : ∀ m, ∃ x, IsForwardSol (Wt u) ((frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u m : ℝ) : ℂ)
      (bt u Y) x := fun m => hM.aliveT u hu Y ⟨hY.le, le_rfl⟩ m
  choose v hv using hmk
  exact (tView κ r W₁ W₂ bt Wt p u).continuousOn_ell_driver ht' hv₀ hv (hne u hu) (hinj u hu)

/-- **Continuity of the `s`-view normalised density in the frozen height** (A14's "What remains" 2, first step): by the
(D6) agreement it is the `t`-view one, in which the height is the own time of the growing curve. -/
theorem continuousOn_normLog_sEll_height {κ : ℝ} (hκ : κ ≠ 0) (r p : Fin n → ℝ) (hW₁ : Continuous W₁)
    (hW₂ : Continuous W₂) (hY : 0 < Y) (hM : TwoViewMarks W₁ W₂ X Y as Ws bt Wt p)
    (hne : ∀ u ∈ Icc (0 : ℝ) X, ∀ m, frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u m ≠ W₁ u - W₂ 0)
    (hinj : ∀ u ∈ Icc (0 : ℝ) X, Function.Injective (frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) X) :
    ContinuousOn (fun y => normLog (sEll κ r W₁ W₂ as Ws p) x y) (Icc 0 Y) := by
  have h0X : (0 : ℝ) ∈ Icc (0 : ℝ) X := ⟨le_rfl, h.nonneg_X⟩
  have hc : ContinuousOn (fun y => normLog (tEll κ r W₁ W₂ bt Wt p) x y) (Icc 0 Y) := by
    unfold normLog
    exact (((h.continuousOn_tEll r p hY hM hne hinj hx).sub continuousOn_const).sub
      (h.continuousOn_tEll r p hY hM hne hinj h0X)).add continuousOn_const
  refine hc.congr fun y hy => ?_
  exact h.normLog_eq hκ r p hW₁ hW₂ hM.alive₁ hM.alive₂ hM.aliveS hM.aliveT hx hy

end TwoViewRect

end InteractingSLE.ZhanGT4
