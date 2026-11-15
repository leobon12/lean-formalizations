/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RefReg
import InteractingSLE.Spec.ZhanGT4.A1DualStatement
import InteractingSLE.Spec.Ito.FiltrationBasic

/-!
# A.1 on one reference space: the canonical statements and their reduction to A1DUAL's Ref statements

Packet PROVE-ZHAN-A1REF. Source: Astra, *Follow-up proofs*, §A.1 L160–L189 (R38); follow-up 4 §2.5 (R71); rulings
R70 (the image law at usual-augmentation stopping times) and R48.

`A1Dual.A1DualCouplingG3RefStatement κ` (resp. `…EightRefStatement`) asks for one standard Borel probability space
carrying the two marginal evolutions and A2X's two conditional image laws (`IsA2DualPairG3`). By `A1RefCond` and
`A1RefReg` the geometric half of each conditional image law (the image chain, its clock, its lifetime, the image
source) is pathwise and canonical, and the needed regularity follows from the marginal paths. What remains is the law
content only:

* `A1DualCouplingG3CanonStatement κ` / `A1DualCouplingEightCanonStatement κ`: one standard Borel probability space with
  the two marginal evolutions (filtrations `𝓕₂`, `𝓕₁`) and the two **canonical** conditional image laws
  (`IsCanonImageLaw`) at every stopping time of the **usual augmentations** `usualAugmentation 𝓕ₖ μ` (R70);
* `A1DualCouplingG3RefUAStatement κ` / `…EightRefUAStatement κ`: A1DUAL's Ref statement with filtrations equal to their
  own usual augmentations (so A2X's image laws hold at usual-augmentation stopping times, R70).

## Main results

* `chainReg_G3_small`, `chainReg_G3_large`, `chainReg_eight_small`, `chainReg_eight_large`: `ChainReg` for the four
  directions from the marginal paths (the image sources `V_y`, `y + V₀`, `V_x`, `x + V₀` are the boundary values of
  `g_τ`; the small curve's last right mark does not meet its driver before the lifetime, by the threshold rule);
* **`isA2DualPairG3_of_canon`**, **`isA2DualPairEight_of_canon`**: marginals and canonical image laws give A2X's pair;
* **`a1DualCouplingG3RefUAStatement_of_canon`**, **`a1DualCouplingEightRefUAStatement_of_canon`**, and the Ref
  statements `a1DualCouplingG3RefStatement_of_canon`, `a1DualCouplingEightRefStatement_of_canon` (hence, by A1DUAL,
  A.1 over every given large curve and A.2/A.3: `a1DualCouplingG3VerStatement_of_canon`, …).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A1Ref

open QuantumZipper (H)
open A2X

/-! ### Small facts -/

/-- The strip life of a mark ends no later than the lifetime. -/
theorem lifeEnd_le (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : lifeEnd w v ζ ≤ ζ := by
  rcases eq_or_ne ζ ⊤ with h | h
  · rw [h]; exact le_top
  · have hn : ¬ Strip.IsStripLife w v ζ ζ.toNNReal := fun hs => by
      have := hs.1
      rw [ENNReal.coe_toNNReal h] at this
      exact lt_irrefl _ this
    calc lifeEnd w v ζ ≤ (ζ.toNNReal : ℝ≥0∞) := by unfold lifeEnd; exact iInf₂_le ζ.toNNReal hn
      _ = ζ := ENNReal.coe_toNNReal h

/-- **The usual augmentation is idempotent.** -/
theorem usualAugmentation_idem {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) :
    usualAugmentation (usualAugmentation 𝓕 P) P = usualAugmentation 𝓕 P := by
  rw [Ito.usualAugmentation_eq_rightCont (usualAugmentation 𝓕 P), Ito.nullAugmented_usualAugmentation,
    Ito.usualAugmentation_eq_rightCont, Filtration.rightCont_self]

/-! ### `ChainReg` in the four directions -/

section Reg

variable {Ω : Type*} {κ y x : ℝ}

/-- **(G3), small given large**: `ChainReg` for the small curve from `y` at stops of the large curve inside the strip
life of `V_x`, image source `V_y`. -/
theorem chainReg_G3_small {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞} {ω : Ω}
    (h₂ : IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] (fun t => W₂ t ω) (fun i t => VL₂ i t ω)
      (fun i t => VR₂ i t ω) (fun t => B₂ t ω) (ζ₂ ω))
    (h₁ : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (fun t => W₁ t ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (fun t => B₁ t ω) (ζ₁ ω)) :
    ChainReg (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0 W₂ (fun t ω => VL₂ 1 t ω) ω := by
  have p₂ := h₂.isSLEPathUpTo le_rfl
  have p₁ := h₁.isSLEPathUpTo le_rfl
  refine chainReg_of_paths p₁.continuousOn_w le_rfl p₁.w_zero p₂.continuousOn_w p₂.w_zero (fun t ht => ht.1)
    fun t ht => ?_
  have hveq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₂ ω → VL₂ 1 s ω =
      y + ∫ r in (0 : ℝ)..s, 2 / (VL₂ 1 r.toNNReal ω - W₂ r.toNNReal ω) := fun s hs => by
    simpa using p₂.vL_eq hs 1
  have hsep : ∀ r ≤ t, VL₂ 1 r ω ≠ W₂ r ω := fun r hr => by
    have hr' : (r : ℝ≥0∞) < ζ₂ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht.1
    have h01 : VL₂ 1 r ω ≤ VL₂ 0 r ω := p₂.antitone_vL hr' (show (0 : Fin 2) ≤ 1 by decide)
    exact (h01.trans_lt (ht.2 r hr)).ne
  have := tendsto_physMap_of_force p₂.continuousOn_w p₂.w_zero (p₂.continuousOn_vL 1) hveq ht.1 hsep 0
  simpa using this

/-- The threshold rule excludes a total right collision of weight `−2` before the lifetime. -/
theorem ne_of_threshold_right {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (p : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ) (hρ : ∑ i, ρR i ≤ -2) (j : Fin nR)
    (hj : ∀ i, i ≤ j) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < ζ) : vR j r ≠ w r := by
  intro heq
  have hall : ∀ i, vR i r = w r := fun i =>
    le_antisymm (heq ▸ p.monotone_vR hr (hj i)) (p.w_le_vR hr i)
  refine p.not_threshold hr (Or.inr ?_)
  rw [Finset.filter_true_of_mem fun i _ => hall i]
  exact hρ

/-- **(G3), large given small**: `ChainReg` for the large curve from `0` (lifetime capped at the end of the strip life
of `V_x`) at stops of the small curve before its lifetime, image source `y + V₀`. -/
theorem chainReg_G3_large {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞} {ω : Ω}
    (h₂ : IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] (fun t => W₂ t ω) (fun i t => VL₂ i t ω)
      (fun i t => VR₂ i t ω) (fun t => B₂ t ω) (ζ₂ ω))
    (h₁ : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (fun t => W₁ t ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (fun t => B₁ t ω) (ζ₁ ω)) :
    ChainReg (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
      (fun t ω => y + VR₁ 2 t ω) ω := by
  have p₂ := h₂.isSLEPathUpTo le_rfl
  have p₁ := h₁.isSLEPathUpTo le_rfl
  refine chainReg_of_paths p₂.continuousOn_w (lifeEnd_le _ _ _) p₂.w_zero p₁.continuousOn_w p₁.w_zero
    (fun t ht => ht) fun t ht => ?_
  have hveq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → VR₁ 2 s ω =
      -y + ∫ r in (0 : ℝ)..s, 2 / (VR₁ 2 r.toNNReal ω - W₁ r.toNNReal ω) := fun s hs => by
    simpa using p₁.vR_eq hs 2
  have hρ : ∑ i, smallG3RhoR κ i ≤ -2 := by
    simp only [smallG3RhoR, Fin.sum_univ_three]; simp; ring_nf; rfl
  have hsep : ∀ r ≤ t, VR₁ 2 r ω ≠ W₁ r ω := fun r hr => by
    have hr' : (r : ℝ≥0∞) < ζ₁ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht
    exact ne_of_threshold_right p₁ hρ 2 (fun i => Fin.le_last i) hr'
  have := tendsto_physMap_of_force p₁.continuousOn_w p₁.w_zero (p₁.continuousOn_vR 2) hveq ht hsep y
  simpa using this

/-- **(Eight), small given large**: `ChainReg` for the small curve from `x` at stops of the large curve inside the
strip life of `V_x`, image source `V_x`. -/
theorem chainReg_eight_small {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞} {ω : Ω}
    (h₂ : IsIntegratedSLEPath κ ![x] ![] ![0] ![] (fun t => W₂ t ω) (fun i t => VL₂ i t ω)
      (fun i t => VR₂ i t ω) (fun t => B₂ t ω) (ζ₂ ω))
    (h₁ : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) (fun t => W₁ t ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (fun t => B₁ t ω) (ζ₁ ω)) :
    ChainReg (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0 W₂ (fun t ω => VL₂ 0 t ω) ω := by
  have p₂ := h₂.isSLEPathUpTo le_rfl
  have p₁ := h₁.isSLEPathUpTo le_rfl
  refine chainReg_of_paths p₁.continuousOn_w le_rfl p₁.w_zero p₂.continuousOn_w p₂.w_zero (fun t ht => ht.1)
    fun t ht => ?_
  have hveq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₂ ω → VL₂ 0 s ω =
      x + ∫ r in (0 : ℝ)..s, 2 / (VL₂ 0 r.toNNReal ω - W₂ r.toNNReal ω) := fun s hs => by
    simpa using p₂.vL_eq hs 0
  have hsep : ∀ r ≤ t, VL₂ 0 r ω ≠ W₂ r ω := fun r hr => (ht.2 r hr).ne
  have := tendsto_physMap_of_force p₂.continuousOn_w p₂.w_zero (p₂.continuousOn_vL 0) hveq ht.1 hsep 0
  simpa using this

/-- **(Eight), large given small**: `ChainReg` for the large curve from `0` (lifetime capped at the end of the strip
life of `V_x`) at stops of the small curve before its lifetime, image source `x + V₀`. -/
theorem chainReg_eight_large {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞} {ω : Ω}
    (h₂ : IsIntegratedSLEPath κ ![x] ![] ![0] ![] (fun t => W₂ t ω) (fun i t => VL₂ i t ω)
      (fun i t => VR₂ i t ω) (fun t => B₂ t ω) (ζ₂ ω))
    (h₁ : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) (fun t => W₁ t ω)
      (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (fun t => B₁ t ω) (ζ₁ ω)) :
    ChainReg (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
      (fun t ω => x + VR₁ 1 t ω) ω := by
  have p₂ := h₂.isSLEPathUpTo le_rfl
  have p₁ := h₁.isSLEPathUpTo le_rfl
  refine chainReg_of_paths p₂.continuousOn_w (lifeEnd_le _ _ _) p₂.w_zero p₁.continuousOn_w p₁.w_zero
    (fun t ht => ht) fun t ht => ?_
  have hveq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → VR₁ 1 s ω =
      -x + ∫ r in (0 : ℝ)..s, 2 / (VR₁ 1 r.toNNReal ω - W₁ r.toNNReal ω) := fun s hs => by
    simpa using p₁.vR_eq hs 1
  have hρ : ∑ i, smallEightRhoR κ i ≤ -2 := by
    simp only [smallEightRhoR, Fin.sum_univ_two]; simp
  have hsep : ∀ r ≤ t, VR₁ 1 r ω ≠ W₁ r ω := fun r hr => by
    have hr' : (r : ℝ≥0∞) < ζ₁ ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht
    exact ne_of_threshold_right p₁ hρ 1 (fun i => Fin.le_last i) hr'
  have := tendsto_physMap_of_force p₁.continuousOn_w p₁.w_zero (p₁.continuousOn_vR 1) hveq ht hsep x
  simpa using this

end Reg

/-! ### The pair from the marginals and the canonical image laws -/

section Pair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {κ y x : ℝ} {P : Measure Ω}

/-- **A2X's (G3) pair from the two marginals and the two canonical conditional image laws.** -/
theorem isA2DualPairG3_of_canon {𝓕₂ : Filtration ℝ≥0 mΩ} {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ} {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {𝓕₁ : Filtration ℝ≥0 mΩ}
    {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ} {VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ}
    {ζ₁ : Ω → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕₁ W₁ VL₁
      VR₁ B₁ ζ₁)
    (hc₁ : IsCanonImageLaw (kh κ) P 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0 W₂
      (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
      (smallG3RhoR κ))
    (hc₂ : IsCanonImageLaw κ P 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
      (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
      (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]) :
    IsA2DualPairG3 κ y x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ := by
  refine ⟨h₂, h₁, isCondImageLaw_of_canon ?_ hc₁, isCondImageLaw_of_canon ?_ hc₂⟩
  · filter_upwards [h₂.2.2.2.2, h₁.2.2.2.2] with ω p₂ p₁
    exact chainReg_G3_small p₂ p₁
  · filter_upwards [h₂.2.2.2.2, h₁.2.2.2.2] with ω p₂ p₁
    exact chainReg_G3_large p₂ p₁

/-- **A2X's (Eight) pair from the two marginals and the two canonical conditional image laws.** -/
theorem isA2DualPairEight_of_canon {𝓕₂ : Filtration ℝ≥0 mΩ} {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ} {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {𝓕₁ : Filtration ℝ≥0 mΩ}
    {W₁ : ℝ≥0 → Ω → ℝ} {VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ} {VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ} {B₁ : ℝ≥0 → Ω → ℝ}
    {ζ₁ : Ω → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕₁ W₁ VL₁ VR₁
      B₁ ζ₁)
    (hc₁ : IsCanonImageLaw (kh κ) P 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0 W₂
      (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ))
    (hc₂ : IsCanonImageLaw κ P 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
      (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
      (fun _ _ => ![]) (largeEightImgRhoL κ) ![]) :
    IsA2DualPairEight κ x P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ := by
  refine ⟨h₂, h₁, isCondImageLaw_of_canon ?_ hc₁, isCondImageLaw_of_canon ?_ hc₂⟩
  · filter_upwards [h₂.2.2.2.2, h₁.2.2.2.2] with ω p₂ p₁
    exact chainReg_eight_small p₂ p₁
  · filter_upwards [h₂.2.2.2.2, h₁.2.2.2.2] with ω p₂ p₁
    exact chainReg_eight_large p₂ p₁

end Pair

/-! ### The canonical statements (R70) and the reductions -/

/-- **A.1 (G3) on one reference space, canonical form** (R70): one standard Borel probability space with the two
marginal evolutions (large `SLE_κ(κ − 4, −4)` from `(0; x, y)` in `𝓕₂`; small `SLE_{κ̂}` from `y` in `𝓕₁`) and the two
canonical conditional image laws at every stopping time of the usual augmentations. -/
def A1DualCouplingG3CanonStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) μ 𝓕₁ W₁ VL₁ VR₁ B₁
        ζ₁ ∧
      IsCanonImageLaw (kh κ) μ (usualAugmentation 𝓕₂ μ)
        (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0 W₂ (fun _ _ => ![0])
        (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ) (smallG3RhoR κ) ∧
      IsCanonImageLaw κ μ (usualAugmentation 𝓕₁ μ) (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
        (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
        (fun _ _ => ![]) (largeG3ImgRhoL κ) ![]

/-- **A.1 (Eight) on one reference space, canonical form** (R70). -/
def A1DualCouplingEightCanonStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) μ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
      IsCanonImageLaw (kh κ) μ (usualAugmentation 𝓕₂ μ)
        (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0 W₂ (fun _ _ => ![0])
        (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) ∧
      IsCanonImageLaw κ μ (usualAugmentation 𝓕₁ μ) (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
        (fun _ _ => ![]) (largeEightImgRhoL κ) ![]

/-- **A1DUAL's (G3) Ref statement with usual-augmentation filtrations** (R70): the dual pair on one standard Borel
space whose two filtrations equal their usual augmentations, so A2X's image laws hold at every stopping time of the
usual augmentations. -/
def A1DualCouplingG3RefUAStatement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsA2DualPairG3 κ y x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
        usualAugmentation 𝓕₂ μ = 𝓕₂ ∧ usualAugmentation 𝓕₁ μ = 𝓕₁

/-- **A1DUAL's (Eight) Ref statement with usual-augmentation filtrations** (R70). -/
def A1DualCouplingEightRefUAStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (_ : StandardBorelSpace Ω₀) (μ : Measure Ω₀)
      (_ : IsProbabilityMeasure μ) (𝓕₂ 𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₀))
      (W₂ : ℝ≥0 → Ω₀ → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω₀ → ℝ) (B₂ : ℝ≥0 → Ω₀ → ℝ)
      (ζ₂ : Ω₀ → ℝ≥0∞) (W₁ : ℝ≥0 → Ω₀ → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω₀ → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω₀ → ℝ)
      (B₁ : ℝ≥0 → Ω₀ → ℝ) (ζ₁ : Ω₀ → ℝ≥0∞),
      IsA2DualPairEight κ x μ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
        usualAugmentation 𝓕₂ μ = 𝓕₂ ∧ usualAugmentation 𝓕₁ μ = 𝓕₁

/-- **The canonical (G3) statement gives the Ref statement with usual-augmentation filtrations.** -/
theorem a1DualCouplingG3RefUAStatement_of_canon {κ : ℝ} (h : A1DualCouplingG3CanonStatement κ) :
    A1DualCouplingG3RefUAStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hc₁, hc₂⟩ :=
    h hκ4 hκ8 y x hyx hx
  exact ⟨Ω₀, m₀, hsb, μ, hμ, usualAugmentation 𝓕₂ μ, usualAugmentation 𝓕₁ μ, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁,
    B₁, ζ₁, isA2DualPairG3_of_canon (Ito.isIntegratedSLEEvolution_usualAugmentation h₂)
      (Ito.isIntegratedSLEEvolution_usualAugmentation h₁) hc₁ hc₂,
    usualAugmentation_idem _ _, usualAugmentation_idem _ _⟩

/-- **The canonical (Eight) statement gives the Ref statement with usual-augmentation filtrations.** -/
theorem a1DualCouplingEightRefUAStatement_of_canon {κ : ℝ} (h : A1DualCouplingEightCanonStatement κ) :
    A1DualCouplingEightRefUAStatement κ := by
  intro hκ8 x hx
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, h₂, h₁, hc₁, hc₂⟩ :=
    h hκ8 x hx
  exact ⟨Ω₀, m₀, hsb, μ, hμ, usualAugmentation 𝓕₂ μ, usualAugmentation 𝓕₁ μ, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁,
    B₁, ζ₁, isA2DualPairEight_of_canon (Ito.isIntegratedSLEEvolution_usualAugmentation h₂)
      (Ito.isIntegratedSLEEvolution_usualAugmentation h₁) hc₁ hc₂,
    usualAugmentation_idem _ _, usualAugmentation_idem _ _⟩

theorem a1DualCouplingG3RefStatement_of_refUA {κ : ℝ} (h : A1DualCouplingG3RefUAStatement κ) :
    A1Dual.A1DualCouplingG3RefStatement κ := by
  intro hκ4 hκ8 y x hyx hx
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair, -, -⟩ :=
    h hκ4 hκ8 y x hyx hx
  exact ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩

theorem a1DualCouplingEightRefStatement_of_refUA {κ : ℝ} (h : A1DualCouplingEightRefUAStatement κ) :
    A1Dual.A1DualCouplingEightRefStatement κ := by
  intro hκ8 x hx
  obtain ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair, -, -⟩ := h hκ8 x hx
  exact ⟨Ω₀, m₀, hsb, μ, hμ, 𝓕₂, 𝓕₁, W₂, VL₂, VR₂, B₂, ζ₂, W₁, VL₁, VR₁, B₁, ζ₁, hpair⟩

/-- **A1DUAL's (G3) Ref statement from the canonical one.** -/
theorem a1DualCouplingG3RefStatement_of_canon {κ : ℝ} (h : A1DualCouplingG3CanonStatement κ) :
    A1Dual.A1DualCouplingG3RefStatement κ :=
  a1DualCouplingG3RefStatement_of_refUA (a1DualCouplingG3RefUAStatement_of_canon h)

/-- **A1DUAL's (Eight) Ref statement from the canonical one.** -/
theorem a1DualCouplingEightRefStatement_of_canon {κ : ℝ} (h : A1DualCouplingEightCanonStatement κ) :
    A1Dual.A1DualCouplingEightRefStatement κ :=
  a1DualCouplingEightRefStatement_of_refUA (a1DualCouplingEightRefUAStatement_of_canon h)

/-- **A.1 (G3) over every given large curve** (A1DUAL's version form) from the canonical statement. -/
theorem a1DualCouplingG3VerStatement_of_canon {κ : ℝ} (h : A1DualCouplingG3CanonStatement κ) :
    A1Dual.A1DualCouplingG3VerStatement.{u} κ :=
  A1Dual.a1DualCouplingG3VerStatement_of_ref (a1DualCouplingG3RefStatement_of_canon h)

/-- **A.1 (Eight) over every given large curve** from the canonical statement. -/
theorem a1DualCouplingEightVerStatement_of_canon {κ : ℝ} (h : A1DualCouplingEightCanonStatement κ) :
    A1Dual.A1DualCouplingEightVerStatement.{u} κ :=
  A1Dual.a1DualCouplingEightVerStatement_of_ref (a1DualCouplingEightRefStatement_of_canon h)

/-- **A.3 (the first-swallow crosscut) from the two canonical statements and A.2's three parts.** -/
theorem firstSwallowCrosscutStatement_of_canon {κ : ℝ} (hA1 : A1DualCouplingG3CanonStatement κ)
    (h1 : A2SmallCrosscutG3Statement.{0} κ) (h2 : A2HullInsideG3Statement.{0} κ)
    (h3 : A2SmallInHullG3Statement.{0} κ) (hA1' : A1DualCouplingEightCanonStatement κ)
    (h1' : A2SmallCrosscutEightStatement.{u} κ) (h2' : A2HullInsideEightStatement.{u} κ)
    (h3' : A2SmallInHullEightStatement.{u} κ) : FirstSwallowCrosscutStatement.{u} κ :=
  A1Dual.firstSwallowCrosscutStatement_of_ref (a1DualCouplingG3RefStatement_of_canon hA1) h1 h2 h3
    (a1DualCouplingEightRefStatement_of_canon hA1') h1' h2' h3'

end InteractingSLE.ZhanGT4.A1Ref
