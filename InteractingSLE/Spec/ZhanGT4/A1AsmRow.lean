/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmCol

/-!
# Zhan's A.1 (Eight): the stochastic half of the rows

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.6 (`ig1_followup_proofs.txt` L300–L500, the
row martingale of the large curve), follow-up 4 §2.5 (R71).

A1-EIGHTFIN's `IsRowStoch` (A1-EIGHTFIN "What remains" 3, A1-COMMON "What remains" 4) for the large Eight curve, which
is ordinary `SLE_κ` from the source `p` with one weight-`0` force point at relative position `x < 0` (the small curve's
start). With

* `B = B₂` (continuous at every sample),
* `D u = W₂(u ∧ S) − √κ B₂ u` (zero on `[0, S]`: the weight-`0` force point gives no drift),
* `V u = V_L(u ∧ S)` (the force point, stopped),

every clause holds once the stopped large path's hull stays in an `ℍ`-hull `E` that keeps a ball around `x` clear:
the identity `V = Re g_u(x) + W_u` on `[0, S]` is A1-SEEDFIELD's `fwdMap_add_eq_force` (through A1-COMMON's
`fwdMap_stopDrv_add_eq`), with the separation of `V_L` from the driver from A1-COMMON's deterministic
`protected_mark_bounds`.

* **`isRowStoch_large`**: `IsRowStoch` for the frozen large drivers of a stopping time `S < ζ₂` whose hull lies in `E`;
* **`isRowStoch_large_lifeExit`**: the same for the lifetime-capped exits of a protected enclosure family
  (`A1Common.IsEnclFamily`), in the exact form of the hypothesis `hrowst` of `seedFieldInputM_of_eight_rows`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (H fwdMap fwdHull)
open A2X A1EightSeed A1SeedField A1G3Calc A1Common A1EightFin

variable {Y : Type*} {mY : MeasurableSpace Y} {𝓕 : Filtration ℝ≥0 mY} {P : Measure Y} {κ x : ℝ}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
  {ζ₂ : Y → ℝ≥0∞}

/-- The frozen large driver relative to its source is the driver stopped at the frozen height. -/
theorem frzPath_sub_zero_eq {W : ℝ≥0 → Y → ℝ} {y : Y} (h0 : W 0 y = 0) (p T : ℝ) (hT : 0 ≤ T) :
    (fun u => frzPath W p T y u - frzPath W p T y 0) = A1Ref.stopDrv (Strip.extPath (W · y)) T := by
  funext u
  have h : A1Ref.stopDrv (Strip.extPath (W · y)) T 0 = 0 := by
    simp only [A1Ref.stopDrv, Strip.extPath, min_eq_left hT, max_self, Real.toNNReal_zero, h0]
  simp only [frzPath, h]
  ring

/-- **The stochastic half of the rows of the large Eight curve.** For the regular large marginal (ordinary `SLE_κ`
with a weight-`0` force point at `x ≠ 0`) whose Brownian paths are continuous at every sample, a stopping time `S`
before the lifetime whose hull lies in an `ℍ`-hull `E` with `0 ∈ closure E` and `ball x ρ ∩ E = ∅`, the frozen large
drivers relative to the source satisfy `IsRowStoch` at the protected point `x`. -/
theorem isRowStoch_large
    (h : A1Marg.IsRegMarginal κ ![x] ![] ![0] ![] P 𝓕 W₂ VL₂ VR₂ B₂ ζ₂) (hBc : ∀ y, Continuous (B₂ · y))
    (hx : x ≠ 0) {S : Y → ℝ≥0} (hS : IsStoppingTime 𝓕 fun y => (S y : WithTop ℝ≥0))
    (hSζ : ∀ y, (S y : ℝ≥0∞) < ζ₂ y) {E : Set ℂ} (hE : IsHPHull E) (h0E : (0 : ℂ) ∈ closure E) {ρ : ℝ}
    (hρ : 0 < ρ) (hxE : Disjoint (ball (x : ℂ) ρ) E) (hK : ∀ y, fwdHull (Strip.extPath (W₂ · y)) (S y) ⊆ E)
    (p : ℝ) :
    IsRowStoch 𝓕 P κ (fun y u => frzPath W₂ p (S y) y u - frzPath W₂ p (S y) y 0) S x B₂
      (fun u y => A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S y) u - Real.sqrt κ * B₂ u y)
      (fun y u => A1Ref.stopDrv (Strip.extPath (VL₂ 0 · y)) (S y) u) := by
  have hB := h.evol.1
  -- pathwise facts at every sample
  have hpath : ∀ y, ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (S y : ℝ)) := fun y =>
    A1Ref.continuousOn_extPath_Icc (h.path y).2.2.2.1 (by rw [ENNReal.ofReal_coe_nnreal]; exact hSζ y)
  have hWd : ∀ y, (fun u => frzPath W₂ p (S y) y u - frzPath W₂ p (S y) y 0) =
      A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S y) := fun y =>
    frzPath_sub_zero_eq (h.path y).1 p (S y) (S y).coe_nonneg
  have htoNN : ∀ y (t : ℝ), A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S y) (t.toNNReal : ℝ) =
      A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S y) t := fun y t =>
    eightDrv_toNNReal W₂ (fun _ _ => S y) 0 y t
  -- the drift part vanishes on `[0, S]`
  have hD0 : ∀ y, ∀ s ∈ Icc (0 : ℝ) (S y),
      A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S y) (s.toNNReal : ℝ) - Real.sqrt κ * B₂ s.toNNReal y = 0 := by
    intro y s hs
    have hs' : (s.toNNReal : ℝ) ∈ Icc (0 : ℝ) (S y) := by rw [Real.coe_toNNReal s hs.1]; exact hs
    rw [A1Ref.stopDrv_eqOn _ _ hs']
    have hlt : (s.toNNReal : ℝ≥0∞) < ζ₂ y :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) (hSζ y)
    have hw := (h.path y).2.2.2.2.2.2.2.2.2.2.2.2.1 s.toNNReal hlt
    simp only [Strip.extPath, Real.toNNReal_coe, Fin.sum_univ_one, Matrix.cons_val_zero, zero_div,
      intervalIntegral.integral_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hw ⊢
    rw [hw]
    ring
  refine ⟨hB, hBc, fun u => ?_, fun y => ?_, fun y => ?_, fun y t ht => ?_, fun u => ?_, fun y u hu => ?_⟩
  · exact (measurable_stopDrv_of_progressive h.progW hS u).sub (measurable_const.mul (hB.2.1 u))
  · exact ((A1Ref.continuous_stopDrv (hpath y) (S y).coe_nonneg).comp NNReal.continuous_coe).sub
      (continuous_const.mul (hBc y))
  · show (fun u => frzPath W₂ p (S y) y u - frzPath W₂ p (S y) y 0) = _
    rw [hWd y]
    funext t
    simp only [driftDriver]
    rw [htoNN y t]
    ring
  · refine (hasDerivWithinAt_const t (Icc (0 : ℝ) (S y)) (0 : ℝ)).congr (fun s hs => hD0 y s hs) (hD0 y t ht)
  · exact measurable_stopDrv_of_progressive (h.progVL 0) hS u
  · -- the source coordinate of the protected force point
    obtain ⟨hw0, -, -, hcw, hcvL, -, -, -, -, -, -, -, -, hvLeq, -⟩ := id (h.path y)
    have hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ y →
        VL₂ 0 t y = x + ∫ s in (0 : ℝ)..t, 2 / (VL₂ 0 s.toNNReal y - W₂ s.toNNReal y) := fun t ht => by
      simpa using hvLeq t ht 0
    obtain ⟨c, hc, hgap⟩ := protected_mark_bounds (h.path y) (hcvL 0) hveq hx hE h0E hρ hxE
    have hsep : ∀ r ≤ S y, VL₂ 0 r y ≠ W₂ r y := fun r hr hEq => by
      have : c ≤ |VL₂ 0 r y - W₂ r y| := (hgap (S y) (hSζ y) (hK y)).1 r hr
      rw [hEq, sub_self, abs_zero] at this
      linarith
    have hu' : u.toNNReal ≤ S y := Real.toNNReal_le_iff_le_coe.2 hu.2
    have hid := fwdMap_stopDrv_add_eq hcw (hcvL 0) hveq (hSζ y) hsep hu'
    rw [Real.coe_toNNReal u hu.1] at hid
    have hWdu : frzPath W₂ p (S y) y u - frzPath W₂ p (S y) y 0 =
        A1Ref.stopDrv (Strip.extPath (W₂ · y)) (S y) u := congrFun (hWd y) u
    show A1Ref.stopDrv (Strip.extPath (VL₂ 0 · y)) (S y) u =
      (fwdMap (fun u => frzPath W₂ p (S y) y u - frzPath W₂ p (S y) y 0) u x).re +
        (frzPath W₂ p (S y) y u - frzPath W₂ p (S y) y 0)
    rw [hWd y, hWdu, hid, A1Ref.stopDrv_eqOn _ _ hu]
    rfl

/-- **The rows of a protected enclosure family** (the hypothesis `hrowst` of `seedFieldInputM_of_eight_rows`, with
`x₀ = −p` and `ρ = δ`): for the large curve's lifetime-capped exits `S₂ m` from the members of a protected enclosure
family for the source `p = −x`, the frozen large drivers satisfy `IsRowStoch` at `−p`. -/
theorem isRowStoch_large_lifeExit [𝓕.IsRightContinuous] (hx : x < 0)
    (h : A1Marg.IsRegMarginal κ ![x] ![] ![0] ![] P 𝓕 W₂ VL₂ VR₂ B₂ ζ₂) (hBc : ∀ y, Continuous (B₂ · y))
    {H₁ H₂ : ℕ → Set ℂ} {δ q dd : ℕ → ℝ} {N : ℕ → ℝ≥0} {Tm : ℕ → ℝ} (hF : IsEnclFamily H₁ H₂ δ q dd (-x) N Tm)
    (hlt : ∀ m y, (lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m) : ℝ≥0∞) < ζ₂ y) (m : ℕ) :
    ∃ (B D : ℝ≥0 → Y → ℝ) (V : Y → ℝ → ℝ), IsRowStoch 𝓕 P κ
      (fun y u => frzPath W₂ (-x) (lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m)) y u -
        frzPath W₂ (-x) (lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m)) y 0)
      (fun y => lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m)) (-(-x)) B D V := by
  have hS := isStoppingTime_rect₂ (fun y => (h.path y).2.2.2.1) h.evol.2.1 (fun m => (hF.pp m).hull₂) N (-x) m
  have he : ∀ y, lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m) =
      lifeExit (W₂ · y) (ζ₂ y) (transl (-(-x)) (H₂ m)) (N m) := fun y => by
    rw [lifeExit_add_const, ← transl_neg_eq_preimage]
  have hK : ∀ y, fwdHull (Strip.extPath (W₂ · y)) (lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m)) ⊆
      transl (-(-x)) (H₂ m) := fun y => by
    rw [he y]
    exact fwdHull_lifeExit_subset (h.path y).2.2.2.1 (h.path y).1 (hF.hull₂ m) (by rw [← he y]; exact hlt m y)
  have hball := hF.disjoint_ball_neg_src m
  have e : ((-(-x) : ℝ) : ℂ) = (x : ℂ) := by simp
  rw [e] at hball
  refine ⟨B₂, fun u y => A1Ref.stopDrv (Strip.extPath (W₂ · y))
      (lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m)) u - Real.sqrt κ * B₂ u y,
    fun y u => A1Ref.stopDrv (Strip.extPath (VL₂ 0 · y)) (lifeExit (fun t => W₂ t y + -x) (ζ₂ y) (H₂ m) (N m)) u,
    ?_⟩
  rw [neg_neg]
  exact isRowStoch_large h hBc hx.ne hS (hlt m) (hF.hull₂ m) (hF.zero_mem_closure₂ m) (hF.pp m).sep_pos
    hball hK (-x)

end InteractingSLE.ZhanGT4.A1Asm
