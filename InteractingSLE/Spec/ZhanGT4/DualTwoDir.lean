/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD6
import InteractingSLE.Spec.ZhanGT4.DualD12

/-!
# The patched density from the two directions

Packet PROVE-ZHAN-GT4-A15. Source: Astra, *Follow-up proofs*, §A.1.4 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L357–L407, R38): "Thus `M*(s, t̄)` is a bounded martingale. Reflection of the construction proves the corresponding
martingale in the other coordinate."

A14 built the column product in the `s`-direction from the `s`-view density `frzDens` (curve `2` frozen). The other
direction uses the same construction in the `t`-view (curve `1` frozen, coordinates translated by `−c`). This file
proves that **the two directions patch the same function**: the (D11) patch `M*` of the `s`-view normalised density
over the staircase of rectangles `[0, S₁ i] × [0, S₂ i]` equals the patch of the `t`-view normalised density over the
transposed staircase (`patch_twoView`), because the two normalised densities agree on every rectangle
(`TwoViewRect.normLog_eq`, DualD6) and the patch only evaluates the density on the staircase (`patchLog_congr`).

## Main results

* `patchLog_congr`: `patchLog` depends only on the values of `m` on the staircase (closed quadrant).
* `frzN_eq_sView`: A14's density `frzN` is `exp` of the `s`-view `ell` (`DualD6.sView`).
* `patchLog_twoView`, `patch_twoView`.
-/

set_option autoImplicit false

noncomputable section

open Finset Set

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-! ### `patchLog` only sees the staircase -/

section Congr

variable {ι : Type*} [Fintype ι] {S₁ S₂ : ι → ℝ}

/-- **`patchLog` only evaluates `m` on the staircase**: if `m = m'` at every point of the closed quadrant lying in
some rectangle `[0, S₁ i] × [0, S₂ i]`, the patched logarithms agree at every `s, t ≥ 0`. -/
theorem patchLog_congr (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) {m m' : ℝ → ℝ → ℝ}
    (h : ∀ x y, 0 ≤ x → 0 ≤ y → InStair S₁ S₂ x y → m x y = m' x y) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    patchLog S₁ S₂ m s t = patchLog S₁ S₂ m' s t := by
  unfold patchLog
  refine sum_congr rfl fun c hc => ?_
  have hc0 := nonneg_of_mem_stairCols hS₁ hc
  obtain ⟨h1, h2⟩ := inStair_args (S₁ := S₁) hS₂ hc hc0 s t
  rw [h _ _ (le_min hc0 hs) (le_min (stairH_nonneg c) ht) h1,
    h _ _ (le_min (prevIn_nonneg _ _) hs) (le_min (stairH_nonneg c) ht) h2]

/-- **The two directions patch the same function** (log form): if the `s`-direction log-density `m₁` and the
`t`-direction one `m₂` (with its arguments in the order (curve-`2` time, curve-`1` time)) agree on the staircase and
both vanish on the axes, the `s`-patch at `(s, t)` equals the transposed `t`-patch at `(t, s)`. -/
theorem patchLog_twoView (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) {m₁ m₂ : ℝ → ℝ → ℝ}
    (h0 : ∀ y, m₁ 0 y = 0) (h0' : ∀ x, m₁ x 0 = 0)
    (h : ∀ x y, 0 ≤ x → 0 ≤ y → InStair S₁ S₂ x y → m₁ x y = m₂ y x) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    patchLog S₁ S₂ m₁ s t = patchLog S₂ S₁ m₂ t s := by
  rw [patchLog_symm hS₁ hS₂ h0 h0' hs ht]
  refine patchLog_congr hS₂ hS₁ (fun y x hy hx hyx => ?_) ht hs
  obtain ⟨i, h1, h2⟩ := hyx
  exact h x y hx hy ⟨i, h2, h1⟩

end Congr

/-! ### A14's density is the `s`-view `ell` -/

section Frz

variable {Ω : Type*} {n : ℕ}

open scoped NNReal

/-- `frzDataOf` with the image data of height `y` is the `s`-view at height `y` (definitional). -/
theorem frzDataOf_eq_sView (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W₂ : ℝ → ℝ) (Wsy asy : ℝ → Ω → ℝ → ℝ) (rr p : Fin n → ℝ)
    (ω : Ω) (y : ℝ) :
    frzDataOf κ B (Wsy y) (asy y) (frzChart W₂ y) rr (W₂ y) (frzMarks W₂ p y) ω =
      sView κ rr (QuantumZipper.drive κ B ω) W₂ (fun y => asy y ω) (fun y => Wsy y ω) p y := rfl

/-- **A14's density `frzN` (with the chart, tip and marks of the frozen curve) is `exp ℓ` of the `s`-view.** -/
theorem frzN_eq_sView (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W₂ : ℝ → ℝ) (Wsy asy : ℝ → Ω → ℝ → ℝ) (rr p : Fin n → ℝ)
    (ω : Ω) (x y : ℝ) :
    frzN κ B Wsy asy (frzChart W₂) rr W₂ (frzMarks W₂ p) ω x y =
      Real.exp ((sView κ rr (QuantumZipper.drive κ B ω) W₂ (fun y => asy y ω) (fun y => Wsy y ω) p y).ell x
        (QuantumZipper.drive κ B ω x)) := rfl

end Frz

/-! ### The two-view patch identity on a staircase of rectangles -/

/-- **Aliveness of the marks on a rectangle** (the mark hypotheses of `TwoViewRect.normLog_eq`): every mark is alive
for both curves on the rectangle and for both image chains at every time of the rectangle. -/
structure TwoViewMarks {n : ℕ} (W₁ W₂ : ℝ → ℝ) (X Y : ℝ) (as Ws bt Wt : ℝ → ℝ → ℝ) (p : Fin n → ℝ) : Prop where
  alive₁ : ∀ m, ∃ w, IsForwardSol W₁ ((p m : ℝ) : ℂ) X w
  alive₂ : ∀ m, ∃ w, IsForwardSol W₂ ((p m : ℝ) : ℂ) Y w
  aliveS : ∀ v ∈ Icc (0 : ℝ) Y, ∀ u ∈ Icc (0 : ℝ) X, ∀ m, ∃ w,
    IsForwardSol (Ws v) ((frzMarks W₂ p v m : ℝ) : ℂ) (as v u) w
  aliveT : ∀ u ∈ Icc (0 : ℝ) X, ∀ v ∈ Icc (0 : ℝ) Y, ∀ m, ∃ w,
    IsForwardSol (Wt u) ((frzMarks (fun s => W₁ s - W₂ 0) (fun m => p m - W₂ 0) u m : ℝ) : ℂ) (bt u v) w

/-- The `s`-view `log M̃(x, y)` (curve `1` at time `x`, curve `2`'s hull of height `y` frozen). -/
def sEll {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ) (as Ws : ℝ → ℝ → ℝ) (p : Fin n → ℝ) (x y : ℝ) : ℝ :=
  (sView κ r W₁ W₂ as Ws p y).ell x (W₁ x)

/-- The `t`-view `log M̃(x, y)` (curve `2` at time `y`, curve `1`'s hull of height `x` frozen; translated). -/
def tEll {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ) (bt Wt : ℝ → ℝ → ℝ) (p : Fin n → ℝ) (x y : ℝ) : ℝ :=
  (tView κ r W₁ W₂ bt Wt p x).ell y (W₂ y - W₂ 0)

section Staircase

variable {ι : Type*} [Fintype ι] {S₁ S₂ : ι → ℝ} {n : ℕ} {κ : ℝ} {r p : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ}
  {as Ws bt Wt : ℝ → ℝ → ℝ}

omit [Fintype ι] in
/-- **(D6) on a staircase**: the `s`-view and `t`-view normalised log-densities agree at every point of every
rectangle. -/
theorem normLog_sEll_eq_tEll (hκ : κ ≠ 0) (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (hR : ∀ i, TwoViewRect W₁ W₂ (S₁ i) (S₂ i) as Ws bt Wt) (hM : ∀ i, TwoViewMarks W₁ W₂ (S₁ i) (S₂ i) as Ws bt Wt p)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : InStair S₁ S₂ x y) :
    normLog (sEll κ r W₁ W₂ as Ws p) x y = normLog (tEll κ r W₁ W₂ bt Wt p) x y := by
  obtain ⟨i, hxi, hyi⟩ := hxy
  exact (hR i).normLog_eq hκ r p hW₁ hW₂ (hM i).alive₁ (hM i).alive₂ (hM i).aliveS (hM i).aliveT
    ⟨hx, hxi⟩ ⟨hy, hyi⟩

/-- **The two directions patch the same function** ((D11) "Reflection of the construction proves the corresponding
martingale in the other coordinate"): the `s`-direction patch of `M_s = exp(normLog ℓ_s)` at `(s, t)` equals the
`t`-direction patch (transposed staircase) of `M_t = exp(normLog ℓ_t)` at `(t, s)`. -/
theorem patch_twoView (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) (hκ : κ ≠ 0) (hW₁ : Continuous W₁)
    (hW₂ : Continuous W₂) (hR : ∀ i, TwoViewRect W₁ W₂ (S₁ i) (S₂ i) as Ws bt Wt)
    (hM : ∀ i, TwoViewMarks W₁ W₂ (S₁ i) (S₂ i) as Ws bt Wt p) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    patch S₁ S₂ (fun x y => Real.exp (normLog (sEll κ r W₁ W₂ as Ws p) x y)) s t =
      patch S₂ S₁ (fun y x => Real.exp (normLog (tEll κ r W₁ W₂ bt Wt p) x y)) t s := by
  unfold patch
  simp only [Real.log_exp]
  congr 1
  refine patchLog_twoView hS₁ hS₂ (fun y => normLog_zero_left _ y) (fun x => normLog_zero_right _ x)
    (fun x y hx hy hxy => ?_) hs ht
  exact normLog_sEll_eq_tEll hκ hW₁ hW₂ hR hM hx hy hxy

end Staircase

end InteractingSLE.ZhanGT4
