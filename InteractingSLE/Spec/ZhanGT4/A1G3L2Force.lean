/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2Ident

/-!
# Zhan's A.1 under R83: the canonical forces are the force coordinates of the seeded geometry

Packet PROVE-A1-G3LAW2 (identification step, generic). At one sample, for an image chain `(a, W')` of a driver agreeing
with the image curve's driver up to a good horizon `S` (`A1G3L2Ident`), and a seeded image geometry `(w, vL, vR)` on
`[0, T]`, `T ≤ a(S)`, whose driver is `W' − W'(0)`:

* **`canonForce_eq_of_geometry_right`/`_left`**: the canonical force (A1-FORCES's `canonForce`) of the frozen-chart
  point `xR j + W'(0) + xj` (a non-seed force point) is `vR j` on `[0, T]`;
* **`canonSeed_eq_of_geometry_right`/`_left`**: the canonical seed forces (A1-LARGEDENS's `canonSeed`) are the
  geometry's seed coordinates on `[0, T]`;
* **`cImgDrv_eq_of_geometry`**: the centred canonical image driver is `w` on `[0, T]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Core

section Canon

variable {Ω : Type*} {L : Set Ω} {xj xk : ℝ} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞} {wk : Ω → ℝ≥0 → ℝ}
  {τ : Ω → ℝ≥0} {ω : Ω} {S : ℝ} {W W' a : ℝ → ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}

/-- A forward solution of `W'` from `z` is one of `W' + c` from `z + c`. -/
theorem isForwardSol_add_const {V : ℝ → ℝ} {z : ℝ} {R : ℝ} {u : ℝ → ℂ} (h : IsForwardSol V (z : ℂ) R u) (c : ℝ) :
    IsForwardSol (fun s => V s + c) ((z + c : ℝ) : ℂ) R u :=
  ⟨h.1, fun s hs => ⟨(h.2 s hs).1, by rw [(h.2 s hs).2]; push_cast; ring⟩⟩

variable
  (hown : OwnData W (physHull (xk - xj) (Strip.extPath (wk ω)) (τ ω))
    (physMap (xk - xj) (Strip.extPath (wk ω)) (τ ω)) S a W')
  (hWj : EqOn W (Strip.extPath (wj ω)) (Icc 0 S))
  (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T))
  (hj0 : Strip.extPath (wj ω) 0 = 0)
  (hk : ∃ τ', ((τ ω : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ'))
  (hk0 : Strip.extPath (wk ω) 0 = 0)
  (hgood : A1Ref.IsGoodTime xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) S)
  (hgeo : SeedImageGeometry xL xR ρL ρR w vL vR T) (hTa : (T : ℝ) ≤ a S)
  (hw : ∀ s : ℝ≥0, s ≤ T → w s = W' s - W' 0)

include hown hWj hj hj0 hk hk0 hgood hTa

/-- The canonical image driver is `W' + xj` on `[0, T]`. -/
theorem imgDrv_eq_of_le (r : ℝ) (hr0 : 0 ≤ r) (hrT : r ≤ T) :
    A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) r = W' r + xj :=
  (imgClk_imgDrv_eqOn_of_ownData hown hWj hj hj0 hk hk0 (τ ω).coe_nonneg hgood).2 ⟨hr0, hrT.trans hTa⟩

/-- Times up to `T` are before the canonical image lifetime. -/
theorem ofReal_lt_imgLife_of_le {t : ℝ≥0} (htT : t ≤ T) :
    ENNReal.ofReal t < A1Ref.imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) :=
  (ENNReal.ofReal_le_ofReal ((NNReal.coe_le_coe.2 htT).trans hTa)).trans_lt
    (ofReal_lt_imgLife_of_ownData hown hWj hj hj0 hk hk0 (τ ω).coe_nonneg hgood)

include hw

/-- **The centred canonical image driver is the geometry's driver on `[0, T]`.** -/
theorem imgDrv_sub_eq_of_geometry {t : ℝ≥0} (htT : t ≤ T) :
    A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) t -
      A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0 = w t := by
  rw [imgDrv_eq_of_le hown hWj hj hj0 hk hk0 hgood hTa t t.coe_nonneg htT,
    imgDrv_eq_of_le hown hWj hj hj0 hk hk0 hgood hTa 0 le_rfl T.coe_nonneg, hw t htT]
  ring

/-- The driver relation `imgDrv s = w s + imgDrv 0` on `[0, t]`, `t ≤ T` (A1-LARGEDENS's `hI`). -/
theorem imgDrv_eq_add_of_geometry {t : ℝ≥0} (htT : t ≤ T) :
    ∀ s ∈ Icc (0 : ℝ) t, A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) s =
      w s.toNNReal + A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0 := by
  intro s hs
  have hsT : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hs.2).trans htT
  rw [imgDrv_eq_of_le hown hWj hj hj0 hk hk0 hgood hTa s hs.1 (hs.2.trans (NNReal.coe_le_coe.2 htT)),
    imgDrv_eq_of_le hown hWj hj hj0 hk hk0 hgood hTa 0 le_rfl T.coe_nonneg, hw _ hsT, Real.coe_toNNReal _ hs.1]
  ring

include hgeo

/-- **The canonical force of a non-seed right frozen-chart point is the geometry's force coordinate** on `[0, T]`. -/
theorem canonForce_eq_of_geometry_right (hω : ω ∈ L) {p : Ω → ℝ} (j : Fin nR) (hxj : xR j ≠ 0)
    (hp : p ω = xR j + W' 0 + xj) {t : ℝ≥0} (htT : t ≤ T) :
    A1Forces.canonForce L xj xk wj ζj wk τ p t ω = vR j t := by
  have hU := QuantumZipper.isForwardSol_restrict (isForwardSol_of_geometry_right hgeo j hxj hw) t.coe_nonneg
    (NNReal.coe_le_coe.2 htT)
  have hU' := isForwardSol_add_const hU xj
  have hv : IsForwardSol (A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
      (p ω : ℂ) t (fun s => ((vR j s.toNNReal - w s.toNNReal : ℝ) : ℂ)) := by
    rw [hp]
    exact QuantumZipper.isForwardSol_congr_drive (fun r hr =>
      (imgDrv_eq_of_le hown hWj hj hj0 hk hk0 hgood hTa r hr.1 (hr.2.trans (NNReal.coe_le_coe.2 htT))).symm) hU'
  rw [A1Forces.canonForce_eq_imgForce hω hj hj0 hk hk0
    (ofReal_lt_imgLife_of_le hown hWj hj hj0 hk hk0 hgood hTa htT) hv, A1MultiMark.imgForce,
    QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨t.coe_nonneg, le_rfl⟩, ofReal_re, Real.toNNReal_coe,
    add_sub_assoc, imgDrv_sub_eq_of_geometry hown hWj hj hj0 hk hk0 hgood hTa hw htT]
  ring

/-- **The canonical force of a non-seed left frozen-chart point is the geometry's force coordinate** on `[0, T]`. -/
theorem canonForce_eq_of_geometry_left (hω : ω ∈ L) {p : Ω → ℝ} (i : Fin nL) (hxi : xL i ≠ 0)
    (hp : p ω = xL i + W' 0 + xj) {t : ℝ≥0} (htT : t ≤ T) :
    A1Forces.canonForce L xj xk wj ζj wk τ p t ω = vL i t := by
  have hU := QuantumZipper.isForwardSol_restrict (isForwardSol_of_geometry_left hgeo i hxi hw) t.coe_nonneg
    (NNReal.coe_le_coe.2 htT)
  have hU' := isForwardSol_add_const hU xj
  have hv : IsForwardSol (A1Ref.imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
      (p ω : ℂ) t (fun s => ((vL i s.toNNReal - w s.toNNReal : ℝ) : ℂ)) := by
    rw [hp]
    exact QuantumZipper.isForwardSol_congr_drive (fun r hr =>
      (imgDrv_eq_of_le hown hWj hj hj0 hk hk0 hgood hTa r hr.1 (hr.2.trans (NNReal.coe_le_coe.2 htT))).symm) hU'
  rw [A1Forces.canonForce_eq_imgForce hω hj hj0 hk hk0
    (ofReal_lt_imgLife_of_le hown hWj hj hj0 hk hk0 hgood hTa htT) hv, A1MultiMark.imgForce,
    QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨t.coe_nonneg, le_rfl⟩, ofReal_re, Real.toNNReal_coe,
    add_sub_assoc, imgDrv_sub_eq_of_geometry hown hWj hj hj0 hk hk0 hgood hTa hw htT]
  ring

/-- **The canonical right seed force is the geometry's seed coordinate** on `[0, T]`. -/
theorem canonSeed_eq_of_geometry_right (hω : ω ∈ L) (j : Fin nR) (hxj : xR j = 0) {t : ℝ≥0} (htT : t ≤ T) :
    A1LargeDens.canonSeed L xj xk wj ζj wk τ 1 t ω = vR j t :=
  A1LargeDens.canonSeed_right_eq_of_geometry hω hj hj0 hk hk0
    (ofReal_lt_imgLife_of_le hown hWj hj hj0 hk hk0 hgood hTa htT) hgeo j hxj htT
    (imgDrv_eq_add_of_geometry hown hWj hj hj0 hk hk0 hgood hTa hw htT)

/-- **The canonical left seed force is the geometry's seed coordinate** on `[0, T]`. -/
theorem canonSeed_eq_of_geometry_left (hω : ω ∈ L) (i : Fin nL) (hxi : xL i = 0) {t : ℝ≥0} (htT : t ≤ T) :
    A1LargeDens.canonSeed L xj xk wj ζj wk τ (-1) t ω = vL i t :=
  A1LargeDens.canonSeed_left_eq_of_geometry hω hj hj0 hk hk0
    (ofReal_lt_imgLife_of_le hown hWj hj hj0 hk hk0 hgood hTa htT) hgeo i hxi htT
    (imgDrv_eq_add_of_geometry hown hWj hj hj0 hk hk0 hgood hTa hw htT)

end Canon

end InteractingSLE.ZhanGT4.A1G3L2
