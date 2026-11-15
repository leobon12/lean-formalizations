/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomOrder
import InteractingSLE.Spec.ZhanGT4.A1MargStatement

/-!
# Zhan's A.1 (R80): the initial image words of the G3 and Eight configurations

Packet PROVE-A1-SEEDGEOM. `A1SeedGeom.seedImageGeometry_of_forces` needs, of the initial image word `(xL, xR)`, that it
is ordered (`IsOrderedForceWord`), has at most one entry at the driver's start on each side, and is not a threshold
state (the seed sums exceed `−2`): `IsSeedWord`. Here these conditions are proved for the four image words of A.1 (the
`ΘL`, `ΘR` of A1-LAW's `A1DualCoupling{G3,Eight}PatchStatement`), at every live frozen time of every sample of the
conditioning curve, from its pathwise integrated relation `IsIntegratedSLEPath` alone (A1-MARG's regular marginals
satisfy it at every sample):

* G3, small curve's image (`smallG3_isSeedWord`): `![0]`, `![0, VL₂0 − VL₂1, W₂ − VL₂1]` on the strip life of `VL₂ 0`;
* Eight, small curve's image (`smallEight_isSeedWord`): `![0]`, `![0, W₂ − VL₂0]` on the strip life of `VL₂ 0`;
* G3, large curve's image (`largeG3_isSeedWord`): `![VR₁1 − VR₁2, VR₁0 − VR₁2, W₁ − VR₁2, VL₁0 − VR₁2]`, `![]`
  before the small curve's lifetime;
* Eight, large curve's image (`largeEight_isSeedWord`): `![VR₁0 − VR₁1, W₁ − VR₁1, VL₁0 − VR₁1]`, `![]` likewise.

The strict separations come from the non-crossing of Loewner force points (`forceCoord_lt_of_lt_of_meet`, through
`vL_lt_vL_of_path`, `vR_lt_vR_of_path`) and from the threshold: the outermost mark of a side whose total weight is
`≤ −2` never reaches the driver before the lifetime (`vR_last_ne_of_path`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1SeedGeom

open Sec2 A2X

/-! ### Admissible initial words -/

/-- **An admissible initial image word** for `seedImageGeometry_of_forces`: ordered, at most one entry at `0` per side,
and not a threshold state. -/
def IsSeedWord {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  IsOrderedForceWord xL xR ∧ (∀ i i', xL i = xL i' → xL i = 0 → i = i') ∧
    (∀ j j', xR j = xR j' → xR j = 0 → j = j') ∧ ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR

/-- **`SeedImageGeometry` from the force equations and the sides, for an admissible initial word.** -/
theorem seedImageGeometry_of_isSeedWord {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}
    (hword : IsSeedWord xL xR ρL ρR) (hw0 : w 0 = 0) (hL0 : ∀ i, vL i 0 = xL i) (hR0 : ∀ j, vR j 0 = xR j)
    (hw : Continuous w) (hvL : ∀ i, Continuous (vL i)) (hvR : ∀ j, Continuous (vR j))
    (hintL : ∀ t ≤ T, ∀ i,
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t)
    (hintR : ∀ t ≤ T, ∀ j,
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹) volume 0 t)
    (heqL : ∀ t ≤ T, ∀ i, vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal))
    (heqR : ∀ t ≤ T, ∀ j, vR j t = xR j + ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal))
    (hltL : ∀ t, 0 < t → t ≤ T → ∀ i, vL i t < w t) (hgtR : ∀ t, 0 < t → t ≤ T → ∀ j, w t < vR j t) :
    SeedImageGeometry xL xR ρL ρR w vL vR T := by
  obtain ⟨⟨hordL, hxL, hordR, hxR⟩, hsL, hsR, hthr⟩ := hword
  obtain ⟨hseedL, hseedR⟩ := (not_thr_iff_seedSum xL xR ρL ρR).1 hthr
  exact seedImageGeometry_of_forces hw0 hL0 hR0 hw hvL hvR hintL hintR heqL heqR hltL hgtR hxL hxR hordL hordR
    hsL hsR hseedL hseedR

/-! ### Force points of a pathwise integrated evolution -/

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- Continuity of a path on `[0, ζ)` read in real time on `[0, T]`, `T < ζ`. -/
theorem continuousOn_real_of_lt {f : ℝ≥0 → ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ}) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) : ContinuousOn (fun s : ℝ => f s.toNNReal) (Icc 0 T) :=
  Strip.continuousOn_extPath hf hT

/-- **Two left force points of a pathwise integrated evolution keep their strict order** up to `T < ζ`, provided they
never meet on the driver. -/
theorem vL_lt_vL_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {i i' : Fin nL}
    (hx : xL i' < xL i) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ)
    (hmeet : ∀ r : ℝ≥0, 0 < r → r ≤ T → vL i' r = vL i r → vL i' r ≠ w r) : vL i' T < vL i T := by
  obtain ⟨-, hL0, -, hcw, hcL, -, -, -, -, -, hiL, -, -, hLeq, -⟩ := hP
  have hTle {t : ℝ≥0} (ht : t ≤ T) : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hT
  have hr (k : Fin nL) := forceCoord_real (T := T) (w := w) (hL0 k) (fun t ht => hiL t (hTle ht) k)
    (fun t ht => hLeq t (hTle ht) k)
  have h := forceCoord_lt_of_lt_of_meet (continuousOn_real_of_lt hcw hT) (continuousOn_real_of_lt (hcL i') hT)
    (continuousOn_real_of_lt (hcL i) hT)
    (fun s hs hm => hmeet s.toNNReal (Real.toNNReal_pos.2 hs.1) (Real.toNNReal_le_iff_le_coe.2 hs.2) hm)
    (hr i').1 (hr i').2 (hr i).1 (hr i).2 (by rw [Real.toNNReal_zero, hL0, hL0]; exact hx) T ⟨T.coe_nonneg, le_rfl⟩
  simpa only [Real.toNNReal_coe] using h

/-- **Two right force points of a pathwise integrated evolution keep their strict order** up to `T < ζ`, provided
they never meet on the driver. -/
theorem vR_lt_vR_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {j j' : Fin nR}
    (hx : xR j < xR j') {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ)
    (hmeet : ∀ r : ℝ≥0, 0 < r → r ≤ T → vR j r = vR j' r → vR j r ≠ w r) : vR j T < vR j' T := by
  obtain ⟨-, -, hR0, hcw, -, hcR, -, -, -, -, -, hiR, -, -, hReq, -⟩ := hP
  have hTle {t : ℝ≥0} (ht : t ≤ T) : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hT
  have hr (k : Fin nR) := forceCoord_real (T := T) (w := w) (hR0 k) (fun t ht => hiR t (hTle ht) k)
    (fun t ht => hReq t (hTle ht) k)
  have h := forceCoord_lt_of_lt_of_meet (continuousOn_real_of_lt hcw hT) (continuousOn_real_of_lt (hcR j) hT)
    (continuousOn_real_of_lt (hcR j') hT)
    (fun s hs hm => hmeet s.toNNReal (Real.toNNReal_pos.2 hs.1) (Real.toNNReal_le_iff_le_coe.2 hs.2) hm)
    (hr j).1 (hr j).2 (hr j').1 (hr j').2 (by rw [Real.toNNReal_zero, hR0, hR0]; exact hx) T ⟨T.coe_nonneg, le_rfl⟩
  simpa only [Real.toNNReal_coe] using h

/-- **The outermost right mark of a side of total weight `≤ −2` never reaches the driver before the lifetime**: if it
did, every right mark would sit on the driver (order), a threshold state. -/
theorem vR_last_ne_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hsum : ∑ j, ρR j ≤ -2)
    {jm : Fin nR} (hjm : ∀ j, j ≤ jm) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : vR jm t ≠ w t := by
  obtain ⟨-, -, -, -, -, -, -, -, hwR, hmono, -, -, -, -, -, -, -, hthr, -⟩ := hP
  intro he
  apply hthr t ht
  right
  have hall : ∀ j, vR j t = w t := fun j =>
    le_antisymm (by rw [← he]; exact hmono t ht (hjm j)) (hwR t ht j)
  rw [Finset.filter_true_of_mem fun j _ => hall j]
  exact hsum

end Path

/-! ### The four image words of A.1 -/

section Config

/-- `2 < κ̂ < 4` for `4 < κ < 8` (`κ̂ = 16/κ`). -/
theorem two_lt_kh_lt_four {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) : 2 < kh κ ∧ kh κ < 4 := by
  have hκ : 0 < κ := by linarith
  refine ⟨?_, ?_⟩
  · rw [kh, lt_div_iff₀ hκ]; linarith
  · rw [kh, div_lt_iff₀ hκ]; linarith

/-- `0 < κ̂ ≤ 2` for `8 ≤ κ`. -/
theorem kh_pos_le_two {κ : ℝ} (hκ8 : 8 ≤ κ) : 0 < kh κ ∧ kh κ ≤ 2 := by
  have hκ : 0 < κ := by linarith
  refine ⟨div_pos (by norm_num) hκ, ?_⟩
  rw [kh, div_le_iff₀ hκ]; linarith

/-- **The G3 small curve's initial image word** (conditioning curve: the large curve `SLE_κ(κ − 4, −4)` with marks
`x, y`; live: the strip life of its mark `x`) is admissible, for `4 < κ < 8`. -/
theorem smallG3_isSeedWord {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) {W : ℝ≥0 → ℝ}
    {VL : Fin 2 → ℝ≥0 → ℝ} {VR : Fin 0 → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath κ ![x, y] ![] ![κ - 4, -4] ![] W VL VR B ζ) {τ : ℝ≥0}
    (hlife : Strip.IsStripLife W (VL 0) ζ τ) :
    IsSeedWord ![(0 : ℝ)] ![0, VL 0 τ - VL 1 τ, W τ - VL 1 τ] (smallG3RhoL κ) (smallG3RhoR κ) := by
  have h01 : VL 1 τ < VL 0 τ := vL_lt_vL_of_path hP (i := 0) (i' := 1) (by simpa using hyx) hlife.1
    fun r _ hrτ hm => by rw [hm]; exact (hlife.2 r hrτ).ne
  have h0W : VL 0 τ < W τ := hlife.2 τ le_rfl
  have ha : 0 < VL 0 τ - VL 1 τ := by linarith
  have hb : 0 < W τ - VL 1 τ := by linarith
  obtain ⟨hk2, hk4⟩ := two_lt_kh_lt_four hκ4 hκ8
  refine ⟨⟨fun i j _ => by fin_cases i; fin_cases j; exact le_rfl, fun i => by fin_cases i; simp,
    A1Marg.monotone_three ha.le (by linarith), fun j => by fin_cases j <;> simp <;> linarith⟩,
    fun i i' _ _ => Subsingleton.elim _ _, fun j j' hjj hj0 => ?_, ?_⟩
  · fin_cases j <;> fin_cases j' <;> simp_all <;> linarith
  · rw [not_thr_iff_seedSum]
    refine ⟨?_, ?_⟩
    · rw [seedSum, Finset.sum_filter, Fin.sum_univ_one]
      simp only [Matrix.cons_val_fin_one, ↓reduceIte, smallG3RhoL]
      linarith
    · rw [seedSum, Finset.sum_filter, Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, ↓reduceIte, ha.ne', hb.ne', add_zero, smallG3RhoR]
      linarith

/-- **The Eight small curve's initial image word** (conditioning curve: the large curve `SLE_κ(0)` with mark `x`;
live: the strip life of its mark) is admissible, for `8 ≤ κ`. -/
theorem smallEight_isSeedWord {κ : ℝ} (hκ8 : 8 ≤ κ) {W : ℝ≥0 → ℝ} {VL : Fin 1 → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {τ : ℝ≥0}
    (hlife : Strip.IsStripLife W (VL 0) ζ τ) :
    IsSeedWord ![(0 : ℝ)] ![0, W τ - VL 0 τ] (smallEightRhoL κ) (smallEightRhoR κ) := by
  have hb : 0 < W τ - VL 0 τ := by linarith [hlife.2 τ le_rfl]
  refine ⟨⟨fun i j _ => by fin_cases i; fin_cases j; exact le_rfl, fun i => by fin_cases i; simp,
    A1Marg.monotone_two hb.le, fun j => by fin_cases j <;> simp; linarith⟩,
    fun i i' _ _ => Subsingleton.elim _ _, fun j j' hjj hj0 => ?_, ?_⟩
  · fin_cases j <;> fin_cases j' <;> simp_all <;> linarith
  · obtain ⟨hk0, hk2⟩ := kh_pos_le_two hκ8
    rw [not_thr_iff_seedSum]
    refine ⟨?_, ?_⟩
    · rw [seedSum, Finset.sum_filter, Fin.sum_univ_one]
      simp only [Matrix.cons_val_fin_one, ↓reduceIte, smallEightRhoL]
      linarith
    · rw [seedSum, Finset.sum_filter, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ↓reduceIte, hb.ne', add_zero, smallEightRhoR]
      linarith

theorem antitone_three {a b c : ℝ} (h₁ : b ≤ a) (h₂ : c ≤ b) : Antitone ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> (simp_all; try linarith)

theorem antitone_four {a b c d : ℝ} (h₁ : b ≤ a) (h₂ : c ≤ b) (h₃ : d ≤ c) : Antitone ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> (simp_all; try linarith)

/-- A word with no entry at `0` has seed sum `0`. -/
theorem seedSum_eq_zero_of_ne {n : ℕ} {x ρ : Fin n → ℝ} (h : ∀ i, x i ≠ 0) : seedSum x ρ = 0 := by
  rw [seedSum, Finset.filter_false_of_mem fun i _ => h i, Finset.sum_empty]

/-- **The G3 large curve's initial image word** (conditioning curve: the small curve, `κ̂ = 16/κ`, with its word
`![0]`, `![0, x − y, −y]`; live: before its lifetime) is admissible: all its entries are negative (no condition on
`κ`: the right weights of the small word sum to `−2`). -/
theorem largeG3_isSeedWord {κ x y : ℝ} (hx : x < 0) {W : ℝ≥0 → ℝ}
    {VL : Fin 1 → ℝ≥0 → ℝ} {VR : Fin 3 → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) W VL VR B ζ)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < ζ) :
    IsSeedWord ![VR 1 τ - VR 2 τ, VR 0 τ - VR 2 τ, W τ - VR 2 τ, VL 0 τ - VR 2 τ] (![] : Fin 0 → ℝ)
      (largeG3ImgRhoL κ) ![] := by
  have hsum : ∑ j, smallG3RhoR κ j ≤ -2 := by
    rw [Fin.sum_univ_three]
    simp only [smallG3RhoR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linarith
  have hlast : ∀ j : Fin 3, j ≤ 2 := fun j => by fin_cases j <;> decide
  have hle {r : ℝ≥0} (hr : r ≤ τ) : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hτ
  have hW2 : VR 2 τ ≠ W τ := vR_last_ne_of_path hP hsum hlast hτ
  obtain ⟨-, -, -, -, -, -, -, hLw, hwR, hmono, -⟩ := id hP
  have hW2' : W τ < VR 2 τ := lt_of_le_of_ne (hwR τ hτ 2) hW2.symm
  have h12 : VR 1 τ < VR 2 τ := by
    refine vR_lt_vR_of_path hP (j := 1) (j' := 2) (by simp; linarith) hτ fun r _ hrτ hm => ?_
    rw [hm]; exact vR_last_ne_of_path hP hsum hlast (hle hrτ)
  have h01 : VR 0 τ ≤ VR 1 τ := hmono τ hτ (by decide)
  have hw0 : W τ ≤ VR 0 τ := hwR τ hτ 0
  have hL : VL 0 τ ≤ W τ := hLw τ hτ 0
  refine ⟨⟨antitone_four (by linarith) (by linarith) (by linarith), fun i => ?_, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i⟩, fun i i' _ h0 => ?_, fun j => Fin.elim0 j, ?_⟩
  · fin_cases i <;> simp <;> linarith
  · exfalso
    fin_cases i <;> simp at h0 <;> linarith
  · rw [not_thr_iff_seedSum]
    refine ⟨?_, ?_⟩
    · rw [seedSum_eq_zero_of_ne fun i => by fin_cases i <;> simp <;> linarith]
      norm_num
    · rw [seedSum, Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
      norm_num

/-- **The Eight large curve's initial image word** (conditioning curve: the small curve with its word `![0]`,
`![0, −x]`; live: before its lifetime) is admissible: all its entries are negative. -/
theorem largeEight_isSeedWord {κ x : ℝ} (hx : x < 0) {W : ℝ≥0 → ℝ} {VL : Fin 1 → ℝ≥0 → ℝ}
    {VR : Fin 2 → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hP : IsIntegratedSLEPath (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) W VL VR B ζ)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < ζ) :
    IsSeedWord ![VR 0 τ - VR 1 τ, W τ - VR 1 τ, VL 0 τ - VR 1 τ] (![] : Fin 0 → ℝ) (largeEightImgRhoL κ) ![] := by
  have hsum : ∑ j, smallEightRhoR κ j ≤ -2 := by
    rw [Fin.sum_univ_two]
    simp only [smallEightRhoR, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  have hlast : ∀ j : Fin 2, j ≤ 1 := fun j => by fin_cases j <;> decide
  have hle {r : ℝ≥0} (hr : r ≤ τ) : (r : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) hτ
  have hW1 : VR 1 τ ≠ W τ := vR_last_ne_of_path hP hsum hlast hτ
  obtain ⟨-, -, -, -, -, -, -, hLw, hwR, -⟩ := id hP
  have hW1' : W τ < VR 1 τ := lt_of_le_of_ne (hwR τ hτ 1) hW1.symm
  have h01 : VR 0 τ < VR 1 τ := by
    refine vR_lt_vR_of_path hP (j := 0) (j' := 1) (by simp; linarith) hτ fun r _ hrτ hm => ?_
    rw [hm]; exact vR_last_ne_of_path hP hsum hlast (hle hrτ)
  have hw0 : W τ ≤ VR 0 τ := hwR τ hτ 0
  have hL : VL 0 τ ≤ W τ := hLw τ hτ 0
  refine ⟨⟨antitone_three (by linarith) (by linarith), fun i => ?_, fun i => Fin.elim0 i,
    fun i => Fin.elim0 i⟩, fun i i' _ h0 => ?_, fun j => Fin.elim0 j, ?_⟩
  · fin_cases i <;> simp <;> linarith
  · exfalso
    fin_cases i <;> simp at h0 <;> linarith
  · rw [not_thr_iff_seedSum]
    refine ⟨?_, ?_⟩
    · rw [seedSum_eq_zero_of_ne fun i => by fin_cases i <;> simp <;> linarith]
      norm_num
    · rw [seedSum, Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty]
      norm_num

end Config

end InteractingSLE.ZhanGT4.A1SeedGeom
