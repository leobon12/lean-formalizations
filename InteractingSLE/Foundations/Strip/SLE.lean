/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Strip.Chain
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

/-!
# Strip `SLE_κ(ρ)` through the half-plane (ruling R36)

Packet PROVE-ZHAN-A. A strip `SLE_κ(ρ)` in `S_π` with lower marks `pL` (left of the source, `≤ 0`) and `pR` (right,
`≥ 0`), weights `ρL`, `ρR`, and endpoint weights `τ₋` at `−∞` and `τ₊` at `+∞` (Astra §3 (ii), (3.3)) is, by
definition, the chordal integrated `SLE_κ(ρ)` evolution (frozen `IsIntegratedSLEEvolution`) of its exponential image
`z ↦ e^z − 1`: the lower marks go to `e^p − 1`, the end `−∞` becomes the extra outermost left mark `−1` with weight
`τ₋`, and the end `+∞` is the chordal target `∞`, which carries the charge `τ₊ = κ − 6 − (Σρ + τ₋)` (Astra (3.4); this
is the condition `q₊ + q₋ = κ − 6` of (3.3)). The strip clock, map, driver and trace are those of `Chain.lean`, applied
to the driver `W` and the end mark `v = V^{L, nL}` (`stripEndMark`).

## Main definitions

* `wordXL`, `wordXR`, `wordRhoL`: the chordal force word of the exponential image;
* `tauPlus`, `chargePlus`, `chargeMinus`: `τ₊`, `q₊ = s₊ + τ₊`, `q₋ = s₋ + τ₋`;
* `IsOrderedStripWord`, `IsSeparatedStripWord`: ordered / separated lower marks;
* `IsStripSLEEvolution`: the strip evolution;
* `extPath`: a path on `ℝ≥0` read on `ℝ`; `IsStripLife w v ζ s`: chordal time `s` lies in the strip life
  (`s < ζ` and `v < w` on `[0, s]`).

## Main results

* `chargePlus_add_chargeMinus`: `q₊ + q₋ = κ − 6`;
* `IsOrderedStripWord.isOrderedForceWord`: the chordal image word is ordered;
* `isSepMark_of_isIntegratedSLEPath`: on the strip life, the driver and the end mark satisfy `IsSepMark`, so the
  strip clock, map and driver of `Chain.lean` apply (with the strip Loewner equation).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Strip

variable {nL nR : ℕ}

/-! ### The chordal force word of the exponential image -/

/-- Left chordal positions: `e^{pL i} − 1` for the lower left marks, then the end `−∞ ↦ −1` (outermost). -/
def wordXL (pL : Fin nL → ℝ) : Fin (nL + 1) → ℝ := Fin.snoc (fun i => Real.exp (pL i) - 1) (-1)

/-- Right chordal positions `e^{pR i} − 1`. -/
def wordXR (pR : Fin nR → ℝ) : Fin nR → ℝ := fun i => Real.exp (pR i) - 1

/-- Left chordal weights: `ρL`, then `τ₋` at the end mark. -/
def wordRhoL (ρL : Fin nL → ℝ) (τm : ℝ) : Fin (nL + 1) → ℝ := Fin.snoc ρL τm

/-- The endpoint weight at `+∞`, the target charge (3.4): `τ₊ = κ − 6 − Σρ − τ₋`. -/
def tauPlus (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (τm : ℝ) : ℝ :=
  κ - 6 - (∑ i, ρL i) - (∑ i, ρR i) - τm

/-- `q₊ = s₊ + τ₊`. -/
def chargePlus (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (τm : ℝ) : ℝ :=
  (∑ i, ρR i) + tauPlus κ ρL ρR τm

/-- `q₋ = s₋ + τ₋`. -/
def chargeMinus (ρL : Fin nL → ℝ) (τm : ℝ) : ℝ := (∑ i, ρL i) + τm

theorem chargePlus_add_chargeMinus (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (τm : ℝ) :
    chargePlus κ ρL ρR τm + chargeMinus ρL τm = κ - 6 := by
  simp only [chargePlus, chargeMinus, tauPlus]; ring

@[simp] theorem wordXL_castSucc (pL : Fin nL → ℝ) (i : Fin nL) :
    wordXL pL i.castSucc = Real.exp (pL i) - 1 := by simp [wordXL]

@[simp] theorem wordXL_last (pL : Fin nL → ℝ) : wordXL pL (Fin.last nL) = -1 := by simp [wordXL]

@[simp] theorem wordRhoL_castSucc (ρL : Fin nL → ℝ) (τm : ℝ) (i : Fin nL) :
    wordRhoL ρL τm i.castSucc = ρL i := by simp [wordRhoL]

@[simp] theorem wordRhoL_last (ρL : Fin nL → ℝ) (τm : ℝ) : wordRhoL ρL τm (Fin.last nL) = τm := by
  simp [wordRhoL]

theorem sum_wordRhoL (ρL : Fin nL → ℝ) (τm : ℝ) : ∑ i, wordRhoL ρL τm i = chargeMinus ρL τm := by
  rw [Fin.sum_univ_castSucc]; simp [chargeMinus]

/-- Ordered lower marks: `pL` antitone and `≤ 0`, `pR` monotone and `≥ 0` (seeds `0⁻`, `0⁺` allowed). -/
def IsOrderedStripWord (pL : Fin nL → ℝ) (pR : Fin nR → ℝ) : Prop :=
  Antitone pL ∧ (∀ i, pL i ≤ 0) ∧ Monotone pR ∧ ∀ i, 0 ≤ pR i

/-- Separated lower marks (Astra (ii), "separated lower force marks"): strictly ordered and off the source. -/
def IsSeparatedStripWord (pL : Fin nL → ℝ) (pR : Fin nR → ℝ) : Prop :=
  StrictAnti pL ∧ (∀ i, pL i < 0) ∧ StrictMono pR ∧ ∀ i, 0 < pR i

theorem IsSeparatedStripWord.isOrderedStripWord {pL : Fin nL → ℝ} {pR : Fin nR → ℝ}
    (h : IsSeparatedStripWord pL pR) : IsOrderedStripWord pL pR :=
  ⟨h.1.antitone, fun i => (h.2.1 i).le, h.2.2.1.monotone, fun i => (h.2.2.2 i).le⟩

theorem IsOrderedStripWord.isOrderedForceWord {pL : Fin nL → ℝ} {pR : Fin nR → ℝ}
    (h : IsOrderedStripWord pL pR) : IsOrderedForceWord (wordXL pL) (wordXR pR) := by
  obtain ⟨hL, hL0, hR, hR0⟩ := h
  refine ⟨?_, ?_, fun i j hij => ?_, fun i => ?_⟩
  · intro i j hij
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => exact le_rfl
      | cast i => simp only [wordXL_last, wordXL_castSucc]; linarith [Real.exp_pos (pL i)]
    | cast j =>
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_le.2 (Fin.castSucc_lt_last j))
      | cast i =>
        simp only [wordXL_castSucc]
        have := hL (Fin.castSucc_le_castSucc_iff.1 hij)
        linarith [Real.exp_le_exp.2 this]
  · intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast i =>
      simp only [wordXL_castSucc, sub_nonpos]
      exact Real.exp_le_one_iff.2 (hL0 i)
  · simp only [wordXR]; linarith [Real.exp_le_exp.2 (hR hij)]
  · simp only [wordXR, sub_nonneg]; exact Real.one_le_exp_iff.2 (hR0 i)

/-! ### The strip evolution -/

/-- **Strip `SLE_κ(ρ)`** (ruling R36): the chordal integrated `SLE_κ(ρ)` evolution of the exponential image, with
left marks `e^{pL} − 1` and the end mark `−1` (weight `τ₋`), right marks `e^{pR} − 1`, and the target `∞` (charge
`tauPlus κ ρL ρR τm`). The end mark is `VL (Fin.last nL)`. -/
def IsStripSLEEvolution (κ : ℝ) (pL : Fin nL → ℝ) (pR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (τm : ℝ) {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsIntegratedSLEEvolution κ (wordXL pL) (wordXR pR) (wordRhoL ρL τm) ρR P 𝓕 W VL VR B ζ

/-- A path on `ℝ≥0` read on `ℝ` (constant on `(−∞, 0]`), the convention of the frozen integrals. -/
def extPath (f : ℝ≥0 → ℝ) : ℝ → ℝ := fun s => f s.toNNReal

@[simp] theorem extPath_coe (f : ℝ≥0 → ℝ) (s : ℝ≥0) : extPath f s = f s := by simp [extPath]

/-- Chordal time `s` lies in the strip life of the path `(w, v)` with lifetime `ζ`: `s < ζ` and the end mark stays
strictly left of the driver on `[0, s]`. -/
def IsStripLife (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (s : ℝ≥0) : Prop :=
  (s : ℝ≥0∞) < ζ ∧ ∀ r ≤ s, v r < w r

theorem IsStripLife.mono {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {s s' : ℝ≥0} (h : IsStripLife w v ζ s)
    (hs' : s' ≤ s) : IsStripLife w v ζ s' :=
  ⟨lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs') h.1, fun r hr => h.2 r (hr.trans hs')⟩

/-- A path continuous on `{t < ζ}` is, read on `ℝ`, continuous on `[0, s]` for `s < ζ`. -/
theorem continuousOn_extPath {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ})
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) : ContinuousOn (extPath f) (Icc 0 (s : ℝ)) := by
  refine hf.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
  refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hs
  exact Real.toNNReal_le_iff_le_coe.2 hr.2

/-- **On the strip life the driver and the end mark form a separated mark pair**, so `Chain.lean` applies. -/
theorem isSepMark_of_isIntegratedSLEPath {a : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a (wordXL pL) xR ρL ρR w vL vR b ζ) {s : ℝ≥0}
    (hs : IsStripLife w (vL (Fin.last nL)) ζ s) :
    IsSepMark (extPath w) (extPath (vL (Fin.last nL))) s := by
  obtain ⟨-, -, -, hcw, hcvL, -, -, -, -, -, -, -, -, hvL, -⟩ := hp
  refine ⟨s.coe_nonneg, continuousOn_extPath hcw hs.1, continuousOn_extPath (hcvL _) hs.1,
    fun r hr => hs.2 _ (Real.toNNReal_le_iff_le_coe.2 hr.2), fun r hr => ?_⟩
  have hr' : (r.toNNReal : ℝ≥0∞) < ζ :=
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hs.1
  have h := hvL r.toNNReal hr' (Fin.last nL)
  rw [wordXL_last, Real.coe_toNNReal r hr.1] at h
  exact h

end Strip

end InteractingSLE
