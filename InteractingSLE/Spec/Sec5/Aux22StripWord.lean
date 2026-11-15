/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftTrace
import InteractingSLE.Spec.Zhan.ConstDriftAlive
import InteractingSLE.Spec.Zhan.StripNoncollision
import InteractingSLE.Spec.Zhan.AvoidPassive
import InteractingSLE.Spec.Sec7.CounterflowProbDilation
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Aux. lemma 22 in the strip, step 3b: the new strip word

Packet PROVE-SEC5-L (specification §4.1, Aux. lemma 22, pp. 113–115). After the change of target, the span `I` of
Aux. lemma 22 is the half-line `(e, ∞)` to the right of the last right mark `e` of the transformed word, and the new
target `∞` is the image of the right end of `I`. Reflecting (`x ↦ −x`) and dilating by `1/e` makes `e` the end mark
`−1` of an R36 strip word (`Foundations/Strip/SLE.lean`): the strip of the map (UC11)–(UC12), with `I` as its upper
boundary.

For an integrated evolution with left positions `XL : Fin n → ℝ` and right positions `XR : Fin (j + 1) → ℝ`,
`e = XR (last j) > 0`, all `XL < e`, and the other right positions below `e`:

* `stripPL XR`, `stripPR XR XL`: the strip positions `log(1 − XR/e)` (new lower left marks) and `log(1 − XL/e)`
  (new lower right marks);
* **`isStripSLEEvolution_reflect_dilate`**: the reflected evolution dilated by `c = e²` is the strip evolution with
  lower left marks `stripPL XR` (weights `Fin.init ρR`), end weight `ρR (last j)`, lower right marks `stripPR XR XL`
  (weights `ρL`);
* `isSeparatedStripWord_strip`: the strip word is separated when every left position is negative and every right
  position is positive and the positions are distinct;
* **`stripEndpointStatement_le_four`**: Zhan's strip endpoint theorem for `0 < κ ≤ 4`, unconditional (PROVE-ZHAN-A5/A7's
  `Zhan.stripEndpointStatement_of_height` with `Zhan.constDriftHeightStatement_of_le_four`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Strip Sec7.Dilation

variable {n j : ℕ}

/-- **Zhan's strip endpoint theorem for `0 < κ ≤ 4`**, with no named input left. -/
theorem stripEndpointStatement_le_four {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) : StripEndpointStatement.{u} κ :=
  Zhan.stripEndpointStatement_of_height hκ (Zhan.constDriftHeightStatement_of_le_four hκ.le hκ4)

/-! ### The strip positions -/

/-- The strip positions of the right marks before the last one, `log(1 − XR/e)` with `e = XR (last j)`. -/
def stripPL (XR : Fin (j + 1) → ℝ) : Fin j → ℝ := fun k => Real.log (1 - XR k.castSucc / XR (Fin.last j))

/-- The strip positions of the left marks, `log(1 − XL/e)` with `e = XR (last j)`. -/
def stripPR (XR : Fin (j + 1) → ℝ) (XL : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.log (1 - XL i / XR (Fin.last j))

/-- The dilation factor `c = e²`. -/
def stripScale (XR : Fin (j + 1) → ℝ) : ℝ≥0 := ⟨XR (Fin.last j) ^ 2, sq_nonneg _⟩

theorem sqrt_stripScale {XR : Fin (j + 1) → ℝ} (he : 0 < XR (Fin.last j)) :
    √((stripScale XR : ℝ≥0) : ℝ) = XR (Fin.last j) := by
  show √(XR (Fin.last j) ^ 2) = _
  exact Real.sqrt_sq he.le

theorem stripScale_ne_zero {XR : Fin (j + 1) → ℝ} (he : 0 < XR (Fin.last j)) : stripScale XR ≠ 0 := by
  intro h
  have := congrArg (fun c : ℝ≥0 => (c : ℝ)) h
  simp only [stripScale, NNReal.coe_zero] at this
  exact absurd this (pow_ne_zero 2 he.ne')

theorem wordXL_stripPL {XR : Fin (j + 1) → ℝ} (he : 0 < XR (Fin.last j))
    (hlt : ∀ k : Fin j, XR k.castSucc < XR (Fin.last j)) :
    wordXL (stripPL XR) = fun i => (√((stripScale XR : ℝ≥0) : ℝ))⁻¹ * (-XR) i := by
  rw [sqrt_stripScale he]
  funext i
  induction i using Fin.lastCases with
  | last =>
    rw [wordXL_last, Pi.neg_apply, mul_neg, inv_mul_cancel₀ he.ne']
  | cast k =>
    rw [wordXL_castSucc, stripPL, Real.exp_log (by
      have := (div_lt_one he).2 (hlt k)
      linarith), Pi.neg_apply]
    field_simp
    ring

theorem wordXR_stripPR {XR : Fin (j + 1) → ℝ} {XL : Fin n → ℝ} (he : 0 < XR (Fin.last j))
    (hlt : ∀ i, XL i < XR (Fin.last j)) :
    wordXR (stripPR XR XL) = fun i => (√((stripScale XR : ℝ≥0) : ℝ))⁻¹ * (-XL) i := by
  rw [sqrt_stripScale he]
  funext i
  rw [wordXR, stripPR, Real.exp_log (by
    have := (div_lt_one he).2 (hlt i)
    linarith), Pi.neg_apply]
  field_simp
  ring

theorem wordRhoL_init (ρ : Fin (j + 1) → ℝ) : wordRhoL (Fin.init ρ) (ρ (Fin.last j)) = ρ :=
  Fin.snoc_init_self ρ

/-! ### The reflected, dilated evolution is a strip evolution -/

theorem isStripSLEEvolution_of_eq {κ : ℝ} {nL nR : ℕ} {xL : Fin (nL + 1) → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL' : Fin nL → ℝ}
    {τm : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (h : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (h1 : wordXL pL = xL)
    (h2 : wordXR pR = xR) (h3 : wordRhoL ρL' τm = ρL) :
    IsStripSLEEvolution κ pL pR ρL' ρR τm P 𝓕 W VL VR B ζ := by
  subst h1 h2 h3
  exact h

/-- **The reflected evolution, dilated by `e²`, is a strip evolution** with end mark `−1` the image of the last right
mark `e`. -/
theorem isStripSLEEvolution_reflect_dilate {κ : ℝ} {XL : Fin n → ℝ} {XR : Fin (j + 1) → ℝ} {ρL : Fin n → ℝ}
    {ρR : Fin (j + 1) → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin n → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ XL XR ρL ρR P 𝓕 W VL VR B ζ)
    (he : 0 < XR (Fin.last j)) (hltR : ∀ k : Fin j, XR k.castSucc < XR (Fin.last j))
    (hltL : ∀ i, XL i < XR (Fin.last j)) :
    IsStripSLEEvolution κ (stripPL XR) (stripPR XR XL) (Fin.init ρR) ρL (ρR (Fin.last j)) P
      (dilFiltration (stripScale XR) 𝓕) (dilProc (stripScale XR) (-W))
      (fun i => dilProc (stripScale XR) (-VR i)) (fun i => dilProc (stripScale XR) (-VL i))
      (dilProc (stripScale XR) (-B)) (fun ω => ζ ω / stripScale XR) :=
  isStripSLEEvolution_of_eq ((IsIntegratedSLEEvolution.reflect hE).dilate (stripScale_ne_zero he))
    (wordXL_stripPL he hltR) (wordXR_stripPR he hltL) (wordRhoL_init ρR)

/-- **The strip word is separated** when every left position is negative, every right position other than the last is
positive, and the positions are strictly ordered. -/
theorem isSeparatedStripWord_strip {XL : Fin n → ℝ} {XR : Fin (j + 1) → ℝ} (he : 0 < XR (Fin.last j))
    (hR : StrictMono XR) (hR0 : ∀ k : Fin j, 0 < XR k.castSucc) (hL : StrictAnti XL) (hL0 : ∀ i, XL i < 0) :
    IsSeparatedStripWord (stripPL XR) (stripPR XR XL) := by
  have hpos : ∀ k : Fin j, 0 < 1 - XR k.castSucc / XR (Fin.last j) := fun k => by
    have := (div_lt_one he).2 (hR (Fin.castSucc_lt_last k))
    linarith
  refine ⟨fun k k' hkk' => ?_, fun k => ?_, fun i i' hii' => ?_, fun i => ?_⟩
  · refine Real.log_lt_log (hpos k') ?_
    have := div_lt_div_of_pos_right (hR (Fin.castSucc_lt_castSucc_iff.2 hkk')) he
    linarith
  · refine Real.log_neg (hpos k) ?_
    have := div_pos (hR0 k) he
    linarith
  · have h1 : 0 < 1 - XL i / XR (Fin.last j) := by
      have := div_neg_of_neg_of_pos (hL0 i) he
      linarith
    refine Real.log_lt_log h1 ?_
    have := div_lt_div_of_pos_right (hL hii') he
    linarith
  · refine Real.log_pos ?_
    have := div_neg_of_neg_of_pos (hL0 i) he
    linarith

end Aux22Strip

end Sec5

end InteractingSLE
