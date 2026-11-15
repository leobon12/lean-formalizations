/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutA31
import InteractingSLE.Spec.ZhanGT4.DualA2LifeJordan
import InteractingSLE.Spec.Restart.StoppedK2Kernel

/-!
# A.2: the dual pair of A.1 in the two configurations used by A.3

Packet PROVE-ZHAN-GT4-A2X. Source: Astra, *Follow-up proofs and dependency audit*, §A.1 (the exact dual coupling,
`source/external/AstraIG1/ig1_followup_proofs.txt` L160–L189), §A.2 (L510–L617), §A.3.1 (L657–L671), §A.3.2
(L691–L705); ruling R38, R53 (the strip-life form).

§A.1 (L183–L187): "There is a coupling of these two marginal laws such that, conditionally on any stopping-time prefix
of curve `k`, curve `j`, mapped by the hydrodynamic map of that prefix and stopped on first contact with it, has the
corresponding force-point law, after its capacity time change. All marked images are retained."

This file fixes the Lean form of that coupling for the two configurations of A.2 that A.3 uses.

* **(G3) configuration** (§A.3.2): `x₁ = y`, `x₂ = 0`, `p₁ = y⁻`, `p₂ = ∞`, `p₃ = y⁺`, `p₄ = x`,
  `C₁ = (κ − 6)/(κ − 4)`, `C₂ = 2/(κ − 4)`, `C₃ = −1/2`, `C₄ = 1`, `4 < κ < 8`, `y < x < 0`. The large curve
  (parameter `κ`) is the integrated `SLE_κ(κ − 4, −4)` evolution from `(0; x, y)`; the small curve (parameter
  `κ̂ = 16/κ`) starts at `y` with seeds `y⁻` (`3κ̂/2 − 4`), `y⁺` (`2 − κ̂/2`), and marks `x` (`κ̂ − 4`), `0`
  (`−κ̂/2`, the other source); the mark at `∞` has no drift.
* **(Eight) configuration** (§A.3.1): `x₁ = x`, `x₂ = 0`, `p₁ = x⁻`, `p₂ = ∞`, `p₃ = x⁺`, `C₁ = 2/(κ − 4)`,
  `κ ≥ 8`, `x < 0`. The large curve is the integrated evolution from `(0; x)` with the amalgamated weight `0`; the
  small curve starts at `x` with seeds `x⁻` (`−κ̂/2`), `x⁺` (`κ̂/2 − 2`) and the mark `0` (`−κ̂/2`).

## Lean form of the coupling

* `physHull x w s`, `physMap x w τ`: the hull and the uncentred Loewner map `g_τ` of a curve started at `x`;
* `contactTime`: the first time the closed hull of curve `j` meets the closed hull of curve `k` at time `τ`, capped
  by the lifetime of curve `j`;
* `IsImageChainUpTo`: the images `g_τ(K_j(s))`, `s` before contact, are the hulls of the image driver after a
  continuous increasing clock (the capacity time change);
* `IsCondImageLaw`: for every stopping time `τ` of curve `k`, on the live event, the image process is a local
  evolution of the image word (an `𝓕ᵏ_τ`-measurable random word, `Restart.StoppedK2.IsRandomWordEvolutionUpTo`, whose
  disintegration is `exists_ae_condExpKernel_agree_upTo`) before the image of the contact time;
* `IsA2DualPair`: the two marginal evolutions and the two conditional image laws; `IsA2DualPairG3`,
  `IsA2DualPairEight`: the two configurations with their exact image words.

The large curve's "first force collision" (A.2 L518) is the end of the strip life of its inner mark (`lifeEnd`), not
its frozen lifetime (PROVE-ZHAN-A34's finding, R53). The small curve's frozen lifetime is its first force collision
(its prefix sums are `≥ κ̂/2 − 2` until the other source is reached, `smallG3_prefix`, `smallEight_prefix`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X

open QuantumZipper

/-! ### Deterministic objects -/

/-- The hull at time `s` of the curve started at the real point `x` with centred driver `w` (`w 0 = 0`). -/
def physHull (x : ℝ) (w : ℝ → ℝ) (s : ℝ) : Set ℂ := (fun z => z + x) '' fwdHull w s

/-- The uncentred hydrodynamic map `g_τ` of the curve started at `x` with centred driver `w`:
`g_τ(z) = x + w(τ) + f_τ(z − x)`, `f_τ` the centred forward map. -/
def physMap (x : ℝ) (w : ℝ → ℝ) (τ : ℝ) (z : ℂ) : ℂ := x + w τ + fwdMap w τ (z - x)

/-- **The first contact time** of curve `j` (start `xj`, driver `wj`, lifetime `ζj`) with the closed hull of curve
`k` (start `xk`, driver `wk`) at its time `τ`: the first time the closures of the two hulls meet, capped by `ζj`. -/
def contactTime (xj : ℝ) (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ : ℝ) : ℝ≥0∞ :=
  min ζj (⨅ (s : ℝ≥0) (_ : (closure (physHull xj wj s) ∩ closure (physHull xk wk τ)).Nonempty), (s : ℝ≥0∞))

/-- **The image chain up to contact** (A.1 L183–L185: "curve `j`, mapped by the hydrodynamic map of that prefix and
stopped on first contact with it, … after its capacity time change"): the clock `clk` is continuous and strictly
increasing before the contact time `c = contactTime …` with `clk 0 = 0`, the image lifetime `ζ'` is its limit at `c`,
and for every `s < c` the image under `g_τ` of the hull of curve `j` at `s` is the hull at `clk s` of the image
driver `w'` started at the image source `x'`. -/
def IsImageChainUpTo (xj : ℝ) (wj : ℝ → ℝ) (ζj : ℝ≥0∞) (xk : ℝ) (wk : ℝ → ℝ) (τ : ℝ) (x' : ℝ) (w' : ℝ → ℝ)
    (clk : ℝ → ℝ) (ζ' : ℝ≥0∞) : Prop :=
  clk 0 = 0 ∧ ContinuousOn clk {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} ∧
    StrictMonoOn clk {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj wj ζj xk wk τ} ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ↔
      ∃ s : ℝ≥0, (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ ∧ (t : ℝ) < clk s) ∧
    ∀ s : ℝ≥0, (s : ℝ≥0∞) < contactTime xj wj ζj xk wk τ →
      physMap xk wk τ '' physHull xj wj s = physHull x' w' (clk s)

/-- The end of the strip life of the mark `v` (the first time `v` meets the driver `w`, or the lifetime). -/
def lifeEnd (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : ¬ Strip.IsStripLife w v ζ t), (t : ℝ≥0∞)

/-- **The large hull before the first force collision**: the closure of the union of the hulls over the strip life of
the inner mark (A.2 L519: "`S` the closure of the union of its hulls before its first force collision"). -/
def lifeHullClosure (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Set ℂ :=
  closure (⋃ (t : ℝ≥0) (_ : Strip.IsStripLife w v ζ t), fwdHull (fun s : ℝ => w s.toNNReal) t)

/-! ### The conditional image law -/

section Cond

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The conditional law of curve `j` given a stopping-time prefix of curve `k`, up to contact** (A.1 L183–L187).
For every stopping time `τ` of the filtration `𝓕k` of curve `k`, on the live event `{live (τ ω) ω}`, the image of curve
`j` under `g_τ` (image source `src (τ ω) ω`, image word `(ΘL, ΘR)` relative to it, weights `(ρL, ρR)`) is a local
integrated `SLE_a(ρ)` evolution of the `𝓕ᵏ_τ`-measurable random image word, before the image `ζ'` of the contact
time, in a filtration `𝓖` with `𝓕ᵏ_τ ≤ 𝓖 0` (`Restart.StoppedK2.IsRandomWordEvolutionUpTo`); almost surely on the live
event its driver is the image chain of curve `j`. Curve `j` has start `xj`, driver `wj` and lifetime `ζj`; curve `k`
has start `xk` and driver `wk`. -/
def IsCondImageLaw (a : ℝ) {nL nR : ℕ} (P : Measure Ω) (𝓕k : Filtration ℝ≥0 mΩ) (live : ℝ≥0 → Ω → Prop)
    (xj : ℝ) (wj : ℝ≥0 → Ω → ℝ) (ζj : Ω → ℝ≥0∞) (xk : ℝ) (wk : ℝ≥0 → Ω → ℝ) (src : ℝ≥0 → Ω → ℝ)
    (ΘL : ℝ≥0 → Ω → Fin nL → ℝ) (ΘR : ℝ≥0 → Ω → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∀ (τ : Ω → ℝ≥0) (hτ : IsStoppingTime 𝓕k fun ω => (τ ω : WithTop ℝ≥0)),
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
      (B' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (clk : Ω → ℝ → ℝ),
      Restart.StoppedK2.IsRandomWordEvolutionUpTo a P hτ.measurableSpace {ω | live (τ ω) ω}
        (fun ω => ΘL (τ ω) ω) (fun ω => ΘR (τ ω) ω) ρL ρR 𝓖 W' VL' VR' B' ζ' ∧
      ∀ᵐ ω ∂P, live (τ ω) ω →
        IsImageChainUpTo xj (Strip.extPath (wj · ω)) (ζj ω) xk (Strip.extPath (wk · ω)) (τ ω) (src (τ ω) ω)
          (Strip.extPath (W' · ω)) (clk ω) (ζ' ω)

end Cond

/-! ### The small words and their arithmetic -/

/-- The small parameter `κ̂ = 16/κ`. -/
abbrev kh (κ : ℝ) : ℝ := 16 / κ

/-- (G3) small curve, left weights: the seed `y⁻` carries `C₁(κ̂ − 4) = 3κ̂/2 − 4`. -/
def smallG3RhoL (κ : ℝ) : Fin 1 → ℝ := ![3 * kh κ / 2 - 4]

/-- (G3) small curve, right weights: `y⁺` (`2 − κ̂/2`), `x` (`κ̂ − 4`), the other source `0` (`−κ̂/2`). -/
def smallG3RhoR (κ : ℝ) : Fin 3 → ℝ := ![2 - kh κ / 2, kh κ - 4, -(kh κ / 2)]

/-- (G3) large curve given a small prefix, left weights (nearest first): `x` (`κ − 4`), `y⁺` (`C₃(κ − 4) = 2 − κ/2`),
the small tip (`−κ/2`), `y⁻` (`C₁(κ − 4) = κ − 6`). -/
def largeG3ImgRhoL (κ : ℝ) : Fin 4 → ℝ := ![κ - 4, 2 - κ / 2, -(κ / 2), κ - 6]

/-- (Eight) small curve, left weight: the seed `x⁻` carries `C₁(κ̂ − 4) = −κ̂/2`. -/
def smallEightRhoL (κ : ℝ) : Fin 1 → ℝ := ![-(kh κ / 2)]

/-- (Eight) small curve, right weights: `x⁺` (`κ̂/2 − 2`), the other source `0` (`−κ̂/2`). -/
def smallEightRhoR (κ : ℝ) : Fin 2 → ℝ := ![kh κ / 2 - 2, -(kh κ / 2)]

/-- (Eight) large curve given a small prefix, left weights (nearest first): `x⁺` (`(κ − 4)/2`), the small tip
(`−κ/2`), `x⁻` (`C₁(κ − 4) = 2`). -/
def largeEightImgRhoL (κ : ℝ) : Fin 3 → ℝ := ![(κ - 4) / 2, -(κ / 2), 2]

theorem kh_bounds_G3 {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) : 2 < kh κ ∧ kh κ < 4 := by
  have hκ0 : 0 < κ := by linarith
  refine ⟨?_, ?_⟩
  · rw [kh, lt_div_iff₀ hκ0]; linarith
  · rw [kh, div_lt_iff₀ hκ0]; linarith

theorem kh_bounds_eight {κ : ℝ} (hκ8 : 8 ≤ κ) : 0 < kh κ ∧ kh κ ≤ 2 := by
  have hκ0 : 0 < κ := by linarith
  refine ⟨div_pos (by norm_num) hκ0, ?_⟩
  rw [kh, div_le_iff₀ hκ0]; linarith

/-- **(G3) small curve, the prefix sums** (§A.3.2 L702–L704: "Both seed charges are at least `κ̂/2 − 2`, and the right
cumulative after `x` is exactly `κ̂/2 − 2`"): the left seed and the first two right prefixes are `≥ κ̂/2 − 2`, the
full right sum is `−2` (the first force collision is the collision with the other source). -/
theorem smallG3_prefix {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) :
    kh κ / 2 - 2 ≤ smallG3RhoL κ 0 ∧ kh κ / 2 - 2 ≤ smallG3RhoR κ 0 ∧
      smallG3RhoR κ 0 + smallG3RhoR κ 1 = kh κ / 2 - 2 ∧
      smallG3RhoR κ 0 + smallG3RhoR κ 1 + smallG3RhoR κ 2 = -2 := by
  obtain ⟨h2, h4⟩ := kh_bounds_G3 hκ4 hκ8
  simp only [smallG3RhoL, smallG3RhoR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  refine ⟨by linarith, by linarith, by ring, by ring⟩

/-- **(G3) the large curve's charges at `y` amalgamate to `−4`** (§A.3.2 L701: "the three charges at `y` sum to
`−4`"): `y⁺`, the other source and `y⁻` in the image word given a small prefix. -/
theorem largeG3Img_amalgamate (κ : ℝ) : largeG3ImgRhoL κ 1 + largeG3ImgRhoL κ 2 + largeG3ImgRhoL κ 3 = -4 := by
  show (2 - κ / 2) + -(κ / 2) + (κ - 6) = -4
  ring

/-- **(Eight) small curve, the prefix sums** (§A.3.1 L668–L670: "The seed condition at `x⁻` is `−κ̂/2 ≥ κ̂/2 − 2`, valid
also at equality `κ̂ = 2`"). -/
theorem smallEight_prefix {κ : ℝ} (hκ8 : 8 ≤ κ) :
    kh κ / 2 - 2 ≤ smallEightRhoL κ 0 ∧ kh κ / 2 - 2 ≤ smallEightRhoR κ 0 ∧
      smallEightRhoR κ 0 + smallEightRhoR κ 1 = -2 := by
  obtain ⟨-, h2⟩ := kh_bounds_eight hκ8
  simp only [smallEightRhoL, smallEightRhoR, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨by linarith, le_rfl, by ring⟩

/-- **(Eight) the large curve's charges at `x` amalgamate to `0`** (§A.3.1 L663–L664). -/
theorem largeEightImg_amalgamate (κ : ℝ) :
    largeEightImgRhoL κ 0 + largeEightImgRhoL κ 1 + largeEightImgRhoL κ 2 = 0 := by
  simp only [largeEightImgRhoL, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- The (G3) small word is an ordered force word (`y < x < 0`): seeds at `0⁻`, `0⁺`, then `x − y < −y`. -/
theorem isOrderedForceWord_smallG3 {y x : ℝ} (hyx : y < x) (hx : x < 0) :
    IsOrderedForceWord (![0] : Fin 1 → ℝ) ![0, x - y, -y] := by
  refine ⟨fun i j _ => by fin_cases i; fin_cases j; exact le_rfl, fun i => by fin_cases i; simp, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith
  · intro i
    fin_cases i <;> simp <;> linarith

/-- The (Eight) small word is an ordered force word (`x < 0`). -/
theorem isOrderedForceWord_smallEight {x : ℝ} (hx : x < 0) :
    IsOrderedForceWord (![0] : Fin 1 → ℝ) ![0, -x] := by
  refine ⟨fun i j _ => by fin_cases i; fin_cases j; exact le_rfl, fun i => by fin_cases i; simp, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    linarith
  · intro i
    fin_cases i <;> simp
    linarith

/-- **The (G3) small marginal exists** (Theorem 2.2, `exists_isIntegratedSLEEvolution_assembled`): the small word is
an ordered force word, so the small curve of the coupling is not vacuous. -/
theorem exists_smallG3_evolution {κ : ℝ} (hκ4 : 4 < κ) {y x : ℝ} (hyx : y < x) (hx : x < 0) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 3 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕 W VL VR B ζ :=
  exists_isIntegratedSLEEvolution_assembled (div_pos (by norm_num) (by linarith)) (isOrderedForceWord_smallG3 hyx hx)

/-- **The (Eight) small marginal exists** (Theorem 2.2). -/
theorem exists_smallEight_evolution {κ : ℝ} (hκ8 : 8 ≤ κ) {x : ℝ} (hx : x < 0) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 2 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕 W VL VR B ζ :=
  exists_isIntegratedSLEEvolution_assembled (div_pos (by norm_num) (by linarith)) (isOrderedForceWord_smallEight hx)

/-! ### The dual pair -/

section Pair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The dual pair of A.1** for a large curve from `0` with left word `(xL₂, ρL₂)` (no right marks) and a small curve
from `x₁` with word `(xL₁, xR₁; ρL₁, ρR₁)` relative to `x₁`, both on `(Ω, P)`:

* the large curve is an integrated `SLE_κ` evolution in `𝓕₂`; it lives before the first force collision, the end of
  the strip life of its inner mark `VL₂ 0` (`lifeEnd`);
* the small curve is an integrated `SLE_{16/κ}` evolution in `𝓕₁` (its frozen lifetime is its first force collision);
* given a large prefix at a stopping time of `𝓕₂` inside the strip life, the small curve mapped by `g_τ` is a local
  evolution of the image word `(src₁; ΘL₁, ΘR₁)` (weights `ρL₁, ρR₁`) up to contact;
* given a small prefix at a stopping time of `𝓕₁` before `ζ₁`, the large curve mapped by `g_σ` is a local evolution of
  the image word `(src₂; ΘL₂)` with the separated weights `ρL₂'` up to contact (contact capped by `lifeEnd`). -/
def IsA2DualPair (κ : ℝ) {nL₂ nL₁ nR₁ mL₂ : ℕ} (xL₂ ρL₂ : Fin nL₂ → ℝ) (x₁ : ℝ) (xL₁ : Fin nL₁ → ℝ)
    (xR₁ : Fin nR₁ → ℝ) (ρL₁ : Fin nL₁ → ℝ) (ρR₁ : Fin nR₁ → ℝ) (ρL₂' : Fin mL₂ → ℝ)
    (src₁ : ℝ≥0 → Ω → ℝ) (ΘL₁ : ℝ≥0 → Ω → Fin nL₁ → ℝ) (ΘR₁ : ℝ≥0 → Ω → Fin nR₁ → ℝ)
    (src₂ : ℝ≥0 → Ω → ℝ) (ΘL₂ : ℝ≥0 → Ω → Fin mL₂ → ℝ) (P : Measure Ω)
    (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ : Fin nL₂ → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ)
    (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞) (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ)
    (VL₁ : Fin nL₁ → ℝ≥0 → Ω → ℝ) (VR₁ : Fin nR₁ → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞)
    (i₀ : Fin nL₂) : Prop :=
  IsIntegratedSLEEvolution κ xL₂ ![] ρL₂ ![] P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ ∧
    IsIntegratedSLEEvolution (kh κ) xL₁ xR₁ ρL₁ ρR₁ P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ ∧
    IsCondImageLaw (kh κ) P 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ i₀ · ω) (ζ₂ ω) t)
      x₁ W₁ ζ₁ 0 W₂ src₁ ΘL₁ ΘR₁ ρL₁ ρR₁ ∧
    IsCondImageLaw κ P 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω)
      0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ i₀ · ω) (ζ₂ ω)) x₁ W₁ src₂ ΘL₂ (fun _ _ => ![]) ρL₂' ![]

/-- **The dual pair in the (G3) configuration** (§A.3.2 L697–L705): large `SLE_κ(κ − 4, −4)` from `(0; x, y)`; small
`SLE_{κ̂}` from `y` with the seeds `y∓` and the marks `x`, `0`. Image words: given a large prefix at `τ`, the small
image starts at `V_y(τ)` with the seeds, `V_x(τ)` and the large tip `W₂(τ)`; given a small prefix at `σ`, the large
image starts at the image `y + V₀(σ)` of `0` with the left marks `x`, `y⁺`, the small tip and `y⁻` (separated). -/
def IsA2DualPairG3 (κ y x : ℝ) (P : Measure Ω) (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
    (VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
    (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 3 → ℝ≥0 → Ω → ℝ)
    (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞) : Prop :=
  IsA2DualPair κ ![x, y] ![κ - 4, -4] y ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) (largeG3ImgRhoL κ)
    (fun t ω => VL₂ 1 t ω) (fun _ _ => ![0])
    (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω])
    (fun t ω => y + VR₁ 2 t ω)
    (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
    P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 0

/-- **The dual pair in the (Eight) configuration** (§A.3.1 L657–L670): large evolution from `(0; x)` with weight `0`;
small `SLE_{κ̂}` from `x` with the seeds `x∓` and the mark `0`. Image words: given a large prefix at `τ`, the small
image starts at `V_x(τ)` with the seeds and the large tip; given a small prefix at `σ`, the large image starts at the
image `x + V₀(σ)` of `0` with the left marks `x⁺`, the small tip and `x⁻`. -/
def IsA2DualPairEight (κ x : ℝ) (P : Measure Ω) (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ) (ζ₂ : Ω → ℝ≥0∞)
    (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (VR₁ : Fin 2 → ℝ≥0 → Ω → ℝ)
    (B₁ : ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞) : Prop :=
  IsA2DualPair κ ![x] ![0] x ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) (largeEightImgRhoL κ)
    (fun t ω => VL₂ 0 t ω) (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω])
    (fun t ω => x + VR₁ 1 t ω)
    (fun t ω => ![VR₁ 0 t ω - VR₁ 1 t ω, W₁ t ω - VR₁ 1 t ω, VL₁ 0 t ω - VR₁ 1 t ω])
    P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 0

end Pair

end InteractingSLE.ZhanGT4.A2X
