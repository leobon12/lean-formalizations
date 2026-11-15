/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1LargeDensBridge

/-!
# Zhan's A.1 (R80): the large-curve image words as frozen data

Packet PROVE-A1-LARGEDENS. Source: Astra, *Follow-up proofs* §A.1 (`ig1_followup_proofs.txt` L160–L187, R38) and
§A.3.1–A.3.2 (the large-curve image words given a small prefix, `CrosscutA2Pair`): (Eight) `x⁺` with `(κ − 4)/2`, the
small tip with `−κ/2`, `x⁻` with `2`; (G3) `x` with `κ − 4`, `y⁺` with `2 − κ/2`, the small tip with `−κ/2`, `y⁻`
with `κ − 6`.

The frozen-curve line (`FrzData`, `FrzD10Hyp`) carries the other tip `ζ₀` with the weight `−κ/2` and the force marks
`ζ_m` with the weights `κ r_m`. Here the large image words are written in that form:

* `largeEightRR`, `largeEightSort` and **`largeEight_markWt`**, **`largeEight_markPos`**: the Eight word is the frozen
  data `(ζ₀, ζ) = (tip, ![x⁺, x⁻])` with reduced charges `((κ − 4)/(2κ), 2/κ)`, all marks on the left;
* `largeG3RR`, `largeG3Sort`, **`largeG3_markWt`**, **`largeG3_markPos`**: the G3 word is `(tip, ![x, y⁺, y⁻])` with
  reduced charges `((κ − 4)/κ, (2 − κ/2)/κ, (κ − 6)/κ)`;
* **`isSeedSampleLaw_largeEight_of_frzD10Hyp`**, **`isSeedSampleLaw_largeG3_of_frzD10Hyp`**: A1-FAMILY's one-sample
  law with exactly A.1's large image weights (`largeEightImgRhoL`, `largeG3ImgRhoL`) and frozen-chart marks in the
  order of PROVE-A1-MULTIMARK's `largeEightMarks`, `largeG3Marks`, under `Q = (M̃_S/M̃_0)·P`.

In (Eight) the large curve is ordinary `SLE_κ` (its only own mark has weight `0`), so `FrzD10Hyp` applies to its own
Brownian motion. In (G3) the large curve carries the own marks `x, y` with `κ − 4, −4`; `FrzD10Hyp` is then needed for
a Brownian motion `B` with `W = √κB` up to the rectangle exit (after removing the own drift by Girsanov).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1LargeDens

open A1Family A1MultiMark A1Forces A2X

/-! ### Eight -/

/-- The reduced charges `ρ/κ` of the Eight large word's force marks `x⁺` (`(κ − 4)/2`) and `x⁻` (`2`). -/
def largeEightRR (κ : ℝ) : Fin 2 → ℝ := ![(κ - 4) / (2 * κ), 2 / κ]

/-- The Eight sorting of the frozen data: `x⁺`, the tip, `x⁻`, all on the left. -/
def largeEightSort : Fin 3 ⊕ Fin 0 ≃ Option (Fin 2) where
  toFun := Sum.elim ![some 0, none, some 1] Fin.elim0
  invFun o := Sum.inl (o.elim 1 ![0, 2])
  left_inv := by
    rintro (i | i)
    · fin_cases i <;> rfl
    · exact i.elim0
  right_inv := by
    rintro (_ | i)
    · rfl
    · fin_cases i <;> rfl

/-- **The Eight weights are the frozen-data weights.** -/
theorem largeEight_markWt {κ : ℝ} (hκ : κ ≠ 0) (i : Fin 3) :
    largeEightImgRhoL κ i = markWt κ (largeEightRR κ) (largeEightSort (.inl i)) := by
  fin_cases i <;>
    simp only [largeEightImgRhoL, largeEightRR, largeEightSort, markWt, Equiv.coe_fn_mk, Sum.elim_inl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Option.elim, Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk] <;> field_simp

/-- **The Eight marks are the frozen-data marks.** -/
theorem largeEight_markPos (pp tip pm : ℝ) (i : Fin 3) :
    ![pp, tip, pm] i = markPos tip ![pp, pm] (largeEightSort (.inl i)) := by
  fin_cases i <;> rfl

/-! ### G3 -/

/-- The reduced charges of the G3 large word's force marks `x` (`κ − 4`), `y⁺` (`2 − κ/2`), `y⁻` (`κ − 6`). -/
def largeG3RR (κ : ℝ) : Fin 3 → ℝ := ![(κ - 4) / κ, (2 - κ / 2) / κ, (κ - 6) / κ]

/-- The G3 sorting of the frozen data: `x`, `y⁺`, the tip, `y⁻`, all on the left. -/
def largeG3Sort : Fin 4 ⊕ Fin 0 ≃ Option (Fin 3) where
  toFun := Sum.elim ![some 0, some 1, none, some 2] Fin.elim0
  invFun o := Sum.inl (o.elim 2 ![0, 1, 3])
  left_inv := by
    rintro (i | i)
    · fin_cases i <;> rfl
    · exact i.elim0
  right_inv := by
    rintro (_ | i)
    · rfl
    · fin_cases i <;> rfl

/-- **The G3 weights are the frozen-data weights.** -/
theorem largeG3_markWt {κ : ℝ} (hκ : κ ≠ 0) (i : Fin 4) :
    largeG3ImgRhoL κ i = markWt κ (largeG3RR κ) (largeG3Sort (.inl i)) := by
  fin_cases i <;>
    simp only [largeG3ImgRhoL, largeG3RR, largeG3Sort, markWt, Equiv.coe_fn_mk, Sum.elim_inl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, Option.elim, Fin.mk_zero, Fin.mk_one, Fin.reduceFinMk] <;>
    field_simp

/-- **The G3 marks are the frozen-data marks.** -/
theorem largeG3_markPos (px pp tip pm : ℝ) (i : Fin 4) :
    ![px, pp, tip, pm] i = markPos tip ![px, pp, pm] (largeG3Sort (.inl i)) := by
  fin_cases i <;> rfl

/-! ### The one-sample laws with A.1's large image words -/

section Law

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ}
  {φ : ℂ → ℂ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {n' : ℕ} {d : Ω → SeedData n'} {A' : Ω → Set ℂ} {Wi : ℝ≥0 → Ω → ℝ} {ζi : Ω → ℝ≥0∞} {N : ℝ≥0 → Ω → ℝ}
  {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}

/-- **(Eight) The large-curve direction's one-sample law** under `Q = (M̃_S/M̃_0)·P`: image word `x⁺`, the small tip,
`x⁻` (frozen-chart marks `pp`, `tip`, `pm`) with A.1's weights `largeEightImgRhoL κ`, given the frozen-curve
hypotheses for the frozen data `(tip, ![pp, pm])` with the reduced charges `largeEightRR κ`. -/
theorem isSeedSampleLaw_largeEight_of_frzD10Hyp {pp tip pm : ℝ}
    (hH : FrzD10Hyp κ B W' a A φ (largeEightRR κ) tip ![pp, pm] S T r a₀ γ Γ lam L Tmax)
    (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ} (hBb : ∀ ω (t : ℝ≥0), t ≤ S ω → |B t ω| ≤ NB)
    (hown : ∀ ω, OwnData (d ω).W (A' ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hdW' : ∀ ω, (d ω).W' = W' ω) {VL : Fin 3 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon d S ω)
    (hW : ∀ ω t, t ≤ Scap m ω → Wi t ω = seedCapacityDriver d S t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω →
      VL i t ω = capForce d S (fun ω => frzImg (d ω).W' (d ω).a (![pp, tip, pm] i)) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ (largeEightImgRhoL κ) ![] (Wi · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζi ω)
    (Tk : ℕ → Ω → ℝ≥0) (hT : ∀ k, IsStoppingTime 𝓕 fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ S ω → (Scap k ω : ℝ) = (d ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, S ω ≤ Tk k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw (girsMeasure P (Real.sqrt κ) B S fun ω =>
        (frzDataOf κ B W' a φ (largeEightRR κ) tip ![pp, pm] ω).ell) Wi ζi VL VR N Scap m :=
  isSeedSampleLaw_of_frzD10Hyp hH hκ hB hBc hS hBb hown hda hdW' largeEightSort (pL := ![pp, tip, pm])
    (pR := ![]) (fun i => largeEight_markPos pp tip pm i) (fun j => j.elim0)
    (fun i => largeEight_markWt hκ.ne' i) (fun j => j.elim0) hSm hW hVL (fun _ j => j.elim0) hN hζ Tk hT hcap₁
    hcap₂

/-- **(G3) The large-curve direction's one-sample law** under `Q = (M̃_S/M̃_0)·P`: image word `x`, `y⁺`, the small
tip, `y⁻` (frozen-chart marks `px`, `pp`, `tip`, `pm`) with A.1's weights `largeG3ImgRhoL κ`, given the frozen-curve
hypotheses for the frozen data `(tip, ![px, pp, pm])` with the reduced charges `largeG3RR κ`. -/
theorem isSeedSampleLaw_largeG3_of_frzD10Hyp {px pp tip pm : ℝ}
    (hH : FrzD10Hyp κ B W' a A φ (largeG3RR κ) tip ![px, pp, pm] S T r a₀ γ Γ lam L Tmax)
    (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ} (hBb : ∀ ω (t : ℝ≥0), t ≤ S ω → |B t ω| ≤ NB)
    (hown : ∀ ω, OwnData (d ω).W (A' ω) (d ω).φ (S ω) (d ω).a (d ω).W') (hda : ∀ ω, (d ω).a = a ω)
    (hdW' : ∀ ω, (d ω).W' = W' ω) {VL : Fin 4 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon d S ω)
    (hW : ∀ ω t, t ≤ Scap m ω → Wi t ω = seedCapacityDriver d S t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω →
      VL i t ω = capForce d S (fun ω => frzImg (d ω).W' (d ω).a (![px, pp, tip, pm] i)) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ (largeG3ImgRhoL κ) ![] (Wi · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζi ω)
    (Tk : ℕ → Ω → ℝ≥0) (hT : ∀ k, IsStoppingTime 𝓕 fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ S ω → (Scap k ω : ℝ) = (d ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, S ω ≤ Tk k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw (girsMeasure P (Real.sqrt κ) B S fun ω =>
        (frzDataOf κ B W' a φ (largeG3RR κ) tip ![px, pp, pm] ω).ell) Wi ζi VL VR N Scap m :=
  isSeedSampleLaw_of_frzD10Hyp hH hκ hB hBc hS hBb hown hda hdW' largeG3Sort (pL := ![px, pp, tip, pm])
    (pR := ![]) (fun i => largeG3_markPos px pp tip pm i) (fun j => j.elim0)
    (fun i => largeG3_markWt hκ.ne' i) (fun j => j.elim0) hSm hW hVL (fun _ j => j.elim0) hN hζ Tk hT hcap₁
    hcap₂

end Law

end InteractingSLE.ZhanGT4.A1LargeDens
