/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CertInner
import InteractingSLE.Spec.Sec7.R6CertOuter
import InteractingSLE.Spec.Sec7.PocketStopMarkedLaw
import InteractingSLE.Spec.Sec7.PocketWordPerQSigma

/-!
# The four walls of R.6: the outer pair and the nested pair

PROVE-R6-CERT. R.6 compares the outer pocket of the walls `(R, L)` with a nested pocket of the walls `(R', L')`
(supplement p. 476). The joint walls–hull law uses the four walls' full histories `fullHist ![R, L, R', L']` as
information. This file records the bookkeeping: each pair's walls σ-algebra satisfies the marked-stop initial bound
for the four-wall information, and the joined walls are the walls of the four-wall family.

* `comap_fullHist_le_four_left`, `comap_fullHist_le_four_right`;
* **`wallsSigma_le_four_left`**, **`wallsSigma_le_four_right`**;
* `walls_union_eq_four`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cert

open PocketStopWalls PocketWordPerQ PocketStopMarked

variable {Ω : Type*}

/-- The outer pair's histories are read off the four walls' histories. -/
theorem comap_fullHist_le_four_left (R L R' L' : Ω → ℝ≥0 → ℂ) :
    MeasurableSpace.comap (fullHist ![R, L]) inferInstance ≤
      MeasurableSpace.comap (fullHist ![R, L, R', L']) inferInstance := by
  have e : fullHist ![R, L] = (fun f : Fin 4 → Sec6.Hist => ![f 0, f 1]) ∘ fullHist ![R, L, R', L'] := by
    funext ω i
    fin_cases i <;> rfl
  have hf : Measurable (fun f : Fin 4 → Sec6.Hist => ![f 0, f 1]) := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact measurable_pi_apply 0
    · exact measurable_pi_apply 1
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hf.comap_le

/-- The nested pair's histories are read off the four walls' histories. -/
theorem comap_fullHist_le_four_right (R L R' L' : Ω → ℝ≥0 → ℂ) :
    MeasurableSpace.comap (fullHist ![R', L']) inferInstance ≤
      MeasurableSpace.comap (fullHist ![R, L, R', L']) inferInstance := by
  have e : fullHist ![R', L'] = (fun f : Fin 4 → Sec6.Hist => ![f 2, f 3]) ∘ fullHist ![R, L, R', L'] := by
    funext ω i
    fin_cases i <;> rfl
  have hf : Measurable (fun f : Fin 4 → Sec6.Hist => ![f 2, f 3]) := by
    refine measurable_pi_iff.2 fun i => ?_
    fin_cases i
    · exact measurable_pi_apply 2
    · exact measurable_pi_apply 3
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hf.comap_le

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The outer pair's walls σ-algebra satisfies the marked-stop bound for the four-wall information.** -/
theorem wallsSigma_le_four_left (hX : IsMeasurableKilledDriving W VL VR ζ) (R L R' L' : Ω → ℝ≥0 → ℂ) :
    wallsSigma P R L ≤
      MeasurableSpace.comap (fullHist ![R, L, R', L']) inferInstance ⊔ drivingFiltration P hX 0 :=
  le_drivingFiltration_zero_of_le hX (sup_le_sup_right (comap_fullHist_le_four_left R L R' L') _)

/-- **The nested pair's walls σ-algebra satisfies the marked-stop bound for the four-wall information.** -/
theorem wallsSigma_le_four_right (hX : IsMeasurableKilledDriving W VL VR ζ) (R L R' L' : Ω → ℝ≥0 → ℂ) :
    wallsSigma P R' L' ≤
      MeasurableSpace.comap (fullHist ![R, L, R', L']) inferInstance ⊔ drivingFiltration P hX 0 :=
  le_drivingFiltration_zero_of_le hX (sup_le_sup_right (comap_fullHist_le_four_right R L R' L') _)

omit mΩ in
/-- The joined walls of the two pairs are the walls of the four-wall family. -/
theorem walls_union_eq_four (R L R' L' : Ω → ℝ≥0 → ℂ) :
    (fun ω => negInv '' (range (R ω) ∪ range (L ω)) ∪ negInv '' (range (R' ω) ∪ range (L' ω))) =
      fun ω => negInv '' ⋃ i, range ((![R, L, R', L'] : Fin 4 → Ω → ℝ≥0 → ℂ) i ω) := by
  funext ω
  rw [← image_union]
  congr 1
  ext z
  simp only [mem_union, mem_iUnion, Fin.exists_fin_succ, Fin.exists_fin_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  constructor
  · rintro ((h | h) | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rintro (h | h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact h.elim

end InteractingSLE.Sec7.R6Cert
