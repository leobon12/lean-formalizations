import QuantumZipper.Proofs.Thm18.LWExcDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 3: truncation of the half-line in `excR`

`excR h (Iic 0) = ⨆ N, excR h (Ioo (-N) 0)`: the excursion flux into the negative half-line is the
limit of the fluxes into bounded intervals (monotone convergence). Used to apply the interval
symmetry `fl3Sym_excR_symm` (bounded intervals) to `FLImageSumBoundStmt`'s half-line
`{x | x a ≤ 0}`. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

theorem fl3_excR_Iic_eq_iSup (h : ℂ → ℝ) :
    excR h (Iic 0) = ⨆ N : ℕ, excR h (Ioo (-(N : ℝ)) 0) := by
  unfold excR
  have hae : (Iio (0 : ℝ) : Set ℝ) =ᵐ[volume] Iic 0 := Iio_ae_eq_Iic
  rw [← setLIntegral_congr hae]
  have hU : Iio (0 : ℝ) = ⋃ N : ℕ, Ioo (-(N : ℝ)) 0 := by
    ext x
    simp only [mem_Iio, mem_iUnion, mem_Ioo]
    constructor
    · intro hx
      obtain ⟨N, hN⟩ := exists_nat_gt (-x)
      exact ⟨N, by linarith, hx⟩
    · rintro ⟨N, -, hx⟩; exact hx
  rw [hU]
  refine setLIntegral_iUnion_of_directed _ ?_
  intro i j
  refine ⟨max i j, ?_, ?_⟩
  · exact Ioo_subset_Ioo_left (neg_le_neg (by exact_mod_cast le_max_left i j))
  · exact Ioo_subset_Ioo_left (neg_le_neg (by exact_mod_cast le_max_right i j))

end FieldLawler
end QuantumZipper
