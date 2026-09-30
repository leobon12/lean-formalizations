import QuantumZipper.Proofs.Zipper.F2Step3DensField
import QuantumZipper.Proofs.Zipper.UnifClAnchor

/-!
# F2 step (3): the `y_t`-halves of the existence and atom inputs from REG-UNIF

The unzipped `y_t` of `y = h⁰ + X` is the field `h0f κ t B X ω` of the REG-UNIF node
(`B2.h0f_eq_unzippedField`, `h0rev_add_eq`). So the `y`-halves of `Step3ExistStmt` and
`Step3NoAtomStmt` are the project statements `RegUnif.UnifGlobalStmt` and
`RegUnif.UnifAtomlessStmt` at every horizon `T` (`handoff/REG-UNIF.md`, item 2), and only the
`x_t`-halves (`x = X + α₀(−log|·|)`) remain as separate inputs. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

theorem h0f_eq_unzY {Ω : Type} (κ t : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    B2.h0f κ t B X ω = unzY κ (X ω) (drive κ B ω) t := by
  rw [B2.h0f_eq_unzippedField, unzY, B2.cfg, h0rev_add_eq]

/-- a.s. for all `t ≥ 0`, from a statement at every horizon `T = n + 1`. -/
theorem ae_forall_nonneg_of_horizons {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Q : ℝ → Ω → Prop} (h : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1), Q s ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Q t ω := by
  filter_upwards [ae_all_iff.2 h] with ω hω t ht
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hω n t ⟨ht, hn.trans (by linarith)⟩

end F2
end QuantumZipper
