import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d
import QuantumZipper.Proofs.Zipper.B5LocF1Assembly

/-!
# D29 (wedge unzipping), part 4: B5 (R1) from the wedge core W-G

`B5.WedgeUnzipLimitStmt γ α κ` (R1 of the B5 locality assembly, `B5LocF1Assembly.lean`) at the
wedge parameter `α = γ − 2/γ` follows from `WedgeUnzip.WedgeGoodAllStmt`: the three sources
`X, A, B` are mutually independent (`iIndep (srcSigma X A B)`), hence `X ⊥ A` and `(X, A) ⊥ B`,
which is the setting of W-G; goodness gives the vague limit of the dyadic boundary
approximations (`LQGMeas.tendsto_bdryApprox_of_good`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

open F1

/-- Pairwise forms of the mutual independence of the three sources. -/
theorem indep_pairs_of_srcSigma {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} (hXm : Measurable X)
    (hAm : ∀ t, Measurable (A t)) (hBm : ∀ t, Measurable (B t))
    (hind : iIndep (srcSigma X A B) P) :
    IndepFun X (fun ω t => A t ω) P ∧
      IndepFun (fun ω => (X ω, fun t => A t ω)) (pathOf B) P := by
  refine ⟨hind.indep (i := 0) (j := 1) (by decide), ?_⟩
  have hle := srcSigma_le hXm hAm hBm
  have h := indep_iSup_of_disjoint hle hind (S := {0, 1}) (T := {2})
    (by simp [Set.disjoint_iff, Fin.ext_iff])
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · refine le_trans (le_of_eq (MeasurableSpace.comap_prodMk X (fun ω t => A t ω))) ?_
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({0, 1} : Set (Fin 3))) => srcSigma X A B i) 0
        (by simp) le_rfl
    · exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({0, 1} : Set (Fin 3))) => srcSigma X A B i) 1
        (by simp) le_rfl
  · exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({2} : Set (Fin 3))) => srcSigma X A B i) 2
      (by simp) le_rfl

end WedgeUnzip
end QuantumZipper
