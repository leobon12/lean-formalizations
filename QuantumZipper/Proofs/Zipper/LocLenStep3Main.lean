import QuantumZipper.Proofs.Zipper.LocLenStep3Weld
import QuantumZipper.Proofs.Zipper.LocLenStep3Dens
import QuantumZipper.Proofs.Zipper.LocLenStep3Arcs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R7a: F2 step (3) with open arcs (`Step3ArcStmt`)

`step3Arc_of_local : Step3LocalDensityArcStmt → Step3WeldArcStmt → Step3ArcStmt`, the open-arc
copy of `F2.step3_of_inputs`/`F2.step3_of_local` (F2Step3.lean). With `y = h⁰ + X = x + γ log|·|`
(`F2.h0rev_add_eq`), the open-arc lengths of `y_t` are the masses of the open arcs for the local
limit `νy = |F_t|^{γ²/2} νx` on `(offSet W t)ᶜ` (rule (5.1), Sheffield arXiv:1012.4797 §5.1 and
p. 70), and welding invariance with `g = |·|^{γ²/2}` (Sheffield §5.4 pp. 70–72) makes them equal.
No endpoint bookkeeping is needed for open arcs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **F2 step (3) with open arcs** from the local rule (5.1) and welding invariance. -/
theorem step3Arc_of_local (hD : Step3LocalDensityArcStmt) (hW : Step3WeldArcStmt) :
    Step3ArcStmt := by
  intro hL κ hκ hκ4
  obtain ⟨t₀, M, ht₀, hM, hL'⟩ := hL κ hκ hκ4
  refine ⟨t₀, M, ht₀, hM, ?_⟩
  intro Ω _ P _ B X hB hX hind
  filter_upwards [hL' P B X hB hX hind, hD κ hκ hκ4 P B X hB hX hind,
    hW κ hκ hκ4 P B X hB hX hind] with ω hLω hDω hWω
  intro t ht htt₀ htM
  obtain ⟨h1, h2, hrx, hry, νx, νy, hx, hy, hd⟩ := hDω t ht
  have key := hWω t₀ M hLω t ht htt₀ htM _ (F2.measurable_logDens (Real.sqrt κ))
  rw [qBoundaryMeasureOn_eq_of_hasBdryLimitOn hrx (isClosed_offSet _ t).isOpen_compl hx] at key
  rw [F2.h0rev_add_eq]
  simp only [unzipLengthsArc]
  rw [show unzippedField (Real.sqrt κ) ((X ω + F2.logSingField κ) + F2.gammaLog κ, drive κ B ω) t
      = F2.unzY κ (X ω) (drive κ B ω) t from rfl,
    arcLen_eq_of_hasBdryLimitOn hry hy (step3_Ioo_subset_left h2),
    arcLen_eq_of_hasBdryLimitOn hry hy (step3_Ioo_subset_right h1), hd,
    withDensity_apply _ measurableSet_Ioo, withDensity_apply _ measurableSet_Ioo]
  exact key

/-- **F2 step (3) with open arcs** from the `Γ⁰` stage geometry, the offset merging input and base
finiteness X1. -/
theorem step3Arc_of_gammaArcs (hG : Step3GammaArcsStmt) (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hX1 : BaseFin.BaseFiniteStmt) : Step3ArcStmt :=
  step3Arc_of_local (step3LocalDensityArc_of_yMergeOffTip hYO)
    (step3WeldArc_of_parts hG (step3InvDensityArc_of_yMergeOffTip hYO) hX1)

/-- **F2 step (3) with open arcs, closed form** (no TipCore, no TIP-X, no global goodness at
variable times): from the offset merging input and base finiteness X1. -/
theorem step3Arc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hX1 : BaseFin.BaseFiniteStmt) : Step3ArcStmt :=
  step3Arc_of_gammaArcs step3GammaArcs_holds hYO hX1

end LocLen
end QuantumZipper
