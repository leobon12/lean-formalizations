import QuantumZipper.Proofs.Thm18.R18AreaNullRef
import QuantumZipper.Proofs.Thm18.R18Basic
import QuantumZipper.Proofs.Zipper.T13Hard3Realize
import QuantumZipper.Proofs.Zipper.B3dDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-AREANULL, part 5: the SLE curve carries zero quantum area (`R18.CurveAreaNullStmt`)

Sheffield (arXiv:1012.4797), §4.1 p. 48: "the measure zero set η" — η is Lebesgue-null and
independent of the canonical description `h`, hence `µ_h(η) = 0` a.s.

Proof: realize the `P_*` sample `(Y, B)` on a product extension (`WedgeUnzip.pStarRealizeStmt_holds`)
as the canonical description of an unscaled wedge `Z` with an independent Brownian `B''`, with
`avgReg Y = avgReg (canonical Z)` (so equal area measures, `Factorization.qAreaMeasure_congr`) and
driver of `B` = canonicalized driver of `B''`; conclude by `ref_curveAreaNull` and transfer back
from the product (`WedgeUnzip.ae_of_ae_prod_fst`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- **The SLE curve carries zero quantum area** (Sheffield p. 48). -/
theorem curveAreaNull_holds : CurveAreaNullStmt := by
  intro γ hγ hγ2 Ω _ P _ B Y hB hY hind
  have hs : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 < 4 := by nlinarith
  have hP : Thm13Asm.IsPStarSample (γ ^ 2) P Y B := by
    refine ⟨hκ, hκ4, ?_, hB, hind.symm⟩
    rw [hs]
    exact hY
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hInd, hB'', hIB, hae⟩ :=
    WedgeUnzip.pStarRealizeStmt_holds (γ ^ 2) P Y B hP
  rw [hs] at hA hae
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, ref_curveAreaNull hγ hγ2 hX hA hInd hB'' hIB] with ω hR h
  obtain ⟨havg, hcfg⟩ := hR
  have hdrv : drive (γ ^ 2) B ω.1 = fun r =>
      drive (γ ^ 2) B'' ω (scaleParam γ (zRef γ X' A ω) ^ 2 * r) /
        scaleParam γ (zRef γ X' A ω) := by
    have h2 := congrArg Prod.snd hcfg
    simp only at h2
    rw [← h2, B3d.canonConfig_snd_of_max (F2.drive_max (γ ^ 2) B'' ω)]
    rfl
  rw [Factorization.qAreaMeasure_congr havg, hdrv]
  exact h

end R18
end QuantumZipper
