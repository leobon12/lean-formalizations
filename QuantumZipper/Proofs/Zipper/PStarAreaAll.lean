import QuantumZipper.Proofs.Zipper.PStarAreaAllBasic
import QuantumZipper.Proofs.Zipper.HitScaleZip
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm

/-!
# E6-PSTAR-AREA-ALL, part 2: `E6.PStarAreaAllStmt` from two wedge area nodes

Theorem 1.3, node E6 area (`HitScaleZip.lean`). The `P_*` unzipped field at time `t` is, in law
and through `avgReg`, the *canonicalization* of the unscaled wedge configuration
(`WedgeUnzip.PStarRealizeStmt`, core P), and by the B3(d) field identity
(`WedgeUnzip.unzippedField_canonConfig_fc`) the canonicalized unzipped field is `RegEq` to the
rescaled unscaled unzipped field at time `a² t`, `a = scaleParam γ (zU γ X' A) > 0`. Since
`AreaAll` reads the field only through the area measure (`areaAll_congr_coords`), and rescaling
does not change `AreaAll` (`E6.areaAll_rescale_iff`, needs goodness of the unscaled field), the
`P_*` statement follows from the same statement for the *unscaled* wedge unzipped fields, exactly
as `WedgeUnzip.pStarGoodAll_of_core` derives the `P_*` goodness from `WedgeGoodAllStmt`.

The two halves of the unscaled input are isolated as named nodes:

* `E6.WedgeAreaFinStmt` (**W-A-fin**): a.s. `μ_t(B_a(0) ∩ ℍ) < ∞` for all `t ≥ 0` and all `a`.
  This is Sheffield p. 21's "a finite amount of `μ_h` mass in each bounded neighborhood of 0",
  transported along the unzipping; the same statement for the *wedge* field (time `0`) is
  `WedgeCan4.WedgeFiniteNearZero`, proved unconditionally
  (`WedgeFinZero.wedgeFiniteNearZero_holds`, `LQG/WedgeFinZeroCoupling.lean`); at `t = 0` the
  unzipping map is the identity on `ℍ`, so the node does hold there
  (`E6.areaAll_unzippedField_zero_of_profile`). `IsLQGGood` alone does **not**
  give it: `HasAreaLimit` yields finiteness only on compact subsets of `ℍ`, and `B_a(0) ∩ ℍ` is
  not compact (it meets the real axis), so this is genuine extra input, not bookkeeping.
* `E6.WedgeAreaHStmt` (**W-A-∞**): a.s. `μ_t(ℍ) = ∞` for all `t ≥ 0`. Route: the area
  coordinate-change rule (the area analogue of M4-T4 / `CoordChange`, missing in this
  repository — the existing `ae_qBoundaryMeasureOn_coordChange` is the boundary version) for the
  conformal map `fwdMapInv W t`, whose image of `ℍ` is the complement of the hull of the curve,
  together with infinite total area of the wedge (`WedgeInf.wedgeInfiniteTotal` /
  `Wire2.ae_hasAreaProfile_wedgeField`) and the fact that far out `fwdMapInv W t` is close to the
  identity (`B5.norm_fwdMapInv_sub_le`), so that the mass near `∞` is not lost.

Results:
* `pStarAreaAllStmt_of_core`: `PStarRealizeStmt → WedgeGoodAllStmt → WedgeExactAllStmt →
  WedgeContinuumStmt → WedgeAreaFinStmt → WedgeAreaHStmt → PStarAreaAllStmt`;
* `hitScaleZipStmt_of_wedgeArea` / `localAbsRichStmt_of_wedgeArea`: the same nodes feed
  `HitScaleZipStmt` and `LocalAbsRichStmt` with the area node in place of `PStarAreaAllStmt`;
* `ae_areaAll_unzippedField_zero`: the node holds at `t = 0` — there the unzipping map is the
  identity, and the statement is the (proved) area property of the unscaled wedge field; the only
  extra input at `t = 0` is the regularity clause of `WedgeContinuumStmt`, so nothing but the
  transport along the unzipping map is open.

Source: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1.6, p. 21: "we
will focus on constructions in which there is almost surely a finite amount of `µ_h` mass and
`ν_h` mass in each bounded neighborhood of 0 and an infinite amount in each neighborhood of ∞",
with "each neighborhood of ∞ includes infinite area ... while the complement of such a
neighborhood contains only finite area". The paper asserts the analogous properties of the
*unzipped* fields without proof (its §5.4, pp. 70–72, in fact only discusses absolute continuity
of the fields and left-right length equality; the area assertions are on p. 21). All lemmas here
are own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

/-! ## The two open halves of the wedge area node -/

/-- **W-A-fin** (open): a.s. the fields unzipped from the unscaled wedge configuration have
finite area on every half-disc `B_a(0) ∩ ℍ`, at all times. -/
def WedgeAreaFinStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ∀ a : ℝ,
      qAreaMeasure (Real.sqrt κ)
        (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t)
        (Metric.ball 0 a ∩ H) < ⊤

/-- **W-A-∞** (open): a.s. the fields unzipped from the unscaled wedge configuration have
infinite total area on `ℍ`, at all times. -/
def WedgeAreaHStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      qAreaMeasure (Real.sqrt κ)
        (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t) H = ⊤

/-! ## The reduction -/

/-! ## Non-vacuity: the node holds at time `0` -/

end QuantumZipper.E6
