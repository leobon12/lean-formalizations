import QuantumZipper.Proofs.Zipper.ZipLenField
import QuantumZipper.Proofs.Zipper.WedgeXExact
import QuantumZipper.Proofs.Zipper.HitScaleZip
import QuantumZipper.Proofs.Zipper.UnifD33Close
import QuantumZipper.Proofs.Thm18.G4ZipUp3LogDeriv
import QuantumZipper.Proofs.Thm18.G4ZipUp3SurMeas
import QuantumZipper.Proofs.Thm18.G4WeldUniq
import QuantumZipper.Proofs.Thm18.G4ZipRegCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN: `B3d.ZipLenInputsStmt` from the `Γ⁰` nodes

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (capacity zipper as a
flow), §1.6 ((1.8), canonical description) and §5.1 (rule (5.1), pp. 60–62). Own elementary
bookkeeping (the paper uses these facts without proof), following the `P_*` pattern
`F1.pStarZipLenInputs_of_core` / `F1.pStarShiftRegStmt_of_core`.

The collided configuration is `c = zipCapDown γ u 𝒵`, `𝒵 = (h⁰ + X, √κ B)`; its field is the
unzipped `Γ⁰` field `y_u = F2.unzY` (`F2.h0rev_add_eq`). The five clauses of
`ZipLenInputsStmt`:

* **side limits** (clause 3): deterministic, `F1.zipCapDown_side_limits`;
* **goodness** (clause 4): `WedgeUnzip.YGoodAllStmt` at time `u + t`, transported to the field of
  `c` unzipped by `t` through the proved field cocycle `RegUnif.capCocycleRegStmt_holds` (RegEq +
  raw convergence give regularity, and goodness reads only `avgReg`);
* **scale positivity** (clauses 1, 2): by the cocycle, the scale of `c` unzipped by `t`, plus `k`,
  is that of `y_{u+t} + k`; it is positive by `E6.scaleParam_pos_of_area` once `y_{u+t}` has
  finite area on half-discs and infinite total area (`YAreaAllStmt`, the `Γ⁰` analogue of
  `E6.PStarAreaAllStmt`);
* **field identity** (clause 5): `ZipLen.zipLen_field_pt`, from `YGoodAllStmt`, `YExactAllStmt`
  and the two `Γ⁰` flow nodes `YFlowRC3Stmt`, `YFlowContStmt` (the `Γ⁰` analogues of
  `F1.XFlowRC3Stmt`, `F1.XFlowContStmt`).

Main result: `zipLenInputsStmt_of_y`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

/-! ## The `Γ⁰` nodes used -/

/-- **(`Γ⁰` area at all times; open.)** A.s., for all `t ≥ 0`, the quantum area measure of the
unzipped `Γ⁰` field `y_t` is finite on every half-disc `B_a(0) ∩ ℍ` and has infinite total mass
(the `Γ⁰` analogue of `E6.PStarAreaAllStmt`). -/
def YAreaAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (∀ a : ℝ, qAreaMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t)
          (Metric.ball 0 a ∩ H) < ⊤) ∧
        qAreaMeasure (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t) H = ⊤

/-- **(`Γ⁰` flow node, RC3; open.)** A.s., for all `u, s ≥ 0` and folded circles centred in `ℍ̄`,
`y_u` is regularized exactly at `R_* fc(d, r)`, `R` the unzipping map of the flow from `u` to
`u + s` (the `Γ⁰` analogue of `F1.XFlowRC3Stmt`; at all circles and horizons, of the proved
`RegUnif.UnifRC3Stmt`). -/
def YFlowRC3Stmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (F2.unzY κ (X ω) (drive κ B ω) u)
          ((foldedCircle d r).map (revMap (B2.vrev (drive κ B ω) (u + s)) s)) =
        F2.unzY κ (X ω) (drive κ B ω) u
          ((foldedCircle d r).map (revMap (B2.vrev (drive κ B ω) (u + s)) s))

/-- **(`Γ⁰` flow node, continuum limit; open.)** A.s., for all `u, t ≥ 0`, `c` and `r > 0`, the
smoothed pairings of `y_u` against the image of `fc(c, r)` under the unzipping map of the shifted
driver at time `t` converge as the smoothing radius tends to `0⁺` (the `Γ⁰` analogue of
`F1.XFlowContStmt`). -/
def YFlowContStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ u t : ℝ, 0 ≤ u → 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (F2.unzY κ (X ω) (drive κ B ω) u)
          (foldedCircle v ρ) ∂((foldedCircle c r).map (fwdMapInv (F1.shiftDrv (drive κ B ω) u) t)))
        (𝓝[>] 0) (𝓝 L)

/-! ## Deterministic lemmas -/

/-- `RegEq` to a regular sample plus raw convergence at every centre gives regularity. -/
theorem isRegularSample_of_regEq_raw {x y : FieldSample} (hx : LocalRule.RawConverges x univ)
    (h : RegEq x y) (hy : IsRegularSample y) : IsRegularSample x := by
  obtain ⟨F, h1, h2, h3⟩ := hy
  refine ⟨F, h1, fun k z hz => ?_, h3⟩
  obtain ⟨l, hl⟩ := hx k z trivial
  have e1 : avgReg x k z = l := hl.limUnder_eq
  have e2 : avgReg y k z = F (z, radius k) := (h2 k z hz).limUnder_eq
  rw [← e1, h k z, e2] at hl
  exact hl

/-- The field of the `Γ⁰` configuration unzipped by `t` is `F2.unzY`. -/
theorem unzippedField_cfg_eq (κ t : ℝ) (x : FieldSample) (W : ℝ → ℝ) :
    unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) t = F2.unzY κ x W t := by
  rw [F2.unzY, F2.h0rev_add_eq]

/-! ## The reduction -/

variable {Ω : Type} [MeasurableSpace Ω]

end ZipLen
end B3d
end QuantumZipper
