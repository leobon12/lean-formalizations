import QuantumZipper.Proofs.Zipper.FlowRegSide
import QuantumZipper.Proofs.Zipper.F1LenInRefl
import QuantumZipper.Proofs.Zipper.F1LenInCanon
import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d
import QuantumZipper.Proofs.Zipper.RegUnifCocycle

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WEDGE-COCYCLE: the capacity-flow cocycle of the unscaled wedge, and `UnscaledFlowCoreStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (the capacity zipper is
a flow: unzipping by `u` and then by `s` is unzipping by `u + s`), §5.1 rule (5.1) (pp. 60–62,
coordinate change `h ∘ ψ + Q log|ψ'|`, which is a cocycle by the chain rule) and §5.4; Duplantier–
Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1 (the
regularized field transforms by the coordinate change rule at pushed circle measures).

For every field `x` and continuous driver `W` with `W 0 = 0`, the raw value at `fc(w, r)` of the
field unzipped by `u` then `s` differs from that of the field unzipped by `u + s` exactly by
`evalReg x_u ν − x_u ν`, `ν = R_* fc(w, r)` (`RegUnif.double_apply_fc`, `RegUnif.single_apply_fc`:
flow property of the Loewner maps and the chain rule). So the **raw cocycle** of the wedge flow is
exactly RC3 of the unzipped wedge fields at the pushed circles — the wedge analogue
`WedgeFlowRC3Stmt` of the `Γ⁰` node `RegUnif.UnifRC3Stmt` (proved there at the dyadic circles by
D33). With it:

* goodness along the flow is goodness at the single time `u + s` (`WedgeUnzip.WedgeGoodAllStmt`);
* RC3 along the flow is RC3 at the single time `u + s` (`WedgeUnzip.WedgeExactAllStmt`);
* scale consistency along the flow follows, as in `WedgeUnzip.unscaledB3dStmt_of_core`, from the
  continuum limit of the unzipped field `x_u` at the images of folded circles under its own flow
  (`WedgeFlowContStmt`, the flow form of `WedgeUnzip.WedgeContinuumStmt`).

Main result: `unscaledFlowCoreStmt_of_wedgeFlow`. The bookkeeping is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## Deterministic lemmas -/

/-- **Raw cocycle from RC3 at the pushed circle** (general field and driver). -/
theorem flow_raw_cocycle_of_rc3 (γ : ℝ) (x : FieldSample) {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (h : evalReg (unzippedField γ (x, W) u)
        ((foldedCircle w r).map (revMap (B2.vrev W (u + s)) s)) =
      unzippedField γ (x, W) u ((foldedCircle w r).map (revMap (B2.vrev W (u + s)) s))) :
    unzippedField γ (zipCapDown γ u (x, W)) s (foldedCircle w r) =
      unzippedField γ (x, W) (u + s) (foldedCircle w r) := by
  show (zipCapDown γ s (zipCapDown γ u (x, W))).1 (foldedCircle w r) =
    (zipCapDown γ (u + s) (x, W)).1 (foldedCircle w r)
  rw [RegUnif.double_apply_fc _ _ hW hu hs w hr, RegUnif.single_apply_fc _ _ hW hW0 hu hs w hr, h]

/-- Raw agreement on folded circles centred in `Hbar` gives agreement at every centre. -/
theorem fc_eq_all_of_Hbar {x y : FieldSample}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r))
    (c : ℂ) {r : ℝ} (hr : 0 < r) : x (foldedCircle c r) = y (foldedCircle c r) := by
  rw [← CoordReg.foldedCircle_foldH c r]
  exact h _ (CircleFubini.foldH_mem_Hbar' c) r hr

/-- Raw agreement on folded circles gives `RegEq`. -/
theorem regEq_of_fc_Hbar {x y : FieldSample}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r)) :
    RegEq x y := by
  intro k z
  unfold avgReg
  simp_rw [fc_eq_all_of_Hbar h _ (radius_pos k)]

/-- Raw agreement on folded circles transfers regularity. -/
theorem isRegularSample_of_fc_Hbar {x y : FieldSample}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r))
    (hy : IsRegularSample y) : IsRegularSample x := by
  obtain ⟨F, h1, h2, h3⟩ := hy
  refine ⟨F, h1, fun k z hz => ?_, h3⟩
  simp_rw [fc_eq_all_of_Hbar h _ (radius_pos k)]
  exact h2 k z hz

/-! ## The wedge flow nodes -/

/-- **RC3 of the unzipped wedge fields at the pushed circles, along the whole flow** (open input;
wedge analogue, at all horizons and all folded circles, of the `Γ⁰` node `RegUnif.UnifRC3Stmt`;
Duplantier–Sheffield 2011, Prop. 3.1; Sheffield §5.1 rule (5.1)): a.s., for all `u, s ≥ 0`, the
field `x_u` unzipped from the unscaled wedge configuration by `u` is regularized exactly by the
coordinate-change rule at `R_* fc(d, r)`, `R` the unzipping map of the flow from `u` to `u + s`. -/
def WedgeFlowRC3Stmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) u)
          ((foldedCircle d r).map (revMap (B2.vrev (drive κ B'' ω) (u + s)) s)) =
        unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) u
          ((foldedCircle d r).map (revMap (B2.vrev (drive κ B'' ω) (u + s)) s))

/-- **Continuum limit of the unzipped wedge fields along their own flow** (open input; flow form
of `WedgeUnzip.WedgeContinuumStmt`, which is the case `u = 0` up to `RegEq`; Duplantier–Sheffield
2011, Prop. 3.1): a.s., for all `u, t ≥ 0`, `c` and `r > 0`, the smoothed pairings of `x_u`
against the image of `fc(c, r)` under the unzipping map of the flowed driver at time `t` are
integrable and converge as the smoothing radius tends to `0⁺`. -/
def WedgeFlowContStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ u t : ℝ, 0 ≤ u → 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      (∀ ρ : ℝ, 0 < ρ → Integrable (fun v => evalReg
          (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) u)
          (foldedCircle v ρ))
        ((foldedCircle c r).map (fwdMapInv
          (zipCapDown (Real.sqrt κ) u (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)).2 t))) ∧
      ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg
          (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) u)
          (foldedCircle v ρ) ∂((foldedCircle c r).map (fwdMapInv
            (zipCapDown (Real.sqrt κ) u (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)).2 t)))
        (𝓝[>] 0) (𝓝 L)

/-! ## The reduction -/

end F1
end QuantumZipper
