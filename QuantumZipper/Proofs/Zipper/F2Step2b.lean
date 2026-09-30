import QuantumZipper.Proofs.Zipper.F2LocalSteps
import QuantumZipper.Proofs.Zipper.B5LocF1Side
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.RS.RealAlive

/-!
# F2 step (2b): lengths agree for `X + α₀(−log|·|)` at small times, from the wedge

Theorem 1.3, node F2, step (2b) (`F2LocalSteps.lean`):
`Step2bStmt := UnscaledLenAgree → LogSingLocLenAgree`. Source: Sheffield, *Conformal weldings of
random surfaces: SLE and the quantum gravity zipper*, arXiv:1012.4797, §5.4 (proof of Theorem 1.3,
pp. 70–72: "restricted to `B₁`, the wedge is a free field plus `α(−log|·|)`, up to an additive
constant, and the lengths of `η[0,t]` for small `t` only see the field near `0`") and §1.6 (the
wedge inside `B₁`).

## Route (own bookkeeping; the paper gives no details)

Instead of transferring the (uncountable-time) event `SmallTimeAgree` through an equality of laws
(which would need a measurable version of the event in (field data, path)), the wedge is built
**pathwise** on a product extension `Ω × Ω₂` of the target space (`WedgeLogCouplingStmt`):
inside `B(0, 1/2)` its circle data are those of `X + α₀(−log|·|)` up to an additive constant, and
its driver is the target driver. A.s. statements on `P.prod Q` about the first coordinate descend
to `P` with no measurability requirement (`ae_of_ae_prod_fst`). Then:

* B5 locality (`B5.unzipLengths_eq_of_dyCircAgree_ball`) with the side-image bound
  (`B5.sideSmallStmt`, `a = 1/16`) transfers the equality `L⁻_t = L⁺_t` at every small time from
  the wedge to the shifted target field; if the target unzipped field has no boundary limit, both
  of its lengths are the junk value `0` (`agree_of_not_exists_limit`);
* the additive constant is removed by `AddConstAgreeStmt` (rule: both lengths are multiplied by
  `e^{γc/2}`, `Cor15GoodConst.qBoundaryMeasure_addConst_ae`, once the unzipped field is regular);
* time `0` is trivial (`O^±_0 = 0`).

## Inputs (open, exact statements below)
* `WedgeLogCouplingStmt`: the pathwise coupling (reverse direction of
  `WedgeBdry.wedge_ae_of_logSing`, with the driver included).
* `WedgeUnzipLimitAllStmt`: a.s. the unzipped wedge field has a global boundary limit at every
  time `t > 0` (without it `UnscaledLenAgree` could hold through the junk value `0`).
* `AddConstAgreeStmt`: a.s. for the target configuration, agreement of the lengths is invariant
  under additive constants.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## The inputs -/

/-- **Pathwise wedge/log-singularity coupling with the driver** (Sheffield §1.6, §5.4; B4(b)).
Given a free field `X` and an independent Brownian motion `B` on `(Ω, P)`, there is a product
extension `(Ω × Ω₂, P ⊗ Q)` carrying a free field `X'` and an `α₀`-wedge radial process `A`,
independent of each other and jointly independent of `B ∘ fst`, such that a.s. the wedge field
`wedgeField (lateralPart X') A Q` has, on all small dyadic circles centred in `B(0, 1/2)`, the
same values as `X + α₀(−log|·|)` plus a (random) additive constant `C`. (Construction: `A` on
`t ≥ 0` from the radial part of `X`, `X'` = lateral part of `X` plus a fresh radial part.) -/
def WedgeLogCouplingStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (Q : Measure Ω₂) (_ : IsProbabilityMeasure Q)
      (X' : Ω × Ω₂ → FieldSample) (A : ℝ → Ω × Ω₂ → ℝ) (C : Ω × Ω₂ → ℝ) (j₀ : ℕ),
      IsFreeGFFModConstH X' (P.prod Q) ∧
      IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A (P.prod Q) ∧
      IndepFun X' (fun ω t => A t ω) (P.prod Q) ∧
      IsBrownianReal (fun t (ω : Ω × Ω₂) => B t ω.1) (P.prod Q) ∧
      IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf (fun t (ω : Ω × Ω₂) => B t ω.1))
        (P.prod Q) ∧
      ∀ᵐ ω ∂(P.prod Q), B5.DyCircAgree
        (wedgeField (lateralPart (X' ω)) (fun t => A t ω) (Qc (Real.sqrt κ)))
        (addConst (X ω.1 + logSingField κ) (C ω)) (Metric.ball 0 (1 / 2)) j₀

/-! ## Deterministic lemmas -/

/-- At time `0` the right side image is `0` (own elementary proof, mirror of
`B5.sideImages_fst_zero_time`). -/
theorem sideImages_snd_zero_time {W : ℝ → ℝ} (hW0 : W 0 = 0) : (sideImages W 0).2 = 0 := by
  show limUnder (𝓝[>] (0 : ℝ)) (fun x : ℝ => (fwdMap W 0 x).re) = 0
  refine Tendsto.limUnder_eq ?_
  have h : (fun x : ℝ => (fwdMap W 0 x).re) =ᶠ[𝓝[>] (0 : ℝ)] fun x => x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [B5.fwdMap_zero_time W (by rw [hW0]; exact_mod_cast (ne_of_gt hx)), hW0]
    simp
  exact (tendsto_congr' h).2 (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0))

/-- A.s. statements about the first coordinate under `P ⊗ Q` hold `P`-a.s. (no measurability
needed; `Measure.prod_prod` holds for all sets). -/
theorem ae_of_ae_prod_fst {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {Q : Measure Ω₂} [IsProbabilityMeasure Q] {p : Ω → Prop}
    (h : ∀ᵐ ω ∂(P.prod Q), p ω.1) : ∀ᵐ ω ∂P, p ω := by
  rw [ae_iff] at h ⊢
  have e : {a : Ω × Ω₂ | ¬ p a.1} = {ω | ¬ p ω} ×ˢ (univ : Set Ω₂) := by
    ext a; simp
  rwa [e, Measure.prod_prod, measure_univ, mul_one] at h

/-! ## Step (2b) -/

end F2
end QuantumZipper
