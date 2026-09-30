import QuantumZipper.Proofs.Zipper.XFlowRC3Det

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3: the regularized-side continuity from a uniform-convergence node

The regularized side `evalReg x_u ν_p` is the limit of `Φ_j(p) = ∫ avgReg x_u j dν_p`
(`evalReg` is this `limUnder`). If a.s. every `Φ_j` is continuous on `flowPar` and `Φ_j`
converges locally uniformly on `flowPar`, the limit is continuous (own bookkeeping; mathlib's
`TendstoLocallyUniformlyOn.continuousOn`). This is the five-parameter form
`(u, s, Re d, Im d, r)` of the D33 uniform-Cauchy node `RegUnif.UnifUCStmt` (which is the same
statement for the `Γ⁰` field, over `(u, s)` only, at the fixed dyadic circles), i.e. a
Kolmogorov–Čentsov statement (Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)) for the family `Φ_j` in the
circle parameters as well; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1.

* `xFlowRegContStmt_of_uc : XFlowPhiContStmt → XFlowUCStmt → XFlowRegContStmt`;
* `xFlowRC3Stmt_of_uc`, `xExactAll_of_uc`: hence `XFlowRC3Stmt` and X-X.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- The regularized pairings `Φ_j(p) = ∫ avgReg x_u j dν_p`. -/
def flowPhi (κ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (j : ℕ) (p : ℝ × ℝ × ℂ × ℝ) : ℝ :=
  ∫ z, avgReg (F2.unzX κ x W p.1) j z ∂flowNu W p

/-- **(Continuity of the regularized pairings.)** A.s., every `Φ_j` is continuous on `flowPar`
(a consequence of a witness of `x_u` jointly continuous in `(u, w, ρ)`, cf. the `Γ⁰` JointMod
witness `RegUnif.ae_exists_joint_witness` and `RegUnif.continuousOn_integral_comp_R`). -/
def XFlowPhiContStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ j : ℕ, ContinuousOn (flowPhi κ (X ω) (drive κ B ω) j) flowPar

/-- **(Five-parameter uniform convergence, D33 form.)** A.s., `Φ_j` converges locally uniformly
on `flowPar` as `j → ∞`. -/
def XFlowUCStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoLocallyUniformlyOn (fun j => flowPhi κ (X ω) (drive κ B ω) j) L atTop flowPar

/-- **`XFlowRegContStmt` from continuity of the `Φ_j` and their locally uniform convergence.** -/
theorem xFlowRegContStmt_of_uc (hC : XFlowPhiContStmt) (hU : XFlowUCStmt) :
    XFlowRegContStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [hC κ hκ hκ4 P B X hB hX hind, hU κ hκ hκ4 P B X hB hX hind] with ω hc hL
  obtain ⟨L, hL⟩ := hL
  have hLc : ContinuousOn L flowPar :=
    hL.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall hc))
  refine hLc.congr fun p hp => ?_
  show limUnder atTop (fun j => flowPhi κ (X ω) (drive κ B ω) j p) = L p
  exact (hL.tendsto_at hp).limUnder_eq

/-- **`XFlowRC3Stmt` from `XFlowPhiContStmt` and `XFlowUCStmt`.** -/
theorem xFlowRC3Stmt_of_uc (hC : XFlowPhiContStmt) (hU : XFlowUCStmt) : XFlowRC3Stmt :=
  xFlowRC3Stmt_of_regCont' (xFlowRegContStmt_of_uc hC hU)

/-- **X-X from `XFlowPhiContStmt` and `XFlowUCStmt`.** -/
theorem xExactAll_of_uc (hC : XFlowPhiContStmt) (hU : XFlowUCStmt) :
    WedgeUnzip.XExactAllStmt :=
  xExactAll_of_regCont' (xFlowRegContStmt_of_uc hC hU)

end F1
end QuantumZipper
