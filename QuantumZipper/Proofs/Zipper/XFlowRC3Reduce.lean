import QuantumZipper.Proofs.Zipper.WedgeFlowWDMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3: the free-field flow RC3 node from a fixed-parameter node and joint continuity

Theorem 1.3, wedge cores (Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.1 rule (5.1), §5.4; Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
185 (2011), Prop. 3.1).

`F1.XFlowRC3Stmt` asks, a.s. and for **all** parameters `p = (u, s, d, r)` at once
(`u, s ≥ 0`, `d ∈ ℍ̄`, `r > 0`), for the identity `evalReg x_u ν_p = x_u ν_p` at the pushed
folded circle `ν_p = (R_{u,s})_* fc(d, r)`, where `x_u = F2.unzX κ X W u`. The existing D33 chain
gives the `Γ⁰` analogue only at the countably many dyadic circles; the uncountable family of
circles needs a continuity input. This file isolates the two genuinely probabilistic inputs:

* `XFlowRC3FixStmt` — the identity at each **fixed** parameter `p`, almost surely (the
  Duplantier–Sheffield Prop. 3.1 statement; its `Γ⁰` analogue is `RegUnif.ae_evalReg_Yf_fc_gen`);
* `XFlowRegContStmt`, `XFlowRawContStmt` — almost surely, the regularized side
  `p ↦ evalReg x_u ν_p` and the raw side `p ↦ x_u ν_p` are continuous on the parameter set
  `flowPar` (a Kolmogorov–Čentsov statement in the five real parameters `(u, s, Re d, Im d, r)`).

and proves, by the standard argument "two a.s. continuous random functions that agree a.s. at
each point of a countable dense set agree everywhere, a.s." (own elementary bookkeeping; the
separability step is `TopologicalSpace.exists_countable_dense_subset`, the closure step
`Set.EqOn.of_subset_closure`):

* `xFlowRC3Stmt_of_fix_cont : XFlowRC3FixStmt → XFlowRegContStmt → XFlowRawContStmt →
  XFlowRC3Stmt`;
* `xExactAll_of_fix_cont`: hence X-X (`WedgeUnzip.XExactAllStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- The parameter set `{(u, s, d, r) : u ≥ 0, s ≥ 0, d ∈ ℍ̄, r > 0}` of the flow node. -/
def flowPar : Set (ℝ × ℝ × ℂ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ p.2.2.1 ∈ Hbar ∧ 0 < p.2.2.2}

/-- The pushed folded circle `ν_p = (R_{u,s})_* fc(d, r)` at `p = (u, s, d, r)`. -/
def flowNu (W : ℝ → ℝ) (p : ℝ × ℝ × ℂ × ℝ) : Measure ℂ :=
  (foldedCircle p.2.2.1 p.2.2.2).map (revMap (B2.vrev W (p.1 + p.2.1)) p.2.1)

/-- Regularized side `evalReg x_u ν_p`. -/
def flowRegSide (κ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (p : ℝ × ℝ × ℂ × ℝ) : ℝ :=
  evalReg (F2.unzX κ x W p.1) (flowNu W p)

/-- Raw side `x_u ν_p`. -/
def flowRawSide (κ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (p : ℝ × ℝ × ℂ × ℝ) : ℝ :=
  F2.unzX κ x W p.1 (flowNu W p)

/-- **(Fixed-parameter free-field flow RC3.)** For each fixed `p = (u, s, d, r) ∈ flowPar`,
almost surely `evalReg x_u ν_p = x_u ν_p` (Duplantier–Sheffield 2011, Prop. 3.1, for the free
field plus the deterministic `α₀(−log|·|)`; the `Γ⁰` analogue is
`RegUnif.ae_evalReg_Yf_fc_gen`). -/
def XFlowRC3FixStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ p ∈ flowPar, ∀ᵐ ω ∂P,
      flowRegSide κ (X ω) (drive κ B ω) p = flowRawSide κ (X ω) (drive κ B ω) p

/-- **(Joint continuity, regularized side.)** Almost surely `p ↦ evalReg x_u ν_p` is continuous
on `flowPar`. -/
def XFlowRegContStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ContinuousOn (flowRegSide κ (X ω) (drive κ B ω)) flowPar

/-- **(Joint continuity, raw side.)** Almost surely `p ↦ x_u ν_p` is continuous on `flowPar`. -/
def XFlowRawContStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ContinuousOn (flowRawSide κ (X ω) (drive κ B ω)) flowPar

/-- Two a.s. continuous random functions on a subset `S` of a second-countable space that agree
a.s. at every fixed point of `S` agree a.s. at every point of `S` (own elementary bookkeeping). -/
theorem ae_eqOn_of_fix_cont {Ω α : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [TopologicalSpace α] [SecondCountableTopology α] {S : Set α} {f g : Ω → α → ℝ}
    (hfix : ∀ p ∈ S, ∀ᵐ ω ∂P, f ω p = g ω p) (hf : ∀ᵐ ω ∂P, ContinuousOn (f ω) S)
    (hg : ∀ᵐ ω ∂P, ContinuousOn (g ω) S) : ∀ᵐ ω ∂P, EqOn (f ω) (g ω) S := by
  obtain ⟨D, hDc, hDS, hSD⟩ := TopologicalSpace.exists_countable_dense_subset S
  have hD : ∀ᵐ ω ∂P, ∀ p ∈ D, f ω p = g ω p :=
    (eventually_countable_ball hDc).2 fun p hp => hfix p (hDS hp)
  filter_upwards [hD, hf, hg] with ω h1 h2 h3
  exact EqOn.of_subset_closure h1 h2 h3 hDS hSD

/-- **`XFlowRC3Stmt` from the fixed-parameter node and joint continuity of both sides.** -/
theorem xFlowRC3Stmt_of_fix_cont (hF : XFlowRC3FixStmt) (hR : XFlowRegContStmt)
    (hW : XFlowRawContStmt) : XFlowRC3Stmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have h := ae_eqOn_of_fix_cont (hF κ hκ hκ4 P B X hB hX hind)
    (hR κ hκ hκ4 P B X hB hX hind) (hW κ hκ hκ4 P B X hB hX hind)
  refine h.mono fun ω hω => ?_
  intro u s hu hs d hd r hr
  have hp : ((u, s, d, r) : ℝ × ℝ × ℂ × ℝ) ∈ flowPar := ⟨hu, hs, hd, hr⟩
  have h1 := hω hp
  simp only [flowRegSide, flowRawSide, flowNu] at h1
  exact h1

end F1
end QuantumZipper
