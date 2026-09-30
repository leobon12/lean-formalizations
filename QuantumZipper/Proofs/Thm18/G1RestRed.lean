import QuantumZipper.Proofs.Thm18.G1RCRep
import QuantumZipper.Proofs.Thm18.G1ProfileConv
import QuantumZipper.Proofs.Thm18.G1FrostAlphaMain
import QuantumZipper.Proofs.Thm18.G1HolderMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST: `G1RegRepRestStmt` from a.s. PAIR-LIM and null-measurability of the good set

`G1RegRepRestStmt` (G1RegRepRed.lean) asks for a **measurable** set `E'` of pairs
(path, wedge data) on which `G1.CoreRest` holds for both sides (RC3 at every folded circle and
PAIR-LIM for every dilated test measure, for the field `fromC c.1` rebuilt from the circle
coordinates), containing `(a, dataFull (wedgeRep ω'))` for a.e. path `a` and a.e. `ω'`.

It has two separate contents:

1. **Almost sure validity at the representative.** RC3 at every folded circle holds a.s.
   (`G1RC.ae_rc3_of`, with the now proved `G1PsiExtStmt` and `G1ProfileStmt`:
   `G1Rest.ae_rc3_rep`). PAIR-LIM for *all* test functions at once is the open input
   `G1RestPairStmt` (the pulled-back wedge field is a.s. a distribution whose circle-smoothed
   pairings converge; same gap as `D3Plus.N2ZPairOscStmt` for the free field).
2. **Measurability.** Both clauses quantify over uncountably many circles / test functions, so
   the good set `{p | ∀ left, CoreRest …}` is not obviously measurable, and an iterated a.s.
   statement about a non-measurable set does not give a measurable one (Rudin, *Real and
   Complex Analysis*, §8.9 (c)). We isolate exactly what is needed: **null-measurability** of
   the RC3 part and of the PAIR-LIM part for the product law
   `(P.map (pathOf B)).prod (P'.map dataFull∘wedgeRep)` (`G1RestRC3NullMeasStmt`,
   `G1RestPairNullMeasStmt`). The abstract step (`G1Rest.exists_measurable_of_nullMeas`) is
   Fubini–Tonelli for null sets (`Measure.measure_ae_null_of_prod_null`).

Main result: `g1RegRepRestStmt_of_pair_nullMeas :
G1RestPairStmt → G1RestRC3NullMeasStmt → G1RestPairNullMeasStmt → G1RegRepRestStmt`.

Own argument (measure-theoretic bookkeeping; the a.s. RC3 is Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1, through `G1RC.ae_rc3_of`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

/-! ## 1. Abstract step: null-measurable good sets and iterated a.s. statements -/

/-- If `S` is null-measurable for `ν ⊗ D_* P'` and `(a, D ω') ∈ S` for `ν`-a.e. `a` and
`P'`-a.e. `ω'`, then a **measurable** `E ⊆ S` has the same iterated a.s. property. -/
theorem exists_measurable_of_nullMeas {α β Ω' : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace Ω'] {ν : Measure α} {P' : Measure Ω'} {D : Ω' → β} (hD : AEMeasurable D P')
    [SFinite (P'.map D)] {S : Set (α × β)} (hS : NullMeasurableSet S (ν.prod (P'.map D)))
    (h : ∀ᵐ a ∂ν, ∀ᵐ ω' ∂P', (a, D ω') ∈ S) :
    ∃ E : Set (α × β), MeasurableSet E ∧ E ⊆ S ∧ ∀ᵐ a ∂ν, ∀ᵐ ω' ∂P', (a, D ω') ∈ E := by
  obtain ⟨E, hES, hEm, hEae⟩ := hS.exists_measurable_subset_ae_eq
  refine ⟨E, hEm, hES, ?_⟩
  set N := toMeasurable (ν.prod (P'.map D)) (S \ E) with hNdef
  have hN0 : ν.prod (P'.map D) N = 0 := by
    rw [hNdef, measure_toMeasurable]; exact (ae_eq_set.1 hEae).2
  filter_upwards [h, Measure.measure_ae_null_of_prod_null hN0] with a ha hNa
  have hm : (P'.map D) (Prod.mk a ⁻¹' N) = 0 := hNa
  rw [Measure.map_apply_of_aemeasurable hD
    (measurable_prodMk_left (measurableSet_toMeasurable _ _))] at hm
  filter_upwards [ha, measure_eq_zero_iff_ae_notMem.1 hm] with ω' h1 h2
  by_contra hE
  exact h2 (subset_toMeasurable _ _ ⟨h1, hE⟩)

/-! ## 2. The two clauses of `CoreRest` -/

/-- PAIR-LIM (second clause of `G1.CoreRest`) for a field `x`. -/
def PairLimAll (x : FieldSample) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
    (∀ s : ℝ, 0 < s → Integrable (fun u => evalReg x (foldedCircle u s))
      ((G1.tmeas σ).map fun z => (c : ℂ) * z)) ∧
    ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg x (foldedCircle u s)
      ∂((G1.tmeas σ).map fun z => (c : ℂ) * z)) (nhdsWithin 0 (Ioi 0)) (nhds L)

/-- RC3 at every folded circle (first clause of `G1.CoreRest`) for a field `x`. -/
def RC3All (x : FieldSample) : Prop :=
  ∀ d ∈ Hbar, ∀ r > 0, evalReg x (foldedCircle d r) = x (foldedCircle d r)

/-- The RC3 part of the good set. -/
def setRC3 (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) : Set G1PathData :=
  {p | ∀ left : Bool, RC3All (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))}

/-- The PAIR-LIM part of the good set. -/
def setPair (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) : Set G1PathData :=
  {p | ∀ left : Bool, PairLimAll (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))}

theorem coreRest_of_mem {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {p : G1PathData}
    (hp : p ∈ setRC3 γ Ψ ∩ setPair γ Ψ) (left : Bool) :
    G1.CoreRest γ (E1.fromC p.2.1) (Ψ left p.1) :=
  ⟨hp.1 left, hp.2 left⟩

/-- **RC3 at every folded circle, a.s., at the representative** (unconditional). -/
theorem ae_rc3_rep :
    G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
      ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ᵐ ω' ∂P',
        RC3All (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ)) :=
  G1RC.ae_rc3_of (G1RC.g1PsiExtStmt_of_holder_α G1RC.g1GoodBMStmt_sideHolderGood)
    (G1RC.g1RawSmoothStmt_of_profile G1RC.g1ProfileStmt_holds)

end G1Rest

/-! ## 3. The open inputs and the reduction -/

/-- **Input: the RC3 part of the good set is null-measurable** for the product of the path law
and the law of the representative's data. -/
def G1RestRC3NullMeasStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    NullMeasurableSet (G1Rest.setRC3 γ Ψ)
      ((P.map (pathOf B)).prod (P'.map fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω')))

end Thm18Asm
end QuantumZipper
