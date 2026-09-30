import QuantumZipper.Proofs.Thm18.G1ZA2ST

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A2, part 6: `G1A2SmallTopStmt` from `G1Z2SideGoodStmt`, and A2

The small-mass clause of the selected field is a measurable condition of the (path, data) pair:
by `small_iff`, `top_iff` (G1ZA2ST.lean) it is a countable combination of the measurable
quantities `mB`, `mT` (values at bounded open sets of the measurable formula
`⨆ₖ ofReal (areaFun γ (openBump U k) (xh p))`), valid on the regular set (RC2) where the area limit
is a vague limit. Hence the node `G1A2SmallTopStmt` follows from the a.s. goodness node
`G1Z2SideGoodStmt` (Sheffield–Wang, arXiv:1605.06171, Thm 1.4 and Thm 4.3), and

`g1RerootFactorStmt_of_good : G1Z2SideGoodStmt → G1RerootFactorStmt`.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA2

open D3Plus Factorization LQGMeas

/-- Area of the ball `B(q, 1/(m+1)) ∩ ℍ` by the measurable formula. -/
def mB (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G1PathData) (q : ℚ) (m : ℕ) :
    ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal (areaFun γ (openBump
    (Metric.ball ((q : ℝ) : ℂ) (1 / ((m : ℝ) + 1)) ∩ H) k) (xh γ Ψ left p))

/-- Area of `B(0, n) ∩ ℍ` by the measurable formula. -/
def mT (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (p : G1PathData) (n : ℕ) : ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal (areaFun γ (openBump (Metric.ball (0 : ℂ) n ∩ H) k)
    (xh γ Ψ left p))

theorem measurable_areaForm {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) (U : Set ℂ) :
    Measurable fun p : G1PathData => ⨆ k : ℕ, ENNReal.ofReal (areaFun γ (openBump U k)
      (xh γ Ψ left p)) :=
  Measurable.iSup fun k => ENNReal.measurable_ofReal.comp
    ((measurable_areaFun γ (continuous_openBump U k).measurable).comp (measurable_xh hΨ left))

/-- The measurable set of data with the small-mass and infinite-mass clauses (formulas). -/
def SetST (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) : Set G1PathData :=
  {p | (∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, |(q : ℝ)| ≤ n → mB γ Ψ left p q m < 1) ∧
    ∀ M : ℕ, ∃ n : ℕ, (M : ℝ≥0∞) ≤ mT γ Ψ left p n}

theorem measurableSet_SetST {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) : MeasurableSet (SetST γ Ψ left) := by
  have h1 : MeasurableSet {p : G1PathData |
      ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, |(q : ℝ)| ≤ n → mB γ Ψ left p q m < 1} := by
    have e : {p : G1PathData | ∀ n : ℕ, ∃ m : ℕ, ∀ q : ℚ, |(q : ℝ)| ≤ n → mB γ Ψ left p q m < 1} =
        ⋂ n : ℕ, ⋃ m : ℕ, ⋂ q : ℚ, {p | |(q : ℝ)| ≤ n → mB γ Ψ left p q m < 1} := by
      ext p; simp
    rw [e]
    refine MeasurableSet.iInter fun n => MeasurableSet.iUnion fun m => MeasurableSet.iInter fun q => ?_
    by_cases hq : |(q : ℝ)| ≤ n
    · have e2 : {p : G1PathData | |(q : ℝ)| ≤ n → mB γ Ψ left p q m < 1} =
          {p | mB γ Ψ left p q m < 1} := by ext p; simp [hq]
      rw [e2]
      exact measurableSet_lt (measurable_areaForm hΨ left _) measurable_const
    · have e2 : {p : G1PathData | |(q : ℝ)| ≤ n → mB γ Ψ left p q m < 1} = univ := by
        ext p; simp [hq]
      rw [e2]; exact MeasurableSet.univ
  have h2 : MeasurableSet {p : G1PathData | ∀ M : ℕ, ∃ n : ℕ, (M : ℝ≥0∞) ≤ mT γ Ψ left p n} := by
    have e : {p : G1PathData | ∀ M : ℕ, ∃ n : ℕ, (M : ℝ≥0∞) ≤ mT γ Ψ left p n} =
        ⋂ M : ℕ, ⋃ n : ℕ, {p | (M : ℝ≥0∞) ≤ mT γ Ψ left p n} := by
      ext p; simp
    rw [e]
    exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun n =>
      measurableSet_le measurable_const (measurable_areaForm hΨ left _)
  exact h1.inter h2

/-- On a regular `xc` with an area limit, the formulas are the measures of the balls. -/
theorem mem_SetST_iff {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {left : Bool} {p : G1PathData}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith (xc γ Ψ left p) F) {μ : Measure ℂ}
    (hμ : HasAreaLimit γ (xc γ Ψ left p) μ) :
    p ∈ SetST γ Ψ left ↔
      ((∀ q : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (q : ℂ) a ∩ H) < 1) ∧ μ H = ⊤) := by
  have har : areaApprox γ (xh γ Ψ left p) = areaApprox γ (xc γ Ψ left p) := by
    funext k; unfold areaApprox; rw [avgReg_xh]
  have hL : IsVagueLimitOn H (areaApprox γ (xh γ Ψ left p)) μ := by
    rw [har]; exact g1z2_isVagueLimitOn_of_hasAreaLimit hF hμ
  have hB : ∀ (q : ℚ) (m : ℕ), mB γ Ψ left p q m =
      μ (Metric.ball ((q : ℝ) : ℂ) (1 / ((m : ℝ) + 1)) ∩ H) := fun q m =>
    (measure_eq_iSup_areaFun hL (Metric.isOpen_ball.inter isOpen_H)
      (Metric.isBounded_ball.subset inter_subset_left) inter_subset_right).symm
  have hT : ∀ n : ℕ, mT γ Ψ left p n = μ (Metric.ball (0 : ℂ) n ∩ H) := fun n =>
    (measure_eq_iSup_areaFun hL (Metric.isOpen_ball.inter isOpen_H)
      (Metric.isBounded_ball.subset inter_subset_left) inter_subset_right).symm
  rw [small_iff, top_iff]
  simp only [SetST, mem_setOf_eq, hB, hT]

end G1ZA2

/-- **The small-mass node from the goodness node.** -/
theorem g1A2SmallTopStmt_of (hG : G1Z2SideGoodStmt) : G1A2SmallTopStmt := by
  intro γ Ω _ P _ B Y hS hIn Ψ hΨ left
  refine ⟨G1ZA2.SetST γ Ψ left ∩ {p : G1PathData |
      IsRegularSample (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))},
    (G1ZA2.measurableSet_SetST hΨ left).inter (G1Meas.measurableSet_rc2 hΨ left), ?_, ?_⟩
  · rintro p ⟨hST, ⟨F, hF⟩⟩ hc hs μ hμ
    exact (G1ZA2.mem_SetST_iff (Ψ := Ψ) (left := left) (p := p) hF hμ).1 hST
  · have hreg := g1z2_ae_isRegularSample (g1RegExStmt_of_rest g1RegRepRestStmt_holds) γ hS hIn hΨ
      left
    filter_upwards [hG γ P B Y hS hIn left, hreg, hS.2.2.1.cont, hIn.2.2]
      with ω hgood hr hc hin
    have hη : IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω)) := hin.1
    obtain ⟨φ₀, hφ₀, hΨe⟩ := hΨ.2.2 (pathOf B ω) hc hη left
    have hM : G1Z2MeasGood γ left (g1z2Field γ Ψ B Y left ω) := by
      unfold g1z2Field
      rw [hΨe]
      exact hgood φ₀ hφ₀
    have hx : G1ZA2.xc γ Ψ left (pathOf B ω, WedgeMeas.dataFull H (Y ω)) =
        g1z2Field γ Ψ B Y left ω :=
      (g1z2_coordChange_congr (Cor15Group.regEq_fromC_coordsFull (Y ω)) _ _).symm
    obtain ⟨⟨μ, hμ, hsm, htop⟩, -⟩ := hM
    obtain ⟨F, hF⟩ := hr
    refine ⟨?_, ⟨F, ?_⟩⟩
    · refine (G1ZA2.mem_SetST_iff (Ψ := Ψ) (left := left)
        (p := (pathOf B ω, WedgeMeas.dataFull H (Y ω))) (by rw [hx]; exact hF)
        (μ := μ) (by rw [hx]; exact hμ)).2 ⟨hsm, htop⟩
    · have h' : IsRegularWith (G1ZA2.xc γ Ψ left (pathOf B ω, WedgeMeas.dataFull H (Y ω))) F := by
        rw [hx]; exact hF
      exact h'

/-- **A2 from the goodness node alone.** -/
theorem g1RerootFactorStmt_of_good (hG : G1Z2SideGoodStmt) : G1RerootFactorStmt :=
  g1RerootFactorStmt_of' hG (g1A2SmallTopStmt_of hG)

end Thm18Asm
end QuantumZipper
