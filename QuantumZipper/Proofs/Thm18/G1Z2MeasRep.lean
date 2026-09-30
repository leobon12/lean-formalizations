import QuantumZipper.Proofs.Thm18.G1ZMeasReg
import QuantumZipper.Proofs.Thm18.G1PkgLeft
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3
import QuantumZipper.Proofs.Zipper.Cor15RegMeas
import QuantumZipper.Proofs.Probability.BrownianPathMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-MEAS, part 1: the measurable representative of the side field

* `g1RegExStmt_of_rest`: the existential regularity half `G1RegExStmt` from the single open input
  `G1RegRepRestStmt` (the selection `g1PsiSelStmt`, G1PkgLeft.lean, and RC2
  `G1RC.g1RegRepRC2Stmt_holds`, Thm18HeadlineV3.lean, are proved).
* `g1z2Field`: the side field built with a measurable selection `Ψ` (`G1PsiSel`) of inverse
  normalized uniformizers: `Z₀ ω = coordChange (Y ω) (Ψ left (pathOf B ω)) Q`.
* `g1z2_aemeasurable_coords`: its dyadic circle coordinates are a.e.-measurable (the field is read
  through its full coordinates, `Cor15Group.regEq_fromC_coordsFull`, and
  `G1Meas.measurable_evalReg_map_param`).
* `g1z2_ae_isRegularSample`: a.s. it is a regular sample (RC2 transferred along a dilation of the
  chart, `g1zMeas_isRegularSample_comp_mul`, from `G1RegExStmt`).

Own argument (measurability bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- **`G1RegExStmt` from the rest node** (selection and RC2 are proved). -/
theorem g1RegExStmt_of_rest (h3 : G1RegRepRestStmt) : G1RegExStmt :=
  g1RegExStmt_of_fixed (g1RegFixedStmt_of_rep
    (g1RegRepStmt_of_rc2_rest G1RC.g1RegRepRC2Stmt_holds h3))

/-- Two normalized uniformizers of a side component: their inverses differ by a dilation on `ℍ`. -/
theorem g1z2_invFunOn_eq_dilate {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool)
    {φ φ' : ℂ → ℂ} (hφ : IsNormalizedUniformizer (sideDom η left) φ)
    (hφ' : IsNormalizedUniformizer (sideDom η left) φ') :
    ∃ b : ℝ, 0 < b ∧ EqOn (invFunOn φ' (sideDom η left))
      (fun w => invFunOn φ (sideDom η left) ((b : ℂ) * w)) H := by
  obtain ⟨a, ha, heq⟩ : ∃ a : ℝ, 0 < a ∧
      EqOn φ' (fun z => (a : ℂ) * φ z) (sideDom η left) := by
    cases left
    · exact CA.Uniformizer.normalizedUniformizer_unique_rightComponent hη hφ hφ'
    · exact CA.Uniformizer.normalizedUniformizer_unique_leftComponent hη hφ hφ'
  exact ⟨a⁻¹, inv_pos.2 ha, G1.invFunOn_eqOn_of_eqOn_mul hφ.1 hφ'.1 ha heq⟩

/-- The side field for the measurable selection `Ψ`. -/
def g1z2Field (γ : ℝ) {Ω : Type} (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) (left : Bool) (ω : Ω) : FieldSample :=
  coordChange (Y ω) (Ψ left (pathOf B ω)) (Qc γ)

/-- A coordinate change reads the field only through its regularized averages. -/
theorem g1z2_coordChange_congr {x x' : FieldSample} (h : RegEq x x') (ψ : ℂ → ℂ) (Q : ℝ) :
    coordChange x ψ Q = coordChange x' ψ Q := by
  funext μ
  unfold coordChange
  rw [evalReg_congr (funext fun k => funext fun z => h k z)]

/-- **Clause 1**: the dyadic circle coordinates of the representative are a.e.-measurable. -/
theorem g1z2_aemeasurable_coords (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ) {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hB : AEMeasurable (pathOf B) P)
    (hY : AEMeasurable (fun ω => CoordsFull.coordsFull (Y ω)) P) (left : Bool) :
    AEMeasurable (fun ω => coords (g1z2Field γ Ψ B Y left ω)) P := by
  set G : (ℕ → ℝ) × (ℝ≥0 → ℝ) → ℕ → ℝ := fun p =>
    coords (coordChange (E1.fromC p.1) (Ψ left p.2) (Qc γ)) with hG
  have hGm : Measurable G := by
    refine measurable_pi_iff.2 fun i => ?_
    have hy : Measurable fun p : (ℕ → ℝ) × (ℝ≥0 → ℝ) => E1.fromC p.1 :=
      G1Meas.measurable_fromC'.comp measurable_fst
    have hψ : Measurable fun q : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℂ => Ψ left q.1.2 q.2 :=
      (hΨ.1 left).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hψd : Measurable fun q : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℂ =>
        Real.log ‖deriv (Ψ left q.1.2) q.2‖ :=
      (hΨ.2.1 left).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    show Measurable fun p : (ℕ → ℝ) × (ℝ≥0 → ℝ) =>
      evalReg (E1.fromC p.1) ((foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)).map
        (Ψ left p.2)) + Qc γ * ∫ z, Real.log ‖deriv (Ψ left p.2) z‖ ∂foldedCircle
          (dyadicIndex i).1 (radius (dyadicIndex i).2)
    exact (G1Meas.measurable_evalReg_map_param hy hψ _).add (measurable_const.mul
      (StronglyMeasurable.integral_prod_right' (f := fun q : ((ℕ → ℝ) × (ℝ≥0 → ℝ)) × ℂ =>
        Real.log ‖deriv (Ψ left q.1.2) q.2‖) hψd.stronglyMeasurable).measurable)
  have e : (fun ω => coords (g1z2Field γ Ψ B Y left ω)) =
      fun ω => G (CoordsFull.coordsFull (Y ω), pathOf B ω) := by
    funext ω
    simp only [hG, g1z2Field]
    rw [g1z2_coordChange_congr (Cor15Group.regEq_fromC_coordsFull (Y ω))]
  rw [e]
  exact hGm.comp_aemeasurable (hY.prodMk hB)

/-- **Clause 3 (regularity)**: a.s. the representative is a regular sample. -/
theorem g1z2_ae_isRegularSample (hR : G1RegExStmt) (γ : ℝ) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y)
    {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ) (left : Bool) :
    ∀ᵐ ω ∂P, IsRegularSample (g1z2Field γ Ψ B Y left ω) := by
  have hside : G1RegExSide γ P B Y left := by
    cases left
    · exact (hR γ P B Y hS hIn).2
    · exact (hR γ P B Y hS hIn).1
  filter_upwards [hside, hIn.2.2, hS.2.2.1.cont] with ω ⟨φ, hφ, hcore⟩ hω hc
  have hη : IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω)) := hω.1
  obtain ⟨φ₀, hφ₀, hΨe⟩ := hΨ.2.2 (pathOf B ω) hc hη left
  have hD : IsOpen (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left) :=
    G1.isOpen_component hω.1 left
  obtain ⟨b, hb, heq⟩ := g1z2_invFunOn_eq_dilate hη left hφ hφ₀
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hφ
  obtain ⟨hreg, hexact, -⟩ := hcore
  have := g1zMeas_isRegularSample_comp_mul (Y ω) (Qc γ) hψd hψ0 hψm hb heq
    (G1.choiceRegular_logDeriv hD hφ) hexact hreg
  unfold g1z2Field
  rw [hΨe]
  exact this

end Thm18Asm
end QuantumZipper
