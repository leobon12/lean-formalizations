import QuantumZipper.Proofs.Thm18.G1CoreRep
import QuantumZipper.Proofs.Zipper.E1TransferRep
import QuantumZipper.Proofs.LQG.GoodMeasurableReg

/-!
# G1-REGREP, part 3: the regularity clause is a measurable condition on (path, data)

For the good set `E` of `G1RegRepStmt` (G1CoreRep.lean) the pulled-back field must be read as a
measurable function of the pair (path `a`, wedge data `c`). We use the field `fromC c.1` rebuilt
from the circle coordinates and a **measurable selection** `Ψ left a` of the inverse normalized
uniformizers of the two side domains (`G1PsiSel`, the path-measurability input (1) of the plan in
`handoff/G1.md`: KT2 gives continuity in the chord, measurability of `a ↦ pathTrace a` is a
separate input, not proved here).

* `G1Meas.isRegularWith_congr_coordsFull`, `isRegularSample_fromC_iff`: regularity only depends
  on `coordsFull`;
* `G1Meas.measurable_evalReg_map_param`: `p ↦ evalReg (y p) (ν.map (ψ p))` is measurable for
  jointly measurable `(p, z) ↦ ψ p z`;
* `G1Meas.measurableSet_isRegularSample_coordChange`: `{p | IsRegularSample (coordChange (y p)
  (ψ p) Q)}` is measurable (via `measurableSet_isRegularSample`, M4-R5(a));
* `G1Meas.g1RegGood_of_core`: `G1RegGood γ (a, c)` follows from `ChoiceRegularCore` of the
  rebuilt field `fromC c.1` for the selected maps `Ψ left a`, both sides.

Own argument (measurability bookkeeping, following `GoodMeasurableReg.lean`).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Meas

open CoordsFull

theorem isRegularWith_congr_coordsFull {x x' : FieldSample} (h : coordsFull x = coordsFull x')
    (F : ℂ × ℝ → ℝ) : IsRegularWith x F ↔ IsRegularWith x' F := by
  have e : ∀ (k n : ℕ) (z : ℂ), x (foldedCircle (dyadicRoundC n z) (radius k)) =
      x' (foldedCircle (dyadicRoundC n z) (radius k)) := fun k n z => by
    rw [radius_eq_div]; exact coordsFull_apply_eq h n z 1 one_pos k
  unfold IsRegularWith
  simp only [e]

theorem isRegularSample_fromC_iff (x : FieldSample) :
    IsRegularSample (E1.fromC (coordsFull x)) ↔ IsRegularSample x := by
  unfold IsRegularSample
  simp only [isRegularWith_congr_coordsFull (E1.coordsFull_fromC x)]

theorem measurable_fromC' : Measurable E1.fromC := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  unfold E1.fromC
  by_cases h : ∃ i, foldedCircle (fullIndex i).1 (fullIndex i).2 = μ
  · simp only [h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]; exact measurable_const

/-- **Regularity is measurable** along a family whose circle coordinates are measurable. -/
theorem measurableSet_isRegularSample_of_coords {Z : Type*} [MeasurableSpace Z]
    {G : Z → FieldSample} (hG : ∀ i, Measurable fun p => coordsFull (G p) i) :
    MeasurableSet {p | IsRegularSample (G p)} := by
  have hm : Measurable fun p => E1.fromC (coordsFull (G p)) :=
    measurable_fromC'.comp (measurable_pi_iff.2 hG)
  have e : {p | IsRegularSample (G p)} =
      (fun p => E1.fromC (coordsFull (G p))) ⁻¹' {x | IsRegularSample x} := by
    ext p; simp only [mem_ofPred_eq, mem_preimage, isRegularSample_fromC_iff]
  rw [e]; exact hm GoodMeas.measurableSet_isRegularSample

/-- Measurability of the regularized evaluation of a pushed measure, in a parameter. -/
theorem measurable_evalReg_map_param {Z : Type*} [MeasurableSpace Z] {y : Z → FieldSample}
    (hy : Measurable y) {ψ : Z → ℂ → ℂ} (hψ : Measurable fun p : Z × ℂ => ψ p.1 p.2)
    (ν : Measure ℂ) [SFinite ν] : Measurable fun p => evalReg (y p) (ν.map (ψ p)) := by
  have hψp : ∀ p, Measurable (ψ p) := fun p => hψ.comp (measurable_const.prodMk measurable_id)
  have e : ∀ p (k : ℕ), ∫ w, avgReg (y p) k w ∂(ν.map (ψ p)) =
      ∫ z, avgReg (y p) k (ψ p z) ∂ν := fun p k =>
    integral_map (hψp p).aemeasurable
      ((measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hk : ∀ k : ℕ, StronglyMeasurable fun p => ∫ z, avgReg (y p) k (ψ p z) ∂ν := fun k =>
    StronglyMeasurable.integral_prod_right'
      (f := fun q : Z × ℂ => avgReg (y q.1) k (ψ q.1 q.2))
      ((measurable_avgReg k).comp ((hy.comp measurable_fst).prodMk hψ)).stronglyMeasurable
  unfold evalReg
  simp_rw [e]
  exact (StronglyMeasurable.limUnder hk).measurable

/-- The circle coordinates of the pulled-back field are measurable in the parameter. -/
theorem measurable_coordsFull_coordChange {Z : Type*} [MeasurableSpace Z] {y : Z → FieldSample}
    (hy : Measurable y) {ψ : Z → ℂ → ℂ} (hψ : Measurable fun p : Z × ℂ => ψ p.1 p.2)
    (hψd : Measurable fun p : Z × ℂ => Real.log ‖deriv (ψ p.1) p.2‖) (Q : ℝ) (i : ℕ) :
    Measurable fun p => coordsFull (coordChange (y p) (ψ p) Q) i := by
  show Measurable fun p => evalReg (y p) ((foldedCircle (fullIndex i).1 (fullIndex i).2).map
      (ψ p)) + Q * ∫ z, Real.log ‖deriv (ψ p) z‖ ∂foldedCircle (fullIndex i).1 (fullIndex i).2
  exact (measurable_evalReg_map_param hy hψ _).add (measurable_const.mul
    (StronglyMeasurable.integral_prod_right' (f := fun q : Z × ℂ =>
      Real.log ‖deriv (ψ q.1) q.2‖) hψd.stronglyMeasurable).measurable)

/-- **RC2 is a measurable condition** on the parameter of the pulled-back field. -/
theorem measurableSet_isRegularSample_coordChange {Z : Type*} [MeasurableSpace Z]
    {y : Z → FieldSample} (hy : Measurable y) {ψ : Z → ℂ → ℂ}
    (hψ : Measurable fun p : Z × ℂ => ψ p.1 p.2)
    (hψd : Measurable fun p : Z × ℂ => Real.log ‖deriv (ψ p.1) p.2‖) (Q : ℝ) :
    MeasurableSet {p | IsRegularSample (coordChange (y p) (ψ p) Q)} :=
  measurableSet_isRegularSample_of_coords fun i =>
    measurable_coordsFull_coordChange hy hψ hψd Q i

end G1Meas

/-- **Measurable selection of inverse normalized uniformizers along paths** (input (1)):
`Ψ left a` is jointly measurable in `(a, z)`, so is `log ‖(Ψ left a)'(z)‖`, and for every
continuous path whose trace is a simple chord, `Ψ left a` is the inverse of some normalized
uniformizer of the corresponding side domain. -/
def G1PsiSel (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) : Prop :=
  (∀ left, Measurable fun p : (ℝ≥0 → ℝ) × ℂ => Ψ left p.1 p.2) ∧
  (∀ left, Measurable fun p : (ℝ≥0 → ℝ) × ℂ => Real.log ‖deriv (Ψ left p.1) p.2‖) ∧
  ∀ a : ℝ≥0 → ℝ, Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) → ∀ left : Bool,
    ∃ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left) φ ∧
      Ψ left a = invFunOn φ (sideDom (pathTrace (γ ^ 2) a) left)

namespace G1Meas

/-- The good pairs from the core package of the rebuilt field for the selected maps. -/
theorem g1RegGood_of_core {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    {p : G1PathData} (hcore : ∀ left, G1.ChoiceRegularCore γ (E1.fromC p.2.1) (Ψ left p.1)) :
    G1RegGood γ p := by
  intro hc hs y hy left
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 p.1 hc hs left
  refine ⟨φ, hφ, ?_⟩
  rw [← hΨa]
  have h1 : p.2.1 = CoordsFull.coordsFull y := by rw [← hy]; rfl
  have h2 : CoordsFull.coordsFull (E1.fromC p.2.1) = CoordsFull.coordsFull y := by
    rw [h1]; exact E1.coordsFull_fromC y
  exact (G1.choiceRegularCore_congr_coordsFull h2 _).1 (hcore left)

/-- The RC2 part of the good set is measurable. -/
theorem measurableSet_rc2 {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    (left : Bool) :
    MeasurableSet {p : G1PathData |
      IsRegularSample (coordChange (E1.fromC p.2.1) (Ψ left p.1) (Qc γ))} := by
  refine measurableSet_isRegularSample_coordChange (y := fun p : G1PathData => E1.fromC p.2.1)
    (ψ := fun p : G1PathData => Ψ left p.1) (measurable_fromC'.comp measurable_snd.fst)
    ((hΨ.1 left).comp (measurable_fst.fst.prodMk measurable_snd))
    ((hΨ.2.1 left).comp (measurable_fst.fst.prodMk measurable_snd)) (Qc γ)

end G1Meas
end Thm18Asm
end QuantumZipper
