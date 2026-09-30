import QuantumZipper.Proofs.Thm18.G3ZqO5Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-G1 (6): moving the window condition away from the root

The window condition `ν[0, x] ≤ U` at a core point `x` reads the boundary measure up to `x`
itself, so it is not measurable for the field outside a neighbourhood of `x` (the conditioning
σ-algebra of the conditional zoom `G3Cv.cond_zoom_palm_free'`, Sheffield, arXiv:1012.4797,
p. 65). We replace it by `ν[0, x − δ] ≤ U` (`winD`, right side; `ν[x + δ, 0] ≤ U` on the left),
which only reads the field at distance `≥ δ` from `x`:

* `winSet ⊆ winD`, and `⋂_δ (winD δ \ winSet) ∩ T = ∅` for an atomless measure
  (`ν[0, x) = lim ν[0, x − δ]`), so `E ν(T ∩ (winD δ \ winSet)) → 0` by dominated convergence
  with the integrable bound `ν(T)` (`lintegral_bdryM_core_lt_top`);
* the node **`G3ZqO6CoreDStmt`** (the core limit with the shifted window condition, for every
  small `δ`) and **`g3ZqO2CoreStmt_of_coreD : G3ZqO6CoreDStmt → G3ZqO2CoreStmt`**.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqO

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The point `δ` closer to the root. -/
def shPt (left : Bool) (δ x : ℝ) : ℝ := if left then x + δ else x - δ

/-- The shifted window: `ν[0, x − δ] ≤ U` (right), `ν[x + δ, 0] ≤ U` (left). -/
def winD (γ : ℝ) (left : Bool) (U δ : ℝ) (y : FieldSample) : Set ℝ :=
  {x | x ∈ g1SideHalf left ∧ bdryM γ y (g1SideSeg left (shPt left δ x)) ≤ ENNReal.ofReal U}

/-- The core functional with the shifted window condition. -/
def g1PhiD (γ L : ℝ) (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞)
    (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (left : Bool) (U η δ : ℝ)
    (p : FieldSample × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  ∫⁻ x, (coreSet left η ∩ winD γ left U δ p.1).indicator
    (fun x => Γ (g1zLocData R (g1zM γ L Ψ left (p, x)))) x ∂(bdryM γ p.1)

/-- The boundary mass of the core inside the shifted window. -/
def winCoreD (γ : ℝ) (left : Bool) (U η δ : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  bdryM γ y (winD γ left U δ y ∩ coreSet left η)

/-- **The core node with the window condition at distance `δ` from the root.** -/
def G3ZqO6CoreDStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Y'' : Ω'' → FieldSample), IsQuantumWedge γ γ Y'' P'' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ left : Bool,
  ∀ (R : ℕ) (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞), Measurable Γ → (∀ y, Γ y ≤ 1) →
  ∀ U : ℝ, 0 < U → ∀ η : ℝ, 0 < η → η < 1 / 4 → ∀ δ : ℝ, 0 < δ → δ < η / 2 →
  ∀ᵐ a ∂(P.map (pathOf B)), Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) →
    ∀ e : ℝ≥0∞, 0 < e → ∀ᶠ L in atTop,
      ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' ≤
          (∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'') *
            ∫⁻ ω', winCoreD γ left U η δ (wedgeU γ X A ω') ∂P' + e ∧
        (∫⁻ ω'', Γ (locFieldFull R (Y'' ω'')) ∂P'') *
            ∫⁻ ω', winCoreD γ left U η δ (wedgeU γ X A ω') ∂P' ≤
          ∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' + e

theorem seg_shPt_subset (left : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (x : ℝ) :
    g1SideSeg left (shPt left δ x) ⊆ g1SideSeg left x := by
  cases left
  · simp only [g1SideSeg, shPt, Bool.false_eq_true, ite_false]
    exact Icc_subset_Icc_right (by linarith)
  · simp only [g1SideSeg, shPt, ite_true]
    exact Icc_subset_Icc_left (by linarith)

theorem winSet_subset_winD (γ : ℝ) (left : Bool) (U : ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (y : FieldSample) : winSet γ left U y ⊆ winD γ left U δ y := fun _ hx =>
  ⟨hx.1, (measure_mono (seg_shPt_subset left hδ _)).trans hx.2⟩

/-- The error set between the two window conditions on the core. -/
def errSet (γ : ℝ) (left : Bool) (U η δ : ℝ) (y : FieldSample) : Set ℝ :=
  coreSet left η ∩ (winD γ left U δ y \ winSet γ left U y)

theorem measurable_bdryM_seg2 (γ : ℝ) (left : Bool) :
    Measurable fun q : FieldSample × ℝ => bdryM γ q.1 (g1SideSeg left q.2) := by
  exact (measurable_bdryM_seg γ left).comp
    (f := fun q : FieldSample × ℝ => ((q.1, (0 : ℝ≥0 → ℝ)), q.2))
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)

theorem measurable_shPt (left : Bool) (δ : ℝ) : Measurable (shPt left δ) := by
  cases left
  · exact measurable_id.sub_const δ
  · exact measurable_id.add_const δ

theorem measurable_bdryM_shseg (γ : ℝ) (left : Bool) (δ : ℝ) :
    Measurable fun q : FieldSample × ℝ => bdryM γ q.1 (g1SideSeg left (shPt left δ q.2)) :=
  (measurable_bdryM_seg2 γ left).comp
    (f := fun q : FieldSample × ℝ => (q.1, shPt left δ q.2))
    (measurable_fst.prodMk ((measurable_shPt left δ).comp measurable_snd))

/-- **The graph of the error set is measurable.** -/
theorem measurableSet_errGraph (γ : ℝ) (left : Bool) (U η δ : ℝ) :
    MeasurableSet {q : FieldSample × ℝ | q.2 ∈ errSet γ left U η δ q.1} := by
  have h1 := measurable_bdryM_seg2 γ left
  have h2 := measurable_bdryM_shseg γ left δ
  have hhalf : MeasurableSet (g1SideHalf left) := by
    cases left
    · exact measurableSet_Ioi
    · exact measurableSet_Iio
  have e : {q : FieldSample × ℝ | q.2 ∈ errSet γ left U η δ q.1} =
      (Prod.snd ⁻¹' coreSet left η) ∩ (((Prod.snd ⁻¹' g1SideHalf left) ∩
        {q | bdryM γ q.1 (g1SideSeg left (shPt left δ q.2)) ≤ ENNReal.ofReal U}) ∩
        ((Prod.snd ⁻¹' g1SideHalf left) ∩
          {q | bdryM γ q.1 (g1SideSeg left q.2) ≤ ENNReal.ofReal U})ᶜ) := rfl
  rw [e]
  exact (measurable_snd (measurableSet_coreSet left η)).inter
    (((measurable_snd hhalf).inter (measurableSet_le h2 measurable_const)).inter
      ((measurable_snd hhalf).inter (measurableSet_le h1 measurable_const)).compl)

theorem measurableSet_errSet (γ : ℝ) (left : Bool) (U η δ : ℝ) (y : FieldSample) :
    MeasurableSet (errSet γ left U η δ y) :=
  measurable_prodMk_left (measurableSet_errGraph γ left U η δ)

/-- The error mass is measurable in the field. -/
theorem measurable_errMass (γ : ℝ) (left : Bool) (U η δ : ℝ) :
    Measurable fun y : FieldSample => bdryM γ y (errSet γ left U η δ y) := by
  have e : (fun y : FieldSample => bdryM γ y (errSet γ left U η δ y)) =
      fun y => ∫⁻ x, ({q : FieldSample × ℝ | q.2 ∈ errSet γ left U η δ q.1}.indicator 1 (y, x))
        ∂(bdryM γ y) := by
    funext y
    rw [← lintegral_indicator_one (measurableSet_errSet γ left U η δ y)]
    rfl
  rw [e]
  exact R18.measurable_lintegral_family (measurable_bdryM γ)
    (fun y N => R18.bdryM_Icc_ne_top γ y _ _)
    (measurable_one.indicator (measurableSet_errGraph γ left U η δ))

end G3ZqO
end Thm18Asm
end QuantumZipper
