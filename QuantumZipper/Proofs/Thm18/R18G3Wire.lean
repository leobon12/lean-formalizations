import QuantumZipper.Proofs.Thm18.R18G3Defs
import QuantumZipper.Proofs.Thm18.G1ZoomModel
import QuantumZipper.Proofs.Thm18.G3G2Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3: `G3PaperStmt` from the five steps of route (b)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71); plan `handoff/R18-PLAN.md` §5, nodes in `R18G3Defs.lean`.

* `g3_lawCyl_local`: a cylinder event of the full field data is an event of the local data
  `locFieldFull R` for all large `R` (a cylinder reads finitely many circles and test functions);
* `g3_loc_eq_wedge`: steps 2–4 express every joint local integral, for every window `U` and every
  constant `C`, as the normalized joint Palm-window integral of the wedge at zoom level `γ C`;
* `g3_cyl_mul_eq`: with step 5 (the level `L = γ C` grows) the product formula for cylinder events;
* `g3PaperStmt_of_nodes`: `indepFun_of_generating_eq_mul` on the π-system `lawCyl`.

Own bookkeeping; the paper's argument is steps 1–5.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm D3Plus

/-- **Cylinder events are local**: for `s ∈ lawCyl` there is `R₀` such that for all `R ≥ R₀`
the event `s` of the full data of a field is the event `s` of its local data at radius `R`. -/
theorem g3_lawCyl_local {s : Set LawD} (hs : s ∈ lawCyl) : ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    ∀ x : FieldSample, (WedgeMeas.dataFull H x ∈ s ↔ locFieldFull R x ∈ s) := by
  classical
  obtain ⟨A, hA, B', hB, rfl⟩ := hs
  obtain ⟨I, S, -, rfl⟩ := (mem_measurableCylinders A).1 hA
  obtain ⟨J, T, -, rfl⟩ := (mem_measurableCylinders B').1 hB
  let RI : ℕ → ℕ := fun i => (E6.exists_inBallFull i).choose
  let RJ : TestFun H → ℕ := fun ρ => (E6.exists_suppIn ρ).choose
  refine ⟨max (I.sup RI) (J.sup RJ), fun R hR x => ?_⟩
  have hI : ∀ i ∈ I, inBallFull R i := fun i hi =>
    E6.inBallFull_mono ((Finset.le_sup (f := RI) hi).trans ((le_max_left _ _).trans hR))
      (E6.exists_inBallFull i).choose_spec
  have hJ : ∀ ρ ∈ J, suppIn R ρ := fun ρ hρ =>
    E6.suppIn_mono ((Finset.le_sup (f := RJ) hρ).trans ((le_max_right _ _).trans hR))
      (E6.exists_suppIn ρ).choose_spec
  have e1 : I.restrict (WedgeMeas.dataFull H x).1 = I.restrict (locFieldFull R x).1 := by
    funext i
    simp [Finset.restrict, WedgeMeas.dataFull, locFieldFull, hI i.1 i.2]
  have e2 : J.restrict (WedgeMeas.dataFull H x).2 = J.restrict (locFieldFull R x).2 := by
    funext ρ
    simp [Finset.restrict, WedgeMeas.dataFull, locFieldFull, hJ ρ.1 ρ.2]
  simp only [mem_prod, mem_cylinder, e1, e2]

/-- The indicator form of `g3_lawCyl_local`. -/
theorem g3_lawCyl_local_ind {s : Set LawD} (hs : s ∈ lawCyl) : ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
    ∀ x : FieldSample, s.indicator (1 : LawD → ℝ≥0∞) (locFieldFull R x) =
      s.indicator 1 (WedgeMeas.dataFull H x) := by
  obtain ⟨R₀, h⟩ := g3_lawCyl_local hs
  refine ⟨R₀, fun R hR x => ?_⟩
  by_cases hx : WedgeMeas.dataFull H x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem ((h R hR x).1 hx)]
    rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem fun h' => hx ((h R hR x).2 h')]

theorem g3_ind_measurable {s : Set LawD} (hs : s ∈ lawCyl) :
    Measurable (s.indicator (1 : LawD → ℝ≥0∞)) :=
  measurable_one.indicator (measurableSet_lawCyl hs)

theorem g3_ind_le_one (s : Set LawD) (y : LawD) : s.indicator (1 : LawD → ℝ≥0∞) y ≤ 1 := by
  by_cases hy : y ∈ s <;> simp [hy]

/-- **Steps 2–4**: every joint local integral is, for every window `U > 0` and every constant
`C`, the normalized joint Palm-window integral of the wedge at zoom level `γ C`. -/
theorem g3_loc_eq_wedge (hC : G3JointConstInvStmt) (hPC : G3JointPalmConstStmt)
    (hZ : G3JointPalmToWedgeStmt) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {U : ℝ} (hU : 0 < U) (C : ℝ)
    (R : ℕ) {Γ₁ Γ₂ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (h1 : Measurable Γ₁)
    (h2 : Measurable Γ₂) (h1' : ∀ y, Γ₁ y ≤ 1) (h2' : ∀ y, Γ₂ y ≤ 1) :
    ∫⁻ ω, Γ₁ (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
        Γ₂ (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P =
      (ENNReal.ofReal U)⁻¹ * g3zWedgePalmInt γ P B Y U (γ * C) R Γ₁ Γ₂ := by
  rw [← hC γ P B Y hS hIn C R Γ₁ Γ₂ h1 h2 h1' h2',
    ← hPC γ P B Y hS hIn U hU C R Γ₁ Γ₂ h1 h2 h1' h2', hZ γ P B Y hS hIn U hU C R Γ₁ Γ₂ h1 h2 h1' h2']

/-- For radii past the cylinder radii, the joint local Palm integral of two cylinder events is
the cylinder Palm integral. -/
theorem g3zWedgePalmInt_ind_eq {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (U L : ℝ) {s t : Set LawD} {R : ℕ}
    (hs : ∀ x : FieldSample, s.indicator (1 : LawD → ℝ≥0∞) (locFieldFull R x) =
      s.indicator 1 (WedgeMeas.dataFull H x))
    (ht : ∀ x : FieldSample, t.indicator (1 : LawD → ℝ≥0∞) (locFieldFull R x) =
      t.indicator 1 (WedgeMeas.dataFull H x)) :
    g3zWedgePalmInt γ P B Y U L R (s.indicator 1) (t.indicator 1) =
      g3zWedgePalmCyl γ P B Y U L s t := by
  unfold g3zWedgePalmInt g3zWedgePalmCyl
  simp only [hs, ht]

/-- **The product formula for cylinder events** of the local canonical data (steps 2–5). -/
theorem g3_cyl_mul_eq (hC : G3JointConstInvStmt) (hPC : G3JointPalmConstStmt)
    (hZ : G3JointPalmToWedgeStmt) (hD : G3WedgePalmDecStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y)
    {s t : Set LawD} (hs : s ∈ lawCyl) (ht : t ∈ lawCyl) {R : ℕ}
    (hsR : ∀ x : FieldSample, s.indicator (1 : LawD → ℝ≥0∞) (locFieldFull R x) =
      s.indicator 1 (WedgeMeas.dataFull H x))
    (htR : ∀ x : FieldSample, t.indicator (1 : LawD → ℝ≥0∞) (locFieldFull R x) =
      t.indicator 1 (WedgeMeas.dataFull H x)) :
    ∫⁻ ω, s.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
        t.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P =
      (∫⁻ ω, s.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) ∂P) *
        ∫⁻ ω, t.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P := by
  have huR : ∀ x : FieldSample, (univ : Set LawD).indicator (1 : LawD → ℝ≥0∞)
      (locFieldFull R x) = (univ : Set LawD).indicator 1 (WedgeMeas.dataFull H x) := by
    intro x; simp
  have hm1 := g3_ind_measurable hs
  have hm2 := g3_ind_measurable ht
  have hmu := g3_ind_measurable univ_mem_lawCyl
  have eL : ∫⁻ ω, s.indicator (1 : LawD → ℝ≥0∞)
        (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) ∂P =
      ∫⁻ ω, s.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
        (univ : Set LawD).indicator 1
          (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P := by
    simp
  have eR : ∫⁻ ω, t.indicator (1 : LawD → ℝ≥0∞)
        (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P =
      ∫⁻ ω, (univ : Set LawD).indicator 1
          (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
        t.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P := by
    simp
  have key : ∀ ε : ℝ≥0∞, 0 < ε →
      ∫⁻ ω, s.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
          t.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P ≤
        (∫⁻ ω, s.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) ∂P) *
          (∫⁻ ω, t.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P)
          + ε ∧
      (∫⁻ ω, s.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) ∂P) *
          (∫⁻ ω, t.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P) ≤
        ∫⁻ ω, s.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y true ω))) *
          t.indicator 1 (locFieldFull R (canonical γ (g1SideField γ B Y false ω))) ∂P + ε := by
    intro ε hε
    obtain ⟨U, hU, hev⟩ := hD γ P B Y hS hIn s hs t ht ε hε
    obtain ⟨L, hL⟩ := hev.exists
    have hγ : γ ≠ 0 := hS.1.ne'
    have hLC : γ * (L / γ) = L := by field_simp
    have ea := g3_loc_eq_wedge hC hPC hZ hS hIn hU (L / γ) R hm1 hm2 (g3_ind_le_one s)
      (g3_ind_le_one t)
    have e1 := g3_loc_eq_wedge hC hPC hZ hS hIn hU (L / γ) R hm1 hmu (g3_ind_le_one s)
      (g3_ind_le_one univ)
    have e2 := g3_loc_eq_wedge hC hPC hZ hS hIn hU (L / γ) R hmu hm2 (g3_ind_le_one univ)
      (g3_ind_le_one t)
    rw [hLC, g3zWedgePalmInt_ind_eq P B Y U L hsR htR] at ea
    rw [hLC, g3zWedgePalmInt_ind_eq P B Y U L hsR huR] at e1
    rw [hLC, g3zWedgePalmInt_ind_eq P B Y U L huR htR] at e2
    rw [eL, eR, ea, e1, e2]
    exact hL
  refine le_antisymm ?_ ?_
  · exact ENNReal.le_of_forall_pos_le_add fun ε hε _ =>
      (key ε (by exact_mod_cast hε)).1
  · exact ENNReal.le_of_forall_pos_le_add fun ε hε _ =>
      (key ε (by exact_mod_cast hε)).2

/-- `P (X⁻¹ s ∩ Z⁻¹ t)` as the integral of the product of indicators. -/
theorem g3_measure_inter_eq_lintegral {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {X Z : Ω → α} (hX : AEMeasurable X P) (hZ : AEMeasurable Z P)
    {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    P (X ⁻¹' s ∩ Z ⁻¹' t) = ∫⁻ ω, s.indicator (1 : α → ℝ≥0∞) (X ω) * t.indicator 1 (Z ω) ∂P := by
  have hn : NullMeasurableSet (X ⁻¹' s ∩ Z ⁻¹' t) P :=
    (hX.nullMeasurable hs).inter (hZ.nullMeasurable ht)
  rw [← lintegral_indicator_one₀ hn]
  refine lintegral_congr fun ω => ?_
  by_cases h1 : X ω ∈ s <;> by_cases h2 : Z ω ∈ t <;> simp [h1, h2, indicator]

theorem g3_measure_preimage_eq_lintegral {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Measure Ω} {X : Ω → α} (hX : AEMeasurable X P) {s : Set α} (hs : MeasurableSet s) :
    P (X ⁻¹' s) = ∫⁻ ω, s.indicator (1 : α → ℝ≥0∞) (X ω) ∂P := by
  rw [← lintegral_indicator_one₀ (hX.nullMeasurable hs)]
  refine lintegral_congr fun ω => ?_
  by_cases h1 : X ω ∈ s <;> simp [h1, indicator]

/-- **`G3PaperStmt` from steps 2–5** (step 1 enters through step 3). -/
theorem g3PaperStmt_of_nodes (hC : G3JointConstInvStmt) (hPC : G3JointPalmConstStmt)
    (hZ : G3JointPalmToWedgeStmt) (hD : G3WedgePalmDecStmt) : G3PaperStmt := by
  intro γ Ω _ P _ B Y hS hIn hWL hWR _hEq
  have hX := aemeasurable_lawData_component hS.1 hS.2.1 true hWL
  have hZ' := aemeasurable_lawData_component hS.1 hS.2.1 false hWR
  refine indepFun_of_generating_eq_mul hX hZ' isPiSystem_lawCyl isPiSystem_lawCyl
    generateFrom_lawCyl generateFrom_lawCyl fun s hs t ht => ?_
  obtain ⟨R₁, h1⟩ := g3_lawCyl_local_ind hs
  obtain ⟨R₂, h2⟩ := g3_lawCyl_local_ind ht
  have hsR := h1 (max R₁ R₂) (le_max_left _ _)
  have htR := h2 (max R₁ R₂) (le_max_right _ _)
  have key := g3_cyl_mul_eq hC hPC hZ hD hS hIn hs ht hsR htR
  rw [g3_measure_inter_eq_lintegral hX hZ' (measurableSet_lawCyl hs) (measurableSet_lawCyl ht),
    g3_measure_preimage_eq_lintegral hX (measurableSet_lawCyl hs),
    g3_measure_preimage_eq_lintegral hZ' (measurableSet_lawCyl ht)]
  have eX : ∀ ω, lawData (componentSurface γ B Y true) ω =
      WedgeMeas.dataFull H (canonical γ (g1SideField γ B Y true ω)) := fun _ => rfl
  have eZ : ∀ ω, lawData (componentSurface γ B Y false) ω =
      WedgeMeas.dataFull H (canonical γ (g1SideField γ B Y false ω)) := fun _ => rfl
  simp only [eX, eZ, ← hsR, ← htR]
  exact key

end R18
end QuantumZipper
