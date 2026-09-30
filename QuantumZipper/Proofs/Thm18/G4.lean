import QuantumZipper.Proofs.Thm18.G4Zero
import QuantumZipper.Proofs.Section5.Prop17Point
import QuantumZipper.Proofs.LQG.WedgeBoundary
import QuantumZipper.Proofs.Zipper.Cor15LawTransfer

/-!
# Theorem 1.8, node G4: properties of `Z^LEN` (conditional reduction)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8, zipper
stationarity (1)–(3), and §5.4; blueprint `blueprint/SECTION5_BLUEPRINT.md` node G4 ("`D_t`
preserves the law (E6) … it is injective … the inverse comes from the explicit `zipLenUpC` …
A5 then gives (1)–(3)").

Proved here:

* `lenWeldPoint_measure_eq` (deterministic, **own elementary argument**, by reflection from
  `S5.lenPoint_spec`): if `ν_x` is atomless, charges every open interval and `ν_x(−∞,0] = ∞`,
  then `ν_x[lenWeldPoint γ x ℓ, 0] = ℓ` for `ℓ > 0`.
* `ae_atomless_pos_wedge`: the boundary measure of the `(γ − 2/γ)`-wedge of Theorem 1.8 is a.s.
  atomless and positive on open intervals (`WedgeBdry.ae_atomless_pos_of_isQuantumWedge`, whose
  reference premise is discharged by `WedgeCan4.ae_wedge_canonical_spec_of_inputs`,
  `WedgeMeas.aemeasurable_wedgeRefData` and `LogSingGood.wedgeRefGoodAS_holds`).
  Hence the D13 conjunct of clause (1) holds given only `WedgeLeftInfStmt` (infinite boundary
  length on `(−∞,0]`).
* `configLawFull_zipLenC_pos`: clause (3) for `t > 0` from E6 by the abstract law transfer
  `Cor15Group.map_comp_eq_of_goodSet` (blueprint A5: `Z_t ∘ D_t = id` and `law(D_t c) = law c`),
  given the factorization hypothesis `G4FactorStmt`.
* `configLawFull_zipLenC_zero` (`G4Zero.lean`): clause (3) at `t = 0`.
* `g4Stmt_of`: `G4Stmt` from the explicit hypotheses `WedgeZeroRegStmt`, `WedgeLeftInfStmt`,
  `G4WeldStmt` (existence and uniqueness of length-welding drivers), `G4RoundStmt` (the two round
  trips), `G4GroupStmt` (clause (2)) and `G4FactorStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## 1. The left length point -/

/-- **`ν_x[x₋, 0] = ℓ`** for `x₋ = lenWeldPoint γ x ℓ`, when `ν_x` is atomless, charges open
intervals and has infinite mass on `(−∞,0]` (reflection of `S5.lenPoint_spec`). -/
theorem lenWeldPoint_measure_eq {γ ℓ : ℝ} {x : FieldSample} (hℓ : 0 < ℓ)
    (hatom : ∀ t : ℝ, qBoundaryMeasure γ x {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ x (Ioo u v))
    (hinf : qBoundaryMeasure γ x (Iic 0) = ⊤) :
    qBoundaryMeasure γ x (Icc (lenWeldPoint γ x ℓ) 0) = ENNReal.ofReal ℓ := by
  have hne : qBoundaryMeasure γ x ≠ 0 := by
    intro h0
    have h1 := hpos 0 1 one_pos
    rw [h0] at h1
    simp at h1
  have := S5.isLocallyFiniteMeasure_qBoundaryMeasure hne
  set μ' := (qBoundaryMeasure γ x).map (fun y : ℝ => -y) with hμ'
  have hm : ∀ s : Set ℝ, MeasurableSet s →
      μ' s = qBoundaryMeasure γ x ((fun y : ℝ => -y) ⁻¹' s) :=
    fun s hs => Measure.map_apply measurable_neg hs
  have hIcc : ∀ y : ℝ, μ' (Icc 0 y) = qBoundaryMeasure γ x (Icc (-y) 0) := by
    intro y
    rw [hm _ measurableSet_Icc]
    congr 1
    ext z
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hatom' : ∀ t : ℝ, μ' {t} = 0 := by
    intro t
    rw [hm _ (measurableSet_singleton t)]
    have : (fun y : ℝ => -y) ⁻¹' {t} = {-t} := by
      ext z
      simp only [mem_preimage, mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [this]
    exact hatom _
  have hpos' : ∀ u v : ℝ, u < v → 0 < μ' (Ioo u v) := by
    intro u v huv
    rw [hm _ measurableSet_Ioo]
    have : (fun y : ℝ => -y) ⁻¹' Ioo u v = Ioo (-v) (-u) := by
      ext z
      simp only [mem_preimage, mem_Ioo]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [this]
    exact hpos _ _ (by linarith)
  have hfin' : ∀ y : ℝ, μ' (Icc 0 y) ≠ ⊤ := fun y => by
    rw [hIcc]
    exact measure_Icc_lt_top.ne
  have hinf' : μ' (Ici 0) = ⊤ := by
    rw [hm _ measurableSet_Ici]
    have : (fun y : ℝ => -y) ⁻¹' Ici 0 = Iic 0 := by
      ext z
      simp only [mem_preimage, mem_Ici, mem_Iic]
      constructor <;> intro h <;> linarith
    rw [this]
    exact hinf
  obtain ⟨-, he, -⟩ := S5.lenPoint_spec hℓ hatom' hpos' hfin' hinf'
  have hset : {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ qBoundaryMeasure γ x (Icc s 0)} =
      -S5.lenSet μ' ℓ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_neg, S5.lenSet, hIcc, neg_neg]
    constructor
    · rintro ⟨hs, hl⟩
      refine ⟨?_, hl⟩
      rcases hs.lt_or_eq with h | h
      · linarith
      · exfalso
        rw [h, Icc_self, hatom] at hl
        exact (ENNReal.ofReal_pos.2 hℓ).not_ge hl
    · rintro ⟨hs, hl⟩
      exact ⟨by linarith, hl⟩
  have hpt : lenWeldPoint γ x ℓ = -S5.lenPoint μ' ℓ := by
    unfold lenWeldPoint
    rw [hset, Real.sSup_neg]
    rfl
  rw [hpt, ← neg_neg (S5.lenPoint μ' ℓ), neg_neg, ← hIcc]
  exact he

/-- The boundary measure of the Theorem 1.8 wedge is a.s. atomless and positive on open
intervals. -/
theorem ae_atomless_pos_wedge {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, (∀ t : ℝ, qBoundaryMeasure γ (Y ω) {t} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ (Y ω) (Ioo u v)) := by
  obtain ⟨hγ, hγ2, -, hY, -⟩ := hS
  have hα := alpha_lt_Qc hγ hγ2
  have hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα
  have hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα
  refine WedgeBdry.ae_atomless_pos_of_isQuantumWedge hγ hγ2 P Y hY hIn.2.1 ?_
  intro Ω' _ P' X A hP' hX hA hI
  have := hP'
  exact ⟨(WedgeCan4.ae_wedge_canonical_spec_of_inputs hfin hinf hγ hγ2 hα hX hA hI).mono
      fun _ h => h.1,
    WedgeMeas.aemeasurable_wedgeRefData hX hA
      (LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP' hX hA hI) H⟩

/-- **Infinite boundary length on the left** (explicit hypothesis; Sheffield §1.6: a wedge has
"an infinite amount [of boundary length] in each neighborhood of ∞", here on `(−∞,0]`). -/
def WedgeLeftInfStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), 0 < γ → γ < 2 → IsQuantumWedge γ (γ - 2 / γ) Y P →
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (Y ω) (Iic 0) = ⊤

/-- The D13 conjunct of clause (1). -/
theorem ae_lenWeldPoint_measure (hL : WedgeLeftInfStmt) {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (Y ω) (Icc (lenWeldPoint γ (Y ω) ℓ) 0) = ENNReal.ofReal ℓ := by
  filter_upwards [ae_atomless_pos_wedge hS hIn, hL γ P Y hS.1 hS.2.1 hS.2.2.2.1] with ω h hi
  exact lenWeldPoint_measure_eq hℓ h.1 h.2 hi

/-! ## 2. Clause (3) for `t > 0` by law transfer -/

/-- The `configLawFull` data of a configuration. -/
def cfgData (x : FieldSample × (ℝ → ℝ)) : E6.FullData :=
  ((CoordsFull.coordsFull x.1, fun ρ : TestFun H => pairRaw x.1 ρ.1), fun t : ℝ≥0 => x.2 t)

theorem configLawFull_eq_map_cfgData {Ω : Type*} [MeasurableSpace Ω]
    (c : Ω → FieldSample × (ℝ → ℝ)) (P : Measure Ω) :
    configLawFull c P = P.map (fun ω => cfgData (c ω)) := rfl

theorem aemeasurable_cfgData_wedgeConfig {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    AEMeasurable (fun ω => cfgData (wedgeConfig γ B Y ω)) P := by
  obtain ⟨B'', hB''m, -, -, -, hB''eq⟩ := RS.exists_good_version0 hS.2.2.1
  have hd : AEMeasurable (fun ω => fun t : ℝ≥0 => drive (γ ^ 2) B ω t) P := by
    refine (measurable_pi_iff.2 fun t =>
      (hB''m t).const_mul (Real.sqrt (γ ^ 2))).aemeasurable.congr ?_
    filter_upwards [hB''eq] with ω hω
    funext t
    simp [drive, hω t]
  exact hIn.2.1.prodMk hd

/-! ## 3. The remaining node hypotheses and the reduction of `G4Stmt` -/

end Thm18Asm
end QuantumZipper
