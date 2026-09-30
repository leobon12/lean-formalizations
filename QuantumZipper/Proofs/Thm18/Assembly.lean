import QuantumZipper.Statements.Thm18
import QuantumZipper.Proofs.Zipper.Thm13AssemblyStmt
import QuantumZipper.Proofs.LQG.WedgeMeasND
import QuantumZipper.Proofs.LQG.WedgeInfTotal
import QuantumZipper.Proofs.LQG.WedgeFinZeroCoupling
import QuantumZipper.Proofs.Complex.UniformizerRight
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

/-!
# Theorem 1.8, top-level conditional assembly (THM18-ASM, blueprint node S5-G5)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 and its proof
(§5.4). Blueprint: `blueprint/SECTION5_BLUEPRINT.md` §3.G, nodes G0–G5. G5 (the assembly) says:
wedge decomposition from G1 and G3, lengths agree from F1, zipper stationarity from G4.

Proved inputs used directly here:

* R23 (c) and WEDGE-MEAS: `WedgeMeasND.IsQuantumWedge.ae_unitArea` and
  `WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge`, with the two analytic inputs discharged
  by `WedgeFinZero.wedgeFiniteNearZero_holds` and `WedgeInf.wedgeInfiniteTotal`
  (`α = γ − 2/γ < Q`, since `γ² < 8`);
* `RS.rohdeSchrammSimple` (the SLE_{γ²} trace is a.s. a simple chord, `γ² < 4`);
* `CA.Uniformizer.riemannMappingCaratheodory` (so the global `uniformizer` of each component is a
  normalized uniformizer, via `Classical.epsilon_spec`);
* `Thm13Asm.E6Stmt` / `Thm13Asm.F1NodeStmt` (E6 and F1 of the Theorem 1.3 chain, hypotheses owned
  there), which give clause (3) of zipper stationarity for `t < 0` and the equality half of the
  lengths clause outright.

These facts are packaged as `Thm18Inputs` and handed to the remaining node hypotheses
(`G1Stmt`, `G3Stmt`, `LenPosStmt`, `G4Stmt`) as premises, so those obligations are weakened by
exactly what is already proved. The assembly itself is an own (trivial) argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## The setting and the proved inputs -/

/-- The hypotheses of `theorem1_8`. -/
def Thm18Setting (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) : Prop :=
  0 < γ ∧ γ < 2 ∧ IsBrownianReal B P ∧ IsQuantumWedge γ (γ - 2 / γ) Y P ∧
    IndepFun (pathOf B) Y P

/-- The consequences of the Theorem 1.8 setting that are supplied by proved nodes: R23 (c)
(unit area, goodness), WEDGE-MEAS (a.e.-measurable data), Rohde–Schramm (simple trace, hull =
trace image), Riemann mapping + Carathéodory (the chosen `uniformizer`s are normalized). -/
def Thm18Inputs (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (Y : Ω → FieldSample) : Prop :=
  (∀ᵐ ω ∂P, IsLQGGood γ (Y ω) ∧ qAreaMeasure γ (Y ω) (Metric.ball 0 1 ∩ H) = 1) ∧
  AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P ∧
  (∀ᵐ ω ∂P, IsSimpleChord (sleTrace (γ ^ 2) B ω) ∧
    (∀ t : ℝ, 0 ≤ t → fwdHull (drive (γ ^ 2) B ω) t = sleTrace (γ ^ 2) B ω '' Set.Ioc 0 t) ∧
    IsNormalizedUniformizer (leftComponent (sleTrace (γ ^ 2) B ω))
      (uniformizer (leftComponent (sleTrace (γ ^ 2) B ω))) ∧
    IsNormalizedUniformizer (rightComponent (sleTrace (γ ^ 2) B ω))
      (uniformizer (rightComponent (sleTrace (γ ^ 2) B ω))))

theorem alpha_lt_Qc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ - 2 / γ < Qc γ := by
  unfold Qc
  have h : 1 < 2 / γ := (one_lt_div hγ).2 hγ2
  linarith

theorem thm18Inputs_of_setting {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) : Thm18Inputs γ P B Y := by
  obtain ⟨hγ, hγ2, hB, hY, -⟩ := hS
  have hα := alpha_lt_Qc hγ hγ2
  have hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα
  have hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα
  refine ⟨WedgeMeasND.IsQuantumWedge.ae_unitArea hfin hinf hγ hγ2 hY,
    WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge hfin hinf hγ hγ2 hY, ?_⟩
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith
  filter_upwards [RS.rohdeSchrammSimple (γ ^ 2) (by positivity) hκ4 P B hB] with ω hω
  obtain ⟨⟨φ₁, h₁⟩, ⟨φ₂, h₂⟩⟩ := CA.Uniformizer.riemannMappingCaratheodory _ hω.1
  exact ⟨hω.1, hω.2, Classical.epsilon_spec ⟨φ₁, h₁⟩, Classical.epsilon_spec ⟨φ₂, h₂⟩⟩

/-- The Theorem 1.8 sample is a `P_*` sample of the Theorem 1.3 chain, with `κ = γ²`. -/
theorem isPStarSample_of_setting {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) :
    Thm13Asm.IsPStarSample (γ ^ 2) P Y B := by
  obtain ⟨hγ, hγ2, hB, hY, hI⟩ := hS
  refine ⟨by positivity, by nlinarith, ?_, hB, hI.symm⟩
  rw [Real.sqrt_sq hγ.le]
  exact hY

/-! ## The remaining node hypotheses (exact statements) -/

/-- **G1** (each side is a `γ`-quantum wedge; Sheffield §5.4, "follows for the left side from
Proposition 1.6 and for the right side by symmetry"). Owner: G1 (deps D4⁺, E5, G0, A1(e), B4(d),
KT2). Premises: the setting and the proved inputs. -/
def G1Stmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    IsQuantumWedge γ γ (componentSurface γ B Y true) P ∧
      IsQuantumWedge γ γ (componentSurface γ B Y false) P

/-! ## Assembly -/

end Thm18Asm
end QuantumZipper
