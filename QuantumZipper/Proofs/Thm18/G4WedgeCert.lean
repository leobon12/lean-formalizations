import QuantumZipper.Proofs.Thm18.G4Read2Main
import QuantumZipper.Proofs.Wire3
import QuantumZipper.Proofs.LQG.WedgeBoundary
import QuantumZipper.Proofs.Zipper.Cor15RegBasic

/-!
# Theorem 1.8, node G4: boundary certificates of the wedge field

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). Task
G4-WEDGECERT.

`G4WedgeCertStmt` (defined in `G4Read2Main.lean`) is the a.s. certificate
`CertC γ (coordsFull (Y ω))` for the `(γ − 2/γ)`-wedge `Y` of the Theorem 1.8 setting: the field
rebuilt from the circle coordinates of `Y` has a vague boundary limit (`E1.M4.BCert`, a countable
certificate readable from the coordinates), no atoms (`AtomQ`) and infinite boundary mass on
`[0,∞)` (`InfQ`).

Route (own assembly of the proved wedge results):

* `CertF γ x` is the same certificate read off the field `x` itself; `CertC γ (coordsFull x)` is
  `CertF γ (fromC (coordsFull x))`, and `fromC (coordsFull x)` has the same regularized averages
  as `x` (`E1.coordsFull_fromC` + `UnzipFull.regEq_of_coordsFull`), so `certC_iff_certF` reduces
  the statement to a field-level one (`certF_congr`).
* `certF_of_isLQGGood`: for a *good* sample (`IsLQGGood γ x`) the dyadic boundary approximations
  have a vague limit (`LQGMeas.tendsto_bdryApprox_of_good`, plus local finiteness
  `IsLQGGood.qBoundaryMeasure_spec`) and are finite on compacts
  (`LogSing.isFiniteMeasureOnCompacts_bdryApprox`, from `IsRegularSample`); this gives `BCert`
  (`E1.M4.bCert_of_isVagueLimitR`), and `AtomQ`/`InfQ` are the countable forms of atomlessness
  and of infinite mass (`Cor15Group.atomQ_of_atomless`, `Cor15Group.infQ_of_measure_Ici`).
* `ae_certF_wedgeRefCanonical`: the canonical reference wedge field of a quantum wedge satisfies
  `CertF` a.s. Its goodness, its atomlessness and its positivity come from
  `Wire2.ae_wedge_canonical_spec` and `WedgeBdry.ae_bReg_canonical_wedgeField`; infinite boundary
  mass on `[0,∞)` from `WedgeBdry.ae_qBoundaryMeasure_Ici_top_wedgeField` with the proved
  free-field input `WedgeBdry.wedgeBdryFreeInfStmt_holds`, transported through the rescaling by
  `scaleParam` (`WedgeBdry.infMassIci_rescale`) — the same inputs as
  `WedgeBdry.ae_atomless_pos_of_isQuantumWedge`.
* `ae_certF_of_isQuantumWedge`: every quantum wedge inherits `CertF` through the law identity
  `fieldLawFull` and the coordinate event transfer `WedgeBdry.ae_of_fieldLawFull_eq` (both full
  data maps are a.e.-measurable: `Thm18Inputs`, `WedgeMeas.aemeasurable_wedgeRefData`).

Sources: Sheffield, arXiv:1012.4797, §1.6 (the wedge as a free field with an `α`-log singularity
plus an independent radial part; boundary measure) and Theorem 1.8 (1). The assembly is our own.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open Cor15Group BdryVague LQGMeas

/-! ## 1. The field-level certificate -/

/-- The boundary certificates (`BCert`, `AtomQ`, `InfQ`) read off a field sample. -/
def CertF (γ : ℝ) (x : FieldSample) : Prop :=
  E1.M4.BCert γ x ∧ AtomQ γ x ∧ InfQ γ x

theorem measurableSet_certF (γ : ℝ) : MeasurableSet {x : FieldSample | CertF γ x} :=
  (E1.M4.measurableSet_bCert γ).inter ((measurableSet_atomQ γ).inter (measurableSet_infQ γ))

theorem certF_congr {γ : ℝ} {x x' : FieldSample} (h : RegEq x x') : CertF γ x ↔ CertF γ x' := by
  have hav : avgReg x = avgReg x' := funext fun k => funext fun z => h k z
  have hb := Factorization.bdryApprox_congr hav γ
  have h1 : E1.M4.BCert γ x ↔ E1.M4.BCert γ x' := by simp only [E1.M4.BCert, hb]
  have h2 : AtomQ γ x ↔ AtomQ γ x' := by
    simp only [AtomQ, Thm14WDG.mIcc, InfMass.Psi, LQGMeas.bdryFun, hb]
  have h3 : InfQ γ x ↔ InfQ γ x' := infQ_congr hav
  exact and_congr h1 (and_congr h2 h3)

theorem certF_reconstruct (γ : ℝ) (x : FieldSample) :
    CertF γ (Factorization.reconstruct (Factorization.coords x)) ↔ CertF γ x :=
  certF_congr fun k z => by rw [Factorization.avgReg_reconstruct_coords]

/-- `CertC` on the coordinates of `x` is `CertF` on `x`. -/
theorem certC_iff_certF (γ : ℝ) (x : FieldSample) :
    CertC γ (CoordsFull.coordsFull x) ↔ CertF γ x := by
  show CertF γ (E1.fromC (CoordsFull.coordsFull x)) ↔ CertF γ x
  exact certF_congr (UnzipFull.regEq_of_coordsFull (E1.coordsFull_fromC x))

/-! ## 2. The certificate of a good sample -/

/-- A good sample has a vague boundary limit, namely `qBoundaryMeasure`. -/
theorem isVagueLimitR_qBoundaryMeasure_of_isLQGGood {γ : ℝ} {x : FieldSample}
    (hx : IsLQGGood γ x) : IsVagueLimitR (bdryApprox γ x) (qBoundaryMeasure γ x) :=
  ⟨hx.qBoundaryMeasure_spec.1, fun _ hf hfc => LQGMeas.tendsto_bdryApprox_of_good hx hf hfc⟩

/-- **The certificates of a good sample.** -/
theorem certF_of_isLQGGood {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hat : ∀ t : ℝ, qBoundaryMeasure γ x {t} = 0)
    (hinf : qBoundaryMeasure γ x (Ici (0 : ℝ)) = ⊤) : CertF γ x := by
  have hν := isVagueLimitR_qBoundaryMeasure_of_isLQGGood hx
  have hfin : ∀ k N : ℕ, bdryApprox γ x k (Icc (-(N : ℝ)) N) < ⊤ := fun k N =>
    (LogSing.isFiniteMeasureOnCompacts_bdryApprox hx.1 γ k).lt_top_of_isCompact isCompact_Icc
  exact ⟨E1.M4.bCert_of_isVagueLimitR hfin hν, atomQ_of_atomless hν hat,
    infQ_of_measure_Ici hν hinf⟩

/-! ## 3. The canonical reference wedge field -/

/-- **The certificates of the reference wedge field** (`α < Q`). -/
theorem ae_certF_wedgeRefCanonical {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', CertF γ (WedgeMeas.wedgeRef γ X A ω) := by
  have hgood := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A inferInstance hX hA hI
  have hcan := Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI
  have hbreg := WedgeBdry.ae_bReg_canonical_wedgeField hγ hγ2 hα hX hA hI
    (hcan.mono fun _ h => h.1)
  have hα1 : α < (α + Qc γ) / 2 := by linarith
  have hα2 : (α + Qc γ) / 2 < Qc γ := by linarith
  have hinf := WedgeBdry.ae_qBoundaryMeasure_Ici_top_wedgeField WedgeBdry.wedgeBdryFreeInfStmt_holds
    hγ hγ2 hα1 hα2 Ω' P' X A inferInstance hX hA hI
  filter_upwards [hcan, hbreg, hinf, hgood] with ω hc hb hi hg
  refine certF_of_isLQGGood hc.2.1 (fun t => hb.noAtom t) ?_
  exact (WedgeBdry.infMassIci_rescale hγ hg hc.1).2 hi

/-! ## 4. Every quantum wedge -/

/-- **The certificates of a quantum wedge** (`0 < γ < 2`, any `α < Q`; no measurability
hypothesis: the a.e.-measurability of the wedge data is `Wire2.aemeasurable_dataFull_of_isQuantumWedge`).
-/
theorem ae_certF_of_isQuantumWedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → FieldSample} (hY : IsQuantumWedge γ α Y P) : ∀ᵐ ω ∂P, CertF γ (Y ω) := by
  have hYm : AEMeasurable (fun ω => (CoordsFull.coordsFull (Y ω),
      fun ρ : TestFun H => pairRaw (Y ω) ρ.1)) P := by
    simpa only [WedgeMeas.dataFull] using
      Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hY.1 hY
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hY
  have hgood := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP' hX hA hI
  exact WedgeBdry.ae_of_fieldLawFull_eq hlaw hYm
    (WedgeMeas.aemeasurable_wedgeRefData hX hA hgood H) (CertF γ)
    (measurableSet_certF γ) (certF_reconstruct γ) (ae_certF_wedgeRefCanonical hγ hγ2 hα hX hA hI)

/-! ## 5. `G4WedgeCertStmt` -/

/-- **`G4WedgeCertStmt`**: a.s. the field rebuilt from the circle coordinates of the
`(γ − 2/γ)`-wedge has the boundary certificates `BCert`, `AtomQ`, `InfQ`. -/
theorem g4WedgeCertStmt : G4WedgeCertStmt := by
  intro γ Ω _ P _ B Y hS _
  obtain ⟨hγ, hγ2, -, hY, -⟩ := hS
  filter_upwards [ae_certF_of_isQuantumWedge (α := γ - 2 / γ) hγ hγ2 hY] with ω hω
  exact (certC_iff_certF γ (Y ω)).2 hω

end Thm18Asm
end QuantumZipper
