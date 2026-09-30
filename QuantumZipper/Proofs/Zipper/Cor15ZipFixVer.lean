import QuantumZipper.Proofs.Zipper.Cor15ZipFixReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D42 (COR15-ZIPFIX): the zip version modulo additive constants, from a coordinate law

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5(a) and §1.4:
the zipped field is `𝔥₀` plus a free field **modulo additive constants**, independent of the
zipped driver.

* `Cor15ZipVersionStmt'`: the restated version form (the old `Cor15ZipVersionStmt` asked for
  `RegEq` with `𝔥₀ + Y` including the constant, which is false, see `Cor15ZipFixReduce`): a
  measurable free `Y`, independent of the normalized zipped driver, whose regularized circle
  averages are those of the zipped field minus `𝔥₀`, up to a random constant `lam`.
* `cor15ZipGenuineStmt'_of_version'`: it gives `Cor15ZipGenuineStmt'`.
* `cor15ZipVersionStmt'_of_coordLaw`: it follows from the proved reconstruction input
  `FreeCircleReconStmt`, the **coordinate law** `Cor15ZipCoordLawStmt'` (a.e.-measurability and
  joint law of the circle coordinates of the zipped field's difference to `𝔥₀`, normalized at
  `σ₀`, with the zipped driver = that of `(nrm0 (coordsFull X), B)`) and the raw circle-average
  convergence of the zipped field `Cor15ZipRawConvStmt`. The version is the unzip-side
  construction without the constant: `Y = R (nrm0 C)`, `lam = C 0` (`Cor15UnzipVerMain`); the
  constant `C 0` need not be measurable.
* `theorem1_5_of_theorem1_3_of_zipFixCoord'`: Corollary 1.5 from these inputs.

Own bookkeeping (as `Cor15UnzipVerMain`); the reconstruction input follows Duplantier–Sheffield,
Invent. Math. 185 (2011), Prop. 3.1 and §6.1.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CoordsFull

/-- **Zip direction, version form modulo constants** (D42). -/
def Cor15ZipVersionStmt' : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∃ (Y : Ω → FieldSample) (lam : Ω → ℝ),
      (∀ μ : Measure ℂ, Measurable fun ω => Y ω μ) ∧
      IsFreeGFFModConstH Y P ∧
      IndepFun (fun ω => zipDrv κ a (grpCfg κ B X ω)) Y P ∧
      ∀ᵐ ω ∂P, ∀ k z, avgReg (zipFld κ a (grpCfg κ B X ω)) k z =
        avgReg (ofFun (h0rev κ) + Y ω) k z + lam ω

/-- **Coordinate law of the zipped configuration, modulo constants** (Corollary 1.5(a) read on the
normalized circle coordinates and the zipped driver). -/
def Cor15ZipCoordLawStmt' : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a →
    AEMeasurable (fun ω => nrm0 (coordsFull (zipFld κ a (grpCfg κ B X ω) - ofFun (h0rev κ)))) P ∧
    P.map (fun ω => (nrm0 (coordsFull (zipFld κ a (grpCfg κ B X ω) - ofFun (h0rev κ))),
        zipDrv κ a (grpCfg κ B X ω))) =
      P.map (fun ω => (nrm0 (coordsFull (X ω)), pathOf B ω))

/-- **Raw circle averages of the zipped field converge** at every dyadic approximation. -/
def Cor15ZipRawConvStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a → ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ z : ℂ, ∃ l, Tendsto
      (fun n => zipFld κ a (grpCfg κ B X ω) (foldedCircle (dyadicRoundC n z) (radius k)))
      atTop (𝓝 l)

/-- **`Cor15ZipGenuineStmt'` from the version form.** -/
theorem cor15ZipGenuineStmt'_of_version' (h13 : theorem1_3) (h : Cor15ZipVersionStmt') :
    Cor15ZipGenuineStmt' := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  obtain ⟨Y, lam, -, hfree, hind, hreg⟩ := h κ hκ hκ4 P B X hS a ha
  refine ⟨fun u ω => zipDrv κ a (grpCfg κ B X ω) u, Y, lam,
    ⟨isBrownianReal_zipDrv h13 hκ hκ4 hS ha, hfree, hind⟩, ?_⟩
  filter_upwards [hreg] with ω hω
  exact ⟨hω, fun u hu => zipCapUp_snd_eq_sqrt_mul_zipDrv hκ (grpCfg κ B X ω) hu⟩

/-- Pathwise: with `C = coordsFull (x − 𝔥₀)` and raw convergence of `x`, the regularized averages
of `x` are those of `𝔥₀ + R (nrm0 C)` plus `C 0`. -/
theorem avgReg_eq_recon_add {R : (ℕ → ℝ) → FieldSample}
    (hRc : ∀ (x : FieldSample) (i : ℕ), R (coordsFull x) (foldedCircle (fullIndex i).1
      (fullIndex i).2) = x (foldedCircle (fullIndex i).1 (fullIndex i).2))
    (h0 : ℂ → ℝ) (x : FieldSample)
    (hraw : ∀ k : ℕ, ∀ z : ℂ, ∃ l, Tendsto
      (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)) (k : ℕ) (z : ℂ) :
    avgReg x k z = avgReg (ofFun h0 + R (nrm0 (coordsFull (x - ofFun h0)))) k z +
      coordsFull (x - ofFun h0) 0 := by
  set w : FieldSample := x - ofFun h0 with hw
  have hc : coordsFull (ofFun h0 + R (nrm0 (coordsFull w))) =
      coordsFull (addConst x (-(coordsFull w 0))) := by
    funext i
    have := hRc (addConst w (-(w sig0))) i
    rw [← nrm0_coordsFull] at this
    simp only [coordsFull, Pi.add_apply] at this ⊢
    rw [this]
    simp only [addConst, measure_univ, ENNReal.toReal_one, mul_one, hw, Pi.sub_apply]
    ring
  rw [avgReg_congr_full hc, LocalRule.avgReg_addConst_of_tendsto (hraw k z)]
  ring

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **`Cor15ZipVersionStmt'` from the coordinate law.** -/
theorem cor15ZipVersionStmt'_of_coordLaw (h13 : theorem1_3) (hRec : FreeCircleReconStmt)
    (hL : Cor15ZipCoordLawStmt') (hRaw : Cor15ZipRawConvStmt) : Cor15ZipVersionStmt' := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  obtain ⟨R, hRm, hRc, hRX⟩ := hRec
  have hX := hS.2.1
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hRf : Measurable fun c => R c := measurable_pi_iff.2 hRm
  set C' : Ω → ℕ → ℝ := fun ω => coordsFull (zipFld κ a (grpCfg κ B X ω) - ofFun (h0rev κ))
    with hC'def
  obtain ⟨hNae, hlaw0⟩ := hL κ hκ hκ4 P B X hS a ha
  set N : Ω → ℕ → ℝ := hNae.mk _ with hNdef
  have hNm : Measurable N := hNae.measurable_mk
  have hNeq : (fun ω => nrm0 (C' ω)) =ᵐ[P] N := hNae.ae_eq_mk
  set Y : Ω → FieldSample := fun ω => R (N ω) with hYdef
  have hYm : ∀ μ : Measure ℂ, Measurable fun ω => Y ω μ := fun μ => (hRm μ).comp hNm
  -- the genuine side: `Z = R (nrm0 (coordsFull X))` is free and independent of `B`
  set Z : Ω → FieldSample := fun ω => R (nrm0 (coordsFull (X ω))) with hZdef
  have hZmeas : Measurable Z := hRf.comp (measurable_nrm0.comp (measurable_coordsFull.comp hXm))
  have hZm : ∀ μ : Measure ℂ, Measurable fun ω => Z ω μ := fun μ =>
    (measurable_pi_apply μ).comp hZmeas
  have hX0 : IsFreeGFFModConstH (fun ω => addConst (X ω) (-(X ω sig0))) P :=
    E5.isFreeGFFModConstH_of_ae_shift hX (fun ω => -(X ω sig0))
      (fun μ => (hX.measurable_coord μ).add ((hX.measurable_coord _).neg.mul_const _))
      (fun μ _ => ae_of_all _ fun ω => by simp only [addConst]; ring)
  have hZfree : IsFreeGFFModConstH Z P := by
    refine E5.isFreeGFFModConstH_of_ae_shift hX0 (fun _ => 0) hZm fun μ hμ => ?_
    filter_upwards [hRX P _ hX0 μ hμ] with ω hω
    simp only [hZdef, nrm0_coordsFull, mul_zero, add_zero]
    exact hω
  have hZind : IndepFun Z (pathOf B) P :=
    hS.2.2.symm.comp (hRf.comp (measurable_nrm0.comp measurable_coordsFull)) measurable_id
  -- the law of the pairs
  have hB' := IsBrownianReal.aemeasurable_pathOf hS.1
  have hD := aemeasurable_zipDrv h13 hκ hκ4 hS.1 hS.2.1 hS.2.2 ha
  have hRid : Measurable fun p : (ℕ → ℝ) × (ℝ≥0 → ℝ) => (R p.1, p.2) :=
    (hRf.comp measurable_fst).prodMk measurable_snd
  have hlaw : P.map (fun ω => (R (nrm0 (C' ω)), zipDrv κ a (grpCfg κ B X ω))) =
      P.map (fun ω => (Z ω, pathOf B ω)) := by
    have e : (P.map (fun ω => (nrm0 (C' ω), zipDrv κ a (grpCfg κ B X ω)))).map
          (fun p : (ℕ → ℝ) × (ℝ≥0 → ℝ) => (R p.1, p.2)) =
        (P.map (fun ω => (nrm0 (coordsFull (X ω)), pathOf B ω))).map
          (fun p : (ℕ → ℝ) × (ℝ≥0 → ℝ) => (R p.1, p.2)) := by
      rw [← hlaw0]
    have h1 : AEMeasurable (fun ω => (nrm0 (C' ω), zipDrv κ a (grpCfg κ B X ω))) P :=
      hNae.prodMk hD
    have h2 : AEMeasurable (fun ω => (nrm0 (coordsFull (X ω)), pathOf B ω)) P :=
      (measurable_nrm0.comp (measurable_coordsFull.comp hXm)).aemeasurable.prodMk hB'
    rw [AEMeasurable.map_map_of_aemeasurable hRid.aemeasurable h1,
      AEMeasurable.map_map_of_aemeasurable hRid.aemeasurable h2] at e
    exact e
  obtain ⟨hfree, hind⟩ := free_indep_of_map_eq
    (f := fun ω => (R (nrm0 (C' ω)), zipDrv κ a (grpCfg κ B X ω)))
    (g := fun ω => (Z ω, pathOf B ω)) (Y := Y) hYm
    (hNeq.mono fun ω hω => by show R (N ω) = R (nrm0 (C' ω)); rw [← hω])
    ((measurable_pi_iff.2 hYm).aemeasurable.prodMk hD)
    (hZmeas.aemeasurable.prodMk hB') hlaw hZfree hZind
  refine ⟨Y, fun ω => C' ω 0, hYm, hfree, hind.symm, ?_⟩
  filter_upwards [hNeq, hRaw κ hκ hκ4 P B X hS a ha] with ω hω hraw k z
  have := avgReg_eq_recon_add hRc (h0rev κ) (zipFld κ a (grpCfg κ B X ω)) hraw k z
  show _ = avgReg (ofFun (h0rev κ) + R (N ω)) k z + C' ω 0
  rw [← hω]
  exact this

end Cor15Group
end QuantumZipper
