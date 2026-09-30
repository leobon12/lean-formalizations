import QuantumZipper.Proofs.Zipper.Cor15MeasVerMain
import QuantumZipper.Proofs.Zipper.Cor15LawB1
import QuantumZipper.Proofs.Zipper.E5IncField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-UNZIPVER: the unzip version `Cor15UnzipVersionStmt` from two named inputs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.2 and §1.4
(Corollary 1.5). Task COR15-UNZIPVER.

`Cor15UnzipVersionStmt` (`Cor15MeasVerMain.lean`) asks for a free field `Y` with measurable
coordinates, independent of the shifted Brownian path `B(a + ·) − B(a)`, such that the unzipped
field `D_a c` is a.s. `RegEq` to `𝔥₀ + Y`. `RegEq` reads only the dyadic folded circles, so `Y`
is built from the (a.e.-measurable, `aemeasurable_coordsFull_unzip_sub`) circle coordinates `C`
of `D_a c − 𝔥₀`:

  `Y = R (nrm0 C) + C₀ · mass`,

where `nrm0` subtracts the coordinate at the circle `σ₀` of index `0`, and `R` is a measurable
reconstruction of a free field from its circle coordinates (input `FreeCircleReconStmt`).

* Freeness: the law of `nrm0 C` is the law of `nrm0 (coordsFull X)` (from the proved B1-FULL,
  `B1Full.b1_full`: the circle coordinates of the normalized unzipped field have the law of those
  of `𝔥₀ + X`); on the `X` side `R (nrm0 (coordsFull X))` is a modification of the free field
  `X − X(σ₀)·mass` (input `FreeCircleReconStmt`), hence free; freeness passes through the law
  (`isFreeGFFModConstH_of_map_eq`) and through the random constant `C₀`
  (`E5.isFreeGFFModConstH_of_ae_shift`).
* Independence: `Y` is a measurable function of `C`, and `C` is independent of the future path
  (input `Cor15UnzipCoordIndepStmt`, the Markov property of the unzipping).
* `RegEq`: `Y` has the raw values of `D_a c − 𝔥₀` at every dyadic folded circle.

The constant `C₀` must be carried: `RegEq` sees additive constants, and B1-FULL only controls
the law of the normalized coordinates. This is why the independence input is needed besides
B1-FULL.

**Inputs** (named `Prop`s, not proved here):
* `FreeCircleReconStmt`: a free field modulo constants is a.s. determined, at every admissible
  measure, by a fixed measurable functional of its dyadic folded-circle values (the circle averages
  generate the Gaussian Hilbert space of the field). Duplantier–Sheffield, *Liouville quantum
  gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1 and §6.1 (circle / boundary semicircle
  average processes; `h_ε → h` as `ε → 0`), `literature/0808.1560.pdf` pp. 13–14, 39–41.
* `Cor15UnzipCoordIndepStmt`: the circle coordinates of `D_a c` (a function of `h` and
  `B|[0,a]`) are independent of `B(a + ·) − B(a)`: the weak Markov property of Brownian motion
  with an independent field (`UnzipInvariance.indepFun_of_past_future`), Sheffield §1.4.

Own bookkeeping (the reduction); the analytic content sits in the two inputs and in B1-FULL.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CoordsFull B1Full

/-! ## Normalization of coordinate vectors at the index `0` -/

/-- Normalization of a coordinate vector at the index `0`. -/
def nrm0 (c : ℕ → ℝ) : ℕ → ℝ := fun i => c i - c 0

theorem measurable_nrm0 : Measurable nrm0 :=
  measurable_pi_iff.2 fun i => (measurable_pi_apply i).sub (measurable_pi_apply 0)

/-- The circle of index `0`. -/
abbrev sig0 : Measure ℂ := foldedCircle (fullIndex 0).1 (fullIndex 0).2

/-- `nrm0` of the circle coordinates is the circle coordinates of the field shifted by its value
at `σ₀` (folded circles are probability measures). -/
theorem nrm0_coordsFull (x : FieldSample) :
    nrm0 (coordsFull x) = coordsFull (addConst x (-(x sig0))) := by
  funext i
  simp only [nrm0, coordsFull, addConst, measure_univ, ENNReal.toReal_one, mul_one]
  ring

/-- `nrm0` of the normalized field's coordinates, minus those of `𝔥₀`, is `nrm0` of the
coordinates of the difference to `𝔥₀`. -/
theorem nrm0_coordsFull_nrm_sub (h0 : ℂ → ℝ) (z : FieldSample) :
    nrm0 (coordsFull (nrm z)) - nrm0 (coordsFull (ofFun h0)) =
      nrm0 (coordsFull (z - ofFun h0)) := by
  funext i
  simp only [Pi.sub_apply, nrm0, coordsFull_nrm]
  simp only [coordsFull, Pi.sub_apply]
  ring

/-! ## The two inputs -/

/-- **Reconstruction of a free field from its dyadic folded-circle values.** There is a fixed
map `R` from circle-coordinate vectors to fields, measurable at every measure, reproducing the
circle values of every field, such that for every free field modulo constants `X` and every
admissible `μ`, a.s. `R (coordsFull X) μ = X μ`.

(True: `X μ − μ(ℂ)·X σ₀` is a balanced increment, the `L²(P)`-limit of linear combinations of
balanced circle increments with coefficients depending only on the covariance kernel `neumannH`;
a fixed fast subsequence converges a.s.; `R` takes `μ(ℂ)·c₀` plus the `limUnder` of these
combinations. Duplantier–Sheffield 2011, Prop. 3.1, §6.1.) -/
def FreeCircleReconStmt : Prop :=
  ∃ R : (ℕ → ℝ) → FieldSample, (∀ μ : Measure ℂ, Measurable fun c => R c μ) ∧
    (∀ (x : FieldSample) (i : ℕ), R (coordsFull x) (foldedCircle (fullIndex i).1
      (fullIndex i).2) = x (foldedCircle (fullIndex i).1 (fullIndex i).2)) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ μ : Measure ℂ, IsAdmissibleH μ →
      (fun ω => R (coordsFull (X ω)) μ) =ᵐ[P] fun ω => X ω μ

/-- **Markov property of the unzipping, circle coordinates.** The circle coordinates of the
unzipped field's difference to `𝔥₀` are independent of the shifted Brownian path. -/
def Cor15UnzipCoordIndepStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
    ∀ a : ℝ, 0 < a →
    IndepFun (fun ω => coordsFull ((zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 -
      ofFun (h0rev κ))) (fun ω => shiftPath a (pathOf B ω)) P

/-! ## The construction -/

/-- The field built from a circle-coordinate vector: `R (nrm0 c) + c₀ · mass`. -/
def unzipVerOf (R : (ℕ → ℝ) → FieldSample) (c : ℕ → ℝ) : FieldSample :=
  addConst (R (nrm0 c)) (c 0)

theorem measurable_unzipVerOf {R : (ℕ → ℝ) → FieldSample}
    (hRm : ∀ μ : Measure ℂ, Measurable fun c => R c μ) : Measurable (unzipVerOf R) :=
  measurable_pi_iff.2 fun μ =>
    ((hRm μ).comp measurable_nrm0).add ((measurable_pi_apply 0).mul_const _)

/-- At the dyadic folded circles, `unzipVerOf R (coordsFull y)` has the values of `y`. -/
theorem unzipVerOf_coordsFull {R : (ℕ → ℝ) → FieldSample}
    (hRc : ∀ (x : FieldSample) (i : ℕ), R (coordsFull x) (foldedCircle (fullIndex i).1
      (fullIndex i).2) = x (foldedCircle (fullIndex i).1 (fullIndex i).2))
    (y : FieldSample) (i : ℕ) :
    unzipVerOf R (coordsFull y) (foldedCircle (fullIndex i).1 (fullIndex i).2) =
      y (foldedCircle (fullIndex i).1 (fullIndex i).2) := by
  simp only [unzipVerOf, addConst, nrm0_coordsFull, hRc, measure_univ, ENNReal.toReal_one,
    mul_one]
  simp only [coordsFull]
  ring

/-- `RegEq` of a field with `𝔥₀ + unzipVerOf R (coordsFull (x − 𝔥₀))`. -/
theorem regEq_unzipVerOf {R : (ℕ → ℝ) → FieldSample}
    (hRc : ∀ (x : FieldSample) (i : ℕ), R (coordsFull x) (foldedCircle (fullIndex i).1
      (fullIndex i).2) = x (foldedCircle (fullIndex i).1 (fullIndex i).2))
    (h0 : ℂ → ℝ) (x : FieldSample) :
    RegEq x (ofFun h0 + unzipVerOf R (coordsFull (x - ofFun h0))) := by
  have h : coordsFull x = coordsFull (ofFun h0 + unzipVerOf R (coordsFull (x - ofFun h0))) := by
    funext i
    have := unzipVerOf_coordsFull hRc (x - ofFun h0) i
    simp only [coordsFull, Pi.add_apply] at this ⊢
    rw [this, Pi.sub_apply]
    ring
  intro k z
  rw [avgReg_congr_full h]

/-! ## The main reduction -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Law of the normalized circle coordinates** of the unzipped field's difference to `𝔥₀`
(from the proved B1-FULL). -/
theorem map_nrm0_coordsFull_unzip_sub {κ a : ℝ} (hκ : 0 < κ) (hS : IsGrpSetup P B X)
    (ha : 0 < a) :
    P.map (fun ω => nrm0 (coordsFull ((zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 -
        ofFun (h0rev κ)))) =
      P.map (fun ω => nrm0 (coordsFull (X ω))) := by
  obtain ⟨hB, hX, hind⟩ := hS
  have hlaw : P.map (fun ω => b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) =
      P.map (fun ω => b1Data (grpCfg κ B X ω)) := b1_full κ hκ P B X hB hX hind ha
  set Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℕ → ℝ :=
    fun p => nrm0 p.1.1 - nrm0 (coordsFull (ofFun (h0rev κ))) with hΦ
  have hΦm : Measurable Φ :=
    (measurable_nrm0.comp (measurable_fst.comp measurable_fst)).sub measurable_const
  have h1 := aemeasurable_b1Data_unzip κ hκ hB hX hind ha
  have h0 := aemeasurable_b1Data_c κ hB hX (P := P)
  have e := congrArg (fun m => m.map Φ) hlaw
  rw [AEMeasurable.map_map_of_aemeasurable hΦm.aemeasurable h1,
    AEMeasurable.map_map_of_aemeasurable hΦm.aemeasurable h0] at e
  have f1 : Φ ∘ (fun ω => b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) =
      fun ω => nrm0 (coordsFull ((zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)).1 -
        ofFun (h0rev κ))) := by
    funext ω
    exact nrm0_coordsFull_nrm_sub _ _
  have f0 : Φ ∘ (fun ω => b1Data (grpCfg κ B X ω)) = fun ω => nrm0 (coordsFull (X ω)) := by
    funext ω
    simp only [Function.comp_apply, hΦ, b1Data]
    rw [nrm0_coordsFull_nrm_sub]
    congr 2
    funext μ
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [f1, f0] at e
  exact e

/-- **`Cor15UnzipVersionStmt` from the reconstruction input and the Markov input.** -/
theorem cor15UnzipVersionStmt_of_recon (hRec : FreeCircleReconStmt)
    (hI : Cor15UnzipCoordIndepStmt) : Cor15UnzipVersionStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  obtain ⟨R, hRm, hRc, hRX⟩ := hRec
  have hX := hS.2.1
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  -- the circle coordinates of the unzipped field's difference, and a measurable version
  have hCae := aemeasurable_coordsFull_unzip_sub (κ := κ) hS ha
  set C : Ω → ℕ → ℝ := hCae.mk _ with hCdef
  have hCm : Measurable C := hCae.measurable_mk
  have hCeq := hCae.ae_eq_mk
  -- the version
  set Y : Ω → FieldSample := fun ω => unzipVerOf R (C ω) with hYdef
  have hU := measurable_unzipVerOf hRm
  have hYm : ∀ μ : Measure ℂ, Measurable fun ω => Y ω μ := fun μ =>
    (measurable_pi_apply μ).comp (hU.comp hCm)
  -- freeness of `R (nrm0 C)`
  set Yb : Ω → FieldSample := fun ω => R (nrm0 (C ω)) with hYbdef
  have hRf : Measurable fun c => R c := measurable_pi_iff.2 hRm
  have hYbm : ∀ μ : Measure ℂ, Measurable fun ω => Yb ω μ := fun μ =>
    (hRm μ).comp (measurable_nrm0.comp hCm)
  set Z : Ω → FieldSample := fun ω => R (nrm0 (coordsFull (X ω))) with hZdef
  have hZm : ∀ μ : Measure ℂ, Measurable fun ω => Z ω μ := fun μ =>
    (hRm μ).comp (measurable_nrm0.comp (measurable_coordsFull.comp hXm))
  have hX0 : IsFreeGFFModConstH (fun ω => addConst (X ω) (-(X ω sig0))) P :=
    E5.isFreeGFFModConstH_of_ae_shift hX (fun ω => -(X ω sig0))
      (fun μ => (hX.measurable_coord μ).add ((hX.measurable_coord _).neg.mul_const _))
      (fun μ _ => ae_of_all _ fun ω => by simp only [addConst]; ring)
  have hZfree : IsFreeGFFModConstH Z P := by
    refine E5.isFreeGFFModConstH_of_ae_shift hX0 (fun _ => 0) hZm fun μ hμ => ?_
    filter_upwards [hRX P _ hX0 μ hμ] with ω hω
    simp only [hZdef, nrm0_coordsFull, mul_zero, add_zero]
    exact hω
  have hlawN : P.map (fun ω => nrm0 (C ω)) = P.map (fun ω => nrm0 (coordsFull (X ω))) := by
    rw [← map_nrm0_coordsFull_unzip_sub hκ hS ha]
    refine Measure.map_congr ?_
    filter_upwards [hCeq] with ω hω
    show nrm0 (C ω) = _
    rw [hCdef, ← hω]
  have hlawYb : P.map Yb = P.map Z := by
    have e1 : Yb = (fun c => R c) ∘ fun ω => nrm0 (C ω) := rfl
    have e2 : Z = (fun c => R c) ∘ fun ω => nrm0 (coordsFull (X ω)) := rfl
    rw [e1, e2, ← Measure.map_map (f := fun ω => nrm0 (C ω)) hRf (measurable_nrm0.comp hCm),
      ← Measure.map_map (f := fun ω => nrm0 (coordsFull (X ω))) hRf
        (measurable_nrm0.comp (measurable_coordsFull.comp hXm)), hlawN]
  have hYbfree : IsFreeGFFModConstH Yb P := isFreeGFFModConstH_of_map_eq hYbm hlawYb hZfree
  have hfree : IsFreeGFFModConstH Y P :=
    E5.isFreeGFFModConstH_of_ae_shift hYbfree (fun ω => C ω 0) hYm
      (fun μ _ => ae_of_all _ fun ω => by simp only [hYdef, unzipVerOf, addConst]; ring)
  -- independence
  have hindC : IndepFun C (fun ω => shiftPath a (pathOf B ω)) P :=
    (hI κ hκ hκ4 P B X hS a ha).congr hCeq (ae_eq_refl _)
  have hind : IndepFun (fun ω => shiftPath a (pathOf B ω)) Y P :=
    (hindC.comp hU measurable_id).symm
  refine ⟨Y, hYm, hfree, hind, ?_⟩
  filter_upwards [hCeq] with ω hω
  show RegEq _ (ofFun (h0rev κ) + unzipVerOf R (C ω))
  rw [hCdef, ← hω]
  exact regEq_unzipVerOf hRc _ _

end Cor15Group
end QuantumZipper
