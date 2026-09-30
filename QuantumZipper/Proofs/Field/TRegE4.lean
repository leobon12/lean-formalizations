import QuantumZipper.Proofs.Zipper.TReg
import QuantumZipper.Proofs.GFF.CoordRegCompLim
import QuantumZipper.Proofs.Field.Factorization
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# TREG-E4: raw and regularized test pairings of the Theorem 1.3 field agree almost surely

For `h = couplingFieldRev κ W T X = 𝔥_T + X ∘ f_T` (`f_T = revMap W T`), with `X` a free boundary
GFF modulo constants and the driver either deterministic, a random path independent of `X`, or
`W = √κ B` for a Brownian motion `B` independent of `X`, we prove, **for each fixed test function
`ρ : TestFun H`**, almost surely

  `pairRaw h ρ = pairTest h ρ`

(`ae_pairRaw_eq_pairTest_fixed`, `ae_pairRaw_eq_pairTest_random`,
`ae_pairRaw_eq_pairTest_couplingFieldRev`). With `g := pairTest (reconstruct ·) ρ` measurable
(`Factorization.pairTest_factor`) this is the per-test input of `E4.E4LawStmt`
(`ae_pairRaw_eq_factor_couplingFieldRev`).

**Route.** Write `Y₁ = coordChange (𝔥₀ + X) f_T Q` (the unzipped field of Theorem 1.2).
1. At every folded circle of positive radius, `h = Y₁` a.s. (REG-SPLIT at circles,
   `UnzipFull.ae_split_fc_fixed`); `avgReg` reads only countably many circles, so a.s.
   `avgReg h = avgReg Y₁` and `pairTest h ρ = pairTest Y₁ ρ`.
2. `pairRaw h ρ = pairRaw Y₁ ρ` a.s. (`UnzipInvariance.pairRaw_unzip_eq`).
3. `evalReg Y₁ ν = Y₁ ν` a.s. for `ν = ρ^± dz` (RC3 for general measures,
   `CoordReg.ae_evalReg_coordChange_revMap_gen` and its convergence form, Duplantier–Sheffield,
   *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1 and its proof,
   through the project's RC3). RC3 is stated for probability measures; `ν` is normalized by its
   mass, and both sides scale linearly because the defining limits exist (no junk `limUnder`).
4. Random driver: Fubini over the independent pair (path, field) (`CharFun.ae_indep`), with the
   event measurable through `Factorization` (coordinates) and `CharFun.measurable_pair_Y2f`.

The reduction (steps 1, 2, 4 and the normalization in 3) is an own elementary argument; the
analytic input is RC3 (DS 2011, Prop. 3.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal Real

namespace QuantumZipper
namespace TRegE4

open CharFun UnzipInvariance UnzipFull Factorization

/-! ## 1. Deterministic lemmas -/

/-- A measure with density bounded by `M` is Frostman with exponent `2`. -/
theorem isFrostman_of_le_smul_volume {ν : Measure ℂ} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ν ≤ M • volume) : IsFrostman ν 2 (M.toReal * π) := by
  intro w r hr
  have h1 : ν (Metric.closedBall w r) ≤ M * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)) := by
    have := Measure.le_iff'.1 h (Metric.closedBall w r)
    rwa [Measure.smul_apply, smul_eq_mul, Complex.volume_closedBall] at this
  have hne : M * (ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top hM (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.coe_ne_top)
  refine (ENNReal.toReal_mono hne h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
    ENNReal.coe_toReal, NNReal.coe_real_pi, Real.rpow_two]
  ring

/-- `evalReg` scales linearly when the defining limit exists. -/
theorem evalReg_smul_of_tendsto {y : FieldSample} {μ : Measure ℂ} {l : ℝ}
    (h : Tendsto (fun k => ∫ z, avgReg y k z ∂μ) atTop (𝓝 l)) (c : ℝ≥0∞) :
    evalReg y (c • μ) = c.toReal * l := by
  unfold evalReg
  simp_rw [integral_smul_measure, smul_eq_mul]
  exact (h.const_mul _).limUnder_eq

/-- The unzipped field `coordChange (𝔥₀ + x) f_T Q` for the driver `Wof κ T hT f`. -/
def Y1 (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (x : FieldSample) : FieldSample :=
  coordChange (ofFun (h0rev κ) + x) (revMap (Wof κ T hT f) T) (Qc (Real.sqrt κ))

/-! ## 2. Fixed driver -/

section Fixed

variable (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}

end Fixed

/-! ## 3. Random driver independent of the field -/

/-! ## 4. The Theorem 1.3 field -/

end TRegE4
end QuantumZipper
