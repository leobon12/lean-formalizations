import QuantumZipper.Proofs.Zipper.E1Defs
import QuantumZipper.Proofs.LQG.InfiniteMass
import QuantumZipper.Proofs.LQG.CoordChangeMain
import QuantumZipper.Proofs.Field.Factorization

/-!
# E1-TR, pathwise part: `ν` on the live set in the coordinates of `Y_t`

`handoff/E1-PLAN.md`, node E1-TR ("Pathwise"). Paper: Sheffield, arXiv:1012.4797, Lemma 5.6 and
its proof (pp. 66–68: "given `f_t`, `h₀ = h̃ ∘ f_t + ĥ_t`"), §5.2 (pp. 57–59).

Deterministic statements, at one sample `ω`:

* `restrict_nuPalm_eq`: if `coordsFull h⁰ = coordsFull (coordChange Y_t F Q)` (B2(b),
  `B2.b2_coordsFull_eq`) and the **normalized** field `h⁰ − m` has a global vague limit of its
  boundary approximations, then `ν|_{liveNeg} = qBoundaryMeasureOn γ (coordChange Y_t F Q − m)
  (liveNeg)` (restriction of a global vague limit is the local one; uniqueness on open sets).
* `lhs_integrand_eq`: with moreover `m = evalReg Y_t ϖ_t + q_t` (`B2.b2_evalReg_split`), the
  inner integral on the left of E1-TR is `trInt … (Vr ω) (V^t, W⁰) (Y_t ω)`;
  `rhs_integrand_eq`: the inner integral on the right is `trInt … (Vr ω) (V^t, W⁰) (𝔥₀ + X ω')`.

The existence hypothesis of `restrict_nuPalm_eq` is *not* supplied by
`Blueprint.RevCouplingBoundaryMeasureRegular` (which gives a limit for `h⁰`, not for `h⁰ − m`):
`avgReg (addConst x c) = avgReg x + c` needs the raw circle-average sequences of `x` at real
points to converge (`LocalRule.RawConverges`), which is not known for `h⁰`. See
`handoff/E1-TR.md`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E1

open B2 CharFun UnzipInvariance UnzipFull

/-- The inner integral of E1-TR as a function of the driver `v`, the path data `d` and the field
`y` (which is `Y_t ω` on the left side and `𝔥₀ + X ω'` on the right side). -/
def trInt (κ t δ : ℝ) (ϖ : Measure ℂ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (v : ℝ → ℝ) (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (y : FieldSample) : ℝ≥0∞ :=
  ∫⁻ x in Icc (-δ) 0, Ψ x d *
      Φ (CoordsFull.coordsFull (addConst y (-(evalReg y (varpiT v t ϖ) + qt κ v t ϖ))))
    ∂qBoundaryMeasureOn (Real.sqrt κ)
      (addConst (coordChange y (revMap v t) (Qc (Real.sqrt κ)))
        (-(evalReg y (varpiT v t ϖ) + qt κ v t ϖ))) (liveNeg v t)

theorem coordsFull_addConst (y : FieldSample) (c : ℝ) (i : ℕ) :
    CoordsFull.coordsFull (addConst y c) i = CoordsFull.coordsFull y i + c := by
  simp [CoordsFull.coordsFull, addConst, measure_univ]

theorem coordsFull_addConst_congr {y y' : FieldSample}
    (h : CoordsFull.coordsFull y = CoordsFull.coordsFull y') (c : ℝ) :
    CoordsFull.coordsFull (addConst y c) = CoordsFull.coordsFull (addConst y' c) := by
  funext i; rw [coordsFull_addConst, coordsFull_addConst, h]

variable {Ω : Type*} {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

/-- **E1-TR, pathwise identification of `ν` on the live set** (conditional on the existence of
the global vague limit for the normalized field). -/
theorem restrict_nuPalm_eq {ω : Ω} (hc : Continuous fun s => B s ω)
    (hcf : CoordsFull.coordsFull (h0f κ T B X ω) = CoordsFull.coordsFull
      (coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t) (Qc (Real.sqrt κ))))
    (hex : ∃ l, IsVagueLimitR (bdryApprox (Real.sqrt κ)
      (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω)))) l) :
    (nuPalm κ T B X ϖ ω).restrict (liveNeg (Vr κ T B ω) t) =
      qBoundaryMeasureOn (Real.sqrt κ)
        (addConst (coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t) (Qc (Real.sqrt κ)))
          (-(mReg κ T B X ϖ ω))) (liveNeg (Vr κ T B ω) t) := by
  obtain ⟨l, hl⟩ := hex
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hI := isOpen_liveNeg hV t
  unfold nuPalm
  rw [qBoundaryMeasure_eq hl]
  rw [Factorization.bdryApprox_congr (CoordsFull.avgReg_congr_full
    (coordsFull_addConst_congr hcf _))] at hl
  exact (CoordChange.qBoundaryMeasureOn_eq hI (InfMass.isVagueLimitOnR_restrict hl hI)).symm

/-- **E1-TR, left integrand.** Under the hypotheses of `restrict_nuPalm_eq` and the split
`m = evalReg Y_t ϖ_t + q_t`, the inner integral of the left side of E1-TR is `trInt`. -/
theorem lhs_integrand_eq {ω : Ω} (hc : Continuous fun s => B s ω)
    (hT : 0 ≤ T) (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞)
    (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))
    (hcf : CoordsFull.coordsFull (h0f κ T B X ω) = CoordsFull.coordsFull
      (coordChange (Yf κ T t B X ω) (revMap (Vr κ T B ω) t) (Qc (Real.sqrt κ))))
    (hex : ∃ l, IsVagueLimitR (bdryApprox (Real.sqrt κ)
      (addConst (h0f κ T B X ω) (-(mReg κ T B X ϖ ω)))) l)
    (hm : mReg κ T B X ϖ ω = evalReg (Yf κ T t B X ω) (varpiT (Vr κ T B ω) t ϖ) +
      qt κ (Vr κ T B ω) t ϖ) :
    ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) t x}.indicator (fun x => Ψ x d *
        Φ (CoordsFull.coordsFull (addConst (Yf κ T t B X ω) (-(mReg κ T B X ϖ ω))))) x
      ∂nuPalm κ T B X ϖ ω =
    trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) d (Yf κ T t B X ω) := by
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  have hV0 : Vr κ T B ω 0 = 0 := vrev_zero hT
  have hL : MeasurableSet {x | IsLive (Vr κ T B ω) t x} :=
    (isOpen_setOf_isLive (t := t) hV).measurableSet
  rw [setLIntegral_indicator hL, inter_comm, Icc_inter_isLive_eq hV0,
    ← Measure.restrict_restrict measurableSet_Icc, restrict_nuPalm_eq hc hcf hex]
  unfold trInt
  rw [← hm]

/-- **E1-TR, right integrand**: definitional. -/
theorem rhs_integrand_eq (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (v : ℝ → ℝ) (d : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) (Y : FieldSample) :
    ∫⁻ x in Icc (-δ) 0, Ψ x d * Φ (CoordsFull.coordsFull
        (addConst (ofFun (h0rev κ) + Y) (-(mFix κ v t ϖ Y))))
      ∂qBoundaryMeasureOn (Real.sqrt κ) (addConst (hFix κ v t Y) (-(mFix κ v t ϖ Y)))
        (liveNeg v t) =
    trInt κ t δ ϖ Ψ Φ v d (ofFun (h0rev κ) + Y) := rfl

end E1
end QuantumZipper
