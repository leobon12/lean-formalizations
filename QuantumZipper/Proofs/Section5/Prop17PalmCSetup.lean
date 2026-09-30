import QuantumZipper.Proofs.Section5.Prop17PalmCCore
import QuantumZipper.Proofs.GFF.CoordRegHarm
import QuantumZipper.Proofs.GFF.LateralGerm

/-!
# Proposition 1.7, Palm-zoom node C: the D3⁺ setup at a fixed boundary point (PALM-C)

For `ϖ = foldedCircle 0 3` and `x ∈ [0, 1]` the Palm-shifted field
`N_ϖ(X + (γ/2)(neumannH x · − kPot ϖ))`, translated by `x`, is (formally) the D3⁺ model field
`zoomModel γ γ C ρ₀ X' g` with

* `X' = palmCField X x`, `X' ω μ = X ω (μ(· − x))` (the free field translated by `x`),
* `ρ₀ = palmCRho ϖ x = ϖ(· + x)` (so that `X' ρ₀ = X ϖ`),
* `g = palmCCorr γ ϖ x = −(γ/2) kPot ϖ (· + x) − ∫ shiftFun dϖ` (deterministic),

because `(γ/2) neumannH x (z + x) = γ(−log‖z‖)` (`neumannH_add_real`). This file proves that
these data form a D3⁺ `Setup` with `r = 1` and trivial conditioning data (`palmC_setup`):

* **translation invariance of the free field** (`isFreeGFFModConstH_translate`): `neumannH` is
  invariant under real translations and translations preserve admissibility, balance and
  linearity; the Gaussian property is reindexing (`IsGaussianProcess.comp_right`);
* **`kPot` of the folded circle** (`kPot_foldedCircle_three`): `kPot ϖ u = −2 log 3` for
  `‖u‖ < 3` (Jensen: the circle average of `log‖· − a‖` over `∂B(0,3)` is `log 3` for
  `‖a‖ < 3`, mathlib `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`), so `g` is
  constant, hence harmonic, on `ball 0 1`.

The identification (Sheffield, arXiv:1012.4797, proof of Prop. 1.6, p. 25: "the conditional law
of `h` given `x` is the GFF plus `(γ/2)G(x, ·)`; zooming in at `x` …"; DMS arXiv:1409.7055,
Prop. 4.7–4.8) is the node `Prop17PalmCAgreeStmt γ` (`Prop17PalmCMain.lean`), proved in
`Prop17PalmCAgree.lean`–`Prop17PalmCMeas.lean`.
Own elementary proofs (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

/-! ## 1. Translation invariance of the free field -/

theorem neumannH_add_real (u v : ℂ) (t : ℝ) :
    neumannH (u + t) (v + t) = neumannH u v := by
  simp only [neumannH, map_add, Complex.conj_ofReal, add_sub_add_right_eq_sub]

theorem isAdmissibleH_map_add_real {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (t : ℝ) :
    IsAdmissibleH (μ.map (· + (t : ℂ))) := by
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.2.1
  refine isAdmissibleH_map hμ hK hμK (measurable_add_const _)
    (continuous_id.add continuous_const).continuousOn ?_ one_pos fun a _ b _ => ?_
  · rintro _ ⟨z, hz, rfl⟩
    show 0 ≤ (z + (t : ℂ)).im
    simpa using (show 0 ≤ z.im from hKH hz)
  · rw [one_mul, add_sub_add_right_eq_sub]

theorem map_add_real_univ (μ : Measure ℂ) (t : ℝ) :
    μ.map (· + (t : ℂ)) univ = μ univ := by
  rw [Measure.map_apply (measurable_add_const _) MeasurableSet.univ, preimage_univ]

theorem kernelCov_neumannH_map_add_real (μ ν : Measure ℂ) (t : ℝ) :
    kernelCov neumannH (μ.map (· + (t : ℂ))) (ν.map (· + (t : ℂ))) = kernelCov neumannH μ ν := by
  unfold kernelCov
  have e : (fun z : ℂ => z + (t : ℂ)) = ⇑(Homeomorph.addRight (t : ℂ)).toMeasurableEquiv := rfl
  rw [e, integral_map_equiv]
  congr 1; funext a
  rw [integral_map_equiv]
  congr 1; funext b
  exact neumannH_add_real a b t

/-- **Translation invariance** of the free boundary GFF modulo constants along `ℝ`. -/
theorem isFreeGFFModConstH_translate {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} (hX : IsFreeGFFModConstH X P) (t : ℝ) :
    IsFreeGFFModConstH (fun ω (μ : Measure ℂ) => X ω (μ.map (· + (t : ℂ)))) P where
  measurable_coord := fun μ => hX.measurable_coord _
  gaussian := by
    let f : {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} →
        {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ} :=
      fun p => ⟨(p.1.1.map (· + (t : ℂ)), p.1.2.map (· + (t : ℂ))),
        isAdmissibleH_map_add_real p.2.1 t, isAdmissibleH_map_add_real p.2.2.1 t, by
          rw [map_add_real_univ, map_add_real_univ]; exact p.2.2.2⟩
    exact hX.gaussian.comp_right f
  centered := fun μ ν hμ hν h => hX.centered _ _ (isAdmissibleH_map_add_real hμ t)
    (isAdmissibleH_map_add_real hν t) (by rw [map_add_real_univ, map_add_real_univ, h])
  covariance_eq := fun p q hp1 hp2 hp hq1 hq2 hq => by
    have h := hX.covariance_eq (p.1.map (· + (t : ℂ)), p.2.map (· + (t : ℂ)))
      (q.1.map (· + (t : ℂ)), q.2.map (· + (t : ℂ))) (isAdmissibleH_map_add_real hp1 t)
      (isAdmissibleH_map_add_real hp2 t) (by rw [map_add_real_univ, map_add_real_univ, hp])
      (isAdmissibleH_map_add_real hq1 t) (isAdmissibleH_map_add_real hq2 t)
      (by rw [map_add_real_univ, map_add_real_univ, hq])
    refine h.trans ?_
    simp only [kernelCov2, kernelCov_neumannH_map_add_real]
  linear := fun μ ν hμ hν a b => by
    have h := hX.linear _ _ (isAdmissibleH_map_add_real hμ t) (isAdmissibleH_map_add_real hν t)
      a b
    refine Filter.EventuallyEq.trans (Eventually.of_forall fun ω => ?_) h
    show X ω ((a • μ + b • ν).map (· + (t : ℂ))) =
      X ω (a • μ.map (· + (t : ℂ)) + b • ν.map (· + (t : ℂ)))
    rw [Measure.map_add _ _ (measurable_add_const _), Measure.map_smul, Measure.map_smul]
    all_goals exact (measurable_add_const _).aemeasurable

/-! ## 2. The potential of the folded circle of radius 3 -/

theorem palmC_neumannH_foldH (u w : ℂ) : neumannH u (foldH w) = neumannH u w := by
  unfold foldH
  split_ifs
  · rfl
  · simp only [neumannH, Complex.conj_conj]; ring

theorem palmC_measurable_neumannH (u : ℂ) : Measurable (neumannH u) := by
  unfold neumannH
  fun_prop

/-- `kPot (foldedCircle 0 3) u = −2 log 3` for `‖u‖ < 3` (Jensen's formula for the circle
average of `log‖· − a‖`). -/
theorem kPot_foldedCircle_three {u : ℂ} (hu : ‖u‖ < 3) :
    kPot (foldedCircle 0 3) u = -2 * Real.log 3 := by
  unfold kPot foldedCircle
  rw [integral_map measurable_foldH.aemeasurable
    (palmC_measurable_neumannH u).aestronglyMeasurable]
  simp_rw [palmC_neumannH_foldH]
  rw [CoordReg.integral_circleUnif_eq_circleAverage (palmC_measurable_neumannH u)]
  have e : neumannH u = fun w => (-1 : ℝ) • (Real.log ‖w - u‖ + Real.log ‖w - conj u‖) := by
    funext w
    simp only [neumannH]
    rw [norm_sub_rev u w, show u - conj w = conj (conj u - w) by simp, Complex.norm_conj,
      norm_sub_rev (conj u) w, smul_eq_mul]
    ring
  have hav : ∀ a : ℂ, ‖a‖ < 3 → Real.circleAverage (fun w => Real.log ‖w - a‖) 0 3 =
      Real.log 3 := by
    intro a ha
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (by norm_num),
      (Real.posLog_eq_zero_iff _).2, add_zero]
    rw [zero_sub, norm_neg, abs_le]
    constructor
    · have : 0 ≤ (3 : ℝ)⁻¹ * ‖a‖ := by positivity
      linarith
    · rw [inv_mul_le_iff₀ (by norm_num)]; linarith
  rw [e, Real.circleAverage_fun_smul, Real.circleAverage_fun_add (circleIntegrable_log_norm_sub_const _)
    (circleIntegrable_log_norm_sub_const _), hav u hu, hav (conj u) (by rwa [Complex.norm_conj]), smul_eq_mul]
  ring

end Raw
end FieldLaw
end S5
end QuantumZipper
