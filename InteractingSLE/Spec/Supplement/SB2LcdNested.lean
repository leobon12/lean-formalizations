/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LcdFiner
import InteractingSLE.Spec.Exist.StagedLawData
import InteractingSLE.Spec.Sec5.CfRegQ
import InteractingSLE.Spec.Supplement.HullDetGenBR4a
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Supplement.SB2JK2

/-!
# SB2(2)'s conditional half: the nested conditional-variance identity (the erasure step)

Packet PROVE-T14-SB2LCOND. Supplement p. 632: "The initial erased portion adds no set in `D_A`. Its conditional
covariance there remains `G_{D_A}`, and the nested conditional-variance identity forces the harmonic mean to remain the
initial projection. Thus even the full erased history, its entry germ and stopping flags leave the same conditional
field in `D_A`." This file proves that step in general and uses it to remove the erasure clause from SB2(2)'s finer
input (`SB2LcdFiner`).

* `ae_eq_of_integral_eq_of_norm_eq`: a complex variable of constant modulus `‖w‖` with mean `w` equals `w` almost
  surely (`∫ |Z − w|² = ∫ |Z|² − 2 Re(w̄ ∫ Z) + |w|² = 0`);
* `ae_integral_integral_condExpKernel_eq`: the tower identity `∫ (∫ f dK'_ω) dK_{ω₀}(ω) = ∫ f dK_{ω₀}` for nested
  σ-algebras `𝒢 ≤ 𝒢'` (`condExp_condExp_of_le`);
* **`ae_map_condExpKernel_eq_of_norm_eq`** (the nested conditional-variance identity): if for every rational test the
  characteristic values of the field under the finer regular conditional law have, almost surely on `F ∈ 𝒢`, the same
  modulus as under the coarser one (equal conditional covariances), then the two conditional laws of the field agree
  almost surely on `F` (the finer conditional mean cannot move);
* `norm_integral_cexp_of_isGFF`: a GFF with piecewise-constant data has characteristic modulus
  `exp(−‖φ‖²_{H⁻¹(ℍ)}/2)`, whatever the data;
* **`ae_isGFF_condExpKernel_of_le`**: if the field is, given `𝒢`, the GFF of `g` and, given `𝒢' ⊇ 𝒢`, the GFF of SOME
  piecewise-constant data `g'`, then given `𝒢'` it is the GFF of `g` (almost surely on `F ∈ 𝒢`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lcd

open Restart Exist Exist.Staged Exist.StagedLaw

/-! ### A variable of constant modulus with the same mean is constant -/

section Rigid

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **L² rigidity**: if `‖Z‖ = ‖w‖` almost surely and `∫ Z = w` under a probability measure, then `Z = w` almost
surely. -/
theorem ae_eq_of_integral_eq_of_norm_eq {ν : Measure Ω} [IsProbabilityMeasure ν] {Z : Ω → ℂ} {w : ℂ}
    (hZm : AEStronglyMeasurable Z ν) (hZb : ∀ᵐ x ∂ν, ‖Z x‖ = ‖w‖) (hint : ∫ x, Z x ∂ν = w) :
    ∀ᵐ x ∂ν, Z x = w := by
  have hZi : Integrable Z ν := Integrable.of_bound (C := ‖w‖) hZm (hZb.mono fun x hx => hx.le)
  have hDi : Integrable (fun x => Z x * conj w) ν := hZi.mul_const _
  have hsq : ∀ᵐ x ∂ν, Complex.normSq (Z x - w) = 2 * Complex.normSq w - 2 * (Z x * conj w).re := by
    filter_upwards [hZb] with x hx
    rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq (Z x), hx, ← Complex.normSq_eq_norm_sq]
    ring
  have hrei : Integrable (fun x => (Z x * conj w).re) ν := by
    have h := hDi.re
    simp only [RCLike.re_to_complex] at h
    exact h
  have hre : ∫ x, (Z x * conj w).re ∂ν = Complex.normSq w := by
    have h := integral_re hDi
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_mul_const, hint, Complex.mul_conj, Complex.ofReal_re]
  have hint0 : ∫ x, Complex.normSq (Z x - w) ∂ν = 0 := by
    rw [integral_congr_ae hsq, integral_sub (integrable_const _) (hrei.const_mul 2), integral_const,
      integral_const_mul, hre]
    simp
  have hnn : 0 ≤ᵐ[ν] fun x => Complex.normSq (Z x - w) := Eventually.of_forall fun x => Complex.normSq_nonneg _
  have hmeas : AEStronglyMeasurable (fun x => Complex.normSq (Z x - w)) ν :=
    (Complex.continuous_normSq.comp_aestronglyMeasurable (hZm.sub aestronglyMeasurable_const))
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn
    (Integrable.of_bound (C := 4 * ‖w‖ ^ 2) hmeas (by
      filter_upwards [hZb] with x hx
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
      have h1 : ‖Z x - w‖ ≤ 2 * ‖w‖ := (norm_sub_le _ _).trans (by rw [hx]; linarith)
      nlinarith [norm_nonneg (Z x - w)]))).1 hint0
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.1 (Complex.normSq_eq_zero.1 hx)

end Rigid

/-! ### The tower identity for nested regular conditional laws -/

section Tower

variable {Ω : Type*} {𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The tower identity for nested regular conditional laws**, for one integrable complex function. -/
theorem ae_integral_integral_condExpKernel_eq (h𝒢 : 𝒢 ≤ 𝒢') (h𝒢' : 𝒢' ≤ mΩ) {f : Ω → ℂ} (hf : Integrable f P) :
    ∀ᵐ ω₀ ∂P, ∫ ω, (∫ x, f x ∂(condExpKernel P 𝒢' ω)) ∂(condExpKernel P 𝒢 ω₀) =
      ∫ x, f x ∂(condExpKernel P 𝒢 ω₀) := by
  have hA := condExp_ae_eq_integral_condExpKernel h𝒢' hf
  have hAi : Integrable (fun ω => ∫ x, f x ∂(condExpKernel P 𝒢' ω)) P := hf.integral_condExpKernel
  have h1 := condExp_ae_eq_integral_condExpKernel (h𝒢.trans h𝒢') hAi
  have h2 := condExp_ae_eq_integral_condExpKernel (h𝒢.trans h𝒢') hf
  have h3 : P[fun ω => ∫ x, f x ∂(condExpKernel P 𝒢' ω) | 𝒢] =ᵐ[P] P[P[f | 𝒢'] | 𝒢] :=
    condExp_congr_ae hA.symm
  have : SigmaFinite (P.trim h𝒢') := inferInstance
  have h4 := condExp_condExp_of_le (μ := P) (f := f) h𝒢 h𝒢'
  filter_upwards [h1, h2, h3, h4] with ω₀ e1 e2 e3 e4
  rw [← e1, e3, e4, e2]

end Tower

/-! ### The nested conditional-variance identity -/

section Nested

open LQGMetric in
/-- The characteristic value of the field `Y` at the test `φ` under the regular conditional law given `m`. -/
def condCF {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (Y : Ω → DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) (ω : Ω) : ℂ :=
  ∫ x, Complex.exp (Complex.I * (Y x φ : ℂ)) ∂(condExpKernel P m ω)

variable {Ω : Type*} {𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

open LQGMetric in
/-- **The nested conditional-variance identity.** Let `𝒢 ≤ 𝒢'` and `F ∈ 𝒢`. If, for every rational test, almost surely
on `F` the characteristic value of the field under the finer regular conditional law has the same modulus as under the
coarser one (for Gaussian conditional laws: the same conditional covariance), then almost surely on `F` the two regular
conditional laws of the field agree. (Under the coarser law the finer characteristic value has constant modulus
`|w|` and mean `w`, the coarser value, so it equals `w`.) -/
theorem ae_map_condExpKernel_eq_of_norm_eq (h𝒢 : 𝒢 ≤ 𝒢') (h𝒢' : 𝒢' ≤ mΩ) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    (hnorm : ∀ k : RatComb, ∀ᵐ ω ∂P, ω ∈ F →
      ‖condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k) ω‖ = ‖condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω‖) :
    ∀ᵐ ω ∂P, ω ∈ F → (condExpKernel P 𝒢' ω).map Y = (condExpKernel P 𝒢 ω).map Y := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans h𝒢'
  have hFm : MeasurableSet F := h𝒢m _ hF
  have hk : ∀ k : RatComb, ∀ᵐ ω ∂P, ω ∈ F →
      condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k) ω = condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω := by
    intro k
    have hXm : Measurable fun x => Y x (ratComb upperHalfPlaneOpens k) := (measurable_distOn_apply _).comp hY
    have hfm : Measurable fun x => Complex.exp (Complex.I * (Y x (ratComb upperHalfPlaneOpens k) : ℂ)) :=
      GFF.measurable_exp_I_mul hXm
    have hfi : Integrable (fun x => Complex.exp (Complex.I * (Y x (ratComb upperHalfPlaneOpens k) : ℂ))) P :=
      GFF.integrable_exp_I_mul (P := P) hXm
    have hAm : StronglyMeasurable[𝒢'] (condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k)) :=
      hfm.stronglyMeasurable.integral_condExpKernel
    have hBm : StronglyMeasurable[𝒢] (condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k)) :=
      hfm.stronglyMeasurable.integral_condExpKernel
    have hAm' : Measurable (condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k)) := (hAm.mono h𝒢').measurable
    have hBm' : Measurable (condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k)) := (hBm.mono h𝒢m).measurable
    have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ {ω | ω ∈ F →
        condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k) ω = condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω} := by
      filter_upwards [ae_integral_integral_condExpKernel_eq h𝒢 h𝒢' hfi,
        Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢m (hnorm k),
        Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢m hBm.measurable,
        Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢m hF,
        Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢m hF.compl] with ω₀ ht hn hB hmem hmemc
      by_cases hω₀ : ω₀ ∈ F
      · have hc := ae_eq_of_integral_eq_of_norm_eq (ν := condExpKernel P 𝒢 ω₀)
          (Z := condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k))
          (w := condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω₀) hAm'.aestronglyMeasurable
          (by
            filter_upwards [hn, hB, hmem hω₀] with ω h1 h2 h3
            exact (h1 h3).trans (congrArg norm h2)) ht
        filter_upwards [hc, hB] with ω h1 h2 _
        exact h1.trans h2.symm
      · filter_upwards [hmemc hω₀] with ω h1 h2
        exact absurd h2 h1
    have hEm : MeasurableSet {ω | ω ∈ F →
        condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k) ω = condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω} := by
      have e : {ω | ω ∈ F → condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k) ω =
          condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω} =
          Fᶜ ∪ {ω | condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k) ω =
            condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω} := by
        ext ω
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
        tauto
      rw [e]
      exact hFm.compl.union (measurableSet_eq_fun hAm' hBm')
    exact Sec5.Lemma56Stages.ae_of_ae_condExpKernel (μ := P) h𝒢m hEm hker
  filter_upwards [ae_all_iff.2 hk] with ω hω hωF
  refine Restart.ext_of_integral_cexp_ratComb fun k => ?_
  have hm : Measurable fun g : DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (g (ratComb upperHalfPlaneOpens k) : ℂ)) :=
    GFF.measurable_exp_I_mul (measurable_distOn_apply _)
  rw [integral_map hY.aemeasurable hm.aestronglyMeasurable, integral_map hY.aemeasurable hm.aestronglyMeasurable]
  exact hω k hωF

end Nested

/-! ### The GFF form -/

section GFF

/-- **The characteristic modulus of a GFF with piecewise-constant data** does not depend on the data:
`|E e^{i h(φ)}| = exp(−‖φ‖²_{H⁻¹(ℍ)}/2)`. -/
theorem norm_integral_cexp_of_isGFF {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → DistOn upperHalfPlaneOpens} {g : ℝ → ℝ} {S : Finset ℝ} (hg : IsPiecewiseConstantBoundaryData g S)
    (hY : IsGFFWithBoundaryData Q Y g S) (φ : TestOn upperHalfPlaneOpens) :
    ‖∫ ω, Complex.exp (Complex.I * (Y ω φ : ℂ)) ∂Q‖ =
      Real.exp (-QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) φ φ / 2) := by
  obtain ⟨c, hc, hcJ, hcb⟩ := Supp8.HullDetGen.exists_sorted_fn_eq hg
  have hY' : IsGFFWithBoundaryData Q Y c.fn c.jumps := by
    rw [hcJ]
    exact (Restart.isGFFWithBoundaryData_congr Q Y (S := (S : Set ℝ)) fun y hy => hcb y (by simpa using hy)).2 hY
  rw [integral_cexp_eq_gaussCF hc hY' φ, Restart.gaussCF, Complex.norm_exp]
  congr 1
  simp
  ring

variable {Ω : Type*} {𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The erasure step** (supplement p. 632): if, given `𝒢`, the field is the GFF of the piecewise-constant data
`g`, and, given the finer `𝒢' ⊇ 𝒢`, it is the GFF of SOME piecewise-constant data `g'` (the finer conditioning keeps
the Green covariance), then, given `𝒢'`, it is still the GFF of `g` (almost surely on `F ∈ 𝒢`). -/
theorem ae_isGFF_condExpKernel_of_le (h𝒢 : 𝒢 ≤ 𝒢') (h𝒢' : 𝒢' ≤ mΩ) {Y : Ω → DistOn upperHalfPlaneOpens}
    (hY : Measurable Y) {F : Set Ω} (hF : MeasurableSet[𝒢] F) {g g' : Ω → ℝ → ℝ} {S S' : Ω → Finset ℝ}
    (hg : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (g ω) (S ω))
    (hg' : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (g' ω) (S' ω))
    (hK : ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω) Y (g ω) (S ω))
    (hK' : ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝒢' ω) Y (g' ω) (S' ω)) :
    ∀ᵐ ω ∂P, ω ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝒢' ω) Y (g ω) (S ω) := by
  have hnorm : ∀ k : RatComb, ∀ᵐ ω ∂P, ω ∈ F →
      ‖condCF 𝒢' P Y (ratComb upperHalfPlaneOpens k) ω‖ = ‖condCF 𝒢 P Y (ratComb upperHalfPlaneOpens k) ω‖ := by
    intro k
    filter_upwards [hK, hK', hg, hg'] with ω h1 h2 h3 h4 hω
    rw [condCF, condCF, norm_integral_cexp_of_isGFF (h4 hω) (h2 hω), norm_integral_cexp_of_isGFF (h3 hω) (h1 hω)]
  filter_upwards [hK, ae_map_condExpKernel_eq_of_norm_eq h𝒢 h𝒢' hY hF hnorm] with ω h1 h2 hω
  exact Sec5.CfRegQ.isGFFWithBoundaryData_of_map_eq (h1 hω) hY (h2 hω).symm

end GFF

end InteractingSLE.Theorem14.SB.Lcd
