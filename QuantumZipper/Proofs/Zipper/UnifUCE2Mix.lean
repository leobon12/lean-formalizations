import QuantumZipper.Proofs.Zipper.UnifRC3Mix
import Mathlib.Probability.Kernel.MeasurableIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# UNIF-RC3-E2 (decision D33), step 1: mixtures with different maps and different centres

The E1 radius modulus (`UnifUC1RadBasic.abs_kernelCov2_muUS_rad_le`) uses the MIX lemma
`abs_kernelCov2_mix_le` with a *single* push map `ψ` and a *single* centre `z`. The time modulus
E2 needs more: `μ_{u,s,ρ}` and `μ_{u',s',ρ}` are mixtures, over the **same** base measure
`fc(d, 2^{-k})`, of pushed circles with **different centre maps** and **different push maps**:

`μ_{p,ρ} = ∫_z νT W (R_p z) ρ u d(fc(d, 2^{-k}))(z)`

(`R_p = RUS W p`, `ψ_u = fwdMapInv W u`; see `muUS_mixFc` below). The centre map `z ↦ R_p z` has
to be carried through the Fubini step, which is what this file does:

* `kernelCov_mixFc_left`: `kernelCov ((bindFc (A.map w) ρ).map ψ) κ = ∫ z, kernelCov
  ((fc (w z) ρ).map ψ) κ ∂A` for a measurable centre map `w` (the proof is the `integral_map`
  change of variables applied to `CircleFubini.integral_bind_circle`; the parametric integral
  `z ↦ ∫ y, F y ∂fc(z,ρ)` is measurable by `StronglyMeasurable.integral_kernel_prod_right'`);
* `kernelCov2_mixFc_left`, `integrable_kernelCov2_mixFc`: the bilinear (pair) versions;
* `energy_mixFc_le`: **the general mixture bound.** If the per-`z` energies are bounded by a
  function `K`, then the energy of the two mixtures is `≤ (∫ √K dA)²`. This is the
  Cauchy–Schwarz/Hilbert-space argument of `abs_kernelCov2_mix_le` (freeVec inner product), with
  the sup replaced by an integral, which is what lets the E2 proof discard the thin strip
  `{Im z < τ}` (where the stability estimate RSTAB degenerates) at the cost of its `A`-measure;
* `abs_kernelCov2_mix_le_two`: the sup form (corollary).

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1; the interpolation between the
large-`Im z` regime and the strip is an own elementary argument.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint GFFExist

variable {A : Measure ℂ} [IsProbabilityMeasure A]

/-! ## Fubini with a centre map -/

/-- **Fubini for circle mixtures with a measurable centre map.** -/
theorem kernelCov_mixFc_left {w : ℂ → ℂ} (hw : Measurable w) {ψ : ℂ → ℂ} (hψ : Measurable ψ)
    {ρ : ℝ} {κ : Measure ℂ} [IsFiniteMeasure κ] {P : ℝ}
    (hb : ∀ᵐ y ∂bindFc (A.map w) ρ, |neuPot κ (ψ y)| ≤ P) :
    Integrable (fun z => kernelCov neumannH ((foldedCircle (w z) ρ).map ψ) κ) A ∧
      kernelCov neumannH ((bindFc (A.map w) ρ).map ψ) κ =
        ∫ z, kernelCov neumannH ((foldedCircle (w z) ρ).map ψ) κ ∂A := by
  have e : ∀ z : ℂ, kernelCov neumannH ((foldedCircle z ρ).map ψ) κ =
      ∫ y, neuPot κ (ψ y) ∂foldedCircle z ρ := fun z =>
    integral_map hψ.aemeasurable (measurable_neuPot κ).aestronglyMeasurable
  have hψκ : Measurable fun z : ℂ => ∫ y, neuPot κ (ψ y) ∂foldedCircle z ρ :=
    (StronglyMeasurable.integral_kernel_prod_right' (κ := CircleFubini.circleKernel ρ)
      (f := fun q : ℂ × ℂ => neuPot κ (ψ q.2))
      (((measurable_neuPot κ).comp hψ).comp measurable_snd).stronglyMeasurable).measurable
  have hfin : IsFiniteMeasure (bindFc (A.map w) ρ) :=
    CircleFubini.isFiniteMeasure_bind_circle (r := ρ) (A.map w)
  have hin : Integrable (fun y => neuPot κ (ψ y)) (bindFc (A.map w) ρ) :=
    Integrable.of_bound ((measurable_neuPot κ).comp hψ).aestronglyMeasurable P
      (hb.mono fun y hy => by rwa [Real.norm_eq_abs])
  obtain ⟨i1, e1⟩ := CircleFubini.integral_bind_circle (A.map w) hin
  have hmap : ∫ z, (∫ y, neuPot κ (ψ y) ∂foldedCircle z ρ) ∂(A.map w) =
      ∫ x, (∫ y, neuPot κ (ψ y) ∂foldedCircle (w x) ρ) ∂A :=
    integral_map hw.aemeasurable hψκ.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine (i1.comp_aemeasurable hw.aemeasurable).congr (Eventually.of_forall fun x => ?_)
    exact (e (w x)).symm
  · calc kernelCov neumannH ((bindFc (A.map w) ρ).map ψ) κ
        = ∫ y, neuPot κ (ψ y) ∂(bindFc (A.map w) ρ) :=
          integral_map hψ.aemeasurable (measurable_neuPot κ).aestronglyMeasurable
      _ = ∫ z, (∫ y, neuPot κ (ψ y) ∂foldedCircle z ρ) ∂(A.map w) := e1
      _ = ∫ x, (∫ y, neuPot κ (ψ y) ∂foldedCircle (w x) ρ) ∂A := hmap
      _ = ∫ x, kernelCov neumannH ((foldedCircle (w x) ρ).map ψ) κ ∂A :=
          integral_congr_ae (Eventually.of_forall fun x => (e (w x)).symm)

/-! ## The bilinear (pair) versions -/

theorem kernelCov2_mixFc_left {w w' : ℂ → ℂ} (hw : Measurable w) (hw' : Measurable w')
    {ψ ψ' : ℂ → ℂ} (hψ : Measurable ψ) (hψ' : Measurable ψ') {ρ ρ' : ℝ}
    {q₁ q₂ : Measure ℂ} [IsFiniteMeasure q₁] [IsFiniteMeasure q₂] {P : ℝ}
    (h₁ : ∀ᵐ y ∂bindFc (A.map w) ρ, |neuPot q₁ (ψ y)| ≤ P)
    (h₂ : ∀ᵐ y ∂bindFc (A.map w) ρ, |neuPot q₂ (ψ y)| ≤ P)
    (h₁' : ∀ᵐ y ∂bindFc (A.map w') ρ', |neuPot q₁ (ψ' y)| ≤ P)
    (h₂' : ∀ᵐ y ∂bindFc (A.map w') ρ', |neuPot q₂ (ψ' y)| ≤ P) :
    kernelCov2 neumannH ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ') (q₁, q₂) =
      ∫ z, kernelCov2 neumannH ((foldedCircle (w z) ρ).map ψ,
        (foldedCircle (w' z) ρ').map ψ') (q₁, q₂) ∂A := by
  obtain ⟨i1, e1⟩ := kernelCov_mixFc_left (A := A) hw hψ h₁
  obtain ⟨i2, e2⟩ := kernelCov_mixFc_left (A := A) hw hψ h₂
  obtain ⟨i3, e3⟩ := kernelCov_mixFc_left (A := A) hw' hψ' h₁'
  obtain ⟨i4, e4⟩ := kernelCov_mixFc_left (A := A) hw' hψ' h₂'
  simp only [kernelCov2]
  set k₁ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle (w z) ρ).map ψ) q₁ with hk₁
  set k₂ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle (w z) ρ).map ψ) q₂ with hk₂
  set k₃ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle (w' z) ρ').map ψ') q₁ with hk₃
  set k₄ : ℂ → ℝ := fun z => kernelCov neumannH ((foldedCircle (w' z) ρ').map ψ') q₂ with hk₄
  have a1 : ∫ z, (k₁ z - k₂ z) ∂A = ∫ z, k₁ z ∂A - ∫ z, k₂ z ∂A := integral_sub i1 i2
  have a2 : ∫ z, (k₁ z - k₂ z - k₃ z) ∂A = ∫ z, (k₁ z - k₂ z) ∂A - ∫ z, k₃ z ∂A :=
    integral_sub (i1.sub i2) i3
  have a3 : ∫ z, (k₁ z - k₂ z - k₃ z + k₄ z) ∂A =
      ∫ z, (k₁ z - k₂ z - k₃ z) ∂A + ∫ z, k₄ z ∂A := integral_add ((i1.sub i2).sub i3) i4
  change _ = ∫ z, (k₁ z - k₂ z - k₃ z + k₄ z) ∂A
  rw [a3, a2, a1, e1, e2, e3, e4]

/-- Integrability of the per-`z` energy in the Fubini step. -/
theorem integrable_kernelCov2_mixFc {w w' : ℂ → ℂ} (hw : Measurable w) (hw' : Measurable w')
    {ψ ψ' : ℂ → ℂ} (hψ : Measurable ψ) (hψ' : Measurable ψ') {ρ ρ' : ℝ}
    {q₁ q₂ : Measure ℂ} [IsFiniteMeasure q₁] [IsFiniteMeasure q₂] {P : ℝ}
    (h₁ : ∀ᵐ y ∂bindFc (A.map w) ρ, |neuPot q₁ (ψ y)| ≤ P)
    (h₂ : ∀ᵐ y ∂bindFc (A.map w) ρ, |neuPot q₂ (ψ y)| ≤ P)
    (h₁' : ∀ᵐ y ∂bindFc (A.map w') ρ', |neuPot q₁ (ψ' y)| ≤ P)
    (h₂' : ∀ᵐ y ∂bindFc (A.map w') ρ', |neuPot q₂ (ψ' y)| ≤ P) :
    Integrable (fun z => kernelCov2 neumannH ((foldedCircle (w z) ρ).map ψ,
      (foldedCircle (w' z) ρ').map ψ') (q₁, q₂)) A := by
  obtain ⟨i1, -⟩ := kernelCov_mixFc_left (A := A) hw hψ h₁
  obtain ⟨i2, -⟩ := kernelCov_mixFc_left (A := A) hw hψ h₂
  obtain ⟨i3, -⟩ := kernelCov_mixFc_left (A := A) hw' hψ' h₁'
  obtain ⟨i4, -⟩ := kernelCov_mixFc_left (A := A) hw' hψ' h₂'
  have h := ((i1.sub i2).sub i3).add i4
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply, Pi.add_apply, kernelCov2]

/-! ## Goodness of a mixture over a centre map -/

/-- A mixture over `A` of good measures `(fc(w z, ρ)).map ψ` is good. -/
theorem goodM_mixFc {w : ℂ → ℂ} (hw : Measurable w) {ψ : ℂ → ℂ} (hψ : Measurable ψ)
    {ρ α C B : ℝ} (hC : 0 ≤ C) (h : ∀ᵐ z ∂A, GoodM ((foldedCircle (w z) ρ).map ψ) α C B) :
    GoodM ((bindFc (A.map w) ρ).map ψ) α C B := by
  have hS : ∀ S : Set ℂ, MeasurableSet S → Measurable fun z : ℂ => ((foldedCircle z ρ).map ψ) S :=
    fun S hS' => by
      have := ProbabilityTheory.Kernel.measurable_coe
        (ProbabilityTheory.Kernel.map (CircleFubini.circleKernel ρ) ψ) hS'
      simpa only [ProbabilityTheory.Kernel.map_apply _ hψ, CircleFubini.circleKernel_apply] using this
  refine ⟨⟨?_⟩, fun y r hr => ?_, ?_⟩
  · rw [map_bindFc_apply hψ ρ MeasurableSet.univ, lintegral_map (hS _ MeasurableSet.univ) hw]
    rw [lintegral_congr_ae (g := fun _ => (1 : ℝ≥0∞))
      (h.mono fun z hz => by simp [hz.prob.measure_univ])]
    simp
  · have hcr : 0 ≤ C * r ^ α := mul_nonneg hC (Real.rpow_nonneg hr.le _)
    refine ENNReal.toReal_le_of_le_ofReal hcr ?_
    rw [map_bindFc_apply hψ ρ measurableSet_closedBall,
      lintegral_map (hS _ measurableSet_closedBall) hw]
    calc ∫⁻ x, ((foldedCircle (w x) ρ).map ψ) (closedBall y r) ∂A
        ≤ ∫⁻ _x, ENNReal.ofReal (C * r ^ α) ∂A := by
          refine lintegral_mono_ae (h.mono fun x hx => ?_)
          have := hx.prob
          exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hcr).2 (hx.frost y r hr)
      _ = ENNReal.ofReal (C * r ^ α) := by simp
  · rw [map_bindFc_apply hψ ρ (measurableSet_closedBall_inter_Hbar B).compl,
      lintegral_map (hS _ (measurableSet_closedBall_inter_Hbar B).compl) hw]
    rw [lintegral_congr_ae (h.mono fun x hx => hx.supp)]
    simp

/-! ## The general mixture bound -/

/-- **UNIF-RC3-MIX (integral form).** Two mixtures over the same base measure `A`, of pushed
circles with centre maps `w`, `w'` and push maps `ψ`, `ψ'`: if for `A`-a.e. `z` the energy of the
pair `(fc(w z, ρ)).map ψ − (fc(w' z, ρ')).map ψ'` is at most `K z`, then the energy of the two
mixtures is at most `(∫ √K dA)²`. -/
theorem energy_mixFc_le {w w' : ℂ → ℂ} (hw : Measurable w) (hw' : Measurable w')
    {ψ ψ' : ℂ → ℂ} (hψ : Measurable ψ) (hψ' : Measurable ψ') {ρ ρ' α C B : ℝ} (hα : 0 < α)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hL : ∀ᵐ z ∂A, GoodM ((foldedCircle (w z) ρ).map ψ) α C B ∧
      GoodM ((foldedCircle (w' z) ρ').map ψ') α C B)
    {K : ℂ → ℝ} (hK : ∀ᵐ z ∂A, kernelCov2 neumannH
      (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ'))
      (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ')) ≤ K z)
    (hKi : Integrable (fun z => Real.sqrt (K z)) A) :
    kernelCov2 neumannH ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ')
      ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ') ≤
      (∫ z, Real.sqrt (K z) ∂A) ^ 2 := by
  set L : ℂ → Measure ℂ := fun z => (foldedCircle (w z) ρ).map ψ with hLdef
  set L' : ℂ → Measure ℂ := fun z => (foldedCircle (w' z) ρ').map ψ' with hL'def
  set M : Measure ℂ := (bindFc (A.map w) ρ).map ψ with hMdef
  set M' : Measure ℂ := (bindFc (A.map w') ρ').map ψ' with hM'def
  have hM : GoodM M α C B := goodM_mixFc hw hψ hC (hL.mono fun z hz => hz.1)
  have hM' : GoodM M' α C B := goodM_mixFc hw' hψ' hC (hL.mono fun z hz => hz.2)
  have hadmM : IsAdmissibleH M := hM.admissible hα
  have hadmM' : IsAdmissibleH M' := hM'.admissible hα
  have huM : M univ = M' univ := hM.univ_eq hM'
  have hE0 : 0 ≤ kernelCov2 neumannH (M, M') (M, M') := kernelCov2_self_nonneg hadmM hadmM' huM
  -- the Fubini step, with integrability
  have fub : ∀ q₁ q₂ : Measure ℂ, GoodM q₁ α C B → GoodM q₂ α C B →
      Integrable (fun z => kernelCov2 neumannH (L z, L' z) (q₁, q₂)) A ∧
      kernelCov2 neumannH (M, M') (q₁, q₂) = ∫ z, kernelCov2 neumannH (L z, L' z) (q₁, q₂) ∂A :=
    fun q₁ q₂ h₁ h₂ => by
      have hq₁ := h₁.prob
      have hq₂ := h₂.prob
      exact ⟨integrable_kernelCov2_mixFc hw hw' hψ hψ'
          (ae_abs_neuPot_le h₁ hα hC hB hψ hM.supp) (ae_abs_neuPot_le h₂ hα hC hB hψ hM.supp)
          (ae_abs_neuPot_le h₁ hα hC hB hψ' hM'.supp) (ae_abs_neuPot_le h₂ hα hC hB hψ' hM'.supp),
        kernelCov2_mixFc_left hw hw' hψ hψ'
          (ae_abs_neuPot_le h₁ hα hC hB hψ hM.supp) (ae_abs_neuPot_le h₂ hα hC hB hψ hM.supp)
          (ae_abs_neuPot_le h₁ hα hC hB hψ' hM'.supp) (ae_abs_neuPot_le h₂ hα hC hB hψ' hM'.supp)⟩
  set E := kernelCov2 neumannH (M, M') (M, M') with hEdef
  -- Cauchy–Schwarz in the freeVec Hilbert space
  have inner : ∀ᵐ z ∂A, |kernelCov2 neumannH (M, M') (L z, L' z)| ≤ Real.sqrt (K z) * Real.sqrt E := by
    filter_upwards [hL, hK] with z hz hEz
    have h1 : IsAdmissibleH (L z) := hz.1.admissible hα
    have h2 : IsAdmissibleH (L' z) := hz.2.admissible hα
    have h3 : (L z) univ = (L' z) univ := hz.1.univ_eq hz.2
    rw [kernelCov2_eq_inner_freeVec hadmM hadmM' h1 h2 huM h3]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hvb : ‖freeVec ⟨L z, h1⟩ - freeVec ⟨L' z, h2⟩‖ ≤ Real.sqrt (K z) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [← kernelCov2_self_eq_norm_sq h1 h2 h3]
      exact hEz
    have hva : ‖freeVec ⟨M, hadmM⟩ - freeVec ⟨M', hadmM'⟩‖ = Real.sqrt E := by
      rw [hEdef, kernelCov2_self_eq_norm_sq hadmM hadmM' huM, Real.sqrt_sq (norm_nonneg _)]
    rw [hva]
    calc √E * ‖freeVec ⟨L z, h1⟩ - freeVec ⟨L' z, h2⟩‖ ≤ √E * √(K z) :=
          mul_le_mul_of_nonneg_left hvb (Real.sqrt_nonneg _)
      _ = √(K z) * √E := mul_comm _ _
  have hmain : ∀ᵐ z ∂A, kernelCov2 neumannH (L z, L' z) (M, M') ≤ Real.sqrt (K z) * Real.sqrt E := by
    filter_upwards [inner, hL] with z hz hzL
    rw [kernelCov2_comm (hzL.1.admissible hα) (hzL.2.admissible hα) hadmM hadmM']
    simpa only [hLdef, hL'def] using (abs_le.1 hz).2
  have hint : Integrable (fun z => Real.sqrt (K z) * Real.sqrt E) A := hKi.mul_const _
  have hstep : E ≤ (∫ z, Real.sqrt (K z) ∂A) * Real.sqrt E := by
    rw [hEdef]
    calc kernelCov2 neumannH (M, M') (M, M')
        = ∫ z, kernelCov2 neumannH (L z, L' z) (M, M') ∂A := (fub M M' hM hM').2
      _ ≤ ∫ z, Real.sqrt (K z) * Real.sqrt E ∂A :=
          integral_mono_ae (fub M M' hM hM').1 hint hmain
      _ = (∫ z, Real.sqrt (K z) ∂A) * Real.sqrt E := integral_mul_const _ _
  rcases hE0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have hsq : Real.sqrt E * Real.sqrt E ≤ (∫ z, Real.sqrt (K z) ∂A) * Real.sqrt E := by
      rw [← sq, Real.sq_sqrt hE0]; exact hstep
    have h1 : Real.sqrt E ≤ ∫ z, Real.sqrt (K z) ∂A :=
      le_of_mul_le_mul_right hsq (Real.sqrt_pos.2 hpos)
    have h2 : 0 ≤ ∫ z, Real.sqrt (K z) ∂A := integral_nonneg fun z => Real.sqrt_nonneg _
    calc E = Real.sqrt E * Real.sqrt E := by rw [← sq, Real.sq_sqrt hE0]
      _ ≤ (∫ z, Real.sqrt (K z) ∂A) * (∫ z, Real.sqrt (K z) ∂A) :=
          mul_le_mul h1 h1 (Real.sqrt_nonneg _) h2
      _ = (∫ z, Real.sqrt (K z) ∂A) ^ 2 := (sq _).symm

/-- **UNIF-RC3-MIX, sup form with two maps and two centre maps.** -/
theorem abs_kernelCov2_mix_le_two {w w' : ℂ → ℂ} (hw : Measurable w) (hw' : Measurable w')
    {ψ ψ' : ℂ → ℂ} (hψ : Measurable ψ) (hψ' : Measurable ψ') {ρ ρ' α C B K : ℝ} (hα : 0 < α)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hK0 : 0 ≤ K)
    (hL : ∀ᵐ z ∂A, GoodM ((foldedCircle (w z) ρ).map ψ) α C B ∧
      GoodM ((foldedCircle (w' z) ρ').map ψ') α C B)
    (hE : ∀ᵐ z ∂A, kernelCov2 neumannH
      (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ'))
      (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ')) ≤ K) :
    |kernelCov2 neumannH ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ')
      ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ')| ≤ K := by
  have hKi : Integrable (fun _ : ℂ => Real.sqrt K) A := integrable_const _
  have h := energy_mixFc_le hw hw' hψ hψ' hα hC hB hL hE hKi
  have hnn : 0 ≤ kernelCov2 neumannH ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ')
      ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ') :=
    kernelCov2_self_nonneg ((goodM_mixFc hw hψ hC (hL.mono fun z hz => hz.1)).admissible hα)
      ((goodM_mixFc hw' hψ' hC (hL.mono fun z hz => hz.2)).admissible hα)
      ((goodM_mixFc hw hψ hC (hL.mono fun z hz => hz.1)).univ_eq
        (goodM_mixFc hw' hψ' hC (hL.mono fun z hz => hz.2)))
  rw [abs_of_nonneg hnn]
  refine h.trans ?_
  have : ∫ _z : ℂ, Real.sqrt K ∂A = Real.sqrt K := by simp
  rw [this, Real.sq_sqrt hK0]

end RegUnif
end QuantumZipper
