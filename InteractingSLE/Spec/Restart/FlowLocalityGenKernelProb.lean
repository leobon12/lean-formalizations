/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCRealCompletionTilt
import InteractingSLE.Spec.Sec7.LocalExtCKernel

/-!
# Flow locality with a general agreement set: probabilistic tools for the pocket kernel

Packet PROVE-G7A-LOC. Three general facts used by the per-stop identification with retained pockets:

* `ae_condExp_pos_of_pos`: the conditional expectation of a strictly positive integrable function is strictly
  positive almost surely;
* **`ae_condExp_withDensity_eq_of_tilt`**: Bayes' formula when only the tilt identity
  `E[e^{−Λ} X | m] = E[e^{−Λ} | m] · c` is known (the conditional mean of `e^{−Λ}` itself is not computed — with
  retained pockets it involves the unknown in-pocket means, PROVE-G3RESTART §6.4);
* **`tendsto_eLpNorm_one_of_sq_le`**: almost sure convergence and a uniform `L²` bound give `L¹` convergence
  (uniform integrability, `MeasureTheory.unifIntegrable_of`, and Vitali,
  `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.FlowLocalityGen

section Bayes

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The conditional expectation of a strictly positive integrable function is strictly positive almost surely. -/
theorem ae_condExp_pos_of_pos [IsFiniteMeasure P] (hm : m ≤ mΩ) {Z : Ω → ℝ} (hZi : Integrable Z P)
    (hZpos : ∀ ω, 0 < Z ω) : ∀ᵐ ω ∂P, 0 < P[Z | m] ω := by
  set A : Set Ω := {ω | P[Z | m] ω ≤ 0} with hA
  have hAm : MeasurableSet[m] A := measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
  have hAm' : MeasurableSet A := hm _ hAm
  have h1 : ∫ ω in A, P[Z | m] ω ∂P = ∫ ω in A, Z ω ∂P := setIntegral_condExp hm hZi hAm
  have h2 : ∫ ω in A, P[Z | m] ω ∂P ≤ 0 := setIntegral_nonpos hAm' fun ω hω => hω
  have h3 : 0 ≤ ∫ ω in A, Z ω ∂P := setIntegral_nonneg hAm' fun ω _ => (hZpos ω).le
  have h4 : ∫ ω in A, Z ω ∂P = 0 := le_antisymm (h1 ▸ h2) h3
  have h5 := (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω => (hZpos ω).le) hZi.integrableOn).1 h4
  have h6 : P A = 0 := by
    have h7 : ∀ᵐ ω ∂(P.restrict A), False := h5.mono fun ω hω => (hZpos ω).ne' hω
    have h8 := (ae_iff.1 h7)
    simp only [not_false_eq_true, Set.ofPred_true, Measure.restrict_apply_univ] at h8
    exact h8
  refine (measure_eq_zero_iff_ae_notMem.1 h6).mono fun ω hω => ?_
  simpa only [hA, Set.mem_ofPred_eq, not_le] using hω

/-- **Bayes' formula from the tilt identity.** Under `Q = k e^{−Λ} · P`, if almost surely on `D`
`E[e^{−Λ} X | m] = E[e^{−Λ} | m] · c` (complex conditional expectations), then `E_Q[X | m] = c` `Q`-almost surely on
`D`, for every bounded `X`. -/
theorem ae_condExp_withDensity_eq_of_tilt [IsProbabilityMeasure P] (hm : m ≤ mΩ) {Λ : Ω → ℝ}
    (hΛm : Measurable Λ) (hint : Integrable (fun ω => Real.exp (-Λ ω)) P) {k : ℝ} (hk : 0 < k)
    {X : Ω → ℂ} (hXm : AEStronglyMeasurable X P) (hXb : ∀ ω, ‖X ω‖ ≤ 1) {D : Set Ω} {c : Ω → ℂ}
    (htilt : ∀ᵐ ω ∂P, ω ∈ D → P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * X ω' | m] ω =
      P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) | m] ω * c ω) :
    ∀ᵐ ω ∂(P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω))), ω ∈ D →
      (P.withDensity fun ω => ENNReal.ofReal (k * Real.exp (-Λ ω)))[X | m] ω = c ω := by
  set Z : Ω → ℝ := fun ω => k * Real.exp (-Λ ω) with hZdef
  set Q := P.withDensity fun ω => ENNReal.ofReal (Z ω) with hQ
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  have hZm : Measurable Z := measurable_const.mul (Real.measurable_exp.comp hΛm.neg)
  have hZpos : ∀ ω, 0 < Z ω := fun ω => mul_pos hk (Real.exp_pos _)
  have hZi : Integrable Z P := hint.const_mul k
  have hpos := ae_condExp_pos_of_pos hm hZi hZpos
  set N : Ω → ℝ := fun ω => if 0 < P[Z | m] ω then P[Z | m] ω else 1 with hNdef
  have hNm : StronglyMeasurable[m] N := by
    have hs : MeasurableSet[m] {ω | 0 < P[Z | m] ω} :=
      measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable
    exact StronglyMeasurable.ite hs stronglyMeasurable_condExp stronglyMeasurable_const
  have hNpos : ∀ ω, 0 < N ω := fun ω => by
    simp only [hNdef]
    split_ifs with h
    · exact h
    · exact one_pos
  have hZN : P[Z | m] =ᵐ[P] N := hpos.mono fun ω hω => by simp only [hNdef, hω, ↓reduceIte]
  have hB := LocalExt.condExp_withDensity_ae_eq (P := P) (m := m) hm hZm (fun ω => (hZpos ω).le) hZi hNm hNpos
    hZN hXm hXb
  -- the numerator and the denominator in terms of `e^{−Λ}`
  have hsm : P[fun ω => Z ω • X ω | m] =ᵐ[P]
      fun ω => (k : ℂ) • P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * X ω' | m] ω := by
    have e := condExp_smul (μ := P) (m := m) (k : ℂ) (fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * X ω')
    have hf : (fun ω => Z ω • X ω) = (k : ℂ) • fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) * X ω' := by
      funext ω
      simp only [hZdef, Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [hf]
    filter_upwards [e] with ω hω
    rw [hω, Pi.smul_apply]
  have hden : P[Z | m] =ᵐ[P] fun ω => k * P[fun ω' => Real.exp (-Λ ω') | m] ω := by
    have e := condExp_smul (μ := P) (m := m) k (fun ω => Real.exp (-Λ ω))
    filter_upwards [e] with ω h1
    have hZf : Z = k • fun ω => Real.exp (-Λ ω) := rfl
    rw [hZf, h1, Pi.smul_apply, smul_eq_mul]
  have hcomm := Complex.ofRealCLM.comp_condExp_comm (m := m) hint
  filter_upwards [hB, hQP.ae_le hsm, hQP.ae_le htilt, hQP.ae_le hZN, hQP.ae_le hden, hQP.ae_le hcomm,
    hQP.ae_le hpos] with ω e1 e2 e3 e4 e5 e6 e7 hD
  rw [e1, e2, e3 hD]
  have h6 : P[fun ω' => ((Real.exp (-Λ ω') : ℝ) : ℂ) | m] ω =
      ((P[fun ω' => Real.exp (-Λ ω') | m] ω : ℝ) : ℂ) := by
    have := e6
    simp only [Function.comp_apply, Complex.ofRealCLM_apply] at this
    exact this.symm
  rw [h6]
  have hN : N ω = k * P[fun ω' => Real.exp (-Λ ω') | m] ω := by rw [← e4]; exact e5
  rw [hN]
  have hkE : 0 < k * P[fun ω' => Real.exp (-Λ ω') | m] ω := by rw [← hN]; exact hNpos ω
  have hE0 : (P[fun ω' => Real.exp (-Λ ω') | m] ω : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (pos_of_mul_pos_right hkE hk.le).ne'
  have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk.ne'
  simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
  field_simp

end Bayes

section Vitali

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **`L¹` convergence from almost sure convergence and a uniform `L²` bound** (uniform integrability and
Vitali). -/
theorem tendsto_eLpNorm_one_of_sq_le [IsFiniteMeasure P] {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Integrable g P)
    (hfg : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hf2 : ∀ n, Integrable (fun ω => f n ω ^ 2) P) {B : ℝ} (hB : ∀ n, ∫ ω, f n ω ^ 2 ∂P ≤ B) :
    Tendsto (fun n => eLpNorm (fun ω => f n ω - g ω) 1 P) atTop (𝓝 0) := by
  have hui : UnifIntegrable f 1 P := by
    refine unifIntegrable_of le_rfl ENNReal.one_ne_top (fun n => (hf n).aestronglyMeasurable) fun ε hε => ?_
    -- a threshold `C` with `B / C ≤ ε`
    obtain ⟨C, hC0, hCε⟩ : ∃ C : ℝ≥0, 0 < C ∧ ENNReal.ofReal (B / C) ≤ ε := by
      by_cases htop : ε = ⊤
      · exact ⟨1, one_pos, htop ▸ le_top⟩
      have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
      set c : ℝ := |B| / ε.toReal + 1 with hc
      have hc0 : 0 < c := by positivity
      refine ⟨c.toNNReal, Real.toNNReal_pos.2 hc0, ?_⟩
      rw [Real.coe_toNNReal _ hc0.le]
      calc ENNReal.ofReal (B / c) ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal (by
            rw [div_le_iff₀ hc0]
            have h2 : |B| = ε.toReal * (|B| / ε.toReal) := by field_simp
            nlinarith [le_abs_self B, abs_nonneg B])
        _ = ε := ENNReal.ofReal_toReal htop
    refine ⟨C, fun n => ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm]
    have hpt : ∀ ω, ‖({x | C ≤ ‖f n x‖₊}.indicator (f n)) ω‖ₑ ≤ ENNReal.ofReal (f n ω ^ 2 / C) := by
      intro ω
      by_cases hω : C ≤ ‖f n ω‖₊
      · rw [indicator_of_mem (show ω ∈ {x | C ≤ ‖f n x‖₊} from hω), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        have hC' : (C : ℝ) ≤ ‖f n ω‖ := by exact_mod_cast hω
        have hCp : (0 : ℝ) < C := NNReal.coe_pos.2 hC0
        rw [le_div_iff₀ hCp, Real.norm_eq_abs] at *
        rw [← sq_abs]
        nlinarith [abs_nonneg (f n ω)]
      · rw [indicator_of_notMem (show ω ∉ {x | C ≤ ‖f n x‖₊} from hω), enorm_zero]
        exact zero_le
    calc ∫⁻ ω, ‖({x | C ≤ ‖f n x‖₊}.indicator (f n)) ω‖ₑ ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (f n ω ^ 2 / C) ∂P := lintegral_mono hpt
      _ = ENNReal.ofReal (∫ ω, f n ω ^ 2 / C ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal ((hf2 n).div_const _)
          (ae_of_all _ fun ω => div_nonneg (sq_nonneg _) C.coe_nonneg)).symm
      _ ≤ ENNReal.ofReal (B / C) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_div]
        exact div_le_div_of_nonneg_right (hB n) C.coe_nonneg
      _ ≤ ε := hCε
  have h := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top (fun n => (hf n).aestronglyMeasurable)
    (memLp_one_iff_integrable.2 hg) hui hfg
  exact h

end Vitali

end InteractingSLE.Restart.FlowLocalityGen
