import HigherDimLFPPAS.Gauss.Process
import HigherDimLFPPAS.Gauss.Increment
import LQGMetric.Gaussian.SupTailField

/-!
# Differences of the convolution field as Gaussian processes (packet F2b)

`H(t, x) := h ∗ K_{e^{-t}}(x)` (`fieldF2b`). For maps `a b : T → ℝ × ℝ^d`, the process
`p ↦ H(a p) - H(b p)` is a centred Gaussian process (`isGaussianProcess_fieldDiff_F2b`,
`integral_fieldDiff_F2b`); almost surely `H` is jointly continuous on `ℝ × ℝ^d`
(`ae_continuous_fieldF2b`). The sharp one-variable Gaussian tail
`P(|H(q)| ≥ A) ≤ 2 exp(-A²/(2V))` for `Var H(q) ≤ V` is `tail_abs_fieldF2b_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

namespace HigherDimLFPPAS.Gauss

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- `H(t, x) = h ∗ K_{e^{-t}}(x)`, indexed by logarithmic scale and position. -/
def fieldF2b (κ : Rd d → ℝ) (h : Ω → DistRd d) (q : ℝ × Rd d) (ω : Ω) : ℝ :=
  convMollify κ (Real.exp (-q.1)) (h ω) q.2

lemma isGaussianProcess_fieldF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) : IsGaussianProcess (fieldF2b κ h) P :=
  convMollify_isGaussianProcess_seed hd hκ hh

lemma integral_fieldF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) (q : ℝ × Rd d) : ∫ ω, fieldF2b κ h q ω ∂P = 0 :=
  integral_convMollify_F2b hd hκ hh (Real.exp_pos _) q.2

/-- Differences `p ↦ H(a p) - H(b p)` form a Gaussian process. -/
theorem isGaussianProcess_fieldDiff_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) {T : Type*} (a b : T → ℝ × Rd d) :
    IsGaussianProcess (fun p ω => fieldF2b κ h (a p) ω - fieldF2b κ h (b p) ω) P := by
  classical
  refine (isGaussianProcess_fieldF2b hd hκ hh).of_isGaussianProcess fun p => ⟨{a p, b p},
    { toFun := fun x => x ⟨a p, by simp⟩ - x ⟨b p, by simp⟩
      map_add' := fun x y => by simp only [Pi.add_apply]; ring
      map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
      cont := by fun_prop }, fun ω => ?_⟩
  simp only [ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Finset.restrict]

lemma integral_fieldDiff_F2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) (q q' : ℝ × Rd d) :
    ∫ ω, (fieldF2b κ h q ω - fieldF2b κ h q' ω) ∂P = 0 := by
  have hG := isGaussianProcess_fieldF2b hd hκ hh
  have i1 : Integrable (fun ω => fieldF2b κ h q ω) P := (hG.hasGaussianLaw_eval q).integrable
  have i2 : Integrable (fun ω => fieldF2b κ h q' ω) P := (hG.hasGaussianLaw_eval q').integrable
  rw [integral_sub i1 i2, integral_fieldF2b hd hκ hh, integral_fieldF2b hd hκ hh, sub_zero]

/-- Almost surely, `(t, x) ↦ h ∗ K_{e^{-t}}(x)` is continuous on `ℝ × ℝ^d`. -/
theorem ae_continuous_fieldF2b (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, Continuous fun q : ℝ × Rd d => fieldF2b κ h q ω := by
  filter_upwards [Signed.l2b_ae_convMollify_continuousOn_seed d hd κ hκ P h hh] with ω hω
  have hm : Continuous fun q : ℝ × Rd d => (Real.exp (-q.1), q.2) :=
    (Real.continuous_exp.comp continuous_fst.neg).prodMk continuous_snd
  have hc := hω.comp_continuous hm fun q => ⟨Real.exp_pos _, mem_univ _⟩
  refine hc.congr fun q => ?_
  simp only [Function.comp_apply, fieldF2b]

/-- **Sharp Gaussian tail** of a value of the convolution field. -/
theorem tail_abs_fieldF2b_le (hd : 2 ≤ d) (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ)
    (hh : IsNormalizedLGF h P) (q : ℝ × Rd d) {V A : ℝ} (hV0 : 0 ≤ V)
    (hV : Var[fieldF2b κ h q; P] ≤ V) (hA : 0 ≤ A) :
    P.real {ω | A ≤ |fieldF2b κ h q ω|} ≤ 2 * Real.exp (-A ^ 2 / (2 * V)) := by
  set X : Unit → Ω → ℝ := fun _ ω => fieldF2b κ h q ω
  have hG : IsGaussianProcess X P :=
    (isGaussianProcess_fieldF2b hd hκ hh).comp_right (fun _ : Unit => q)
  have h0q := integral_fieldF2b hd hκ hh q
  have h0 : ∀ t : Unit, ∫ ω, X t ω ∂P = 0 := fun _ => h0q
  have hint : ∀ s : ℝ, Integrable (fun ω => ⨆ _ : Unit, s * X () ω) P := by
    intro s
    simp only [ciSup_const]
    exact ((hG.hasGaussianLaw_eval ()).integrable).const_mul s
  have hvar : ∀ t : Unit, Var[X t; P] ≤ Real.sqrt V ^ 2 := by
    intro _
    rw [Real.sq_sqrt hV0]
    exact hV
  have ht := LQGMetric.SupTail.tail_iSup_abs_le hG h0 (fun ω => continuous_const)
    (by simpa only [one_mul] using hint 1)
    (by simpa only [neg_one_mul] using hint (-1)) (M := 0)
    (by simp only [X, ciSup_const, h0q, le_refl])
    (by simp only [X, ciSup_const, integral_neg, h0q, neg_zero, le_refl]) hvar hA
  simpa only [X, ciSup_const, zero_add, Real.sq_sqrt hV0] using ht

end HigherDimLFPPAS.Gauss
