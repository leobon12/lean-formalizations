import InteractingSLE.GFF.LocalSets.Projection
import QuantumZipper.Proofs.GFF.K3.BubbleGates

/-!
# Green covariances on subdomains of `ℍ`: scaling and component decomposition

Infrastructure for Propositions 3.8–3.9 (specification §3.2, pp. 58–59, transcription
`source/spec/p049-096.md#prop-3.8`, `#prop-3.9`), packet PROVE-LS-C.

For an open `V ⊆ ℍ` and a test function `φ` on `ℍ`, `σ²_V(φ) = zeroGFFTestCov V φ φ` is the
variance of `(h, φ)` for the zero-boundary GFF on `V` (extended by zero).

* `zeroGFFTestCov_smul_self` : `σ²_V(c φ) = c² σ²_V(φ)`;
* `zeroGFFTestCov_eq_of_isClopen` : if `C ⊆ V` is open and relatively closed in `V` (a union of
  components of `V`) and `supp φ ⊆ C`, then `σ²_V(φ) = σ²_C(φ)`: the zero-boundary GFF on `V`
  restricted to `C` is the zero-boundary GFF on `C` ("Decompose the remaining GFF as the
  independent sum of its zero-boundary fields on `C` and on `(D ∖ A₁) ∖ C`", p. 59).

Proof of the decomposition (own argument, by the variational formula
`σ²_V(φ) = sup_f (∫ φ f)² / E(f)`, `ofReal_zeroGFFTestCov_eq_iSup`): for `f ∈ C_c^∞(V)` the cut
`1_C f` is again smooth, supported in `C`, has the same pairing with `φ` and no more energy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric

/-! ### Scaling -/

theorem covVec_smul {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (c : ℝ)
    (φ : TestOn upperHalfPlaneOpens) : covVec V ⇑(c • φ) = c • covVec V φ := by
  have := covVec_lin hV hVH (toTestFunH φ) (toTestFunH 0) (toTestFunH (c • φ)) c
    (fun z => by simp [toTestFunH])
  simp only [toTestFunH] at this
  rw [this, covVec_zero V hV hVH, add_zero]

/-- `σ²_V(c φ) = c² σ²_V(φ)`. -/
theorem zeroGFFTestCov_smul_self {V : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H) (c : ℝ)
    (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov V ⇑(c • φ) ⇑(c • φ) = c ^ 2 * zeroGFFTestCov V φ φ := by
  rw [zeroGFFTestCov_eq_inner_covVec hV hVH, zeroGFFTestCov_eq_inner_covVec hV hVH,
    covVec_smul hV hVH, real_inner_smul_left, real_inner_smul_right]
  ring

/-! ### Cutting a test function to a relatively clopen piece -/

section Cut

variable {V C : Set ℂ} {f : ℂ → ℝ}

/-- Near every point, the cut `1_C f` agrees with `f` (points of `C`) or with `0`. -/
lemma indicator_eventuallyEq (hC : IsOpen C) (hVC : IsOpen (V \ C))
    (hf : tsupport f ⊆ V) (z : ℂ) :
    (z ∈ C → C.indicator f =ᶠ[𝓝 z] f) ∧ (z ∉ C → C.indicator f =ᶠ[𝓝 z] 0) := by
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · filter_upwards [hC.mem_nhds hz] with w hw
    exact indicator_of_mem hw f
  · by_cases hzV : z ∈ V
    · filter_upwards [hVC.mem_nhds ⟨hzV, hz⟩] with w hw
      exact indicator_of_notMem hw.2 f
    · have hz' : z ∉ tsupport f := fun h => hzV (hf h)
      have h0 := (notMem_tsupport_iff_eventuallyEq).1 hz'
      filter_upwards [h0] with w hw
      by_cases hwC : w ∈ C
      · rw [indicator_of_mem hwC, hw]
      · rw [indicator_of_notMem hwC]; rfl

lemma contDiff_indicator (hC : IsOpen C) (hVC : IsOpen (V \ C)) (hf : f ∈ zeroSpace V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (C.indicator f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ C
  · exact (hf.1.contDiffAt).congr_of_eventuallyEq
      ((indicator_eventuallyEq hC hVC hf.2.2 z).1 hz)
  · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      ((indicator_eventuallyEq hC hVC hf.2.2 z).2 hz)

lemma tsupport_indicator_subset (hC : IsOpen C) (hVC : IsOpen (V \ C))
    (hf : tsupport f ⊆ V) : tsupport (C.indicator f) ⊆ C := by
  intro z hz
  by_contra hzC
  exact ((notMem_tsupport_iff_eventuallyEq).2 ((indicator_eventuallyEq hC hVC hf z).2 hzC)) hz

lemma support_indicator_subset' : Function.support (C.indicator f) ⊆ Function.support f := by
  intro z hz
  by_cases hzC : z ∈ C
  · rwa [Function.mem_support, indicator_of_mem hzC] at hz
  · rw [Function.mem_support, indicator_of_notMem hzC] at hz
    exact absurd rfl hz

lemma indicator_mem_zeroSpace (hC : IsOpen C) (hVC : IsOpen (V \ C)) (hf : f ∈ zeroSpace V) :
    C.indicator f ∈ zeroSpace C :=
  ⟨contDiff_indicator hC hVC hf, hf.2.1.mono support_indicator_subset',
    tsupport_indicator_subset hC hVC hf.2.2⟩

lemma norm_fderiv_indicator_le (hC : IsOpen C) (hVC : IsOpen (V \ C)) (hf : tsupport f ⊆ V)
    (z : ℂ) : ‖fderiv ℝ (C.indicator f) z‖ ≤ ‖fderiv ℝ f z‖ := by
  by_cases hz : z ∈ C
  · rw [((indicator_eventuallyEq hC hVC hf z).1 hz).fderiv_eq]
  · rw [((indicator_eventuallyEq hC hVC hf z).2 hz).fderiv_eq]
    have : fderiv ℝ (0 : ℂ → ℝ) z = 0 := fderiv_const_apply 0
    rw [this, norm_zero]
    exact norm_nonneg _

lemma energyC_indicator_le (hC : IsOpen C) (hVC : IsOpen (V \ C)) (hf : f ∈ zeroSpace V) :
    energyC (C.indicator f) ≤ energyC f := by
  unfold energyC
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcont : ∀ g : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
      Integrable (fun z => ‖fderiv ℝ g z‖ ^ 2) := fun g hg hgc =>
    ((hg.continuous_fderiv (by simp)).norm.pow 2).integrable_of_hasCompactSupport
      ((hgc.fderiv (𝕜 := ℝ)).norm.mono fun z hz => by
        simp only [Function.mem_support, ne_eq] at hz ⊢
        intro h0
        exact hz (by simp only [Pi.pow_apply, h0]; ring))
  refine integral_mono (hcont _ (contDiff_indicator hC hVC hf)
    (hf.2.1.mono support_indicator_subset')) (hcont f hf.1 hf.2.1) fun z => ?_
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_indicator_le hC hVC hf.2.2 z) 2

lemma integral_mul_indicator {φ : ℂ → ℝ} (hφ : tsupport φ ⊆ C) :
    ∫ z, φ z * C.indicator f z = ∫ z, φ z * f z := by
  congr 1
  funext z
  by_cases hz : z ∈ C
  · rw [indicator_of_mem hz]
  · rw [image_eq_zero_of_notMem_tsupport fun h => hz (hφ h), zero_mul, zero_mul]

end Cut

/-- **Component decomposition of the Green covariance.** If `C ⊆ V ⊆ ℍ` are open, `V ∖ C` is open
(so `C` is a union of components of `V`) and `supp φ ⊆ C`, then `σ²_V(φ) = σ²_C(φ)`. -/
theorem zeroGFFTestCov_eq_of_isClopen {V C : Set ℂ} (hV : IsOpen V) (hVH : V ⊆ H)
    (hC : IsOpen C) (hCV : C ⊆ V) (hVC : IsOpen (V \ C)) (φ : TestOn upperHalfPlaneOpens)
    (hφ : tsupport φ ⊆ C) : zeroGFFTestCov V φ φ = zeroGFFTestCov C φ φ := by
  have hCH : C ⊆ H := hCV.trans hVH
  have hle : zeroGFFTestCov C φ φ ≤ zeroGFFTestCov V φ φ := by
    rw [← ENNReal.ofReal_le_ofReal_iff (zeroGFFTestCov_self_nonneg hV hVH φ),
      ofReal_zeroGFFTestCov_eq_iSup hV hVH, ofReal_zeroGFFTestCov_eq_iSup hC hCH]
    refine iSup₂_le fun f hf => ?_
    exact le_iSup₂ (f := fun g (_ : g ∈ {g | g ∈ zeroSpace V ∧ 0 < energyC g}) =>
      ENNReal.ofReal ((∫ z, φ z * g z) ^ 2 / energyC g)) f
      ⟨⟨hf.1.1, hf.1.2.1, hf.1.2.2.trans hCV⟩, hf.2⟩
  refine le_antisymm ?_ hle
  rw [← ENNReal.ofReal_le_ofReal_iff (zeroGFFTestCov_self_nonneg hC hCH φ),
    ofReal_zeroGFFTestCov_eq_iSup hV hVH, ofReal_zeroGFFTestCov_eq_iSup hC hCH]
  refine iSup₂_le fun f hf => ?_
  have hfC := indicator_mem_zeroSpace hC hVC hf.1
  have hint := integral_mul_indicator (f := f) hφ
  by_cases hE : 0 < energyC (C.indicator f)
  · refine le_trans ?_ (le_iSup₂ (f := fun g (_ : g ∈ {g | g ∈ zeroSpace C ∧ 0 < energyC g}) =>
      ENNReal.ofReal ((∫ z, φ z * g z) ^ 2 / energyC g)) (C.indicator f) ⟨hfC, hE⟩)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hint]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hE (energyC_indicator_le hC hVC hf.1)
  · have hE0 : energyC (C.indicator f) = 0 :=
      le_antisymm (not_lt.1 hE) (by unfold energyC; positivity)
    have hzero : ∀ z ∈ C, C.indicator f z = 0 := by
      refine zeroSpace_eq_zero_of_energy_zero hC hfC.1 hfC.2.1 hfC.2.2 ?_
      rw [energy_eq_of_tsupport_subset hfC.2.2]
      exact hE0
    have h0 : ∫ z, φ z * f z = 0 := by
      rw [← hint]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ C
      · simp [hzero z hz]
      · simp [indicator_of_notMem hz]
    rw [h0]
    simp

end LocalSets
end InteractingSLE
