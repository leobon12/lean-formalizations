import QuantumZipper.Proofs.Thm18.G3Za6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (b), layer 2: the local conformal coupling with far gauge constants

`exists_pullCouplingHarmFar` / `exists_pullSetupFar`: the couplings of
`G3Cv.exists_pullCouplingHarm` / `G3Cv.exists_pullSetup` (proofs repeated verbatim, since the
coupling is existential), with one more conclusion: for a local `μ` and an admissible `S` of the
same mass carried away from `Φ(closedBall b ρ)` and its reflection,
`W(Φ_*μ) − W(S) = X'(μ) − X'(bal μ) + D` a.s. with `D` measurable for `σ(Ξ)`
(`G3Za.ae_realWP_far`). Sources as in G3CvAsm.lean.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Za

open G3Cv K3 GFFExist LQGDimension.ExistAsm

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

theorem exists_pullCouplingHarmFar (hD : PullData Φ b r₀ ρ r₁ m M) (hr₁0 : 0 < r₁) :
    ∃ (W X' : (ℕ → ℝ) → FieldSample) (Ξ : (ℕ → ℝ) → (PXiIdx Φ b ρ r₁ → ℝ))
      (g : (ℕ → ℝ) → ℂ → ℝ),
      IsFreeGFFModConstH W stdP ∧ IsFreeGFFModConstH X' stdP ∧ Measurable Ξ ∧
      Indep (MeasurableSpace.comap Ξ inferInstance) (freeIncrSigma X') stdP ∧
      (∀ ω, ContinuousOn (g ω) Hbar) ∧
      (∀ᵐ ω ∂stdP, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (ball (b : ℂ) r₁)) ∧
      (∀ z ∈ Hbar, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' b ρ]
        fun ω => g ω z) ∧
      (∀ μ μ' : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH μ' → μ Set.univ = μ' Set.univ →
        μ (closedBall (b : ℂ) r₁)ᶜ = 0 → μ' (closedBall (b : ℂ) r₁)ᶜ = 0 →
        ∀ᵐ ω ∂stdP, W ω (μ.map Φ) - W ω (μ'.map Φ) =
          X' ω μ - X' ω μ' + ((∫ z, g ω z ∂μ) - ∫ z, g ω z ∂μ'))
      ∧ (∀ μ : LocIdx b r₁, ∀ S : Measure ℂ, IsAdmissibleH S → μ.1 Set.univ = S Set.univ →
        (∀ᵐ y ∂S, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) →
        ∃ D : (ℕ → ℝ) → ℝ, Measurable[MeasurableSpace.comap Ξ inferInstance] D ∧
          ∀ᵐ ω ∂stdP, W ω (μ.1.map Φ) - W ω S = X' ω μ.1 - X' ω (bal b ρ μ.1) + D ω) := by
  obtain ⟨J, hJ1, hJ2⟩ := exists_pullIsometry hD
  obtain ⟨Z, hZm, hZ⟩ := gs_process_hilbert (PIdx Φ b ρ r₁) (pVec J)
  have hW : IsFreeGFFModConstH (realWP Z) stdP := realWP_isFree hZm hZ
  have hX : IsFreeGFFModConstH (realXP Z) stdP := realXP_isFree hZm hZ
  set Ξ : (ℕ → ℝ) → (PXiIdx Φ b ρ r₁ → ℝ) := fun ω u => Z (Sum.inr (Sum.inr u)) ω with hΞ
  set uz : ℂ → PXiIdx Φ b ρ r₁ := fun z => ⟨harmVec Φ b ρ r₁ z, harmVec_orth hD hr₁0 z⟩ with huz
  set F : ℂ → (ℕ → ℝ) → ℝ := fun z ω => Z (Sum.inr (Sum.inr (uz z))) ω with hF
  have hb : ‖(b : ℂ) - b‖ ≤ r₁ := by rw [norm_self_sub_ofReal]; exact hr₁0.le
  -- `F z` is a version of the pulled-back harmonic increment
  have hFW : ∀ z, F z =ᵐ[stdP] pullIncr (realWP Z) Φ b ρ r₁ z := by
    intro z
    have hz := norm_retr_sub_le (t := b) hr₁0 z
    have a1 := hD.adm_map (isAdmissibleH_halfDiscPoisson hD.hρ hD.hr₁ hz)
      (halfDiscPoisson_closedBall_compl hD.hρ _)
    have a2 := hD.adm_map (isAdmissibleH_halfDiscPoisson hD.hρ hD.hr₁ hb)
      (halfDiscPoisson_closedBall_compl hD.hρ _)
    have hlaw := gs_comb4 hZ ![Sum.inr (Sum.inr (uz z)), Sum.inl ⟨_, a1⟩, Sum.inl ⟨_, a2⟩,
      Sum.inl ⟨_, a1⟩] ![1, -1, 1, 0]
      (fun ω => F z ω - (Z (Sum.inl ⟨_, a1⟩) ω - Z (Sum.inl ⟨_, a2⟩) ω))
      (fun ω => by simp [hF, Fin.sum_univ_four]; ring) (0 : WithLp 2 (HkE × HkE))
      (by
        simp [Fin.sum_univ_four, pVec, jointW, huz, harmVec, fvM_eq a1, fvM_eq a2]
        rw [← WithLp.toLp_neg, ← WithLp.toLp_add, ← WithLp.toLp_add]
        have e : freeVec ⟨Measure.map Φ (halfDiscPoisson b ρ (retr b r₁ z)), a1⟩ -
              freeVec ⟨Measure.map Φ (halfDiscPoisson b ρ ↑b), a2⟩ +
            -freeVec ⟨Measure.map Φ (halfDiscPoisson b ρ (retr b r₁ z)), a1⟩ +
          freeVec ⟨Measure.map Φ (halfDiscPoisson b ρ ↑b), a2⟩ = 0 := by abel
        simp only [Prod.mk_add_mk, Prod.neg_mk, add_zero, neg_zero, e]
        rfl)
    have h0 : (‖(0 : WithLp 2 (HkE × HkE))‖ ^ 2).toNNReal = 0 := by simp
    have hae : ∀ᵐ ω ∂stdP, F z ω - (Z (Sum.inl ⟨_, a1⟩) ω - Z (Sum.inl ⟨_, a2⟩) ω) = 0 := by
      refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
      rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
      exact Filter.eventually_pure.2 rfl
    filter_upwards [hae] with ω hω
    simp only [pullIncr]
    rw [realWP_apply (Z := Z) _ a1 ω, realWP_apply (Z := Z) _ a2 ω]
    linarith
  -- Kolmogorov version, measurable for `σ(Ξ)`
  set Kc : ℝ := (4 * pullLipC ρ r₁ m M b) ^ 4 * gaussianAbsMoment 8 with hKc
  have hK0 : 0 ≤ Kc := mul_nonneg (pow_nonneg (mul_nonneg (by norm_num)
    (pullLipC_nonneg hr₁0.le hD.hr₁)) 4) (gaussianAbsMoment_nonneg 8)
  have hmom : CircleCont.MomentBound F stdP Kc := by
    intro z hz w hw
    have h := momentBound_pullIncr hW hD hr₁0 hD.hr₁ z hz w hw
    refine le_of_eq_of_le (lintegral_congr_ae ?_) h
    filter_upwards [hFW z, hFW w] with ω h1 h2
    rw [h1, h2]
  obtain ⟨hYc, hYv⟩ := kolY_spec (fun z => (hZm _).aemeasurable) hK0 hmom
  have hY : ∀ z ∈ Hbar, kolY F z =ᵐ[stdP] pullIncr (realWP Z) Φ b ρ r₁ z := fun z hz =>
    (hYv z hz).trans (hFW z)
  have hFm : ∀ z, Measurable[MeasurableSpace.comap Ξ inferInstance] (F z) := fun z =>
    (measurable_pi_apply (uz z)).comp (comap_measurable Ξ)
  set g : (ℕ → ℝ) → ℂ → ℝ := fun ω z => kolY F z ω - harmH (realXP Z) b ρ r₁ ω z with hg
  refine ⟨realWP Z, realXP Z, Ξ, g, hW, hX, measurable_pi_iff.2 fun u => hZm _,
    realP_indep hZm hZ hJ2, fun ω => ?_, ?_, fun z hz => ?_, ?_, ?_⟩
  · exact (hYc ω).sub (continuous_harmH hX hD.hρ hr₁0 hD.hr₁ ω).continuousOn
  · filter_upwards [ae_harmonicOnNhd_pullY hW hD hr₁0 hYc hY,
      ae_harmonicOnNhd_harmH hX hD.hρ hr₁0 hD.hr₁] with ω h1 h2
    intro z hz
    have e : (fun z => g ω (foldH z)) =
        (fun z => kolY F (foldH z) ω) - harmH (realXP Z) b ρ r₁ ω := by
      funext v
      simp only [hg, Pi.sub_apply, harmH, CircleFubini.foldH_of_mem' (CircleFubini.foldH_mem_Hbar' v)]
    rw [e]
    exact (h1 z hz).sub (h2 z hz)
  · exact ((@measurable_kolY _ (MeasurableSpace.comap Ξ inferInstance) F hFm z hz).mono
      le_sup_left le_rfl).sub
      ((measurable_harmH_outside hD.hρ hr₁0 hD.hr₁ z).mono le_sup_right le_rfl)
  · intro μ μ' hμA hμ'A hm hμc hμ'c
    have := hμA.1
    have := hμ'A.1
    have hK : ∀ α : Measure ℂ, IsAdmissibleH α → α (closedBall (b : ℂ) r₁)ᶜ = 0 →
        α (closedBall (b : ℂ) r₁ ∩ Hbar)ᶜ = 0 := fun α hα hαc => by
      rw [compl_inter]
      exact measure_union_null hαc (mem_ae_iff.1 (ae_mem_Hbar_of_admissible hα))
    have hgi : ∀ ω (α : Measure ℂ) [IsFiniteMeasure α], α (closedBall (b : ℂ) r₁ ∩ Hbar)ᶜ = 0 →
        ∫ z, g ω z ∂α = (∫ z, kolY F z ω ∂α) - ∫ z, harmH (realXP Z) b ρ r₁ ω z ∂α := by
      intro ω α _ hα
      exact integral_sub (integrable_of_continuousOn_closedBall_Hbar
        ((hYc ω).mono inter_subset_right) hα)
        (integrable_of_continuousOn_closedBall_Hbar
          (continuous_harmH hX hD.hρ hr₁0 hD.hr₁ ω).continuousOn hα)
    filter_upwards [realP_local hZ hD hJ1 ⟨μ, hμA, hμc⟩, realP_local hZ hD hJ1 ⟨μ', hμ'A, hμ'c⟩,
      pull_stochFubini hW hD hr₁0 hD.hr₁ μ (hK μ hμA hμc) hYc hY,
      pull_stochFubini hW hD hr₁0 hD.hr₁ μ' (hK μ' hμ'A hμ'c) hYc hY,
      markov_decomposition hX hD.hρ hr₁0 hD.hr₁ hμA hμc,
      markov_decomposition hX hD.hρ hr₁0 hD.hr₁ hμ'A hμ'c] with ω h1 h2 h3 h4 h5 h6
    rw [hgi ω μ (hK μ hμA hμc), hgi ω μ' (hK μ' hμ'A hμ'c), h3, h4, hm]
    simp only [markovZ] at h5 h6
    rw [hm] at h5
    linarith
  · intro μ S hS hm hSy
    obtain ⟨u, hu⟩ := ae_realWP_far hD hJ1 hZ μ hS hm hSy
    exact ⟨fun ω => Ξ ω u, (measurable_pi_apply u).comp (comap_measurable Ξ), hu⟩

/-- **Piece 1: the local conformal Markov coupling (D3⁺ form).** -/
theorem exists_pullSetupFar (hD : PullData Φ b r₀ ρ r₁ m M) (hr₁0 : 0 < r₁) {r' : ℝ}
    (hr' : 0 < r') (hr'r : r' < r₁) :
    ∃ (W X' : (ℕ → ℝ) → FieldSample) (Ξ : (ℕ → ℝ) → (PXiIdx Φ b ρ r₁ → ℝ))
      (g : (ℕ → ℝ) → ℂ → ℝ),
      IsFreeGFFModConstH W stdP ∧ IsFreeGFFModConstH X' stdP ∧ Measurable Ξ ∧
      Indep (MeasurableSpace.comap Ξ inferInstance) (freeIncrSigma X') stdP ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (closedBall (b : ℂ) r')) ∧
      (∀ z, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' b ρ]
        fun ω => g ω z) ∧
      (∀ μ μ' : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH μ' → μ Set.univ = μ' Set.univ →
        μ (closedBall (b : ℂ) r')ᶜ = 0 → μ' (closedBall (b : ℂ) r')ᶜ = 0 →
        ∀ᵐ ω ∂stdP, W ω (μ.map Φ) - W ω (μ'.map Φ) =
          X' ω μ - X' ω μ' + ((∫ z, g ω z ∂μ) - ∫ z, g ω z ∂μ'))
      ∧ (∀ μ : LocIdx b r₁, ∀ S : Measure ℂ, IsAdmissibleH S → μ.1 Set.univ = S Set.univ →
        (∀ᵐ y ∂S, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) →
        ∃ D : (ℕ → ℝ) → ℝ, Measurable[MeasurableSpace.comap Ξ inferInstance] D ∧
          ∀ᵐ ω ∂stdP, W ω (μ.1.map Φ) - W ω S = X' ω μ.1 - X' ω (bal b ρ μ.1) + D ω) := by
  obtain ⟨W, X', Ξ, g, hW, hX, hΞ, hind, hgc, hgh, hgm, hid, hfar⟩ :=
    exists_pullCouplingHarmFar hD hr₁0
  set δ : ℝ := (r₁ - r') / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ρ₁ : ℝ := r' + δ with hρ₁
  set s : ℝ := r' + 2 * δ with hs
  have hρ₁0 : 0 < ρ₁ := by linarith
  have hρ₁s : ρ₁ < s := by linarith
  have hr'ρ₁ : r' < ρ₁ := by linarith
  have hsr₁ : s < r₁ := by rw [hs, hδ]; linarith
  set G : (ℕ → ℝ) → ℂ → ℝ := fun ω w => g ω (foldH w) with hG
  have hGc : ∀ ω, Continuous (G ω) := fun ω =>
    (hgc ω).comp_continuous CircleFubini.continuous_foldH' CircleFubini.foldH_mem_Hbar'
  have hGm : ∀ w, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' b ρ]
      fun ω => G ω w := fun w => hgm (foldH w) (CircleFubini.foldH_mem_Hbar' w)
  refine ⟨W, X', Ξ, fun ω => poisSm b s ρ₁ (G ω), hW, hX, hΞ, hind,
    fun ω => harmonicOnNhd_poisSm_foldH (hGc ω) hρ₁0 hρ₁s hr'ρ₁,
    fun z => measurable_poisSm _ hGc hGm b s ρ₁ z, ?_, hfar⟩
  intro μ μ' hμA hμ'A hm hμc hμ'c
  have hsub : (closedBall (b : ℂ) r₁)ᶜ ⊆ (closedBall (b : ℂ) r')ᶜ :=
    compl_subset_compl.2 (closedBall_subset_closedBall hr'r.le)
  have hK : ∀ α : Measure ℂ, IsAdmissibleH α → α (closedBall (b : ℂ) r')ᶜ = 0 →
      ∀ᵐ z ∂α, z ∈ closedBall (b : ℂ) r' ∩ Hbar := fun α hα hαc => by
    filter_upwards [ae_mem_Hbar_of_admissible hα, ae_mem_of_compl_null_g3cv hαc] with z h1 h2
    exact ⟨h2, h1⟩
  filter_upwards [hid μ μ' hμA hμ'A hm (measure_mono_null hsub hμc)
    (measure_mono_null hsub hμ'c), hgh] with ω h1 h2
  have hGh : InnerProductSpace.HarmonicOnNhd (G ω) (closedBall (b : ℂ) s) := fun z hz =>
    h2 z (closedBall_subset_ball hsr₁ hz)
  have heq : ∀ α : Measure ℂ, IsAdmissibleH α → α (closedBall (b : ℂ) r')ᶜ = 0 →
      ∫ z, poisSm b s ρ₁ (G ω) z ∂α = ∫ z, g ω z ∂α := fun α hα hαc =>
    integral_congr_ae ((hK α hα hαc).mono fun z hz => by
      rw [poisSm_eq_of_harmonic hρ₁s hGh (fun x _ => by simp only [hG, foldH_conj_k3]) hz.2
        ((mem_closedBall_iff_norm.1 hz.1).trans hr'ρ₁.le)]
      simp only [hG, CircleFubini.foldH_of_mem' hz.2])
  rw [heq μ hμA hμc, heq μ' hμ'A hμ'c]
  exact h1

end G3Za
end QuantumZipper
