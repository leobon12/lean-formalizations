import QuantumZipper.Proofs.Thm18.G3CvAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (c), step 1: the pulled-back field away from the pull-back region is `Ξ`-measurable

For the two-point zoom (Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71: "conditioned on
the field outside of the two small half-discs, the two zooms are independent"), the local
conformal coupling of `exists_pullCouplingHarm` at the first point must also say that the field
`W` **away** from the pull-back region `Φ(closedBall b ρ)` is a function of the conditioning
variables `Ξ` (which are independent of the coupled free field `X'`). This is the domain Markov
property of `W ∘ Φ` (Sheffield, *Gaussian free fields for mathematicians* (2007), Thm. 2.17): in
the Hilbert realization, the vector `v̂_α − v̂_α'` of an increment carried away from
`Φ(closedBall b ρ)` and its reflection is orthogonal to the pulled-back local part
(`inner_fvM_sub_pullLocVec_eq_zero`, G3CvOut), so it is itself one of the `Ξ`-indices, and the
increment equals that `Ξ`-coordinate a.s. (zero variance of the difference).

* `FarPair Φ b ρ α α'`: admissible, equal mass, carried away from `Φ(closedBall b ρ)` and its
  reflection;
* `realP_far`: a.s. `W(α) − W(α') = Ξ(v̂_α − v̂_α')`;
* `exists_pullCouplingHarm_far`: `exists_pullCouplingHarm` plus this conjunct (same proof).

Own adaptation (AGENT_GUIDE cost rule) of `realP_local` (G3CvReal) and G3CvAsm.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- A balanced pair of admissible measures carried away from `Φ(closedBall b ρ)` and from its
reflection. -/
def FarPair (Φ : ℂ → ℂ) (b ρ : ℝ) (α α' : Measure ℂ) : Prop :=
  IsAdmissibleH α ∧ IsAdmissibleH α' ∧ α Set.univ = α' Set.univ ∧
    (∀ᵐ y ∂α, ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y) ∧
    (∀ᵐ y ∂α', ∀ w ∈ closedBall (b : ℂ) ρ, Φ w ≠ y ∧ Φ w ≠ conj y)

/-- The `Ξ`-index of a far increment. -/
def farIdx (hD : PullData Φ b r₀ ρ r₁ m M) {α α' : Measure ℂ} (h : FarPair Φ b ρ α α') :
    PXiIdx Φ b ρ r₁ :=
  ⟨fvM α - fvM α', fun ν =>
    inner_fvM_sub_pullLocVec_eq_zero hD h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 ν⟩

/-- **Far increments are `Ξ`-coordinates** (Hilbert realization). -/
theorem realP_far {hρ : 0 < ρ} {hr₁ : r₁ < ρ} {J : freeLocSpace (t := b) hρ hr₁ →ₗᵢ[ℝ] HkE}
    {Z : PIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ}
    (hZ : ∀ {ι : Type} [Fintype ι] (τ : ι → PIdx Φ b ρ r₁) (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * Z (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • pVec J (τ i)‖ ^ 2).toNNReal) stdP)
    (hD : PullData Φ b r₀ ρ r₁ m M) {α α' : Measure ℂ} (h : FarPair Φ b ρ α α') :
    ∀ᵐ ω ∂stdP, realWP Z ω α - realWP Z ω α' = Z (Sum.inr (Sum.inr (farIdx hD h))) ω := by
  have a1 := h.1
  have a2 := h.2.1
  have hlaw := gs_comb4 hZ ![Sum.inl ⟨α, a1⟩, Sum.inl ⟨α', a2⟩, Sum.inr (Sum.inr (farIdx hD h)),
      Sum.inl ⟨α, a1⟩] ![1, -1, -1, 0]
    (fun ω => Z (Sum.inl ⟨α, a1⟩) ω - Z (Sum.inl ⟨α', a2⟩) ω - Z (Sum.inr (Sum.inr (farIdx hD h))) ω)
    (fun ω => by simp [Fin.sum_univ_four]; ring) (0 : WithLp 2 (HkE × HkE))
    (by
      have e1 : fvM α = freeVec ⟨α, a1⟩ := fvM_eq a1
      have e2 : fvM α' = freeVec ⟨α', a2⟩ := fvM_eq a2
      simp [Fin.sum_univ_four, pVec, jointW, farIdx, e1, e2]
      have e : (freeVec ⟨α, a1⟩, (0 : HkE)) + -(freeVec ⟨α', a2⟩, (0 : HkE)) +
          -(freeVec ⟨α, a1⟩ - freeVec ⟨α', a2⟩, (0 : HkE)) = 0 := by
        refine Prod.ext ?_ ?_
        · simp only [Prod.fst_add, Prod.fst_neg, Prod.fst_zero]; abel
        · simp
      show (0 : WithLp 2 (HkE × HkE)) = WithLp.toLp 2 ((freeVec ⟨α, a1⟩, (0 : HkE)) +
        -(freeVec ⟨α', a2⟩, (0 : HkE)) + -(freeVec ⟨α, a1⟩ - freeVec ⟨α', a2⟩, (0 : HkE)))
      rw [e]
      rfl)
  have h0 : (‖(0 : WithLp 2 (HkE × HkE))‖ ^ 2).toNNReal = 0 := by simp
  have hae : ∀ᵐ ω ∂stdP, Z (Sum.inl ⟨α, a1⟩) ω - Z (Sum.inl ⟨α', a2⟩) ω -
      Z (Sum.inr (Sum.inr (farIdx hD h))) ω = 0 := by
    refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
    rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  filter_upwards [hae] with ω hω
  rw [realWP_apply (Z := Z) _ a1 ω, realWP_apply (Z := Z) _ a2 ω]
  linarith

/-- The `Ξ`-variables of a realization `Z`. -/
def realXi (Z : PIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ) : (ℕ → ℝ) → (PXiIdx Φ b ρ r₁ → ℝ) :=
  fun ω u => Z (Sum.inr (Sum.inr u)) ω

/-- **The local conformal coupling for a given realization `Z`**, with the far field in `σ(Ξ)`:
the proof of `exists_pullCouplingHarm` for an arbitrary process `Z` with the isonormal laws of
`pVec J`, plus the far conjunct. Parametrizing by `Z` lets two such couplings (at two points)
share the same field `W = realWP Z` (ZOOM-C (c)). -/
theorem pullCouplingHarm_of_process (hD : PullData Φ b r₀ ρ r₁ m M) (hr₁0 : 0 < r₁)
    {J : freeLocSpace (t := b) hD.hρ hD.hr₁ →ₗᵢ[ℝ] HkE}
    (hJ1 : ∀ μ : LocIdx b r₁, J ⟨freeLocVec hD.hρ hD.hr₁ μ,
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)⟩ =
          pullLocVec Φ b ρ μ.1)
    (hJ2 : ∀ x, J x ∈ (Submodule.span ℝ (Set.range fun μ : LocIdx b r₁ =>
        pullLocVec Φ b ρ μ.1)).topologicalClosure)
    {Z : PIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ} (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ {ι : Type} [Fintype ι] (τ : ι → PIdx Φ b ρ r₁) (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * Z (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • pVec J (τ i)‖ ^ 2).toNNReal) stdP) :
    ∃ g : (ℕ → ℝ) → ℂ → ℝ,
      IsFreeGFFModConstH (realWP Z) stdP ∧ IsFreeGFFModConstH (realXP Z) stdP ∧
      Measurable (realXi Z) ∧
      Indep (MeasurableSpace.comap (realXi Z) inferInstance) (freeIncrSigma (realXP Z)) stdP ∧
      (∀ α α' : Measure ℂ, FarPair Φ b ρ α α' →
        ∃ u : PXiIdx Φ b ρ r₁, ∀ᵐ ω ∂stdP, realWP Z ω α - realWP Z ω α' = realXi Z ω u) ∧
      (∀ ω, ContinuousOn (g ω) Hbar) ∧
      (∀ᵐ ω ∂stdP, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (ball (b : ℂ) r₁)) ∧
      (∀ z ∈ Hbar, Measurable[MeasurableSpace.comap (realXi Z) inferInstance ⊔
          outsideSigma (realXP Z) b ρ] fun ω => g ω z) ∧
      ∀ μ μ' : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH μ' → μ Set.univ = μ' Set.univ →
        μ (closedBall (b : ℂ) r₁)ᶜ = 0 → μ' (closedBall (b : ℂ) r₁)ᶜ = 0 →
        ∀ᵐ ω ∂stdP, realWP Z ω (μ.map Φ) - realWP Z ω (μ'.map Φ) =
          realXP Z ω μ - realXP Z ω μ' + ((∫ z, g ω z ∂μ) - ∫ z, g ω z ∂μ') := by
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
  refine ⟨g, hW, hX, measurable_pi_iff.2 fun u => hZm _,
    realP_indep hZm hZ hJ2, fun α α' hf => ⟨farIdx hD hf, realP_far hZ hD hf⟩, fun ω => ?_, ?_,
    fun z hz => ?_, ?_⟩
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

end G3Cv
end QuantumZipper
