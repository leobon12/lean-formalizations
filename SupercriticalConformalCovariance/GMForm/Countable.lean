import SupercriticalConformalCovariance.Frozen.ConformalCovariance
import SupercriticalConformalCovariance.GMForm.Functional
import SupercriticalConformalCovariance.Tangent.LocalFunctional

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set Function
open scoped ENNReal
open LQGMetric (DistC DistOn IsGFFPlusCont IsWholePlaneGFF IsZeroBoundaryGFF restrictTo ofCont)
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)
open SupercriticalConformalCovariance
open SmallGammaGeodesics.CC (mixMeasure exists_pos_weights isProbabilityMeasure_mixMeasure
  measurable_sigmaMk measurable_of_sigma map_mixMeasure sum_smul_eq_of_tsum_eq_one
  ae_of_ae_mixMeasure)

namespace SupercriticalConformalCovariance.GMForm

/-- One Borel domain-metric functional serves any specified countable family
of realized domain fields, even with corrections dependent on their GFFs.
This is the domain-realization analogue of the Lemma 3.3 proof's coin-mixture argument. -/
theorem exists_countably_universal_domain_metric
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U : Opens ℂ)
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (h : ∀ i, Ω i → DistOn U)
    (g : ∀ i, Ω i → DistC) (f : ∀ i, Ω i → C(U, ℝ))
    (hr : ∀ i, IsDomainRealization U (P i) (h i) (g i) (f i)) :
    ∃ Φ : DistOn U → (U × U → ℝ≥0∞), Measurable Φ ∧
      ∀ i, ∀ᵐ ω ∂P i,
        Φ (h i ω) = domainMetric (ξ : ℝ) D U (g i ω) (f i ω) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ _ => 0, measurable_const, fun i => (IsEmpty.false i).elim⟩
  obtain ⟨w, hw0, hw1⟩ := exists_pos_weights ι
  choose c hcm hG using fun i => (hr i).2.1.2
  haveI : IsProbabilityMeasure (mixMeasure w P) := isProbabilityMeasure_mixMeasure hw1
  let H : Sigma Ω → DistOn U := fun p => h p.1 p.2
  let G : Sigma Ω → DistC := fun p => g p.1 p.2
  let F : Sigma Ω → C(U, ℝ) := fun p => f p.1 p.2
  let C : Sigma Ω → C(ℂ, ℝ) := fun p => c p.1 p.2
  have hHm : Measurable H := measurable_of_sigma fun i => (hr i).1
  have hGm : Measurable G := measurable_of_sigma fun i => (hr i).2.1.1
  have hFm : Measurable F := measurable_of_sigma fun i => (hr i).2.2.1
  have hCm : Measurable C := measurable_of_sigma fun i => hcm i
  have hXm : Measurable fun p => G p - ofCont (C p) :=
    measurable_of_sigma fun i => (hG i).measurable
  obtain ⟨i₀⟩ := hι
  have hX : IsWholePlaneGFF (fun p => G p - ofCont (C p)) (mixMeasure w P) := by
    refine SmallGammaGeodesics.CC.isWholePlaneGFF_of_map_pairProc_eq hXm (hG i₀) ?_
    rw [map_mixMeasure (LQGMetric.GFFLaw.measurable_pairProc hXm)]
    have e : ∀ i, (P i).map (fun ω => LQGMetric.GFFLaw.pairProc
        (fun p => G p - ofCont (C p)) ⟨i, ω⟩) =
        (P i₀).map (LQGMetric.GFFLaw.pairProc fun ω => g i₀ ω - ofCont (c i₀ ω)) :=
      fun i => LQGMetric.GFFLaw.map_pairProc_eq (hG i) (hG i₀)
    simp only [e]
    exact sum_smul_eq_of_tsum_eq_one hw1 _
  have hGc : IsGFFPlusCont G (mixMeasure w P) := ⟨hGm, C, hCm, hX⟩
  have hRm : Measurable fun p : Sigma Ω =>
      restrictTo U (G p) +
        Distribution.ofFun U (Function.extend Subtype.val (F p) 0) volume ⊤ := by
    apply LQGMetric.measurable_distOn_iff.2
    intro ψ
    have h1 := (LQGMetric.measurable_distOn_apply ψ).comp
      ((LQGMetric.measurable_restrictTo U).comp hGm)
    have h2 := (LQGMetric.measurable_distOn_apply ψ).comp
      (SupercriticalConformalCovariance.Domain.measurable_ofFun_extZ U hFm)
    exact h1.add h2
  have hE : MeasurableSet {p : Sigma Ω | H p = restrictTo U (G p) +
      Distribution.ofFun U (Function.extend Subtype.val (F p) 0) volume ⊤} :=
    measurableSet_eq_fun hHm hRm
  have hRe : ∀ᵐ p ∂mixMeasure w P, H p = restrictTo U (G p) +
      Distribution.ofFun U (Function.extend Subtype.val (F p) 0) volume ⊤ := by
    rw [mixMeasure, Measure.ae_sum_iff]
    intro i
    rw [Measure.ae_ennreal_smul_measure_iff (hw0 i)]
    exact (ae_map_iff (measurable_sigmaMk i).aemeasurable hE).2 (by
      simpa only [H, G, F] using (hr i).2.2.2)
  have hR : IsDomainRealization U (mixMeasure w P) H G F :=
    ⟨hHm, hGc, hFm, hRe⟩
  obtain ⟨Φ, hΦm, hΦ⟩ := SupercriticalConformalCovariance.Domain.exists_measurable_domainMetric hD U hR
  exact ⟨Φ, hΦm, fun i =>
    (ae_of_ae_mixMeasure hw0 hΦ i).mono fun _ e => e.symm⟩

/-- For any specified countable collection of GM zero-boundary fields, one
Borel distribution-indexed domain metric works for chosen whole-plane
realizations of every member, including arbitrary dependent corrections. -/
theorem exists_countably_universal_metric_of_zeroBoundary
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U : Opens ℂ) (hUg : IsGreenian U)
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (h z : ∀ i, Ω i → DistOn U) (f : ∀ i, Ω i → C(U, ℝ))
    (hh : ∀ i, Measurable (h i)) (hz : ∀ i, IsZeroBoundaryGFF U (z i) (P i))
    (hf : ∀ i, Measurable (f i))
    (heq : ∀ i, ∀ᵐ ω ∂P i, h i ω = z i ω +
      Distribution.ofFun U (Function.extend Subtype.val (f i ω) 0) volume ⊤) :
    ∃ Φ : DistOn U → (U × U → ℝ≥0∞), Measurable Φ ∧
      ∀ i, ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
          (π : Ω' → Ω i) (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
        MeasurePreserving π P' (P i) ∧
        IsDomainRealization U P' (h i ∘ π) g₀ k ∧
        ∀ᵐ ω' ∂P', Φ (h i (π ω')) = domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') := by
  have hex : ∀ i, ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (π : Ω' → Ω i) (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
        MeasurePreserving π P' (P i) ∧
        IsDomainRealization U P' (h i ∘ π) g₀ k := by
    intro i
    exact exists_realization_of_zeroBoundary (P i) U hUg (h i) (z i) (f i)
      (hh i) (hz i) (hf i) (heq i)
  choose Ω' mΩ' P' π g₀ k hπ hr using hex
  letI : ∀ i, MeasurableSpace (Ω' i) := mΩ'
  haveI : ∀ i, IsProbabilityMeasure (P' i) :=
    fun i => SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving (hπ i)
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_countably_universal_domain_metric
    ξ Q D hD U ι Ω' P' (fun i => h i ∘ π i) g₀ k hr
  exact ⟨Φ, hΦm, fun i =>
    ⟨Ω' i, mΩ' i, P' i, π i, g₀ i, k i, hπ i, hr i, hΦ i⟩⟩

/-- The forward GM coordinate formula with one Borel map on each domain for
any specified countable family of zero-boundary fields. Both maps are shared
across the family; the all-pairs event lives on each chosen realization
extension. -/
theorem exists_countably_universal_gm_axiomIV_on_extensions
    (ξ : Set.Ioi (0 : ℝ)) (hξ : xiCrit < (ξ : ℝ))
    (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U V : Opens ℂ) (hUc : IsConnected (U : Set ℂ)) (hVc : IsConnected (V : Set ℂ))
    (hUg : IsGreenian U) (hVg : IsGreenian V)
    (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (h z : ∀ i, Ω i → DistOn U) (f : ∀ i, Ω i → C(U, ℝ))
    (hh : ∀ i, Measurable (h i)) (hz : ∀ i, IsZeroBoundaryGFF U (z i) (P i))
    (hf : ∀ i, Measurable (f i))
    (heq : ∀ i, ∀ᵐ ω ∂P i, h i ω = z i ω +
      Distribution.ofFun U (Function.extend Subtype.val (f i ω) 0) volume ⊤) :
    ∃ ΦU : DistOn U → (U × U → ℝ≥0∞), Measurable ΦU ∧
    ∃ ΦV : DistOn V → (V × V → ℝ≥0∞), Measurable ΦV ∧
    ∀ i, ∃ (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁)
        (π₁ : Ω₁ → Ω i) (a₀ : Ω₁ → DistC) (a : Ω₁ → C(U, ℝ)),
      MeasurePreserving π₁ P₁ (P i) ∧
      IsDomainRealization U P₁ (h i ∘ π₁) a₀ a ∧
      (∀ᵐ ω ∂P₁, ΦU (h i (π₁ ω)) = domainMetric (ξ : ℝ) D U (a₀ ω) (a ω)) ∧
      ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂)
          (π₂ : Ω₂ → Ω₁) (b₀ : Ω₂ → DistC) (b : Ω₂ → C(V, ℝ)),
        MeasurePreserving π₂ P₂ P₁ ∧
        IsDomainRealization V P₂
          (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
            (h i (π₁ (π₂ ω)))) b₀ b ∧
        (∀ᵐ ω ∂P₂,
          ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
            (h i (π₁ (π₂ ω)))) = domainMetric (ξ : ℝ) D V (b₀ ω) (b ω)) ∧
        (∀ᵐ ω ∂P₂, ∀ u v : U,
          ΦU (h i (π₁ (π₂ ω))) (u, v) =
            ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
              (h i (π₁ (π₂ ω))))
              (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩)) := by
  have hex : ∀ i, ∃ (Ω₁ : Type) (_ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁)
      (π₁ : Ω₁ → Ω i) (a₀ : Ω₁ → DistC) (a : Ω₁ → C(U, ℝ)),
      MeasurePreserving π₁ P₁ (P i) ∧
      IsDomainRealization U P₁ (h i ∘ π₁) a₀ a ∧
      ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂)
          (π₂ : Ω₂ → Ω₁) (b₀ : Ω₂ → DistC) (b : Ω₂ → C(V, ℝ)),
        MeasurePreserving π₂ P₂ P₁ ∧
        IsDomainRealization V P₂
          (fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
            (h i (π₁ (π₂ ω)))) b₀ b ∧
        (∀ᵐ ω ∂P₂, ∀ u v : U,
          domainMetric (ξ : ℝ) D U (a₀ (π₂ ω)) (a (π₂ ω)) (u, v) =
            domainMetric (ξ : ℝ) D V (b₀ ω) (b ω)
              (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩)) := by
    intro i
    exact gm_zeroBoundary_covariance_on_extension ξ hξ Q hQ D hD
      U V hUc hVc hUg hVg φ hφ (P i) (h i) (z i) (f i)
      (hh i) (hz i) (hf i) (heq i)
  choose Ω₁ mΩ₁ P₁ π₁ a₀ a hπ₁ ha Ω₂ mΩ₂ P₂ π₂ b₀ b hπ₂ hb hcov using hex
  letI : ∀ i, MeasurableSpace (Ω₁ i) := mΩ₁
  haveI : ∀ i, IsProbabilityMeasure (P₁ i) :=
    fun i => SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving (hπ₁ i)
  letI : ∀ i, MeasurableSpace (Ω₂ i) := mΩ₂
  haveI : ∀ i, IsProbabilityMeasure (P₂ i) :=
    fun i => SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving (hπ₂ i)
  obtain ⟨ΦU, hΦUm, hΦU⟩ := exists_countably_universal_domain_metric
    ξ Q D hD U ι Ω₁ P₁ (fun i => h i ∘ π₁ i) a₀ a ha
  obtain ⟨ΦV, hΦVm, hΦV⟩ := exists_countably_universal_domain_metric
    ξ Q D hD V ι Ω₂ P₂
    (fun i ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ)
      (h i (π₁ i (π₂ i ω)))) b₀ b hb
  refine ⟨ΦU, hΦUm, ΦV, hΦVm, fun i =>
    ⟨Ω₁ i, mΩ₁ i, P₁ i, π₁ i, a₀ i, a i, hπ₁ i, ha i, hΦU i,
      Ω₂ i, mΩ₂ i, P₂ i, π₂ i, b₀ i, b i, hπ₂ i, hb i, hΦV i, ?_⟩⟩
  have hΦU₂ : ∀ᵐ ω ∂P₂ i,
      ΦU (h i (π₁ i (π₂ i ω))) =
        domainMetric (ξ : ℝ) D U (a₀ i (π₂ i ω)) (a i (π₂ i ω)) := by
    have hm : ∀ᵐ x ∂(P₂ i).map (π₂ i),
        ΦU (h i (π₁ i x)) = domainMetric (ξ : ℝ) D U (a₀ i x) (a i x) := by
      rw [(hπ₂ i).map_eq]
      exact hΦU i
    exact ae_of_ae_map (hπ₂ i).measurable.aemeasurable hm
  filter_upwards [hΦU₂, hΦV i, hcov i] with ω eU eV ec
  intro u v
  rw [eU, eV]
  exact ec u v

end SupercriticalConformalCovariance.GMForm
