import SupercriticalConformalCovariance.Frozen.ConformalCovariance
import SupercriticalConformalCovariance.GMForm.Countable
import SupercriticalConformalCovariance.GPull.Measurable
import SupercriticalConformalCovariance.GMForm.Independence
import SupercriticalConformalCovariance.Tangent.LocalFunctional

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set Function
open scoped ENNReal
open LQGMetric (DistC DistOn IsGFFPlusCont IsZeroBoundaryGFF restrictTo)
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GMForm

theorem ae_of_ae_fst {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X]
    [Nonempty X] {P : Measure Ω} {μ : Measure (Ω × X)} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving Prod.fst μ P) {q : Ω → Prop} (hq : ∀ᵐ p ∂μ, q p.1) : ∀ᵐ ω ∂P, q ω := by
  rw [ae_iff] at hq
  obtain ⟨t, hst, htm, ht0⟩ := exists_measurable_superset_of_null hq
  rw [← μ.disintegrate μ.condKernel, Measure.compProd_apply htm] at ht0
  have h2 := (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left htm)).1 ht0
  have hfst : μ.fst = P := by rw [Measure.fst, hμ.map_eq]
  rw [hfst] at h2
  filter_upwards [h2] with ω hω
  by_contra hn
  have hu : Prod.mk ω ⁻¹' t = univ := eq_univ_of_forall fun x => hst (show ¬ q (ω, x).1 from hn)
  have : μ.condKernel ω univ = 0 := by simpa [hu] using hω
  simp at this

theorem isZeroBoundaryGFF_comp {U : Opens ℂ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P)
    {z : Ω → DistOn U} (hz : IsZeroBoundaryGFF U z P) : IsZeroBoundaryGFF U (z ∘ π) P' where
  measurable := hz.measurable.comp hπ.measurable
  process :=
    { measurable := fun φ => (hz.process.measurable φ).comp hπ.measurable
      gaussian := ⟨fun I => by
        have hI := hz.process.gaussian.hasGaussianLaw I
        have hm : Measurable fun ω => I.restrict fun φ => z ω φ :=
          measurable_pi_iff.2 fun φ => hz.process.measurable φ.1
        refine ⟨(hm.comp hπ.measurable).aemeasurable, ?_⟩
        have e : P'.map (fun ω' => I.restrict fun φ => (z ∘ π) ω' φ) =
            P.map (fun ω => I.restrict fun φ => z ω φ) := by
          rw [show (fun ω' => I.restrict fun φ => (z ∘ π) ω' φ) =
            (fun ω => I.restrict fun φ => z ω φ) ∘ π from rfl, ← Measure.map_map hm hπ.measurable,
            hπ.map_eq]
        rw [e]; exact hI.isGaussian_map⟩
      centered := fun φ => by
        rw [← hz.process.centered φ, ← hπ.map_eq,
          integral_map hπ.measurable.aemeasurable (hz.process.measurable φ).aestronglyMeasurable]
        rfl
      covariance_eq := fun φ ψ => by
        rw [← hz.process.covariance_eq φ ψ, ← hπ.map_eq,
          covariance_map (hz.process.measurable φ).aestronglyMeasurable
            (hz.process.measurable ψ).aestronglyMeasurable hπ.measurable.aemeasurable]
        rfl }

/-- The proof of `exists_realization_of_zeroBoundary`, with the extension exposed as `Ω × DistC`, `π = Prod.fst`. -/
theorem exists_prod_realization_of_zeroBoundary
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Opens ℂ) (hU : IsGreenian U)
    (h z : Ω → DistOn U) (f : Ω → C(U, ℝ))
    (hh : Measurable h) (hz : IsZeroBoundaryGFF U z P) (hf : Measurable f)
    (heq : ∀ᵐ ω ∂P, h ω = z ω +
      Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤) :
    ∃ (P' : Measure (Ω × DistC)) (g₀ : Ω × DistC → DistC) (k : Ω × DistC → C(U, ℝ)),
      MeasurePreserving Prod.fst P' P ∧ IsDomainRealization U P' (h ∘ Prod.fst) g₀ k := by
  obtain ⟨P', F, H, hP', hfst, hg, hFm, hHm, hHc, hzeq, hpair⟩ :=
    SupercriticalConformalCovariance.GPull.exists_reference_coupling P hz hU
  let T : (Ω × DistC) → U → ℝ := fun p x => f p.1 x - H p.2 x
  have hTm : Measurable (fun q : (Ω × DistC) × U => T q.1 q.2) := by
    have hf' : Measurable (fun q : (Ω × DistC) × U => f q.1.1 q.2) :=
      continuous_eval.measurable.comp
        (Measurable.prodMk
          (hf.comp (measurable_fst.comp measurable_fst)) measurable_snd)
    have hH' : Measurable (fun q : (Ω × DistC) × U => H q.1.2 q.2) :=
      hHm.comp (Measurable.prodMk
        (measurable_snd.comp measurable_fst)
        (measurable_subtype_coe.comp measurable_snd))
    exact hf'.sub hH'
  have hTc : ∀ᵐ p ∂P', Continuous (T p) := by
    filter_upwards [hHc] with p hp
    exact (f p.1).continuous.sub hp
  obtain ⟨k, hkm, hk⟩ :=
    SupercriticalConformalCovariance.GPull.exists_measurable_continuous_version hTm hTc
  let g₀ : (Ω × DistC) → DistC := Prod.snd
  have hgp : IsGFFPlusCont g₀ P' :=
    LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hg
  have heq' : ∀ᵐ p ∂P', h p.1 = z p.1 +
      Distribution.ofFun U (Function.extend Subtype.val (f p.1) 0) volume ⊤ := by
    have he : ∀ᵐ ω ∂P'.map (Prod.fst : Ω × DistC → Ω),
        h ω = z ω +
          Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤ := by
      simpa only [hfst.map_eq] using heq
    exact ae_of_ae_map measurable_fst.aemeasurable he
  have hreal : ∀ᵐ p ∂P', h p.1 = restrictTo U (g₀ p) +
      Distribution.ofFun U (Function.extend Subtype.val (k p) 0) volume ⊤ := by
    filter_upwards [heq', hzeq, hpair, hk, hHc] with p hp hzpair hpairp hkp hcont
    ext ψ
    have hfcont : ContinuousOn (Function.extend Subtype.val (f p.1) 0)
        (U : Set ℂ) := SupercriticalConformalCovariance.GPull.continuousOn_extZ (f p.1)
    have hHcont : ContinuousOn (H p.2) (U : Set ℂ) :=
      continuousOn_iff_continuous_domRestrict.mpr hcont
    have hKcont : ContinuousOn (fun x : ℂ =>
        Function.extend Subtype.val (k p) 0 x) (U : Set ℂ) :=
      SupercriticalConformalCovariance.GPull.continuousOn_extZ (k p)
    have hKeq : ∀ x (hx : x ∈ (U : Set ℂ)),
        k p ⟨x, hx⟩ =
          Function.extend Subtype.val (f p.1) 0 x - H p.2 x := by
      intro x hx
      calc
        k p ⟨x, hx⟩ = f p.1 ⟨x, hx⟩ - H p.2 x := hkp ⟨x, hx⟩
        _ = Function.extend Subtype.val (f p.1) 0 x - H p.2 x := by
          have hfpoint : Function.extend Subtype.val (f p.1) 0 x = f p.1 ⟨x, hx⟩ := by
            conv_lhs => rw [show x = ((⟨x, hx⟩ : U) : ℂ) from rfl]
            exact Subtype.val_injective.extend_apply _ _ _
          rw [hfpoint]
    have hKi := SupercriticalConformalCovariance.GPull.ofFun_extZ_apply_eq (k p)
      (hfcont.sub hHcont) hKeq ψ
    simp only [Pi.sub_apply] at hKi
    have hFi := SupercriticalConformalCovariance.GPull.ofFun_extZ_pair (f p.1) ψ
    have hsub := SupercriticalConformalCovariance.GPull.integral_test_sub hfcont hHcont ψ
    have hrsub : (restrictTo U (p.2 - F p.2)) ψ =
        (restrictTo U p.2) ψ - (restrictTo U (F p.2)) ψ := rfl
    have hzp : z p.1 ψ = (restrictTo U (F p.2)) ψ := by rw [hzpair]
    have hdiff := hpairp ψ
    rw [hrsub] at hdiff
    rw [hp, add_apply, add_apply, hzp, hFi, hKi, hsub]
    dsimp only [g₀]
    linarith
  exact ⟨P', g₀, k, hfst,
    ⟨hh.comp measurable_fst, hgp, hkm, hreal⟩⟩



/-- Pull a product realization to an arbitrary base extension using its conditional law. -/
theorem product_common_refinement
    {Ω Ω' X : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P₁ : Measure (Ω × X)) [IsProbabilityMeasure P₁]
    (h₁ : MeasurePreserving Prod.fst P₁ P)
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (π : Ω' → Ω) (hπ : MeasurePreserving π P' P) :
    ∃ Pc : Measure (Ω' × X),
      MeasurePreserving Prod.fst Pc P' ∧
      MeasurePreserving (fun p : Ω' × X => (π p.1, p.2)) Pc P₁ := by
  let κ : Kernel Ω X := P₁.condKernel
  haveI : IsMarkovKernel κ := inferInstance
  let Pc : Measure (Ω' × X) := P' ⊗ₘ Kernel.comap κ π hπ.measurable
  have hfst : MeasurePreserving Prod.fst Pc P' :=
    ⟨measurable_fst, by
      change Pc.fst = P'
      exact Measure.fst_compProd P' (Kernel.comap κ π hπ.measurable)⟩
  have hm : Measurable (fun p : Ω' × X => (π p.1, p.2)) :=
    hπ.measurable.comp measurable_fst |>.prodMk measurable_snd
  have hmap : Pc.map (fun p : Ω' × X => (π p.1, p.2)) = P₁ := by
    have hP₁ : P₁ = P ⊗ₘ κ := by
      rw [← P₁.disintegrate P₁.condKernel]
      simpa [κ, Measure.fst, h₁.map_eq]
    rw [hP₁]
    ext s hs
    rw [Measure.map_apply hm hs, Measure.compProd_apply (hs.preimage hm),
      Measure.compProd_apply hs]
    have he : (fun ω' => (Kernel.comap κ π hπ.measurable) ω'
        (Prod.mk ω' ⁻¹' ((fun p : Ω' × X => (π p.1, p.2)) ⁻¹' s))) =
        (fun ω => κ ω (Prod.mk ω ⁻¹' s)) ∘ π := by
      funext ω'
      simp only [Kernel.comap_apply, Function.comp_apply]
      rfl
    rw [he, ← hπ.map_eq]
    exact (lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hπ.measurable).symm
  exact ⟨Pc, hfst, ⟨hm, hmap⟩⟩

/-- Agreement with one product realization pins a measurable metric map to every
realization on every measure-preserving extension of the same base field. -/
theorem version_on_all_extensions
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U : Opens ℂ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn U)
    (P₁ : Measure (Ω × DistC)) [IsProbabilityMeasure P₁]
    (h₁ : MeasurePreserving Prod.fst P₁ P)
    (a₀ : Ω × DistC → DistC) (a : Ω × DistC → C(U, ℝ))
    (ha : IsDomainRealization U P₁ (h ∘ Prod.fst) a₀ a)
    (Φ : DistOn U → (U × U → ℝ≥0∞))
    (hΦ : ∀ᵐ p ∂P₁, Φ (h p.1) = domainMetric (ξ : ℝ) D U (a₀ p) (a p)) :
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      (π : Ω' → Ω) (hπ : MeasurePreserving π P' P)
      (b₀ : Ω' → DistC) (b : Ω' → C(U, ℝ))
      (hb : IsDomainRealization U P' (h ∘ π) b₀ b),
      ∀ᵐ p ∂P', Φ (h (π p)) = domainMetric (ξ : ℝ) D U (b₀ p) (b p) := by
  intro Ω' _ P' π hπ b₀ b hb
  haveI : IsProbabilityMeasure P' := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ
  obtain ⟨Pc, hfst, hmap⟩ := product_common_refinement P P₁ h₁ P' π hπ
  haveI : IsProbabilityMeasure Pc := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hfst
  have heq := metric_agrees_on_common_refinement ξ Q hQ D hD U P
    P₁ P' Pc Prod.fst π (fun p : Ω' × DistC => (π p.1, p.2)) Prod.fst
    h₁ hπ hmap hfst (Filter.Eventually.of_forall fun _ => rfl) h a₀ a b₀ b ha hb
  have hΦc : ∀ᵐ p ∂Pc, Φ (h (π p.1)) =
      domainMetric (ξ : ℝ) D U (a₀ (π p.1, p.2)) (a (π p.1, p.2)) := by
    have hm : ∀ᵐ p ∂Pc.map (fun p : Ω' × DistC => (π p.1, p.2)),
        Φ (h p.1) = domainMetric (ξ : ℝ) D U (a₀ p) (a p) := by
      rw [hmap.map_eq]
      exact hΦ
    exact ae_of_ae_map hmap.measurable.aemeasurable hm
  have hPc : ∀ᵐ p ∂Pc,
      Φ (h (π p.1)) = domainMetric (ξ : ℝ) D U (b₀ p.1) (b p.1) := by
    filter_upwards [hΦc, heq] with p h1 h2
    exact h1.trans h2
  exact ae_of_ae_fst hfst hPc

/-- Per-field data for the base-space form: product realizations of `h` and of `h^φ`, and the root's
all-pairs equality on the common space. -/
theorem base_data
    (ξ : Set.Ioi (0 : ℝ)) (hξ : xiCrit < (ξ : ℝ))
    (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U V : Opens ℂ) (hUc : IsConnected (U : Set ℂ)) (hVc : IsConnected (V : Set ℂ))
    (hUg : IsGreenian U) (hVg : IsGreenian V)
    (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h z : Ω → DistOn U) (f : Ω → C(U, ℝ))
    (hh : Measurable h) (hz : IsZeroBoundaryGFF U z P) (hf : Measurable f)
    (heq : ∀ᵐ ω ∂P, h ω = z ω +
      Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤) :
    ∃ (P₁ : Measure (Ω × DistC)) (a₀ : Ω × DistC → DistC) (a : Ω × DistC → C(U, ℝ)),
      MeasurePreserving Prod.fst P₁ P ∧ IsDomainRealization U P₁ (h ∘ Prod.fst) a₀ a ∧
    ∃ (P₂ : Measure ((Ω × DistC) × DistC)) (b₀ : (Ω × DistC) × DistC → DistC)
        (b : (Ω × DistC) × DistC → C(V, ℝ)),
      MeasurePreserving Prod.fst P₂ P₁ ∧
      IsDomainRealization V P₂ (fun ω => confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h ω.1.1)) b₀ b ∧
      ∀ᵐ ω ∂P₂, ∀ u v : U,
        domainMetric (ξ : ℝ) D U (a₀ ω.1) (a ω.1) (u, v) =
          domainMetric (ξ : ℝ) D V (b₀ ω) (b ω) (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) := by
  let ψ := SupercriticalConformalCovariance.Reversal.inverse_conformal hφ
  obtain ⟨P₁, a₀, a, hπ₁, ha⟩ := exists_prod_realization_of_zeroBoundary P U hUg h z f hh hz hf heq
  haveI : IsProbabilityMeasure P₁ := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ₁
  have hz₁ := isZeroBoundaryGFF_comp hπ₁ hz
  have heq₁ : ∀ᵐ ω ∂P₁, h ω.1 = z ω.1 +
      Distribution.ofFun U (Function.extend Subtype.val (f ω.1) 0) volume ⊤ :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hπ₁.map_eq]; exact heq)
  obtain ⟨hzV, hgV, heqV⟩ := gm_class_pullback Q hφ (h ∘ Prod.fst) (z ∘ Prod.fst) (f ∘ Prod.fst)
    hz₁ (hf.comp measurable_fst) heq₁
  obtain ⟨P₂, b₀, b, hπ₂, hb⟩ := exists_prod_realization_of_zeroBoundary P₁ V hVg
    (fun ω => confPullbackField Q ψ (h ω.1)) _ _
    ((SupercriticalConformalCovariance.GPull.measurable_confPullbackField Q ψ).comp (hh.comp measurable_fst))
    hzV hgV heqV
  have hcov := (gm_direction_of_root ξ hξ Q hQ D hD U V hUc hVc hUg hVg φ hφ P₁ (h ∘ Prod.fst) a₀ a ha).2
    ((Ω × DistC) × DistC) P₂ Prod.fst hπ₂ b₀ b hb
  exact ⟨P₁, a₀, a, hπ₁, ha, P₂, b₀, b, hπ₂, hb, hcov⟩

/-- The `V`-side hypotheses are redundant: `V = φ(U)` is connected and Greenian when `U` is. -/
theorem target_hyps {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
    (hUc : IsConnected (U : Set ℂ)) (hUg : IsGreenian U) :
    IsConnected (V : Set ℂ) ∧ IsGreenian V :=
  ⟨hφ.2.image_eq ▸ hUc.image φ hφ.1.continuousOn,
    SupercriticalConformalCovariance.GPull.isGreenian_of_conf
      (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) hUg⟩


/-- Gwynne–Miller Axiom IV on the original probability space. Both measurable
maps are versions of the domain metric on every realization extension. -/
theorem gm_axiomIV_on_base
    (ξ : Set.Ioi (0 : ℝ)) (hξ : xiCrit < (ξ : ℝ))
    (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U V : Opens ℂ) (hUc : IsConnected (U : Set ℂ)) (hUg : IsGreenian U)
    (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h z : Ω → DistOn U) (f : Ω → C(U, ℝ))
    (hh : Measurable h) (hz : IsZeroBoundaryGFF U z P) (hf : Measurable f)
    (heq : ∀ᵐ ω ∂P, h ω = z ω +
      Distribution.ofFun U (Function.extend Subtype.val (f ω) 0) volume ⊤) :
    ∃ ΦU : DistOn U → (U × U → ℝ≥0∞), Measurable ΦU ∧
    ∃ ΦV : DistOn V → (V × V → ℝ≥0∞), Measurable ΦV ∧
      (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        (π : Ω' → Ω) (hπ : MeasurePreserving π P' P)
        (a₀ : Ω' → DistC) (a : Ω' → C(U, ℝ))
        (ha : IsDomainRealization U P' (h ∘ π) a₀ a),
        ∀ᵐ ω ∂P', ΦU (h (π ω)) = domainMetric (ξ : ℝ) D U (a₀ ω) (a ω)) ∧
      (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        (π : Ω' → Ω) (hπ : MeasurePreserving π P' P)
        (b₀ : Ω' → DistC) (b : Ω' → C(V, ℝ))
        (hb : IsDomainRealization V P'
          ((fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h ω)) ∘ π) b₀ b),
        ∀ᵐ ω ∂P',
          ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h (π ω))) =
            domainMetric (ξ : ℝ) D V (b₀ ω) (b ω)) ∧
      (∃ (P₁ : Measure (Ω × DistC)) (a₀ : Ω × DistC → DistC)
          (a : Ω × DistC → C(U, ℝ)),
        MeasurePreserving Prod.fst P₁ P ∧
          IsDomainRealization U P₁ (h ∘ Prod.fst) a₀ a) ∧
      (∃ (PV : Measure (Ω × DistC)) (b₀ : Ω × DistC → DistC)
          (b : Ω × DistC → C(V, ℝ)),
        MeasurePreserving Prod.fst PV P ∧
          IsDomainRealization V PV
            ((fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h ω)) ∘ Prod.fst)
            b₀ b) ∧
      ∀ᵐ ω ∂P, ∀ u v : U,
        ΦU (h ω) (u, v) =
          ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (h ω))
            (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) := by
  obtain ⟨hVc, hVg⟩ := target_hyps hφ hUc hUg
  obtain ⟨P₁, a₀, a, hπ₁, ha, P₂, b₀, b, hπ₂, hb, hcov⟩ :=
    base_data ξ hξ Q hQ D hD U V hUc hVc hUg hVg φ hφ P h z f hh hz hf heq
  haveI : IsProbabilityMeasure P₁ := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ₁
  haveI : IsProbabilityMeasure P₂ := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπ₂
  let ψ := SupercriticalConformalCovariance.Reversal.inverse_conformal hφ
  let hV : Ω → DistOn V := fun ω => confPullbackField Q ψ (h ω)
  obtain ⟨hzV, hfV, heqV⟩ := gm_class_pullback Q hφ h z f hz hf heq
  obtain ⟨PV, c₀, c, hπV, hc⟩ := exists_prod_realization_of_zeroBoundary P V hVg hV
    (fun ω => SupercriticalConformalCovariance.ZBConformal.distPullback ψ (z ω)) (fun ω => gmCorrection Q hφ (f ω))
    ((SupercriticalConformalCovariance.GPull.measurable_confPullbackField Q ψ).comp hh) hzV hfV heqV
  haveI : IsProbabilityMeasure PV := SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving hπV
  obtain ⟨ΦU, hΦUm, hΦU⟩ := SupercriticalConformalCovariance.Domain.exists_measurable_domainMetric hD U ha
  obtain ⟨ΦV, hΦVm, hΦV⟩ := SupercriticalConformalCovariance.Domain.exists_measurable_domainMetric hD V hc
  refine ⟨ΦU, hΦUm, ΦV, hΦVm, ?_, ?_,
    ⟨P₁, a₀, a, hπ₁, ha⟩, ⟨PV, c₀, c, hπV, hc⟩, ?_⟩
  · exact version_on_all_extensions ξ Q hQ D hD U P h P₁ hπ₁ a₀ a ha ΦU
      (hΦU.mono fun _ e => e.symm)
  · exact version_on_all_extensions ξ Q hQ D hD V P hV PV hπV c₀ c hc ΦV
      (hΦV.mono fun _ e => e.symm)
  · have hπV₂ : MeasurePreserving (fun p : (Ω × DistC) × DistC => p.1.1) P₂ P :=
      hπ₁.comp hπ₂
    have hΦU₂ : ∀ᵐ p ∂P₂, ΦU (h p.1.1) =
        domainMetric (ξ : ℝ) D U (a₀ p.1) (a p.1) := by
      have hm : ∀ᵐ p ∂P₂.map (Prod.fst : (Ω × DistC) × DistC → Ω × DistC),
          ΦU (h p.1) = domainMetric (ξ : ℝ) D U (a₀ p) (a p) := by
        rw [hπ₂.map_eq]
        exact hΦU.mono fun _ e => e.symm
      exact ae_of_ae_map measurable_fst.aemeasurable hm
    have hΦV₂ := version_on_all_extensions ξ Q hQ D hD V P hV PV hπV c₀ c hc ΦV
      (hΦV.mono fun _ e => e.symm) P₂
      (fun p : (Ω × DistC) × DistC => p.1.1) hπV₂ b₀ b hb
    have h₂ : ∀ᵐ p ∂P₂, (fun q : Ω × DistC =>
        (fun ω : Ω => ∀ u v : U,
          ΦU (h ω) (u, v) = ΦV (hV ω)
            (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩)) q.1) p.1 := by
      filter_upwards [hΦU₂, hΦV₂, hcov] with p eU eV ec
      intro u v
      rw [eU, eV]
      exact ec u v
    exact ae_of_ae_fst hπ₁ (ae_of_ae_fst hπ₂ h₂)
/-- One pair of measurable metric maps works for a countable family of
zero-boundary fields and conformal maps, with universal versions on both sides. -/
theorem exists_countably_universal_gm_axiomIV_on_base
    (ξ : Set.Ioi (0 : ℝ)) (hξ : xiCrit < (ξ : ℝ))
    (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (U V : Opens ℂ) (hUc : IsConnected (U : Set ℂ)) (hUg : IsGreenian U)
    (ι : Type) [Countable ι]
    (φ : ι → ℂ → ℂ) (hφ : ∀ i, IsConformalBijection (φ i) U V)
    (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (h z : ∀ i, Ω i → DistOn U) (f : ∀ i, Ω i → C(U, ℝ))
    (hh : ∀ i, Measurable (h i)) (hz : ∀ i, IsZeroBoundaryGFF U (z i) (P i))
    (hf : ∀ i, Measurable (f i))
    (heq : ∀ i, ∀ᵐ ω ∂P i, h i ω = z i ω +
      Distribution.ofFun U (Function.extend Subtype.val (f i ω) 0) volume ⊤) :
    ∃ ΦU : DistOn U → (U × U → ℝ≥0∞), Measurable ΦU ∧
    ∃ ΦV : DistOn V → (V × V → ℝ≥0∞), Measurable ΦV ∧
      ∀ i,
      (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        (π : Ω' → Ω i) (hπ : MeasurePreserving π P' (P i))
        (a₀ : Ω' → DistC) (a : Ω' → C(U, ℝ))
        (ha : IsDomainRealization U P' (h i ∘ π) a₀ a),
        ∀ᵐ ω ∂P', ΦU (h i (π ω)) = domainMetric (ξ : ℝ) D U (a₀ ω) (a ω)) ∧
      (∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        (π : Ω' → Ω i) (hπ : MeasurePreserving π P' (P i))
        (b₀ : Ω' → DistC) (b : Ω' → C(V, ℝ))
        (hb : IsDomainRealization V P'
          ((fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal (hφ i)) (h i ω)) ∘ π)
          b₀ b),
        ∀ᵐ ω ∂P',
          ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal (hφ i)) (h i (π ω))) =
            domainMetric (ξ : ℝ) D V (b₀ ω) (b ω)) ∧
      (∃ (P₁ : Measure (Ω i × DistC)) (a₀ : Ω i × DistC → DistC)
          (a : Ω i × DistC → C(U, ℝ)),
        MeasurePreserving Prod.fst P₁ (P i) ∧
          IsDomainRealization U P₁ (h i ∘ Prod.fst) a₀ a) ∧
      (∃ (PV : Measure (Ω i × DistC)) (b₀ : Ω i × DistC → DistC)
          (b : Ω i × DistC → C(V, ℝ)),
        MeasurePreserving Prod.fst PV (P i) ∧
          IsDomainRealization V PV
            ((fun ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal (hφ i)) (h i ω))
              ∘ Prod.fst) b₀ b) ∧
      ∀ᵐ ω ∂P i, ∀ u v : U,
        ΦU (h i ω) (u, v) =
          ΦV (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal (hφ i)) (h i ω))
            (⟨φ i u, (hφ i).2.mapsTo u.2⟩, ⟨φ i v, (hφ i).2.mapsTo v.2⟩) := by
  choose P₁ a₀ a hπ₁ ha P₂ b₀ b hπ₂ hb hcov using fun i =>
    base_data ξ hξ Q hQ D hD U V hUc (target_hyps (hφ i) hUc hUg).1
      hUg (target_hyps (hφ i) hUc hUg).2 (φ i) (hφ i)
      (P i) (h i) (z i) (f i) (hh i) (hz i) (hf i) (heq i)
  haveI : ∀ i, IsProbabilityMeasure (P₁ i) :=
    fun i => SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving (hπ₁ i)
  haveI : ∀ i, IsProbabilityMeasure (P₂ i) :=
    fun i => SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving (hπ₂ i)
  let hV : ∀ i, Ω i → DistOn V :=
    fun i ω => confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal (hφ i)) (h i ω)
  have hexV : ∀ i, ∃ (PV : Measure (Ω i × DistC))
      (c₀ : Ω i × DistC → DistC) (c : Ω i × DistC → C(V, ℝ)),
      MeasurePreserving Prod.fst PV (P i) ∧
        IsDomainRealization V PV (hV i ∘ Prod.fst) c₀ c := by
    intro i
    obtain ⟨hzV, hfV, heqV⟩ :=
      gm_class_pullback Q (hφ i) (h i) (z i) (f i) (hz i) (hf i) (heq i)
    exact exists_prod_realization_of_zeroBoundary (P i) V
      (target_hyps (hφ i) hUc hUg).2 (hV i)
      (fun ω => SupercriticalConformalCovariance.ZBConformal.distPullback (SupercriticalConformalCovariance.Reversal.inverse_conformal (hφ i)) (z i ω))
      (fun ω => gmCorrection Q (hφ i) (f i ω))
      ((SupercriticalConformalCovariance.GPull.measurable_confPullbackField Q
        (SupercriticalConformalCovariance.Reversal.inverse_conformal (hφ i))).comp (hh i)) hzV hfV heqV
  choose PV c₀ c hπV hc using hexV
  haveI : ∀ i, IsProbabilityMeasure (PV i) :=
    fun i => SupercriticalConformalCovariance.Root.isProbabilityMeasure_of_measurePreserving (hπV i)
  obtain ⟨ΦU, hΦUm, hΦU⟩ := exists_countably_universal_domain_metric
    ξ Q D hD U ι (fun i => Ω i × DistC) P₁ (fun i => h i ∘ Prod.fst) a₀ a ha
  obtain ⟨ΦV, hΦVm, hΦV⟩ := exists_countably_universal_domain_metric
    ξ Q D hD V ι (fun i => Ω i × DistC) PV (fun i => hV i ∘ Prod.fst) c₀ c hc
  refine ⟨ΦU, hΦUm, ΦV, hΦVm, fun i => ?_⟩
  refine ⟨?_, ?_, ⟨P₁ i, a₀ i, a i, hπ₁ i, ha i⟩,
    ⟨PV i, c₀ i, c i, hπV i, hc i⟩, ?_⟩
  · exact version_on_all_extensions ξ Q hQ D hD U (P i) (h i) (P₁ i)
      (hπ₁ i) (a₀ i) (a i) (ha i) ΦU (hΦU i)
  · exact version_on_all_extensions ξ Q hQ D hD V (P i) (hV i) (PV i)
      (hπV i) (c₀ i) (c i) (hc i) ΦV (hΦV i)
  · have hπV₂ : MeasurePreserving (fun p : (Ω i × DistC) × DistC => p.1.1)
        (P₂ i) (P i) := (hπ₁ i).comp (hπ₂ i)
    have hΦU₂ : ∀ᵐ p ∂P₂ i, ΦU (h i p.1.1) =
        domainMetric (ξ : ℝ) D U (a₀ i p.1) (a i p.1) := by
      have hm : ∀ᵐ p ∂(P₂ i).map (Prod.fst : (Ω i × DistC) × DistC → Ω i × DistC),
          ΦU (h i p.1) = domainMetric (ξ : ℝ) D U (a₀ i p) (a i p) := by
        rw [(hπ₂ i).map_eq]
        exact hΦU i
      exact ae_of_ae_map measurable_fst.aemeasurable hm
    have hΦV₂ := version_on_all_extensions ξ Q hQ D hD V (P i) (hV i) (PV i)
      (hπV i) (c₀ i) (c i) (hc i) ΦV (hΦV i) (P₂ i)
      (fun p : (Ω i × DistC) × DistC => p.1.1) hπV₂ (b₀ i) (b i) (hb i)
    have h₂ : ∀ᵐ p ∂P₂ i, (fun q : Ω i × DistC =>
        (fun ω : Ω i => ∀ u v : U,
          ΦU (h i ω) (u, v) = ΦV (hV i ω)
            (⟨φ i u, (hφ i).2.mapsTo u.2⟩, ⟨φ i v, (hφ i).2.mapsTo v.2⟩)) q.1) p.1 := by
      filter_upwards [hΦU₂, hΦV₂, hcov i] with p eU eV ec
      intro u v
      rw [eU, eV]
      exact ec u v
    exact ae_of_ae_fst (hπ₁ i) (ae_of_ae_fst (hπ₂ i) h₂)

end SupercriticalConformalCovariance.GMForm
