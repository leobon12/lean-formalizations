/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12CanonicalCond

/-!
# Canonical coupling laws are realized by optional hull couplings (S4, sufficiency)

Packet PROVE-PARAM12C. For a law `π` on `XCode × 𝒟'(ℍ)` with `CanonCond κ θ π`:

* `setIntegral_eq_of_generate` (Dynkin): the countably many identities on the generating π-system of the observations
  extend to every event of the code filtration at the dyadic time;
* `CanonCond.sampled`, `CanonCond.projIndep`: the dyadic sampling identities at the rational test functions, and the
  dyadic projection-independence identities at every Dirichlet direction (through the resampling characterization
  `Coupling.isProjIndepMeasure_resample`);
* `isSampledCoupling_of_ratComb`: at a protected stop, the sampling identities at the rational test functions give
  `IsSampledCoupling` (the protected kernel `Coupling.exists_protectedKernel` and `ext_of_integral_cexp_ratComb`);
* `CanonCond.exists_isOptionalHullCoupling`: an optional hull coupling of the word on `ULift (XCode) × 𝒟'(ℍ)` whose
  joint law of field and killed driving code is `π.map canonF`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal Classical

universe u

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Coupling Ito Staged LQGMetric Restart GFF

variable {nL nR : ℕ}

/-! ### Set-integral forms and the Dynkin extension -/

section Dynkin

theorem integral_ite_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure (X × Y)}
    {S : Set X} (hS : MeasurableSet S) (g : X × Y → ℂ) :
    ∫ p, (if p.1 ∈ S then g p else 0) ∂μ = ∫ p in Prod.fst ⁻¹' S, g p ∂μ := by
  rw [← integral_indicator (measurable_fst hS)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  by_cases hp : p.1 ∈ S
  · simp [hp]
  · simp [hp]

/-- **Dynkin extension of set-integral identities** over the events `G⁻¹ A ∩ E`, `A` measurable, from a generating
π-system and `A = univ`. -/
theorem setIntegral_eq_of_generate {Y Ω' : Type*} [mY : MeasurableSpace Y] [MeasurableSpace Ω']
    {μ : Measure Ω'} {G : Ω' → Y} (hG : Measurable G) {E : Set Ω'} (hE : MeasurableSet E)
    {g₁ g₂ : Ω' → ℂ} (hg₁ : Integrable g₁ μ) (hg₂ : Integrable g₂ μ)
    {Cp : Set (Set Y)} (hgen : mY = MeasurableSpace.generateFrom Cp) (hpi : IsPiSystem Cp)
    (h : ∀ A ∈ insert univ Cp, ∫ x in G ⁻¹' A ∩ E, g₁ x ∂μ = ∫ x in G ⁻¹' A ∩ E, g₂ x ∂μ)
    {A : Set Y} (hA : MeasurableSet A) :
    ∫ x in G ⁻¹' A ∩ E, g₁ x ∂μ = ∫ x in G ⁻¹' A ∩ E, g₂ x ∂μ := by
  have huniv := h univ (mem_insert _ _)
  refine MeasurableSpace.induction_on_inter (C := fun A _ =>
    ∫ x in G ⁻¹' A ∩ E, g₁ x ∂μ = ∫ x in G ⁻¹' A ∩ E, g₂ x ∂μ) hgen hpi ?_ ?_ ?_ ?_ A hA
  · simp
  · intro t ht; exact h t (mem_insert_of_mem _ ht)
  · intro t htm ht
    have hsplit : ∀ g : Ω' → ℂ, Integrable g μ →
        ∫ x in G ⁻¹' univ ∩ E, g x ∂μ = (∫ x in G ⁻¹' t ∩ E, g x ∂μ) + ∫ x in G ⁻¹' tᶜ ∩ E, g x ∂μ := by
      intro g hg
      have e : G ⁻¹' univ ∩ E = (G ⁻¹' t ∩ E) ∪ (G ⁻¹' tᶜ ∩ E) := by
        ext x; by_cases hx : G x ∈ t <;> simp [hx]
      rw [e, setIntegral_union _ ((hG htm.compl).inter hE) hg.integrableOn hg.integrableOn]
      exact Set.disjoint_left.2 fun x h1 h2 => h2.1 h1.1
    have h1 := hsplit g₁ hg₁
    have h2 := hsplit g₂ hg₂
    rw [huniv, ht] at h1
    rw [h1] at h2
    exact add_left_cancel h2
  · intro f hfd hfm hf
    have e : G ⁻¹' (⋃ i, f i) ∩ E = ⋃ i, (G ⁻¹' f i ∩ E) := by
      ext x; simp only [preimage_iUnion, mem_inter_iff, mem_iUnion]; tauto
    have hd : Pairwise (Function.onFun Disjoint fun i => G ⁻¹' f i ∩ E) := fun i j hij =>
      Set.disjoint_left.2 fun x h1 h2 => Set.disjoint_left.1 (hfd hij) h1.1 h2.1
    have hm : ∀ i, MeasurableSet (G ⁻¹' f i ∩ E) := fun i => (hG (hfm i)).inter hE
    rw [e, integral_iUnion hm hd hg₁.integrableOn, integral_iUnion hm hd hg₂.integrableOn]
    exact tsum_congr hf

end Dynkin

/-! ### Consequences of the canonical conditions on the code space -/

section Code

variable {κ : ℝ} {θ : WordData nL nR} {π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)}
  [IsProbabilityMeasure π]

omit [IsProbabilityMeasure π] in
theorem CanonCond.ae_mem (hC : CanonCond κ θ π) :
    ∀ᵐ p ∂π, p.1 ∈ CRel κ θ.1.1 θ.1.2 θ.2.1 θ.2.2 :=
  ae_of_ae_map measurable_fst.aemeasurable hC.1.ae_mem

theorem fst_preimage_condEv (F : RatBallSet) (q : ℝ≥0) (A : Set (ObsY nL nR)) :
    (Prod.fst ⁻¹' condEv F q A : Set (XCode nL nR × DistOn upperHalfPlaneOpens)) =
      (fun p : XCode nL nR × DistOn upperHalfPlaneOpens => codeObs q p.1) ⁻¹' A ∩
        Prod.fst ⁻¹' codeAlive (ballsK F.1) q := rfl

/-- The alive-restricted protected characteristic function on the canonical space. -/
def cfAlive (κ : ℝ) (θ : WordData nL nR) (K : Set ℂ) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    (p : XCode nL nR × DistOn upperHalfPlaneOpens) : ℂ :=
  if (θ, p.1).2 ∈ codeAlive K q then cfAt κ cwP (uP κ) ψ 1 (fun _ => q) (θ, p.1) else 0

theorem measurable_cfAlive (κ : ℝ) (θ : WordData nL nR) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (ψ : TestOn upperHalfPlaneOpens) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) (q : ℝ≥0) :
    Measurable (cfAlive (nL := nL) (nR := nR) κ θ K ψ q) :=
  (measurable_cfAt_indicator κ hK hKH ψ hψK q).comp (measurable_const.prodMk measurable_fst)

theorem CanonCond.integrable_cfAlive (hC : CanonCond κ θ π) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (ψ : TestOn upperHalfPlaneOpens) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) (q : ℝ≥0) :
    Integrable (cfAlive κ θ K ψ q) π := by
  refine Integrable.of_bound (measurable_cfAlive κ θ hK hKH ψ hψK q).aestronglyMeasurable 1 ?_
  filter_upwards [hC.ae_mem] with p hp
  unfold cfAlive
  by_cases ha : (θ, p.1).2 ∈ codeAlive K q
  · rw [ite_eq_left_iff.2 fun h => absurd ha h]
    obtain ⟨hg, hq, hal⟩ := ha
    exact norm_cfAt_le_one (W := cwP) (uP κ) 1 ψ (r := fun _ => q) (ω := (θ, p.1))
      (continuousOn_rpath hg.continuousOn_w hq) hp.1.2.2.1 fun z hz => hal z (hψK hz)
  · rw [ite_eq_right_iff.2 fun h => absurd h ha, norm_zero]; exact zero_le_one

theorem integrable_cexp_snd (ψ : TestOn upperHalfPlaneOpens) :
    Integrable (fun p : XCode nL nR × DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (p.2 ψ : ℂ))) π :=
  Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply ψ).comp measurable_snd)).aestronglyMeasurable
    1 (Eventually.of_forall fun _ => (Complex.norm_exp_I_mul_ofReal _).le)

/-- **The dyadic sampling identities at every observation event.** -/
theorem CanonCond.sampled (hC : CanonCond κ θ π) (F : RatBallSet) (n k : ℕ) (j : RatComb)
    {A : Set (ObsY nL nR)} (hA : MeasurableSet A) :
    ∫ p in Prod.fst ⁻¹' condEv F (dyad n k) A, Complex.exp (Complex.I * (p.2 (sampTest F j) : ℂ)) ∂π =
      ∫ p in Prod.fst ⁻¹' condEv F (dyad n k) A, cfAlive κ θ (ballsK F.1) (sampTest F j) (dyad n k) p ∂π := by
  have hK := isCompact_ballsK F.1
  have hψK := tsupport_sampTest_subset F j
  have hE : MeasurableSet (Prod.fst ⁻¹' codeAlive (ballsK F.1) (dyad n k) :
      Set (XCode nL nR × DistOn upperHalfPlaneOpens)) :=
    measurable_fst (measurableSet_codeAlive hK F.2 _)
  have key : ∀ A' ∈ insert univ (obsPi nL nR),
      ∫ p in Prod.fst ⁻¹' condEv F (dyad n k) A', Complex.exp (Complex.I * (p.2 (sampTest F j) : ℂ)) ∂π =
        ∫ p in Prod.fst ⁻¹' condEv F (dyad n k) A', cfAlive κ θ (ballsK F.1) (sampTest F j) (dyad n k) p ∂π := by
    intro A' hA'
    have h := hC.2.2.1 F n k A' hA' j
    rw [sampL, sampR, integral_ite_fst (measurableSet_condEv F _ (measurableSet_obsPi hA')),
      integral_ite_fst (measurableSet_condEv F _ (measurableSet_obsPi hA'))] at h
    rw [h]
    refine setIntegral_congr_fun (measurable_fst (measurableSet_condEv F _ (measurableSet_obsPi hA')))
      fun p hp => ?_
    simp only [cfAlive, show (θ, p.1).2 ∈ codeAlive (ballsK F.1) (dyad n k) from hp.2, ↓reduceIte]
  simp only [fst_preimage_condEv] at key ⊢
  exact setIntegral_eq_of_generate ((measurable_codeObs _).comp measurable_fst) hE (integrable_cexp_snd _)
    (hC.integrable_cfAlive hK F.2 _ hψK _) obsPi_spec.2.2 obsPi_spec.2.1 key hA

/-- **Projection independence of the restricted field laws at every observation event.** -/
theorem CanonCond.projIndep (hC : CanonCond κ θ π) (F : RatBallSet) (n k : ℕ) {A : Set (ObsY nL nR)}
    (hA : MeasurableSet A) :
    IsProjIndepMeasure (ballsOpens F) ((π.restrict (Prod.fst ⁻¹' condEv F (dyad n k) A)).map Prod.snd) := by
  have hK := isCompact_ballsK F.1
  obtain ⟨hGm, hGd⟩ := projMap_spec F
  set G := projMap F
  set c : DistOn upperHalfPlaneOpens := meanH (wordExt κ θ) with hc
  set S : Set (XCode nL nR × DistOn upperHalfPlaneOpens) := Prod.fst ⁻¹' condEv F (dyad n k) A with hS
  have hSm : MeasurableSet S := measurable_fst (measurableSet_condEv F _ hA)
  set m := (π.restrict S).map Prod.snd with hm
  have hE : MeasurableSet (Prod.fst ⁻¹' codeAlive (ballsK F.1) (dyad n k) :
      Set (XCode nL nR × DistOn upperHalfPlaneOpens)) :=
    measurable_fst (measurableSet_codeAlive hK F.2 _)
  have hu : Measurable fun p : XCode nL nR × DistOn upperHalfPlaneOpens => p.2 - c :=
    (measurable_sub_distOnConst c).comp measurable_snd
  -- the identities at every rational test function
  have hj : ∀ j : RatComb, ∫ z, Complex.exp (Complex.I * (z (ratComb upperHalfPlaneOpens j) : ℂ))
      ∂resample G c m = ∫ x, Complex.exp (Complex.I * (x (ratComb upperHalfPlaneOpens j) : ℂ)) ∂m := by
    intro j
    set φ := ratComb upperHalfPlaneOpens j
    set Z := projConst F j with hZ
    have hb1 : Measurable fun p : XCode nL nR × DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * ((p.2 φ - G (p.2 - c) φ : ℝ) : ℂ)) :=
      GFF.measurable_exp_I_mul (((measurable_distOn_apply φ).comp measurable_snd).sub
        ((measurable_distOn_apply φ).comp (hGm.comp hu)))
    have hg₁ : Integrable (fun p : XCode nL nR × DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * ((p.2 φ - G (p.2 - c) φ : ℝ) : ℂ)) * Z) π :=
      (Integrable.of_bound hb1.aestronglyMeasurable 1
        (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)).mul_const Z
    have key : ∀ A' ∈ insert univ (obsPi nL nR),
        ∫ p in (fun p : XCode nL nR × DistOn upperHalfPlaneOpens => codeObs (dyad n k) p.1) ⁻¹' A' ∩
          Prod.fst ⁻¹' codeAlive (ballsK F.1) (dyad n k),
            Complex.exp (Complex.I * ((p.2 φ - G (p.2 - c) φ : ℝ) : ℂ)) * Z ∂π =
        ∫ p in (fun p : XCode nL nR × DistOn upperHalfPlaneOpens => codeObs (dyad n k) p.1) ⁻¹' A' ∩
          Prod.fst ⁻¹' codeAlive (ballsK F.1) (dyad n k), Complex.exp (Complex.I * (p.2 φ : ℂ)) ∂π := by
      intro A' hA'
      have h := hC.2.2.2 F n k A' hA' j
      rw [projL, projR, integral_ite_fst (measurableSet_condEv F _ (measurableSet_obsPi hA')),
        integral_ite_fst (measurableSet_condEv F _ (measurableSet_obsPi hA'))] at h
      rw [← fst_preimage_condEv, integral_mul_const]
      exact h
    have h := setIntegral_eq_of_generate ((measurable_codeObs (dyad n k)).comp measurable_fst) hE hg₁
      (integrable_cexp_snd φ) obsPi_spec.2.2 obsPi_spec.2.1 key hA
    have h' : ∫ p in S, Complex.exp (Complex.I * ((p.2 φ - G (p.2 - c) φ : ℝ) : ℂ)) * Z ∂π =
        ∫ p in S, Complex.exp (Complex.I * (p.2 φ : ℂ)) ∂π := h
    have hf1 : Measurable fun x : DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * ((x φ - G (x - c) φ : ℝ) : ℂ)) :=
      GFF.measurable_exp_I_mul ((measurable_distOn_apply φ).sub
        ((measurable_distOn_apply φ).comp (hGm.comp (measurable_sub_distOnConst c))))
    have hf2 : Measurable fun x : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (x φ : ℂ)) :=
      GFF.measurable_exp_I_mul (measurable_distOn_apply φ)
    have e2 : ∫ x, Complex.exp (Complex.I * ((x φ - G (x - c) φ : ℝ) : ℂ)) ∂m =
        ∫ p in S, Complex.exp (Complex.I * ((p.2 φ - G (p.2 - c) φ : ℝ) : ℂ)) ∂π := by
      rw [hm, integral_map measurable_snd.aemeasurable hf1.aestronglyMeasurable]
    have e3 : ∫ x, Complex.exp (Complex.I * (x φ : ℂ)) ∂m = ∫ p in S, Complex.exp (Complex.I * (p.2 φ : ℂ)) ∂π := by
      rw [hm, integral_map measurable_snd.aemeasurable hf2.aestronglyMeasurable]
    rw [integral_cexp_resample hGm c m φ, e2, e3, ← integral_mul_const]
    exact h'
  have heq : resample G c m = m := ext_of_integral_cexp_ratComb hj
  have hac : m ≪ fieldLaw0 (wordExt κ θ) := by
    refine Measure.absolutelyContinuous_of_le ?_
    have h2 : π.map Prod.snd = fieldLaw0 (wordExt κ θ) := hC.2.1
    rw [hm, ← h2]
    exact Measure.map_mono Measure.restrict_le_self measurable_snd
  have hharm : InnerProductSpace.HarmonicOnNhd (wordExt κ θ) H :=
    (isBoundedHarmonicExtension_wordExt κ θ.1.1 θ.1.2 θ.2.1 θ.2.2).1
  rw [← heq]
  exact isProjIndepMeasure_resample hGm hGd (ballsOpens_subset_H F) hharm hac

end Code

/-! ### Sampling at a stop from the rational test functions -/

section Stop

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ}
  {ζ : Ω₀ → ℝ≥0∞}

/-- **Sampling at a protected stop from the rational test functions** (the protected kernel at the stop and the
uniqueness of laws on `𝒟'(V)` from the rational combinations of the generating family). -/
theorem isSampledCoupling_of_ratComb [IsProbabilityMeasure P₀]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ) (hκ : 0 < κ)
    (u : Ω₀ → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {μ : Measure (Ω₀ × DistOn upperHalfPlaneOpens)} [IsProbabilityMeasure μ]
    (V : TopologicalSpace.Opens ℂ) (hVH : (V : Set ℂ) ⊆ H)
    {s : Ω₀ → ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    (hsV : ∀ᵐ ω ∂P₀, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (V : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω)))
    (hj : ∀ j : RatComb, ∀ A₀ : Set Ω₀, MeasurableSet[hs.measurableSpace] A₀ →
      ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 (toTestH V (ratComb V j)) : ℂ)) ∂μ =
        ∫ ω in A₀, cfAt κ W u (toTestH V (ratComb V j)) 1 s ω ∂P₀) :
    IsSampledCoupling κ W u P₀ V hs μ := by
  obtain ⟨Q, hQ, hQcf⟩ := exists_protectedKernel hE hκ u hu hs hVH hsV
  intro ψ hψ A₀ hA₀
  have hA₀m : MeasurableSet A₀ := hs.measurableSpace_le _ hA₀
  set m1 : Measure (DistOn V) := (μ.restrict (Prod.fst ⁻¹' A₀)).map (fun p => restrictDist V p.2) with hm1
  set m2 : Measure (DistOn V) := secMeas P₀ A₀ Q with hm2
  have hr : Measurable fun p : Ω₀ × DistOn upperHalfPlaneOpens => restrictDist V p.2 :=
    (measurable_restrictDist V).comp measurable_snd
  have hcf1 : ∀ ψ' : TestOn V, ∫ g, Complex.exp (Complex.I * (g ψ' : ℂ)) ∂m1 =
      ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 (toTestH V ψ') : ℂ)) ∂μ := fun ψ' => by
    rw [hm1, integral_map hr.aemeasurable (GFF.measurable_exp_I_mul (measurable_distOn_apply ψ')).aestronglyMeasurable]
    rfl
  have hcf2 : ∀ ψ' : TestOn V, ∫ g, Complex.exp (Complex.I * (g ψ' : ℂ)) ∂m2 =
      ∫ ω in A₀, cfAt κ W u (toTestH V ψ') 1 s ω ∂P₀ := fun ψ' => by
    rw [hm2, integral_secMeas (GFF.measurable_exp_I_mul (measurable_distOn_apply ψ'))
      fun x => (Complex.norm_exp_I_mul_ofReal _).le]
    refine setIntegral_congr_ae hA₀m ?_
    filter_upwards [hQcf] with ω hω _
    rw [hω ψ', coe_toTestH hVH]
  have : IsFiniteMeasure m1 := by rw [hm1]; infer_instance
  have heq : m1 = m2 := ext_of_integral_cexp_ratComb fun j => by rw [hcf1, hcf2]; exact hj j A₀ hA₀
  have hψV : tsupport ψ ⊆ V := hψ
  set ψ' : TestOn V := testRestrict ψ hψV
  have hψ' : toTestH V ψ' = ψ := testIncl_testRestrict hVH ψ hψV
  have h := hcf1 ψ'
  rw [heq, hcf2 ψ', hψ'] at h
  exact h.symm

end Stop

/-! ### The canonical coupling lifted to `ULift (XCode)` -/

section Lift

/-- The code law lifted to `ULift (XCode)`. -/
def liftP (π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)) : Measure (ULift.{u} (XCode nL nR)) :=
  (π.map Prod.fst).map ULift.up

/-- The coupling lifted to `ULift (XCode) × 𝒟'(ℍ)`. -/
def liftμ (π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)) :
    Measure (ULift.{u} (XCode nL nR) × DistOn upperHalfPlaneOpens) :=
  π.map fun p => (ULift.up p.1, p.2)

/-- The lifted driver, marks, lifetime. -/
def Wl (t : ℝ≥0) (ω : ULift.{u} (XCode nL nR)) : ℝ := cw ω.down t
/-- The lifted harmonic extension of the state. -/
def ul (κ : ℝ) (θ : WordData nL nR) (ω : ULift.{u} (XCode nL nR)) (t : ℝ≥0) : ℂ → ℝ := uP κ (θ, ω.down) t
/-- The lifted alive events. -/
def El (K : Set ℂ) (q : ℝ≥0) : Set (ULift.{u} (XCode nL nR)) := ULift.down ⁻¹' codeAlive K q

theorem measurable_liftUp : Measurable fun p : XCode nL nR × DistOn upperHalfPlaneOpens =>
    ((ULift.up.{u} p.1 : ULift.{u} (XCode nL nR)), p.2) :=
  (measurable_up.comp measurable_fst).prodMk measurable_snd

variable {π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)}

theorem liftμ_map_fst : (liftμ.{u} π).map Prod.fst = liftP.{u} π := by
  rw [liftμ, liftP, Measure.map_map measurable_fst measurable_liftUp,
    Measure.map_map measurable_up measurable_fst]
  rfl

theorem liftμ_map_snd : (liftμ.{u} π).map Prod.snd = π.map Prod.snd := by
  rw [liftμ, Measure.map_map measurable_snd measurable_liftUp]
  rfl

theorem liftP_map_down : (liftP.{u} π).map ULift.down = π.map Prod.fst := by
  rw [liftP, Measure.map_map measurable_down measurable_up]
  exact Measure.map_id

theorem cfAt_lift (κ : ℝ) (θ : WordData nL nR) (ψ : ℂ → ℝ) (r : ULift.{u} (XCode nL nR) → ℝ≥0)
    (ω : ULift.{u} (XCode nL nR)) :
    cfAt κ Wl (ul κ θ) ψ 1 r ω = cfAt κ cwP (uP κ) ψ 1 (fun _ => r ω) (θ, ω.down) := rfl

theorem measurable_cfAt_lift (κ : ℝ) (θ : WordData nL nR) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (ψ : TestOn upperHalfPlaneOpens) (hψK : tsupport (ψ : ℂ → ℝ) ⊆ K) (q : ℝ≥0) :
    Measurable ((El.{u} K q).indicator fun ω => cfAt κ Wl (ul κ θ) ψ 1 (fun _ => q) ω) := by
  have h := (measurable_cfAt_indicator (nL := nL) (nR := nR) κ hK hKH ψ hψK q).comp
    (measurable_const.prodMk measurable_down : Measurable fun ω : ULift.{u} (XCode nL nR) => (θ, ω.down))
  convert h using 1
  funext ω
  simp only [Function.comp_apply, El, indicator, mem_preimage, cfAt_lift]

theorem measurableSet_El {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (q : ℝ≥0) :
    MeasurableSet (El.{u} (nL := nL) (nR := nR) K q) :=
  measurable_down (measurableSet_codeAlive hK hKH q)

theorem ae_mem_El_iff [IsProbabilityMeasure π] {κ : ℝ} {θ : WordData nL nR} (hC : CanonCond κ θ π)
    (K : Set ℂ) :
    ∀ᵐ ω ∂liftP.{u} π, ∀ q, ω ∈ El.{u} K q ↔ ω ∈ aliveEv Wl (fun ω => cζ ω.down) K q := by
  have h : ∀ᵐ ω ∂liftP.{u} π, ω.down ∈ CRel κ θ.1.1 θ.1.2 θ.2.1 θ.2.2 := by
    rw [liftP]
    exact ae_map_iff measurable_up.aemeasurable (measurable_down (measurableSet_cRel _ _ _ _ _)) |>.2
      hC.1.ae_mem
  filter_upwards [h] with ω hω q
  exact ⟨fun h' => h'.2, fun h' => ⟨hω.1.1, h'⟩⟩

theorem measurableEmbedding_up : MeasurableEmbedding (ULift.up.{u} : XCode nL nR → ULift.{u} (XCode nL nR)) :=
  (MeasurableEquiv.ulift.{0, u} (α := XCode nL nR)).symm.measurableEmbedding

theorem measurableEmbedding_liftUp : MeasurableEmbedding fun p : XCode nL nR × DistOn upperHalfPlaneOpens =>
    ((ULift.up.{u} p.1 : ULift.{u} (XCode nL nR)), p.2) :=
  ((MeasurableEquiv.ulift.{0, u} (α := XCode nL nR)).symm.prodCongr
    (MeasurableEquiv.refl (DistOn upperHalfPlaneOpens))).measurableEmbedding

/-- The events of the lifted code filtration are lifted observation events. -/
theorem exists_obs_of_measurableSet_lift {q : ℝ≥0} {A : Set (ULift.{u} (XCode nL nR))}
    (hA : MeasurableSet[(Coupling.filtrationComap (codeFilt (nL := nL) (nR := nR)) measurable_down) q] A) :
    ∃ A' : Set (ObsY nL nR), MeasurableSet A' ∧ A = ULift.down ⁻¹' (codeObs q ⁻¹' A') := by
  obtain ⟨s, hs, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  obtain ⟨A', hA', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
  exact ⟨A', hA', rfl⟩

variable [IsProbabilityMeasure π] {κ : ℝ} {θ : WordData nL nR}

omit [IsProbabilityMeasure π] in
theorem setIntegral_liftμ (F : RatBallSet) (q : ℝ≥0) (A' : Set (ObsY nL nR)) (g : DistOn upperHalfPlaneOpens → ℂ) :
    ∫ p in Prod.fst ⁻¹' (ULift.down ⁻¹' (codeObs q ⁻¹' A') ∩ El.{u} (ballsK F.1) q), g p.2 ∂liftμ.{u} π =
      ∫ p in Prod.fst ⁻¹' condEv F q A', g p.2 ∂π := by
  rw [liftμ, measurableEmbedding_liftUp.setIntegral_map]
  rfl

/-- **The dyadic sampling identities on the lifted space.** -/
theorem CanonCond.dyadic_sampled_lift (hC : CanonCond κ θ π) (F : RatBallSet) (j : RatComb) (n k : ℕ)
    {A : Set (ULift.{u} (XCode nL nR))}
    (hA : MeasurableSet[(Coupling.filtrationComap (codeFilt (nL := nL) (nR := nR)) measurable_down) (dyad n k)] A) :
    ∫ p in Prod.fst ⁻¹' (A ∩ El.{u} (ballsK F.1) (dyad n k)),
        Complex.exp (Complex.I * (p.2 (sampTest F j) : ℂ)) ∂liftμ.{u} π =
      ∫ ω in A ∩ El.{u} (ballsK F.1) (dyad n k),
        cfAt κ Wl (ul κ θ) (sampTest F j) 1 (fun _ => dyad n k) ω ∂liftP.{u} π := by
  obtain ⟨A', hA', rfl⟩ := exists_obs_of_measurableSet_lift hA
  rw [setIntegral_liftμ F _ A' fun x => Complex.exp (Complex.I * (x (sampTest F j) : ℂ)), hC.sampled F n k j hA',
    liftP, measurableEmbedding_up.setIntegral_map]
  have hcm : MeasurableSet (condEv (nL := nL) (nR := nR) F (dyad n k) A') := measurableSet_condEv F _ hA'
  have hf' := (measurable_cfAt_indicator (nL := nL) (nR := nR) κ (isCompact_ballsK F.1) F.2 (sampTest F j)
    (tsupport_sampTest_subset F j) (dyad n k)).comp
    (measurable_const.prodMk measurable_id : Measurable fun x : XCode nL nR => (θ, x))
  have e : ∫ x in ULift.up ⁻¹' (ULift.down ⁻¹' (codeObs (dyad n k) ⁻¹' A') ∩ El.{u} (ballsK F.1) (dyad n k)),
      cfAt κ Wl (ul κ θ) (sampTest F j) 1 (fun _ => dyad n k) (ULift.up x) ∂(π.map Prod.fst) =
      ∫ x in condEv F (dyad n k) A', ((fun p : WordData nL nR × XCode nL nR =>
        if p.2 ∈ codeAlive (ballsK F.1) (dyad n k) then cfAt κ cwP (uP κ) (sampTest F j) 1 (fun _ => dyad n k) p
        else 0) ∘ fun a => (θ, a)) x ∂(π.map Prod.fst) := by
    refine setIntegral_congr_fun hcm fun x hx => ?_
    have hx2 : x ∈ codeAlive (ballsK F.1) (dyad n k) := hx.2
    simp only [Function.comp_apply, hx2, ↓reduceIte]
    rfl
  rw [e, setIntegral_map hcm hf'.aestronglyMeasurable measurable_fst.aemeasurable]
  rfl

/-- **The dyadic projection-independence identities on the lifted space.** -/
theorem CanonCond.dyadic_proj_lift (hC : CanonCond κ θ π) (F : RatBallSet) (n k : ℕ)
    (f : LQGMetric.MarkovZB.zsSub (ballsOpens F : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens)
    {A : Set (ULift.{u} (XCode nL nR))}
    (hA : MeasurableSet[(Coupling.filtrationComap (codeFilt (nL := nL) (nR := nR)) measurable_down) (dyad n k)] A) :
    ∫ p in Prod.fst ⁻¹' (A ∩ El.{u} (ballsK F.1) (dyad n k)),
        Complex.exp (Complex.I * (p.2 (LocalSets.lapTest (ballsOpens F) f + Ξ) : ℂ)) ∂liftμ.{u} π =
      projFactor (ballsOpens F) f Ξ * ∫ p in Prod.fst ⁻¹' (A ∩ El.{u} (ballsK F.1) (dyad n k)),
        Complex.exp (Complex.I * (p.2 Ξ : ℂ)) ∂liftμ.{u} π := by
  obtain ⟨A', hA', rfl⟩ := exists_obs_of_measurableSet_lift hA
  rw [setIntegral_liftμ F _ A' fun x => Complex.exp (Complex.I * (x (LocalSets.lapTest (ballsOpens F) f + Ξ) : ℂ)),
    setIntegral_liftμ F _ A' fun x => Complex.exp (Complex.I * (x Ξ : ℂ))]
  have h := hC.projIndep F n k hA' f Ξ
  rw [integral_map measurable_snd.aemeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable] at h
  exact h

end Lift


/-! ### The family constraints of the lifted canonical coupling -/

section Family

variable {π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)} [IsProbabilityMeasure π] {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The lifted code filtration. -/
abbrev filtL (nL nR : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ULift.{u} (XCode nL nR))) :=
  Coupling.filtrationComap (codeFilt (nL := nL) (nR := nR)) measurable_down

theorem CanonCond.isIntegratedSLEEvolution_lift (hC : CanonCond κ ((xL, xR), (ρL, ρR)) π) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR (liftP.{u} π) (filtL.{u} nL nR) Wl
      (fun i t ω => cvL ω.down i t) (fun j t ω => cvR ω.down j t) (fun t ω => cb ω.down t)
      (fun ω => cζ ω.down) :=
  IsIntegratedSLEEvolution.comap measurable_down liftP_map_down (isIntegratedSLEEvolution_canon hC.1)

theorem isBoundedHarmonicExtension_ul (κ : ℝ) (θ : WordData nL nR) (ω : ULift.{u} (XCode nL nR)) (t : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ θ.2.1 θ.2.2 (fun i => cvL ω.down i t - Wl t ω) (fun j => cvR ω.down j t - Wl t ω))
      (forceJumpSet (fun i => cvL ω.down i t - Wl t ω) (fun j => cvR ω.down j t - Wl t ω)) (ul κ θ ω t) :=
  isBoundedHarmonicExtension_uP κ (θ, ω.down) t

/-- **The lifted canonical coupling is sampled at every protected stop of a rational ball set.** -/
theorem CanonCond.isSampledCoupling_lift (hκ : 0 < κ) (hC : CanonCond κ ((xL, xR), (ρL, ρR)) π)
    (F : RatBallSet) {s : ULift.{u} (XCode nL nR) → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation (filtL.{u} nL nR) (liftP.{u} π)) fun ω => (s ω : WithTop ℝ≥0))
    (hsafe : ∀ᵐ ω ∂liftP.{u} π, (s ω : ℝ≥0∞) < cζ ω.down ∧
      Disjoint (ballsK F.1) (fwdHull (fun r : ℝ => Wl r.toNNReal ω) (s ω))) :
    IsSampledCoupling κ Wl (ul κ ((xL, xR), (ρL, ρR))) (liftP.{u} π) (ballsU F.1) hs (liftμ.{u} π) := by
  have hE₀ := CanonCond.isIntegratedSLEEvolution_lift.{u} hC
  have hK := isCompact_ballsK F.1
  have : IsProbabilityMeasure (liftP.{u} π) := by rw [liftP]; infer_instance
  have : IsProbabilityMeasure (liftμ.{u} π) := by rw [liftμ]; infer_instance
  refine isSampledCoupling_of_ratComb hE₀ hκ (ul κ ((xL, xR), (ρL, ρR)))
    (isBoundedHarmonicExtension_ul κ _) (ballsOpens F) (ballsOpens_subset_H F) hs
    (hsafe.mono fun ω h => ⟨h.1, h.2.mono_left (ballsU_subset_ballsK F.1)⟩) fun j A₀ hA₀ => ?_
  exact setIntegral_cexp_eq_cfAt_of_dyadic hE₀ (ul κ ((xL, xR), (ρL, ρR))) (isBoundedHarmonicExtension_ul κ _)
    liftμ_map_fst hK F.2 (fun q => measurableSet_El hK F.2 q) (ae_mem_El_iff hC _) (sampTest F j)
    (tsupport_sampTest_subset F j)
    (fun q => measurable_cfAt_lift κ _ hK F.2 (sampTest F j) (tsupport_sampTest_subset F j) q)
    (fun n k A hA => hC.dyadic_sampled_lift F j n k hA) hs hsafe hA₀

/-- **The lifted canonical coupling is projection-independent at every protected stop of a rational ball set.** -/
theorem CanonCond.isProjIndepCoupling_lift (hC : CanonCond κ ((xL, xR), (ρL, ρR)) π)
    (F : RatBallSet) {s : ULift.{u} (XCode nL nR) → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation (filtL.{u} nL nR) (liftP.{u} π)) fun ω => (s ω : WithTop ℝ≥0))
    (hsafe : ∀ᵐ ω ∂liftP.{u} π, (s ω : ℝ≥0∞) < cζ ω.down ∧
      Disjoint (ballsK F.1) (fwdHull (fun r : ℝ => Wl r.toNNReal ω) (s ω))) :
    IsProjIndepCoupling (ballsOpens F) hs (liftμ.{u} π) := by
  have hE₀ := CanonCond.isIntegratedSLEEvolution_lift.{u} hC
  have hK := isCompact_ballsK F.1
  have : IsProbabilityMeasure (liftP.{u} π) := by rw [liftP]; infer_instance
  have : IsProbabilityMeasure (liftμ.{u} π) := by rw [liftμ]; infer_instance
  exact isProjIndepCoupling_of_dyadic hE₀ liftμ_map_fst hK F.2 (ballsOpens F)
    (fun q => measurableSet_El hK F.2 q) (ae_mem_El_iff hC _)
    (fun f Ξ n k A hA => hC.dyadic_proj_lift F n k f Ξ hA) hs hsafe

end Family

/-! ### The optional hull coupling of a canonical law -/

section Assembly

open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {π : Measure (XCode nL nR × DistOn upperHalfPlaneOpens)} [IsProbabilityMeasure π] {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The read-out of the field and the killed driving code on the canonical space. -/
def canonF (p : XCode nL nR × DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens × DCode :=
  (p.2, (cζ p.1, killedCode (fun t (x : XCode nL nR) => cw x t) 0 cζ p.1))

theorem measurable_canonF : Measurable (canonF (nL := nL) (nR := nR)) :=
  measurable_snd.prodMk ((measurable_cζ.comp measurable_fst).prodMk
    ((measurable_killedCode (𝓕 := codeFilt) adaptedBefore_cw 0).comp measurable_fst))

/-- The field law of every coupling of a word: the fields `x − ∫ u₀ φ` form a zero-boundary GFF for every bounded
harmonic extension `u₀` of the force data (all of them agree on `ℍ`). -/
theorem isZBGFFProcess_fieldLawW (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    IsZBGFFProcess upperHalfPlaneOpens (fun φ x => x φ - ∫ z, u₀ z * φ z)
      (fieldLawW κ (((xL, xR), (ρL, ρR)) : WordData nL nR)) := by
  have hw := isBoundedHarmonicExtension_wordExt κ xL xR ρL ρR
  have heq : EqOn u₀ (wordExt κ (((xL, xR), (ρL, ρR)) : WordData nL nR)) H :=
    Impl.eqOn_of_isBoundedHarmonicExtension (Impl.forceJumpSet_finite (weightWord ρL ρR) xL xR) hw hu₀
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, ∫ z, u₀ z * φ z =
      ∫ z, wordExt κ (((xL, xR), (ρL, ρR)) : WordData nL nR) z * φ z := fun φ => by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ H
    · simp only [heq hz]
    · have : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (φ.tsupport_subset h)
      simp [this]
  simp_rw [hint]
  exact isZBGFFProcess_fieldLaw0 (continuousOn_wordExt κ _)

/-- **The family constraints of the lifted canonical coupling** (the output of Theorem 1.1's compactness step). -/
theorem CanonCond.familyProps (hκ : 0 < κ) (hC : CanonCond κ ((xL, xR), (ρL, ρR)) π) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    IsFamilySampled κ ρL ρR (liftμ.{u} π) (filtrationFst (filtL.{u} nL nR) (DistOn upperHalfPlaneOpens))
        (fun t p => Wl t p.1) (fun i t p => cvL p.1.down i t) (fun j t p => cvR p.1.down j t)
        (fun p => cζ p.1.down) (fun p => p.2) ∧
      IsFamilyLocal (liftμ.{u} π) (filtrationFst (filtL.{u} nL nR) (DistOn upperHalfPlaneOpens))
        (fun t p => Wl t p.1) (fun p => cζ p.1.down) (fun p => p.2 - smoothDist upperHalfPlaneOpens u₀) := by
  have hE₀ := CanonCond.isIntegratedSLEEvolution_lift.{u} hC
  have : IsProbabilityMeasure (liftP.{u} π) := by rw [liftP]; infer_instance
  have hμ1 := liftμ_map_fst (π := π)
  have hu := isBoundedHarmonicExtension_ul.{u} κ (((xL, xR), (ρL, ρR)) : WordData nL nR)
  have hharm := isHarmonicDistOn_smoothDist_of hu₀
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · have hζ0 := ae_zeta_eq_zero_of_threshold hE₀ hseed
    set U0 : Empty → Set ℂ := fun i => i.elim
    set s0 : Empty → ULift.{u} (XCode nL nR) → ℝ≥0 := fun i => i.elim
    have hs0 : ∀ i, IsStoppingTime (usualAugmentation (filtL.{u} nL nR) (liftP.{u} π))
        fun ω => (s0 i ω : WithTop ℝ≥0) := fun i => i.elim
    have hexh : ∀ᵐ ω ∂liftP.{u} π, ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ ω.down → ∀ K : Set ℂ, IsCompact K →
        K ⊆ H → Disjoint K (fwdHull (fun r : ℝ => Wl r.toNNReal ω) t) → ∃ i, K ⊆ U0 i ∧ t ≤ s0 i ω := by
      filter_upwards [hζ0] with ω h t ht
      rw [h] at ht
      exact absurd ht not_lt_zero
    have hexhL : ∀ᵐ ω ∂liftP.{u} π, ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ ω.down → ∀ K : Set ℂ, IsCompact K →
        K ⊆ H → Disjoint K (fwdHull (fun r : ℝ => Wl r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
          ∃ i, K ⊆ U0 i ∧ U0 i ⊆ O ∧ t ≤ s0 i ω := by
      filter_upwards [hζ0] with ω h t ht
      rw [h] at ht
      exact absurd ht not_lt_zero
    exact ⟨isFamilySampled_of_isSampledCoupling hE₀ hκ (ul κ _) hu U0 s0 hs0 (fun i => i.elim) hexh hμ1
        (fun i => i.elim),
      isFamilyLocal_of_projCoupling U0 (fun i => i.elim) (fun i => i.elim) s0 hs0 hexhL hμ1 hharm
        fun i => i.elim⟩
  · obtain ⟨T, hT⟩ := exists_isAnnouncingSeq hE₀ hκ hseed
    obtain ⟨s, hs, hsafe, hexh⟩ := exists_safeFamilyLoc hE₀ hT
    set U : RatBallSet × ℕ → Set ℂ := fun i => ballsU i.1.1 with hU
    have hUo : ∀ i, IsOpen (U i) := fun i => isOpen_ballsU _
    have hUH : ∀ i, U i ⊆ H := fun i => (ballsU_subset_ballsK _).trans i.1.2
    have hsafeU : ∀ i, ∀ᵐ ω ∂liftP.{u} π, (s i ω : ℝ≥0∞) < cζ ω.down ∧
        Disjoint (U i) (fwdHull (fun r : ℝ => Wl r.toNNReal ω) (s i ω)) := fun i =>
      (hsafe i).mono fun ω h => ⟨h.1, h.2.mono_left (ballsU_subset_ballsK _)⟩
    have hexhOld : ∀ᵐ ω ∂liftP.{u} π, ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ ω.down → ∀ K : Set ℂ, IsCompact K →
        K ⊆ H → Disjoint K (fwdHull (fun r : ℝ => Wl r.toNNReal ω) t) → ∃ i, K ⊆ U i ∧ t ≤ s i ω :=
      hexh.mono fun ω h t ht K hK hKH hdis => by
        obtain ⟨i, h1, -, h3⟩ := h t ht K hK hKH hdis univ isOpen_univ (subset_univ K)
        exact ⟨i, h1, h3⟩
    have hexhL : ∀ᵐ ω ∂liftP.{u} π, ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ ω.down → ∀ K : Set ℂ, IsCompact K →
        K ⊆ H → Disjoint K (fwdHull (fun r : ℝ => Wl r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
          ∃ i, K ⊆ U i ∧ U i ⊆ O ∧ t ≤ s i ω :=
      hexh.mono fun ω h t ht K hK hKH hdis O hO hKO => by
        obtain ⟨i, h1, h2, h3⟩ := h t ht K hK hKH hdis O hO hKO
        exact ⟨i, h1, (ballsU_subset_ballsK _).trans h2, h3⟩
    exact ⟨isFamilySampled_of_isSampledCoupling hE₀ hκ (ul κ _) hu U s hs hsafeU hexhOld hμ1
        fun i => hC.isSampledCoupling_lift hκ i.1 (hs i) (hsafe i),
      isFamilyLocal_of_projCoupling U hUo hUH s hs hexhL hμ1 hharm
        fun i => hC.isProjIndepCoupling_lift i.1 (hs i) (hsafe i)⟩

/-- **Sufficiency (S4).** Every canonical coupling law of an ordered word is realized by an optional hull coupling
(on `ULift (XCode) × 𝒟'(ℍ)`, any universe) whose joint law of field and killed driving code is `π.map canonF`. -/
theorem CanonCond.exists_isOptionalHullCoupling (hκ : 0 < κ) (hC : CanonCond κ ((xL, xR), (ρL, ρR)) π) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h ∧ P.map (fieldCode h W ζ) = π.map canonF := by
  set u₀ := wordExt κ (((xL, xR), (ρL, ρR)) : WordData nL nR)
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ :=
    isBoundedHarmonicExtension_wordExt κ xL xR ρL ρR
  have hu₀c : ContinuousOn u₀ H := continuousOn_wordExt κ _
  have hE₀ := CanonCond.isIntegratedSLEEvolution_lift.{u} hC
  have hμp : IsProbabilityMeasure (liftμ.{u} π) := by rw [liftμ]; infer_instance
  have hμ1 := liftμ_map_fst (π := π)
  have hμ2 : (liftμ.{u} π).map Prod.snd = fieldLawW κ (((xL, xR), (ρL, ρR)) : WordData nL nR) := by
    rw [liftμ_map_snd]; exact hC.2.1
  obtain ⟨hfamS, hfamL⟩ := CanonCond.familyProps.{u} hκ hC hu₀
  have hEμ := IsIntegratedSLEEvolution.fst (X := DistOn upperHalfPlaneOpens) hμ1 hE₀
  have hZμ : IsZeroBoundaryGFF upperHalfPlaneOpens
      (fun p : ULift.{u} (XCode nL nR) × DistOn upperHalfPlaneOpens => p.2 - smoothDist upperHalfPlaneOpens u₀)
      (liftμ.{u} π) :=
    isZeroBoundaryGFF_sub_smoothDist measurable_snd hu₀c
      (isZBGFFProcess_comp_snd hμ2 (isZBGFFProcess_fieldLawW κ xL xR ρL ρR hu₀))
  have hharm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := isHarmonicDistOn_smoothDist_of hu₀
  refine ⟨ULift.{u} (XCode nL nR) × DistOn upperHalfPlaneOpens, inferInstance, liftμ.{u} π, hμp, _, _, _, _, _, _,
    fun p => p.2, isOptionalHullCoupling_of_isFamilySampled hEμ hκ measurable_snd
      (fun u₀' hu₀' => isZBGFFProcess_comp_snd hμ2 (isZBGFFProcess_fieldLawW κ xL xR ρL ρR hu₀')) hfamS
      fun hX τ hτ hτζ => ?_, ?_⟩
  · have hl := isLocalSet_hull_of_isFamilyLocal hEμ hX hZμ hfamL hτ hτζ
    have hl' := IsLocalSet.add_dist hl hharm
    have e : (fun p : ULift.{u} (XCode nL nR) × DistOn upperHalfPlaneOpens =>
        p.2 - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = fun p => p.2 :=
      funext fun p => sub_add_cancel _ _
    rw [e] at hl'
    exact hl'
  · have e : fieldCode (fun p : ULift.{u} (XCode nL nR) × DistOn upperHalfPlaneOpens => p.2)
        (fun t p => Wl t p.1) (fun p => cζ p.1.down) = canonF ∘ fun p => (p.1.down, p.2) := rfl
    have hm : Measurable (canonF ∘ fun p : ULift.{u} (XCode nL nR) × DistOn upperHalfPlaneOpens =>
        (p.1.down, p.2)) := measurable_canonF.comp ((measurable_down.comp measurable_fst).prodMk measurable_snd)
    rw [e, liftμ, Measure.map_map hm measurable_liftUp]
    rfl

end Assembly

end Param12

end Exist

end InteractingSLE
