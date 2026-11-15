/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54RefSide

/-!
# Aux. lemma 54 for general words, part 11: locality on the extension after the stop

Packet PROVE-AUX54. On a record extension `E = P ⊗ κ₀(record)` of a coupling through a stop `V` by a family reference,
after the reference's stop (`D₀` a safe event of the reference at `s`, inside `{V₀ ≤ s}`), the original centred field
`X = h − T₀` satisfies the projection identity at `U ⊆ C`. Write `X = Z + Y` (Markov decomposition at `U`).

1. On `D₀` the recorded hull lies in the reference's hull at `s` and avoids `C` (`recHull_subset_fwdHull`), so the
   projections agree, `Z(p.1) = Ẑ(p.2)` (`LocalExt.ae_markov_eq_of_lapTest_eq`), and so do the records of `Y` and `Ŷ`.
2. `∫_{snd⁻¹ D₀} F(p.1) dE = ∫ F · κ₀(rec)(D₀) · 1_{C ∩ recorded hull = ∅} dP` (compound product).
3. The stopped coupling's history-marked locality (`indep_markSigmaQ`, `measurableSet_markSigmaQ_recHull`):
   `Z ⫫ (Y(Ξ), record of Y)`; replace `e^{iY(Ξ)}` by its conditional expectation given the record of `Y`.
4. Back on `E` and through the record to the reference (`LocalExt.map_eq_of_ae_coord`), where `Ẑ` is independent of
   the record of `Ŷ` on `D₀` (`setIntegral_recOn_gauss` on the safe σ-algebra, `setIntegral_lapTest_refSafe`).

PROVE-LOCEXT-N's `extPostLocalStatement` for general words.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF Coupling DomainMarkov LQGMetric.MarkovZB LocalSets
open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {nL nR : ℕ}

/-- A full evolution is never at a threshold state before its lifetime. -/
theorem ae_not_threshold_of_evolution {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      ¬ ForceWord.ThresholdCondition ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω) := by
  filter_upwards [hE.2.2.2.2] with ω hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, -, -⟩ := hp
  exact h17

section Post

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens} {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀}
  {𝓕₀ : Filtration ℝ≥0 mΩ₀} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ}
  {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞} {h₀ : Ω₀ → DistOn upperHalfPlaneOpens}

/-- **The projection identity on the extension after the reference's stop** (PROVE-LOCEXT-N's
`extPostLocalStatement` for general words). -/
theorem setIntegral_lapTest_postE [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hreg : IsRegularStop ρL ρR P W VL VR V)
    (href : WholeFieldStopped.IsFamilyRef κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ h₀)
    (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀) {V₀ : Ω₀ → ℝ≥0∞}
    (hV₀ : IsStoppingTime (drivingFiltration P₀ hX₀) fun ω => (V₀ ω : WithTop ℝ≥0)) (hV₀ζ : ∀ ω, V₀ ω ≤ ζ₀ ω)
    {E : Measure (Ω × Ω₀)} [IsProbabilityMeasure E]
    (hE : IsRecExt P P₀ (recHull ρL ρR xL xR) h (killedHistory W VL VR V) h₀ (killedHistory W₀ VL₀ VR₀ V₀) E)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) {U : TopologicalSpace.Opens ℂ} (hUC : (U : Set ℂ) ⊆ C)
    (hUne : (U : Set ℂ).Nonempty) {s : ℝ≥0} {D₀ : Set Ω₀} (hD₀ : D₀ ∈ refSafeGens P₀ hX₀ C s)
    (hD₀V : ∀ ω ∈ D₀, V₀ ω ≤ s) (f : zsSub (U : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ p in Prod.snd ⁻¹' D₀,
        Complex.exp (Complex.I * ((h p.1 - smoothDist upperHalfPlaneOpens u₀) (lapTest U f + Ξ) : ℂ)) ∂E =
      Coupling.projFactor U f Ξ * ∫ p in Prod.snd ⁻¹' D₀,
        Complex.exp (Complex.I * ((h p.1 - smoothDist upperHalfPlaneOpens u₀) Ξ : ℂ)) ∂E := by
  classical
  obtain ⟨T₀, hT₀def⟩ : ∃ T₀, T₀ = smoothDist upperHalfPlaneOpens u₀ := ⟨_, rfl⟩
  rw [← hT₀def]
  obtain ⟨hfst, hsnd, hYE, hfR, hrecm, κ₀, hκ₀, hEeq⟩ := hE
  have := hκ₀
  obtain ⟨hEv, hcont, hhm, hgff, hX, -⟩ := id hSC
  obtain ⟨hEv₀, hh₀, hgff₀, -, hfamL⟩ := href
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hT₀ : IsHarmonicDistOn T₀ H := hT₀def ▸ Coupling.isHarmonicDistOn_smoothDist_of hu₀
  have hX₁ : IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => h ω - T₀) P :=
    hT₀def ▸ Coupling.isZeroBoundaryGFF_sub_smoothDist hhm hu₀c (hgff u₀ hu₀)
  have hX₂ : IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => h₀ ω - T₀) P₀ :=
    hT₀def ▸ Coupling.isZeroBoundaryGFF_sub_smoothDist hh₀ hu₀c (hgff₀ u₀ hu₀)
  have hfam : IsFamilyLocal P₀ 𝓕₀ W₀ ζ₀ fun ω => h₀ ω - T₀ := hT₀def ▸ hfamL u₀ hu₀
  have hUH : (U : Set ℂ) ⊆ H := hUC.trans hCH
  have hU : U ≤ upperHalfPlaneOpens := hUH
  have hCne : C.Nonempty := hUne.mono hUC
  obtain ⟨G, hGG, hGd⟩ := exists_markovMap U hUH
  have hd₁ := hGd hX₁
  have hd₂ := hGd hX₂
  have hX₁m : Measurable fun ω => h ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hhm
  have hX₂m : Measurable fun ω => h₀ ω - T₀ := (WholeField.measurable_sub_dist T₀).comp hh₀
  set Y : Ω → HistorySpace nL nR := killedHistory W VL VR V with hYdef
  set Y₀ : Ω₀ → HistorySpace nL nR := killedHistory W₀ VL₀ VR₀ V₀ with hY₀def
  have hYm : Measurable Y := measurable_killedHistory hX
  have hY₀σ := measurable_killedHistory_of_stop hX₀ hV₀ hV₀ζ
  have hY₀m : Measurable Y₀ := hY₀σ.mono hV₀.measurableSpace_le le_rfl
  -- the safe event of the reference
  obtain ⟨hD₀m', hD₀safe⟩ := hD₀
  have hD₀m : MeasurableSet D₀ := (drivingFiltration P₀ hX₀).le s _ hD₀m'
  have hD₀E : MeasurableSet (Prod.snd ⁻¹' D₀ : Set (Ω × Ω₀)) := measurable_snd hD₀m
  have hdis₀ : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ D₀ → Disjoint C (recHull ρL ρR xL xR (Y₀ ω₀)) := by
    filter_upwards [hEv₀.isSLEEvolutionUpTo.ae_path, hD₀safe, ae_not_threshold_of_evolution hEv₀] with ω₀ hp
      hsafe hnt hω
    obtain ⟨hsζ, hd⟩ := hsafe hω
    have hc := continuousOn_state_of_isSLEPathUpTo hp
    have h0 : dState W₀ VL₀ VR₀ ω₀ 0 = initVal xL xR := by
      simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
      exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
    exact hd.mono_right (recHull_subset_fwdHull hc h0 hnt (hD₀V ω₀ hω) hsζ)
  have hdisE : ∀ᵐ p ∂E, p.2 ∈ D₀ → Disjoint C (recHull ρL ρR xL xR (Y₀ p.2)) := by
    rw [← hsnd] at hdis₀
    exact ae_of_ae_map measurable_snd.aemeasurable hdis₀
  set Γq : Set Ω := {ω | Disjoint C (recHull ρL ρR xL xR (Y ω))} with hΓqdef
  have hΓqm : MeasurableSet Γq := hYm (isMeasHull_recHull ρL ρR xL xR C hC)
  have hsuppE : ∀ᵐ p ∂E, p.2 ∈ D₀ → p.1 ∈ Γq := by
    filter_upwards [hYE, hdisE] with p h1 h3 hp
    show Disjoint C (recHull ρL ρR xL xR (Y p.1))
    rw [h1]
    exact h3 hp
  -- 1. the projections agree after the stop
  have hlapE : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E, p.2 ∈ D₀ →
      Disjoint (tsupport ψ) (recHull ρL ρR xL xR (Y₀ p.2)) → (h p.1 - T₀) ψ = (h₀ p.2 - T₀) ψ := by
    intro ψ
    filter_upwards [hfR ψ, hYE] with p hp hy _ hdis
    have hp' := hp
    rw [hy] at hp'
    rw [fieldRecA_of_disjoint hdis, fieldRecA_of_disjoint hdis] at hp'
    simp only [sub_apply, hp']
  have hZE : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ p ∂E, p ∈ Prod.snd ⁻¹' D₀ →
      G (h p.1 - T₀) χ = G (h₀ p.2 - T₀) χ := fun χ =>
    LocalExt.ae_markov_eq_of_lapTest_eq hfst hsnd hU hX₁m hX₂m hGG hd₁ hd₂ hD₀E (fun f' => by
      filter_upwards [hlapE (lapTest U f'), hdisE] with p hp hd hpD
      exact hp hpD ((hd hpD).mono_left ((tsupport_lapTest_subset hU f').trans (f'.2.2.2.trans hUC)))) χ
  -- 2. the compound-product formula
  set rec : Ω → RecSpace nL nR := fun ω => recOfA (recHull ρL ρR xL xR) (h ω) (Y ω) with hrecdef
  set g : RecSpace nL nR → ℝ := fun R => (κ₀ R D₀).toReal with hgdef
  have hgm : Measurable g := (κ₀.measurable_coe hD₀m).ennreal_toReal
  have hg01 : ∀ R, 0 ≤ g R ∧ g R ≤ 1 := fun R => ⟨ENNReal.toReal_nonneg, by
    have := prob_le_one (μ := κ₀ R) (s := D₀)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩
  have hCP : ∀ F : Ω → ℂ, Measurable F → (∀ ω, ‖F ω‖ ≤ 1) →
      ∫ p in Prod.snd ⁻¹' D₀, F p.1 ∂E =
        ∫ ω, F ω * ((g (rec ω) : ℝ) : ℂ) * Γq.indicator (fun _ => (1 : ℂ)) ω ∂P := by
    intro F hF hFb
    have hnull : (Prod.snd ⁻¹' D₀ : Set (Ω × Ω₀)) =ᵐ[E] (Γq ×ˢ D₀ : Set (Ω × Ω₀)) := by
      filter_upwards [hsuppE] with p hp
      apply propext
      simp only [mem_preimage, mem_prod]
      exact ⟨fun h2 => ⟨hp h2, h2⟩, fun h2 => h2.2⟩
    have hint : IntegrableOn (fun p : Ω × Ω₀ => F p.1) (Γq ×ˢ D₀)
        (P ⊗ₘ κ₀.comap (fun ω => recOfA (recHull ρL ρR xL xR) (h ω) (Y ω)) hrecm) :=
      (Integrable.of_bound (hF.comp measurable_fst).aestronglyMeasurable 1
        (Eventually.of_forall fun p => hFb p.1)).integrableOn
    rw [setIntegral_congr_set hnull, hEeq, Measure.setIntegral_compProd hΓqm hD₀m hint,
      ← integral_indicator hΓqm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ Γq
    · simp only [indicator_of_mem hω, setIntegral_const, Kernel.comap_apply, measureReal_def, hgdef,
        Complex.real_smul, mul_one]
      ring
    · simp only [indicator_of_notMem hω, mul_zero]
  -- 3. the stopped coupling's side: the record of the complementary projection
  set Y₁ : Ω → DistOn upperHalfPlaneOpens := fun ω => markovCompl G (h ω - T₀) with hY₁def
  set Vq : Ω → ℝ × RecSpace nL nR := fun ω => (Γq.indicator (fun _ => (1 : ℝ)) ω,
    recOn ρL ρR xL xR Γq Y₁ Y ω) with hVqdef
  have hmarkM : ∀ M : Set (HistorySpace nL nR), MeasurableSet M →
      MeasurableSet[markSigmaQ P W VL VR V (U : Set ℂ)] (Γq ∩ Y ⁻¹' M) := fun M hM =>
    measurableSet_markSigmaQ_recHull hSC hseed hreg hC hCH hCne hUC hM
  have hΓqσ : MeasurableSet[markSigmaQ P W VL VR V (U : Set ℂ)] Γq := by
    have := hmarkM univ MeasurableSet.univ
    rwa [preimage_univ, inter_univ] at this
  have h𝓜r : markSigmaQ P W VL VR V (U : Set ℂ) ≤
      MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ P W VL VR V (U : Set ℂ) := le_sup_right
  have hVqm : Measurable[MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ P W VL VR V (U : Set ℂ)] Vq := by
    have hrec := measurable_recOn (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR)
      (𝓐 := MeasurableSpace.comap Y₁ inferInstance)
      (𝓜 := MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ P W VL VR V (U : Set ℂ)) (D := Γq) (y := Y)
      (comap_measurable Y₁) le_sup_left (h𝓜r _ hΓqσ) fun M hM => h𝓜r _ (hmarkM M hM)
    exact Measurable.prodMk (m := MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ P W VL VR V (U : Set ℂ))
      (measurable_const.indicator (h𝓜r _ hΓqσ)) hrec
  set W₁ : Ω → ℝ × (ℝ × RecSpace nL nR) := fun ω => (Y₁ ω Ξ, Vq ω) with hW₁def
  have hW₁m : Measurable[MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ P W VL VR V (U : Set ℂ)] W₁ :=
    Measurable.prodMk (m := MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ P W VL VR V (U : Set ℂ))
      (((measurable_distOn_apply Ξ).comp (comap_measurable Y₁)).mono le_sup_left le_rfl) hVqm
  have hindQ : IndepFun (fun ω => G (h ω - T₀)) W₁ P :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
      (indep_markSigmaQ hSC hT₀ hseed hreg hUH hUne hGG hd₁) hW₁m.comap_le)
  have hσle : MeasurableSpace.comap Y₁ inferInstance ⊔ markSigmaQ P W VL VR V (U : Set ℂ) ≤ mΩ :=
    sup_le ((measurable_markovCompl hGG).comp hX₁m).comap_le (markSigmaQ_le _)
  have hW₁m' : Measurable W₁ := hW₁m.mono hσle le_rfl
  -- the conditional expectation of `e^{iY(Ξ)}` given the record of `Y`
  set A : Ω → ℂ := fun ω => Complex.exp (Complex.I * (Y₁ ω Ξ : ℂ)) with hAdef
  have hsm : StronglyMeasurable[MeasurableSpace.comap Vq inferInstance]
      (P[A | MeasurableSpace.comap Vq inferInstance]) := stronglyMeasurable_condExp
  obtain ⟨ã₀, hã₀, hã₀e⟩ := hsm.exists_eq_measurable_comp
  set ã : ℝ × RecSpace nL nR → ℂ := fun x => if ‖ã₀ x‖ ≤ 1 then ã₀ x else 0 with hãdef
  have hãm : Measurable ã :=
    hã₀.measurable.ite (measurableSet_le hã₀.measurable.norm measurable_const) measurable_const
  have hãb : ∀ x, ‖ã x‖ ≤ 1 := fun x => by
    by_cases hx : ‖ã₀ x‖ ≤ 1
    · simp only [hãdef, hx, ↓reduceIte]
    · simp only [hãdef, hx, ↓reduceIte, norm_zero, zero_le_one]
  have hãe : P[A | MeasurableSpace.comap Vq inferInstance] =ᵐ[P] fun ω => ã (Vq ω) := by
    have hb := ae_bdd_norm_condExp_of_ae_bdd_norm (m := MeasurableSpace.comap Vq inferInstance) (μ := P) (R := 1)
      (f := A) (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
    filter_upwards [hb] with ω hω
    have e := congrFun hã₀e ω
    simp only [Function.comp_apply] at e
    rw [e] at hω ⊢
    simp only [hãdef, hω, ↓reduceIte]
  -- 4. the chain for one test function
  have hVqΓ : ∀ ω, ω ∈ Γq → Vq ω = ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (Y₁ ω) (Y ω)) := by
    intro ω hΓ
    simp only [hVqdef, indicator_of_mem hΓ, recOn_of_mem hΓ]
  have hVq0 : ∀ ω, ω ∉ Γq → (Vq ω).1 = 0 := fun ω hΓ => by
    simp only [hVqdef, indicator_of_notMem hΓ]
  have hY₂m : Measurable fun ω => markovCompl G (h₀ ω - T₀) := (measurable_markovCompl hGG).comp hX₂m
  have hVqm' : Measurable Vq := hVqm.mono hσle le_rfl
  -- the reference side on the safe σ-algebra
  have hle₀ : MeasurableSpace.generateFrom (refSafeGens P₀ hX₀ C s) ≤ mΩ₀ :=
    MeasurableSpace.generateFrom_le fun D hD => (drivingFiltration P₀ hX₀).le s _ hD.1
  have hid₀ : ∀ (f' : zsSub (U : Set ℂ)) (Ξ' : TestOn upperHalfPlaneOpens) (D : Set Ω₀),
      MeasurableSet[MeasurableSpace.generateFrom (refSafeGens P₀ hX₀ C s)] D →
      ∫ ω in D, Complex.exp (Complex.I * ((h₀ ω - T₀) (lapTest U f' + Ξ') : ℂ)) ∂P₀ =
        Coupling.projFactor U f' Ξ' * ∫ ω in D, Complex.exp (Complex.I * ((h₀ ω - T₀) Ξ' : ℂ)) ∂P₀ :=
    fun f' Ξ' D hD => setIntegral_lapTest_refSafe hEv₀ hX₀ hh₀ hT₀ hfam hC hCH hUC hGG hd₂ s f' Ξ' hD
  have hD₀σ : MeasurableSet[MeasurableSpace.generateFrom (refSafeGens P₀ hX₀ C s)] D₀ :=
    MeasurableSpace.measurableSet_generateFrom ⟨hD₀m', hD₀safe⟩
  have hy₀ : ∀ M : Set (HistorySpace nL nR), MeasurableSet M →
      MeasurableSet[MeasurableSpace.generateFrom (refSafeGens P₀ hX₀ C s)] (D₀ ∩ Y₀ ⁻¹' M) := by
    intro M hM
    refine MeasurableSpace.measurableSet_generateFrom ⟨?_, hD₀safe.mono fun ω h' hω => h' hω.1⟩
    have h1 := ((hV₀.measurableSet _).1 (hY₀σ hM)).2 s
    have e : D₀ ∩ Y₀ ⁻¹' M = D₀ ∩ (Y₀ ⁻¹' M ∩ {ω | (V₀ ω : WithTop ℝ≥0) ≤ ((s : ℝ≥0) : WithTop ℝ≥0)}) := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨hω, hM'⟩
        exact ⟨hω, hM', hD₀V ω hω⟩
      · rintro ⟨hω, hM', -⟩
        exact ⟨hω, hM'⟩
    rw [e]
    exact hD₀m'.inter h1
  have key : ∀ χ : TestOn upperHalfPlaneOpens, (∀ᵐ ω ∂P, Y₁ ω χ = Y₁ ω Ξ) →
      ∫ p in Prod.snd ⁻¹' D₀, Complex.exp (Complex.I * ((h p.1 - T₀) χ : ℂ)) ∂E =
        LocalExt.gaussFactor U χ * ∫ ω in D₀,
          ã ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (markovCompl G (h₀ ω - T₀)) (Y₀ ω)) ∂P₀ := by
    intro χ hYχ
    set Φ : DistOn upperHalfPlaneOpens × (ℝ × RecSpace nL nR) → ℂ := fun x =>
      Complex.exp (Complex.I * (x.1 χ : ℂ)) *
        (if x.2.1 = 1 then ((g (recBuild ρL ρR xL xR T₀ (x.1, x.2.2)) : ℝ) : ℂ) else 0) with hΦdef
    have hΦm : Measurable Φ := (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp measurable_fst)).mul
      (Measurable.ite (measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const)
        (Complex.measurable_ofReal.comp (hgm.comp ((measurable_recBuild T₀).comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))) measurable_const)
    have hΦb : ∀ x, ‖Φ x‖ ≤ 1 := fun x => by
      rw [hΦdef, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
      split_ifs
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg01 _).1]; exact (hg01 _).2
      · rw [norm_zero]; exact zero_le_one
    have hrecQ : ∀ ω, ω ∈ Γq → recBuild ρL ρR xL xR T₀ (G (h ω - T₀), (Vq ω).2) = rec ω := fun ω hΓ => by
      rw [hVqΓ ω hΓ]
      exact recBuild_markov T₀ (h ω) G (Y ω)
    have hdec : ∀ᵐ ω ∂P, Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)) * ((g (rec ω) : ℝ) : ℂ) *
        Γq.indicator (fun _ => (1 : ℂ)) ω = A ω * Φ (G (h ω - T₀), Vq ω) := by
      filter_upwards [hYχ] with ω hY
      by_cases hΓ : ω ∈ Γq
      · have h1 : (Vq ω).1 = 1 := by rw [hVqΓ ω hΓ]
        rw [indicator_of_mem hΓ, hΦdef]
        simp only [h1, ↓reduceIte, hrecQ ω hΓ, hAdef, mul_one]
        rw [show (h ω - T₀) χ = G (h ω - T₀) χ + Y₁ ω χ by simp only [hY₁def, markovCompl, sub_apply]; ring, hY]
        push_cast
        rw [mul_add, Complex.exp_add]
        ring
      · have h0 : ¬ (Vq ω).1 = 1 := by rw [hVq0 ω hΓ]; norm_num
        rw [indicator_of_notMem hΓ, hΦdef]
        simp only [h0, ↓reduceIte, mul_zero]
    have hdec' : ∀ ω, ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ)) * ((g (rec ω) : ℝ) : ℂ) *
        Γq.indicator (fun _ => (1 : ℂ)) ω = ã (Vq ω) * Φ (G (h ω - T₀), Vq ω) := by
      intro ω
      by_cases hΓ : ω ∈ Γq
      · have h1 : (Vq ω).1 = 1 := by rw [hVqΓ ω hΓ]
        rw [indicator_of_mem hΓ, hΦdef]
        simp only [h1, ↓reduceIte, hrecQ ω hΓ, mul_one]
        ring
      · have h0 : ¬ (Vq ω).1 = 1 := by rw [hVq0 ω hΓ]; norm_num
        rw [indicator_of_notMem hΓ, hΦdef]
        simp only [h0, ↓reduceIte, mul_zero]
    have hGL := LocalExt.integral_mul_eq_of_indepFun_condExp (hGG.comp hX₁m) hW₁m' hindQ
      (a := fun w : ℝ × (ℝ × RecSpace nL nR) => Complex.exp (Complex.I * (w.1 : ℂ)))
      (GFF.measurable_exp_I_mul measurable_fst) (fun w => (Complex.norm_exp_I_mul_ofReal _).le)
      (v := Prod.snd) measurable_snd hãm hãb hãe hΦm hΦb
    have hFm : Measurable fun ω => ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ)) :=
      (hãm.comp hVqm').mul (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp (hGG.comp hX₁m)))
    have hFb : ∀ ω, ‖ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ))‖ ≤ 1 := fun ω => by
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]; exact hãb _
    rw [hCP (fun ω => Complex.exp (Complex.I * ((h ω - T₀) χ : ℂ)))
      (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp hX₁m))
      (fun ω => (Complex.norm_exp_I_mul_ofReal _).le), integral_congr_ae hdec]
    have hGL' : ∫ ω, A ω * Φ (G (h ω - T₀), Vq ω) ∂P = ∫ ω, ã (Vq ω) * Φ (G (h ω - T₀), Vq ω) ∂P := hGL
    rw [hGL', ← integral_congr_ae (Eventually.of_forall hdec'),
      ← hCP (fun ω => ã (Vq ω) * Complex.exp (Complex.I * (G (h ω - T₀) χ : ℂ))) hFm hFb]
    -- transfer to the reference through the record
    set f₁ : Ω × Ω₀ → (ℝ × ℝ × HistorySpace nL nR) × (TestOn upperHalfPlaneOpens → ℝ) :=
      fun p => ((G (h p.1 - T₀) χ, (Vq p.1).1, (Vq p.1).2.1), (Vq p.1).2.2) with hf₁def
    set f₂ : Ω × Ω₀ → (ℝ × ℝ × HistorySpace nL nR) × (TestOn upperHalfPlaneOpens → ℝ) :=
      fun p => ((G (h₀ p.2 - T₀) χ, (1 : ℝ), Y₀ p.2),
        fieldRecA (recHull ρL ρR xL xR) (markovCompl G (h₀ p.2 - T₀)) (Y₀ p.2)) with hf₂def
    set k : (ℝ × ℝ × HistorySpace nL nR) × (TestOn upperHalfPlaneOpens → ℝ) → ℂ :=
      fun x => ã (x.1.2.1, (x.1.2.2, x.2)) * Complex.exp (Complex.I * (x.1.1 : ℂ)) with hkdef
    have hf₁m : Measurable f₁ :=
      ((((measurable_distOn_apply χ).comp (hGG.comp hX₁m)).comp measurable_fst).prodMk
        (((measurable_fst.comp hVqm').comp measurable_fst).prodMk
          ((measurable_fst.comp (measurable_snd.comp hVqm')).comp measurable_fst))).prodMk
        ((measurable_snd.comp (measurable_snd.comp hVqm')).comp measurable_fst)
    have hf₂m : Measurable f₂ :=
      ((((measurable_distOn_apply χ).comp (hGG.comp hX₂m)).comp measurable_snd).prodMk
        (measurable_const.prodMk (hY₀m.comp measurable_snd))).prodMk
        ((measurable_snd.comp ((measurable_recOfA (isMeasHull_recHull ρL ρR xL xR)).comp
          (hY₂m.prodMk hY₀m))).comp measurable_snd)
    have hkm : Measurable k := (hãm.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))).mul
      (GFF.measurable_exp_I_mul (measurable_fst.comp measurable_fst))
    have h1 : ∀ᵐ p ∂E.restrict (Prod.snd ⁻¹' D₀), (f₁ p).1 = (f₂ p).1 := by
      rw [ae_restrict_iff' hD₀E]
      filter_upwards [hZE χ, hsuppE, hYE] with p hz hs' hy hp
      simp only [hf₁def, hf₂def, hVqΓ p.1 (hs' hp), recOfA, hz hp, hy]
    have h2 : ∀ ψ, ∀ᵐ p ∂E.restrict (Prod.snd ⁻¹' D₀), (f₁ p).2 ψ = (f₂ p).2 ψ := by
      intro ψ
      rw [ae_restrict_iff' hD₀E]
      filter_upwards [hZE ψ, hsuppE, hYE, hlapE ψ] with p hz hs' hy hl hp
      simp only [hf₁def, hf₂def, hVqΓ p.1 (hs' hp), recOfA, hy]
      by_cases hd : Disjoint (tsupport ψ) (recHull ρL ρR xL xR (Y₀ p.2))
      · rw [fieldRecA_of_disjoint hd, fieldRecA_of_disjoint hd]
        simp only [hY₁def, markovCompl, sub_apply]
        rw [hz hp]
        have := hl hp hd
        simp only [sub_apply] at this
        rw [this]
      · simp only [fieldRecA, hd, ↓reduceIte]
    have hmap := LocalExt.map_eq_of_ae_coord hf₁m hf₂m h1 h2
    have htr : ∫ p in Prod.snd ⁻¹' D₀, ã (Vq p.1) * Complex.exp (Complex.I * (G (h p.1 - T₀) χ : ℂ)) ∂E =
        ∫ p in Prod.snd ⁻¹' D₀, ã ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (markovCompl G (h₀ p.2 - T₀)) (Y₀ p.2)) *
          Complex.exp (Complex.I * (G (h₀ p.2 - T₀) χ : ℂ)) ∂E := by
      calc _ = ∫ p, k (f₁ p) ∂E.restrict (Prod.snd ⁻¹' D₀) := rfl
        _ = ∫ x, k x ∂(E.restrict (Prod.snd ⁻¹' D₀)).map f₁ :=
          (integral_map hf₁m.aemeasurable hkm.aestronglyMeasurable).symm
        _ = ∫ x, k x ∂(E.restrict (Prod.snd ⁻¹' D₀)).map f₂ := by rw [hmap]
        _ = ∫ p, k (f₂ p) ∂E.restrict (Prod.snd ⁻¹' D₀) :=
          integral_map hf₂m.aemeasurable hkm.aestronglyMeasurable
        _ = _ := rfl
    rw [htr]
    have hFm₂ : Measurable fun ω => ã ((1 : ℝ), recOfA (recHull ρL ρR xL xR) (markovCompl G (h₀ ω - T₀)) (Y₀ ω)) *
        Complex.exp (Complex.I * (G (h₀ ω - T₀) χ : ℂ)) :=
      (hãm.comp (measurable_const.prodMk ((measurable_recOfA (isMeasHull_recHull ρL ρR xL xR)).comp
        (hY₂m.prodMk hY₀m)))).mul
        (GFF.measurable_exp_I_mul ((measurable_distOn_apply χ).comp (hGG.comp hX₂m)))
    have hsm := setIntegral_map (μ := E) (g := Prod.snd) (f := fun ω => ã ((1 : ℝ),
      recOfA (recHull ρL ρR xL xR) (markovCompl G (h₀ ω - T₀)) (Y₀ ω)) *
        Complex.exp (Complex.I * (G (h₀ ω - T₀) χ : ℂ))) hD₀m
      (by rw [hsnd]; exact hFm₂.aestronglyMeasurable) measurable_snd.aemeasurable
    rw [hsnd] at hsm
    rw [← hsm]
    have hrefg := setIntegral_recOn_gauss (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) hX₂m hUH hGG hd₂ hle₀
      hid₀ hD₀σ hy₀ hãm χ
    rw [← hrefg]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    ring
  -- 5. the projection identity
  have hlap : ∀ᵐ ω ∂P, Y₁ ω (lapTest U f + Ξ) = Y₁ ω Ξ := by
    filter_upwards [ae_markov_sub_lapTest_eq hU hd₁ (lapTest U f) f] with ω hω
    rw [sub_self, map_zero] at hω
    simp only [hY₁def, markovCompl, map_add, sub_apply] at hω ⊢
    linarith
  rw [key _ hlap, key Ξ (Eventually.of_forall fun _ => rfl), LocalExt.gaussFactor_lapTest_add hUH f Ξ, mul_assoc]

end Post

end Aux54

end Restart

end InteractingSLE
