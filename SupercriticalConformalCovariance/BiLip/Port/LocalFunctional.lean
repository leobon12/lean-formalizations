import SupercriticalConformalCovariance.Domain.Locality
import LQGMetric.Field.StandardBorelRange
import LQGMetric.Field.Measurable
import LQGMetric.Prob.PolishContinuousMap
import LQGMetric.Papers.DFGPS.L2_17Core2H
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Lemma 3.3, step 7: the metric as a measurable functional of the local field

Paper l. 233: "The metric is a measurable functional of that field." What the proof of Lemma 3.3
needs is stronger than Axiom II (locality) of DG Definition 1.7 as frozen (`IsStrongLQGMetric`,
conjunct 3): one measurable functional of the **restricted** field, valued in a standard Borel space
(here the space of lower semicontinuous functions), that is almost surely correct simultaneously for
countably many laws (the transformed fields `h^{ψ_n}`, `n ∈ ℕ`, and the limit `h^a`).

`exists_universal_local_functional` proves this for every measurable observable `Θ` of whole-plane
fields which is **pathwise local** on an open set `W` (`IsPathwiseLocal`: two whole-plane GFFs plus
continuous functions on one probability space that agree on `W` a.s. have a.s. equal `Θ`). The
proof:
1. coin mixture of the countably many laws (`SmallGammaGeodesics.CC.mixMeasure`), as in
   `SupercriticalConformalCovariance.Domain.universalLocality_lsc`;
2. two conditionally independent copies `(g₁, f₁)`, `(g₂, f₂)` of `(Y, f)` given the coordinates
   `pairJ W (Y|_W)` (Mathlib's `Measure.condKernel` on the standard Borel `𝒟'(ℂ) × C(ℂ, ℝ)`); both
   are again whole-plane GFFs plus continuous functions (the property only depends on the law);
3. pathwise locality gives `Θ(g₁) = Θ(g₂)` a.s., so the conditional law of `Θ(Y)` is a.s. a Dirac
   mass; its atom is a measurable function of the coordinates (a measurable embedding into `ℝ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.PortTan

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont IsWholePlaneGFF ofCont pairJ CoordJ)
open SmallGammaGeodesics.CC (mixMeasure exists_pos_weights isProbabilityMeasure_mixMeasure
  measurable_of_sigma map_mixMeasure sum_smul_eq_of_tsum_eq_one ae_of_ae_mixMeasure)

/-- An observable `Θ` of whole-plane fields is **pathwise local** on the open set `W` if any two
whole-plane GFFs plus continuous functions on one probability space whose restrictions to `W`
agree almost surely have almost surely equal observables. -/
def IsPathwiseLocal (W : TopologicalSpace.Opens ℂ) {L : Type*} (Θ : DistC → L) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g₁ g₂ : Ω → DistC),
    IsGFFPlusCont g₁ P → IsGFFPlusCont g₂ P →
    (∀ᵐ ω ∂P, restrictTo W (g₁ ω) = restrictTo W (g₂ ω)) → ∀ᵐ ω ∂P, Θ (g₁ ω) = Θ (g₂ ω)

/-- The coordinates of the restriction to `W`. -/
def locCoord (W : TopologicalSpace.Opens ℂ) (g : DistC) : CoordJ → ℝ :=
  pairJ W (restrictTo W g)

theorem measurable_locCoord (W : TopologicalSpace.Opens ℂ) : Measurable (locCoord W) :=
  (LQGMetric.measurable_pairJ W).comp (LQGMetric.measurable_restrictTo W)

theorem locCoord_inj {W : TopologicalSpace.Opens ℂ} {g₁ g₂ : DistC}
    (h : locCoord W g₁ = locCoord W g₂) : restrictTo W g₁ = restrictTo W g₂ :=
  LQGMetric.injective_pairJ W h

/-- `(g, f) ↦ g - f` is measurable on `𝒟'(ℂ) × C(ℂ, ℝ)`. -/
theorem measurable_sub_ofCont : Measurable fun s : DistC × C(ℂ, ℝ) => s.1 - ofCont s.2 := by
  refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
  have h1 : Measurable fun s : DistC × C(ℂ, ℝ) => s.1 φ :=
    (LQGMetric.measurable_distOn_apply φ).comp measurable_fst
  have h2 : Measurable fun s : DistC × C(ℂ, ℝ) => ofCont s.2 φ :=
    (LQGMetric.measurable_ofCont_apply φ).comp measurable_snd
  have e : (fun s : DistC × C(ℂ, ℝ) => (s.1 - ofCont s.2) φ) = fun s => s.1 φ - ofCont s.2 φ :=
    funext fun s => rfl
  rw [e]
  exact h1.sub h2

instance instStandardBorelContC : StandardBorelSpace C(ℂ, ℝ) := by
  haveI := LQGMetric.polishSpace_continuousMap ℂ ℝ
  infer_instance

/-- **One law.** For a whole-plane GFF plus a continuous function `Y` and a measurable pathwise
local observable `Θ` with values in a standard Borel space, `Θ(Y)` is almost surely a measurable
function of the coordinates of `Y|_W`. -/
theorem exists_local_functional_single (W : TopologicalSpace.Opens ℂ) {L : Type}
    [MeasurableSpace L] [StandardBorelSpace L] [Nonempty L] {Θ : DistC → L}
    (hΘ : Measurable Θ) (hloc : IsPathwiseLocal W Θ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → DistC}
    (hY : IsGFFPlusCont Y P) :
    ∃ Φ : (CoordJ → ℝ) → L, Measurable Φ ∧ ∀ᵐ ω ∂P, Θ (Y ω) = Φ (locCoord W (Y ω)) := by
  obtain ⟨hYm, f, hfm, hX⟩ := hY
  set A := CoordJ → ℝ
  set S := DistC × C(ℂ, ℝ)
  have hc : Measurable (locCoord W) := measurable_locCoord W
  set Z : Ω → A × S := fun ω => (locCoord W (Y ω), (Y ω, f ω)) with hZ
  have hZm : Measurable Z := (hc.comp hYm).prodMk (hYm.prodMk hfm)
  set ρ : Measure (A × S) := P.map Z with hρ
  haveI : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  haveI : Nonempty S := ⟨(0, 0)⟩
  set κ : Kernel A S := ρ.condKernel with hκ
  set ν : Measure (A × (S × S)) := ρ.fst ⊗ₘ (κ ×ₖ κ) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- the two pair marginals of `ν` are `ρ`
  have hmarg₁ : ν.map (fun p => (p.1, p.2.1)) = ρ := by
    have e : (fun p : A × (S × S) => (p.1, p.2.1)) = Prod.map id Prod.fst := rfl
    rw [e, hν, ← Measure.compProd_map measurable_fst]
    rw [← Kernel.fst_eq, Kernel.fst_prod]
    exact Measure.disintegrate ρ κ
  have hmarg₂ : ν.map (fun p => (p.1, p.2.2)) = ρ := by
    have e : (fun p : A × (S × S) => (p.1, p.2.2)) = Prod.map id Prod.snd := rfl
    rw [e, hν, ← Measure.compProd_map measurable_snd]
    rw [← Kernel.snd_eq, Kernel.snd_prod]
    exact Measure.disintegrate ρ κ
  -- the copies are whole-plane GFFs plus continuous functions
  have hlawS : ∀ (j : A × (S × S) → S), Measurable j →
      ν.map (fun p => (p.1, j p)) = ρ → ν.map j = P.map fun ω => (Y ω, f ω) := by
    intro j hj hmj
    have h1 : ν.map j = (ν.map fun p => (p.1, j p)).map Prod.snd := by
      rw [Measure.map_map measurable_snd (measurable_fst.prodMk hj)]
      rfl
    rw [h1, hmj, hρ, Measure.map_map measurable_snd hZm]
    rfl
  have hcopy : ∀ (j : A × (S × S) → S), Measurable j →
      ν.map (fun p => (p.1, j p)) = ρ → IsGFFPlusCont (fun p => (j p).1) ν := by
    intro j hj hmj
    refine ⟨measurable_fst.comp hj, fun p => (j p).2, measurable_snd.comp hj, ?_⟩
    refine LQGMetric.DFGPS.L217.isWholePlaneGFF_of_map_eq (measurable_sub_ofCont.comp hj) hX ?_
    have hsub : Measurable fun s : S => s.1 - ofCont s.2 := measurable_sub_ofCont
    calc ν.map (fun p => (j p).1 - ofCont (j p).2)
        = (ν.map j).map (fun s : S => s.1 - ofCont s.2) := by
          rw [Measure.map_map hsub hj]; rfl
      _ = (P.map fun ω => (Y ω, f ω)).map (fun s : S => s.1 - ofCont s.2) := by
          rw [hlawS j hj hmj]
      _ = P.map (fun ω => Y ω - ofCont (f ω)) := by
          rw [Measure.map_map hsub (hYm.prodMk hfm)]; rfl
  have hj₁ : Measurable fun p : A × (S × S) => p.2.1 := measurable_fst.comp measurable_snd
  have hj₂ : Measurable fun p : A × (S × S) => p.2.2 := measurable_snd.comp measurable_snd
  have hg₁ := hcopy (fun p => p.2.1) hj₁ hmarg₁
  have hg₂ := hcopy (fun p => p.2.2) hj₂ hmarg₂
  -- the coordinates of both copies are the conditioning variable, a.s.
  set G : Set (A × S) := {q | q.1 = locCoord W q.2.1} with hG
  have hGm : MeasurableSet G :=
    measurableSet_eq_fun measurable_fst (hc.comp (measurable_fst.comp measurable_snd))
  have hρG : ∀ᵐ q ∂ρ, q ∈ G := by
    rw [hρ]
    exact (ae_map_iff hZm.aemeasurable (p := fun q => q ∈ G) hGm).2
      (Eventually.of_forall fun ω => rfl)
  have hcoord : ∀ (j : A × (S × S) → S), Measurable j →
      ν.map (fun p => (p.1, j p)) = ρ → ∀ᵐ p ∂ν, p.1 = locCoord W (j p).1 := by
    intro j hj hmj
    have h := hρG
    rw [← hmj] at h
    exact (ae_map_iff (measurable_fst.prodMk hj).aemeasurable (p := fun q => q ∈ G) hGm).1 h
  have hrestr : ∀ᵐ p ∂ν, restrictTo W (p.2.1.1) = restrictTo W (p.2.2.1) := by
    filter_upwards [hcoord _ hj₁ hmarg₁, hcoord _ hj₂ hmarg₂] with p h1 h2
    exact locCoord_inj (h1.symm.trans h2)
  have hΘeq : ∀ᵐ p ∂ν, Θ (p.2.1.1) = Θ (p.2.2.1) := hloc ν _ _ hg₁ hg₂ hrestr
  -- the conditional law of `Θ` is a.s. a Dirac mass
  set θ : S → L := fun s => Θ s.1 with hθ
  have hθm : Measurable θ := hΘ.comp measurable_fst
  set Bad : Set (S × S) := {q | θ q.1 ≠ θ q.2} with hBad
  have hBadm : MeasurableSet Bad :=
    (measurableSet_eq_fun (hθm.comp measurable_fst) (hθm.comp measurable_snd)).compl
  have hνBad : ν {p | p.2 ∈ Bad} = 0 := ae_iff.1 hΘeq
  have hker : ∀ᵐ a ∂ρ.fst, (κ ×ₖ κ) a Bad = 0 := by
    have h : ν (Prod.snd ⁻¹' Bad) = 0 := hνBad
    rw [hν, Measure.compProd_apply (measurable_snd hBadm)] at h
    have h' := (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left
      (measurable_snd hBadm))).1 h
    filter_upwards [h'] with a ha
    exact ha
  have hdirac : ∀ a, (κ ×ₖ κ) a Bad = 0 → ∃ t : L, ∀ᵐ s ∂κ a, θ s = t := by
    intro a ha
    rw [Kernel.prod_apply] at ha
    have h1 := (Measure.measure_prod_null hBadm).1 ha
    obtain ⟨s₀, hs₀⟩ := h1.exists
    refine ⟨θ s₀, ?_⟩
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hs₀
    exact fun h => hs (h.symm)
  -- a measurable choice of the atom
  obtain ⟨e, he⟩ := exists_measurableEmbedding_real L
  obtain ⟨e', he'm, he'⟩ := he.exists_measurable_extend measurable_id fun _ => inferInstance
  set φ : A → ℝ := fun a =>
    Real.log (∫⁻ s, ENNReal.ofReal (Real.exp (e (θ s))) ∂(κ a)).toReal with hφ
  have hφm : Measurable φ := by
    have hint : Measurable fun s => ENNReal.ofReal (Real.exp (e (θ s))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (he.measurable.comp hθm))
    exact Real.measurable_log.comp (hint.lintegral_kernel.ennreal_toReal)
  have hφval : ∀ a (t : L), (∀ᵐ s ∂κ a, θ s = t) → e' (φ a) = t := by
    intro a t ht
    have hl : ∫⁻ s, ENNReal.ofReal (Real.exp (e (θ s))) ∂(κ a) =
        ENNReal.ofReal (Real.exp (e t)) := by
      rw [lintegral_congr_ae (ht.mono fun s hs => by rw [hs]), lintegral_const,
        measure_univ, mul_one]
    have : φ a = e t := by
      rw [hφ]
      dsimp only
      rw [hl, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
    rw [this]
    exact congrFun he' t
  refine ⟨e' ∘ φ, he'm.comp hφm, ?_⟩
  -- transfer back to `P`
  set Good : Set (A × S) := {q | θ q.2 = e' (φ q.1)} with hGood
  have hGoodm : MeasurableSet Good :=
    measurableSet_eq_fun (hθm.comp measurable_snd) ((he'm.comp hφm).comp measurable_fst)
  have hρGood : ∀ᵐ q ∂ρ, q ∈ Good := by
    rw [ae_iff]
    have hc' : ρ Goodᶜ = ∫⁻ a, κ a {s | (a, s) ∈ Goodᶜ} ∂ρ.fst := by
      conv_lhs => rw [← Measure.disintegrate ρ κ]
      exact Measure.compProd_apply hGoodm.compl
    change ρ Goodᶜ = 0
    rw [hc']
    show ∫⁻ a, κ a (Prod.mk a ⁻¹' Goodᶜ) ∂ρ.fst = 0
    rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hGoodm.compl)]
    filter_upwards [hker] with a ha
    obtain ⟨t, ht⟩ := hdirac a ha
    have hval := hφval a t ht
    rw [ae_iff] at ht
    refine measure_mono_null (fun s hs => ?_) ht
    simp only [hGood, mem_compl_iff, mem_setOf_eq] at hs
    exact fun h => hs (h.trans hval.symm)
  rw [hρ] at hρGood
  have h2 := (ae_map_iff hZm.aemeasurable (p := fun q => q ∈ Good) hGoodm).1 hρGood
  filter_upwards [h2] with ω hω
  exact hω

/-- **Universal measurable local functional.** For countably many whole-plane GFFs plus continuous
functions, on possibly different probability spaces, and a measurable pathwise local observable
`Θ` on `W` with values in a standard Borel space, there is **one** measurable `Φ` on the coordinates
of the restricted field with `Θ(g_i) = Φ(coordinates of g_i|_W)` almost surely, for every `i`. -/
theorem exists_universal_local_functional (W : TopologicalSpace.Opens ℂ) {L : Type}
    [MeasurableSpace L] [StandardBorelSpace L] [Nonempty L] {Θ : DistC → L}
    (hΘ : Measurable Θ) (hloc : IsPathwiseLocal W Θ)
    (ι : Type) [Countable ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)]
    (g : ∀ i, Ω i → DistC) (hg : ∀ i, IsGFFPlusCont (g i) (P i)) :
    ∃ Φ : (CoordJ → ℝ) → L, Measurable Φ ∧
      ∀ i, ∀ᵐ ω ∂P i, Θ (g i ω) = Φ (locCoord W (g i ω)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨fun _ => Classical.arbitrary L, measurable_const, fun i => (IsEmpty.false i).elim⟩
  obtain ⟨w, hw0, hw1⟩ := exists_pos_weights ι
  choose f hfm hfg using fun i => (hg i).2
  haveI : IsProbabilityMeasure (mixMeasure w P) := isProbabilityMeasure_mixMeasure hw1
  set Y : Sigma Ω → DistC := fun p => g p.1 p.2 with hYdef
  set fY : Sigma Ω → C(ℂ, ℝ) := fun p => f p.1 p.2 with hfYdef
  have hYm : Measurable Y := measurable_of_sigma fun i => (hg i).1
  have hfYm : Measurable fY := measurable_of_sigma fun i => hfm i
  have hXm : Measurable fun p => Y p - ofCont (fY p) :=
    measurable_of_sigma fun i => (hfg i).measurable
  obtain ⟨i₀⟩ := hι
  have hX : IsWholePlaneGFF (fun p => Y p - ofCont (fY p)) (mixMeasure w P) := by
    refine SmallGammaGeodesics.CC.isWholePlaneGFF_of_map_pairProc_eq hXm (hfg i₀) ?_
    rw [map_mixMeasure (LQGMetric.GFFLaw.measurable_pairProc hXm)]
    have e : ∀ i, (P i).map (fun ω => LQGMetric.GFFLaw.pairProc
        (fun p => Y p - ofCont (fY p)) ⟨i, ω⟩) =
        (P i₀).map (LQGMetric.GFFLaw.pairProc fun ω => g i₀ ω - ofCont (f i₀ ω)) :=
      fun i => LQGMetric.GFFLaw.map_pairProc_eq (hfg i) (hfg i₀)
    simp only [e]
    exact sum_smul_eq_of_tsum_eq_one hw1 _
  have hYc : IsGFFPlusCont Y (mixMeasure w P) := ⟨hYm, fY, hfYm, hX⟩
  obtain ⟨Φ, hΦ, hae⟩ := exists_local_functional_single W hΘ hloc (mixMeasure w P) hYc
  exact ⟨Φ, hΦ, fun i => ae_of_ae_mixMeasure hw0 hae i⟩

end SupercriticalConformalCovariance.BiLip.PortTan
