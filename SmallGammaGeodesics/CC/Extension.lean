import SmallGammaGeodesics.CC.UniversalLocality
import LQGMetric.Field.StandardBorelRange
import Mathlib.Probability.Kernel.CondDistrib

/-!
# The coordinate extension lemma for the whole-plane GFF (track CC, packet CC12a, T2)

Sources: planning audit `planning/audits/GA5-inputs-and-reuse.md`, Details **(a11)** (GFF extension
via `condDistrib`), and `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D17**
item 2 ("the coordinate extension lemma (GA5 (a11) with `condDistrib` of `id` given the
coordinates, on the standard Borel `DistC`) gives, on `Ω × DistC`, a whole-plane GFF `h̄` with
`h̄(e_k) = X_k` a.s.").

Let `(e_i)_{i ∈ ι}` be a countable family of mean-zero test functions and let `Y : Ω → ι → ℝ` be
measurable with the law of the coordinates `(h₀(e_i))_i` of a whole-plane GFF `h₀`. Put
`ν := law(h₀)` on `DistC`, `r x := (x(e_i))_i`, and let `κ := condDistrib id r ν` be the regular
conditional law of the field given its coordinates (it exists because `DistC` is standard Borel,
`LQGMetric.standardBorelSpace_distOn`). On `Ω × DistC` take `P' := P ⊗ₘ (κ ∘ Y)`.

* `map_compProd_comap`: `law_{P'}(Y ∘ fst, snd) = (law Y) ⊗ₘ κ = law_ν(r, id)`
  (`compProd_map_condDistrib`);
* `ae_of_ae_compProd_fst`: an a.s. statement about the first coordinate under `μ ⊗ₘ κ` holds
  `μ`-a.s. (no measurability needed; `Measure.ae_ae_of_ae_compProd`);
* **T2** `exists_extension_of_map_eq`: `P'` is a probability measure with first marginal `P`, the
  second coordinate `h̄ := snd` is a whole-plane GFF, and a.s. `h̄(e_i) = Y_i ∘ fst` for every `i`
  (the diagonal `{(y, x) | r x = y}` is measurable because `ι` is countable, and has full measure
  under `law_ν(r, id)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace SmallGammaGeodesics.CC

open LQGMetric

section CompProd

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- **Transfer back along the first coordinate.** If a property of the first coordinate holds
`μ ⊗ₘ κ`-a.s. for a Markov kernel `κ`, it holds `μ`-a.s. No measurability of the property is
needed. -/
theorem ae_of_ae_compProd_fst {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsMarkovKernel κ]
    {q : α → Prop} (h : ∀ᵐ p ∂(μ ⊗ₘ κ), q p.1) : ∀ᵐ a ∂μ, q a := by
  filter_upwards [Measure.ae_ae_of_ae_compProd h] with a ha
  have : (ae (κ a)).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨_, hb⟩ := ha.exists
  exact hb

/-- The law of `(Y ∘ fst, snd)` under `μ ⊗ₘ (κ ∘ Y)` is `(law Y) ⊗ₘ κ`. -/
theorem map_compProd_comap (μ : Measure α) [SFinite μ] (κ : Kernel β γ) [IsSFiniteKernel κ]
    {Y : α → β} (hY : Measurable Y) :
    (μ ⊗ₘ κ.comap Y hY).map (fun p => (Y p.1, p.2)) = (μ.map Y) ⊗ₘ κ := by
  have hm : Measurable fun p : α × γ => (Y p.1, p.2) :=
    (hY.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hY]
  rfl

end CompProd

/-- A test function of integral `1` supported in a nonempty open set (a normed bump). -/
theorem exists_testC_integral_eq_one {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ ρ : TestC, tsupport (ρ : ℂ → ℝ) ⊆ U ∧ ∫ x, ρ x = 1 := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU u hu
  let b : ContDiffBump u := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, subset_univ _⟩, ?_,
    b.integral_normed⟩
  show tsupport (b.normed volume) ⊆ U
  rw [b.tsupport_normed_eq]
  have hrb : b.rOut < r := by
    show r / 2 < r
    linarith
  exact (Metric.closedBall_subset_ball hrb).trans hball

/-! ## T2: the coordinate extension -/

/-- **T2 (GA5 (a11), CC0 D17.2): the coordinate extension lemma.** Let `(e_i)_{i ∈ ι}` be a
countable family of mean-zero test functions and `Y : Ω → ι → ℝ` measurable, with the law of the
coordinates `(h₀(e_i))_i` of a whole-plane GFF `h₀`. Then on `Ω × DistC` there is a probability
measure `P'` with first marginal `P`, under which every a.s. statement about the first coordinate
transfers back to `P`, the second coordinate `h̄ = snd` is a whole-plane GFF, and a.s.
`h̄(e_i) = Y_i ∘ fst` for all `i`. -/
theorem exists_extension_of_map_eq {ι : Type} [Countable ι] (e : ι → TestC0)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ι → ℝ} (hY : Measurable Y)
    {Ω₀ : Type*} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} {h₀ : Ω₀ → DistC}
    (hh₀ : IsWholePlaneGFF h₀ P₀)
    (hlaw : P.map Y = P₀.map (fun ω i => h₀ ω (e i).1)) :
    ∃ P' : Measure (Ω × DistC), IsProbabilityMeasure P' ∧ P'.map Prod.fst = P ∧
      (∀ q : Ω → Prop, (∀ᵐ p ∂P', q p.1) → ∀ᵐ ω ∂P, q ω) ∧
      IsWholePlaneGFF (fun p : Ω × DistC => p.2) P' ∧
      ∀ᵐ p ∂P', ∀ i, p.2 (e i).1 = Y p.1 i := by
  have hP₀ : IsProbabilityMeasure P₀ := hh₀.gaussian.isProbabilityMeasure
  -- the law of the field and its coordinates
  set ν : Measure DistC := P₀.map h₀ with hν
  have hνp : IsProbabilityMeasure ν := inferInstance
  set r : DistC → ι → ℝ := fun x i => x (e i).1 with hr
  have hrm : Measurable r := measurable_pi_iff.2 fun i => GFFInv.measurable_pair (e i).1
  have hrid : Measurable fun x : DistC => (r x, x) := hrm.prodMk measurable_id
  -- the regular conditional law of the field given its coordinates
  set κ : Kernel (ι → ℝ) DistC := condDistrib id r ν with hκ
  have hdis : (ν.map r) ⊗ₘ κ = ν.map (fun x => (r x, x)) :=
    compProd_map_condDistrib hrm.aemeasurable aemeasurable_id
  have hYr : P.map Y = ν.map r := by
    rw [hlaw, hν, Measure.map_map hrm hh₀.measurable]
    rfl
  set P' : Measure (Ω × DistC) := P ⊗ₘ κ.comap Y hY with hP'
  have hm : Measurable fun p : Ω × DistC => (Y p.1, p.2) :=
    (hY.comp measurable_fst).prodMk measurable_snd
  -- the joint law of `(Y ∘ fst, snd)`
  have hjoint : P'.map (fun p => (Y p.1, p.2)) = ν.map (fun x => (r x, x)) := by
    rw [hP', map_compProd_comap P κ hY, hYr, hdis]
  have hsnd : P'.map Prod.snd = ν := by
    have h1 : P'.map Prod.snd = (P'.map (fun p => (Y p.1, p.2))).map Prod.snd := by
      rw [Measure.map_map measurable_snd hm]
      rfl
    rw [h1, hjoint, Measure.map_map measurable_snd hrid]
    exact Measure.map_id
  refine ⟨P', inferInstance, Measure.fst_compProd P _, fun q hq => ae_of_ae_compProd_fst hq,
    ?_, ?_⟩
  · -- `snd` is a whole-plane GFF: its law is that of `h₀`
    refine isWholePlaneGFF_of_map_pairProc_eq measurable_snd hh₀ ?_
    have e1 : GFFLaw.pairProc (fun p : Ω × DistC => p.2) =
        GFFLaw.pairProc (id : DistC → DistC) ∘ Prod.snd := rfl
    rw [e1, ← Measure.map_map (GFFLaw.measurable_pairProc measurable_id) measurable_snd, hsnd, hν,
      Measure.map_map (GFFLaw.measurable_pairProc measurable_id) hh₀.measurable]
    rfl
  · -- the diagonal has full measure
    have hAm : MeasurableSet {q : (ι → ℝ) × DistC | ∀ i, q.2 (e i).1 = q.1 i} := by
      rw [ofPred_forall]
      exact MeasurableSet.iInter fun i =>
        measurableSet_eq_fun ((GFFInv.measurable_pair (e i).1).comp measurable_snd)
          ((measurable_pi_apply i).comp measurable_fst)
    have hfull : ∀ᵐ q ∂(ν.map (fun x => (r x, x))), ∀ i, q.2 (e i).1 = q.1 i :=
      (ae_map_iff hrid.aemeasurable hAm).2 (ae_of_all _ fun x i => rfl)
    rw [← hjoint] at hfull
    exact (ae_map_iff hm.aemeasurable hAm).1 hfull

end SmallGammaGeodesics.CC
