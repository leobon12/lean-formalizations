/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStaged
import InteractingSLE.Spec.Sec5.CrossCondMartFwd

/-!
# The staged cross-conditioning law on the θ-glued space: any flow-side set with the counterflow hull

Packet PROVE-CROSSCOND-STAGED. On the glued space of `CrossCond.Theta` (the field `h` of a flow line from the root,
an independent centred counterflow of `h − θχ` glued through its kernel `k` given the field), the flow side of the
revealed union is here an **arbitrary random set read from a recorded history** `Yf` of the first coordinate:

* `𝔄 (Yf ω)` — e.g. the hull of a staged prefix `α₁ ∪ ⋯ ∪ α_k ∪ β[0, t']` with `Yf` its stopped labelled record, or
  (the root instance, `CrossCond.Theta`) the flow hull `hullAt q (killedHistory W VL VR ζ ω)`;
* its locality (`IsLocalSet`, and history-avoidance locality for the marks `σ(Yf)|𝔐f`) is an input on `(Ω, P)`: for a
  staged prefix this is the staged entrance locality (`Restart.StagedEntrance`, PROVE-STAGEDLOC; SBSEW's
  `isHistoryAvoidanceLocal_stage_of_path`).

Results:

* **`isHistoryAvoidanceLocal_union_cfGlueT`**: the union `𝔄 (Yf p.1) ∪ cfHullQ s p.2` is history-avoidance local on
  the glued space for the joint marks `σ(Yf ∘ fst, snd)|𝔐f ⊗ 𝔖_s` (Proposition 3.7 with retained histories; the two
  records are conditionally independent given the field by the glue);
* **`isLocalSet_union_cfGlueT`**: the individual sets and the union are local sets on the glued space;
* **`ae_condExp_union_cfGlueT_add_eq`** (the staged mean identification on the θ-glued space): given the flow side's own
  local-set mean with an explicit harmonic representative `wA` (for a staged prefix: its own mean in the chart of the
  current tip) and the per-sample union datum `HasUnionWordBoundary` against the explicit counterflow mean `cfMeanQ`,
  almost surely `E[(h − 𝔥₀)(φ) | 𝒜_{A ∪ G_s} ∨ σ(Yf, G-history)] + ∫ 𝔥₀ φ = ∫ v φ`, `v` the surviving-word candidate in
  the joint chart (current tip ↦ 0, counterflow tip ↦ ∞).

Conditional helpers with distinct names; they replace no source theorem. The root coupling `hC` only supplies the
field's law (and the counterflow's regularity through `CfThetaBounds`); the flow side is arbitrary. R48: nothing here
uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.Staged

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets Theta
open Theorem14.SB.SewGerm (HasUnionWordBoundary HasSurvivingWordBoundary)

/-- A pair of records generates the supremum of the two record σ-algebras. -/
theorem comap_pair_prod {α γ δ : Type*} (F : α → γ) (G : α → δ) (m₁ : MeasurableSpace γ)
    (m₂ : MeasurableSpace δ) : (m₁.prod m₂).comap (fun a => (F a, G a)) = m₁.comap F ⊔ m₂.comap G := by
  rw [MeasurableSpace.prod, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

section Glue

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}
  {γ : Type*} {𝔐f : MeasurableSpace γ} [mγ : MeasurableSpace γ] {Yf : Ω → γ} {𝔄 : γ → Set ℂ}

/-- **The revealed union of a recorded flow-side set and the counterflow hull is history-avoidance local on the
θ-glued space** (θ-version of `isHistoryAvoidanceLocal_cfGlueT` with an arbitrary flow side): if `𝔄 ∘ Yf` is
history-avoidance local on `(Ω, P)` for the marks `σ(Yf)|𝔐f`, then `𝔄 (Yf p.1) ∪ cfHullQ s p.2` is for the joint
marks `σ(Yf ∘ fst, snd)|𝔐f ⊗ 𝔖_s`. -/
theorem isHistoryAvoidanceLocal_union_cfGlueT (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hYf : Measurable Yf) (h𝔐f : 𝔐f ≤ mγ) (h𝔄 : Measurable[mγ, hittingSigma] 𝔄)
    (hAloc : IsHistoryAvoidanceLocal (𝔐f.comap Yf) (fun ω => 𝔄 (Yf ω))
      (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P) (s : ℝ≥0) :
    IsHistoryAvoidanceLocal ((𝔐f.prod (stopSigma s)).comap fun p : Ω × HistorySpace 0 0 => (Yf p.1, p.2))
      (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1) ∪ cfHullQ s p.2)
      (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hX₀ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hh₂m := CfRegQ.measurable_of_isCenteredCounterflowDriver hcf
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hXm : Measurable fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω)) := (measurable_cenTT κ θ u₀).comp hXm₀
  have hY₂m : Measurable (cfHistory W₂ ζ₂) := measurable_cfHistory hX₀
  have hX₂m : Measurable fun ω => cenTT κ θ u₀ (h₂ ω) := (measurable_cenTT κ θ u₀).comp hh₂m
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  -- the flow side's record, transported along `fst`
  have hlaw₁ : μ.map (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), Yf p.1)) =
      P.map (fun ω => (cenTT κ θ u₀ (cfFieldT κ θ (h ω)), Yf ω)) := by
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), Yf p.1)) =
        (fun ω => (cenTT κ θ u₀ (cfFieldT κ θ (h ω)), Yf ω)) ∘ Prod.fst from rfl,
      ← Measure.map_map (hXm.prodMk hYf) measurable_fst, hμ, glueMeasure_fst k hXm₀]
  have hA₁ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := 𝔐f) hXm hYf (hXm.comp measurable_fst)
    (hYf.comp measurable_fst) hlaw₁ h𝔄 h𝔐f hAloc
  -- the counterflow's record, transported along the law of `(h − θχ, history)`
  have hlaw₂ : μ.map (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), p.2)) =
      P₂.map (fun ω => (cenTT κ θ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) := by
    have hT : Measurable fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2) :=
      ((measurable_cenTT κ θ u₀).comp measurable_fst).prodMk measurable_snd
    have hpair : Measurable fun p : Ω × HistorySpace 0 0 => (cfFieldT κ θ (h p.1), p.2) :=
      (hXm₀.comp measurable_fst).prodMk measurable_snd
    have hpair₂ : Measurable fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) := hh₂m.prodMk hY₂m
    rw [show (fun p : Ω × HistorySpace 0 0 => (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)), p.2)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2)) ∘
          fun p => (cfFieldT κ θ (h p.1), p.2) from rfl,
      show (fun ω => (cenTT κ θ u₀ (h₂ ω), cfHistory W₂ ζ₂ ω)) =
        (fun r : DistOn upperHalfPlaneOpens × HistorySpace 0 0 => (cenTT κ θ u₀ r.1, r.2)) ∘
          fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω) from rfl,
      ← Measure.map_map hT hpair, ← Measure.map_map hT hpair₂, hμ, glueMeasure_map_pair hXm₀ k, hlaw, hk]
  have hA₂ := isHistoryAvoidanceLocal_of_map_eq (𝔐 := stopSigma s) hX₂m hY₂m (hXm.comp measurable_fst)
    measurable_snd hlaw₂ (measurable_cfHullQ s) (stopSigma_le _)
    (isHistoryAvoidanceLocal_cfHullQT hcf hκ hreg₂ hu₀.1 s)
  -- the union
  have hci := condIndepEv_glue_fst (μ := P) k hXm₀
  rw [← comap_cenTT_glue κ θ u₀ (fun ω => cfFieldT κ θ (h ω))] at hci
  have hℋ₁ : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => Yf p.1) 𝔐f ≤
      MeasurableSpace.comap Prod.fst mΩ := by
    rw [show (fun p : Ω × HistorySpace 0 0 => Yf p.1) = Yf ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono ((MeasurableSpace.comap_mono h𝔐f).trans hYf.comap_le)
  have hℋ₂ : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => p.2) (stopSigma s) ≤
      MeasurableSpace.comap Prod.snd inferInstance :=
    MeasurableSpace.comap_mono (stopSigma_le _)
  rw [comap_pair_prod]
  exact isHistoryAvoidanceLocal_union measurable_fst.comap_le measurable_snd.comap_le hℋ₁ hℋ₂
    ((h𝔄.comp hYf).comp (comap_measurable Prod.fst))
    ((measurable_cfHullQ s).comp (comap_measurable Prod.snd)) hci hA₁ hA₂

/-- **The inputs of the generic glued-union theorems on the θ-glued space**: the centred field is a zero-boundary
GFF, the flow-side set and the counterflow hull are local on the glued space, the flow side's mean pulls back, the
counterflow hull has a local-set mean represented by `cfMeanQ`, and the union datum holds for every pair of harmonic
representatives of the two individual means. -/
theorem cfGlueT_union_inputs (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hYf : Measurable Yf) (h𝔄 : Measurable[mγ, hittingSigma] 𝔄)
    (hAl : IsLocalSet (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P)
    {gA : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P gA)
    {wA : Ω → ℂ → ℝ} (hwA : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (wA ω) (H \ 𝔄 (Yf ω)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ 𝔄 (Yf ω) → gA ω φ = ∫ z, wA ω z * φ z)
    (s : ℝ≥0) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    (v : Ω × HistorySpace 0 0 → ℂ → ℝ) (b : Ω × HistorySpace 0 0 → ℝ → ℝ)
    (jumps : Ω × HistorySpace 0 0 → Finset ℝ) {D : Set (Ω × HistorySpace 0 0)}
    (hword : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ D → HasUnionWordBoundary (𝔄 (Yf p.1)) (cfHullQ s p.2) u₀ (v p) (wA p.1)
        (cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) u' s p.2)
        (chiC κ) (b p) (jumps p)) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P ∧
    IsLocalSet (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1))
      (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) ∧
    IsLocalSet (fun p : Ω × HistorySpace 0 0 => cfHullQ s p.2)
      (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) ∧
    IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1))
      (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) (fun p => gA p.1) ∧
    ∃ gG : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun p : Ω × HistorySpace 0 0 => cfHullQ s p.2)
        (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))
        (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) gG ∧
      ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
        p ∈ D → ∀ wA' wG' : ℂ → ℝ,
        InnerProductSpace.HarmonicOnNhd wA' (H \ 𝔄 (Yf p.1)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ 𝔄 (Yf p.1) → gA p.1 φ = ∫ z, wA' z * φ z) →
        InnerProductSpace.HarmonicOnNhd wG' (H \ cfHullQ s p.2) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cfHullQ s p.2 → gG p φ = ∫ z, wG' z * φ z) →
        HasUnionWordBoundary (𝔄 (Yf p.1)) (cfHullQ s p.2) u₀ (v p) wA' wG' (chiC κ) (b p) (jumps p) := by
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hF : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P := by
    have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
      funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
    rw [e]
    exact WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  have hAm : Measurable[mΩ, hittingSigma] fun ω => 𝔄 (Yf ω) := h𝔄.comp hYf
  have hAg := IsLocalSet.glue_fst hXm₀ k (T := cenTT κ θ u₀) hAl
  have hGg := IsLocalSet.glue_snd hXm₀ k (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)
    (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw hk
    (measurable_cenTT κ θ u₀) (measurable_cfHullQ s) MeasurableSet.univ (fun y _ => cfHullQ_relClosed s y)
    (Eventually.of_forall fun _ => mem_univ _) (isLocalSet_cfHullQ_cenTT hcf hreg₂ hu₀.1 s)
  have hgA' := IsLocalSetMean.comp measurable_fst (glueMeasure_fst (μ := P) k hXm₀) hAm
    ((measurable_cenTT κ θ u₀).comp hXm₀) hgA
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_pathT hC hκ hcf hreg₂ hlaw hk hu₀ s hu'
  refine ⟨hF, hAg, hGg, hgA', gG, hgG, ?_⟩
  filter_upwards [hword, ae_glue_fst (μ := P) k hXm₀ hwA, hidG, ae_glue_fst (μ := P) k hXm₀ hAl.2.1, hGg.2.1]
    with p hwp hwAp hidGp hoA hoG hpD wA' wG' hA' hrA' hG' hrG'
  have e₁ : EqOn (wA p.1) wA' (H \ 𝔄 (Yf p.1)) := eqOn_of_rep hoA.2 sdiff_subset hwAp.1 hA' hwAp.2 hrA'
  have e₂ := eqOn_of_rep hoG.2 sdiff_subset
    (harmonicOnNhd_cfMeanQ κ _ (forceJumpFinset xL xR) hu'.1 s p.2) hG' hidGp hrG'
  exact HasUnionWordBoundary.congr (hwp hpD) (e₁.mono (sdiff_subset_sdiff_right subset_union_left))
    (e₂.mono (sdiff_subset_sdiff_right subset_union_right))

/-- **The staged mean identification on the θ-glued space.** Let `𝔄 ∘ Yf` be a local set of the centred field on
`(Ω, P)`, history-avoidance local for its record, with own local-set mean `gA` represented by the harmonic `wA`
(for a staged prefix: its own mean read in the chart of the current tip). If almost surely on `D` the union datum
`HasUnionWordBoundary` holds for `wA` and the explicit counterflow mean `cfMeanQ` with the candidate `v` (the
surviving-word mean in the joint chart), then almost surely on `D`, for every test function `φ` supported off the
union, `E[(h − 𝔥₀)(φ) | 𝒜_{A ∪ G_s} ∨ σ(Yf, G-history)] + ∫ 𝔥₀ φ = ∫ v φ`. -/
theorem ae_condExp_union_cfGlueT_add_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hYf : Measurable Yf) (h𝔐f : 𝔐f ≤ mγ) (h𝔄 : Measurable[mγ, hittingSigma] 𝔄)
    (hAl : IsLocalSet (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P)
    (hAloc : IsHistoryAvoidanceLocal (𝔐f.comap Yf) (fun ω => 𝔄 (Yf ω))
      (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (𝔄 (Yf ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (𝔄 (Yf ω))) z))
    {gA : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P gA)
    {wA : Ω → ℂ → ℝ} (hwA : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (wA ω) (H \ 𝔄 (Yf ω)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ 𝔄 (Yf ω) → gA ω φ = ∫ z, wA ω z * φ z)
    (s : ℝ≥0) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    (v : Ω × HistorySpace 0 0 → ℂ → ℝ) (b : Ω × HistorySpace 0 0 → ℝ → ℝ)
    (jumps : Ω × HistorySpace 0 0 → Finset ℝ) {D : Set (Ω × HistorySpace 0 0)}
    (hword : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ D → HasUnionWordBoundary (𝔄 (Yf p.1)) (cfHullQ s p.2) u₀ (v p) (wA p.1)
        (cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) u' s p.2)
        (chiC κ) (b p) (jumps p))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ D → tsupport φ ⊆ H \ (𝔄 (Yf p.1) ∪ cfHullQ s p.2) →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
          germSigma (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1) ∪ cfHullQ s p.2)
            (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            (𝔐f.prod (stopSigma s)).comap (fun p : Ω × HistorySpace 0 0 => (Yf p.1, p.2))] p +
        ∫ z, u₀ z * φ z = ∫ z, v p z * φ z := by
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨hF, hAg, hGg, hgA', gG, hgG, hword'⟩ := cfGlueT_union_inputs hC hκ hθb hcf hlaw hk hu₀ hYf h𝔄 hAl
    hgA hwA s hu' v b jumps hword
  have hmark := isHistoryAvoidanceLocal_union_cfGlueT hC hκ hθb hcf hlaw hk hu₀ hYf h𝔐f h𝔄 hAloc s
  have hpair : Measurable fun p : Ω × HistorySpace 0 0 => (Yf p.1, p.2) :=
    (hYf.comp measurable_fst).prodMk measurable_snd
  have h𝔐 : 𝔐f.prod (stopSigma s) ≤ (inferInstance : MeasurableSpace (γ × HistorySpace 0 0)) :=
    sup_le_sup (MeasurableSpace.comap_mono h𝔐f) (MeasurableSpace.comap_mono (stopSigma_le s))
  exact ae_condExp_union_glue_add_eq_of_wordBoundary hXm₀ (measurable_cenTT κ θ u₀) (measurable_cenTT' κ θ u₀)
    (cenTT'_cenTT κ θ u₀) hF (h𝔄.comp hYf) (measurable_cfHullQ s) hAg hGg (ae_glue_fst (μ := P) k hXm₀ hunb)
    (Eventually.of_forall fun p => not_isBounded_lowerUnion_image_negInv (isHPHull_hullAt _ _)) hgA' hgG
    hpair h𝔐 hmark hu₀.1 hu₀.2.1 v (chiC κ) b jumps hword' φ

/-- **The conditional law given the revealed union on the θ-glued space** (characteristic-function form of
`ae_condExp_union_cfGlueT_add_eq`): given the germs of `𝔄 (Yf) ∪ G_s` and both records, the field `h` is, off the
union, the zero-boundary GFF of the complement plus the surviving-word mean `v` (the input of the chart clause
`Sec7.Lemma71D.IsChartCouplingCharFunConst` of the next piece). -/
theorem ae_condExp_cexp_union_cfGlueT_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hYf : Measurable Yf) (h𝔐f : 𝔐f ≤ mγ) (h𝔄 : Measurable[mγ, hittingSigma] 𝔄)
    (hAl : IsLocalSet (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P)
    (hAloc : IsHistoryAvoidanceLocal (𝔐f.comap Yf) (fun ω => 𝔄 (Yf ω))
      (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P)
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (𝔄 (Yf ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (𝔄 (Yf ω))) z))
    {gA : Ω → DistOn upperHalfPlaneOpens}
    (hgA : IsLocalSetMean (fun ω => 𝔄 (Yf ω)) (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) P gA)
    {wA : Ω → ℂ → ℝ} (hwA : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (wA ω) (H \ 𝔄 (Yf ω)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ 𝔄 (Yf ω) → gA ω φ = ∫ z, wA ω z * φ z)
    (s : ℝ≥0) {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    (v : Ω × HistorySpace 0 0 → ℂ → ℝ) (b : Ω × HistorySpace 0 0 → ℝ → ℝ)
    (jumps : Ω × HistorySpace 0 0 → Finset ℝ) {D : Set (Ω × HistorySpace 0 0)}
    (hword : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ D → HasUnionWordBoundary (𝔄 (Yf p.1)) (cfHullQ s p.2) u₀ (v p) (wA p.1)
        (cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) u' s p.2)
        (chiC κ) (b p) (jumps p))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ D → tsupport φ ⊆ H \ (𝔄 (Yf p.1) ∪ cfHullQ s p.2) →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1) ∪ cfHullQ s p.2)
            (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            (𝔐f.prod (stopSigma s)).comap (fun p : Ω × HistorySpace 0 0 => (Yf p.1, p.2))] p =
        Complex.exp (Complex.I * ((∫ z, v p z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov (H \ relClosureH (𝔄 (Yf p.1) ∪ cfHullQ s p.2)) φ φ) :
            ℝ) : ℂ) := by
  have hXm₀ : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  obtain ⟨hF, hAg, hGg, hgA', gG, hgG, hword'⟩ := cfGlueT_union_inputs hC hκ hθb hcf hlaw hk hu₀ hYf h𝔄 hAl
    hgA hwA s hu' v b jumps hword
  have hmark := isHistoryAvoidanceLocal_union_cfGlueT hC hκ hθb hcf hlaw hk hu₀ hYf h𝔐f h𝔄 hAloc s
  have hpair : Measurable fun p : Ω × HistorySpace 0 0 => (Yf p.1, p.2) :=
    (hYf.comp measurable_fst).prodMk measurable_snd
  have h𝔐 : 𝔐f.prod (stopSigma s) ≤ (inferInstance : MeasurableSpace (γ × HistorySpace 0 0)) :=
    sup_le_sup (MeasurableSpace.comap_mono h𝔐f) (MeasurableSpace.comap_mono (stopSigma_le s))
  have hcf' := ae_condExp_cexp_union_glue_eq_of_wordBoundary hXm₀ (measurable_cenTT κ θ u₀)
    (measurable_cenTT' κ θ u₀) (cenTT'_cenTT κ θ u₀) hF (h𝔄.comp hYf) (measurable_cfHullQ s) hAg hGg
    (ae_glue_fst (μ := P) k hXm₀ hunb)
    (Eventually.of_forall fun p => not_isBounded_lowerUnion_image_negInv (isHPHull_hullAt _ _)) hgA' hgG
    hpair h𝔐 hmark hu₀.1 hu₀.2.1 v (chiC κ) b jumps hword' φ
  -- the constant `e^{i ∫ 𝔥₀ φ}` is pulled out
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)) φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, cenTT_cfFieldT, ← Complex.exp_add]
    rw [show h p.1 - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ =
      centredField h u₀ p.1 from rfl, centredField_apply h hu₀.1 p.1 φ]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ :=
    (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))) c
    (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (cenTT κ θ u₀ (cfFieldT κ θ (h p.1)) φ : ℂ)))
    (germSigma (fun p : Ω × HistorySpace 0 0 => 𝔄 (Yf p.1) ∪ cfHullQ s p.2)
      (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
      (𝔐f.prod (stopSigma s)).comap (fun p : Ω × HistorySpace 0 0 => (Yf p.1, p.2)))
  rw [← e] at hpull
  filter_upwards [hcf', hpull] with p h1 h2 hpD hφ
  rw [h2, Pi.smul_apply, smul_eq_mul]
  refine (congrArg (c * ·) (h1 hpD hφ)).trans ?_
  rw [hc, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### The root instance: one flow line from the root is a flow side -/

/-- **The root instance of the staged mean identification.** For the flow line of the root coupling itself (stage 1
of a staged prefix), every flow-side input of `ae_condExp_union_cfGlueT_add_eq` holds: its hull at time `q` is local
and history-avoidance local for its stopped record (`isLocalSet_hullAt_flowT`, `isHistoryAvoidanceLocal_hullAt_flowT`),
an `ℍ`-hull, and its own local-set mean is the coupling mean `couplingMean κ W q u − 𝔥₀`
(`Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull`). The marks are `cfGlueMarks`. Only the per-sample union
datum remains. -/
theorem ae_condExp_union_cfGlueT_add_eq_flowHull (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (q s : ℝ≥0)
    {u : Ω → ℂ → ℝ} (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (u ω))
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR)) u')
    (v : Ω × HistorySpace 0 0 → ℂ → ℝ) (b : Ω × HistorySpace 0 0 → ℝ → ℝ)
    (jumps : Ω × HistorySpace 0 0 → Finset ℝ) {D : Set (Ω × HistorySpace 0 0)}
    (hword : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ D → HasUnionWordBoundary (hullAt q (killedHistory W VL VR ζ p.1)) (cfHullQ s p.2) u₀ (v p)
        (fun z => couplingMean κ (fun r : ℝ => W r.toNNReal p.1) q (u p.1) z - u₀ z)
        (cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) (forceJumpFinset xL xR) u' s p.2)
        (chiC κ) (b p) (jumps p))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ D → tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2) →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
            (fun p : Ω × HistorySpace 0 0 => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔
            cfGlueMarks W VL VR ζ q s] p +
        ∫ z, u₀ z * φ z = ∫ z, v p z * φ z := by
  have hX := hC.2.2.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hAm : Measurable[mΩ, hittingSigma] fun ω => hullAt q (killedHistory W VL VR ζ ω) :=
    (measurable_hullAt q).comp hYm
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [Word49.ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC] with ω hω using hω.1
  -- the own mean of the flow hull on `Ω`
  have hh0 := WholeField.isZeroBoundaryGFF_centredField hC hu₀
  have e : (fun ω => cenTT κ θ u₀ (cfFieldT κ θ (h ω))) = WholeField.centredField h u₀ :=
    funext fun ω => cenTT_cfFieldT κ θ u₀ (h ω)
  have hAl := isLocalSet_hullAt_flowT (θ := θ) hC hζ hu₀ q
  have hloc : IsLocalSet (fun ω => hullAt q (killedHistory W VL VR ζ ω)) (WholeField.centredField h u₀) P :=
    e ▸ hAl
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  have hτζ : ∀ᵐ ω ∂P, (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hgood := Aux50Hit.ae_isGoodPath hC.1 hζ
  have hAK : ∀ᵐ ω ∂P, hullAt q (killedHistory W VL VR ζ ω) =
      (fun z : ℂ => z + ((0 : ℝ) : ℂ)) '' fwdHull (fun s : ℝ => W s.toNNReal ω)
        (((fun _ : Ω => ((q : ℝ≥0) : WithTop ℝ≥0)) ω).untopD 0 : ℝ≥0) := by
    filter_upwards [hgood] with ω hg
    rw [WithTop.untopD_coe, hullAt, Aux50Hit.regHull_stopHistory_cstop hg q]
    simp only [Complex.ofReal_zero, add_zero, image_id']
    rfl
  have hid := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull (x := 0) (c := 0) hC hκ
    (fun ω => by simpa only [zero_mul] using Sec7.StripSysField.isTranslateAddConst_zero_self (h ω) 0) hh0 hu₀.1
    hu₀ (fun z _ => by simp only [Complex.ofReal_zero, add_zero]) hX (isStoppingTime_const _ q) hτζ hAm hAK hg
    (u := u) (by simpa only [WithTop.untopD_coe] using hu)
  have hwA : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd
      (fun z => couplingMean κ (fun r : ℝ => W r.toNNReal ω) q (u ω) z - u₀ z)
        (H \ hullAt q (killedHistory W VL VR ζ ω)) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ hullAt q (killedHistory W VL VR ζ ω) →
        g ω φ = ∫ z, (couplingMean κ (fun r : ℝ => W r.toNNReal ω) q (u ω) z - u₀ z) * φ z := by
    filter_upwards [hid, hAK, hζ, hC.1.2.2.2.2] with ω hω hAKω hζω hpath
    have hK : hullAt q (killedHistory W VL VR ζ ω) = fwdHull (fun r : ℝ => W r.toNNReal ω) q := by
      rw [hAKω, WithTop.untopD_coe]
      simp only [Complex.ofReal_zero, add_zero, image_id']
    have hqζ : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
    have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean_rpath (κ := κ) hpath.2.2.2.1 hqζ (hu ω).1
    refine ⟨fun z hz => ?_, fun φ hφ => ?_⟩
    · rw [hK] at hz
      exact (hcm z hz).sub (hu₀.1 z hz.1)
    · rw [hω φ hφ]
      simp only [WithTop.untopD_coe, Complex.ofReal_zero, sub_zero]
  have hmain := ae_condExp_union_cfGlueT_add_eq (𝔄 := hullAt q) (Yf := killedHistory W VL VR ζ) (𝔐f := stopSigma q)
    hC hκ hθb hcf hlaw hk hu₀ hYm (stopSigma_le q) (measurable_hullAt q) hAl
    (isHistoryAvoidanceLocal_hullAt_flowT hC hκ hζ hu₀ q)
    (Eventually.of_forall fun ω => not_isBounded_lowerUnion_of_isHPHull (isHPHull_hullAt _ _)) (e ▸ hg) hwA s hu'
    v b jumps hword φ
  rwa [comap_pair_prod] at hmain

end Glue

end InteractingSLE.Sec5.CrossCond.Staged
