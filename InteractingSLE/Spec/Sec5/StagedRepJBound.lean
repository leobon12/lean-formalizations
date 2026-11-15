/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJGlue
import InteractingSLE.Spec.Sec5.StagedRepJGam

/-!
# Prop 5.9's later root stages: the glued bound for the transfer to PIECES' candidates

Packet PROVE-STAGED-REPJ. The comparison clause of PIECES' candidate `(ℓ, t)` is transferred
(`compClauseK_transfer`) along the pair `gZ = (field in chart Q, counterflow history)` from the glued space of the root
coupling. The glued side must give, for every canonical past event `M ⊆ gamR` of `Gam`, the bound
`p μ(gZ⁻¹ M) ≤ μ(gZ⁻¹ M ∩ {gamObsJ ∘ gZ ∈ S})`. It comes from `compClauseK_glue` (S6's word entrance) with:

* the dilation factor `gC s = tf (rootLam s ·.2)` of PIECES' tree (a past event: `measurable_gC_candFilt`);
* two glued identifications, named here as statements:
  - **`GluePast`**: the `gZ`-preimages of `Gam`'s canonical past events inside `gamR` are, almost surely, events of the
    Galmarino filtration `candFilt` at time `0` inside the alive event (the past of a later stage is read before the
    restart);
  - **`GlueObs`**: almost surely on the alive event and `gZ⁻¹ gamR`, the canonical marks of `Gam`'s candidate are the
    dilated restarted marks and its killed samples are those of the dilated restarted word;

**`gamBound_of_glue`** assembles them. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real symmDiff
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open StagedRepLater StagedKCand StagedKill StagedRep StagedCand
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### Null-set completion of the usual augmentation -/

section Aug

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A measurable set almost surely equal to an event at time `0` is an event of the usual augmentation at `0`. -/
theorem measurableSet_usualAugmentation_of_ae {𝓕 : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {A D : Set Ω}
    (hA : MeasurableSet[𝓕 0] A) (hD : MeasurableSet D) (h : A =ᵐ[μ] D) :
    MeasurableSet[usualAugmentation 𝓕 μ 0] D := by
  have hAm : MeasurableSet A := 𝓕.le 0 _ hA
  have hN : MeasurableSet[usualAugmentation 𝓕 μ 0] (A ∆ D) :=
    Ito.measurableSet_usualAugmentation_of_null (hAm.symmDiff hD) (measure_symmDiff_eq_zero_iff.2 h) 0
  have hA' : MeasurableSet[usualAugmentation 𝓕 μ 0] A := Ito.le_usualAugmentation 𝓕 μ 0 _ hA
  have e : D = A ∆ (A ∆ D) := (symmDiff_symmDiff_cancel_left A D).symm
  rw [e]
  exact hA'.symmDiff hN

end Aug

section Bound

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

/-- The pair (field in chart `Q`, counterflow history) of a glued sample. -/
abbrev gZ (p : Ω × HistorySpace 0 0) : Gam := (qField x₀ κ h p.1, p.2)

/-- **The dilation factor of PIECES' tree** read from the glued history (Brownian time factor `λ⁻²`). -/
abbrev gC (s : ℝ≥0) (p : Ω × HistorySpace 0 0) : ℝ≥0 := tf (rootLam s p.2)

theorem measurable_tf : Measurable tf := (measurable_inv.pow_const 2).real_toNNReal

theorem rootLam_cfStop (r : ℝ≥0) (y : HistorySpace 0 0) : rootLam r (cfStop r y) = rootLam r y := by
  simp only [rootLam, cfDrv0_cfStop]

/-- **The glued past of a later stage** (named statement): the `gZ`-preimage of every canonical past event of
`Gam`'s candidate `(ℓ, t)` inside its reached event is almost surely an event of the Galmarino filtration at time `0`
inside the alive event. -/
def GluePast (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) : Prop :=
  ∀ M, MeasurableSet[gamQ h44 hκ hκ4 (x₀ := x₀) hb s ℓ t] M → M ⊆ gamR h44 hκ hκ4 (x₀ := x₀) hb s ℓ t →
    ∃ A, MeasurableSet[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0] A ∧
      A ⊆ gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s ∧ A =ᵐ[gMu x₀ (κ := κ) P h W ζ hG.1] gZ x₀ (κ := κ) h ⁻¹' M

/-- **The glued observable of a later stage** (named statement): almost surely on the alive event and on
`gZ⁻¹ gamR`, the canonical marks of `Gam`'s candidate `(ℓ, t)` are the `gC`-dilated restarted marks and its killed
samples are the samples of the `gC`-dilated restarted word. -/
def GlueObs (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Prop :=
  ∀ᵐ p ∂(gMu x₀ (κ := κ) P h W ζ hhm), p ∈ gA x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s →
    gZ x₀ (κ := κ) h p ∈ gamR h44 hκ hκ4 (x₀ := x₀) hb s ℓ t →
    (canonY (gamCand h44 hκ hκ4 (x₀ := x₀) hb s) (gamY0 h44 hκ hκ4 (x₀ := x₀) hb s) ℓ t
      (gZ x₀ (κ := κ) h p)).2 = (dilV (gC s p) (gStart x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s p)).2 ∧
    pieceSamp (gamCand h44 hκ hκ4 (x₀ := x₀) hb s ℓ t).W (gamCand h44 hκ hκ4 (x₀ := x₀) hb s ℓ t).VL
      (gamCand h44 hκ hκ4 (x₀ := x₀) hb s ℓ t).VR (gamCand h44 hκ hκ4 (x₀ := x₀) hb s ℓ t).ζ (gZ x₀ (κ := κ) h p) =
      samp (fun r => (√(gC s p : ℝ))⁻¹ * gW x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s (gC s p * r) p)
        (fun i r => (√(gC s p : ℝ))⁻¹ * gVL x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s i (gC s p * r) p)
        (fun j r => (√(gC s p : ℝ))⁻¹ * gVR x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s j (gC s p * r) p)
        (gζ x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s p / gC s p)

theorem rootXL_cfStop (r : ℝ≥0) (y : HistorySpace 0 0) :
    rootXL hκ hb x₀ r (cfStop r y) = rootXL hκ hb x₀ r y := by
  simp only [rootXL, cfDrv0_cfStop]

theorem rootXR_cfStop (r : ℝ≥0) (y : HistorySpace 0 0) :
    rootXR hκ hb x₀ r (cfStop r y) = rootXR hκ hb x₀ r y := by
  simp only [rootXR, cfDrv0_cfStop]

/-- The root start on `Gam` reads only the stopped history: its traces are events of `gamPast r`. -/
theorem measurableSet_gamPast_gamY0 (r : ℝ≥0) {S : Set (Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + 0)
    (rootNR (sourceWord (x₀ := x₀) hκ hb) + 0))} (hS : MeasurableSet S) :
    MeasurableSet[gamPast r] (univ ∩ gamY0 h44 hκ hκ4 (x₀ := x₀) hb r ⁻¹' S) := by
  set F : HistorySpace 0 0 → Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + 0)
      (rootNR (sourceWord (x₀ := x₀) hκ hb) + 0) := fun y =>
    ((0 : ℝ), fun i => rootLam r y * rootXL hκ hb x₀ r y i, fun j => rootLam r y * rootXR hκ hb x₀ r y j) with hF
  have hFm : Measurable F := measurable_const.prodMk
    ((measurable_pi_iff.2 fun i => (measurable_rootLam r).mul
      ((measurable_pi_apply i).comp (measurable_rootXL hκ hb r))).prodMk
    (measurable_pi_iff.2 fun j => (measurable_rootLam r).mul
      ((measurable_pi_apply j).comp (measurable_rootXR hκ hb r))))
  refine ⟨F ⁻¹' S, hFm hS, ?_⟩
  ext γ
  simp only [mem_preimage, mem_inter_iff, mem_univ, true_and, hF, rootLam_cfStop, rootXL_cfStop, rootXR_cfStop]
  rfl

include hκ4 in
/-- The dilation factor is an event of the Galmarino filtration at time `0` (it reads the stopped history). -/
theorem measurable_gC_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    Measurable[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0] (gC s) := by
  intro B hB
  have hm : Measurable fun y : HistorySpace 0 0 => tf (rootLam s y) := measurable_tf.comp (measurable_rootLam s)
  refine measurableSet_candFilt_of_stopD x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
    ((hm.comp measurable_snd) hB) fun q _ => ⟨univ ×ˢ ((fun y => tf (rootLam s y)) ⁻¹' B),
      MeasurableSet.univ.prod (hm hB), fun p _ _ _ => ?_⟩
  simp only [stopD, mem_prod, mem_univ, mem_preimage, true_and, rootLam_cfStop]

/-- The past of the glued clause: the usual augmentation of `candFilt` (for `μ[|A]`) at time `0`. -/
abbrev gQ0 (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) : MeasurableSpace (Ω × HistorySpace 0 0) :=
  usualAugmentation (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
    ((gMu x₀ (κ := κ) P h W ζ hG.1)[|gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s]) 0

include hκ4 in
/-- **The glued bound for the transfer of a later stage's comparison clause.** From the two glued identifications
`GluePast`, `GlueObs` (and PROVE-STAGED-S7's killed representation, through `compClauseK_glue`), every canonical
past event
`M ⊆ gamR` of `Gam` satisfies `p μ(gZ⁻¹ M) ≤ μ(gZ⁻¹ M ∩ {gamObsJ ∘ gZ ∈ S})` under every killed premise for the
stage word `(stageρL κ (rootρL κ c) ℓ, stageρR κ (rootρR κ c) ℓ)`. -/
theorem gamBound_of_glue (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) {s : ℝ≥0} (hs : 0 < s)
    (hpast : GluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
    (hobs : GlueObs x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) :
    ∀ S : Set (Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + (j + 1)) (rootNR (sourceWord (x₀ := x₀) hκ hb) + (j + 1)) ×
      Samp (rootNL (sourceWord (x₀ := x₀) hκ hb) + (j + 1)) (rootNR (sourceWord (x₀ := x₀) hκ hb) + (j + 1))),
      MeasurableSet S → ∀ p : ℝ≥0∞,
      CompPremiseFarK κ (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
        (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
        (farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ (j + 1))))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ (j + 1)))) univ S p →
      ∀ M, MeasurableSet[gamQ h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t] M → M ⊆ gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t →
        p * gMu x₀ (κ := κ) P h W ζ hG.1 (gZ x₀ (κ := κ) h ⁻¹' M) ≤
          gMu x₀ (κ := κ) P h W ζ hG.1 (gZ x₀ (κ := κ) h ⁻¹' M ∩
            {p' | gamObsJ h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t (gZ x₀ (κ := κ) h p') ∈ S}) := by
  classical
  intro S hS p hp M hM hMR
  set μ := gMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set A := gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s with hAdef
  by_cases hA0 : μ A = 0
  · obtain ⟨A', -, hAA, hAM⟩ := hpast M hM hMR
    have h0 : μ (gZ x₀ (κ := κ) h ⁻¹' M) = 0 := by
      rw [← measure_congr hAM]; exact measure_mono_null hAA hA0
    rw [h0, mul_zero]
    exact bot_le
  set 𝓐 := candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs with h𝓐
  have h𝓐𝓠 : 𝓐 0 ≤ gQ0 x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs := Ito.le_usualAugmentation 𝓐 (μ[|A]) 0
  have hAm𝓐 : MeasurableSet[𝓐 0] A := measurableSet_s3Alive_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0
  have hAm : MeasurableSet A := 𝓐.le 0 _ hAm𝓐
  have hZm : Measurable (gZ x₀ (κ := κ) h) :=
    (((measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hG.1).comp measurable_fst).prodMk
      measurable_snd
  -- a glued past event of `Gam` is an event of `𝓠₀`
  have hpast₀ : ∀ M', MeasurableSet[gamQ h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t] M' →
      M' ⊆ gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t →
      MeasurableSet[gQ0 x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs] (A ∩ gZ x₀ (κ := κ) h ⁻¹' M') := by
    intro M' hM' hM'R
    obtain ⟨A', hA', hAA, hAM⟩ := hpast M' hM' hM'R
    refine measurableSet_usualAugmentation_of_ae hA' (hAm.inter (hZm (gamQ_le h44 hκ hκ4 hb s (j + 1) t _ hM'))) ?_
    have h1 : A' =ᵐ[μ] A ∩ gZ x₀ (κ := κ) h ⁻¹' M' := by
      filter_upwards [hAM] with p' hp'
      show (p' ∈ A') = (p' ∈ A ∧ p' ∈ gZ x₀ (κ := κ) h ⁻¹' M')
      by_cases h' : p' ∈ A'
      · have : p' ∈ gZ x₀ (κ := κ) h ⁻¹' M' := by rw [← hp']; exact h'
        have hpA : p' ∈ A := hAA h'
        simp only [h', hpA, this, and_self]
      · have : p' ∉ gZ x₀ (κ := κ) h ⁻¹' M' := by rw [← hp']; exact h'
        simp only [h', this, and_false]
    exact cond_absolutelyContinuous.ae_eq h1
  have hRm := measurableSet_canonR (𝓑 := gamPast s) (cand := gamCand h44 hκ hκ4 (x₀ := x₀) hb s) (G := ratGrid)
    (hnL := rootNL_pos _) (hnR := rootNR_pos _) (y₀ := gamY0 h44 hκ hκ4 (x₀ := x₀) hb s) MeasurableSet.univ (j + 1) t
  have hD : MeasurableSet[gQ0 x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs]
      (A ∩ gZ x₀ (κ := κ) h ⁻¹' gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t) :=
    hpast₀ _ hRm le_rfl
  -- the start
  set y' : Ω × HistorySpace 0 0 → Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + (j + 1))
      (rootNR (sourceWord (x₀ := x₀) hκ hb) + (j + 1)) := fun p' =>
    if p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t then
      canonY (gamCand h44 hκ hκ4 (x₀ := x₀) hb s) (gamY0 h44 hκ hκ4 (x₀ := x₀) hb s) (j + 1) t (gZ x₀ (κ := κ) h p')
    else ((0 : ℝ), (dilV (gC s p') (gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p')).2) with hy'def
  have hC : Measurable[gQ0 x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs] (gC s) :=
    (measurable_gC_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs).mono h𝓐𝓠 le_rfl
  have hg : Measurable[gQ0 x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs] fun p' => ((0 : ℝ),
      (dilV (gC s p') (gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p')).2) :=
    measurable_const.prodMk (measurable_dilV hC
      ((measurable_gStart_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs).mono h𝓐𝓠 le_rfl)).snd
  have hy' : Measurable[gQ0 x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs] y' := by
    intro T hT
    have e : y' ⁻¹' T = (A ∩ gZ x₀ (κ := κ) h ⁻¹' (gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t ∩
        canonY (gamCand h44 hκ hκ4 (x₀ := x₀) hb s) (gamY0 h44 hκ hκ4 (x₀ := x₀) hb s) (j + 1) t ⁻¹' T)) ∪
        ((A ∩ gZ x₀ (κ := κ) h ⁻¹' gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t)ᶜ ∩
          (fun p' => ((0 : ℝ), (dilV (gC s p') (gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p')).2)) ⁻¹' T) := by
      ext p'
      by_cases hp' : p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t
      · have hy1 : y' p' = canonY (gamCand h44 hκ hκ4 (x₀ := x₀) hb s) (gamY0 h44 hκ hκ4 (x₀ := x₀) hb s) (j + 1) t
            (gZ x₀ (κ := κ) h p') := by simp only [hy'def, hp', ↓reduceIte]
        rw [mem_preimage, hy1]
        exact ⟨fun h1 => Or.inl ⟨hp'.1, hp'.2, h1⟩,
          fun h1 => h1.elim (fun h2 => h2.2.2) fun h2 => absurd hp' h2.1⟩
      · have hy1 : y' p' = ((0 : ℝ), (dilV (gC s p') (gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p')).2) := by
          simp only [hy'def, hp', ↓reduceIte]
        rw [mem_preimage, hy1]
        exact ⟨fun h1 => Or.inr ⟨hp', h1⟩,
          fun h1 => h1.elim (fun h2 => absurd ⟨h2.1, h2.2.1⟩ hp') fun h2 => h2.2⟩
    rw [e]
    refine (hpast₀ _ ?_ inter_subset_left).union (hD.compl.inter (hg hT))
    exact measurableSet_canonR_inter_canonY (isRegFam_gamCand h44 hκ hκ4 hb s) (measurable_gamY0 h44 hκ hκ4 hb s)
      MeasurableSet.univ (fun S' hS' => measurableSet_gamPast_gamY0 x₀ h44 hκ hκ4 hb s hS') (j + 1) t T hT
  have hy'e : ∀ᵐ p' ∂μ, p' ∈ A →
      (y' p').2 = (dilV (gC s p') (gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p')).2 := by
    filter_upwards [hobs] with p' hp' hpA
    by_cases hR : gZ x₀ (κ := κ) h p' ∈ gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t
    · have hm : p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t := ⟨hpA, hR⟩
      simp only [hy'def, hm, ↓reduceIte]
      exact (hp' hpA hR).1
    · have hm : p' ∉ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t := fun h' => hR h'.2
      simp only [hy'def, hm, ↓reduceIte]
  have hglue := compClauseK_glue x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs hA0 hC
    (fun p' => tf_ne_zero (rootLam_pos s p'.2)) hy' hy'e
  refine bound_of_compClauseK hglue (fun M' hM' hM'R => ?_) ?_ S hS p hp M hM hMR
  · obtain ⟨A', hA', hAA, hAM⟩ := hpast M' hM' hM'R
    exact ⟨A', h𝓐𝓠 _ hA', hAA, hAM⟩
  · filter_upwards [hobs] with p' hp' hpA hR
    have hm : p' ∈ A ∩ gZ x₀ (κ := κ) h ⁻¹' gamR h44 hκ hκ4 (x₀ := x₀) hb s (j + 1) t := ⟨hpA, hR⟩
    simp only [hy'def, hm, ↓reduceIte, gamObsJ]
    rw [(hp' hpA hR).2]

end Bound

end InteractingSLE.Sec5.CrossCond.StagedRepJ
