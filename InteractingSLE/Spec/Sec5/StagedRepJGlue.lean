/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJTools
import InteractingSLE.Spec.Sec5.StagedS7Rep

/-!
# Prop 5.9's later root stages: the killed comparison clause on the glued space

Packet PROVE-STAGED-REPJ. PROVE-STAGED-S6 proved, for PIECES' candidate `(ℓ, t)` on the glued space of the root
coupling and conditioned on the alive event `A` of its last switch (`μ_A = μ[|A]`), the word entrance of the restarted
word in tree order (`StagedS6.exists_isWordEntrance_cand`). Here it is turned into the comparison clause of the killed
stage law (`CompClauseK`, ruling R78) under `μ` itself:

* the glued objects of the candidate (`gMu`, `gA`, `gW`, `gVL`, `gVR`, `gζ`,
  the start `gStart`) as abbreviations;
* **`compClauseK_glue`**: for every time factor `C ≠ 0` and every start `y'` measurable for the usual augmentation of
  `candFilt` at time `0` (`𝓠₀`), with the marks of `y'` the `C`-dilated marks of the restarted start, the dilated
  restarted word obeys the comparison clause under `μ` for the past `𝓠₀` and the stage event `A`. Route: S7's killed
  representation (past enlarged to the usual augmentation), `IsStoppedRep.compClauseK_dil` (frozen dilation),
  `CompClauseK.of_prod_fst`, `CompClauseK.of_cond`.

The killed representation itself (strict start, no threshold at time `0`, kill at the far marks with left limits, trace,
PIECES' stage weights) is PROVE-STAGED-S7's `StagedS7.exists_isKilledStageRep_cand`. R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`; the only named input of the chain
is R74's `h44`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedRepJ

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open StagedRepLater StagedKCand StagedKill StagedRep
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open StagedFinal (imgStageRhoL imgStageRhoR)

section Glue

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

/-! ### The glued objects of the candidate `(ℓ, t)` -/

/-- The glued space's measure (the root coupling's field glued with the counterflow history). -/
abbrev gMu (hhm : Measurable h) : Measure (Ω × HistorySpace 0 0) := candMu x₀ (κ := κ) P h W ζ hhm

/-- The alive event of the candidate's last switch. -/
abbrev gA (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  s3Alive s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted driver. -/
abbrev gW (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  s3W s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted left marks in tree order. -/
abbrev gVL (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) :
    Fin (rootNL (sourceWord (x₀ := x₀) hκ hb) + ℓ) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs ℓ t) ℓ s
    (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted right marks in tree order. -/
abbrev gVR (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) :
    Fin (rootNR (sourceWord (x₀ := x₀) hκ hb) + ℓ) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTs ℓ t) ℓ s
    (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted lifetime. -/
abbrev gζ (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Ω × HistorySpace 0 0 → ℝ≥0∞ :=
  s3ζ s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted start (driver `0`, the initial marks in tree order). -/
abbrev gStart (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (p : Ω × HistorySpace 0 0) :
    Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + ℓ) (rootNR (sourceWord (x₀ := x₀) hκ hb) + ℓ) :=
  ((0 : ℝ), fun i => gVL x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s i 0 p,
    fun j => gVR x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s j 0 p)

include hκ4 in
/-- The restarted start is an event of the Galmarino filtration at time `0`. -/
theorem measurable_gStart_candFilt (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    Measurable[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0]
      (gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s) := by
  have hL0 : ∀ i, Measurable[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0]
      fun p => gVL x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s i 0 p := fun i =>
    (stronglyAdapted_s6VL_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
      (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) i 0).measurable
  have hR0 : ∀ j, Measurable[candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0]
      fun p => gVR x₀ h44 hκ hκ4 hb P h W ζ hG.1 ℓ t s j 0 p := fun j =>
    (stronglyAdapted_s6VR_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs
      (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) j 0).measurable
  exact measurable_const.prodMk (((@measurable_pi_iff _ _ _
    (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0) _ _).2 hL0).prodMk
    ((@measurable_pi_iff _ _ _ (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0) _ _).2 hR0))

include hκ4 in
/-- **The killed comparison clause of the dilated restarted word on the glued space.** For PIECES' candidate
`(j + 1, t)` with a non-null alive event, every time factor `C ≠ 0` and start `y'` that are
measurable for `𝓠₀ = usualAugmentation candFilt μ_A 0` (the marks of `y'` being, on the alive event, the
`C`-dilated initial marks) give the comparison clause of the dilated restarted word `t ↦ (√C)⁻¹ X(C t)` under `μ`, for
the past `𝓠₀` and the alive event. -/
theorem compClauseK_glue (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : gMu x₀ (κ := κ) P h W ζ hG.1 (gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) ≠ 0)
    {C : Ω × HistorySpace 0 0 → ℝ≥0}
    (hC : Measurable[usualAugmentation (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      ((gMu x₀ (κ := κ) P h W ζ hG.1)[|gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s]) 0] C)
    (hC0 : ∀ p, C p ≠ 0)
    {y' : Ω × HistorySpace 0 0 → Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + (j + 1))
      (rootNR (sourceWord (x₀ := x₀) hκ hb) + (j + 1))}
    (hy' : Measurable[usualAugmentation (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
      ((gMu x₀ (κ := κ) P h W ζ hG.1)[|gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s]) 0] y')
    (hy'e : ∀ᵐ p ∂(gMu x₀ (κ := κ) P h W ζ hG.1), p ∈ gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s →
      (y' p).2 = (dilV (C p) (gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p)).2) :
    CompClauseK κ (gMu x₀ (κ := κ) P h W ζ hG.1)
      (usualAugmentation (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
        ((gMu x₀ (κ := κ) P h W ζ hG.1)[|gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s]) 0)
      (gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ (j + 1))))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ (j + 1)))) y'
      (fun r p => (√(C p : ℝ))⁻¹ * gW x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s (C p * r) p)
      (fun i r p => (√(C p : ℝ))⁻¹ * gVL x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s i (C p * r) p)
      (fun k r p => (√(C p : ℝ))⁻¹ * gVR x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s k (C p * r) p)
      (fun p => gζ x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p / C p) := by
  set μ := gMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set A := gA x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s with hAdef
  set μA := μ[|A] with hμA
  set 𝓐 := candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs with h𝓐
  set 𝓖 := usualAugmentation 𝓐 μA with h𝓖
  have h𝓐𝓖 : 𝓐 ≤ 𝓖 := Ito.le_usualAugmentation 𝓐 μA
  have hAm𝓐 : MeasurableSet[𝓐 0] A := measurableSet_s3Alive_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0
  have hAm : MeasurableSet A := 𝓐.le 0 _ hAm𝓐
  have : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s
  have hF := Theorem15.isOrderedForceWord_flowLine (sourceWord (x₀ := x₀) hκ hb).fn
    (sourceWord (x₀ := x₀) hκ hb).jumps 0
  have hK := isKilledWord_s6
    (xL := flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
    (xR := flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) hEg hF.2.1 hF.1
    hF.2.2.2 hF.2.2.1 (candTs_bounds hv) (monotone_candTs hv)
  obtain ⟨P₀, hP₀, 𝓦, B, hrep₀⟩ :=
    StagedS7.exists_isKilledStageRep_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs hA0
  -- the past enlarged to the usual augmentation at time `0`
  have hrep := IsKilledStageRep.mk (𝓠 := (𝓖 0).comap Prod.fst)
    (WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 0) hrep₀.brownian hrep₀.adapted_W hrep₀.adapted_VL
    hrep₀.adapted_VR hrep₀.ae_path
  have hstop := hrep.isStoppedRep
  have hcomap : ∀ {β : Type} [MeasurableSpace β] {f : Ω × HistorySpace 0 0 → β}, Measurable[𝓖 0] f →
      Measurable[(𝓖 0).comap Prod.fst] fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => f p.1 :=
    fun hf => hf.comp (Measurable.of_comap_le le_rfl)
  have hy0 : Measurable[𝓖 0] fun p => gStart x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p :=
    (measurable_gStart_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs).mono (h𝓐𝓖 0) le_rfl
  have hobs := measurable_samp_of_adaptedBefore hrep.adapted_W hrep.adapted_VL hrep.adapted_VR
  have hy'p : Measurable[(𝓖 0).comap Prod.fst] fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => y' p.1 := hcomap hy'
  have hCp : Measurable[(𝓖 0).comap Prod.fst] fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => C p.1 := hcomap hC
  have hdil := IsStoppedRep.compClauseK_dil (C := fun p => C p.1) (y' := fun p => y' p.1) hκ hstop
    MeasurableSet.univ (hcomap hy0) hobs hCp (fun p => hC0 p.1) hy'p
    (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae
        ((ae_cond_mem hAm).and (cond_absolutelyContinuous.ae_le hy'e))] with p hp _
      exact hp.2 hp.1)
    (Eventually.of_forall fun p _ => ⟨hK.contW p.1, fun i => (hK.pathL p.1 i).1, fun k => (hK.pathR p.1 k).1⟩)
  have h𝓖le : 𝓖 0 ≤ (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) := 𝓖.le 0
  rw [← preimage_univ (f := (Prod.fst : (Ω × HistorySpace 0 0) × (ℕ → ℝ) → Ω × HistorySpace 0 0))] at hdil
  have hU := CompClauseK.of_prod_fst (P₀ := P₀) (R := univ) (y := y')
    (W := fun r p => (√(C p : ℝ))⁻¹ * gW x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s (C p * r) p)
    (VL := fun i r p => (√(C p : ℝ))⁻¹ * gVL x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s i (C p * r) p)
    (VR := fun k r p => (√(C p : ℝ))⁻¹ * gVR x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s k (C p * r) p)
    (ζ := fun p => gζ x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s p / C p) h𝓖le hdil
  refine CompClauseK.of_cond hAm hA0 le_rfl fun S hS p hp A' hA' _ => hU S hS p hp A' hA' (subset_univ _)

end Glue

end InteractingSLE.Sec5.CrossCond.StagedRepJ
