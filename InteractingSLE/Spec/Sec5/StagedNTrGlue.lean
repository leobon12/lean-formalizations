/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrAgree

/-!
# Prop 5.9's node laws: the flag word's comparison clause on the glued space

Packet PROVE-STAGED-NODETRANSFER. PROVE-STAGED-NODECOMP's `FlagGluedRep` (the stopped representation of a flag
candidate's restarted word on the glued space, conditioned on its alive event `A`, past `candFiltF … 0`) is turned into
the killed comparison clause (`CompClauseK`, R78) under the glued measure `μ` itself, for the restarted word dilated by
any factor `C` and started at any start `y'` that are measurable for the null-augmented past
`flQ0 = candFiltF 0 ∨ 𝒩(μ[|A])` (the marks of `y'` being the `C`-dilated restarted marks on `A`):

* `flA`, `flW`, `flVL`, `flVR`, `flζ`, `flStart`, `flQ0`: the glued objects of the flag candidate;
* **`compClauseK_flagGlue`**: the clause. The representation's filtration is replaced by its usual augmentation (a
  Brownian motion stays one, `Ito.isFilteredBrownianReal_usualAugmentation`), so that its past contains the null sets
  of `μ[|A]`; then PROVE-STAGED-REPJ's `IsStoppedRep.compClauseK_dil` (frozen dilation), `CompClauseK.of_prod_fst`
  and `CompClauseK.of_cond`;
* **`CompClauseK.reindex`**: the clause along equalities of the numbers of marks (the node candidates count their
  marks as `(rootNL + m) + j`, the flag word as `rootNL + (m + j)`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn)

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces Prop59Stage Prop59System
open Prop59NodeTree StagedRepLater StagedKCand StagedKill StagedRep StagedRepJ StagedNComp
open Sec4 (IsStripGFF IsStripCounterflowDriver)

/-! ### Reindexing the marks -/

section Reindex

variable {κ : ℝ} {Ω : Type*} {𝓠 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω}

/-- **The comparison clause along equalities of the numbers of marks.** -/
theorem CompClauseK.reindex {nL nR nL' nR' : ℕ} (eL : nL = nL') (eR : nR = nR') {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : CompClauseK κ P 𝓠 R ρL ρR iL iR y W VL VR ζ) :
    CompClauseK κ P 𝓠 R (fun i => ρL (Fin.cast eL.symm i)) (fun k => ρR (Fin.cast eR.symm k)) (Fin.cast eL iL)
      (Fin.cast eR iR) (fun ω => ((y ω).1, fun i => (y ω).2.1 (Fin.cast eL.symm i),
        fun k => (y ω).2.2 (Fin.cast eR.symm k))) W (fun i => VL (Fin.cast eL.symm i))
      (fun k => VR (Fin.cast eR.symm k)) ζ := by
  subst eL eR
  exact h

end Reindex

/-! ### The glued objects of a flag candidate -/

section Flag

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

/-- The alive event of the flag candidate's last switch. -/
abbrev flA (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  s3Alive s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted driver of the flag candidate. -/
abbrev flW (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  s3W s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted left marks of the flag candidate in tree order. -/
abbrev flVL (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) :
    Fin (rootNL (sourceWord (x₀ := x₀) hκ hb) + ℓ) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTsF fl ℓ t) ℓ s
    (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted right marks of the flag candidate in tree order. -/
abbrev flVR (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) :
    Fin (rootNR (sourceWord (x₀ := x₀) hκ hb) + ℓ) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) (candTsF fl ℓ t) ℓ s
    (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted lifetime of the flag candidate. -/
abbrev flζ (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) : Ω × HistorySpace 0 0 → ℝ≥0∞ :=
  s3ζ s (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (candEgF x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s) (lastO ℓ t : ℝ)

/-- The restarted start of the flag candidate (driver `0`, the initial marks in tree order). -/
abbrev flStart (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (p : Ω × HistorySpace 0 0) :
    Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + ℓ) (rootNR (sourceWord (x₀ := x₀) hκ hb) + ℓ) :=
  ((0 : ℝ), fun i => flVL x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s i 0 p,
    fun j => flVR x₀ h44 hκ hκ4 hb P h W ζ fl hhm ℓ t s j 0 p)

/-- **The past of the flag glued clause**: the Galmarino filtration `candFiltF` at time `0` with the null sets of the
conditioned glued measure. -/
abbrev flQ0 (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) : MeasurableSpace (Ω × HistorySpace 0 0) :=
  Ito.nullAugmented (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
    ((candMu x₀ (κ := κ) P h W ζ hG.1)[|flA x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s]) 0

include hκ4 in
/-- The restarted start is an event of the Galmarino filtration at time `0`. -/
theorem measurable_flStart_candFiltF (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) :
    Measurable[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0]
      (flStart x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) := by
  have hL0 : ∀ i, Measurable[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0]
      fun p => flVL x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s i 0 p := fun i =>
    (stronglyAdapted_s6VL_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
      (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) i 0).measurable
  have hR0 : ∀ j, Measurable[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0]
      fun p => flVR x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s j 0 p := fun j =>
    (stronglyAdapted_s6VR_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs
      (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) j 0).measurable
  exact measurable_const.prodMk (((@measurable_pi_iff _ _ _
    (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0) _ _).2 hL0).prodMk
    ((@measurable_pi_iff _ _ _ (candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0) _ _).2 hR0))

include hκ4 in
/-- **The killed comparison clause of the dilated restarted flag word on the glued space.** From the stopped
representation `FlagGluedRep` of the flag candidate `(ℓ, t)` (non-null alive event `A`), every time factor `C ≠ 0`
and start `y'` measurable for `flQ0 = candFiltF 0 ∨ 𝒩(μ[|A])`, with the marks of `y'` on `A` the `C`-dilated
restarted marks, give the comparison clause of the dilated restarted word `r ↦ (√C)⁻¹ X(C r)` under the glued measure,
for the past `flQ0` and the stage event `A`. -/
theorem compClauseK_flagGlue (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (flA x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s) ≠ 0)
    (hrep : FlagGluedRep x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
    {C : Ω × HistorySpace 0 0 → ℝ≥0} (hC : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs] C)
    (hC0 : ∀ p, C p ≠ 0)
    {y' : Ω × HistorySpace 0 0 → Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + ℓ)
      (rootNR (sourceWord (x₀ := x₀) hκ hb) + ℓ)}
    (hy' : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs] y')
    (hy'e : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ flA x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s →
      (y' p).2 = (dilV (C p) (flStart x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s p)).2) :
    CompClauseK κ (candMu x₀ (κ := κ) P h W ζ hG.1) (flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs)
      (flA x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s)
      (consAlt (bornL κ fl) (nodeρL0 κ (sourceWord (x₀ := x₀) hκ hb) (flagAngle (fl 0))) ℓ)
      (consAlt (bornR κ fl) (nodeρR0 κ (sourceWord (x₀ := x₀) hκ hb) (flagAngle (fl 0))) ℓ)
      (farL (Nat.lt_of_lt_of_le (rootNL_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ)))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos (sourceWord (x₀ := x₀) hκ hb)) (Nat.le_add_right _ ℓ))) y'
      (fun r p => (√(C p : ℝ))⁻¹ * flW x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s (C p * r) p)
      (fun i r p => (√(C p : ℝ))⁻¹ * flVL x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s i (C p * r) p)
      (fun k r p => (√(C p : ℝ))⁻¹ * flVR x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s k (C p * r) p)
      (fun p => flζ x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s p / C p) := by
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set A := flA x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s with hAdef
  set μA := μ[|A] with hμA
  set 𝓐 := candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs with h𝓐
  have hAm𝓐 : MeasurableSet[𝓐 0] A := measurableSet_s3Alive_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs 0
  have hAm : MeasurableSet A := 𝓐.le 0 _ hAm𝓐
  have : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  have h𝓐𝓠 : 𝓐 0 ≤ flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs := Ito.le_nullAugmented 𝓐 μA 0
  have h𝓠le : flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs ≤
      (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) := (Ito.nullAugmented 𝓐 μA).le 0
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
  have hF := Theorem15.isOrderedForceWord_flowLine (sourceWord (x₀ := x₀) hκ hb).fn
    (sourceWord (x₀ := x₀) hκ hb).jumps 0
  have hK := isKilledWord_s6
    (xL := flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
    (xR := flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0) hEg hF.2.1 hF.1
    hF.2.2.2 hF.2.2.1 (candTsF_bounds (fl := fl) hv) (monotone_candTsF (fl := fl) hv)
  obtain ⟨P₀, hP₀, 𝓕, B, hrep₀⟩ := hrep
  -- the past enlarged by the null sets of `μ[|A]`, the filtration by its usual augmentation
  have hle0 : (flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs).comap Prod.fst ≤
      usualAugmentation 𝓕 (μA.prod P₀) 0 := by
    change (𝓐 0 ⊔ Ito.nullSets μA).comap Prod.fst ≤ _
    rw [MeasurableSpace.comap_sup]
    refine sup_le (hrep₀.le0.trans (Ito.le_usualAugmentation 𝓕 _ 0)) ?_
    refine le_trans ?_ (Ito.nullSets_le_usualAugmentation 𝓕 _ 0)
    rw [Ito.nullSets, MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨N, ⟨hN, hN0⟩, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom ⟨measurable_fst hN, ?_⟩
    rw [← Measure.map_apply measurable_fst hN, Measure.map_fst_prod, measure_univ, one_smul]
    exact hN0
  have hrep := IsKilledStageRep.mk (𝓠 := (flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs).comap Prod.fst) hle0
    (Ito.isFilteredBrownianReal_usualAugmentation hrep₀.brownian)
    (fun r D hD => Ito.le_usualAugmentation 𝓕 _ r _ (hrep₀.adapted_W r D hD))
    (fun i r D hD => Ito.le_usualAugmentation 𝓕 _ r _ (hrep₀.adapted_VL i r D hD))
    (fun j r D hD => Ito.le_usualAugmentation 𝓕 _ r _ (hrep₀.adapted_VR j r D hD)) hrep₀.ae_path
  have hstop := hrep.isStoppedRep
  have hcomap : ∀ {β : Type} [MeasurableSpace β] {f : Ω × HistorySpace 0 0 → β},
      Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs] f →
      Measurable[(flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs).comap Prod.fst]
        fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => f p.1 :=
    fun hf => hf.comp (Measurable.of_comap_le le_rfl)
  have hy0 : Measurable[flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs]
      fun p => flStart x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s p :=
    (measurable_flStart_candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs).mono h𝓐𝓠 le_rfl
  have hobs := measurable_samp_of_adaptedBefore hrep.adapted_W hrep.adapted_VL hrep.adapted_VR
  have hRm : MeasurableSet[(flQ0 x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs).comap Prod.fst]
      (Prod.fst ⁻¹' A : Set ((Ω × HistorySpace 0 0) × (ℕ → ℝ))) := ⟨A, h𝓐𝓠 _ hAm𝓐, rfl⟩
  have hdil := IsStoppedRep.compClauseK_dil (C := fun p => C p.1) (y' := fun p => y' p.1) hκ hstop hRm
    (hcomap hy0) hobs (hcomap hC) (fun p => hC0 p.1) (hcomap hy')
    (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (cond_absolutelyContinuous.ae_le hy'e)] with p hp hpR
      exact hp hpR)
    (Eventually.of_forall fun p _ => ⟨hK.contW p.1, fun i => (hK.pathL p.1 i).1, fun k => (hK.pathR p.1 k).1⟩)
  have hU := CompClauseK.of_prod_fst (P₀ := P₀) (R := A) (y := y')
    (W := fun r p => (√(C p : ℝ))⁻¹ * flW x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s (C p * r) p)
    (VL := fun i r p => (√(C p : ℝ))⁻¹ * flVL x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s i (C p * r) p)
    (VR := fun k r p => (√(C p : ℝ))⁻¹ * flVR x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s k (C p * r) p)
    (ζ := fun p => flζ x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s p / C p) h𝓠le hdil
  exact CompClauseK.of_cond hAm hA0 le_rfl hU

end Flag

end InteractingSLE.Sec5.CrossCond.StagedNTr
