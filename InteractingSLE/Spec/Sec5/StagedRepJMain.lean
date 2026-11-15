/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepJReach
import InteractingSLE.Spec.Sec5.StagedRepJBound

/-!
# Prop 5.9's later root stages: the killed comparison clause of PIECES' candidates

Packet PROVE-STAGED-REPJ. For every rational `q > 0` and every list `t` of length `j + 1`, the comparison clause of the
killed stage law (`CompClauseK`, R78) of PIECES' root candidate `rootCand … q (j + 1) t` for its canonical past,
reached event and start (the second clause of `Wire.Night.RootLaw … (j + 1) t`), by the transfer
`compClauseK_transfer` along the pair `(field in chart Q, counterflow history)`:

* the target side: PIECES' tree data agree with REP2's tree `gamData` on `Gam` at almost every sample
  (`agreeAt_rootData_gamData`, `ae_pieceAt_rootCand`), so the canonical pasts lie in `aeComap` of `Gam`'s
  (`canonQ_le_aeComap`), and the record is `gamObsJ ∘ pieceZ` almost surely;
* the laws of the pair agree on PIECES' space and on the glued space (`map_pieceZ_eq`);
* the source side: `gamBound_of_glue` (S7's killed representation, with the frozen dilation), whose remaining inputs are
  the glued identifications `GluePast` and `GlueObs`;
* inadmissible lists are never reached (`TreeData.reach` on `Gam`).

**`compClauseK_rootCand_succ`**. R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`,
`Theorem13Statement` or any `*_of_param`.
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
open StagedRepLater StagedKCand StagedKill StagedRep StagedCand
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Theta (cfFieldT measurable_cfFieldT)

/-! ### Continued drivers read at a sample -/

section Drv

theorem continuedDriver_congr {Ω Ω' : Type*} {E : ℕ → Ω → Driver} {E' : ℕ → Ω' → Driver} {ω : Ω} {ω' : Ω'}
    (h : ∀ i, E i ω = E' i ω') : ∀ (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0)),
      continuedDriver E j a l ω = continuedDriver E' j a l ω'
  | _, _, [] => rfl
  | j, _, [_] => by funext r; simp only [continuedDriver, h]
  | j, a, p :: q :: l => by
    funext r
    simp only [continuedDriver, h, continuedDriver_congr h (j + 1) p.2 (q :: l)]

/-- The candidate paths of a field read only the field's value. -/
theorem qPath_eq_fst {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (h44 : Theorem12ParamCond44Statement.{0}) (c : BoundaryWord)
    {Ω : Type*} (F : Ω → DistOn upperHalfPlaneOpens) (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω) (y : HistorySpace 0 0) :
    qPath h44 hκ hκ4 c F j t ω = qPath h44 hκ hκ4 c Prod.fst j t ((F ω, y) : Gam) := by
  have e := continuedDriver_congr (E := codeFam h44 hκ hκ4 c F (candSched j t))
    (E' := codeFam h44 hκ hκ4 c Prod.fst (candSched j t)) (ω := ω) (ω' := ((F ω, y) : Gam)) (fun _ => rfl) 0 0
    (scheduleList (candSched j t))
  funext u
  show LP.traceAt u.toNNReal (continuedDriver (codeFam h44 hκ hκ4 c F (candSched j t)) 0 0
      (scheduleList (candSched j t)) ω) = LP.traceAt u.toNNReal (continuedDriver
      (codeFam h44 hκ hκ4 c Prod.fst (candSched j t)) 0 0 (scheduleList (candSched j t)) ((F ω, y) : Gam))
  rw [e]

end Drv

section Main

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace Ωa] (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **PIECES' root tree data agree with `gamData` at `(qField ω, cfHistory ω)`** on the good samples. -/
theorem agreeAt_rootData_gamData (q : ℚ) (noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) {ω : Ω}
    (hω : ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal)
    (hZ : (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω) ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (canonLam W ζ q) (canonXL x₀ hκ hb W ζ q)
      (canonXR x₀ hκ hb W ζ q) noise).AgreeAt (gamData h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal) ω
      (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω) :=
  ⟨rfl, rfl, rfl, ⟨fun _ => hZ, fun _ => hω⟩, fun j t => qPath_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) j t ω _,
    fun _ _ => Iff.rfl, rfl, rfl⟩

/-- `gamData` is a tree (as PIECES' `isTree_rootData`). -/
theorem isTree_gamData (r : ℝ≥0) : (gamData h44 hκ hκ4 (x₀ := x₀) hb r).IsTree where
  init j t hv := ⟨hv.init, qLast_init_le hv, (hv.2 _).2.1⟩
  pfx j t hv γ u _ hu := qPath_pfx h44 hκ hκ4 _ _ hv γ hu
  qnonneg j t hv := by
    show 0 ≤ qLast j t
    rw [← lastO_eq hv]; exact_mod_cast lastO_nonneg hv

/-- On `Gam` only admissible lists are reached. -/
theorem isValid_of_mem_gamR {r : ℝ≥0} {j : ℕ} {t : Fin (j + 1) → ℝ≥0} {γ : Gam}
    (hγ : γ ∈ gamR h44 hκ hκ4 (x₀ := x₀) hb r (j + 1) t) : IsValid (j + 1) t :=
  ((TreeData.reach (rootNL_pos _) (rootNR_pos _) (isReg_gamData h44 hκ hκ4 hb r) (isTree_gamData x₀ h44 hκ hκ4 hb r)
    (fun _ _ => Iff.rfl) (j + 1) t γ hγ).2 (Nat.succ_pos j)).1.1

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_gZ (hhm : Measurable h) : Measurable (gZ x₀ (κ := κ) h) :=
  (((measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm).comp measurable_fst).prodMk
    measurable_snd

omit [StandardBorelSpace Ω] in
/-- **The pair has the same law on PIECES' space and on the glued space.** -/
theorem map_pieceZ_eq (hhm : Measurable h) (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    (P.prod Pa).map (pieceZ (Ωa := Ωa) x₀ κ h W ζ) = (gMu x₀ (κ := κ) P h W ζ hhm).map (gZ x₀ (κ := κ) h) := by
  have hqm : Measurable (qField x₀ κ h) :=
    (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hcfm := measurable_cfHistory_of_strip hcf
  have h1 : (P.prod Pa).map (pieceZ (Ωa := Ωa) x₀ κ h W ζ) =
      P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) := by
    have e : pieceZ (Ωa := Ωa) x₀ κ h W ζ = (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) ∘ Prod.fst := rfl
    rw [e, ← Measure.map_map (hqm.prodMk hcfm) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have hXm : Measurable fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω) :=
    (measurable_cfFieldT κ (π / 2)).comp (measurable_rootField hhm)
  have hk : P.map (fun ω => (cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω), Cond44Ref.cfHistory W ζ ω)) =
      P.map (fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω)) ⊗ₘ candK x₀ (κ := κ) P h W ζ := by
    simp only [Theta.cfFieldT_pi_div_two, cfField_rootField]
    exact (compProd_map_condDistrib (μ := P) hqm.aemeasurable hcfm.aemeasurable).symm
  have e : gMu x₀ (κ := κ) P h W ζ hhm =
      glueMeasure P (candK x₀ (κ := κ) P h W ζ) (fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω))
        hXm := rfl
  rw [h1, e]
  exact map_pair_eq_glue hXm hcfm (candK x₀ (κ := κ) P h W ζ) hk (D := qField x₀ κ h) (L := id) measurable_id
    (Eventually.of_forall fun ω => (cfField_rootField ω).symm)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [IsProbabilityMeasure Pa] in
/-- **PIECES' root candidates agree almost surely with `Gam`'s at the pair `pieceZ`.** -/
theorem ae_pieceAt_rootCand (hgood : ∀ r : ℝ≥0, ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r ∧
      pieceZ (Ωa := Ωa) x₀ κ h W ζ ω' ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb)
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (q : ℚ) :
    ∀ᵐ ω' ∂(P.prod Pa), (∀ j t, PieceAt (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q j t) (gamCand h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal j t) ω'
        (pieceZ (Ωa := Ωa) x₀ κ h W ζ ω')) ∧
      rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) (Ωa := Ωa) q ω' =
        gamY0 h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal (pieceZ (Ωa := Ωa) x₀ κ h W ζ ω') := by
  filter_upwards [hgood (q : ℝ).toNNReal] with ω' hω'
  have hag := agreeAt_rootData_gamData x₀ h44 hκ hκ4 hb P h W ζ q (noise q) hω'.1 hω'.2
  refine ⟨fun j t => ?_, rfl⟩
  have hc := hag.cand j t
  exact ⟨hc.W, hc.VL, hc.VR, hc.ζ, hc.clk⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [IsProbabilityMeasure Pa] in
/-- PIECES' root past is read on `Gam`. -/
theorem rootBase_le_aeComap (q : ℚ) :
    rootBase W ζ (Ωa := Ωa) q ≤ aeComap (P.prod Pa) (pieceZ (Ωa := Ωa) x₀ κ h W ζ) (gamPast (q : ℝ).toNNReal) := by
  rintro _ ⟨B, hB, rfl⟩
  exact ⟨(fun γ : Gam => cfStop (q : ℝ).toNNReal γ.2) ⁻¹' B, ⟨B, hB, rfl⟩, EventuallyEq.rfl⟩

include hκ4 in
/-- **The killed comparison clause of PIECES' root candidate at depth `j + 1`** (the second clause of
`Wire.Night.RootLaw … (j + 1) t`), from the two glued identifications `GluePast` and `GlueObs` of the candidate (needed
only for admissible lists; inadmissible lists are never reached). -/
theorem compClauseK_rootCand_succ (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hgood : ∀ r : ℝ≥0, ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r ∧
      pieceZ (Ωa := Ωa) x₀ κ h W ζ ω' ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb)
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) {q : ℚ} (hq : 0 < q) {j : ℕ} (t : Fin (j + 1) → ℝ≥0)
    (hpast : ∀ us : ℂ → ℝ, IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn
        (sourceWord (x₀ := x₀) hκ hb).jumps us → ∀ hv : IsValid (j + 1) t,
      GluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq)))
    (hobs : IsValid (j + 1) t → GlueObs x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t (q : ℝ).toNNReal) :
    CompClauseK κ (P.prod Pa)
      (canonQ (rootBase W ζ (Ωa := Ωa) q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) (j + 1) t)
      (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (j + 1) t)
      (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
      (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ (j + 1))))
      (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ (j + 1))))
      (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
        (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) q) (j + 1) t)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q (j + 1) t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q (j + 1) t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q (j + 1) t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q (j + 1) t).ζ := by
  have hhm := hG.1
  have hcfm := measurable_cfHistory_of_strip hcf
  have hag := ae_pieceAt_rootCand x₀ h44 hκ hκ4 hb P Pa h W ζ hgood noise q
  have hZm := measurable_pieceZ (Ωa := Ωa) x₀ hhm hcf
  have hlamm : ∀ q', Measurable (canonLam W ζ q') := fun q' => (measurable_rootLam _).comp hcfm
  have hxLm : ∀ q', Measurable (canonXL x₀ hκ hb W ζ q') := fun q' => measurable_pi_iff.2 fun i =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp hcfm))
  have hxRm : ∀ q', Measurable (canonXR x₀ hκ hb W ζ q') := fun q' => measurable_pi_iff.2 fun k =>
    ((measurable_rootLam _).comp hcfm).mul ((measurable_pi_apply k).comp ((measurable_rootXR hκ hb _).comp hcfm))
  have hfam := isRegFam_rootCand x₀ h44 hκ hκ4 hb (Ωa := Ωa) (noise := noise) hhm hcf hlamm
    (fun _ _ => rootLam_pos _ _) hxLm hxRm q
  have hy₀ := measurable_rootStart x₀ hκ hb (Ωa := Ωa) hxLm hxRm q
  have hQ := canonQ_le_aeComap ratGrid (rootNL_pos _) (rootNR_pos _) hfam
    (isRegFam_gamCand h44 hκ hκ4 hb (q : ℝ).toNNReal) hy₀ (measurable_gamY0 h44 hκ hκ4 hb (q : ℝ).toNNReal) hag
    (rootBase_le_aeComap x₀ P Pa h W ζ q) (j + 1) t
  have hRae := canonR_ae_eq ratGrid (rootNL_pos _) (rootNR_pos _) (R₀ := univ) (R₀' := univ) hag
    (Eventually.of_forall fun _ => Iff.rfl) (j + 1) t
  by_cases hv : IsValid (j + 1) t
  · obtain ⟨us, hus, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
      (Restart.BoundaryWord.isPiecewiseConstantBoundaryData (sourceWord (x₀ := x₀) hκ hb))
    have hr0 : 0 < (q : ℝ).toNNReal := (Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq)
    have hbound := gamBound_of_glue x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hr0 (hpast us hus hv) (hobs hv)
    refine compClauseK_transfer hZm (measurable_gZ x₀ h hhm) (map_pieceZ_eq x₀ P Pa h W ζ hhm hcf)
      (gamQ_le h44 hκ hκ4 hb (q : ℝ).toNNReal (j + 1) t)
      (RΓ := gamR h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal (j + 1) t)
      (measurable_gamObsJ h44 hκ hκ4 hb (q : ℝ).toNNReal (j + 1) t) ?_ ?_ hbound
    · intro A hA hAR
      obtain ⟨M₀, hM₀, hAM⟩ := hQ A hA
      have hRm := measurableSet_canonR (𝓑 := gamPast (q : ℝ).toNNReal)
        (cand := gamCand h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal) (G := ratGrid) (hnL := rootNL_pos _)
        (hnR := rootNR_pos _) (y₀ := gamY0 h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal) MeasurableSet.univ (j + 1) t
      refine ⟨M₀ ∩ gamR h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal (j + 1) t, hM₀.inter hRm, inter_subset_right, ?_⟩
      have e : A = A ∩ canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ)
          (canonXR x₀ hκ hb W ζ) noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
          (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (j + 1) t :=
        (inter_eq_left.2 hAR).symm
      rw [e, preimage_inter]
      exact hAM.inter hRae
    · filter_upwards [hag] with ω' hω' _
      refine Prod.ext (canonY_congr hω'.1 hω'.2 (j + 1) t) ?_
      have hc := hω'.1 (j + 1) t
      simp only [gamObsJ, pieceSamp, hc.W, hc.VL, hc.VR, hc.ζ]
  · intro S hS p hp A hA hAR
    have hempty : canonR (gamCand h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal) ratGrid (rootNL_pos _)
        (rootNR_pos _) (gamY0 h44 hκ hκ4 (x₀ := x₀) hb (q : ℝ).toNNReal) univ (j + 1) t = ∅ :=
      eq_empty_of_forall_notMem fun γ hγ => hv (isValid_of_mem_gamR x₀ h44 hκ hκ4 hb hγ)
    have h0 : (P.prod Pa) A = 0 := by
      refine measure_mono_null hAR ?_
      rw [measure_congr hRae, hempty, preimage_empty, measure_empty]
    rw [h0, mul_zero]
    exact bot_le

end Main

end InteractingSLE.Sec5.CrossCond.StagedRepJ
