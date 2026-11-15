/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightInputs
import InteractingSLE.Spec.Sec5.StagedRepLaterMain
import InteractingSLE.Spec.Sec5.KillArcStage

/-!
# Proposition 5.9's proved root comparison with clearance Part A

PROVE-WIRE-PARTA. A small adapter of StagedRepLaterMain: only its good-history
proof used the older Part A interface. The stopped representation, standard Borel
disintegration, dilation and transfer proofs are reused. KillArc is discharged.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Function
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real
namespace InteractingSLE.Wire.Night
open Sec5 Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Restart Sec4 Sec5.GlueCond Sec5.CrossCond.Word49 WangWu LawUnique
open Sec5.Prop59System Sec5.Prop59Stage Sec5.Prop59Pieces Sec5.CrossCond.StagedKCand
open Sec5.CrossCond.StagedKill Sec5.CrossCond.StagedRep Sec5.CrossCond.StagedRepLater
open Sec5.CrossCond
open Sec5.Prop513Wire

theorem cfHistory_goodHit_clearance
    (hA : PartAInputsSixteenDivOfClearance)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hG : IsStripGFF κ P h
      (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) :
    ∀ᵐ ω ∂P, Cond44Ref.cfHistory W ζ ω ∈ goodHitSet ∧ ζ ω = ⊤ ∧ Continuous (fun t => W t ω) := by
  have hreg := fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 hb hG hcf
  have hcont := CrossRestart.ae_continuousOn_of_isStripCounterflowDriver hcf
  filter_upwards [hreg, hcont, htr] with ω hω hc' hγ
  have hζ := hω.1
  rw [hζ] at hγ hc'
  have hw : Continuous fun t => W t ω :=
    continuousOn_univ.1 (by simpa only [ENNReal.coe_lt_top, ofPred_true] using hc'.1)
  refine ⟨cfHistory_mem_goodHitSet hζ hw hc'.2 hγ fun t ht x _ he => ?_, hζ, hw⟩
  have hH := hω.2 _ hγ t ht
  rw [he] at hH
  exact lt_irrefl _ (show (0 : ℝ) < ((x : ℂ)).im from hH) |>.elim


section
variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

theorem rootGood_pieceZ_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) (r : ℝ≥0) :
    ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r ∧
      pieceZ x₀ κ h W ζ ω' ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := by
  obtain ⟨γ, htr⟩ := exists_cfTrace hκ hb hG hcf
  have h2 := cfHistory_goodHit_clearance hA hκ hκ4 hb hG hcf htr
  have hg := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSched j t)
  have hroot : ∀ᵐ ω ∂P, RootGood x₀ h44 hκ hκ4 hb h W ζ r ω := by
    filter_upwards [hg, h2] with ω hgω hcω
    exact ⟨hcω, fun j t hv => (isProperArc_qPath_of h44 hκ hκ4 _ _ (hgω j t hv)).1⟩
  have h1 : ∀ᵐ ω ∂P, ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r := by
    rw [ae_iff]
    have he : {ω | ¬ ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r} =
        toMeasurable P {ω | ¬ RootGood x₀ h44 hκ hκ4 hb h W ζ r ω} := by
      ext ω; simp [rootGood]
    rw [he, measure_toMeasurable]
    exact ae_iff.1 hroot
  have h3 := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSched j t)
  have h0 : ∀ᵐ ω ∂P, ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ r ∧
      (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω) ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := by
    filter_upwards [h1, h2, h3] with ω hω1 hω2 hω3
    exact ⟨hω1, hω2.1, fun j t hv k hk => hω3 j t hv k hk⟩
  exact Measure.quasiMeasurePreserving_fst.ae h0

theorem compClauseK_rootCand_clearance (hA : PartAInputsSixteenDivOfClearance) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) {q : ℚ} (hq : 0 < q) (t : Fin 0 → ℝ≥0) :
    CompClauseK κ (P.prod Pa) (rootBase W ζ (Ωa := Ωa) q) univ (rootρL κ (sourceWord (x₀ := x₀) hκ hb))
      (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (Fin.last (flowLineNL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0))
      (Fin.last (flowLineNR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0))
      (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q)
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).W
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).VL
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).VR
      (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
        (Ωa := Ωa) q 0 t).ζ := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set r : ℝ≥0 := (q : ℝ).toNNReal with hr
  have hr0 : 0 < r := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  obtain ⟨htop, 𝓕, VL, VR, B, hC⟩ := exists_rootCoupling h44 hκ hκ4 hb (P := P) hhm hG
  have hcfc := isCenteredCounterflowDriver_of_strip hκ hcf
  have hcfm := measurable_cfHistory_of_strip hcf
  have hqm : Measurable (qField x₀ κ h) := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  set k := condDistrib (Cond44Ref.cfHistory W ζ) (qField x₀ κ h) P with hkdef
  have hk : P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) = P.map (qField x₀ κ h) ⊗ₘ k :=
    (compProd_map_condDistrib hqm.aemeasurable hcfm.aemeasurable).symm
  have hXq : (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω)) = qField x₀ κ h :=
    funext fun ω => cfField_rootField ω
  have hlaw : P.map (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω)) = P.map (qField x₀ κ h) := by
    rw [hXq]
  have hxLs : StrictAnti (flowLineXL c.fn c.jumps 0) := fun i j hij => Theorem14.GW0.flowLineXL_lt c.fn c.jumps 0 hij
  have hxRs : StrictMono (flowLineXR c.fn c.jumps 0) := fun i j hij => Theorem14.GW0.flowLineXR_lt c.fn c.jumps 0 hij
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have h44' : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) :=
    cond44_upper hκ (sourceWord_extreme hκ hb)
  have hglue := compClauseK_img_dil killedArcSwallowStatement hκ hκ4 hF h44' hxLs hxRs hC hcfc hlaw k hk hr0
    measurable_startC
    startC_ne_zero
  set μ := glueMeasure P k (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω))
    ((Cond44Ref.measurable_cfField κ).comp hC.2.1) with hμ
  set Z := pieceZ (Ωa := Ωa) x₀ κ h W ζ with hZdef
  set Z' : Ω × HistorySpace 0 0 → Gam := fun p => (qField x₀ κ h p.1, p.2) with hZ'def
  have hZ := measurable_pieceZ (Ωa := Ωa) x₀ hhm hcf
  have hZ' : Measurable Z' := (hqm.comp measurable_fst).prodMk measurable_snd
  -- the laws of the pair agree
  have hlawZ : (P.prod Pa).map Z = μ.map Z' := by
    have h1 : (P.prod Pa).map Z = P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) := by
      have e : Z = (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) ∘ Prod.fst := rfl
      rw [e, ← Measure.map_map (hqm.prodMk hcfm) measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    have hk' : P.map (fun ω => (Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω),
        Cond44Ref.cfHistory W ζ ω)) =
        P.map (fun ω => Cond44Ref.cfField κ (rootField (κ := κ) (x₀ := x₀) h ω)) ⊗ₘ k := by
      simpa only [cfField_rootField] using hk
    rw [h1, StagedCand.map_pair_eq_glue ((Cond44Ref.measurable_cfField κ).comp hC.2.1) hcfm k hk' measurable_id
      (Eventually.of_forall fun ω => (cfField_rootField ω).symm)]
    rfl
  -- good samples
  have hgP := rootGood_pieceZ_clearance x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hG hcf hE hR r
  have hgamP : ∀ᵐ γ ∂((P.prod Pa).map Z), γ ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb :=
    (ae_map_iff hZ.aemeasurable (measurableSet_gamGood h44 hκ hκ4 hb)).2 (hgP.mono fun _ h => h.2)
  have hgZ' : ∀ᵐ p ∂μ, Z' p ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb := by
    rw [hlawZ] at hgamP
    exact (ae_map_iff hZ'.aemeasurable (measurableSet_gamGood h44 hκ hκ4 hb)).1 hgamP
  set W₀ : ℝ≥0 → Ω → ℝ := fun t ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).1 t with hW₀
  set ζ₀ : Ω → ℝ≥0∞ := fun ω => (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h ω).2 with hζ₀
  have hgE : ∀ᵐ p ∂μ, p ∈ glueGood μ r ζ₀ W₀ := by
    have hae : ∀ᵐ p ∂μ, IsGood49 r ζ₀ W₀ p := by
      filter_upwards [cfGlueAE_isGood49 r hr0 κ hκ hκ4 _ _ _ _ hF h44' P 𝓕 W₀ VL VR B ζ₀ _ hC P
        (qField x₀ κ h) W ζ hcfc hlaw k hk] with p hp
      exact isGood49_of_mem hp.1 hp.2
    exact ae_mem_glueGood hae
  have htopG : ∀ᵐ p ∂μ, (rootDrv h44 hκ hκ4 (x₀ := x₀) hb h p.1).2 = ⊤ :=
    WangWu.ae_glue_fst k ((Cond44Ref.measurable_cfField κ).comp hC.2.1) htop
  -- the clause on the glued space for the observable
  have h𝓜Z' : (gamPast r).comap Z' =
      MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cfStop r p.2) inferInstance := by
    rw [MeasurableSpace.comap_comp]; rfl
  have h𝓜Z : (gamPast r).comap Z = rootBase W ζ (Ωa := Ωa) q := by
    rw [MeasurableSpace.comap_comp]; rfl
  have h' : ∀ S : Set (Start (rootNL c + 0) (rootNR c + 0) × Samp (rootNL c + 0) (rootNR c + 0)), MeasurableSet S →
      ∀ p : ℝ≥0∞, CompPremiseFarK κ (rootρL κ c) (rootρR κ c) (Fin.last (flowLineNL c.fn c.jumps 0))
        (Fin.last (flowLineNR c.fn c.jumps 0)) univ S p → ∀ A : Set (Ω × HistorySpace 0 0),
        MeasurableSet[(gamPast r).comap Z'] A → A ⊆ Z' ⁻¹' univ →
        p * μ A ≤ μ (A ∩ {p' | gamObs h44 hκ hκ4 (x₀ := x₀) hb r (Z' p') ∈ S}) := by
    intro S hS p hp A hA _
    rw [h𝓜Z'] at hA
    refine (hglue S hS p hp A hA (subset_univ _)).trans (le_of_eq (measure_congr ?_))
    filter_upwards [hgE, hgZ', htopG] with p' hpE hpZ htp
    have he := glueObs_eq_gamObs h44 hκ hκ4 hb r (E := glueGood μ r ζ₀ W₀) hpE hpZ htp
    show (p' ∈ A ∧ _ ∈ S) = (p' ∈ A ∧ _ ∈ S)
    rw [he]
  have key := StagedCand.compClause_of_map_eq hZ hZ' hlawZ (gamPast_le r) MeasurableSet.univ
    (measurable_gamObs h44 hκ hκ4 hb r) h'
  intro S hS p hp A hA hAR
  rw [← h𝓜Z] at hA
  refine (key S hS p hp A hA (fun _ _ => mem_univ _)).trans (le_of_eq (measure_congr ?_))
  filter_upwards [hgP] with ω' hω'
  have he := rootObs_eq_gamObs x₀ h44 hκ hκ4 hb hhm hcf noise (Ωa := Ωa) t hω'.1 hω'.2
  show (ω' ∈ A ∧ _ ∈ S) = (ω' ∈ A ∧ _ ∈ S)
  rw [he]

end
end InteractingSLE.Wire.Night
