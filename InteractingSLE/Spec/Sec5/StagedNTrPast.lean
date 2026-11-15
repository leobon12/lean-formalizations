/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrNodeCausal

/-!
# Prop 5.9's node laws: the glued past

Packet PROVE-STAGED-NODETRANSFER. **`nodeGluePast_of_partA`** proves `NodeGluePast` (`StagedNTrBound`): for every
canonical node past event `M ⊆ gamNodeR` of `Gam`, the event `A = (alive) ∩ gZ⁻¹ M` of the glued space is an event of
the Galmarino filtration `candFiltF` at time `0`, and `A =ᵐ gZ⁻¹ M`. Route:

* `measurableSet_candFiltF_of_stopD_ae`: PROVE-STAGED-NODECOMP's criterion (`measurableSet_candFiltF_of_stopD`) with the
  representation through the stopped data required only almost surely;
* `ae_alive_of_gamNodeR`: almost surely on the glued space, a reached node candidate of `gZ p` has an alive tree
  candidate
  (PROVE-STAGED-NODE's `alive_of_mem_canonR` on PIECES' space, the a.e. agreement `ae_nodeGood_pieceZ`, the law of the
  pair `map_pieceZ_eq`);
* a measurable co-null set of good glued samples (`nodeGoodSet`);
* **saturation** on it: two good samples with the same stopped data `stopD q` (`q` rational after the last switch) have
  the same node tree data and node path up to the last switch (`alphaD_stopD`), so by `gamNode_causal` no canonical node
  past event separates them;
* **Lusin separation** (PROVE-STAGED-REPJ's `exists_measurableSet_inter_eq`): `A` is, on the good set, a preimage of a
  Borel set of stopped data.

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
open Prop59Nodes Prop59NodeTree StagedRepLater StagedKCand StagedKill StagedRep StagedRepJ StagedNComp StagedCand
open StagedNode
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)

section Past

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞) (fl : ℕ → Bool)

include hκ4 in
/-- **An event read almost surely from the stopped data on every window is an event of the Galmarino filtration.** -/
theorem measurableSet_candFiltF_of_stopD_ae (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}
    (hv : IsValid ℓ t) {s : ℝ≥0} (hs : 0 < s) {r : ℝ≥0} {A : Set (Ω × HistorySpace 0 0)} (hA : MeasurableSet A)
    (hrep : ∀ q : ℚ, lastO ℓ t < q → ∃ C : Set (Y49 0 0), MeasurableSet C ∧
      ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r →
        (p ∈ A ↔ stopD (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p ∈ C)) :
    MeasurableSet[candFiltF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf us hv hs r] A := by
  rw [candFiltF, measurableSet_galFilt_iff]
  refine ⟨hA, fun q => ?_⟩
  by_cases hq : lastO ℓ t < q
  · rw [candMarksF_of_lt x₀ h44 hκ hκ4 hb h fl hq]
    have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s
    have hqpos : 0 < q := lt_of_le_of_lt (lastO_nonneg hv) hq
    have hτ0 : (0 : ℝ) ≤ (lastO ℓ t : ℝ) := by exact_mod_cast lastO_nonneg hv
    have hτq : ((lastO ℓ t : ℚ) : ℝ) ≤ q := by exact_mod_cast hq.le
    obtain ⟨C, hC, hAC⟩ := hrep q hq
    obtain ⟨CW, hCW, hWC⟩ := exists_measurableSet_of_subtypeD
      (measurableSet_s5Win (s := s) (q := q) (τ := lastO ℓ t) hτ0 hτq r)
    obtain ⟨B, hB, hBe⟩ := exists_candSigmaF_ae_eq_stopD x₀ h44 hκ hκ4 hb P h W ζ fl hG us hv hq s (hC.inter hCW)
    refine ⟨B, hB, hBe.trans ?_⟩
    filter_upwards [ae_good_candF x₀ h44 hκ hκ4 hb P h W ζ fl hG hcf ℓ t hv hs, hAC] with p hpg hpA
    obtain ⟨hpE, hg, -⟩ := hpg
    have hwin : p ∈ candWinF x₀ h44 hκ hκ4 hb P h W ζ fl hG.1 ℓ t s q r ↔
        stopD (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s p ∈ CW := by
      change _ ↔ (stopX hqpos hEg hpE hg).1 ∈ CW
      rw [← (hWC (stopX hqpos hEg hpE hg)), mem_s5Win_iff hqpos hEg hpE hg hq.le r]
      simp only [candWinF, mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, hq, h.2.1, h.2.2⟩⟩
    show (p ∈ stopD _ _ _ _ q s ⁻¹' (C ∩ CW)) = (p ∈ A ∩ _)
    rw [eq_iff_iff, mem_preimage, mem_inter_iff, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have hw := hwin.2 h2
      exact ⟨(hpA hw).2 h1, hw⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hpA h2).1 h1, hwin.1 h2⟩
  · refine ⟨∅, @MeasurableSet.empty _ (candMarksF x₀ h44 hκ hκ4 hb h fl us ℓ t s q), Eventually.of_forall fun p => ?_⟩
    show (p ∈ (∅ : Set (Ω × HistorySpace 0 0))) = (p ∈ A ∩ _)
    rw [eq_iff_iff]
    simp only [mem_empty_iff_false, false_iff, mem_inter_iff, candWinF, mem_ofPred_eq, not_and]
    intro _ _ h
    exact absurd h hq

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The stopped data of a flag candidate are measurable. -/
theorem measurable_stopD_candWF (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (q : ℚ) (s : ℝ≥0) :
    Measurable (stopD (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
      (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q s) := by
  have hX : IsMeasurableKilledDriving (candWF x₀ h44 hκ hκ4 hb h fl ℓ t) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
      (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) := by
    intro r A hA
    have hS : MeasurableSet {x : ℝ | (x, (Fin.elim0 : Fin 0 → ℝ), (Fin.elim0 : Fin 0 → ℝ)) ∈ A} :=
      (measurable_id.prodMk measurable_const) hA
    have hm := adaptedBefore_candWF x₀ h44 hκ hκ4 hb h fl hhm ℓ t r _ hS
    have e : {ω : Ω | ((r : ℝ≥0) : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧
        (candWF x₀ h44 hκ hκ4 hb h fl ℓ t r ω, fun i => (Fin.elim0 i : ℝ≥0 → Ω → ℝ) r ω,
          fun i => (Fin.elim0 i : ℝ≥0 → Ω → ℝ) r ω) ∈ A} =
        {ω : Ω | ((r : ℝ≥0) : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧
          candWF x₀ h44 hκ hκ4 hb h fl ℓ t r ω ∈
            {x : ℝ | (x, (Fin.elim0 : Fin 0 → ℝ), (Fin.elim0 : Fin 0 → ℝ)) ∈ A}} := by
      ext ω
      simp only [mem_ofPred_eq]
      have e1 : (fun i : Fin 0 => (Fin.elim0 i : ℝ≥0 → Ω → ℝ) r ω) = (Fin.elim0 : Fin 0 → ℝ) :=
        funext fun i => i.elim0
      rw [e1]
    rw [e]
    exact hm
  exact (measurable_stopD q s).mono (CrossCond.cfGlueMarks_le _ _ hX) le_rfl

variable {x₀ h44 hκ hκ4 hb P h W ζ}

omit [StandardBorelSpace Ω] in
/-- A good glued sample whose tree candidate on `Gam` is alive is alive on the glued space. -/
theorem mem_ndA_of_alive {hhm : Measurable h} {n j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) {r : ℝ≥0}
    {p : Ω × HistorySpace 0 0}
    (hpE : p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hhm (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) r)
    (hZ : gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n))
    (hal : gZ x₀ (κ := κ) h p ∈ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).alive
      (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) :
    p ∈ ndA x₀ h44 hκ hκ4 hb P h W ζ hhm n j t r := by
  refine ⟨hpE, ?_⟩
  rw [lastO_eq hv, ← gamNodeData_pre_eq hv hpE hZ]
  exact hal.2

variable (x₀ h44 hκ hκ4 hb P h W ζ)

include hκ4 in
/-- **Almost surely on the glued space, a reached node candidate of `gZ p` has an alive tree candidate** (PIECES' side
and the law of the pair). -/
theorem ae_alive_of_gamNodeR (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (n : ℕ) (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1),
      gZ x₀ (κ := κ) h p ∈ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t →
      gZ x₀ (κ := κ) h p ∈ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal).alive
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) := by
  set B : Set Gam := gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t \
    (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal).alive (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t) with hB
  have hBm : MeasurableSet B :=
    (gamNodeQ_le h44 hκ hκ4 hb n _ j t _ (measurableSet_gamNodeR h44 hκ hκ4 hb n _ j t)).diff
      ((isReg_gamNodeData h44 hκ hκ4 hb (scheduleAt n) _).measurableSet_alive _ _)
  have noise : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ := fun _ _ _ _ _ _ => 0
  have hgood := ae_nodeGood_pieceZ x₀ h44 hκ hκ4 hb P (Measure.dirac (0 : ℝ)) h W ζ hA hG hcf (scheduleAt n)
  have hP : ∀ᵐ ω' ∂(P.prod (Measure.dirac (0 : ℝ))), pieceZ (Ωa := ℝ) x₀ κ h W ζ ω' ∉ B := by
    filter_upwards [hgood] with ω' hω'
    have hag := agreeAt_nodeD_gamNodeData x₀ h44 hκ hκ4 hb P h W ζ noise n q hω'.1 hω'.2
    have hc : ∀ j t, PieceAt (nodeCand (Ωa := ℝ) x₀ h44 hκ hκ4 hb P h W ζ noise n q j t)
        (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t) ω' (pieceZ (Ωa := ℝ) x₀ κ h W ζ ω') :=
      fun j t => pieceAt_nodeCand (Ωa := ℝ) hag j t
    have hiff := mem_canonR_congr ratGrid (nodeNL_pos x₀ hκ hb n) (nodeNR_pos x₀ hκ hb n) hc
      (nodeStart_eq_gam (Ωa := ℝ) hag) (mem_nodeR0_iff_gam (Ωa := ℝ) hag) j t
    rintro ⟨hR, hnal⟩
    have hR' := hiff.2 hR
    have hal := (alive_of_mem_canonR x₀ h44 hκ hκ4 hb P h W ζ noise hG.1 hcf n q j t ω' hR').1
    exact hnal ((hag.mem_alive _ _).1 hal)
  have hZ := measurable_pieceZ (Ωa := ℝ) x₀ hG.1 hcf
  have hmap : ∀ᵐ γ ∂((P.prod (Measure.dirac (0 : ℝ))).map (pieceZ (Ωa := ℝ) x₀ κ h W ζ)), γ ∉ B :=
    (ae_map_iff hZ.aemeasurable hBm.compl).2 hP
  rw [map_pieceZ_eq x₀ P (Measure.dirac (0 : ℝ)) h W ζ hG.1 hcf] at hmap
  filter_upwards [(ae_map_iff (measurable_gZ x₀ h hG.1).aemeasurable hBm.compl).1 hmap] with p hp hR
  by_contra hn
  exact hp ⟨hR, hn⟩

include hκ4 in
/-- **`NodeGluePast` from Part A's clearance form**: every canonical node past event `M ⊆ gamNodeR` pulls back, up to a
null set, to the event `(alive) ∩ gZ⁻¹ M` of the Galmarino filtration at time `0`. -/
theorem nodeGluePast_of_partA (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (us : ℂ → ℝ) (n : ℕ) {q : ℚ} (hq : 0 < q)
    {j : ℕ} {t : Fin j → ℝ≥0} (hv : IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) :
    NodeGluePast x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv
      ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq)) := by
  intro M hM hMR
  have hEg := candEgF_good x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG.1 (nodeLen (scheduleAt n) + j)
    (Fin.append (nodePre (scheduleAt n)) t) (q : ℝ).toNNReal
  have hZm : Measurable (gZ x₀ (κ := κ) h) := measurable_gZ x₀ h hG.1
  -- the good samples
  let Good : Ω × HistorySpace 0 0 → Prop := fun p =>
    p ∈ candEgF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG.1 (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) (q : ℝ).toNNReal ∧
      Aux50Hit.IsGoodPath (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t)) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) p.1 ∧
      gZ x₀ (κ := κ) h p ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) ∧
      (gZ x₀ (κ := κ) h p ∈ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n (q : ℝ).toNNReal j t →
        gZ x₀ (κ := κ) h p ∈ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (q : ℝ).toNNReal).alive
          (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))
  have hGood : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), Good p := by
    filter_upwards [ae_good_candF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf _ _ hv
        ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq)),
      ae_gamNodeGood_glue x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf (scheduleAt n),
      ae_alive_of_gamNodeR x₀ h44 hκ hκ4 hb P h W ζ hA hG hcf n q j t] with p h1 h2 h3
    exact ⟨h1.1, h1.2.1, h2, h3⟩
  set Gs : Set (Ω × HistorySpace 0 0) := (toMeasurable (candMu x₀ (κ := κ) P h W ζ hG.1) {p | ¬ Good p})ᶜ
    with hGs
  have hGm : MeasurableSet Gs := (measurableSet_toMeasurable _ _).compl
  have hGsub : ∀ p ∈ Gs, Good p := fun p hp => by
    by_contra hn
    exact hp (subset_toMeasurable _ _ hn)
  have hGae : ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p ∈ Gs := by
    rw [ae_iff]
    have e : {p | ¬ p ∈ Gs} = toMeasurable (candMu x₀ (κ := κ) P h W ζ hG.1) {p | ¬ Good p} := by
      ext p; simp only [hGs, mem_compl_iff, not_not, mem_ofPred_eq]
    rw [e, measure_toMeasurable]
    exact ae_iff.1 hGood
  -- the event
  set A := ndA x₀ h44 hκ hκ4 hb P h W ζ hG.1 n j t (q : ℝ).toNNReal ∩ gZ x₀ (κ := κ) h ⁻¹' M with hAdef
  have hAm : MeasurableSet A :=
    ((candFiltF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv
        ((Real.toNNReal_pos (r := (q : ℝ))).2 (by exact_mod_cast hq))).le 0 _
      (measurableSet_s3Alive_candFiltF x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv _ 0)).inter
      (hZm (gamNodeQ_le h44 hκ hκ4 hb n _ j t _ hM))
  -- gZ⁻¹ M ⊆ alive on good samples
  have hsubA : ∀ p ∈ Gs, gZ x₀ (κ := κ) h p ∈ M → p ∈ A := fun p hpG hpM => by
    obtain ⟨hpE, -, hZ, hal⟩ := hGsub p hpG
    exact ⟨mem_ndA_of_alive hv hpE hZ (hal (hMR hpM)), hpM⟩
  refine ⟨A, ?_, inter_subset_left, ?_⟩
  · refine measurableSet_candFiltF_of_stopD_ae x₀ h44 hκ hκ4 hb P h W ζ (nodeFlag (scheduleAt n)) hG hcf us hv _ hAm
      fun q' hq' => ?_
    -- saturation
    have hsat : ∀ x ∈ A ∩ Gs, ∀ x' ∈ Gs, stopD (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
        (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q' (q : ℝ).toNNReal x' =
        stopD (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t)) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q' (q : ℝ).toNNReal x → x' ∈ A := by
      rintro x ⟨⟨hxA, hxM⟩, hxG⟩ x' hx'G hY
      obtain ⟨-, hgx, hZx, halx⟩ := hGsub x hxG
      obtain ⟨-, hgx', hZx', -⟩ := hGsub x' hx'G
      have hR := hMR hxM
      have hy : cfStop (q : ℝ).toNNReal (gZ x₀ (κ := κ) h x).2 = cfStop (q : ℝ).toNNReal (gZ x₀ (κ := κ) h x').2 :=
        (congrArg Prod.snd hY).symm
      have hs := treeSameAt_gamNodeData h44 hκ hκ4 hb n (q : ℝ).toNNReal hy hZx hZx'
      have hlt : qLast (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) < q' := by
        rw [← lastO_eq hv]; exact_mod_cast hq'
      have hα : EqOn (gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h x))
          (gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t) (gZ x₀ (κ := κ) h x'))
          (Icc 0 (qLast (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))) := by
        intro u hu
        have huq : u ≤ (q' : ℝ) := hu.2.trans hlt.le
        rw [gamNodeAlpha_append, ← qPathF_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) _ _ _ x.1 x.2,
          ← qPathF_eq_fst hκ hκ4 h44 _ (qField x₀ κ h) _ _ _ x'.1 x'.2, ← seedLine_candWF, ← seedLine_candWF,
          ← alphaD_stopD hgx huq, ← alphaD_stopD hgx' huq, hY]
      have hM' := (gamNode_causal h44 hκ hκ4 hb n (q : ℝ).toNNReal hs hα hR (halx hR) M hM).1 hxM
      exact hsubA x' hx'G hM'
    obtain ⟨C, hC, hDC⟩ := exists_measurableSet_inter_eq
      (measurable_stopD_candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) hG.1 _ _ q' (q : ℝ).toNNReal) hAm hGm
      hsat
    refine ⟨C, hC, ?_⟩
    filter_upwards [hGae] with p hpG _
    constructor
    · intro hpA
      have hp2 : p ∈ A ∩ Gs := ⟨hpA, hpG⟩
      rw [hDC] at hp2
      exact hp2.2
    · intro hpC
      have hp2 : p ∈ Gs ∩ stopD (candWF x₀ h44 hκ hκ4 hb h (nodeFlag (scheduleAt n)) (nodeLen (scheduleAt n) + j)
          (Fin.append (nodePre (scheduleAt n)) t)) (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ)
          (Fin.elim0 : Fin 0 → ℝ≥0 → Ω → ℝ) (fun _ => ⊤) q' (q : ℝ).toNNReal ⁻¹' C := ⟨hpG, hpC⟩
      rw [← hDC] at hp2
      exact hp2.1
  · filter_upwards [hGae] with p hpG
    show (p ∈ A) = (p ∈ gZ x₀ (κ := κ) h ⁻¹' M)
    exact propext ⟨fun h1 => h1.2, fun h1 => hsubA p hpG h1⟩

end Past

end InteractingSLE.Sec5.CrossCond.StagedNTr
