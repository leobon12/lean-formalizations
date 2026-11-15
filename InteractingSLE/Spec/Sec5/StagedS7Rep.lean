/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS7Exit

/-!
# Proposition 5.9 at depth `j + 1`, step S7 (d): the stopped representation of the restarted word

Packet PROVE-STAGED-S7 (`planning/handoffs/PROVE-STAGED-S6.md` §5, item 1). For PIECES' candidate `(j + 1, t)` on the
glued space, conditioned on the alive event of its last switch and extended by the standard noise space
(`μ_A ⊗ P₀`, PROVE-STAGED-S6's `exists_isWordEntrance_cand`):

* `ae_goodSet49_cand`: almost every glued sample has a good counterflow history;
* `strictMono_candTs`: the candidate's switch times are positive and strictly increasing;
* the weights of S6's word entrance are PIECES' stage weights (`StagedS7.imgStageRhoL_treeIdx`), which satisfy Zhan's
  strip hypotheses for the left span at even depth and for the right span at odd depth
  (`Prop59Stage.hwL_of_isStageInit`, `hwR_of_isStageInit`);
* **`ae_exit_cand`**: almost surely the full staged image arc has a finite terminal capacity and its killed trace
  converges there to a real point beyond the left junction (even depth, `ae_restartExitL`) or beyond the right junction
  (odd depth, `ae_restartExitR`);
* **`exists_isKilledStageRep_cand`**: the restarted word in tree order has the stopped representation
  `StagedKCand.IsKilledStageRep` with PIECES' stage weights `stageρL κ (rootρL κ c) (j + 1)`, far marks `farL`,
  `farR`, start `(0, V(0))`, the past `candFilt 0` (read on the first factor), the stage event `univ` and the
  filtration `prodFiltration (usualAugmentation candFilt μ_A) 𝓦`: strict start (`StagedS7.strictAnti_s6Start`),
  threshold failing at time `0` (`StagedS7.not_threshold_stage`), killing at the far marks with left limits
  (`StagedS7.isKilledAtFarLim_s6`) and a trace up to the lifetime (`StagedS7.exists_isGeneratingTrace_s3W`).

Conditional helpers with distinct names; they replace no source theorem. R48: the only named input is `h44`
(`Theorem12ParamCond44Statement`, R74, through PROVE-STAGED-S4/S5/S6); nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS7

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q Word49 Theta StagedS3 StagedS4 StagedS5 StagedS6
open Restart Exist.StagedLaw Exist.Staged MartChar.RealFlow
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target StagedGlue StagedDepth Prop59Pieces StagedRepLater
open Prop59Stage Prop59System
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)
open StagedFinal (imgStageRhoL imgStageRhoR)

/-! ### The candidate's switch times -/

section Times

variable {ℓ : ℕ} {t : Fin ℓ → ℝ≥0}

/-- **The candidate's switch times are positive and strictly increasing.** -/
theorem strictMono_candTs (hv : IsValid ℓ t) :
    (∀ j : Fin ℓ, 0 < candTs ℓ t (j + 1) ∧ candTs ℓ t (j + 1) ≤ (lastO ℓ t : ℝ)) ∧
      StrictMono fun j : Fin ℓ => candTs ℓ t (j + 1) := by
  refine ⟨fun j => ⟨?_, (candTs_bounds hv j).2⟩, fun j j' hjj => ?_⟩
  · rw [candTs_succ hv j]
    exact_mod_cast oTime_pos hv j
  · simp only [candTs_succ hv]
    rw [oTime_eq (hv.2 j).2.2, oTime_eq (hv.2 j').2.2]
    exact decode_strictMono (hv.2 j').2.1 (hv.1 hjj)

end Times

/-! ### Good counterflow histories -/

section Good

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] in
include h44 hκ hκ4 hb in
/-- **Almost every glued sample has a good counterflow history** (`goodSet49`: good hitting history, junctions off the
driver), for PIECES' candidate measure. -/
theorem ae_goodSet49_cand (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {s : ℝ≥0} (hs : 0 < s) :
    ∀ᵐ p ∂(candMu x₀ (κ := κ) P h W ζ hG.1), p.2 ∈ goodSet49 s := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  have hhm : Measurable h := hG.1
  obtain ⟨_, 𝓕, VL, VR, B, hC⟩ := exists_rootCoupling h44 hκ hκ4 hb (P := P) hhm hG
  have hcfc := isCenteredCounterflowDriver_of_strip hκ hcf
  have hcfm := measurable_cfHistory_of_strip hcf
  have hqm : Measurable (qField x₀ κ h) :=
    (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hk : P.map (fun ω => (qField x₀ κ h ω, Cond44Ref.cfHistory W ζ ω)) =
      P.map (qField x₀ κ h) ⊗ₘ candK x₀ (κ := κ) P h W ζ :=
    (compProd_map_condDistrib hqm.aemeasurable hcfm.aemeasurable).symm
  have hlaw : P.map (fun ω => cfFieldT κ (π / 2) (rootField (κ := κ) (x₀ := x₀) h ω)) =
      P.map (qField x₀ κ h) := by
    congr 1
    funext ω
    rw [cfFieldT_pi_div_two]
    exact cfField_rootField ω
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have h44' : Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2)) (flowLineRhoR κ c.fn c.jumps 0 (π / 2)) :=
    cond44_upper hκ (sourceWord_extreme hκ hb)
  have hθb := cfThetaBounds_of_cond44 hκ hκ4 hF h44'
  have hcfg := ae_cfGood_glueT hκ hC hθb hcfc hlaw (candK x₀ (κ := κ) P h W ζ) hk hs
  filter_upwards [hcfg] with p hp
  exact hp.2

end Good

/-! ### Helpers -/

section Help

/-- A stage word of any size whose left index type is `Fin (m + 1)` is a stage word. -/
theorem isStageWord_of_N {κ : ℝ} {m n : ℕ} {ρL : Fin (m + 1) → ℝ} {ρR : Fin n → ℝ}
    (h : IsStageWordN κ ρL ρR) : Prop59Tips.IsStageWord κ ρL ρR := by
  obtain ⟨k, hk, hw⟩ := h
  have hkm : k = m := by omega
  subst hkm
  exact hw

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {s : ℝ≥0} {y : HistorySpace 0 0}

/-- On a good sample the time-`0` left marks of the image arc are `≤ 0`. -/
theorem imgMarkL_nonpos (hxL : ∀ i, xL i ≤ 0) (hj : 0 < rightImg (cfDrv0 s y) 0 s - cfDrv0 s y s) (k : Fin (nL + 1)) :
    GlueImg.imgMarkL xL (cfDrv0 s y) s k ≤ 0 := by
  have hc := continuous_cfDrv0 s y
  exact snoc_le (fun i => psiL_nonpos hc s.coe_nonneg hj (hxL i))
    ((junL_le_psiL hc s.coe_nonneg hj le_rfl).trans (psiL_nonpos hc s.coe_nonneg hj le_rfl)) k

/-- On a good sample the time-`0` right marks of the image arc are `≥ 0`. -/
theorem imgMarkR_nonneg (hxR : ∀ j, 0 ≤ xR j) (hj : -rightImg (fun r => -cfDrv0 s y r) 0 s - cfDrv0 s y s < 0)
    (k : Fin (nR + 1)) : 0 ≤ GlueImg.imgMarkR xR (cfDrv0 s y) s k := by
  have hc := continuous_cfDrv0 s y
  exact le_snoc (fun j => psiR_nonneg hc s.coe_nonneg hj (hxR j))
    ((psiR_nonneg hc s.coe_nonneg hj le_rfl).trans (psiR_le_junR hc s.coe_nonneg hj le_rfl)) k

end Help

/-! ### The stopped representation of the candidate after its last switch -/

section Rep

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

include hκ4 in
/-- **Proposition 5.9's killed stage law at depth `j + 1`, in stopped-representation form, on the conditioned glued
space** (PROVE-STAGED-S6 §5 item 1). For PIECES' candidate `(j + 1, t)`, conditioned on the alive event of its last
switch (`μ_A`) and extended by the standard noise space, the restarted word in tree order (driver `s3W`, marks `s6VL`,
`s6VR`, lifetime `s3ζ`) has the stopped representation `IsKilledStageRep` with PIECES' stage weights of the root word,
far marks `farL`, `farR` (the two junctions), start `(0, V(0))`, past `candFilt 0` on the first factor and stage event
`univ`, its noise being the Brownian motion of S6's word entrance. -/
theorem exists_isKilledStageRep_cand (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {us : ℂ → ℝ}
    (hus : IsBoundedHarmonicExtension (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps us)
    {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) {s : ℝ≥0} (hs : 0 < s)
    (hA0 : candMu x₀ (κ := κ) P h W ζ hG.1 (s3Alive s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
      (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (lastO (j + 1) t : ℝ)) ≠ 0) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (B : ℝ≥0 → (Ω × HistorySpace 0 0) × (ℕ → ℝ) → ℝ),
      StagedKCand.IsKilledStageRep κ
        (((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (lastO (j + 1) t : ℝ)]).prod P₀)
        (MeasurableSpace.comap Prod.fst (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0)) univ
        (stageρL κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
        (stageρR κ (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) (j + 1))
        (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ (j + 1))))
        (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ (j + 1))))
        (fun p => ((0 : ℝ),
          fun i => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (lastO (j + 1) t : ℝ) i 0 p.1,
          fun k => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
            (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (lastO (j + 1) t : ℝ) k 0 p.1))
        (fun r p => s3W s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s)
          (lastO (j + 1) t : ℝ) r p.1)
        (fun i r p => s6VL (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (lastO (j + 1) t : ℝ) i r p.1)
        (fun k r p => s6VR (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps 0)
          (candTs (j + 1) t) (j + 1) s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
          (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (lastO (j + 1) t : ℝ) k r p.1) B
        (fun p => s3ζ s (candW x₀ h44 hκ hκ4 hb h (j + 1) t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s)
          (lastO (j + 1) t : ℝ) p.1)
        (WholeField.prodFiltration (usualAugmentation (candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs)
          ((candMu x₀ (κ := κ) P h W ζ hG.1)[|s3Alive s (candW x₀ h44 hκ hκ4 hb h (j + 1) t)
            (candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s) (lastO (j + 1) t : ℝ)])) 𝓦) B := by
  set c := sourceWord (x₀ := x₀) hκ hb with hc
  set Wc := candW x₀ h44 hκ hκ4 hb h (j + 1) t with hWc
  set Eg := candEg x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s with hEgdef
  set τ : ℝ := (lastO (j + 1) t : ℝ) with hτ
  set μ := candMu x₀ (κ := κ) P h W ζ hG.1 with hμ
  set A := s3Alive s Wc Eg τ with hAdef
  set μA := μ[|A] with hμA
  set 𝓐 := candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs with h𝓐
  set xLc := flowLineXL c.fn c.jumps 0 with hxLc
  set xRc := flowLineXR c.fn c.jumps 0 with hxRc
  have hEg := candEg_good x₀ h44 hκ hκ4 hb P h W ζ hG.1 (j + 1) t s
  have hF := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hxLs : StrictAnti xLc := fun i i' hii => Theorem14.GW0.flowLineXL_lt c.fn c.jumps 0 hii
  have hxRs : StrictMono xRc := fun i i' hii => Theorem14.GW0.flowLineXR_lt c.fn c.jumps 0 hii
  obtain ⟨hτs, hτm⟩ := strictMono_candTs hv
  have hτs' : ∀ k : Fin (j + 1), 0 ≤ candTs (j + 1) t (k + 1) ∧ candTs (j + 1) t (k + 1) ≤ τ := fun k =>
    ⟨(hτs k).1.le, (hτs k).2⟩
  have hK := isKilledWord_s6 (xL := xLc) (xR := xRc) hEg hF.2.1 hF.1 hF.2.2.2 hF.2.2.1 hτs' hτm.monotone
  obtain ⟨P₀, hP₀, 𝓦, B, hB, hBc, hEnt⟩ := exists_isWordEntrance_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf hus hv hs hA0
  refine ⟨P₀, hP₀, 𝓦, B, ?_⟩
  have hμA1 : IsProbabilityMeasure μA := cond_isProbabilityMeasure hA0
  have hρL : (fun i => imgStageRhoL κ (π / 2) (flowLineRhoL κ c.fn c.jumps 0 (π / 2))
      (fun k => candAng (j + 1) t k - candAng (j + 1) t 0) (j + 1) (treeIdx (j + 1) _ i)) =
      stageρL κ (rootρL κ c) (j + 1) := funext fun i => imgStageRhoL_treeIdx hv _ i
  have hρR : (fun i => imgStageRhoR κ (π / 2) (flowLineRhoR κ c.fn c.jumps 0 (π / 2))
      (fun k => candAng (j + 1) t k - candAng (j + 1) t 0) (j + 1) (treeIdx (j + 1) _ i)) =
      stageρR κ (rootρR κ c) (j + 1) := funext fun i => imgStageRhoR_treeIdx hv _ i
  rw [hρL, hρR] at hEnt
  -- the filtration
  set 𝓖 := usualAugmentation 𝓐 μA with h𝓖
  have hle : 𝓐 ≤ 𝓖 := Ito.le_usualAugmentation 𝓐 μA
  have hWa : StronglyAdapted 𝓖 (s3W s Wc Eg τ) := fun r =>
    (stronglyAdapted_s3W_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r).mono (hle r)
  have hVLa : ∀ i, StronglyAdapted 𝓖 (s6VL xLc (candTs (j + 1) t) (j + 1) s Wc Eg τ i) := fun i r =>
    (stronglyAdapted_s6VL_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs xLc i r).mono (hle r)
  have hVRa : ∀ k, StronglyAdapted 𝓖 (s6VR xRc (candTs (j + 1) t) (j + 1) s Wc Eg τ k) := fun k r =>
    (stronglyAdapted_s6VR_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs xRc k r).mono (hle r)
  have hζq : ∀ r : ℝ≥0, MeasurableSet[𝓖 r] {p | (r : ℝ≥0∞) < s3ζ s Wc Eg τ p} := fun r =>
    hle r _ (measurableSet_lt_s3ζ_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs r)
  have hTst : IsStoppingTime 𝓖 (fun p => (s3ζ s Wc Eg τ p : WithTop ℝ≥0)) := fun r => by
    have h1 := (hζq r).compl
    convert h1 using 1
    ext p
    exact (not_lt (a := (r : WithTop ℝ≥0)) (b := (s3ζ s Wc Eg τ p : WithTop ℝ≥0))).symm
  have hTst' := Sec7.PhaseSelFull.isStoppingTime_fst (𝓦 := 𝓦) hTst
  have hAd : ∀ X : ℝ≥0 → Ω × HistorySpace 0 0 → ℝ, StronglyAdapted 𝓖 X →
      AdaptedBefore (WholeField.prodFiltration 𝓖 𝓦) (fun p => (s3ζ s Wc Eg τ p.1 : ℝ≥0∞))
        (fun r p => X r p.1) := fun X hX =>
    Sec7.PhaseSelFull.adaptedBefore_of_stronglyAdapted' (Sec7.PhaseSelFull.stronglyAdapted_fst hX) hTst'
  have hTq : ∀ q : ℝ≥0, MeasurableSet[WholeField.prodFiltration 𝓖 𝓦 q]
      {p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) | (q : ℝ≥0∞) < s3ζ s Wc Eg τ p.1} := fun q =>
    WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 q _ ⟨_, hζq q, rfl⟩
  have hT0 : ∀ p : (Ω × HistorySpace 0 0) × (ℕ → ℝ), 0 < s3ζ s Wc Eg τ p.1 := fun p =>
    StagedS6.zero_lt_arcζ (fun p => StagedS5.s3Start_lt_kLife' hEg τ p) p.1
  -- almost sure facts on the first factor
  have hAmeas : MeasurableSet A :=
    𝓐.le 0 _ (measurableSet_s3Alive_candFilt x₀ h44 hκ hκ4 hb P h W ζ hG hcf us hv hs 0)
  have hgood : ∀ᵐ p ∂μA, p ∈ A ∧ p ∈ Eg ∧ p.2 ∈ goodSet49 s := by
    filter_upwards [ae_cond_mem hAmeas,
      cond_absolutelyContinuous.ae_le (ae_goodSet49_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf hs),
      cond_absolutelyContinuous.ae_le (ae_good_cand x₀ h44 hκ hκ4 hb P h W ζ hG hcf (j + 1) t hv hs)]
      with p hpA hy hgc
    exact ⟨hpA, hgc.1, hy⟩
  have hgood' : ∀ᵐ p ∂(μA.prod P₀), p.1 ∈ A ∧ p.1 ∈ Eg ∧ p.1.2 ∈ goodSet49 s :=
    Measure.quasiMeasurePreserving_fst.ae hgood
  -- strict start and threshold at time `0`
  have hstr : ∀ p : Ω × HistorySpace 0 0, p ∈ A → p.2 ∈ goodSet49 s →
      StrictAnti (fun i => s6VL xLc (candTs (j + 1) t) (j + 1) s Wc Eg τ i 0 p) ∧
        StrictMono (fun k => s6VR xRc (candTs (j + 1) t) (j + 1) s Wc Eg τ k 0 p) := fun p hp hy =>
    ⟨strictAnti_s6Start hEg hp hy hF.2.1 hxLs hτs hτm, strictMono_s6Start hEg hp hy hF.2.2.2 hxRs hτs hτm⟩
  have hO : ∀ p : Ω × HistorySpace 0 0, IsOrderedForceWord
      (fun i => s6VL xLc (candTs (j + 1) t) (j + 1) s Wc Eg τ i 0 p)
      (fun k => s6VR xRc (candTs (j + 1) t) (j + 1) s Wc Eg τ k 0 p) :=
    isOrderedForceWord_s6Start hEg hF.2.1 hF.1 hF.2.2.2 hF.2.2.1 hτs' hτm.monotone
  have hthr0 : ∀ p : Ω × HistorySpace 0 0, p ∈ A → p.2 ∈ goodSet49 s →
      ¬ ForceWord.ThresholdCondition (stageρL κ (rootρL κ c) (j + 1)) (stageρR κ (rootρR κ c) (j + 1))
        (s3W s Wc Eg τ 0 p) (fun i => s6VL xLc (candTs (j + 1) t) (j + 1) s Wc Eg τ i 0 p)
        (fun k => s6VR xRc (candTs (j + 1) t) (j + 1) s Wc Eg τ k 0 p) := by
    intro p hp hy
    obtain ⟨hsA, hsM⟩ := hstr p hp hy
    have hW0 : s3W s Wc Eg τ 0 p = 0 := StagedS6.arcW_zero p
    rw [hW0]
    exact not_threshold_stage hκ hκ4 (Nat.succ_pos j) (rootρL κ c) (rootρR κ c) hsA hsM ((hO p).2.1 _)
      ((hO p).2.2.2 _)
  have hthr : ∀ᵐ p ∂(μA.prod P₀), ¬ ForceWord.ThresholdCondition (stageρL κ (rootρL κ c) (j + 1))
      (stageρR κ (rootρR κ c) (j + 1)) (s3W s Wc Eg τ 0 p.1)
      (fun i => s6VL xLc (candTs (j + 1) t) (j + 1) s Wc Eg τ i 0 p.1)
      (fun k => s6VR xRc (candTs (j + 1) t) (j + 1) s Wc Eg τ k 0 p.1) := by
    filter_upwards [hgood'] with p hp
    exact hthr0 p.1 hp.1 hp.2.2
  -- the exit of the full staged arc through a far span
  have hγf : ∀ p : (Ω × HistorySpace 0 0) × (ℕ → ℝ),
      IsKilledArc (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) := fun p =>
    isKilledArc_gCurve hEg p.1
  have hζ' : ∀ (p : (Ω × HistorySpace 0 0) × (ℕ → ℝ)) (r : ℝ≥0), (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 ↔
      ((s3Start s Wc Eg τ p.1 + r : ℝ≥0) : WithTop ℝ≥0) <
        kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) := fun p r =>
    lt_arcζ_iff.trans ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hWk : ∀ (p : (Ω × HistorySpace 0 0) × (ℕ → ℝ)) (r : ℝ≥0), (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 →
      s3W s Wc Eg τ r p.1 = kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)
        (s3Start s Wc Eg τ p.1 + r) -
        kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) (s3Start s Wc Eg τ p.1) :=
    fun p r hr => arcW_of_lt hr
  have hnH : ∀ᵐ p ∂(μA.prod P₀), ∀ (T : ℝ≥0) (z : ℂ),
      (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) →
      Tendsto (kTrace (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)) (𝓝[<] T) (𝓝 z) →
        z ∉ H := by
    filter_upwards [hgood'] with p hp T z hT hz
    exact notMem_H_of_tendsto_gCurve hp.2.1 (hEg p.1 hp.2.1) hT hz
  have hexit : ∀ᵐ p ∂(μA.prod P₀), ∃ T : ℝ≥0,
      (T : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) ∧
      ∃ x₁ : ℝ, Tendsto (kTrace (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)) (𝓝[<] T)
          (𝓝 (x₁ : ℂ)) ∧
        (x₁ < GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _) ∨
          GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _) < x₁) := by
    rcases Nat.even_or_odd (j + 1) with hev | hod
    · have hw := isStageWord_of_N (m := rootNL c + j)
        (hwL_of_isStageInit hκ hκ4 (isStageInit_sourceWord (x₀ := x₀) hκ hb) (j + 1) hev)
      have hfar : ∀ᵐ p ∂(μA.prod P₀), ∀ r : ℝ≥0, (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 →
          s6VL xLc (candTs (j + 1) t) (j + 1) s Wc Eg τ (Fin.last (rootNL c + j)) r p.1 - s3W s Wc Eg τ r p.1 =
            -kImg (fun r => -kPath (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) r)
                (-GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _)) (s3Start s Wc Eg τ p.1 + r) -
              kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) (s3Start s Wc Eg τ p.1 + r) := by
        filter_upwards [hgood'] with p hp r hr
        exact s6VL_far_sub hEg hp.1 hτs' (by simp only [Fin.val_last, rootNL]; omega) hr
      have ha : ∀ᵐ p ∂(μA.prod P₀), GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _) ≤ 0 := by
        filter_upwards [hgood'] with p hp
        obtain ⟨-, -, hjL, -, -⟩ := hEg p.1 hp.2.1
        exact imgMarkL_nonpos hF.2.1 hjL _
      have hX := ae_restartExitL (m := rootNL c + j) hκ hκ4.le hw.2.1 (Prop59Tips.abs_charge_lt_of_sum hκ hκ4 _ hw.1)
        hB hBc (Sec7.PhaseSelFull.stronglyAdapted_fst hWa)
        (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
        (fun k => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa k)) hTq hT0 hEnt
        (fun p r hr0 hr i => hK.sepL p.1 r hr0 hr i) (fun p r hr0 hr k => hK.sepR p.1 r hr0 hr k) hthr hγf hζ' hWk
        hfar ha hnH
      filter_upwards [hX] with p hp
      obtain ⟨T, hT, x₁, hx₁, hlim⟩ := hp
      exact ⟨T, hT, x₁, hlim, Or.inl hx₁⟩
    · have hw := isStageWord_of_N (m := rootNR c + j)
        (hwR_of_isStageInit hκ hκ4 (isStageInit_sourceWord (x₀ := x₀) hκ hb) (j + 1)
          (Nat.not_even_iff_odd.2 hod))
      have hfar : ∀ᵐ p ∂(μA.prod P₀), ∀ r : ℝ≥0, (r : ℝ≥0∞) < s3ζ s Wc Eg τ p.1 →
          s6VR xRc (candTs (j + 1) t) (j + 1) s Wc Eg τ (Fin.last (rootNR c + j)) r p.1 - s3W s Wc Eg τ r p.1 =
            kImg (kPath (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1))
                (GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _)) (s3Start s Wc Eg τ p.1 + r) -
              kW (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) (s3Start s Wc Eg τ p.1 + r) := by
        filter_upwards [hgood'] with p hp r hr
        exact s6VR_far_sub hEg hp.1 hτs' (by simp only [Fin.val_last, rootNR]; omega) hr
      have hb' : ∀ᵐ p ∂(μA.prod P₀), 0 ≤ GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _) := by
        filter_upwards [hgood'] with p hp
        obtain ⟨-, -, -, hjR, -⟩ := hEg p.1 hp.2.1
        exact imgMarkR_nonneg hF.2.2.2 hjR _
      have hX := ae_restartExitR (n := rootNR c + j) hκ hκ4.le hw.2.1
        (Prop59Tips.abs_charge_lt_of_sum hκ hκ4 _ hw.1)
        hB hBc (Sec7.PhaseSelFull.stronglyAdapted_fst hWa)
        (fun i => Sec7.PhaseSelFull.stronglyAdapted_fst (hVLa i))
        (fun k => Sec7.PhaseSelFull.stronglyAdapted_fst (hVRa k)) hTq hT0 hEnt
        (fun p r hr0 hr i => hK.sepL p.1 r hr0 hr i) (fun p r hr0 hr k => hK.sepR p.1 r hr0 hr k) hthr hγf hζ' hWk
        hfar hb' hnH
      filter_upwards [hX] with p hp
      obtain ⟨T, hT, x₁, hx₁, hlim⟩ := hp
      exact ⟨T, hT, x₁, hlim, Or.inr hx₁⟩
  -- the stopped representation
  refine StagedRep.isKilledStageRep_of_entrance ?_ hB (hAd _ hWa) (fun i => hAd _ (hVLa i))
    (fun k => hAd _ (hVRa k)) ?_
  · exact (MeasurableSpace.comap_mono (hle 0)).trans (WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 0)
  filter_upwards [hgood', hEnt, hexit] with p hp hE hX _
  obtain ⟨hpA, hpE, hy⟩ := hp
  obtain ⟨hsA, hsM⟩ := hstr p.1 hpA hy
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p.1 hpE
  obtain ⟨T, hT, x₁, hlim, hside⟩ := hX
  have hexit' : ∀ T' : ℝ≥0,
      (T' : WithTop ℝ≥0) = kLife (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1) →
      ∃ x₂ : ℝ, Tendsto (kTrace (gCurve s (fun _ => ⊤) Wc Eg p.1) (gPre s (fun _ => ⊤) Wc Eg p.1)) (𝓝[<] T')
          (𝓝 (x₂ : ℂ)) ∧
        (x₂ < GlueImg.imgMarkL xLc (cfDrv0 s p.1.2) s (Fin.last _) ∨
          GlueImg.imgMarkR xRc (cfDrv0 s p.1.2) s (Fin.last _) < x₂) := by
    intro T' hT'
    have hTT : T' = T := WithTop.coe_injective (hT'.trans hT.symm)
    subst hTT
    exact ⟨x₁, hlim, hside⟩
  have hx₁ : x₁ ≠ 0 := by
    rcases hside with h' | h'
    · linarith [imgMarkL_nonpos hF.2.1 hjL (Fin.last _)]
    · linarith [imgMarkR_nonneg hF.2.2.2 hjR (Fin.last _)]
  refine ⟨hO p.1, hsA, hsM, hE, hthr0 p.1 hpA hy, fun r hr0 hr i => hK.sepL p.1 r hr0 hr i,
    fun r hr0 hr k => hK.sepR p.1 r hr0 hr k, ?_, exists_isGeneratingTrace_s3W hEg p.1 hT hx₁ hlim⟩
  exact isKilledAtFarLim_s6 hEg hpA hF.2.1 hF.1 hF.2.2.2 hF.2.2.1 hτs' hτm.monotone (Nat.succ_pos j) hsA hsM
    (by simp only [farL, rootNL]; omega) (by simp only [farR, rootNR]; omega) hexit'

end Rep

end InteractingSLE.Sec5.CrossCond.StagedS7
