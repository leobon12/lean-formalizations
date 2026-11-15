/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterStd
import InteractingSLE.Spec.Sec5.StagedRepLaterDil
import InteractingSLE.Spec.Sec5.StagedRepStrict
import InteractingSLE.Spec.Sec5.StagedKCandDisint
import InteractingSLE.Spec.Sec5.CrossCondMartStop

/-!
# Prop 5.9's root stage: the killed comparison clause on the glued space

Packet PROVE-STAGED-REP2. PROVE-STAGED-REP proved the stopped representation of the root stage (Proposition 4.9's
killed image word, read in the counterflow chart of the stopped counterflow) on `glue × Ω₀` with an existential noise
space `Ω₀`, so the disintegration over the past (`StagedKCand.IsStoppedRep.isStageLawFarK`, which needs a standard
Borel space) could not be applied. Here:

* `exists_isKilledStageRep_img_std`: the same representation on `glue × (ℕ → ℝ)` (`exists_isWordEntrance_std`);
* `histStart`: the stage start as a Borel function of the counterflow history stopped at `s` (it agrees almost surely
  with the image marks at time `0`);
* **`compClauseK_img`**: the comparison clause of the killed stage law (`CompClauseK`, ruling R78) of the image word on
  the glued space itself, for the past `σ(cfStop s)`, when the flow space `Ω` is standard Borel;
* **`compClauseK_img_dil`**: the same for the image word dilated by a Borel function of the start
  (`CompClauseK.dilate`), the form of PROVE-PROP59-PIECES' root candidates.

The only named input is the deterministic `StagedRep.KilledArcSwallowStatement` (PROVE-KILLARC). R48: nothing here
uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond.Word49 MartChar.RealFlow Prop49Exit LawUnique Cond44Ref Prop411Q
open Prop59Stage Prop59Nodes StagedKill StagedKCand StagedRep GlueCond

/-! ### The representation with the standard noise space -/

section Std

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The stopped representation of the root stage on `glue × (ℕ → ℝ)`** (PROVE-STAGED-REP's
`exists_isKilledStageRep_img'` with the standard noise space; same proof through `exists_isWordEntrance_std`). -/
theorem exists_isKilledStageRep_img_std (hsw : KilledArcSwallowStatement) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hxLs : StrictAnti xL) (hxRs : StrictMono xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × (ℕ → ℝ) → ℝ),
      IsKilledStageRep κ ((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀)
        (cfPast s (ℕ → ℝ)) univ (jwL cL6 κ ρL) (jwR cR6 κ ρR) (Fin.last nL) (Fin.last nR)
        (fun p => ((0 : ℝ), fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) i 0 p.1,
          fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) j 0 p.1))
        (fun t p => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) t p.1)
        (fun i t p => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) i t p.1)
        (fun j t p => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) j t p.1) Bi
        (fun p => (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) s ζ W) p.1 : ℝ≥0∞))
        (WholeField.prodFiltration (imgFilt (glueMeasure P k (fun ω => cfField κ (h ω))
          ((measurable_cfField κ).comp hC.2.1)) xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W)) 𝓦) Bi := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨hnull, hK, hWa, hVLa, hVRa, hσ, hσm, hσT, hσlim, hζq⟩ :=
    filtClauses (μ := μ) (xL := xL) (xR := xR) hWad hF hae
  obtain ⟨P₀, hP₀, 𝓦, Bi, hB, -, hEnt⟩ := exists_isWordEntrance_std hκ hnull hK hWa hVLa hVRa hσ hσm hσT hσlim
    (imageWord49FiltCStatement κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)
  refine ⟨P₀, hP₀, 𝓦, Bi, ?_⟩
  set 𝓖 := imgFilt μ xL xR s ζ W E with h𝓖
  have hTst : IsStoppingTime 𝓖 (imgT s ζ W E) := fun t => by
    have h1 := (hζq t).compl
    convert h1 using 1
    ext p
    exact (not_lt (a := (t : WithTop ℝ≥0)) (b := imgT s ζ W E p)).symm
  have hTst' := Sec7.PhaseSelFull.isStoppingTime_fst (𝓦 := 𝓦) hTst
  have hAd : ∀ X : ℝ≥0 → Ω × HistorySpace 0 0 → ℝ, StronglyAdapted 𝓖 X →
      AdaptedBefore (WholeField.prodFiltration 𝓖 𝓦) (fun p => (imgT s ζ W E p.1 : ℝ≥0∞))
        (fun t p => X t p.1) := fun X hX =>
    Sec7.PhaseSelFull.adaptedBefore_of_stronglyAdapted' (Sec7.PhaseSelFull.stronglyAdapted_fst hX) hTst'
  have hfar := ae_imgFar hκ hκ4 hF h44 hC hcf hlaw k hk hs
  have hstr := ae_strict_imgStart hκ hκ4 hF h44 hxLs hxRs hC hcf hlaw k hk hs
  have h0 : ∀ᵐ p ∂μ, p ∈ E ∧ (∃ (T : ℝ≥0) (x₀ : ℝ), (T : WithTop ℝ≥0) = imgT s ζ W E p ∧
      x₀ < gXL xL s E p (Fin.last nL) ∧ Tendsto (imgTr s ζ W E p) (𝓝[<] T) (𝓝 (x₀ : ℂ))) ∧
      StrictAnti (fun i => imgVL xL s ζ W E i 0 p) ∧ StrictMono (fun j => imgVR xR s ζ W E j 0 p) := by
    filter_upwards [hfar, hstr] with p hp hp'
    exact ⟨hp.1, hp.2, hp'⟩
  have h1 : ∀ᵐ p ∂(μ.prod P₀), p.1 ∈ E ∧ (∃ (T : ℝ≥0) (x₀ : ℝ), (T : WithTop ℝ≥0) = imgT s ζ W E p.1 ∧
      x₀ < gXL xL s E p.1 (Fin.last nL) ∧ Tendsto (imgTr s ζ W E p.1) (𝓝[<] T) (𝓝 (x₀ : ℂ))) ∧
      StrictAnti (fun i => imgVL xL s ζ W E i 0 p.1) ∧ StrictMono (fun j => imgVR xR s ζ W E j 0 p.1) :=
    Measure.quasiMeasurePreserving_fst.ae h0
  refine isKilledStageRep_of_entrance ?_ hB (hAd _ hWa) (fun i => hAd _ (hVLa i)) (fun j => hAd _ (hVRa j)) ?_
  · rintro A ⟨S, hS, rfl⟩
    exact WholeField.comap_fst_le_prodFiltration 𝓖 𝓦 0 _ ⟨_, measurable_cfStop_imgFilt 0 hS, rfl⟩
  filter_upwards [h1, hEnt] with p hp hEp _
  obtain ⟨hpE, ⟨T, x₀, hT, hx₀, hz⟩, hsA, hsM⟩ := hp
  have hγ := isKilledArc_gCurve hEg p.1
  have hT0 : (0 : ℝ≥0∞) < (imgT s ζ W E p.1 : ℝ≥0∞) := hγ.zero_lt_kLife
  have hVL0 : (fun i => imgVL xL s ζ W E i 0 p.1) = gXL xL s E p.1 := funext fun i => imgVL_zero hF.2.1 hEg p.1 i
  have hVR0 : (fun j => imgVR xR s ζ W E j 0 p.1) = gXR xR s E p.1 :=
    funext fun j => imgVR_zero hF.2.2.2 hEg p.1 j
  obtain ⟨-, -, hjL, hjR, -⟩ := hEg p.1 hpE
  have hjL0 : junL (cfDrv0 s p.1.2) s ≠ 0 := div_ne_zero (by norm_num) hjL.ne'
  have hjR0 : junR (cfDrv0 s p.1.2) s ≠ 0 := div_ne_zero (by norm_num) hjR.ne
  refine ⟨?_, hsA, hsM, hEp, not_threshold_img hκ hF h44 hEg hpE, fun t ht htT i => hK.sepL p.1 t ht htT i,
    fun t ht htT j => hK.sepR p.1 t ht htT j, ⟨hT0, fun t htT => ?_, fun T' hT' => ?_⟩, ?_⟩
  · show IsOrderedForceWord (fun i => imgVL xL s ζ W E i 0 p.1) (fun j => imgVR xR s ζ W E j 0 p.1)
    rw [hVL0, hVR0]
    exact ⟨antitone_gXL hF.2.1 hF.1 hEg p.1, gXL_nonpos hF.2.1 hEg p.1, monotone_gXR hF.2.2.2 hF.2.2.1 hEg p.1,
      gXR_nonneg hF.2.2.2 hEg p.1⟩
  · rcases eq_zero_or_pos t with rfl | ht0
    · have hL0 : imgVL xL s ζ W E (Fin.last nL) 0 p.1 = junL (cfDrv0 s p.1.2) s := by
        rw [imgVL_zero hF.2.1 hEg p.1, Word49.gXL_of_mem hpE, Fin.snoc_last]
      have hR0 : imgVR xR s ζ W E (Fin.last nR) 0 p.1 = junR (cfDrv0 s p.1.2) s := by
        rw [imgVR_zero hF.2.2.2 hEg p.1, Word49.gXR_of_mem hpE, Fin.snoc_last]
      rw [imgW_zero hEg, hL0, hR0]
      exact ⟨hjL0.symm, hjR0.symm⟩
    · exact ⟨(hK.sepL p.1 t ht0 htT (Fin.last nL)).ne', (hK.sepR p.1 t ht0 htT (Fin.last nR)).ne⟩
  · have hTT' : T' = T := by
      have : ((T' : ℝ≥0) : WithTop ℝ≥0) = (T : WithTop ℝ≥0) := by rw [hT]; exact hT'
      exact WithTop.coe_injective this
    subst hTT'
    have hxL := gXL_nonpos hF.2.1 hEg p.1
    obtain ⟨w₀, vL₀, vR₀, hw₀, hvL, hvR, hL, -⟩ := hsw (gCurve s ζ W E p.1) (gPre s ζ W E p.1) hγ
      (gXL xL s E p.1) (gXR xR s E p.1) hxL (antitone_gXL hF.2.1 hF.1 hEg p.1) (gXR_nonneg hF.2.2.2 hEg p.1)
      (monotone_gXR hF.2.2.2 hF.2.2.1 hEg p.1) T' x₀ hT (Or.inl hx₀) hz
    exact ⟨w₀, vL₀, vR₀, hw₀, hvL, hvR, Or.inl (hL hx₀)⟩
  · refine exists_isGeneratingTrace_of_Icc hT0 (fun t ht => isGeneratingTraceIcc_imgTr hEg p.1 ht)
      fun T' hT' => ⟨(x₀ : ℂ), ?_⟩
    have hTT' : T' = T := by
      have : ((T' : ℝ≥0) : WithTop ℝ≥0) = (T : WithTop ℝ≥0) := by rw [hT]; exact hT'
      exact WithTop.coe_injective this
    rw [hTT']
    exact hz

end Std

/-! ### The stage start as a function of the stopped counterflow history -/

section Start

variable {nL nR : ℕ}

/-- **The root stage start read from the counterflow history**: the driver at `0`, the chart images of the flow
word's marks and the two junctions (`Word49.gXL`/`gXR` without the good-set cut-off). -/
def histStart (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (s : ℝ≥0) (y : HistorySpace 0 0) : Start (nL + 1) (nR + 1) :=
  (0, Fin.snoc (fun i => psiL (cfDrv0 s y) s (xL i)) (junL (cfDrv0 s y) s),
    Fin.snoc (fun j => psiR (cfDrv0 s y) s (xR j)) (junR (cfDrv0 s y) s))

theorem histStart_cfStop (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (s : ℝ≥0) (y : HistorySpace 0 0) :
    histStart xL xR s (cfStop s y) = histStart xL xR s y := by
  simp only [histStart, cfDrv0_cfStop]

theorem measurable_histStart (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (s : ℝ≥0) : Measurable (histStart xL xR s) :=
  measurable_const.prodMk ((Word49.measurable_snoc (measurable_pi_iff.2 fun i => Word49.measurable_psiL s (xL i))
    (Word49.measurable_junL s)).prodMk (Word49.measurable_snoc
      (measurable_pi_iff.2 fun j => Word49.measurable_psiR s (xR j)) (Word49.measurable_junR s)))

/-- The start is measurable for the stopped counterflow history: on any space with a history coordinate `Y`,
`histStart ∘ Y` is `σ(cfStop s ∘ Y)`-measurable. -/
theorem measurable_histStart_comap {α : Type*} (Y : α → HistorySpace 0 0) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (s : ℝ≥0) :
    Measurable[MeasurableSpace.comap (fun a => cfStop s (Y a)) inferInstance] fun a => histStart xL xR s (Y a) := by
  intro S hS
  refine ⟨histStart xL xR s ⁻¹' S, measurable_histStart xL xR s hS, ?_⟩
  ext a
  simp only [mem_preimage, histStart_cfStop]

/-- On good glued samples the image marks at time `0` form `histStart`. -/
theorem imgStart_eq_histStart {Ω : Type*} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {E : Set (Ω × HistorySpace 0 0)} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) :
    (((0 : ℝ), fun i => imgVL xL s ζ W E i 0 p, fun j => imgVR xR s ζ W E j 0 p) : Start (nL + 1) (nR + 1)) =
      histStart xL xR s p.2 := by
  have h1 : (fun i => imgVL xL s ζ W E i 0 p) = gXL xL s E p := funext fun i => imgVL_zero hF.2.1 hEg p i
  have h2 : (fun j => imgVR xR s ζ W E j 0 p) = gXR xR s E p := funext fun j => imgVR_zero hF.2.2.2 hEg p j
  rw [h1, h2, Word49.gXL_of_mem hp, Word49.gXR_of_mem hp]
  rfl

end Start

/-! ### Changing the start on a null set; descending from a product -/

section Congr

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}

/-- A stopped representation reads its start only almost surely. -/
theorem _root_.InteractingSLE.Sec5.CrossCond.StagedKCand.IsKilledStageRep.congr_ae_start {Ω : Type*}
    {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω} {y y' : Ω → Start nL nR}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {𝓕 : Filtration ℝ≥0 mΩ} {B' : ℝ≥0 → Ω → ℝ}
    (h : IsKilledStageRep κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ 𝓕 B') (hy : ∀ᵐ ω ∂P, y ω = y' ω) :
    IsKilledStageRep κ P 𝓠 R ρL ρR iL iR y' W VL VR B ζ 𝓕 B' :=
  { h with
    ae_path := by
      filter_upwards [h.ae_path, hy] with ω hω he hR
      rw [← he]
      exact hω hR }

/-- **The comparison clause descends from a product with an independent factor** (the factor carries only the
driving noise). -/
theorem CompClauseK.of_prod_fst {Ω Ω₀ : Type*} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace Ω₀] {P : Measure Ω} {P₀ : Measure Ω₀} [SFinite P] [IsProbabilityMeasure P₀] (h𝓠 : 𝓠 ≤ mΩ)
    {R : Set Ω} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (h : CompClauseK κ (P.prod P₀) (𝓠.comap Prod.fst) (Prod.fst ⁻¹' R) ρL ρR iL iR (fun p => y p.1)
      (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) (fun p => ζ p.1)) :
    CompClauseK κ P 𝓠 R ρL ρR iL iR y W VL VR ζ := by
  intro S hS p hp A hA hAR
  have hA' : MeasurableSet[𝓠.comap Prod.fst] (Prod.fst ⁻¹' A : Set (Ω × Ω₀)) := ⟨A, hA, rfl⟩
  have hle := h S hS p hp _ hA' (preimage_mono hAR)
  have hAm : MeasurableSet A := h𝓠 _ hA
  have e1 : (P.prod P₀) (Prod.fst ⁻¹' A) = P A := by
    rw [← Measure.map_apply measurable_fst hAm, Measure.map_fst_prod, measure_univ, one_smul]
  have e2 : (Prod.fst ⁻¹' A ∩ {p : Ω × Ω₀ | ((fun p => y p.1) p, samp ((fun t p => W t p.1) · p)
      (fun i t => (fun i t p => VL i t p.1) i t p) (fun k t => (fun j t p => VR j t p.1) k t p)
      ((fun p => ζ p.1) p)) ∈ S}) =
      Prod.fst ⁻¹' (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  rw [e1, e2] at hle
  refine hle.trans ?_
  calc (P.prod P₀) (Prod.fst ⁻¹' (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω)
        (ζ ω)) ∈ S}))
      ≤ ((P.prod P₀).map Prod.fst) (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω)
        (fun k t => VR k t ω) (ζ ω)) ∈ S}) := Measure.le_map_apply measurable_fst.aemeasurable _
    _ = P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]

end Congr

/-! ### The comparison clause of the root stage on the glued space -/

section Clause

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The killed comparison clause of Proposition 5.9's root stage on the glued space** (Proposition 4.9's killed
image word in the counterflow chart of the counterflow stopped at `s`, past `σ(cfStop s)`, start `histStart`): the
standard-noise representation, its start changed on a null set, disintegrated over the past
(`IsStoppedRep.isStageLawFarK`) and descended from the noise factor. -/
theorem compClauseK_img (hsw : KilledArcSwallowStatement) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hxLs : StrictAnti xL) (hxRs : StrictMono xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    CompClauseK κ (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
      (MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cfStop s p.2) inferInstance) univ
      (jwL cL6 κ ρL) (jwR cR6 κ ρR) (Fin.last nL) (Fin.last nR) (fun p => histStart xL xR s p.2)
      (imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W))
      (imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W))
      (imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W))
      (fun p => (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) p : ℝ≥0∞)) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hEae : ∀ᵐ p ∂μ, p ∈ E := by
    have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
      filter_upwards [cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
        hlaw k hk] with p hp
      exact isGood49_of_mem hp.1 hp.2
    exact ae_mem_glueGood hae
  obtain ⟨P₀, hP₀, 𝓦, Bi, hrep⟩ := exists_isKilledStageRep_img_std hsw hκ hκ4 hF h44 hxLs hxRs hC hcf hlaw k hk hs
  have hy : ∀ᵐ p ∂(μ.prod P₀), (((0 : ℝ), fun i => imgVL xL s ζ W E i 0 p.1, fun j => imgVR xR s ζ W E j 0 p.1) :
      Start (nL + 1) (nR + 1)) = histStart xL xR s p.1.2 := by
    have h0 : ∀ᵐ p ∂μ, (((0 : ℝ), fun i => imgVL xL s ζ W E i 0 p, fun j => imgVR xR s ζ W E j 0 p) :
        Start (nL + 1) (nR + 1)) = histStart xL xR s p.2 := by
      filter_upwards [hEae] with p hp
      exact imgStart_eq_histStart hF hEg hp
    exact Measure.quasiMeasurePreserving_fst.ae h0
  have hrep' := hrep.congr_ae_start hy
  have : StandardBorelSpace (Ω × HistorySpace 0 0) := StandardBorelSpace.prod
  have : StandardBorelSpace ((Ω × HistorySpace 0 0) × (ℕ → ℝ)) := StandardBorelSpace.prod
  have hyQ : Measurable[cfPast s (ℕ → ℝ)] fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => histStart xL xR s p.1.2 :=
    measurable_histStart_comap (fun p : (Ω × HistorySpace 0 0) × (ℕ → ℝ) => p.1.2) xL xR s
  have hobs := measurable_samp_of_adaptedBefore hrep'.adapted_W hrep'.adapted_VL hrep'.adapted_VR
  have hL := hrep'.isStoppedRep.isStageLawFarK hκ MeasurableSet.univ hyQ hobs
  have hle : MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cfStop s p.2) inferInstance ≤
      (inferInstance : MeasurableSpace (Ω × HistorySpace 0 0)) :=
    (measurable_cfStop s |>.comp measurable_snd).comap_le
  refine CompClauseK.of_prod_fst (P₀ := P₀) hle ?_
  have e𝓠 : (MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cfStop s p.2) inferInstance).comap
      (Prod.fst : (Ω × HistorySpace 0 0) × (ℕ → ℝ) → Ω × HistorySpace 0 0) = cfPast s (ℕ → ℝ) := by
    rw [MeasurableSpace.comap_comp]
    rfl
  rw [e𝓠, preimage_univ]
  exact hL.compClauseK

/-- **The killed comparison clause of the dilated root stage on the glued space**: `compClauseK_img` passed through
`CompClauseK.dilate` with a time factor `C` that is a Borel function of the start (PROVE-PROP59-PIECES' root marks
are dilated by `rootLam`, a function of the junction marks). -/
theorem compClauseK_img_dil (hsw : KilledArcSwallowStatement) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hxLs : StrictAnti xL) (hxRs : StrictMono xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s)
    {C : Start (nL + 1) (nR + 1) → ℝ≥0} (hCm : Measurable C) (hC0 : ∀ y, C y ≠ 0) :
    CompClauseK κ (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
      (MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => cfStop s p.2) inferInstance) univ
      (jwL cL6 κ ρL) (jwR cR6 κ ρR) (Fin.last nL) (Fin.last nR)
      (fun p => dilV (C (histStart xL xR s p.2)) (histStart xL xR s p.2))
      (fun t p => (√(C (histStart xL xR s p.2) : ℝ))⁻¹ * imgW s ζ W (glueGood (glueMeasure P k
        (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W) (C (histStart xL xR s p.2) * t) p)
      (fun i t p => (√(C (histStart xL xR s p.2) : ℝ))⁻¹ * imgVL xL s ζ W (glueGood (glueMeasure P k
        (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W) i (C (histStart xL xR s p.2) * t) p)
      (fun j t p => (√(C (histStart xL xR s p.2) : ℝ))⁻¹ * imgVR xR s ζ W (glueGood (glueMeasure P k
        (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W) j (C (histStart xL xR s p.2) * t) p)
      (fun p => (show ℝ≥0∞ from imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) s ζ W) p) / (C (histStart xL xR s p.2) : ℝ≥0∞)) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hK := isKilledWord_img hF hEg
  refine (compClauseK_img hsw hκ hκ4 hF h44 hxLs hxRs hC hcf hlaw k hk hs).dilate hCm hC0
    (Eventually.of_forall fun p _ => ⟨hK.contW p, fun i => (hK.pathL p i).1, fun j => (hK.pathR p j).1⟩)

end Clause

end InteractingSLE.Sec5.CrossCond.StagedRepLater
