/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeTwo

/-!
# R.6's certificates for two outer arms on outer pockets opening at the flow seed

PROVE-R6-SAFE. The seed-opening counterpart of `twoSeedNestCertInput_two`: the outer pocket `C` of `(R, L)` opens at
the flow seed (`rightLo = 0`, `R6Rel.TwoSeedNestCertInputInf`), and the intermediate mixed pocket `V` of `(R, M_L)`
containing the tip is bounded (`ae_certInf_two_pos`, geometry `R6GeomTwoInfRemaining`) or opens at the flow seed as
well (`ae_certInf_two_zero`, geometry `R6GeomTwoInfInfRemaining`); the two shapes are combined almost surely in
**`twoSeedNestCertInputInf_two`**.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open R6Fin WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketCoupling PocketStopField Lemma71C Lemma71I PocketTraversal PocketStop LocalSets
  PocketWordPerQ PocketSeedOpen PocketStopWallsFin PocketStopWalls

section Cert

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **Two outer arms, outer pocket opening at the flow seed, bounded intermediate pocket**: the certificate at every
sample whose tip lies in a bounded mixed pocket `V` of `(R, M_L)` (the half of `twoSeedNestCertInputInf_two` with
`0 < rightLo` for `V`). -/
theorem ae_certInf_two_pos (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : Sec4.Aux7Statement.{u} k) {c c' : ℝ}
    (hk4 : 4 < k) (hL : -2 < rL) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hdL : k / 2 - 4 < rL) (hdR : k / 2 - 4 < rR)
    (hsideV : R7OuterSideMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hgeoV : OuterGeomAeMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hgeom : R6GeomTwoInfRemaining.{u} k rL rR c c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {q₀ : ℚ} {G : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q₀))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q₀) = 0 →
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω))
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A)
    (hAG : A ⊆ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)}) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) (StripSys.rt q₀) (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L (StripSys.rt q₀)
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} ψ)
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) (q : ℚ) {MR ML : Ω → ℝ≥0 → ℂ}
    (hMR : IsFrontierVersion P βR MR) (hML : IsFrontierVersion P βL ML) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q)) (centredField h'' u₀') P g) :
    ∀ᵐ ω ∂P, ω ∈ A → (∃ sV : ℚ, ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q ∧
      0 < rightLo (R ω) (ML ω) (StripSys.rt sV)) →
    ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ pocketSetInf A R L (StripSys.rt q₀) η ψ n
        (StripSys.rt q) ω) ∧
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ pocketSetInf A R L (StripSys.rt q₀) η ψ n
        (StripSys.rt q) ω → g ω φ = ∫ z, v z * φ z) ∧
      R6Cert k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
        (fun i => geomLW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t) (fun _ => LP.twoSeedXL) i
          (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
        (fun j => geomRW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t) (fun _ => LP.twoSeedXR) j
          (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
        (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) (StripSys.rt q₀)) ψ ω) (n ω))
          (travAllInf R L (StripSys.rt q₀) η ψ) (StripSys.rt q) ω) u₀' v := by
  -- constants and the counterflow coupling
  have hk0 : 0 < k := lt_trans (by norm_num) hk4
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := id hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have hhC := isZeroBoundaryGFF_centredField hC hu₀'
  -- the walls of `C` and of `V`
  have hWR := isWallData_R hk4 hcfg hu₀ hV
  have hWL := isWallData_L hk4 hcfg hu₀ hV
  have hWM : IsWallData P (centredField h u₀) ML := by
    have hw := isWallData_innerLeft hk4 hcfg hu₀ hV hML
    rwa [show innerLeft k rR L ML = ML by simp only [innerLeft, hdR, ↓reduceIte]] at hw
  -- the outer pocket's local set and mean
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L] {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L] {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω) := fun ω hω =>
    hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω).1
  obtain ⟨hCm, hCloc, hCunb⟩ := isLocalSet_activeCompl_outerInf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWL hG0
    hcfgI' hA hAG hζA hψ hψm hV.η_meas hn (StripSys.rt q)
  -- the intermediate mixed pocket `V` of `(R, M_L)`
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hθL : π / 2 < R7.thetaL k rR := (R7.d_lt_rR_iff hk4).1 hdR
  have hχ := Sec4.chiC_pos hκ hκ4
  have hcV : 0 ≤ c + (R7.thetaL k rR - π / 2) * chiC (16 / k) := add_nonneg hc (mul_nonneg (by linarith) hχ.le)
  have hcfgV := OuterGeom.isR7OuterConfig_leftExt h55 hk4 hL hc hc' hθL hcfg
  have hVV := isR7Versions_leftExt hV hML
  have hd : (-2 : ℝ) < k / 2 - 4 := by linarith
  have hmaxV : k / 2 - 4 < max rL (k / 2 - 4) := lt_max_of_lt_left hdL
  have hgV := hgeoV P h W' ζ' αR βR βL βL ζαR ζβR ζβL ζβL hcfgV b' J' h' h'' 𝓕 VL VR B hD R ML η hVV
  have hRVm := measurable_right_wallsSigma (P := P) hV.R_cont hML.1
  have hLVm := measurable_left_wallsSigma (P := P) hV.R_cont hML.1
  -- `V`'s tests at every rational parameter
  have hFex : ∀ sV : ℚ, ∃ F : Set Ω, MeasurableSet[wallsSigma P R ML] F ∧
      (0 < sV → ∀ᵐ ω ∂P, ML ω (StripSys.rt sV) ∉ range (R ω) → ω ∈ F) ∧
      ∀ ω ∈ F, IsChangeConfigInc (R ω) (ML ω) (StripSys.rt sV) ∧ ζ' ω = ⊤ ∧
        (0 < rightLo (R ω) (ML ω) (StripSys.rt sV) →
          IsOuterCfg (R ω) (ML ω) (StripSys.rt sV) (fun t : ℝ => W' t.toNNReal ω) (η ω)) ∧
        (rightLo (R ω) (ML ω) (StripSys.rt sV) = 0 →
          IsOuterCfgInf (R ω) (ML ω) (StripSys.rt sV) (fun t : ℝ => W' t.toNNReal ω) (η ω)) := by
    intro sV
    by_cases hsV : 0 < sV
    · obtain ⟨F, hFm, hFae, hF⟩ := exists_outerCfgEvent h411 h51 haux7 hk4 hL hd hmaxV hcV hc' hcfgV hVV sV hsV
        (hgV sV hsV).1 (hgV sV hsV).2
      exact ⟨F, hFm, fun _ => hFae, hF⟩
    · exact ⟨∅, @MeasurableSet.empty _ (wallsSigma P R ML), fun h' => absurd h' hsV,
        fun ω hω => absurd hω (Set.notMem_empty ω)⟩
  choose F hFm hFae hF using hFex
  have hconfF : ∀ sV, ∀ ω ∈ F sV, IsChangeConfigInc (R ω) (ML ω) (StripSys.rt sV) := fun sV ω hω => (hF sV ω hω).1
  have hFp : ∀ sV, MeasurableSet[wallsSigma P R ML] {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} :=
    fun sV => (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R ML) hRVm hLVm (hFm sV) (hconfF sV)).1
  have hcfgF : ∀ sV, ∀ ω ∈ {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)},
      IsOuterCfg (R ω) (ML ω) (StripSys.rt sV) (fun t : ℝ => W' t.toNNReal ω) (η ω) :=
    fun sV ω hω => (hF sV ω hω.1).2.2.1 hω.2
  have hζF : ∀ sV, ∀ ω ∈ {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}, ζ' ω = ⊤ :=
    fun sV ω hω => (hF sV ω hω.1).2.1
  -- `V`'s Jordan charts
  have hψex : ∀ sV : ℚ, ∃ ψV : Ω → ℂ → ℂ,
      (∀ ω ∈ {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)},
        IsCfJordan (R ω) (ML ω) (StripSys.rt sV) (ψV ω)) ∧
      @IsPointMeasurable Ω (wallsSigma P R ML) R ML (StripSys.rt sV)
        {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} ψV := fun sV => by
    obtain ⟨ψV, h1, h2, -⟩ := exists_measurable_pocketMarks_pts (mΩ := wallsSigma P R ML) hRVm hLVm (hFp sV)
      (fun ω hω => hconfF sV ω hω.1) (fun ω hω => zero_notMem_closure_of_rightLo_pos (hconfF sV ω hω.1) hω.2)
      (fun ω hω => (hcfgF sV ω hω).oriented) 0
    exact ⟨ψV, h1, h2⟩
  choose ψV hψV hψVm using hψex
  -- `V`'s zero-phase two-seed words at every rational parameter
  have hsideEx : ∀ sV : ℚ, ∃ (nV : Ω → ℤ) (aV : ℝ), Measurable[wallsSigma P R ML] nV ∧ ∀ q'' : ℝ≥0,
      PocketStopSideLimit k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => k / 2 - 4) P
        {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} (travAll R ML (StripSys.rt sV) η (ψV sV))
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
        (fun ω => shiftChart (pChart {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}
          (fun ω => cfPocket (R ω) (ML ω) (StripSys.rt sV)) (ψV sV) ω) (nV ω)) aV (centredField h'' u₀') u₀'
        (activeCompl {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}
          (travAll R ML (StripSys.rt sV) η (ψV sV))
          (fun ω => shiftChart (pChart {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}
            (fun ω => cfPocket (R ω) (ML ω) (StripSys.rt sV)) (ψV sV) ω) (nV ω)) q'') q'' := by
    intro sV
    by_cases hP : P {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} = 0
    · refine ⟨fun _ => 0, 0, measurable_const, fun q'' g' _ => ?_⟩
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hP] with ω hω hωA
      exact absurd hωA hω
    have hPp := pos_iff_ne_zero.2 hP
    obtain ⟨ω₀, hω₀⟩ := nonempty_of_measure_ne_zero hP
    have hsV : 0 < sV := Rat.cast_pos.1 (Real.toNNReal_pos.1 (hconfF sV ω₀ hω₀.1).pos)
    obtain ⟨hs', -⟩ := hsideV P h W' ζ' αR βR βL βL ζαR ζβR ζβL ζβL hcfgV b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R ML
      η hVV sV hsV (F sV) (hFm sV) (lt_of_lt_of_le hPp (measure_mono fun ω hω => hω.1)) (hconfF sV)
      (fun ω hω => (hF sV ω hω).2.1) (fun ω hω => (hF sV ω hω).2.2.1) (fun ω hω => (hF sV ω hω).2.2.2)
    obtain ⟨nV, aV, hnV, hS⟩ := hs' _ (hFp sV) subset_rfl hPp (ψV sV) (hψV sV) (hψVm sV)
    exact ⟨nV, aV, hnV, hS⟩
  choose nV aV hnV hlimV using hsideEx
  -- `V`'s local sets and means at every rational relative time
  have hU := fun i : ℚ × ℚ => isLocalSet_activeCompl_outer hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR.cont hWM.cont
    hWR.zero hWM.zero hWR.meas hWM.meas hWR.det hWM.det hWR.loc hWM.loc (hFp i.1) (hcfgF i.1) (hFp i.1) subset_rfl
    (hζF i.1) (hψV i.1) (hψVm i.1) hV.η_meas (hnV i.1) (StripSys.rt i.2)
  choose gU hgU using fun i : ℚ × ℚ => IsLocalSet.exists_isLocalSetMean hhC (hU i).1 (hU i).2.1
  -- the germ comparisons of the two outer pockets
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP₁ := isStopPocket_outerInf (X := fullHist ![R, L, R, ML]) (wallsSigma_le hV.R_meas hV.L_meas)
    (wallsSigma_le_four_left hX R L _ _) hWad hRm' hLm' hG0 hcfgI' hA hAG hζA hψ hψm hV.η_meas hn (StripSys.rt q)
  have hgerm := fun i : ℚ × ℚ => ae_r6Germ_four hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWL hWR hWM hP₁
    (isStopPocket_outer (X := fullHist ![R, L, R, ML]) (wallsSigma_le hWR.meas hWM.meas)
      (wallsSigma_le_four_right hX R L _ _) hWad hRVm hLVm (hFp i.1) (hcfgF i.1) (hFp i.1) subset_rfl (hζF i.1)
      (hψV i.1) (hψVm i.1) hV.η_meas (hnV i.1) (StripSys.rt i.2))
    hCm hCloc hCunb (hU i).1 (hU i).2.1 (hU i).2.2 hg (hgU i)
  -- the pathwise geometry
  have hgeo := fun sV : ℚ => hgeom hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    (StripSys.rt q₀) A {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} ψ (ψV sV) n (nV sV) sV q
    (fun ω hω => ⟨hcfgI' ω (hAG hω), hψ ω hω⟩) (fun ω hω => ⟨hcfgF sV ω hω, hψV sV ω hω⟩)
  -- almost every sample of the nested event is in a test of some intermediate pocket containing the tip
  have hFae' : ∀ᵐ ω ∂P, ∀ sV : ℚ, 0 < sV → ML ω (StripSys.rt sV) ∉ range (R ω) → ω ∈ F sV := by
    rw [ae_all_iff]
    intro sV
    by_cases hsV : 0 < sV
    · filter_upwards [hFae sV hsV] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hsV
  have hin : ∀ᵐ ω ∂P, (∃ sV : ℚ, ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q ∧
        0 < rightLo (R ω) (ML ω) (StripSys.rt sV)) →
      ∃ sV : ℚ, ω ∈ {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} ∧
        ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q := by
    filter_upwards [hFae'] with ω hFω hex
    obtain ⟨sV, hN, hp⟩ := hex
    have hcV := hN.2.2.1
    exact ⟨sV, ⟨hFω sV (Rat.cast_pos.1 (Real.toNNReal_pos.1 hcV.pos)) hcV.off, hp⟩, hN⟩
  -- the family of candidates `(s_V, q')`
  have key := ae_exists_r6Cert_of_family (κ := k) (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
    (σL := fun _ : Fin 1 => rL) (σR := fun _ : Fin 1 => k / 2 - 4) (ι := ℚ × ℚ) (u := u₀')
    (E := {ω | ω ∈ A ∧ ∃ sV : ℚ, ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q ∧
      0 < rightLo (R ω) (ML ω) (StripSys.rt sV)})
    (EC := pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q))
    (outer := relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) (StripSys.rt q₀)) ψ ω) (n ω))
      (travAllInf R L (StripSys.rt q₀) η ψ) (StripSys.rt q)) (g := g)
    (vL := fun ω i => geomLW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXL) i (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
    (vR := fun ω j => geomRW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXR) j (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
    (EU := fun i => pocketSet {ω | ω ∈ F i.1 ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt i.1)} R ML
      (StripSys.rt i.1) η (ψV i.1) (nV i.1) (StripSys.rt i.2))
    (inner := fun i => relChart (fun ω => shiftChart (pChart
      {ω | ω ∈ F i.1 ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt i.1)}
      (fun ω => cfPocket (R ω) (ML ω) (StripSys.rt i.1)) (ψV i.1) ω) (nV i.1 ω))
      (travAll R ML (StripSys.rt i.1) η (ψV i.1)) (StripSys.rt i.2)) (gU := gU)
    (wL := fun i ω j => geomLW (fun t ω => segDriver (travAll R ML (StripSys.rt i.1) η (ψV i.1) ω) t)
      (fun _ => LP.twoSeedXL) j (StripSys.rt i.2) ω -
      segDriver (travAll R ML (StripSys.rt i.1) η (ψV i.1) ω) (StripSys.rt i.2))
    (wR := fun i ω j => geomRW (fun t ω => segDriver (travAll R ML (StripSys.rt i.1) η (ψV i.1) ω) t)
      (fun _ => LP.twoSeedXR) j (StripSys.rt i.2) ω -
      segDriver (travAll R ML (StripSys.rt i.1) η (ψV i.1) ω) (StripSys.rt i.2))
    (aI := fun i => aV i.1)
    (Live := fun i => {ω | ω ∈ {ω | ω ∈ F i.1 ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt i.1)} ∧
      ((StripSys.rt i.2 : ℝ≥0) : ℝ≥0∞) < capLife (travAll R ML (StripSys.rt i.1) η (ψV i.1) ω)})
    hg.2.1 (fun i => (hgU i).2.1)
    (fun i => (hlimV i.1 (StripSys.rt i.2) (gU i) (hgU i)).mono fun ω hω hL => hω hL.1 hL.2)
    (fun i => hgerm i) (by
      filter_upwards [hin, ae_all_iff.2 hgeo] with ω h1 h2 hωE
      obtain ⟨sV, hFV, hN'⟩ := h1 hωE.2
      obtain ⟨q', hq', hgq'⟩ := h2 sV hωE.1 hFV hN'
      exact ⟨(sV, q'), ⟨hFV, hq'⟩, hgq'⟩)
  filter_upwards [key] with ω hω hωA hex
  exact hω ⟨hωA, hex⟩

/-- **Two outer arms, outer and intermediate pockets opening at the flow seed**: the certificate at every sample whose
tip lies in a mixed pocket `V` of `(R, M_L)` opening at the flow seed (the half of `twoSeedNestCertInputInf_two` with
`rightLo = 0` for `V`). -/
theorem ae_certInf_two_zero (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : Sec4.Aux7Statement.{u} k) {c c' : ℝ}
    (hk4 : 4 < k) (hL : -2 < rL) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hdL : k / 2 - 4 < rL) (hdR : k / 2 - 4 < rR)
    (hsideV : R7OuterSideMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hgeoV : OuterGeomAeMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hgeom : R6GeomTwoInfInfRemaining.{u} k rL rR c c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {q₀ : ℚ} {G : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q₀))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q₀) = 0 →
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω))
    {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A)
    (hAG : A ⊆ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)}) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) (StripSys.rt q₀) (ψ ω))
    (hψm : @IsPointMeasurableInf Ω (wallsSigma P R L) R L (StripSys.rt q₀)
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} ψ)
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) (q : ℚ) {MR ML : Ω → ℝ≥0 → ℂ}
    (hMR : IsFrontierVersion P βR MR) (hML : IsFrontierVersion P βL ML) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q)) (centredField h'' u₀') P g) :
    ∀ᵐ ω ∂P, ω ∈ A → (∃ sV : ℚ, ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q ∧
      ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)) →
    ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ pocketSetInf A R L (StripSys.rt q₀) η ψ n
        (StripSys.rt q) ω) ∧
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ pocketSetInf A R L (StripSys.rt q₀) η ψ n
        (StripSys.rt q) ω → g ω φ = ∫ z, v z * φ z) ∧
      R6Cert k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
        (fun i => geomLW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t) (fun _ => LP.twoSeedXL) i
          (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
        (fun j => geomRW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t) (fun _ => LP.twoSeedXR) j
          (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
        (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) (StripSys.rt q₀)) ψ ω) (n ω))
          (travAllInf R L (StripSys.rt q₀) η ψ) (StripSys.rt q) ω) u₀' v := by
  -- constants and the counterflow coupling
  have hk0 : 0 < k := lt_trans (by norm_num) hk4
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := id hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have hhC := isZeroBoundaryGFF_centredField hC hu₀'
  -- the walls of `C` and of `V`
  have hWR := isWallData_R hk4 hcfg hu₀ hV
  have hWL := isWallData_L hk4 hcfg hu₀ hV
  have hWM : IsWallData P (centredField h u₀) ML := by
    have hw := isWallData_innerLeft hk4 hcfg hu₀ hV hML
    rwa [show innerLeft k rR L ML = ML by simp only [innerLeft, hdR, ↓reduceIte]] at hw
  -- the outer pocket's local set and mean
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L] {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L] {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω) := fun ω hω =>
    hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω).1
  obtain ⟨hCm, hCloc, hCunb⟩ := isLocalSet_activeCompl_outerInf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWL hG0
    hcfgI' hA hAG hζA hψ hψm hV.η_meas hn (StripSys.rt q)
  -- the intermediate mixed pocket `V` of `(R, M_L)`
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hθL : π / 2 < R7.thetaL k rR := (R7.d_lt_rR_iff hk4).1 hdR
  have hχ := Sec4.chiC_pos hκ hκ4
  have hcV : 0 ≤ c + (R7.thetaL k rR - π / 2) * chiC (16 / k) := add_nonneg hc (mul_nonneg (by linarith) hχ.le)
  have hcfgV := OuterGeom.isR7OuterConfig_leftExt h55 hk4 hL hc hc' hθL hcfg
  have hVV := isR7Versions_leftExt hV hML
  have hd : (-2 : ℝ) < k / 2 - 4 := by linarith
  have hmaxV : k / 2 - 4 < max rL (k / 2 - 4) := lt_max_of_lt_left hdL
  have hgV := hgeoV P h W' ζ' αR βR βL βL ζαR ζβR ζβL ζβL hcfgV b' J' h' h'' 𝓕 VL VR B hD R ML η hVV
  have hRVm := measurable_right_wallsSigma (P := P) hV.R_cont hML.1
  have hLVm := measurable_left_wallsSigma (P := P) hV.R_cont hML.1
  -- `V`'s tests at every rational parameter
  have hFex : ∀ sV : ℚ, ∃ F : Set Ω, MeasurableSet[wallsSigma P R ML] F ∧
      (0 < sV → ∀ᵐ ω ∂P, ML ω (StripSys.rt sV) ∉ range (R ω) → ω ∈ F) ∧
      ∀ ω ∈ F, IsChangeConfigInc (R ω) (ML ω) (StripSys.rt sV) ∧ ζ' ω = ⊤ ∧
        (0 < rightLo (R ω) (ML ω) (StripSys.rt sV) →
          IsOuterCfg (R ω) (ML ω) (StripSys.rt sV) (fun t : ℝ => W' t.toNNReal ω) (η ω)) ∧
        (rightLo (R ω) (ML ω) (StripSys.rt sV) = 0 →
          IsOuterCfgInf (R ω) (ML ω) (StripSys.rt sV) (fun t : ℝ => W' t.toNNReal ω) (η ω)) := by
    intro sV
    by_cases hsV : 0 < sV
    · obtain ⟨F, hFm, hFae, hF⟩ := exists_outerCfgEvent h411 h51 haux7 hk4 hL hd hmaxV hcV hc' hcfgV hVV sV hsV
        (hgV sV hsV).1 (hgV sV hsV).2
      exact ⟨F, hFm, fun _ => hFae, hF⟩
    · exact ⟨∅, @MeasurableSet.empty _ (wallsSigma P R ML), fun h' => absurd h' hsV,
        fun ω hω => absurd hω (Set.notMem_empty ω)⟩
  choose F hFm hFae hF using hFex
  have hconfF : ∀ sV, ∀ ω ∈ F sV, IsChangeConfigInc (R ω) (ML ω) (StripSys.rt sV) := fun sV ω hω => (hF sV ω hω).1
  have hFp' : ∀ sV, MeasurableSet[wallsSigma P R ML] {ω | ω ∈ F sV ∧ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} :=
    fun sV => (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R ML) hRVm hLVm (hFm sV) (hconfF sV)).1
  have hFp : ∀ sV, MeasurableSet[wallsSigma P R ML] {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} := by
    intro sV
    convert (hFm sV).diff (hFp' sV) using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hseed : ∀ sV, ∀ ω ∈ {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)},
      rightLo (R ω) (ML ω) (StripSys.rt sV) = 0 := fun sV ω hω =>
    le_antisymm (not_lt.1 hω.2) ((hconfF sV ω hω.1).changeCorner_props.1.1)
  have hcfgF : ∀ sV, ∀ ω ∈ {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)},
      IsOuterCfgInf (R ω) (ML ω) (StripSys.rt sV) (fun t : ℝ => W' t.toNNReal ω) (η ω) :=
    fun sV ω hω => (hF sV ω hω.1).2.2.2 (hseed sV ω hω)
  have hζF : ∀ sV, ∀ ω ∈ {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}, ζ' ω = ⊤ :=
    fun sV ω hω => (hF sV ω hω.1).2.1
  -- `V`'s Jordan charts
  have hψex : ∀ sV : ℚ, ∃ ψV : Ω → ℂ → ℂ,
      (∀ ω ∈ {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)},
        IsCfJordanInf (R ω) (ML ω) (StripSys.rt sV) (ψV ω)) ∧
      @IsPointMeasurableInf Ω (wallsSigma P R ML) R ML (StripSys.rt sV)
        {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} ψV := fun sV => by
    obtain ⟨ψV, h1, h2, -⟩ := exists_measurable_pocketMarksInf_pts (mΩ := wallsSigma P R ML) hRVm hLVm (hFp sV)
      (fun ω hω => hconfF sV ω hω.1) (hseed sV) (fun ω hω => (hcfgF sV ω hω).oriented) 0
    exact ⟨ψV, h1, h2⟩
  choose ψV hψV hψVm using hψex
  -- `V`'s zero-phase two-seed words at every rational parameter
  have hsideEx : ∀ sV : ℚ, ∃ (nV : Ω → ℤ) (aV : ℝ), Measurable[wallsSigma P R ML] nV ∧ ∀ q'' : ℝ≥0,
      PocketStopSideLimit k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => k / 2 - 4) P
        {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} (travAllInf R ML (StripSys.rt sV) η (ψV sV))
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
        (fun ω => shiftChart (pChart {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}
          (fun ω => cfPocket (R ω) (ML ω) (StripSys.rt sV)) (ψV sV) ω) (nV ω)) aV (centredField h'' u₀') u₀'
        (activeCompl {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}
          (travAllInf R ML (StripSys.rt sV) η (ψV sV))
          (fun ω => shiftChart (pChart {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)}
            (fun ω => cfPocket (R ω) (ML ω) (StripSys.rt sV)) (ψV sV) ω) (nV ω)) q'') q'' := by
    intro sV
    by_cases hP : P {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} = 0
    · refine ⟨fun _ => 0, 0, measurable_const, fun q'' g' _ => ?_⟩
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hP] with ω hω hωA
      exact absurd hωA hω
    have hPp := pos_iff_ne_zero.2 hP
    obtain ⟨ω₀, hω₀⟩ := nonempty_of_measure_ne_zero hP
    have hsV : 0 < sV := Rat.cast_pos.1 (Real.toNNReal_pos.1 (hconfF sV ω₀ hω₀.1).pos)
    obtain ⟨-, hs'⟩ := hsideV P h W' ζ' αR βR βL βL ζαR ζβR ζβL ζβL hcfgV b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R ML
      η hVV sV hsV (F sV) (hFm sV) (lt_of_lt_of_le hPp (measure_mono fun ω hω => hω.1)) (hconfF sV)
      (fun ω hω => (hF sV ω hω).2.1) (fun ω hω => (hF sV ω hω).2.2.1) (fun ω hω => (hF sV ω hω).2.2.2)
    obtain ⟨nV, aV, hnV, hS⟩ := hs' _ (hFp sV) subset_rfl hPp (ψV sV) (hψV sV) (hψVm sV)
    exact ⟨nV, aV, hnV, hS⟩
  choose nV aV hnV hlimV using hsideEx
  -- `V`'s local sets and means at every rational relative time
  have hU := fun i : ℚ × ℚ => isLocalSet_activeCompl_outerInf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWM
    (hFp i.1) (hcfgF i.1) (hFp i.1) subset_rfl (hζF i.1) (hψV i.1) (hψVm i.1) hV.η_meas (hnV i.1) (StripSys.rt i.2)
  choose gU hgU using fun i : ℚ × ℚ => IsLocalSet.exists_isLocalSetMean hhC (hU i).1 (hU i).2.1
  -- the germ comparisons of the two outer pockets
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP₁ := isStopPocket_outerInf (X := fullHist ![R, L, R, ML]) (wallsSigma_le hV.R_meas hV.L_meas)
    (wallsSigma_le_four_left hX R L _ _) hWad hRm' hLm' hG0 hcfgI' hA hAG hζA hψ hψm hV.η_meas hn (StripSys.rt q)
  have hgerm := fun i : ℚ × ℚ => ae_r6Germ_four hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWL hWR hWM hP₁
    (isStopPocket_outerInf (X := fullHist ![R, L, R, ML]) (wallsSigma_le hWR.meas hWM.meas)
      (wallsSigma_le_four_right hX R L _ _) hWad hRVm hLVm (hFp i.1) (hcfgF i.1) (hFp i.1) subset_rfl (hζF i.1)
      (hψV i.1) (hψVm i.1) hV.η_meas (hnV i.1) (StripSys.rt i.2))
    hCm hCloc hCunb (hU i).1 (hU i).2.1 (hU i).2.2 hg (hgU i)
  -- the pathwise geometry
  have hgeo := fun sV : ℚ => hgeom hdL hdR P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML
    (StripSys.rt q₀) A {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} ψ (ψV sV) n (nV sV) sV q
    (fun ω hω => ⟨hcfgI' ω (hAG hω), hψ ω hω⟩) (fun ω hω => ⟨hcfgF sV ω hω, hψV sV ω hω⟩)
  -- almost every sample of the nested event is in a test of some intermediate pocket containing the tip
  have hFae' : ∀ᵐ ω ∂P, ∀ sV : ℚ, 0 < sV → ML ω (StripSys.rt sV) ∉ range (R ω) → ω ∈ F sV := by
    rw [ae_all_iff]
    intro sV
    by_cases hsV : 0 < sV
    · filter_upwards [hFae sV hsV] with ω hω _ using hω
    · exact ae_of_all _ fun ω h' => absurd h' hsV
  have hin : ∀ᵐ ω ∂P, (∃ sV : ℚ, ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q ∧
        ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)) →
      ∃ sV : ℚ, ω ∈ {ω | ω ∈ F sV ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)} ∧
        ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q := by
    filter_upwards [hFae'] with ω hFω hex
    obtain ⟨sV, hN, hp⟩ := hex
    have hcV := hN.2.2.1
    exact ⟨sV, ⟨hFω sV (Rat.cast_pos.1 (Real.toNNReal_pos.1 hcV.pos)) hcV.off, hp⟩, hN⟩
  -- the family of candidates `(s_V, q')`
  have key := ae_exists_r6Cert_of_family (κ := k) (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
    (σL := fun _ : Fin 1 => rL) (σR := fun _ : Fin 1 => k / 2 - 4) (ι := ℚ × ℚ) (u := u₀')
    (E := {ω | ω ∈ A ∧ ∃ sV : ℚ, ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q ∧
      ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)})
    (EC := pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q))
    (outer := relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) (StripSys.rt q₀)) ψ ω) (n ω))
      (travAllInf R L (StripSys.rt q₀) η ψ) (StripSys.rt q)) (g := g)
    (vL := fun ω i => geomLW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXL) i (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
    (vR := fun ω j => geomRW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXR) j (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
    (EU := fun i => pocketSetInf {ω | ω ∈ F i.1 ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt i.1)} R ML
      (StripSys.rt i.1) η (ψV i.1) (nV i.1) (StripSys.rt i.2))
    (inner := fun i => relChart (fun ω => shiftChart (pChart
      {ω | ω ∈ F i.1 ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt i.1)}
      (fun ω => cfPocket (R ω) (ML ω) (StripSys.rt i.1)) (ψV i.1) ω) (nV i.1 ω))
      (travAllInf R ML (StripSys.rt i.1) η (ψV i.1)) (StripSys.rt i.2)) (gU := gU)
    (wL := fun i ω j => geomLW (fun t ω => segDriver (travAllInf R ML (StripSys.rt i.1) η (ψV i.1) ω) t)
      (fun _ => LP.twoSeedXL) j (StripSys.rt i.2) ω -
      segDriver (travAllInf R ML (StripSys.rt i.1) η (ψV i.1) ω) (StripSys.rt i.2))
    (wR := fun i ω j => geomRW (fun t ω => segDriver (travAllInf R ML (StripSys.rt i.1) η (ψV i.1) ω) t)
      (fun _ => LP.twoSeedXR) j (StripSys.rt i.2) ω -
      segDriver (travAllInf R ML (StripSys.rt i.1) η (ψV i.1) ω) (StripSys.rt i.2))
    (aI := fun i => aV i.1)
    (Live := fun i => {ω | ω ∈ {ω | ω ∈ F i.1 ∧ ¬ 0 < rightLo (R ω) (ML ω) (StripSys.rt i.1)} ∧
      ((StripSys.rt i.2 : ℝ≥0) : ℝ≥0∞) < capLife (travAllInf R ML (StripSys.rt i.1) η (ψV i.1) ω)})
    hg.2.1 (fun i => (hgU i).2.1)
    (fun i => (hlimV i.1 (StripSys.rt i.2) (gU i) (hgU i)).mono fun ω hω hL => hω hL.1 hL.2)
    (fun i => hgerm i) (by
      filter_upwards [hin, ae_all_iff.2 hgeo] with ω h1 h2 hωE
      obtain ⟨sV, hFV, hN'⟩ := h1 hωE.2
      obtain ⟨q', hq', hgq'⟩ := h2 sV hωE.1 hFV hN'
      exact ⟨(sV, q'), ⟨hFV, hq'⟩, hgq'⟩)
  filter_upwards [key] with ω hω hωA hex
  exact hω ⟨hωA, hex⟩

/-- **R.6's certificates for two outer arms on outer pockets opening at the flow seed** (supplement p. 476): the
conclusion of `R6Rel.R6NestCertRemaining` for the seed-opening outer pocket shape on one R.7 configuration with two
outer arms; the intermediate pocket containing the tip is bounded (`ae_certInf_two_pos`) or opens at the flow seed
(`ae_certInf_two_zero`). -/
theorem twoSeedNestCertInputInf_two (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : Sec4.Aux7Statement.{u} k) {c c' : ℝ}
    (hk4 : 4 < k) (hL : -2 < rL) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hdL : k / 2 - 4 < rL) (hdR : k / 2 - 4 < rR)
    (hsideV : R7OuterSideMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hgeoV : OuterGeomAeMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hgeom : R6GeomTwoInfRemaining.{u} k rL rR c c') (hgeom' : R6GeomTwoInfInfRemaining.{u} k rL rR c c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B) {u₀' : ℂ → ℝ}
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {q₀ : ℚ} {G : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q₀))
    (hζG : ∀ ω ∈ G, ζ' ω = ⊤)
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q₀) = 0 →
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    TwoSeedNestCertInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q₀) η
      {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} (centredField h'' u₀') u₀' βR βL
      (innerRight k rL R βR) (innerLeft k rR L βL) := by
  have eR : innerRight k rL R βR = βR := by simp only [innerRight, hdL, ↓reduceIte]
  have eL : innerLeft k rR L βL = βL := by simp only [innerLeft, hdR, ↓reduceIte]
  rw [eR, eL]
  intro A hA hAG hPA ψ hψ hψm n hn q s
  -- constants and the counterflow coupling
  have hk0 : 0 < k := lt_trans (by norm_num) hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := id hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have hhC := isZeroBoundaryGFF_centredField hC hu₀'
  have hWR := isWallData_R hk4 hcfg hu₀ hV
  have hWL := isWallData_L hk4 hcfg hu₀ hV
  obtain ⟨⟨MR, hMR⟩, ⟨ML, hML⟩⟩ := exists_isFrontierVersion hcfg
  -- the outer pocket's local set and mean
  have hRm' := measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hLm' := measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont
  have hGp : MeasurableSet[wallsSigma P R L] {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} :=
    (measurableSet_rightLo_pos_and (mΩ := wallsSigma P R L) hRm' hLm' hGm hconf).1
  have hG0 : MeasurableSet[wallsSigma P R L] {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} := by
    convert hGm.diff hGp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hcfgI' : ∀ ω ∈ {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)},
      IsOuterCfgInf (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω) := fun ω hω =>
    hcfgI ω hω.1 (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1))
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω).1
  obtain ⟨hCm, hCloc, -⟩ := isLocalSet_activeCompl_outerInf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWL hG0
    hcfgI' hA hAG hζA hψ hψm hV.η_meas hn (StripSys.rt q)
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hhC hCm hCloc
  refine ⟨g, hg, ?_⟩
  -- almost every sample of the nested event has its tip in an intermediate pocket
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hθL : π / 2 < R7.thetaL k rR := (R7.d_lt_rR_iff hk4).1 hdR
  have hRβL : ∀ᵐ ω ∂P, range (βL ω) ⊆ closedLeftSide (αR ω) :=
    ae_order_r7 h55 hk4 hc hc' (R7.thetaR_lt_pi_div_two hk4 hL) (thetaR_mem_r7 rR hk4 hL)
      (pi_div_two_mem_r7 k rL rR) hcfg.gff hcfg.flow_αR hcfg.flow_βL
  have hex : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ βR βL βR βL s q →
      ∃ sV : ℚ, ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML R ML sV q := by
    filter_upwards [hcfg.regular, hcfg.order, hV.R_ae, hV.L_ae, hRβL, hMR.2.2.2, hML.2.2.2] with
      ω hreg hord hRe hLe h1 hMRe hMLe hωA hωN
    obtain ⟨hq, hlive, hcU, hsubU, u, hu0, hcap, htipU, hfront⟩ := hωN
    have hincC := hconf ω (hAG hωA).1
    have hRL : range (L ω) ⊆ closedLeftSide (R ω) := by rw [hRe, hLe]; exact hord.2.1
    have h1' : range (βL ω) ⊆ closedLeftSide (R ω) := by rw [hRe]; exact h1
    have hLout : ∀ w ∈ range (L ω), w ∈ H → w ∈ leftSideOf (range (βL ω)) ∪ range (βL ω) :=
      fun w hw _ => (hord.2.2.2.1 hθL).1 (hLe ▸ hw)
    obtain ⟨sV, -, hcV', hmemV, hsubV⟩ := exists_rat_leftPocket hincC hRL
      (R7Outer.IsSeedProper.isSimpleProper hreg.2.2.1) h1' hLout hcU hsubU htipU
    rw [← hMLe] at hcV' hmemV hsubV
    refine ⟨sV, hq, hlive, hcV', hsubV, u, hu0, hcap, hmemV, ?_⟩
    rw [hMRe, hMLe]
    exact hfront
  filter_upwards [hex, ae_certInf_two_pos h411 h51 haux7 hk4 hL hc hc' hdL hdR hsideV hgeoV hgeom hcfg hD hu₀' hV
      hGm hconf hζG hcfgI hA hAG hψ hψm hn q hMR hML hg,
    ae_certInf_two_zero h411 h51 haux7 hk4 hL hc hc' hdL hdR hsideV hgeoV hgeom' hcfg hD hu₀' hV
      hGm hconf hζG hcfgI hA hAG hψ hψm hn q hMR hML hg] with ω h0 h1 h2 hωA hωN
  obtain ⟨sV, hN⟩ := h0 hωA hωN
  by_cases hp : 0 < rightLo (R ω) (ML ω) (StripSys.rt sV)
  · exact h1 hωA ⟨sV, hN, hp⟩
  · exact h2 hωA ⟨sV, hN, hp⟩

end Cert

end InteractingSLE.Sec7.R6Safe
