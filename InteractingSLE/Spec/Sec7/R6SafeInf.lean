/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeBounded
import InteractingSLE.Spec.Sec7.R6FinInf

/-!
# R.6's certificates on outer pockets opening at the flow seed (mixed case), R48-safe

PROVE-R6-SAFE. `twoSeedNestCertInputInf_of_geom_safe` (and its two halves `ae_certInf_pos_safe`,
`ae_certInf_zero_safe`) is `R6Fin.twoSeedNestCertInputInf_of_geom` (PROVE-R6-CERT2) without the input
`hstrip : R7StripOnConfig`, exactly as `twoSeedNestCertInput_of_geom_safe`: the constant-angle strip system
`StripSafe.exists_isConstStripSystem` replaces the full strip system. The proofs are otherwise verbatim.

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

open R6Fin
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketCoord PocketJordan PocketMarks PocketWordAssembly
  PocketCoupling PocketStopField Lemma71C Lemma71I PocketTraversal PocketStop LocalSets PocketWordPerQ PocketSeedOpen
  PocketStopWallsFin PocketStopWalls

section Cert

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- The bounded nested pockets of `twoSeedNestCertInputInf_of_geom_safe` (`R6Fin.ae_certInf_pos`, R48-safe). -/
theorem ae_certInf_pos_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {c c' : ℝ}
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hgeom : R6GeomMixedInfRemaining.{u} k rL rR c c')
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR))
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
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) (q s : ℚ) (hs : 0 < s) {MR ML : Ω → ℝ≥0 → ℂ}
    (hMR : IsFrontierVersion P βR MR) (hML : IsFrontierVersion P βL ML) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q)) (centredField h'' u₀') P g) :
    ∀ᵐ ω ∂P, ω ∈ A →
    ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR) (innerLeft k rR L βL) s q →
    0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) →
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
  have hc : 0 ≤ c := (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le).trans hcπ
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := id hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have hhC := isZeroBoundaryGFF_centredField hC hu₀'
  -- the walls
  have hWR := isWallData_R hk4 hcfg hu₀ hV
  have hWL := isWallData_L hk4 hcfg hu₀ hV
  have hWR' := isWallData_innerRight hk4 hcfg hu₀ hV hMR
  have hWL' := isWallData_innerLeft hk4 hcfg hu₀ hV hML
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
  -- the inner configuration and its tests at `rt s`
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hcfgI := IsR7OuterConfig.inner h55 hk4 hL hR hc hc' hcfg
  have hVI := isR7Versions_inner (k := k) (rL := rL) (rR := rR) hV hMR hML
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights_ge (rL := rL) (rR := rR) hk4 hcπ hc'
  obtain ⟨Es, hS, hSreg⟩ :=
    StripSafe.exists_isConstStripSystem h44 hκ hκ4 hb hcumL hcumR hgff hcfg.counterflow hζ
  have e : prop74Data (r7A k (innerLeft k rR rR (k / 2 - 4)) +
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4)))))
      (r7B k (innerRight k rL rL (k / 2 - 4)) + (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4))))) =
      prop74Data (r7A k rR + c) (r7B k rL + c') := by
    congr 1 <;> ring
  obtain ⟨F, hFm, hFae, hF⟩ := exists_cfgEvent_extremal_const h411 h51 h47 h47T haux7 h44 hk4
    (neg_two_lt_innerRight_weight hk4 hL) (neg_two_lt_innerLeft_weight hk4 hR) (max_inner_weights_eq hmix)
    (innerMarginL_nonneg hk4 hc) (innerMarginR_nonneg hk4 hc') hcfgI (Es := Es) (by rw [e]; exact hS)
    hSreg (by rw [e]; exact hcumL) (by rw [e]; exact hcumR) hVI s hs
  have hR''m := measurable_right_wallsSigma (P := P) hWR'.cont hWL'.cont
  have hL''m := measurable_left_wallsSigma (P := P) hWR'.cont hWL'.cont
  have hconfF : ∀ ω ∈ F, IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hF ω hω).1
  have hFp := (measurableSet_rightLo_pos_and (mΩ := wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML))
    hR''m hL''m hFm hconfF).1
  have hF0 : MeasurableSet[wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)]
      {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} := by
    convert hFm.diff hFp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP₁ := isStopPocket_outerInf (X := fullHist ![R, L, innerRight k rL R MR, innerLeft k rR L ML])
    (wallsSigma_le hV.R_meas hV.L_meas) (wallsSigma_le_four_left hX R L _ _) hWad hRm' hLm' hG0 hcfgI' hA hAG hζA hψ
    hψm hV.η_meas hn (StripSys.rt q)
  -- almost every sample of the nested event is in the inner event `F`
  have hin : ∀ᵐ ω ∂P, ω ∈ A →
      ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR) (innerLeft k rR L βL) s q →
      ω ∈ F ∧ ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q := by
    filter_upwards [hFae, hMR.2.2.2, hML.2.2.2] with ω hωF hωR hωL hωA hωN
    have hωN' := (mem_nestRelEventInf_congr hωR hωL).1 hωN
    exact ⟨hωF hωN'.2.2.1.off, hωN'⟩
  have hPF0 : 0 < P F ∨ P F = 0 := (eq_zero_or_pos (P F)).symm
  rcases hPF0 with hPF0 | hPF0
  swap
  · filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hPF0] with ω h1 h2 hωA hωN
    exact absurd (h1 hωA hωN).1 h2
  obtain ⟨hside, hsideI⟩ := inner_side_of_word h55 hk4 hL hR hc hc' hword hcfg hD hu₀' hV hMR hML s hs F hFm hPF0
    hconfF (fun ω hω => (hF ω hω).2.1) (fun ω hω => (hF ω hω).2.2.1) (fun ω hω => (hF ω hω).2.2.2)
  by_cases hPF : P {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} = 0
  · filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hPF] with ω h1 h2 hωA hωN hp
    exact absurd ⟨(h1 hωA hωN).1, hp⟩ h2
  have hPFp := pos_iff_ne_zero.2 hPF
  have hcfgF : ∀ ω ∈ {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)},
      IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
        (fun t : ℝ => W' t.toNNReal ω) (η ω) := fun ω hω => (hF ω hω.1).2.2.1 hω.2
  have hζF : ∀ ω ∈ {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)},
      ζ' ω = ⊤ := fun ω hω => (hF ω hω.1).2.1
  obtain ⟨ψ', hψ', hψ'm, -⟩ := exists_measurable_pocketMarks_pts
    (mΩ := wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)) hR''m hL''m hFp
    (fun ω hω => hconfF ω hω.1) (fun ω hω => zero_notMem_closure_of_rightLo_pos (hconfF ω hω.1) hω.2)
    (fun ω hω => (hcfgF ω hω).oriented) 0
  obtain ⟨n', a', hn', hlimq⟩ := hside _ hFp subset_rfl hPFp ψ' hψ' hψ'm
  have hU := fun q' : ℚ => isLocalSet_activeCompl_cf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR'.cont hWL'.cont
    hWR'.zero hWL'.zero hWR'.meas hWL'.meas hWR'.det hWL'.det hWR'.loc hWL'.loc hFp hcfgF hFp subset_rfl hζF hψ'
    hψ'm hV.η_meas hn' (StripSys.rt q')
  choose gU hgU using fun q' : ℚ => IsLocalSet.exists_isLocalSetMean hhC (hU q').1 (hU q').2.1
  have hgerm := fun q' : ℚ => ae_r6Germ_four hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWL hWR' hWL' hP₁
    (isStopPocket_cf (X := fullHist ![R, L, innerRight k rL R MR, innerLeft k rR L ML])
      (wallsSigma_le hWR'.meas hWL'.meas) (wallsSigma_le_four_right hX R L _ _) hWad hR''m hL''m hFp hcfgF hFp
      subset_rfl hζF hψ' hψ'm hV.η_meas hn' (StripSys.rt q'))
    hCm hCloc hCunb (hU q').1 (hU q').2.1 (hU q').2.2 hg (hgU q')
  have hgeo := hgeom hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML (StripSys.rt q₀) A
    {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} ψ ψ' n n' s q
    (fun ω hω => ⟨hcfgI' ω (hAG hω), hψ ω hω⟩) (fun ω hω => ⟨hcfgF ω hω, hψ' ω hω⟩)
  have key := ae_exists_r6Cert_of_family (κ := k) (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
    (σL := fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4)) (σR := fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
    (ι := ℚ) (u := u₀')
    (E := {ω | ω ∈ A ∧ ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR)
      (innerLeft k rR L βL) s q ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)})
    (EC := pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q))
    (outer := relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) (StripSys.rt q₀)) ψ ω)
      (n ω)) (travAllInf R L (StripSys.rt q₀) η ψ) (StripSys.rt q)) (g := g)
    (vL := fun ω i => geomLW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXL) i (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω)
        (StripSys.rt q))
    (vR := fun ω j => geomRW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXR) j (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω)
        (StripSys.rt q))
    (EU := fun q' => pocketSet
      {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)}
      (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q'))
    (inner := fun q' => relChart (fun ω => shiftChart (pChart
      {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)}
      (fun ω => cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
      (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')) (gU := gU)
    (wL := fun q' ω i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
      (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
      segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) (StripSys.rt q'))
    (wR := fun q' ω j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
      (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
      segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) (StripSys.rt q'))
    (aI := fun _ => a')
    (Live := fun q' => {ω | ω ∈ {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω)
      (StripSys.rt s)} ∧ ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
        capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)})
    hg.2.1 (fun q' => (hgU q').2.1)
    (fun q' => (hlimq (StripSys.rt q') (gU q') (hgU q')).mono fun ω hω hL => hω hL.1 hL.2)
    (fun q' => hgerm q') (by
      filter_upwards [hin, hgeo] with ω h1 h2 hωE
      obtain ⟨hF', hN'⟩ := h1 hωE.1 hωE.2.1
      obtain ⟨q', hq', hgq'⟩ := h2 hωE.1 ⟨hF', hωE.2.2⟩ hN'
      exact ⟨q', ⟨⟨hF', hωE.2.2⟩, hq'⟩, hgq'⟩)
  filter_upwards [key] with ω hω hωA hωN hp
  exact hω ⟨hωA, hωN, hp⟩

/-- The seed-opening nested pockets of `twoSeedNestCertInputInf_of_geom_safe` (`R6Fin.ae_certInf_zero`,
R48-safe). -/
theorem ae_certInf_zero_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {c c' : ℝ}
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hgeom' : R6GeomMixedInfInfRemaining.{u} k rL rR c c')
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR))
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
    {n : Ω → ℤ} (hn : Measurable[wallsSigma P R L] n) (q s : ℚ) (hs : 0 < s) {MR ML : Ω → ℝ≥0 → ℂ}
    (hMR : IsFrontierVersion P βR MR) (hML : IsFrontierVersion P βL ML) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q)) (centredField h'' u₀') P g) :
    ∀ᵐ ω ∂P, ω ∈ A →
    ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR) (innerLeft k rR L βL) s q →
    ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) →
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
  have hc : 0 ≤ c := (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le).trans hcπ
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := id hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have hhC := isZeroBoundaryGFF_centredField hC hu₀'
  -- the walls
  have hWR := isWallData_R hk4 hcfg hu₀ hV
  have hWL := isWallData_L hk4 hcfg hu₀ hV
  have hWR' := isWallData_innerRight hk4 hcfg hu₀ hV hMR
  have hWL' := isWallData_innerLeft hk4 hcfg hu₀ hV hML
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
  -- the inner configuration and its tests at `rt s`
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hcfgI := IsR7OuterConfig.inner h55 hk4 hL hR hc hc' hcfg
  have hVI := isR7Versions_inner (k := k) (rL := rL) (rR := rR) hV hMR hML
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights_ge (rL := rL) (rR := rR) hk4 hcπ hc'
  obtain ⟨Es, hS, hSreg⟩ :=
    StripSafe.exists_isConstStripSystem h44 hκ hκ4 hb hcumL hcumR hgff hcfg.counterflow hζ
  have e : prop74Data (r7A k (innerLeft k rR rR (k / 2 - 4)) +
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4)))))
      (r7B k (innerRight k rL rL (k / 2 - 4)) + (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4))))) =
      prop74Data (r7A k rR + c) (r7B k rL + c') := by
    congr 1 <;> ring
  obtain ⟨F, hFm, hFae, hF⟩ := exists_cfgEvent_extremal_const h411 h51 h47 h47T haux7 h44 hk4
    (neg_two_lt_innerRight_weight hk4 hL) (neg_two_lt_innerLeft_weight hk4 hR) (max_inner_weights_eq hmix)
    (innerMarginL_nonneg hk4 hc) (innerMarginR_nonneg hk4 hc') hcfgI (Es := Es) (by rw [e]; exact hS)
    hSreg (by rw [e]; exact hcumL) (by rw [e]; exact hcumR) hVI s hs
  have hR''m := measurable_right_wallsSigma (P := P) hWR'.cont hWL'.cont
  have hL''m := measurable_left_wallsSigma (P := P) hWR'.cont hWL'.cont
  have hconfF : ∀ ω ∈ F, IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hF ω hω).1
  have hFp := (measurableSet_rightLo_pos_and (mΩ := wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML))
    hR''m hL''m hFm hconfF).1
  have hF0 : MeasurableSet[wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)]
      {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} := by
    convert hFm.diff hFp using 1
    ext ω
    simp only [mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have hP₁ := isStopPocket_outerInf (X := fullHist ![R, L, innerRight k rL R MR, innerLeft k rR L ML])
    (wallsSigma_le hV.R_meas hV.L_meas) (wallsSigma_le_four_left hX R L _ _) hWad hRm' hLm' hG0 hcfgI' hA hAG hζA hψ
    hψm hV.η_meas hn (StripSys.rt q)
  -- almost every sample of the nested event is in the inner event `F`
  have hin : ∀ᵐ ω ∂P, ω ∈ A →
      ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR) (innerLeft k rR L βL) s q →
      ω ∈ F ∧ ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q := by
    filter_upwards [hFae, hMR.2.2.2, hML.2.2.2] with ω hωF hωR hωL hωA hωN
    have hωN' := (mem_nestRelEventInf_congr hωR hωL).1 hωN
    exact ⟨hωF hωN'.2.2.1.off, hωN'⟩
  have hPF0 : 0 < P F ∨ P F = 0 := (eq_zero_or_pos (P F)).symm
  rcases hPF0 with hPF0 | hPF0
  swap
  · filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hPF0] with ω h1 h2 hωA hωN
    exact absurd (h1 hωA hωN).1 h2
  obtain ⟨hside, hsideI⟩ := inner_side_of_word h55 hk4 hL hR hc hc' hword hcfg hD hu₀' hV hMR hML s hs F hFm hPF0
    hconfF (fun ω hω => (hF ω hω).2.1) (fun ω hω => (hF ω hω).2.2.1) (fun ω hω => (hF ω hω).2.2.2)
  by_cases hPF : P {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} = 0
  · filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hPF] with ω h1 h2 hωA hωN hp
    exact absurd ⟨(h1 hωA hωN).1, hp⟩ h2
  have hPFp := pos_iff_ne_zero.2 hPF
  have hseed : ∀ ω ∈ {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)},
      rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) = 0 := fun ω hω =>
    le_antisymm (not_lt.1 hω.2) ((hconfF ω hω.1).changeCorner_props.1.1)
  have hcfgF : ∀ ω ∈ {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)},
      IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
        (fun t : ℝ => W' t.toNNReal ω) (η ω) := fun ω hω => (hF ω hω.1).2.2.2 (hseed ω hω)
  have hζF : ∀ ω ∈ {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)},
      ζ' ω = ⊤ := fun ω hω => (hF ω hω.1).2.1
  obtain ⟨ψ', hψ', hψ'm, -⟩ := exists_measurable_pocketMarksInf_pts
    (mΩ := wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)) hR''m hL''m hF0
    (fun ω hω => hconfF ω hω.1) hseed (fun ω hω => (hcfgF ω hω).oriented) 0
  obtain ⟨n', a', hn', hlimq⟩ := hsideI _ hF0 subset_rfl hPFp ψ' hψ' hψ'm
  have hU := fun q' : ℚ => isLocalSet_activeCompl_cfInf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR' hWL' hF0 hcfgF hF0
    subset_rfl hζF hψ' hψ'm hV.η_meas hn' (StripSys.rt q')
  choose gU hgU using fun q' : ℚ => IsLocalSet.exists_isLocalSetMean hhC (hU q').1 (hU q').2.1
  have hgerm := fun q' : ℚ => ae_r6Germ_four hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR hWL hWR' hWL' hP₁
    (isStopPocket_cfInf (X := fullHist ![R, L, innerRight k rL R MR, innerLeft k rR L ML])
      (wallsSigma_le hWR'.meas hWL'.meas) (wallsSigma_le_four_right hX R L _ _) hWad hR''m hL''m hF0 hcfgF hF0
      subset_rfl hζF hψ' hψ'm hV.η_meas hn' (StripSys.rt q'))
    hCm hCloc hCunb (hU q').1 (hU q').2.1 (hU q').2.2 hg (hgU q')
  have hgeo := hgeom' hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML (StripSys.rt q₀) A
    {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} ψ ψ' n n' s q
    (fun ω hω => ⟨hcfgI' ω (hAG hω), hψ ω hω⟩) (fun ω hω => ⟨hcfgF ω hω, hψ' ω hω⟩)
  have key := ae_exists_r6Cert_of_family (κ := k) (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
    (σL := fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4)) (σR := fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
    (ι := ℚ) (u := u₀')
    (E := {ω | ω ∈ A ∧ ω ∈ nestRelEventInf R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR)
      (innerLeft k rR L βL) s q ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)})
    (EC := pocketSetInf A R L (StripSys.rt q₀) η ψ n (StripSys.rt q))
    (outer := relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) (StripSys.rt q₀)) ψ ω)
      (n ω)) (travAllInf R L (StripSys.rt q₀) η ψ) (StripSys.rt q)) (g := g)
    (vL := fun ω i => geomLW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXL) i (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω)
        (StripSys.rt q))
    (vR := fun ω j => geomRW (fun t ω => segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω) t)
      (fun _ => LP.twoSeedXR) j (StripSys.rt q) ω - segDriver (travAllInf R L (StripSys.rt q₀) η ψ ω)
        (StripSys.rt q))
    (EU := fun q' => pocketSetInf
      {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)}
      (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q'))
    (inner := fun q' => relChart (fun ω => shiftChart (pChart
      {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)}
      (fun ω => cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
      (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')) (gU := gU)
    (wL := fun q' ω i => geomLW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
      (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
      segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) (StripSys.rt q'))
    (wR := fun q' ω j => geomRW (fun t ω => segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML)
      (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
      segDriver (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) (StripSys.rt q'))
    (aI := fun _ => a')
    (Live := fun q' => {ω | ω ∈ {ω | ω ∈ F ∧ ¬ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω)
      (StripSys.rt s)} ∧ ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
        capLife (travAllInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)})
    hg.2.1 (fun q' => (hgU q').2.1)
    (fun q' => (hlimq (StripSys.rt q') (gU q') (hgU q')).mono fun ω hω hL => hω hL.1 hL.2)
    (fun q' => hgerm q') (by
      filter_upwards [hin, hgeo] with ω h1 h2 hωE
      obtain ⟨hF', hN'⟩ := h1 hωE.1 hωE.2.1
      obtain ⟨q', hq', hgq'⟩ := h2 hωE.1 ⟨hF', hωE.2.2⟩ hN'
      exact ⟨q', ⟨⟨hF', hωE.2.2⟩, hq'⟩, hgq'⟩)
  filter_upwards [key] with ω hω hωA hωN hp
  exact hω ⟨hωA, hωN, hp⟩

/-- **R.6's certificates on outer pockets opening at the flow seed, mixed case, R48-safe** (supplement
pp. 475–477): `R6Fin.twoSeedNestCertInputInf_of_geom` without the strip-system input. -/
theorem twoSeedNestCertInputInf_of_geom_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {c c' : ℝ}
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hgeom : R6GeomMixedInfRemaining.{u} k rL rR c c') (hgeom' : R6GeomMixedInfInfRemaining.{u} k rL rR c c')
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c')
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR))
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
  intro A hA hAG hPA ψ hψ hψm n hn q s
  -- constants and the counterflow coupling
  have hk0 : 0 < k := lt_trans (by norm_num) hk4
  have hκ : 0 < 16 / k := R7.sixteen_div_pos hk0
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ c := (mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le).trans hcπ
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hgff hu₀
  obtain ⟨-, hT', hTr, hC⟩ := id hD
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ :=
    (ae_counterflow_trace_r7 hk4 hc hc' hgff hcfg.counterflow).mono fun ω hω => hω.1
  have hhC := isZeroBoundaryGFF_centredField hC hu₀'
  -- the walls
  have hWR := isWallData_R hk4 hcfg hu₀ hV
  have hWL := isWallData_L hk4 hcfg hu₀ hV
  obtain ⟨⟨MR, hMR⟩, ⟨ML, hML⟩⟩ := exists_isFrontierVersion hcfg
  have hWR' := isWallData_innerRight hk4 hcfg hu₀ hV hMR
  have hWL' := isWallData_innerLeft hk4 hcfg hu₀ hV hML
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
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hhC hCm hCloc
  refine ⟨g, hg, ?_⟩
  -- the inner parameter is positive on the nested event
  by_cases hs : 0 < s
  swap
  · refine Eventually.of_forall fun ω _ hωN => absurd ?_ hs
    have hpos := hωN.2.2.1.pos
    exact Rat.cast_pos.1 (Real.toNNReal_pos.1 hpos)
  filter_upwards [ae_certInf_pos_safe h411 h51 h47 h47T haux7 h44 hword hgeom hk4 hL hR hcπ hc' hmix hcfg hD hu₀'
      hV hGm hconf hζG hcfgI hA hAG hψ hψm hn q s hs hMR hML hg,
    ae_certInf_zero_safe h411 h51 h47 h47T haux7 h44 hword hgeom' hk4 hL hR hcπ hc' hmix hcfg hD hu₀' hV hGm hconf
      hζG hcfgI hA hAG hψ hψm hn q s hs hMR hML hg] with ω h1 h2 hωA hωN
  by_cases hp : 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
  · exact h1 hωA hωN hp
  · exact h2 hωA hωN hp

end Cert

end InteractingSLE.Sec7.R6Safe
