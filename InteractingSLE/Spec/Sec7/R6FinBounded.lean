/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FinCfg
import InteractingSLE.Spec.Sec7.R6FinWalls
import InteractingSLE.Spec.Sec7.R6FinGeom

/-!
# R.6's certificates on bounded outer pockets (mixed case)

PROVE-R6-CERT2. On every R.7 configuration of the mixed case and every bounded outer pocket test,
`twoSeedNestCertInput_of_geom` proves `R6Rel.TwoSeedNestCertInput` (the R.6 certificates of the inner pair) from:

* the inner pockets' R.5 word up to phase at the inner weights and margins (`PhaseCont.R7PhaseWordRemaining`,
  PROVE-POCKET-SIDEIN's target), through Aux. 122's zero phase (`R6Rel.inner_side_of_word`);
* the inner tests at every sample (`exists_cfgEvent_extremal`: Lemma 4.7's first exits, Aux. 37's attachments from
  a strip system, Proposition 5.5);
* the germ comparisons (`R6Cert.ae_r6Germ_outer_cf`, the joint walls–hull law at `T_C⁰(q) ∨ T_U⁰(q')`);
* the named pathwise input `R6GeomMixedRemaining` (the current-face geometry).

The outer mean is the local-set mean of the outer active complement (`R6Cert.isLocalSet_activeCompl_outer`); the
inner candidates are the inner pocket read at every rational relative time `q'` (`ae_exists_r6Cert_of_family`).

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

namespace InteractingSLE.Sec7.R6Fin

open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketCoord PocketJordan PocketMarks PocketWordAssembly
  PocketCoupling PocketStopField Lemma71C Lemma71I PocketTraversal PocketStop LocalSets PocketWordPerQ

/-! ### Small facts -/

section Small

variable {k rL rR : ℝ}

/-- In the mixed case the inner configuration is extremal. -/
theorem max_inner_weights_eq (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) :
    max (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4)) = k / 2 - 4 := by
  rcases hmix with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [innerRight, innerLeft, h1, ↓reduceIte, not_lt.2 h2]
    exact max_eq_left h2
  · simp only [innerRight, innerLeft, h2, ↓reduceIte, not_lt.2 h1]
    exact max_eq_right h1

/-- **Strip heights of the R.7 data at margins `c ≥ πχ(16/k)`, `c′ ≥ 0`** (as `R7Leaves.r7_strip_heights`). -/
theorem r7_strip_heights_ge {c c' : ℝ} (hk4 : 4 < k) (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c') :
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ ({0} : Finset ℝ) →
      prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k) ≤ -sleLambda (16 / k)) ∧
    ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ ({0} : Finset ℝ) →
      sleLambda (16 / k) ≤ prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hχ := Sec4.chiC_pos hκ hκ4
  refine ⟨fun a ha y hy _ => ?_, fun a ha y hy _ => ?_⟩
  · have h1 : a * chiC (16 / k) ≤ r7ThetaHi k rR * chiC (16 / k) :=
      mul_le_mul_of_nonneg_right (ha.2.trans (le_max_right _ _)) hχ.le
    simp only [prop74Data, hy, ↓reduceIte, r7A]
    linarith
  · have h1 : r7ThetaLo k rL * chiC (16 / k) ≤ a * chiC (16 / k) :=
      mul_le_mul_of_nonneg_right ((min_le_right _ _).trans ha.1) hχ.le
    simp only [prop74Data, not_lt_of_ge hy.le, ↓reduceIte, r7B]
    linarith

variable {Ω : Type*} {R L βR βL MR ML : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {s q : ℚ}

/-- The nested-pocket event only reads the frontiers at the sample. -/
theorem mem_nestRelEvent_congr {ω : Ω} (hR : MR ω = βR ω) (hL : ML ω = βL ω) :
    ω ∈ nestRelEvent R L r η ψ βR βL (innerRight k rL R βR) (innerLeft k rR L βL) s q ↔
      ω ∈ nestRelEvent R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q := by
  have e1 : innerRight k rL R βR ω = innerRight k rL R MR ω := by
    by_cases hd : k / 2 - 4 < rL <;> simp only [innerRight, hd, ↓reduceIte, hR]
  have e2 : innerLeft k rR L βL ω = innerLeft k rR L ML ω := by
    by_cases hd : k / 2 - 4 < rR <;> simp only [innerLeft, hd, ↓reduceIte, hL]
  simp only [nestRelEvent, mem_ofPred_eq, e1, e2, hR, hL]

end Small

/-! ### The certificates on one configuration -/

section Cert

variable {k rL rR : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **R.6's certificates on bounded outer pockets, mixed case** (supplement pp. 475–477): the conclusion of
`R6Rel.R6NestCertRemaining` for the bounded outer pocket shape on one R.7 configuration, from the inner R.5 word up to
phase, the landed a.s. inputs of the inner tests, and the named pathwise current-face geometry. -/
theorem twoSeedNestCertInput_of_geom (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    {c c' : ℝ} (hstrip : R7StripOnConfig.{u} k rL rR c c')
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hgeom : R6GeomMixedRemaining.{u} k rL rR c c') (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
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
    (hcfgP : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q₀) →
      IsOuterCfg (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    TwoSeedNestCertInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q₀) η
      {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)} (centredField h'' u₀') u₀' βR βL
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
  have hcfgP' : ∀ ω ∈ {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q₀)},
      IsOuterCfg (R ω) (L ω) (StripSys.rt q₀) (fun s : ℝ => W' s.toNNReal ω) (η ω) :=
    fun ω hω => hcfgP ω hω.1 hω.2
  have hζA : ∀ ω ∈ A, ζ' ω = ⊤ := fun ω hω => hζG ω (hAG hω).1
  obtain ⟨hCm, hCloc, -⟩ := isLocalSet_activeCompl_outer hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR.cont hWL.cont
    hWR.zero hWL.zero hWR.meas hWL.meas hWR.det hWL.det hWR.loc hWL.loc hGp hcfgP' hA hAG hζA hψ hψm hV.η_meas hn
    (StripSys.rt q)
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hhC hCm hCloc
  refine ⟨g, hg, ?_⟩
  -- the inner parameter is positive on the nested event
  by_cases hs : 0 < s
  swap
  · refine Eventually.of_forall fun ω _ hωN => absurd ?_ hs
    have hpos := hωN.2.2.1.pos
    exact Rat.cast_pos.1 (Real.toNNReal_pos.1 hpos)
  -- the inner configuration and its tests at `rt s`
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  have hcfgI := IsR7OuterConfig.inner h55 hk4 hL hR hc hc' hcfg
  have hVI := isR7Versions_inner (k := k) (rL := rL) (rR := rR) hV hMR hML
  obtain ⟨Es, hS⟩ := hstrip P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights_ge (rL := rL) (rR := rR) hk4 hcπ hc'
  have e : prop74Data (r7A k (innerLeft k rR rR (k / 2 - 4)) +
      (c + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4)))))
      (r7B k (innerRight k rL rL (k / 2 - 4)) + (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4))))) =
      prop74Data (r7A k rR + c) (r7B k rL + c') := by
    congr 1 <;> ring
  obtain ⟨F, hFm, hFae, hF⟩ := exists_cfgEvent_extremal h411 h51 h47 h47T haux7 h44 hk4
    (neg_two_lt_innerRight_weight hk4 hL) (neg_two_lt_innerLeft_weight hk4 hR) (max_inner_weights_eq hmix)
    (innerMarginL_nonneg hk4 hc) (innerMarginR_nonneg hk4 hc') hcfgI (Es := Es) (by rw [e]; exact hS)
    (by rw [e]; exact hcumL) (by rw [e]; exact hcumR) hVI s hs
  have hR''m := measurable_right_wallsSigma (P := P) hWR'.cont hWL'.cont
  have hL''m := measurable_left_wallsSigma (P := P) hWR'.cont hWL'.cont
  have hconfF : ∀ ω ∈ F, IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hF ω hω).1
  have hFp := (measurableSet_rightLo_pos_and (mΩ := wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML))
    hR''m hL''m hFm hconfF).1
  -- almost every sample of the nested event is in the bounded inner test
  have hin : ∀ᵐ ω ∂P, ω ∈ A →
      ω ∈ nestRelEvent R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR) (innerLeft k rR L βL) s q →
      ω ∈ {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} ∧
      ω ∈ nestRelEvent R L (StripSys.rt q₀) η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q := by
    filter_upwards [hFae, hMR.2.2.2, hML.2.2.2] with ω hωF hωR hωL hωA hωN
    have hωN' := (mem_nestRelEvent_congr hωR hωL).1 hωN
    have hc'' := hωN'.2.2.1
    exact ⟨⟨hωF hc''.off, rightLo_pos_of_cfPocket_subset (hconf ω (hAG hωA).1) (hAG hωA).2
      hc''.isChangeConfigInc hωN'.2.2.2.1⟩, hωN'⟩
  by_cases hPF : P {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} = 0
  · have hnull := measure_eq_zero_iff_ae_notMem.1 hPF
    filter_upwards [hin, hnull] with ω h1 h2 hωA hωN
    exact absurd (h1 hωA hωN).1 h2
  have hPFp := pos_iff_ne_zero.2 hPF
  have hPF0 : 0 < P F := lt_of_lt_of_le hPFp (measure_mono fun ω hω => hω.1)
  have hcfgF : ∀ ω ∈ {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)},
      IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
        (fun t : ℝ => W' t.toNNReal ω) (η ω) := fun ω hω => (hF ω hω.1).2.2.1 hω.2
  have hζF : ∀ ω ∈ {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)},
      ζ' ω = ⊤ := fun ω hω => (hF ω hω.1).2.1
  -- the inner Jordan chart and the inner zero-phase word
  obtain ⟨ψ', hψ', hψ'm, -⟩ := exists_measurable_pocketMarks_pts
    (mΩ := wallsSigma P (innerRight k rL R MR) (innerLeft k rR L ML)) hR''m hL''m hFp
    (fun ω hω => hconfF ω hω.1) (fun ω hω => zero_notMem_closure_of_rightLo_pos (hconfF ω hω.1) hω.2)
    (fun ω hω => (hcfgF ω hω).oriented) 0
  obtain ⟨hside, -⟩ := inner_side_of_word h55 hk4 hL hR hc hc' hword hcfg hD hu₀' hV hMR hML s hs F hFm hPF0
    hconfF (fun ω hω => (hF ω hω).2.1) (fun ω hω => (hF ω hω).2.2.1) (fun ω hω => (hF ω hω).2.2.2)
  obtain ⟨n', a', hn', hlimq⟩ := hside _ hFp subset_rfl hPFp ψ' hψ' hψ'm
  -- the inner local sets and means at every rational relative time
  have hU := fun q' : ℚ => isLocalSet_activeCompl_cf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR'.cont hWL'.cont
    hWR'.zero hWL'.zero hWR'.meas hWL'.meas hWR'.det hWL'.det hWR'.loc hWL'.loc hFp hcfgF hFp subset_rfl hζF hψ'
    hψ'm hV.η_meas hn' (StripSys.rt q')
  choose gU hgU using fun q' : ℚ => IsLocalSet.exists_isLocalSetMean hhC (hU q').1 (hU q').2.1
  -- the germ comparisons
  have hgerm := fun q' : ℚ => ae_r6Germ_outer_cf hT' hTr hu₀.1 hh0 hC hk0 hu₀' hX hζ hWR.cont hWL.cont hWR.zero
    hWL.zero hWR.meas hWL.meas hWR.det hWL.det hWR.loc hWL.loc hWR'.cont hWL'.cont hWR'.zero hWL'.zero hWR'.meas
    hWL'.meas hWR'.det hWL'.det hWR'.loc hWL'.loc hV.η_meas hGp hcfgP' hA hAG hζA hψ hψm hn (StripSys.rt q) hFp hcfgF
    hFp subset_rfl hζF hψ' hψ'm hn' (StripSys.rt q') hg (hgU q')
  -- the pathwise geometry
  have hgeo := hgeom hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML (StripSys.rt q₀) A
    {ω | ω ∈ F ∧ 0 < rightLo (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)} ψ ψ' n n' s q
    (fun ω hω => ⟨hcfgP' ω (hAG hω), hψ ω hω⟩) (fun ω hω => ⟨hcfgF ω hω, hψ' ω hω⟩)
  -- the family of inner candidates
  have key := ae_exists_r6Cert_of_family (κ := k) (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR)
    (σL := fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4)) (σR := fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
    (ι := ℚ) (u := u₀')
    (E := {ω | ω ∈ A ∧
      ω ∈ nestRelEvent R L (StripSys.rt q₀) η ψ βR βL (innerRight k rL R βR) (innerLeft k rR L βL) s q})
    (EC := pocketSet A R L (StripSys.rt q₀) η ψ n (StripSys.rt q))
    (outer := relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) (StripSys.rt q₀)) ψ ω) (n ω))
      (travAll R L (StripSys.rt q₀) η ψ) (StripSys.rt q)) (g := g)
    (vL := fun ω i => geomLW (fun t ω => segDriver (travAll R L (StripSys.rt q₀) η ψ ω) t) (fun _ => LP.twoSeedXL) i
      (StripSys.rt q) ω - segDriver (travAll R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
    (vR := fun ω j => geomRW (fun t ω => segDriver (travAll R L (StripSys.rt q₀) η ψ ω) t) (fun _ => LP.twoSeedXR) j
      (StripSys.rt q) ω - segDriver (travAll R L (StripSys.rt q₀) η ψ ω) (StripSys.rt q))
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
      obtain ⟨hF', hN'⟩ := h1 hωE.1 hωE.2
      obtain ⟨q', hq', hgq'⟩ := h2 hωE.1 hF' hN'
      exact ⟨q', ⟨hF', hq'⟩, hgq'⟩)
  filter_upwards [key] with ω hω hωA hωN
  exact hω ⟨hωA, hωN⟩

end Cert

end InteractingSLE.Sec7.R6Fin
