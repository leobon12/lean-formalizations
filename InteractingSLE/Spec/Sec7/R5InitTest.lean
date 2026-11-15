/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5InitPocket
import InteractingSLE.Spec.Sec7.SideC16GeneralFrame
import InteractingSLE.Spec.Sec7.SideC15Branch
import InteractingSLE.Spec.Sec7.R5FreshInit

/-!
# R.5's initial heights, part 2: `R7InitialHeights` on every R.7 test (ruling R98)

Packet PROVE-R5-INIT. Astra's pocket-mean note (`source/external/AstraIG1/ig1_pocket_mean_and_frames.txt`, ruling
R98): Theorem 9 / Remark 10 (the original filled-pocket mean of the two constant-angle arms is the flow word, with
source constant `b = 0`; `R5Init.ae_eqOn_selectedChangePocket_r7` below), Proposition 15 and §5.1 (transport through
`m(z) = −1/z` with `F = −h ∘ m + πχ − 2χ Arg z`, landed as PROVE-SIDE-COLLAR2's `SideC16.sampleFrame_of_originalMean`,
and the native two-seed word, `SideC16.centeredReversedMean_eq_twoSeed_of_sourceExtension`), and (14): the relift
`ℓ_c ↦ ℓ_c + 2π(n − 1)` (`shiftChart c (1 − n)`) with the walls-measurable source integer `n`
(`SideC15.exists_measurable_branch_conjugate_pChart`) and offset `a = 0`
(`SideC16.r7InitialHeights_zero_of_originalMean`).

* **`exists_r7InitialHeights_of_flowChart`**: on a walls-measurable selection of R.7 change pockets with a conformal
  counterflow coordinate whose conjugate is a flow chart, `R5Wall.R7InitialHeights` holds with offset `0`, the
  chart `shiftChart (pChart A C ψ) (1 − n)` and every exceptional selector `X₀`;
* **`twoSeedSplitInputInit_r7`**, **`twoSeedSplitInputInitInf_r7`**: R5-FRESHTIP's named per-test inputs
  `R5Fresh.TwoSeedSplitInputInit(Inf)` (both pocket shapes), with `X₀ = ∅`;
* **`r7SplitRemainingInit_proved`**: `R5Fresh.R7SplitRemainingInit k rL rR c c'` for every `k > 4`, all weights and
  margins — the last named input of the extremal R.5 bundle;
* **`r7R5RemainingOn_of_partA`**, **`r7R5RemainingOn_of_aux7`** and the phase-word twins: extremal R.5 from Zhan's
  Part A inputs (resp. Aux. lemma 7 at `k`) alone.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses (no `*_of_param`, no `*_of_thm12_thm13`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R5Init

open LocalSets WholeField Aux119Bdry Aux119Heights Aux2728Pocket PocketCoord PocketJordan PocketMarks PocketStop
  PocketStopSide PocketStopField PocketTraversal PocketWordAssembly PocketSeedOpen PocketWordPerQ PocketUnionPt
  R7Outer R7Leaves R5Wall Lemma71N Lemma71I SideC13

/-! ### The pocket chart and the zero-time exterior -/

section Geom

variable {Ω : Type*}

/-- On the event, the pocket chart `(ψ, ψ⁻¹, Im ℓ)` is a domain chart of the pocket. -/
theorem isDomainChart_pChart {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) {ω : Ω} (hω : ω ∈ A) :
    IsDomainChart (C ω) (pChart A C ψ ω) := by
  have hc := (pChart_props hCo hCH hψ ω).2.2.1
  refine ⟨hc, hc.coe_dom.symm.trans ?_, pLog A C ψ ω, isDerivLog_pLog hCo hψ hω, fun _ _ => rfl⟩
  rw [(pChart_props hCo hCH hψ ω).2.2.2]
  ext z
  simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]

theorem negInv_image_H : negInv '' H = H := by
  have h := WangWu.H_diff_image_negInv (∅ : Set ℂ)
  simp only [image_empty, sdiff_empty] at h
  exact h.symm

/-- **The zero-time pocket exterior, read in the original frame**: `m(B ∪ R₀) = ℍ ∖ C_orig` with `C_orig` the
selected original change pocket (`ℍ` off the test). -/
theorem negInv_image_liveExt_zero {A : Set Ω} {γ : Ω → ℝ → ℂ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (ω : Ω) :
    negInv '' liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0 ω =
      H \ SideC14.selectedChangePocket A R L r ω := by
  rw [liveExt_zero_eq_eventFilled hγ]
  by_cases hω : ω ∈ A
  · rw [eventFilled, ite_eq_left hω, SideC14.selectedChangePocket, ite_eq_left hω]
    have e : extHullSet (cfPocket (R ω) (L ω) r) ∅ = H \ cfPocket (R ω) (L ω) r := by
      ext z
      simp only [extHullSet, mem_inter_iff, mem_union, mem_compl_iff, mem_empty_iff_false, or_false, Set.mem_sdiff]
    rw [e, cfPocket, WangWu.H_diff_image_negInv, WangWu.image_negInv_image_negInv]
  · rw [eventFilled, ite_eq_right hω, SideC14.selectedChangePocket, ite_eq_right hω, sdiff_empty, negInv_image_H]

theorem liveExt_zero_eq_negInv {A : Set Ω} {γ : Ω → ℝ → ℂ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) :
    liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0 =
      fun ω => negInv '' (H \ SideC14.selectedChangePocket A R L r ω) := by
  funext ω
  rw [← negInv_image_liveExt_zero hγ ω, WangWu.image_negInv_image_negInv]

/-- The zero-time exterior is relatively closed in `ℍ`. -/
theorem liveExt_zero_regular {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hCo : ∀ ω ∈ A, IsOpen (C ω)) (ω : Ω) :
    liveExt A γ C (fun _ => ∅) 0 ω ⊆ H ∧ IsOpen (H \ liveExt A γ C (fun _ => ∅) 0 ω) := by
  rw [liveExt_zero_eq_eventFilled hγ]
  exact eventFilled_regular hCo (fun _ _ => by rw [sdiff_empty]; exact QuantumZipper.isOpen_H) ω

/-- On the test the complement of the zero-time exterior is the pocket. -/
theorem H_diff_liveExt_zero {A : Set Ω} {γ : Ω → ℝ → ℂ} {C : Ω → Set ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ω : Ω} (hω : ω ∈ A) :
    H \ liveExt A γ C (fun _ => ∅) 0 ω = C ω := by
  rw [liveExt_zero_eq_eventFilled hγ, eventFilled, ite_eq_left hω]
  ext z
  simp only [extHullSet, Set.mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff, mem_empty_iff_false, or_false]
  exact ⟨fun h => not_not.1 fun h' => h.2 ⟨h.1, h'⟩, fun h => ⟨hCH ω hω h, fun h' => h'.2 h⟩⟩

end Geom

/-! ### The original filled-pocket formula for the R.7 arms -/

section Original

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **Astra's Theorem 9 for R.7's arms** (constant angles `θ_R`, `θ_L`, no angle bound; the first original-frame fact
of the pocket-mean note): for walls `R`, `L` that are versions of the arms `α_R`, `α_L`, a walls-measurable test `A` of
change pockets, and every version `gC` of the mean of the selected pocket's exterior, almost surely on `A`, every
harmonic representative of `gC` on the pocket plus the original mean `u₀` is the explicit two-height word read in every
flow chart of the pocket, with the chart's lift and its common branch. -/
theorem ae_eqOn_selectedChangePocket_r7 (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (prop74Data (r7A k rR + c) (r7B k rL + c'))
      ((({0} : Finset ℝ)) : Set ℝ) u₀)
    {r : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A)
    (hconf : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r) {gC : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (fun ω => H \ SideC14.selectedChangePocket A R L r ω) (centredField h u₀) P gC) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (changePocket (R ω) (L ω) r) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ changePocket (R ω) (L ω) r → gC ω φ = ∫ z, v z * φ z) →
      ∀ (Ψ : ℂ → ℂ) (c₀ : Chart) (ℓ : ℂ → ℂ) (n : ℤ), IsFlowChart (R ω) (L ω) r Ψ c₀ →
      IsDerivLog c₀.1 ℓ (changePocket (R ω) (L ω) r) →
      (∀ z ∈ changePocket (R ω) (L ω) r, c₀.2.2 z = (ℓ z).im) → IsPocketBranch (L ω) (R ω) c₀ n →
      ∀ z ∈ changePocket (R ω) (L ω) r, v z + u₀ z =
        r7FlowMean (16 / k) (rs136Theta1 (16 / k) rL) (rs136Theta2 (16 / k) rR) (c₀.1 z) -
          chiC (16 / k) * (c₀.2.2 z + 2 * π * n) := by
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := by positivity
  have hκ4 : 16 / k < 4 := by rw [div_lt_iff₀ hk0]; linarith
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  have hgff := hcfg.gff
  obtain ⟨ΦαR, ΦβR, ΦβL, ΦαL, hΦαR, -, -, hΦαL, hΦ⟩ := hcfg.borel
  have hreg := hcfg.regular
  have hζR : ∀ᵐ ω ∂P, ζαR ω = ⊤ := hreg.mono fun ω hω => hω.2.2.2.2.1
  have hζL : ∀ᵐ ω ∂P, ζαL ω = ⊤ := hreg.mono fun ω hω => hω.2.2.2.2.2.2.2
  have hdetR := fun t => hdet_of_borel hΦαR (fun ω => (hΦ ω).1) hV.R_ae u₀ t
  have hdetL := fun t => hdet_of_borel hΦαL (fun ω => (hΦ ω).2.2.2) hV.L_ae u₀ t
  have hlocR := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αR hζR hu₀ hV.R_cont hV.R_zero
    hV.R_meas hV.R_ae
  have hlocL := isEntranceHistoryLocal_of_flowLine hκ hκ4 hb hgff hcfg.flow_αL hζL hu₀ hV.L_cont hV.L_zero
    hV.L_meas hV.L_ae
  have hflR := Lemma71G.IsFlowLine.congr_ae (η' := R) hcfg.flow_αR (hV.R_ae.mono fun ω hω t => by rw [hω])
  have hflL := Lemma71G.IsFlowLine.congr_ae (η' := L) hcfg.flow_αL (hV.L_ae.mono fun ω hω t => by rw [hω])
  have hRsp : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.1
  have hLsp : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.2.2.2.1
  obtain ⟨_, _, WR, _, _, _, _, hCR, htrR⟩ := hcfg.flow_αR
  obtain ⟨_, _, WL, _, _, _, _, hCL, htrL⟩ := hcfg.flow_αL
  have hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => WR t ω) ⊤ (R ω) ∧ Continuous (fun t => WR t ω) ∧
      WR 0 ω = 0 := by
    filter_upwards [htrR, hζR, hV.R_ae, hCR.1.2.2.2.2] with ω h1 hz he hp
    rw [hz] at h1 hp
    refine ⟨?_, continuousOn_univ.mp (hp.2.2.2.1.mono fun t _ => ENNReal.coe_lt_top), hp.1⟩
    rw [he]
    simpa only [Complex.ofReal_zero, sub_zero] using h1
  have hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => WL t ω) ⊤ (L ω) ∧ Continuous (fun t => WL t ω) ∧
      WL 0 ω = 0 := by
    filter_upwards [htrL, hζL, hV.L_ae, hCL.1.2.2.2.2] with ω h1 hz he hp
    rw [hz] at h1 hp
    refine ⟨?_, continuousOn_univ.mp (hp.2.2.2.1.mono fun t _ => ENNReal.coe_lt_top), hp.1⟩
    rw [he]
    simpa only [Complex.ofReal_zero, sub_zero] using h1
  have hRw := fun t => measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hLw := fun t => measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hCm := SideC14.measurable_selectedChangePocket_exterior hV.R_cont hV.L_cont hRw hLw hA hconf
  obtain ⟨hCo, hCs, hCc⟩ := SideC14.selectedChangePocket_geometry hconf
  have hfill := ae_eqOn_filledPocket_allAngles_ae hκ hb hgff hu₀ hflL hζL hflR hζR hV.L_cont hV.L_zero
    hV.L_meas hdetL hlocL hV.R_cont hV.R_zero hV.R_meas hdetR hlocR hLsp hRsp
    (WL := fun ω t => WL t ω) (WR := fun ω t => WR t ω) hLtr hRtr hCm hCo hCs (ae_of_all _ hCc) hgC
  have hleft : ∀ᵐ ω ∂P, ω ∈ A → changePocket (R ω) (L ω) r ⊆ leftSideOf (range (R ω)) := by
    filter_upwards [hcfg.order, hV.R_ae, hV.L_ae] with ω hord hRe hLe hω
    have hsub : range (L ω) ⊆ closedLeftSide (R ω) := by rw [hRe, hLe]; exact hord.2.1
    have hd := Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide (hconf ω hω).left
      (hconf ω hω).right hsub
    exact (hconf ω hω).changePocket_subset_leftSideOf
      ((hconf ω hω).mem_leftSideOf_of_leftFrontier (hconf ω hω).left rfl hd)
  filter_upwards [hfill, hleft] with ω hfω hlω hω v hv hrep Ψ c₀ ℓ n hF hℓ hlift hn z hz
  have hsel : SideC14.selectedChangePocket A R L r ω = changePocket (R ω) (L ω) r := ite_eq_left hω
  rw [← hsel] at hv hrep hz
  exact hfω v hv hrep r Ψ c₀ ℓ n _ hsel hF (hlω hω) hℓ hlift hn
    (isBoundedHarmonicExtension_r7FlowMean _ _ _ _ _ _ _ _) z hz

end Original

/-! ### The initial heights on one test -/

section Test

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {u₀' : ℂ → ℝ}

/-- **R.7's initial heights on one test** (R98, §5.1 and (14)): for a walls-measurable test `A` of change pockets with
a traversal `γ` driven on `A` and a conformal counterflow coordinate `ψ` of the inverted pocket whose conjugate pocket
chart is a flow chart, there is a walls-measurable integer `n` (`1 −` the source branch) such that
`R5Wall.R7InitialHeights` holds for the relifted pocket chart `shiftChart (pChart A C ψ) n`, with offset `0`, the
two-seed word `(r_L; r_R)` at `0`, and every exceptional selector. -/
theorem exists_r7InitialHeights_of_flowChart (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η)
    {r : ℝ≥0} {A : Set Ω} (hA : MeasurableSet[wallsSigma P R L] A)
    (hconf : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    {ψ Ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H)
    (hψm : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z))
    (hF : ∀ ω ∈ A, IsFlowChart (R ω) (L ω) r (Ψ ω)
      (conjugateFlowChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω))) :
    ∃ n : Ω → ℤ, Measurable[wallsSigma P R L] n ∧ ∀ X₀ : Ω → Set ℂ,
      R7InitialHeights k (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ (fun ω => cfPocket (R ω) (L ω) r)
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR)
        (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) 0
        (centredField h'' u₀') u₀' X₀ := by
  have hk0 : 0 < k := by linarith
  have hκ : 0 < 16 / k := by positivity
  have hκ4 : 16 / k < 4 := by rw [div_lt_iff₀ hk0]; linarith
  have e : 16 / (16 / k) = k := by field_simp
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨-, hT, hTr, hCcf⟩ := hD
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / k))) (chiC (16 / (16 / k)))
      (h ω) (h' ω) := by
    rw [e]; exact hT
  have hTr' : ∀ ω, IsTranslateAddConst 0 0 (h' ω) (h'' ω) := by simpa only [zero_mul] using hTr
  have hRw := fun t => measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hLw := fun t => measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    WangWu.isOpen_image_negInv (hconf ω hω).isOpen_changePocket (hconf ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hconf ω hω).changePocket_subset_H
  have hCmem : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRw hLw hA hconf hA subset_rfl z
  obtain ⟨n₀, hn₀m, hn₀⟩ := SideC15.exists_measurable_branch_conjugate_pChart (mΩ := wallsSigma P R L)
    hV.L_cont hV.L_zero hLw hA hCo hCH hψ hCmem hψm (fun _ _ => rfl) hF
  refine ⟨fun ω => 1 - n₀ ω, SideC16.measurable_canonicalShift hn₀m, fun X₀ => ?_⟩
  have hc : ∀ ω ∈ A, IsDomainChart (cfPocket (R ω) (L ω) r)
      (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) := fun ω hω => isDomainChart_pChart hCo hCH hψ hω
  have hB := liveExt_zero_regular (C := fun ω => cfPocket (R ω) (L ω) r) hγ hCo
  have hBC : ∀ ω ∈ A, H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0 ω =
      cfPocket (R ω) (L ω) r := fun ω hω => H_diff_liveExt_zero hγ hCH hω
  have hBm : Measurable[mΩ, hittingSigma] (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0) := by
    rw [liveExt_zero_eq_negInv hγ]
    exact WangWu.measurable_image_negInv.comp
      ((SideC14.measurable_selectedChangePocket_exterior hV.R_cont hV.L_cont hRw hLw hA hconf).mono
        (wallsSigma_le hV.R_meas hV.L_meas) le_rfl)
  have hhm : Measurable (centredField h'' u₀') := WholeField.measurable_centredField hCcf.2.1 u₀'
  have hNative : ∀ ω ∈ A, EqOn (PocketStopSide.centeredReversedMean (16 / k)
      ((fun _ => r7FlowMean (16 / k) (rs136Theta1 (16 / k) rL) (rs136Theta2 (16 / k) rR)) ω))
      (MartChar.meanExt (16 / (16 / k)) (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) 0 LP.twoSeedXL LP.twoSeedXR) H :=
    fun ω hω => SideC16.centeredReversedMean_eq_twoSeed_of_sourceExtension hκ hκ4 rL rR (hF ω hω)
      (isBoundedHarmonicExtension_r7FlowMean _ _ _ _ _ _ _ _)
  intro gcf hgcf
  have hgO := SideC15.localSetMean_inversePhysicalMean hB hT' hTr' hu₀.1 hu₀'.1 hgcf
  have hSetF : (fun ω => negInv '' liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0 ω) =
      fun ω => H \ SideC14.selectedChangePocket A R L r ω := funext (negInv_image_liveExt_zero hγ)
  have hgC : IsLocalSetMean (fun ω => H \ SideC14.selectedChangePocket A R L r ω) (centredField h u₀) P
      (fun ω => SideC15.inversePhysicalMean (-(π * chiC (16 / k))) (chiC (16 / (16 / k))) 0 u₀ u₀' (gcf ω)) := by
    rw [← hSetF]; exact hgO
  have hfill := ae_eqOn_selectedChangePocket_r7 hk4 hcfg hV hu₀ hA hconf hgC
  have hFlow : ∀ᵐ ω ∂P, ω ∈ A → ∀ z ∈ cfPocket (R ω) (L ω) r,
      harmRep (SideC15.inversePhysicalMean (-(π * chiC (16 / k))) (chiC (16 / (16 / k))) 0 u₀ u₀' (gcf ω))
          (H \ negInv '' liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0 ω) (negInv z) +
          u₀ (negInv z) =
        (fun _ => r7FlowMean (16 / k) (rs136Theta1 (16 / k) rL) (rs136Theta2 (16 / k) rR)) ω
            (SideC12.conjugateFlowMap (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (negInv z)) -
          chiC (16 / k) * (SideC12.conjugateFlowLift (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω)
            (negInv z) + 2 * π * (n₀ ω : ℝ)) := by
    filter_upwards [hfill, hgC.2.1] with ω hfω hharm hω z hz
    have hsel : SideC14.selectedChangePocket A R L r ω = changePocket (R ω) (L ω) r := ite_eq_left hω
    have hselH : SideC14.selectedChangePocket A R L r ω ⊆ H := by
      rw [hsel]; exact (hconf ω hω).changePocket_subset_H
    rw [Set.sdiff_sdiff_cancel_left hselH, hsel] at hharm
    rw [negInv_image_liveExt_zero hγ ω, Set.sdiff_sdiff_cancel_left hselH, hsel]
    obtain ⟨hv, hrep⟩ := harmRep_spec hharm
    obtain ⟨ℓ, hℓ, hlift⟩ := (isDomainChart_conjugate_pocket (C := changePocket (R ω) (L ω) r) (hc ω hω)).2.2
    obtain ⟨w, hw, rfl⟩ := hz
    simp only [WangWu.negInv_negInv]
    exact hfω hω _ hv hrep (Ψ ω) _ ℓ (n₀ ω) (hF ω hω) hℓ (fun _ hz => hlift hz) (hn₀ ω hω) w hw
  have key := SideC16.r7InitialHeights_zero_of_originalMean (nL := 0) (nR := 0) hκ hT' hTr' hu₀.1 hu₀'.1
    (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) hc hB hBC hgO hFlow hNative hBm hhm X₀
  rw [e] at key
  exact key gcf hgcf

end Test

/-! ### The two pocket shapes and the bundle -/

section Shapes

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
  {b' : ℝ → ℝ} {J' : Finset ℝ} {h' h'' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
  {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {u₀' : ℂ → ℝ}

/-- **R5-FRESHTIP's per-test initial-heights input, bounded change pockets** (`X₀ = ∅`, offset `0`). -/
theorem twoSeedSplitInputInit_r7 (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {r : ℝ≥0} {G : Set Ω}
    (hcfgP : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    R5Fresh.TwoSeedSplitInputInit k rL rR P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG _ ψ hψ hψm
  have hconf : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfgP ω (hAG hω)).conf
  have hRw := fun t => measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hLw := fun t => measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hCmem : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRw hLw hA hconf hA subset_rfl z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCmem z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const
      (fun ω hω => ⟨subset_closure hω.2, fun he => (hconf ω hω.1).cfPt_openPt_notMem (he ▸ hω.2)⟩)
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    WangWu.isOpen_image_negInv (hconf ω hω).isOpen_changePocket (hconf ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hconf ω hω).changePocket_subset_H
  have hψb : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hF : ∀ ω ∈ A, IsFlowChart (R ω) (L ω) r (SideAnc.jordanUnif (openPt (R ω) (L ω) r) (ψ ω))
      (conjugateFlowChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω)) := fun ω hω =>
    isFlowChart_conjugate (hcfgP ω (hAG hω)).conf
      (zero_notMem_closure_of_rightLo_pos (hcfgP ω (hAG hω)).conf (hcfgP ω (hAG hω)).bounded)
      (hcfgP ω (hAG hω)).oriented (hψ ω hω) (isDomainChart_pChart hCo hCH hψb hω)
      (fun z _ => by change pFwd A ψ ω z = ψ ω z; rw [pFwd_of_mem hω])
  obtain ⟨n, hn, hI⟩ := exists_r7InitialHeights_of_flowChart hk4 hcfg hD hu₀' hV hA hconf
    (fun ω hω => ((hcfgP ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) hψb hψm' hF
  exact ⟨n, hn, 0, ⟨0, by simp⟩, fun _ => ∅, fun _ => finite_empty, hI _⟩

/-- **R5-FRESHTIP's per-test initial-heights input, pockets opening at the flow seed** (`X₀ = ∅`, offset `0`). -/
theorem twoSeedSplitInputInitInf_r7 (hk4 : 4 < k)
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    (hD : IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0) (flowLineRhoR k b' J' 0 0)
      (flowLineXL b' J' 0) (flowLineXR b' J' 0)) (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀')
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {r : ℝ≥0} {G : Set Ω}
    (hcfgI : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω)) :
    R5Fresh.TwoSeedSplitInputInitInf k rL rR P R L r η G (centredField h'' u₀') u₀' := by
  intro A hA hAG _ ψ hψ hψm
  have hconf : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfgI ω (hAG hω)).conf
  have hRw := fun t => measurable_right_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hLw := fun t => measurable_left_wallsSigma (P := P) hV.R_cont hV.L_cont t
  have hCmem : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRw hLw hA hconf hA subset_rfl z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCmem z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const (fun _ hω => subset_closure hω.2)
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    WangWu.isOpen_image_negInv (hconf ω hω).isOpen_changePocket (hconf ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hconf ω hω).changePocket_subset_H
  have hψb : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hF : ∀ ω ∈ A, IsFlowChart (R ω) (L ω) r (SideAnc.jordanUnif (openPt (R ω) (L ω) r) (ψ ω))
      (conjugateFlowChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω)) := fun ω hω =>
    isFlowChart_conjugate_inf (hcfgI ω (hAG hω)).conf (hcfgI ω (hAG hω)).seed (hcfgI ω (hAG hω)).oriented
      (hψ ω hω) (isDomainChart_pChart hCo hCH hψb hω)
      (fun z _ => by change pFwd A ψ ω z = ψ ω z; rw [pFwd_of_mem hω])
  obtain ⟨n, hn, hI⟩ := exists_r7InitialHeights_of_flowChart hk4 hcfg hD hu₀' hV hA hconf
    (fun ω hω => ((hcfgI ω (hAG hω)).isDrivenCurve (hψ ω hω)).1) hψb hψm' hF
  exact ⟨n, hn, 0, ⟨0, by simp⟩, fun _ => ∅, fun _ => finite_empty, hI _⟩

end Shapes

/-- **R5-FRESHTIP's last named input of the extremal R.5 bundle, proved**: `R5Fresh.R7SplitRemainingInit` for every
`k > 4`, all seed weights `r_L`, `r_R` and margins `c`, `c′` (R98: Theorem 9, Proposition 15, (14), with `a = 0`). -/
theorem r7SplitRemainingInit_proved {k rL rR c c' : ℝ} (hk4 : 4 < k) :
    R5Fresh.R7SplitRemainingInit.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
    q _ G _ _ hconf _ hcfgP hcfgI
  exact ⟨twoSeedSplitInputInit_r7 hk4 hcfg hD hu₀' hV (fun ω hω => hcfgP ω hω.1 hω.2),
    twoSeedSplitInputInitInf_r7 hk4 hcfg hD hu₀' hV (fun ω hω => hcfgI ω hω.1
      (le_antisymm (not_lt.1 hω.2) ((hconf ω hω.1).changeCorner_props.1.1)))⟩

/-- **Lemma R.5 on every extremal R.7 configuration from Aux. lemma 7 at `k`** (no other named input). -/
theorem r7R5RemainingOn_of_aux7 {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) : R5Enl.R7R5RemainingOn.{u} k rL rR c c' :=
  R5Fresh.r7R5RemainingOn_of_splitInit hk4 hc hc' haux7 (r7SplitRemainingInit_proved hk4)

/-- **R.5 up to phase on every R.7 pocket test from Aux. lemma 7 at `k`**. -/
theorem r7PhaseWordRemaining_of_aux7 {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (haux7 : Sec4.Aux7Statement.{u} k) : PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c' :=
  R5Fresh.r7PhaseWordRemaining_of_splitInit hk4 hc hc' haux7 (r7SplitRemainingInit_proved hk4)

/-- **Lemma R.5 on every extremal R.7 configuration from Zhan's Part A inputs** (no other named input). -/
theorem r7R5RemainingOn_of_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) : R5Enl.R7R5RemainingOn.{u} k rL rR c c' :=
  R5Fresh.r7R5RemainingOn_of_splitInit_partA hk4 hc hc' hA (r7SplitRemainingInit_proved hk4)

/-- **R.5 up to phase on every R.7 pocket test from Zhan's Part A inputs**. -/
theorem r7PhaseWordRemaining_of_partA {k rL rR c c' : ℝ} (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hA : Sec5.PartAInputsSixteenDiv) : PhaseCont.R7PhaseWordRemaining.{u} k rL rR c c' :=
  R5Fresh.r7PhaseWordRemaining_of_splitInit_partA hk4 hc hc' hA (r7SplitRemainingInit_proved hk4)

end InteractingSLE.Sec7.R5Init
