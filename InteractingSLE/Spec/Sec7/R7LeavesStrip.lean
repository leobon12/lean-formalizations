/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LeavesExtremal
import InteractingSLE.Spec.Sec7.Aux37WallsR7

/-!
# Theorem R.7's extremal pockets: Aux. lemma 37's attachments from a strip system on the R.7 field

Packet PROVE-R7-LEAVES. `R7Leaves.r7PocketStop_extremal_of_config` leaves Aux. lemma 37's attachment constancy for
the two walls as an input. PROVE-AUX37-WALLS proved its witness exclusion (`Aux37Walls.hwit_r7`, `hwitI_r7`) for the
constant-angle walls `η_θ` of a strip system (`StripSys.IsStripSystem`, whose staged histories include the
constant-angle programs `R7Aux131.constSpec θ`). This file transfers it to the arms of an R.7 configuration carried by
the same field and counterflow:

* `ae_regular_const`, `stagedPiecesRegular_const`, `regStrip_const`: the constant-angle program of a strip system is
  regular (R51), so the regularized family `StripWall.regStrip` is regular at every sample on it;
* `ae_isGeneratingTrace_of_isFlowLine`: a flow line of `(4.4)` data is almost surely the generating trace of every
  flow-line driver of the same field at the same angle (both drivers are `AdmCode.admDrv` of the field, R74-allowed
  `Theorem12ParamCond44Statement`);
* `r7Attach_of_stripSystem`: the attachment constancy inputs of `R7ExtremalInputs` for any versions of the arms, from
  the rational first exits and a strip system on the same field and counterflow;
* `R7ExtremalStripRemaining`, `r7ExtremalRemaining_of_strip`: the remaining extremal inputs with the attachments
  replaced by the existence of a strip system on every configuration (heights `c = πχ(16/k)`, `c′ = 0`), and
  `r7ExtremalRemaining_of_construction`: that existence from Theorem 1.4's staged-history construction input.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`
(`Theorem14.StagedHistoryConstructionStatement` appears only as a hypothesis of the last corollary).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Function
open LQGMetric (DistOn IsZeroBoundaryGFF)
open QuantumZipper (H Hbar chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R7Leaves

open R7Outer Sec5.Prop55Half WangWu WholeField Lemma71C Lemma71I PocketCoord PocketJordan PocketMarks
  PocketWordAssembly PocketSeedOpen PocketStopField PocketStopWallsFin PocketStopWalls PocketCoupling
  StripPocketConfig PocketWordPerQ PocketStop R7Aux131 R7Pocket RefWire
open Exist.Staged (IsRegularDriver)
open Theorem14.StagedReg (regHist regHist_snd isRegularDriver_regHist regularize_eq_of_lt)

/-! ### The constant-angle program of a strip system is regular -/

section Const

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The driver of `η_θ` is regular almost surely** (as `StripPocketVersions.ae_regular_leftExtremal`, at a general
angle `θ ∈ [−π/2, π/2]`): infinite lifetime, `0` at `0`, continuous, with a transient generating trace. -/
theorem ae_regular_const (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    ∀ᵐ ω ∂P, (Es (constSpec θ) 0 ω).2 = ⊤ ∧ (Es (constSpec θ) 0 ω).1 0 = 0 ∧
      Continuous (Es (constSpec θ) 0 ω).1 ∧ ∃ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (Es (constSpec θ) 0 ω).1 ⊤ η ∧ Tendsto (fun t => ‖η t‖) atTop atTop := by
  have hE := isStagedHistory_const hS hθ
  obtain ⟨h', 𝓕, VL, VR, B, -, hC⟩ := isFlowLineDriver_const hS.kappa_pos hS.boundaryData hS.gff hE
  obtain ⟨hL0, hR0⟩ := heights_const hS.kappa_pos hS.kappa_lt_four hcumL hcumR hθ
  filter_upwards [ae_simple_trace_const hS.kappa_pos hS.kappa_lt_four hS.boundaryData hS.gff hE hL0 hR0,
    hC.1.2.2.2.2] with ω h1 hp
  obtain ⟨hζ, η, hη, -, -, htr⟩ := h1
  have hc : ContinuousOn (Es (constSpec θ) 0 ω).1 {t : ℝ≥0 | (t : ℝ≥0∞) < (Es (constSpec θ) 0 ω).2} :=
    hp.2.2.2.1
  rw [hζ] at hc
  exact ⟨hζ, hp.1, continuousOn_univ.1 (hc.mono fun t _ => ENNReal.coe_lt_top), η, hη, htr⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The only instruction of `constSpec θ` is the angle-`θ` piece run through its lifetime. -/
theorem eq_of_constSpec_getElem? {θ : ℝ} {k : ℕ} {θ' : ℝ} {t : ℝ≥0∞}
    (hk : (constSpec θ).2.2[k]? = some (Sum.inl (θ', t))) : k = 0 ∧ t = ⊤ := by
  rcases k with _ | n
  · simp only [constSpec, List.getElem?_cons_zero, Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at hk
    exact ⟨rfl, hk.2.symm⟩
  · simp [constSpec] at hk

/-- **`η_θ` is `StagedPiecesRegular`** (R51) for the strip system (its only piece is the stage-`0` flow line). -/
theorem stagedPiecesRegular_const (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    StagedPiecesRegular κ b jumps P (constSpec θ) (Es (constSpec θ)) := by
  filter_upwards [ae_regular_const hS hcumL hcumR hθ] with ω hω k θ' t c hk _
  obtain ⟨hζ, h0, hc, η, hη, htr⟩ := hω
  obtain ⟨rfl, rfl⟩ := eq_of_constSpec_getElem? hk
  rw [hζ, min_self]
  exact ⟨h0, hc.continuousOn, η, hη, fun _ => htr⟩

/-- **The regularized strip family is regular at every sample on `η_θ`**, with almost surely the original driver. -/
theorem regStrip_const (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {θ : ℝ} (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) :
    ∀ ω, IsRegularDriver (StripWall.regStrip κ b jumps P Es (constSpec θ) 0 ω) := by
  have e := StripWall.regStrip_of (stagedPiecesRegular_const hS hcumL hcumR hθ)
  exact fun ω => by rw [e]; exact isRegularDriver_regHist 0 ω

end Const

/-! ### A flow line is the trace of every flow-line driver of the same field and angle -/

/-- **Uniqueness of the flow-line driver** (R48-safe, through `AdmCode.admDrv`): for `(4.4)` heights at the angle
`θ`, a flow line `α` of the field `h` is almost surely the generating trace on `[0, ∞)` of every flow-line driver `W`
of `h` at the angle `θ`, and both lifetimes are infinite. -/
theorem ae_isGeneratingTrace_of_isFlowLine (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) {κ θ : ℝ}
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hL0 : ∀ y : ℝ, y < 0 → y ∉ jumps → b y + θ * chiC κ ≤ -sleLambda κ + π * chiC κ)
    (hR0 : ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + θ * chiC κ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {α : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ b jumps 0 θ P h α ζ) {W : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hW : IsFlowLineDriver κ b jumps θ P h W L) :
    ∀ᵐ ω ∂P, L ω = ⊤ ∧ ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (α ω) := by
  obtain ⟨c₀, hc₀J, hc₀⟩ := Restart.BoundaryWord.exists_fn_eq hb
  have h44c : Sec4.Cond44 κ (flowLineRhoL κ c₀.fn c₀.jumps 0 θ) (flowLineRhoR κ c₀.fn c₀.jumps 0 θ) := by
    refine StripDet.cond44_flowLine_of_heights hκ c₀.isPiecewiseConstantBoundaryData θ
      (fun y hy hyJ => ?_) (fun y hy hyJ => ?_)
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hL0 y hy hyJ
    · rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hR0 y hy hyJ
  obtain ⟨h', 𝓕, W₁, VL, VR, B, htr, hC, hgen⟩ := hfl
  have hE₁ : IsFlowLineDriver κ b jumps θ P h W₁ ζ := ⟨h', 𝓕, VL, VR, B, htr, hC⟩
  have hcongr := fun {W₀ : ℝ≥0 → Ω → ℝ} {L₀ : Ω → ℝ≥0∞} =>
    (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn (κ := κ) (θ := θ) (P := P) (h := h) (W := W₀) (ζ := L₀) hb
      c₀.isPiecewiseConstantBoundaryData jumps (fun y hy => hc₀ y hy)).2
  filter_upwards [AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 θ c₀ h44c (hcongr hE₁),
    AdmCode.ae_admDrv_eq_of_isFlowLineDriver h44 hκ hκ4 θ c₀ h44c (hcongr hW), hgen] with ω h1 h2 h3
  refine ⟨h2.1, h1.1, ?_⟩
  have hWW : (fun t => W t ω) = fun t => W₁ t ω := funext fun t => by
    rw [← h2.2.2 t (by rw [h2.1]; exact ENNReal.coe_lt_top), h1.2.2 t (by rw [h1.1]; exact ENNReal.coe_lt_top)]
  rw [hWW, ← h1.1]
  simpa only [Complex.ofReal_zero, sub_zero] using h3

/-! ### Aux. lemma 37's attachments for the arms of a configuration carrying a strip system -/

section Attach

variable {k rL rR c c' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
  {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}

/-- **Aux. lemma 37's attachment constancy for the extremal R.7 pocket** (both shapes): for versions `R`, `L`, `η` of
the arms `α_R`, `α_L` and of the counterflow's trace of an R.7 configuration whose field and counterflow also carry a
strip system (strip heights `hcumL`, `hcumR`), the rational first exits imply the `attach` and `attachInf` inputs of
`R7ExtremalInputs` (`Aux37Walls.hwit_r7`, `hwitI_r7` on the regularized strip family, whose constant-angle walls are
the arms by `ae_isGeneratingTrace_of_isFlowLine`; then `StripPocketPath.attachmentConstancy(Inf)_of_noWitness`). -/
theorem r7Attach_of_stripSystem (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) (hk4 : 4 < k) (hL : -2 < rL)
    (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4) (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ ({0} : Finset ℝ) →
      prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k) ≤ -sleLambda (16 / k))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ ({0} : Finset ℝ) →
      sleLambda (16 / k) ≤ prop74Data (r7A k rR + c) (r7B k rL + c') y + a * chiC (16 / k))
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η)
    (hfirstR : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (StripSys.rt q))) (negInv (R ω (StripSys.rt q))))
    (hfirstL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (L ω '' Ioc 0 (StripSys.rt q))) (negInv (L ω (StripSys.rt q)))) :
    (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      Sec6.AttachmentConstancy (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcR (R ω) (L ω) (StripSys.rt q)) (cfArcL (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) (StripSys.rt q) 0))) ∧
    (∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
      rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      Sec6.AttachmentConstancyInf (η ω) (cfPocket (R ω) (L ω) (StripSys.rt q))
        (cfArcRInf (R ω) (L ω) (StripSys.rt q)) (cfArcLInf (R ω) (L ω) (StripSys.rt q))
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) (StripSys.rt q) 0))) := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hb := isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')
  obtain ⟨-, hθ1, hθ2, hθ3⟩ := aux131_angles_of_max_eq hk4 hL hR hmax
  have hθR : R7.thetaR k rL ∈ Ico (-(π / 2)) (π / 2) := ⟨hθ1, hθ2.trans_le hθ3⟩
  have hθL : R7.thetaL k rR ∈ Ioc (-(π / 2)) (π / 2) := ⟨hθ1.trans_lt hθ2, hθ3⟩
  have hθRc : R7.thetaR k rL ∈ Icc (-(π / 2)) (π / 2) := Ico_subset_Icc_self hθR
  have hθLc : R7.thetaL k rR ∈ Icc (-(π / 2)) (π / 2) := Ioc_subset_Icc_self hθL
  have hS' := StripWall.isStripSystem_regStrip hS
  have hregR := regStrip_const hS hcumL hcumR hθRc
  have hregL := regStrip_const hS hcumL hcumR hθLc
  -- the arms are the constant-angle walls of the regularized strip family
  have hflR : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaR k rL) P h R ζαR :=
    IsFlowLine.congr_path hcfg.flow_αR (hV.R_ae.mono fun ω hω t _ => by rw [hω])
  have hflL : IsFlowLine (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} 0 (R7.thetaL k rR) P h L ζαL :=
    IsFlowLine.congr_path hcfg.flow_αL (hV.L_ae.mono fun ω hω t _ => by rw [hω])
  obtain ⟨hL0R, hR0R⟩ := heights_const hκ hκ4 hcumL hcumR hθRc
  obtain ⟨hL0L, hR0L⟩ := heights_const hκ hκ4 hcumL hcumR hθLc
  have hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace
      (StripWall.regStrip (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} P Es
        (constSpec (R7.thetaR k rL)) 0 ω).1 ⊤ (R ω) :=
    (ae_isGeneratingTrace_of_isFlowLine h44 hκ hκ4 hb hL0R hR0R hflR (isFlowLineDriver_const hκ hb hcfg.gff
      (isStagedHistory_const hS' hθRc))).mono fun ω hω => hω.2.2
  have hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace
      (StripWall.regStrip (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} P Es
        (constSpec (R7.thetaL k rR)) 0 ω).1 ⊤ (L ω) :=
    (ae_isGeneratingTrace_of_isFlowLine h44 hκ hκ4 hb hL0L hR0L hflL (isFlowLineDriver_const hκ hb hcfg.gff
      (isStagedHistory_const hS' hθLc))).mono fun ω hω => hω.2.2
  -- the walls' visits and order
  have hreg := hcfg.regular
  have hRs : ∀ᵐ ω ∂P, IsSimpleProper (R ω) := by
    filter_upwards [hreg, hV.R_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.1
  have hLs : ∀ᵐ ω ∂P, IsSimpleProper (L ω) := by
    filter_upwards [hreg, hV.L_ae] with ω hω he
    rw [he]; exact R7Outer.IsSeedProper.isSimpleProper hω.2.2.2.1
  have hwR := WallsPath.ae_walls_of_simpleProper_rat_firstHit hRs hV.η_cont hfirstR
  have hwL := WallsPath.ae_walls_of_simpleProper_rat_firstHit hLs hV.η_cont hfirstL
  have hwalls : ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) ∧
      IsWallReverseVisit (L ω) (η ω) ∧ IsWallVisited (L ω) (η ω) := by
    filter_upwards [hwR, hwL] with ω h1 h2 using ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hord : ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))) := by
    filter_upwards [hcfg.order, hRs, hLs, hV.R_ae, hV.L_ae] with ω hω hRω hLω hRe hLe
    have hsub : range (L ω) ⊆ closedLeftSide (R ω) := by rw [hRe, hLe]; exact hω.2.1
    exact Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide hLω hRω hsub
  have hwit := Aux37Walls.hwit_r7 h44 hS' hcumL hcumR hθR hθL hregR hregL hV.R_cont hV.R_zero hV.R_meas hRtr
    hV.L_cont hV.L_zero hV.L_meas hLtr hV.η_trace hwalls hord
  have hwitI := Aux37Walls.hwitI_r7 h44 hS' hcumL hcumR hθR hθL hregR hregL hV.R_cont hV.R_zero hV.R_meas hRtr
    hV.L_cont hV.L_zero hV.L_meas hLtr hV.η_trace hwalls hord
  have htrace := ae_isLoewnerTrace_counterflow_r7 hk4 hc hc' hcfg.gff hcfg.counterflow hV.η_trace
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
        0 < rightLo (R ω) (L ω) (StripSys.rt q) →
          ¬ StripPocketPath.IsPocketWitness (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwit q hq
    filter_upwards [htrace, hwalls, hw] with ω htr hwl hwω hconf hpos
    exact StripPocketPath.attachmentConstancy_of_noWitness hconf hpos htr.1 htr.2.1 (by simpa using htr.2.2) hwl.1
      hwl.2.2.1 hwl.2.1 fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf hpos
  · have hw : ∀ᵐ ω ∂P, ∀ s₁ s₂ v v₁ v₂ : ℚ, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q) →
        rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
          ¬ StripPocketPath.IsPocketWitnessInf (R ω) (L ω) (StripSys.rt q) (η ω) s₁ s₂ v v₁ v₂ := by
      simp only [ae_all_iff]
      exact hwitI q hq
    filter_upwards [htrace, hwalls, hw] with ω htr hwl hwω hconf h0
    exact StripPocketPath.attachmentConstancyInf_of_noWitness hconf h0 htr.1 htr.2.1 (by simpa using htr.2.2)
      hwl.1 hwl.2.2.1 hwl.2.1 hwl.2.2.2 fun s₁ s₂ v v₁ v₂ => hwω s₁ s₂ v v₁ v₂ hconf h0

end Attach

/-! ### The extremal remaining inputs with the attachments from strip systems -/

section Remaining

/-- **Strip heights of the R.7 data at `c = πχ(16/k)`, `c′ = 0`** (the cumulative heights `hcumL`, `hcumR` of a strip
system at every angle of `[−π/2, π/2]`): on `ℝ₋` the data is `−λ − max(θ_L, π/2)χ`, on `ℝ₊` it is
`λ − min(θ_R, −π/2)χ`. -/
theorem r7_strip_heights {k rL rR : ℝ} (hk4 : 4 < k) :
    (∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ ({0} : Finset ℝ) →
      prop74Data (r7A k rR + π * chiC (16 / k)) (r7B k rL + 0) y + a * chiC (16 / k) ≤ -sleLambda (16 / k)) ∧
    ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ ({0} : Finset ℝ) →
      sleLambda (16 / k) ≤ prop74Data (r7A k rR + π * chiC (16 / k)) (r7B k rL + 0) y + a * chiC (16 / k) := by
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

/-- **A strip system on every R.7 configuration** (heights `c`, `c′`): the field and the centred counterflow of every
configuration carry the staged histories of a strip system (`StripSys.IsStripSystem` at `16/k`). -/
def R7StripOnConfig (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∃ Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      StripSys.IsStripSystem (16 / k) (prop74Data (r7A k rR + c) (r7B k rL + c')) {0} P h W' ζ' Es

/-- **The core remaining inputs** (the `R7ExtremalInputs` other than Aux. lemma 37's attachments) on versions `R`,
`L`, `η`: the rational first exits, the two-seed side limits and Proposition 5.13 for the counterflow. -/
structure R7ExtremalCore (k rL rR : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (h'' : Ω → DistOn upperHalfPlaneOpens) (u₀' : ℂ → ℝ) (R L : Ω → ℝ≥0 → ℂ)
    (η : Ω → ℝ → ℂ) : Prop where
  firstR : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
    Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (StripSys.rt q))) (negInv (R ω (StripSys.rt q)))
  firstL : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
    Sec4.IsFirstHitPoint (η ω) T (negInv '' (L ω '' Ioc 0 (StripSys.rt q))) (negInv (L ω (StripSys.rt q)))
  side : ∀ q : ℚ, 0 < q → ∀ G : Set Ω, MeasurableSet[wallsSigma P R L] G → 0 < P G →
    (∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) (StripSys.rt q)) →
    (∀ ω ∈ G, ζ' ω = ⊤) →
    (∀ ω ∈ G, 0 < rightLo (R ω) (L ω) (StripSys.rt q) →
      IsCfPocketConfig (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    (∀ ω ∈ G, rightLo (R ω) (L ω) (StripSys.rt q) = 0 →
      IsCfPocketConfigInf (R ω) (L ω) (StripSys.rt q) (fun s : ℝ => W' s.toNNReal ω) (η ω)) →
    TwoSeedSideInput k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀' ∧
      TwoSeedSideInputInf k rL rR (wallsSigma P R L) P R L (StripSys.rt q) η
        {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) (StripSys.rt q)} (centredField h'' u₀') u₀'
  det : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h'' inferInstance]
    fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t

/-- **The core remaining inputs on every configuration** (heights `c`, `c′`), as in `R7ExtremalRemaining`. -/
def R7ExtremalCoreRemaining (k rL rR c c' : ℝ) : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' h'' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), IsCfDecomp k P h W' ζ' b' J' h' h'' 𝓕 VL VR B →
    ∀ u₀' : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData k (flowLineRhoL k b' J' 0 0)
      (flowLineRhoR k b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀' →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
      R7ExtremalCore k rL rR P W' ζ' h'' u₀' R L η

/-- **The extremal remaining inputs from the core inputs and strip systems** (heights `c = πχ(16/k)`, `c′ = 0`):
Aux. lemma 37's attachments are `r7Attach_of_stripSystem`. -/
theorem r7ExtremalRemaining_of_strip (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) {k rL rR : ℝ}
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR) (hmax : max rL rR = k / 2 - 4)
    (hcore : R7ExtremalCoreRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hstrip : R7StripOnConfig.{u} k rL rR (π * chiC (16 / k)) 0) :
    R7ExtremalRemaining.{u} k rL rR := by
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  have hc : 0 ≤ π * chiC (16 / k) := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hκ hκ4).le
  obtain ⟨hcumL, hcumR⟩ := r7_strip_heights (rL := rL) (rR := rR) hk4
  refine ⟨π * chiC (16 / k), 0, hc, le_rfl, ?_⟩
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  have hC := hcore P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV
  obtain ⟨Es, hS⟩ := hstrip P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
  obtain ⟨hat, hatI⟩ := r7Attach_of_stripSystem h44 hk4 hL hR hmax hc le_rfl hcfg hS hcumL hcumR hV hC.firstR
    hC.firstL
  exact ⟨hC.firstR, hC.firstL, hat, hatI, hC.side, hC.det⟩

/-- **A strip system on every R.7 configuration from Theorem 1.4's staged-history construction input**
(`StripSys.exists_isStripSystem_of_construction`; the counterflow's infinite lifetime is `ae_counterflow_trace_r7`). -/
theorem r7StripOnConfig_of_construction (hCon : Theorem14.StagedHistoryConstructionStatement.{u}) {k rL rR c c' : ℝ}
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') : R7StripOnConfig.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
  have hκ : 0 < 16 / k := R7.sixteen_div_pos (by linarith)
  have hκ4 : 16 / k < 4 := R7.sixteen_div_lt_four hk4
  exact StripSys.exists_isStripSystem_of_construction hCon hκ hκ4
    (isPiecewiseConstant_prop74Data (r7A k rR + c) (r7B k rL + c')) hcfg.gff hcfg.counterflow
    ((ae_counterflow_trace_r7 hk4 hc hc' hcfg.gff hcfg.counterflow).mono fun ω hω => hω.1)

end Remaining

end InteractingSLE.Sec7.R7Leaves
