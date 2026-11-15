/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.RestartGenFirstHit
import InteractingSLE.Spec.Sec5.CrossCondTheta
import InteractingSLE.Spec.Sec5.CfLineRegQ
import InteractingSLE.Spec.Sec7.R7OuterAvoid

/-!
# The restart law for one flow-line piece, on the space of the field (the one-angle case)

Packet PROVE-RESTART-GEN. Lemma 4.7 (specification p. 118; Remark 4.8 (c), "the first-exit conditional law in the
remaining component") is proved in the chart `Q` on the **glued space** of `Prop411Q.CfGlueAE` (the flow line and a
counterflow sample, conditionally independent given the field): `Prop411Q.Lemma47QHitStatement` (PROVE-CFRESTART…5).
Its consumers (Lemma 5.7's reverse visits, the pocket walls of Aux. 130, the R.7 walls, Proposition 5.13's tree)
work instead on **one probability space carrying the field `h`, a flow line of `h` and a centred counterflow of `h`**
(the strip-system frame `Sec7.StripSys`). This file transfers Lemma 4.7's first contact to that frame, for a flow line
of `h` at any angle `θ` whose (4.4) heights hold, given Lemma 4.7 on the glued space at relative angle `θ`:

* `Lemma47QHitTStatement θ`: Lemma 4.7's first contact in the chart `Q` on the glued space of the counterflow of
  `h − θχ` (`CrossCond.Theta.CfGlueAET θ`); at `θ = π/2` it is the landed named input
  (`lemma47QHitTStatement_pi_div_two`);
* `cfFieldT_flowField`: the counterflow field at relative angle `θ` of the coupling field `h + θχ` of an angle-`θ`
  flow line is `h` itself;
* **`ae_isFirstHitQ_of_isFlowLine`**: on any probability space carrying a GFF `h` (data `b`, (4.4) heights at `θ`), a
  centred counterflow of `h` with infinite lifetime and trace `η`, and the angle-`θ` flow line `β` of `h`: almost surely
  the counterflow `R ∘ η` first contacts `β((0, q])` at `β(q)` (`IsFirstHitQ`), at every positive rational `q`.

The transfer: the flow line is a Borel function of the field (Lemma 7.5 in the non-boundary regime, from the §4.2
reference), the counterflow history has a regular conditional law given the field, so the glued space has the joint
law of (flow line, counterflow history) (`R7Outer.ae_of_glue`); the first contact is a Borel event of the two paths
on good histories (`RestartGenFirstHit`). R48: the inputs are Lemma 4.7 on the glued space and the §4.2 reference;
nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.RestartGen

open WangWu (negInv glueMeasure histLine)
open Prop411Q (IsFirstHitQ)
open Cond44Ref (cfHistory)
open CrossCond.Theta (CfGlueAET CfThetaBounds cfFieldT measurable_cfFieldT)
open CfRegQ (goodCfSet measurableSet_goodCfSet hDrv)
open Sec7.R7Outer (exists_flowLineMap_of_heights cond44_of_heights hasAdmissiblePartialSums_of_heights)
open Sec7.StripHeights44 (IsHeightBounded44)
open Sec5.Prop55Half (IsSeedProper)

/-! ### Lemma 4.7 on the glued space at relative angle `θ` -/

/-- **Lemma 4.7 in the chart `Q` at relative angle `θ`** (glued space of `CfGlueAET θ`: the flow line of `h` and the
counterflow of `h − θχ`, conditionally independent given `h`): at every positive rational flow time `q` the
counterflow first contacts the flow line's prefix `η((0, q])` at `η(q)`. At `θ = π/2` this is
`Prop411Q.Lemma47QHitStatement` (`lemma47QHitTStatement_pi_div_two`). -/
def Lemma47QHitTStatement (θ : ℝ) : Prop :=
  ∀ q : ℚ, 0 < q → CfGlueAET.{u} θ fun η y => IsFirstHitQ η (histLine y) q

/-- At relative angle `π/2`, Lemma 4.7 at relative angle `θ` is the landed named input (the extra admissibility
hypothesis of the `θ`-setting is not used). -/
theorem lemma47QHitTStatement_pi_div_two (h47 : Prop411Q.Lemma47QHitStatement.{u}) :
    Lemma47QHitTStatement.{u} (π / 2) := by
  intro q hq κ hκ hκ4 nL nR xL xR ρL ρR hF h44 _ Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  exact h47 q hq κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk

/-- The counterflow field at relative angle `θ` of `h + θχ` is `h`. -/
theorem cfFieldT_flowField (κ θ : ℝ) (f : DistOn upperHalfPlaneOpens) :
    cfFieldT κ θ (Exist.flowField 0 (θ * chiC κ) f) = f := by
  rw [cfFieldT, GlueCond.flowField_zero_flowField_zero, neg_add_cancel, GlueCond.flowField_zero_zero]

/-- The admissibility hypothesis of the `θ`-setting at `θ = π/2` from the (4.4) heights at `π/2`. -/
theorem cfThetaBounds_pi_div_two_of_heights {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J (π / 2)) :
    CfThetaBounds κ (π / 2) (flowLineRhoL κ b J 0 (π / 2)) (flowLineRhoR κ b J 0 (π / 2)) (flowLineXL b J 0)
      (flowLineXR b J 0) :=
  CrossCond.Theta.cfThetaBounds_of_cond44 hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b J 0)
    (cond44_of_heights hκ hb hθ)

/-! ### The admissibility of the counterflow at every relative angle -/

open Finset in
/-- Splitting off the seed term of a `Fin.cons` word in a filtered sum whose filter contains the seed. -/
theorem sum_filter_cons_eq {n : ℕ} (s s' : ℝ) (f : Fin n → ℝ) (p : Fin (n + 1) → Prop) [DecidablePred p]
    (h0 : p 0) : ∑ i ∈ univ.filter p, (Fin.cons s f : Fin (n + 1) → ℝ) i =
      ∑ i ∈ univ.filter p, (Fin.cons s' f : Fin (n + 1) → ℝ) i + (s - s') := by
  rw [sum_filter, sum_filter, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, h0, ite_true]
  ring

/-- **Changing the two seed weights of a word with seeds at `0` shifts its force boundary data by a constant**:
`ρL₀ ↦ ρL₀ − c/λ`, `ρR₀ ↦ ρR₀ + c/λ` adds `c` on both sides. -/
theorem forceBoundaryData_cons_shift {κ : ℝ} (hκ : 0 < κ) {n m : ℕ} (sL sL' : ℝ) (fL gL : Fin n → ℝ)
    (sR sR' : ℝ) (fR gR : Fin m → ℝ) (c : ℝ) (hL : sL = sL' - c / sleLambda κ)
    (hR : sR = sR' + c / sleLambda κ) (x : ℝ) :
    forceBoundaryData κ (Fin.cons sL fL : Fin (n + 1) → ℝ) (Fin.cons sR fR : Fin (m + 1) → ℝ)
      (Fin.cons 0 gL : Fin (n + 1) → ℝ) (Fin.cons 0 gR : Fin (m + 1) → ℝ) x =
    forceBoundaryData κ (Fin.cons sL' fL : Fin (n + 1) → ℝ) (Fin.cons sR' fR : Fin (m + 1) → ℝ)
      (Fin.cons 0 gL : Fin (n + 1) → ℝ) (Fin.cons 0 gR : Fin (m + 1) → ℝ) x + c := by
  have hΛ : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  rcases lt_or_ge x 0 with hx | hx
  · rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hx, Sec4.forceBoundaryData_of_neg _ _ _ _ hx,
      sum_filter_cons_eq sL sL' fL _ (by simpa using hx), hL]
    field_simp
    ring
  · rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ hx, Sec4.forceBoundaryData_of_nonneg _ _ _ _ hx,
      sum_filter_cons_eq sR sR' fR _ (by simpa using hx), hR]
    field_simp
    ring

/-- **The angle enters the flow-line word only through its seed weights**: the force boundary data of the
angle-`θ` flow-line word from `0` is that of the angle-`θ′` word plus `(θ − θ′)χ`. -/
theorem forceBoundaryData_flowLine_angle {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (J : Finset ℝ) (θ θ' x : ℝ) :
    forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0) x =
      forceBoundaryData κ (flowLineRhoL κ b J 0 θ') (flowLineRhoR κ b J 0 θ') (flowLineXL b J 0)
        (flowLineXR b J 0) x + (θ - θ') * chiC κ :=
  forceBoundaryData_cons_shift hκ _ _ _ _ _ _ _ _ _ (by ring) (by ring) x

/-- **The counterflow of `h` is admissible at every relative angle** once it is at one: `CfThetaBounds` for the
angle-`θ` flow-line word does not depend on `θ` (the shift `θχ` of the word cancels the shift `−θχ` of the field). -/
theorem cfThetaBounds_angle {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ} {θ' : ℝ}
    (h : CfThetaBounds κ θ' (flowLineRhoL κ b J 0 θ') (flowLineRhoR κ b J 0 θ') (flowLineXL b J 0)
      (flowLineXR b J 0)) (θ : ℝ) :
    CfThetaBounds κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := h.1 x hx
    rw [forceBoundaryData_flowLine_angle hκ b J θ θ' x]
    linarith
  · have := h.2 x hx
    rw [forceBoundaryData_flowLine_angle hκ b J θ θ' x]
    linarith

/-- The admissibility hypothesis of the `θ`-setting at every `θ`, from the (4.4) heights at `π/2`. -/
theorem cfThetaBounds_of_heights {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J (π / 2)) (θ : ℝ) :
    CfThetaBounds κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0) :=
  cfThetaBounds_angle hκ (cfThetaBounds_pi_div_two_of_heights hκ hκ4 hb hθ) θ

/-! ### The transfer to the space of the field -/

/-- The curve read from a good counterflow history is continuous. -/
theorem continuous_histLine_of_mem_goodCfSet {y : LawUnique.HistorySpace 0 0} (hy : y ∈ goodCfSet) :
    Continuous (histLine y) := by
  rw [CfRegQ.histLine_eq_traceAt]
  exact (CfLineRegQ.continuous_traceAt_of_mem_goodCfSet hy).comp continuous_real_toNNReal

/-- A seed-proper curve read on `ℝ` is continuous and nonzero at positive times. -/
theorem realPath_regular {γ : ℝ≥0 → ℂ} (hγ : IsSeedProper γ) (q : ℚ) :
    ContinuousOn (Sec7.Lemma71I.realPath γ) (Ioc 0 q) ∧
      ∀ s ∈ Ioc (0 : ℝ) q, Sec7.Lemma71I.realPath γ s ≠ 0 := by
  refine ⟨(hγ.1.comp continuous_real_toNNReal).continuousOn, fun s hs => ?_⟩
  have hpos : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
  have hH := hγ.2.2.2.1 _ hpos
  intro h0
  have h0' : γ s.toNNReal = 0 := h0
  rw [h0'] at hH
  exact absurd hH (by simp [H])

/-- **Lemma 4.7's first contact for an angle-`θ` flow line, on the space of the field** (the one-angle case of the
restart law; specification p. 118 and Remark 4.8 (c)). Let `0 < κ < 4`, let `h` be a GFF on `ℍ` with piecewise
constant data `b` satisfying the (4.4) heights at the angle `θ` and the admissibility of the counterflow of `h`
(`CfThetaBounds`), let `W′` be a centred counterflow driver of `h` (frozen `IsCenteredCounterflowDriver`) with almost
surely infinite lifetime and continuous generating trace `η` (chart `R`), and let `β` be the angle-`θ` flow line of
`h` from `0` (frozen `IsFlowLine`). Given Lemma 4.7 on the glued space at relative angle `θ` and the §4.2 reference,
almost surely the counterflow `R ∘ η` first contacts `β((0, q])` at `β(q)`. -/
theorem ae_isFirstHitQ_of_isFlowLine {θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J θ)
    (hθb : CfThetaBounds κ θ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0)
      (flowLineXR b J 0))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 θ P h β ζ) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (β ω)) (fun s : ℝ => η ω s.toNNReal) q := by
  have hreg := Sec7.R7Outer.IsFlowLine.ae_regular_of_heights hκ hκ4 hb hθ hβ
  obtain ⟨Φ, hΦm, hΦ⟩ := exists_flowLineMap_of_heights href hκ hκ4 hb hθ
  have hΦβ := hΦ P h hh β ζ hβ
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hC, hgen⟩ := hβ
  have hF := Theorem15.isOrderedForceWord_flowLine b J 0
  have h44 := cond44_of_heights hκ hb hθ
  have hadm := hasAdmissiblePartialSums_of_heights hκ hκ4 hb hθ
  have hXe : (fun ω => cfFieldT κ θ (h' ω)) = h := funext fun ω => by
    rw [Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htr ω)]
    exact cfFieldT_flowField κ θ (h ω)
  have hXm : Measurable fun ω => cfFieldT κ θ (h' ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hYm := Cond44Ref.measurable_cfHistory (Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)
  set k := condDistrib (cfHistory W' ζ') h P with hkdef
  have hk : P.map (fun ω => (h ω, cfHistory W' ζ' ω)) = P.map h ⊗ₘ k :=
    (compProd_map_condDistrib hh.1.aemeasurable hYm.aemeasurable).symm
  have hlaw : P.map (fun ω => cfFieldT κ θ (h' ω)) = P.map h := by rw [hXe]
  have hglue := h47 q hq κ hκ hκ4 _ _ _ _ hF h44 hθb P 𝓕 W VL VR B ζ h' hC P h W' ζ' hcf hlaw k hk
  have hk' : P.map (fun ω => ((fun ω => cfFieldT κ θ (h' ω)) ω, cfHistory W' ζ' ω)) =
      P.map (fun ω => cfFieldT κ θ (h' ω)) ⊗ₘ k := by
    have e2 : (fun ω => (cfFieldT κ θ (h' ω), cfHistory W' ζ' ω)) = fun ω => (h ω, cfHistory W' ζ' ω) :=
      funext fun ω => by rw [show cfFieldT κ θ (h' ω) = h ω from congrFun hXe ω]
    rw [e2, hXe]
    exact hk
  set G : DistOn upperHalfPlaneOpens → ℝ → ℂ := fun f s => (Φ f).2 s.toNNReal with hGdef
  have hGm : Measurable G :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply _).comp (measurable_snd.comp hΦm)
  have hline := Cond44Ref.ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  -- the flow line is the seed line, a Borel function of the field, and seed-proper
  have hDG : ∀ᵐ ω ∂P, WangWu.seedLine ζ W ω = G (cfFieldT κ θ (h' ω)) ∧
      WangWu.seedLine ζ W ω = Sec7.Lemma71I.realPath (β ω) ∧ IsSeedProper (β ω) := by
    filter_upwards [hline, hgen, hΦβ, hC.1.2.2.2.2, hreg] with ω hl hg hΦω hpath hr
    obtain ⟨hζ, -, -⟩ := hl
    obtain ⟨hw0, -, -, hcw, -⟩ := hpath
    have hg' : IsGeneratingTrace (fun t => W t ω) (ζ ω) (β ω) := by
      have e : (fun t => β ω t - ((0 : ℝ) : ℂ)) = β ω := funext fun t => by simp
      rw [← e]
      exact hg
    have hsl : WangWu.seedLine ζ W ω = fun s : ℝ => β ω s.toNNReal := by
      funext s
      simp only [WangWu.seedLine]
      have hk : (fun t => InteractingSLE.killedProc ζ W t ω) = fun t => W t ω :=
        funext (InteractingSLE.killedProc_of_eq_top hζ)
      rw [hk]
      exact LP.traceAt_eq_of_isGeneratingTrace hg' hcw hw0 (by rw [hζ]; exact ENNReal.coe_lt_top)
    refine ⟨?_, hsl, hr.2⟩
    rw [hsl, show cfFieldT κ θ (h' ω) = h ω from congrFun hXe ω]
    funext s
    simp only [hGdef]
    exact (hΦω.2 _ (by rw [hζ]; exact le_top)).symm
  -- the Borel event: a bad history, or the first-contact code
  set S : Set ((ℝ → ℂ) × LawUnique.HistorySpace 0 0) :=
    {p | p.2 ∉ goodCfSet ∨ FirstHitCode q p.1 (histLine p.2)} with hSdef
  have hS : MeasurableSet S := by
    have h1 : MeasurableSet {p : (ℝ → ℂ) × LawUnique.HistorySpace 0 0 | p.2 ∉ goodCfSet} :=
      (measurable_snd measurableSet_goodCfSet).compl
    have h2 := measurableSet_firstHitCode (γ := fun p : (ℝ → ℂ) × LawUnique.HistorySpace 0 0 => p.1)
      (β := fun p => histLine p.2) (fun s => (measurable_pi_apply s).comp measurable_fst)
      (fun s => (WangWu.measurable_histLine s).comp measurable_snd) q
    exact h1.union h2
  have hglueS : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h' ω)) hXm),
      (WangWu.seedLine ζ W p.1, p.2) ∈ S := by
    filter_upwards [hglue, WangWu.ae_glue_fst (μ := P) k hXm hDG] with p hp hd
    by_cases hy : p.2 ∈ goodCfSet
    · right
      have hγ := realPath_regular hd.2.2 q
      rw [hd.2.1] at hp ⊢
      exact firstHitCode_of_isFirstHitQ (continuous_histLine_of_mem_goodCfSet hy) hq hγ.1 hγ.2 hp
    · exact Or.inl hy
  have htrans := Sec7.R7Outer.ae_of_glue hXm hYm k hk' hGm (hDG.mono fun ω hω => hω.1) hS hglueS
  have hpathW : ∀ᵐ ω ∂P, W' 0 ω = 0 ∧ ContinuousOn (fun t => W' t ω) {t | (t : ℝ≥0∞) < ζ' ω} := by
    obtain ⟨b', J', g, -, -, hd⟩ := hcf
    obtain ⟨g', 𝓕', VL', VR', B', -, hC'⟩ := hd
    filter_upwards [hC'.1.2.2.2.2] with ω hp
    exact ⟨hp.1, hp.2.2.2.1⟩
  filter_upwards [htrans, hDG, hζ', hη, hpathW] with ω hS' hd hζ hηω hpω
  have hw : Continuous fun t => W' t ω := by
    have := hpω.2
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  have hgood : cfHistory W' ζ' ω ∈ goodCfSet := CfRegQ.cfHistory_mem_goodCfSet hζ hw hpω.1 hηω
  have hcode : FirstHitCode q (WangWu.seedLine ζ W ω) (histLine (cfHistory W' ζ' ω)) :=
    hS'.resolve_left (not_not.2 hgood)
  have hηc : Continuous (η ω) :=
    continuousOn_univ.1 (hηω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hhl : histLine (cfHistory W' ζ' ω) = fun s : ℝ => η ω s.toNNReal := by
    rw [CfRegQ.histLine_eq_traceAt, GlueCond.hDrv_cfHistory hζ hw]
    funext s
    exact LP.traceAt_eq_of_isGeneratingTrace hηω hw.continuousOn hpω.1 ENNReal.coe_lt_top
  rw [hd.2.1, hhl] at hcode
  have hγ := realPath_regular hd.2.2 q
  refine isFirstHitQ_of_firstHitCode (hηc.comp continuous_real_toNNReal) ?_ hq hγ.1 hγ.2 hcode
  show η ω (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero]
  exact hηω.1

/-- **The angle-`π/2` case from the landed Lemma 4.7** (the left boundary of the counterflow,
`Sec7.StripSys.leftExtremalSpec`): Lemma 4.7's first contact on the space of the field for the angle-`π/2` flow line
of `h`, from `Prop411Q.Lemma47QHitStatement` and the §4.2 reference. -/
theorem ae_isFirstHitQ_of_isFlowLine_pi_div_two (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J (π / 2))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 (π / 2) P h β ζ) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (β ω)) (fun s : ℝ => η ω s.toNNReal) q :=
  ae_isFirstHitQ_of_isFlowLine (lemma47QHitTStatement_pi_div_two h47) href hκ hκ4 hb hθ
    (cfThetaBounds_pi_div_two_of_heights hκ hκ4 hb hθ) hh hcf hζ' hη hβ q hq

/-- **The one-angle restart law with the admissibility discharged**: as `ae_isFirstHitQ_of_isFlowLine`, with
`CfThetaBounds` from the (4.4) heights at `π/2` (which, with the heights at `θ`, are the strip system's height
choice at the two angles). -/
theorem ae_isFirstHitQ_of_isFlowLine_heights {θ : ℝ} (h47 : Lemma47QHitTStatement.{u} θ)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ}
    {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (hθ : IsHeightBounded44 κ b J θ)
    (hπ : IsHeightBounded44 κ b J (π / 2))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω)) {β : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hβ : IsFlowLine κ b J 0 θ P h β ζ) (q : ℚ) (hq : 0 < q) :
    ∀ᵐ ω ∂P, IsFirstHitQ (Sec7.Lemma71I.realPath (β ω)) (fun s : ℝ => η ω s.toNNReal) q :=
  ae_isFirstHitQ_of_isFlowLine h47 href hκ hκ4 hb hθ (cfThetaBounds_of_heights hκ hκ4 hb hπ θ) hh hcf hζ' hη hβ q hq

end InteractingSLE.Sec5.RestartGen
