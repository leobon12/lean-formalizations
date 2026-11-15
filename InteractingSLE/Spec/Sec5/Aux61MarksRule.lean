/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ULocWire
import InteractingSLE.Spec.Sec5.Aux61NestRule
import InteractingSLE.Spec.Sec7.Lemma72CLocal
import InteractingSLE.Spec.Coupling.WholeField2Kernel

/-!
# The marked local sets at the glued stop: rule marks, nesting and locality

Packet PROVE-AUX61-MARKS. The physical marked local sets of Aux. lemma 61 (Astra's follow-up 4 §1.1) at fibre time `r`
are read at the glued stop `T(r)` (the restart's physical time at relative capacity `r`). When the glued stop is a
measurable Galmarino rule `ρ` of (the counterflow record at `s`, the flow's killed history), the marks are UNIONLOC's
`ruleMarks` (the counterflow record at `s` and the flow history stopped at `T`). Here:

* the rule marks are sub-σ-algebras of the ambient one (`ruleMarks_le`) and are **nested** for ordered rules
  (NEST's `ruleMarks_mono`);
* **locality at the glued stop** (`isHistoryAvoidanceLocal_ruleSet_gluedQ`): at the binders of
  `Aux61UnionK.GluedLocalCoverOn`, for the flow line's own coupling `(W, V, ζ)` (given, not chosen) and every bounded
  harmonic extension `u₀` of its force data, every set `A` measurable for the rule marks (hitting σ-algebra) containing
  `ℍ ∩ (K_s ∪ K̃_T)` almost surely (`K_s` the counterflow hull at `s`, `K̃_T` the flow's Loewner hull at `T`) is
  history-marked local for the rule marks and the centred field `h + θ₂χ − u₀` — UNIONLOC's (P1)
  `isHistoryAvoidanceLocal_unionAt_rule_cfGlueT` and `Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set`;
* the centred field is a zero-boundary GFF on the glued space (`isZeroBoundaryGFF_glued`), and the flow line's coupling
  is exposed for the field `h + θ₂χ` (`exists_coupling_of_flowLine`).

R48 / R77: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or
Astra's post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc

/-! ### Rule marks -/

section Rule

variable {X 𝒴 γ : Type*} [mX : MeasurableSpace X] [m𝒴 : MeasurableSpace 𝒴] [mγ : MeasurableSpace γ]
  {stop : ℝ≥0 → γ → γ} {ρ : 𝒴 × γ → ℝ≥0∞} {Y₀ : X → 𝒴} {R₀ : X → γ}

/-- The retained record of a rule stop is measurable. -/
theorem measurable_ruleRecord (hstop : IsRecordStop stop) (hρ : Measurable ρ) (hY : Measurable Y₀)
    (hR : Measurable R₀) : Measurable fun x => (Y₀ x, stopAt stop (ρ (Y₀ x, R₀ x)) (R₀ x)) :=
  hY.prodMk ((measurable_stopAt hstop).comp ((hρ.comp (hY.prodMk hR)).prodMk hR))

/-- **The rule marks are sub-σ-algebras of the ambient one.** -/
theorem ruleMarks_le (hstop : IsRecordStop stop) (hρ : Measurable ρ) (hY : Measurable Y₀)
    (hR : Measurable R₀) : ruleMarks stop ρ Y₀ R₀ ≤ mX :=
  (measurable_ruleRecord hstop hρ hY hR).comap_le

omit mX in
/-- **A function of the retained record is measurable for the rule marks.** -/
theorem measurable_ruleMarks_of_factor {δ : Type*} [MeasurableSpace δ] {F : 𝒴 × γ → δ} (hF : Measurable F) :
    Measurable[ruleMarks stop ρ Y₀ R₀] fun x => F (Y₀ x, stopAt stop (ρ (Y₀ x, R₀ x)) (R₀ x)) :=
  hF.comp (comap_measurable _)

end Rule

/-! ### Locality at the glued stop -/

section Glued

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ WholeField LocalSets CrossCond.Theta Coupling
open Sec7.PocketStopWallsFin (regHull ae_regHull_eq)

/-- **The flow line's coupling for the field `h + θχ`** (the witnesses of `IsFlowLine`, with the translated field
identified with `Exist.flowField 0 (θχ) h`). -/
theorem exists_coupling_of_flowLine {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b jumps 0 θ P h η ζ) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (flowLineNL b jumps 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR b jumps 0) → ℝ≥0 → Ω → ℝ) (Bm : ℝ≥0 → Ω → ℝ),
      IsOptionalHullCoupling κ (flowLineXL b jumps 0) (flowLineXR b jumps 0) (flowLineRhoL κ b jumps 0 θ)
        (flowLineRhoR κ b jumps 0 θ) P 𝓕 W VL VR Bm ζ (fun ω => Exist.flowField 0 (θ * chiC κ) (h ω)) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - ((0 : ℝ) : ℂ)) := by
  obtain ⟨h', 𝓕, W, VL, VR, Bm, htrans, hC, htr⟩ := hfl
  have hh' : h' = fun ω => Exist.flowField 0 (θ * chiC κ) (h ω) :=
    funext fun ω => Lemma75Bridge.eq_flowField_of_isTranslateAddConst (htrans ω)
  subst hh'
  exact ⟨𝓕, W, VL, VR, Bm, hC, htr⟩

/-- **The centred field of the flow line's coupling is a zero-boundary GFF on the glued space.** -/
theorem isZeroBoundaryGFF_glued {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {Bm : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR Bm ζ h') {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {β : Type*} [MeasurableSpace β] (k : Kernel (DistOn upperHalfPlaneOpens) β) [IsMarkovKernel k]
    {f : Ω → DistOn upperHalfPlaneOpens} (hf : Measurable f) :
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × β => centredField h' u₀ p.1)
      (glueMeasure P k f hf) :=
  isZeroBoundaryGFF_comp_of_map_eq measurable_fst (glueMeasure_fst k hf) (isZeroBoundaryGFF_centredField hC hu₀)

/-- **History-marked locality of the marked set at the glued stop** (Aux. lemma 61's physical marked local set, from
UNIONLOC's (P1)). At the binders of `Aux61UnionK.GluedLocalCoverOn`, for the flow line's coupling `(W, V, ζ)` for the
field `h + θ₂χ` and a bounded harmonic extension `u₀` of its force data: for every counterflow time `s`, every
measurable Galmarino rule `ρ` of (the counterflow record at `s`, the flow's killed history), and every set `A` measurable for the
rule marks containing `ℍ ∩ (K_s ∪ K̃_T)` almost surely at the rule stop `T` (`K̃_T` the flow's Loewner hull), `A` is
history-marked local for the rule marks and the centred field on the glued measure. -/
theorem isHistoryAvoidanceLocal_ruleSet_gluedQ {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ}
    (h12 : θ₁ < θ₂) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (ζ : Ω → ℝ≥0∞)
    (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) (({0} : Finset ℝ) : Set ℝ))
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ} {Bm : ℝ≥0 → Ω → ℝ}
    (hC : IsOptionalHullCoupling κ (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)
      (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) P 𝓕 W VL VR Bm
      ζ (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω)))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂)
        (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineXL (Sec7.prop74Data a b) {0} 0)
        (flowLineXR (Sec7.prop74Data a b) {0} 0))
      (forceJumpSet (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)) u₀)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) (s : ℝ≥0)
    {ρ : HistorySpace 0 0 × HistorySpace (flowLineNL (Sec7.prop74Data a b) {0} 0)
      (flowLineNR (Sec7.prop74Data a b) {0} 0) → ℝ≥0∞}
    (hρ : Measurable ρ) (hG : IsGalmarinoRule stopRec ρ) {A : Ω × HistorySpace 0 0 → Set ℂ}
    (hAm : Measurable[ruleMarks stopRec ρ (fun p => stopRec s p.2) (fun p => killedHistory W VL VR ζ p.1),
      hittingSigma] A)
    (hsub : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
        ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
      unionAt (fun p => cfHullQ s p.2) (fun r p => fwdHull (fun t : ℝ => W t.toNNReal p.1) (r : ℝ))
        (fun p => ρ (stopRec s p.2, killedHistory W VL VR ζ p.1)) p ⊆ A p) :
    @IsHistoryAvoidanceLocal (Ω × HistorySpace 0 0)
      (ruleMarks stopRec ρ (fun p => stopRec s p.2) fun p => killedHistory W VL VR ζ p.1)
      Prod.instMeasurableSpace A
      (fun p => centredField (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω)) u₀ p.1)
      (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
        ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) := by
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by
    have hχ := Sec4.chiC_pos hκ hκ4
    have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
    linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  set θ := θ₂ - θ₁ + π / 2 with hθdef
  have hXeq : (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) =
      fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω)) := by
    funext ω
    rw [Prop51G.cfField_flowField_eq_cfFieldT κ θ₁ θ₂]
  have hμ : glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)) =
      glueMeasure P k (fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω)))
        ((measurable_cfFieldT κ θ).comp hC.2.1) := by
    congr 1
  have hlaw' : P.map (fun ω => cfFieldT κ θ (Exist.flowField 0 (θ₂ * chiC κ) (h ω))) = P₂.map h₂ := by
    rw [← hXeq]
    exact hlaw
  have hθb := Prop51G.cfThetaBounds_prop74 (a := a) (b := b) (θ₁ := θ₁) (θ₂ := θ₂) hκ hb (by
    have hχ := Sec4.chiC_pos hκ hκ4
    have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
    linarith)
  have hseed := ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hseed.mono fun _ hω => hω.1
  have hloc := isHistoryAvoidanceLocal_unionAt_rule_cfGlueT hC hκ hζ hθb hcf hlaw' hk hu₀ s hρ hG
  rw [← hμ] at hloc
  refine Sec7.Lemma72C.isHistoryAvoidanceLocal_mono_set hloc hAm ?_
  have hreg : ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
      ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
      ∀ t : ℝ≥0, regHull W ζ t p.1 = fwdHull (fun s : ℝ => W s.toNNReal p.1) (t : ℝ) := by
    have h1 : ∀ᵐ ω ∂((glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
        ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))).map Prod.fst),
        ∀ t : ℝ≥0, regHull W ζ t ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ) := by
      rw [glueMeasure_fst]
      exact ae_regHull_eq hC hζ
    exact ae_of_ae_map measurable_fst.aemeasurable h1
  filter_upwards [hsub, hreg] with p hp hr
  have e : unionAt (fun p => cfHullQ s p.2) (fun r p => regHull W ζ r p.1)
      (fun p => ρ (stopRec s p.2, killedHistory W VL VR ζ p.1)) p =
      unionAt (fun p => cfHullQ s p.2) (fun r p => fwdHull (fun t : ℝ => W t.toNNReal p.1) (r : ℝ))
        (fun p => ρ (stopRec s p.2, killedHistory W VL VR ζ p.1)) p := by
    simp only [unionAt, hr]
  rw [e]
  exact hp

/-- **The rule marks' facts for the assembly** (the fields `harmonic_originalMean`, `zero_field`, `baseMarks_le`,
`baseMarks_mono`, `locality` of `Aux61Marks.MarksFacts`), at the binders of `Aux61UnionK.GluedLocalCoverOn`, for the
flow line's coupling and the glued stops `ρ i r` (measurable Galmarino rules, nondecreasing in the fibre time from
`r = 0`): the physical marks `ruleMarks stopRec (ρ i r) …` are sub-σ-algebras, nested from time `0`, and every family
of sets `A i r` measurable for them and containing `ℍ ∩ (K_s ∪ K̃_{T(i,r)})` almost surely is history-marked local;
the centred field is a zero-boundary GFF on the glued space and `u₀` is harmonic. -/
theorem ruleMarksFacts_gluedQ {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ}
    (h12 : θ₁ < θ₂) (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (ζ : Ω → ℝ≥0∞)
    (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a b) (({0} : Finset ℝ) : Set ℝ))
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (flowLineNL (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (flowLineNR (Sec7.prop74Data a b) {0} 0) → ℝ≥0 → Ω → ℝ} {Bm : ℝ≥0 → Ω → ℝ}
    (hC : IsOptionalHullCoupling κ (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)
      (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) P 𝓕 W VL VR Bm
      ζ (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (h ω)))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ (Sec7.prop74Data a b) {0} 0 θ₂)
        (flowLineRhoR κ (Sec7.prop74Data a b) {0} 0 θ₂) (flowLineXL (Sec7.prop74Data a b) {0} 0)
        (flowLineXR (Sec7.prop74Data a b) {0} 0))
      (forceJumpSet (flowLineXL (Sec7.prop74Data a b) {0} 0) (flowLineXR (Sec7.prop74Data a b) {0} 0)) u₀)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω))) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) (s : ℝ≥0) {ι : Type*}
    (ρ : ι → ℝ≥0 → HistorySpace 0 0 × HistorySpace (flowLineNL (Sec7.prop74Data a b) {0} 0)
      (flowLineNR (Sec7.prop74Data a b) {0} 0) → ℝ≥0∞)
    (hρm : ∀ i r, Measurable (ρ i r)) (hρG : ∀ i r, IsGalmarinoRule stopRec (ρ i r))
    (hρle : ∀ i r y g, ρ i 0 (y, g) ≤ ρ i r (y, g)) (A : ι → ℝ≥0 → Ω × HistorySpace 0 0 → Set ℂ)
    (hAm : ∀ i r, Measurable[ruleMarks stopRec (ρ i r) (fun p => stopRec s p.2)
      (fun p => killedHistory W VL VR ζ p.1), hittingSigma] (A i r))
    (hsub : ∀ i r, ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
        ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))),
      unionAt (fun p => cfHullQ s p.2) (fun r p => fwdHull (fun t : ℝ => W t.toNNReal p.1) (r : ℝ))
        (fun p => ρ i r (stopRec s p.2, killedHistory W VL VR ζ p.1)) p ⊆ A i r p) :
    InnerProductSpace.HarmonicOnNhd u₀ H ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField (fun p : Ω × HistorySpace 0 0 => Exist.flowField 0 (θ₂ * chiC κ) (h p.1)) u₀)
      (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
        ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) ∧
    (∀ i r, ruleMarks stopRec (ρ i r) (fun p : Ω × HistorySpace 0 0 => stopRec s p.2)
      (fun p => killedHistory W VL VR ζ p.1) ≤ (Prod.instMeasurableSpace : MeasurableSpace (Ω × HistorySpace 0 0))) ∧
    (∀ i r, ruleMarks stopRec (ρ i 0) (fun p : Ω × HistorySpace 0 0 => stopRec s p.2)
      (fun p => killedHistory W VL VR ζ p.1) ≤
      ruleMarks stopRec (ρ i r) (fun p : Ω × HistorySpace 0 0 => stopRec s p.2)
        (fun p => killedHistory W VL VR ζ p.1)) ∧
    ∀ i r, @IsHistoryAvoidanceLocal (Ω × HistorySpace 0 0)
      (ruleMarks stopRec (ρ i r) (fun p => stopRec s p.2) fun p => killedHistory W VL VR ζ p.1)
      Prod.instMeasurableSpace (A i r)
      (centredField (fun p : Ω × HistorySpace 0 0 => Exist.flowField 0 (θ₂ * chiC κ) (h p.1)) u₀)
      (glueMeasure P k (fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)))
        ((measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1))) := by
  have hY : Measurable fun p : Ω × HistorySpace 0 0 => stopRec s p.2 :=
    (isRecordStop_stopRec (nL := 0) (nR := 0)).measurable.comp (measurable_const.prodMk measurable_snd)
  have hR : Measurable fun p : Ω × HistorySpace 0 0 => killedHistory W VL VR ζ p.1 :=
    (LawUnique.measurable_killedHistory hC.2.2.2.1).comp measurable_fst
  refine ⟨hu₀.1, isZeroBoundaryGFF_glued hC hu₀ k _, fun i r => ruleMarks_le isRecordStop_stopRec (hρm i r) hY hR,
    fun i r => Aux61Nest.ruleMarks_mono isRecordStop_stopRec (hρm i 0) (hρG i 0) (hρle i r) _ _, fun i r => ?_⟩
  exact isHistoryAvoidanceLocal_ruleSet_gluedQ hκ hκ4 h12 hb ha P h ζ hh hC hu₀ P₂ h₂ W₂ ζ₂ hcf hlaw k hk s
    (hρm i r) (hρG i r) (hAm i r) (hsub i r)

end Glued

end InteractingSLE.Sec5.Aux61Marks
