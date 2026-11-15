/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRoute
import InteractingSLE.Spec.Sec5.Prop49QExitMain

/-!
# Proposition 4.9's first exit and Proposition 4.11 in the chart `Q` without the general no-return input

Packet PROVE-CFNORETURN3 (ruling R59). PROVE-GLUECOND11's `Sec5.Prop49Exit.prop49QExitStatement_of_noReturn` takes
`Theorem14.GW4Ident.CounterflowNoReturnStatement` for every word, whose landed proof (two-seed completeness, through
Lemma 7.25) is circular for Theorems 1.2–1.3. It uses it only for the counterflow of a GFF with Cond. (4.4)'s data
`forceBoundaryData − πχ/2`, which is `≤ −λ + πχ/2` on `ℝ₋` and `≥ λ − πχ/2` on `ℝ₊`
(`Sec4.forceBoundaryData_bounds_of_cond44`). So the restricted input
`CfNoReturn.Route.CounterflowNoReturnAdmStatement` suffices, and it holds given Zhan's Part A inputs at `16/κ`
(`Sec5.PartAInputsSixteenDiv`, already an input of the route: `CfLineRegQ`, `GlueCondHit`, `Prop55`).

The proofs of `ae_cfHistory_mem_nrSet_of_adm` and `prop49QExitStatement_of_adm` are those of PROVE-GLUECOND11's
`ae_cfHistory_mem_nrSet` and `prop49QExitStatement_of_noReturn`, with the input replaced.

## Main results

* `prop49QExitStatement_of_partA : Sec5.PartAInputsSixteenDiv → Prop411Q.Prop49QExitStatement`.
* `prop411QStatement_of_lemma47Q_of_partA : Lemma47QHitStatement → Sec5.PartAInputsSixteenDiv →
  Cond44Ref.Prop411QStatement`.

No result here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement`, `Theorem13Statement`, two-seed completeness
or Lemma 7.25 (R48).
-/
set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop49Exit

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 MartChar.RealFlow LawUnique Cond44Ref Prop411Q CfRegQ

section NoReturnAdm

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂}
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}


/-- **The counterflow's history lies in `nrSet` almost surely**, given that centred counterflows of barrier data do
not return to their start (`CfNoReturn.Route.CounterflowNoReturnAdmStatement`). -/
theorem ae_cfHistory_mem_nrSet_of_adm [IsProbabilityMeasure P₂]
    (hNR : CfNoReturn.Route.CounterflowNoReturnAdmStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂) :
    ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ nrSet := by
  -- the counterflow field is a GFF with piecewise constant data
  set c : ℝ := -(π / 2 * chiC κ) with hc
  set b : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + c with hbdef
  have hb : IsPiecewiseConstantBoundaryData b (forceJumpFinset xL xR) :=
    isPiecewiseConstant_forceData κ ρL ρR xL xR c
  have hh : IsGFFWithBoundaryData P h (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) := ⟨hC.2.1, hC.2.2.1⟩
  have hh' := isGFFWithBoundaryData_flowField_zero hh c
  rw [← coe_forceJumpFinset] at hh'
  have hh'' : IsGFFWithBoundaryData P (fun ω => cfField κ (h ω)) b (forceJumpFinset xL xR) := hh'
  have hh₂ := isGFFWithBoundaryData_of_map_eq hh'' (measurable_of_isCenteredCounterflowDriver hcf) hlaw
  -- infinite lifetime, a continuous driver from `0` and a generating trace, almost surely
  obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm, hE⟩ :=
    exists_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
  have hk' : 0 < 16 / κ := by positivity
  have htr := ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm hE
  obtain ⟨hbL, hbR⟩ := Sec4.forceBoundaryData_bounds_of_cond44 hκ hκ4 hF h44
  have hnr := hNR κ hκ hκ4 b (forceJumpFinset xL xR) hb
    (fun x hx _ => by have := hbL x hx; simp only [hbdef, hc]; linarith)
    (fun x hx _ => by have := hbR x hx.le; simp only [hbdef, hc]; linarith) P₂ h₂ hh₂ W₂ ζ₂ hcf
  filter_upwards [htr, hE.2.2.2.2, hnr] with ω ⟨hζω, _, η, hη⟩ hp hnrω
  have hw : Continuous fun t => W₂ t ω := by
    have := hp.2.2.2.1
    rw [hζω] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  have hgood := cfHistory_mem_goodCfSet hζω hw hp.1 hη
  refine ⟨hgood, fun n => ?_⟩
  -- the driver read from the history is the counterflow driver
  have hval : ∀ p : ℕ × ℕ, dyVal (cfHistory W₂ ζ₂ ω) p = W₂ (dyadicTime p) ω := fun p => by
    simp [dyVal, cfHistory, killedHistory, hζω]
  have hdrv : hDrv (cfHistory W₂ ζ₂ ω) = fun t => W₂ t ω := by
    funext t
    rw [hDrv_apply]
    simp only [hval]
    exact (tendsto_lowerDyadic_of_continuousOn (T := ⊤) hw.continuousOn ENNReal.coe_lt_top).limUnder_eq
  have hc' := continuous_traceAt_of_mem_goodCfSet hgood
  have hgen : IsGeneratingTrace (fun t => W₂ t ω) ⊤ fun t => LP.traceAt t (hDrv (cfHistory W₂ ζ₂ ω)) := by
    have hev : ∀ N : ℕ, ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W₂ t ω)
        (((N : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) η' := fun N =>
      ⟨η, hη.1, hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top, fun t _ => hη.2.2 t ENNReal.coe_lt_top⟩
    rw [hdrv]
    exact isGeneratingTrace_top_traceAt hw hp.1 hev
  have hne := hnrω _ hgen
  -- a positive lower bound on the compact `[1/(n+1), n+1]`
  set K : Set ℝ≥0 := Icc ((1 / ((n : ℝ) + 1)).toNNReal) (((n : ℝ) + 1).toNNReal) with hK
  have hKne : K.Nonempty := ⟨((n : ℝ) + 1).toNNReal, by
    refine ⟨Real.toNNReal_le_toNNReal ?_, le_rfl⟩
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hKne
    ((continuous_norm.comp hc').continuousOn (s := K))
  have ht₀0 : 0 < t₀ := lt_of_lt_of_le (Real.toNNReal_pos.2 (by positivity)) ht₀.1
  have hpos : 0 < ‖LP.traceAt t₀ (hDrv (cfHistory W₂ ζ₂ ω))‖ := norm_pos_iff.2 (hne t₀ ht₀0)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  refine ⟨m, fun q hq1 hq2 => hm.le.trans (hmin ⟨?_, ?_⟩)⟩
  · exact Real.toNNReal_le_iff_le_coe.2 hq1
  · exact (Real.le_toNNReal_iff_coe_le (by positivity)).2 hq2


end NoReturnAdm

section MainAdm


/-- **Proposition 4.9's first exit at a rational counterflow time, in the chart `Q`** (`Prop411Q.Prop49QExitStatement`;
specification p. 120, Remark 4.10 and Aux. lemma 22), from the no-return of centred counterflows of barrier data
(`CfNoReturn.Route.CounterflowNoReturnAdmStatement`; ruling R59). -/
theorem prop49QExitStatement_of_adm (hNR : CfNoReturn.Route.CounterflowNoReturnAdmStatement.{u}) :
    Prop49QExitStatement.{u} := by
  intro s hs κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set s' : ℝ≥0 := (s : ℝ).toNNReal with hs'def
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hs' : 0 < s' := Real.toNNReal_pos.2 hs0
  have hss' : (s' : ℝ) = (s : ℝ) := Real.coe_toNNReal _ hs0.le
  set E := glueGood μ s' ζ W with hEdef
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hgood := cfGlueAE_isGood49 s' hs' κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hae : ∀ᵐ p ∂μ, IsGood49 s' ζ W p := by
    filter_upwards [hgood] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hexit := ae_imgExit hκ hκ4 hF h44 hC hcf hlaw k hk hs'
  have hnr : ∀ᵐ p ∂μ, p.2 ∈ nrSet :=
    ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf)
      (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf)) hlaw k hk
      measurableSet_nrSet (ae_cfHistory_mem_nrSet_of_adm hNR hκ hκ4 hF h44 hC hcf hlaw)
  filter_upwards [hexit, hgood, hnr, ae_mem_glueGood hae] with p ⟨hTne, z, hz, hzalt⟩ hpg hpnr hpE
  obtain ⟨hα, hG0, hjL0, -, hQ⟩ := isGood49_of_mem_glueGood p hpE
  have hy : p.2 ∈ goodCfSet := hpg.2.1.1
  obtain ⟨-, hw, hw0, hβ⟩ := reg_of_mem_goodCfSet hy
  -- from the stopped driver `cfDrv0` to the counterflow driver `cfDrv`
  have hEq := eqOn_cfDrv0_cfDrv hy s'
  have hK0 := fwdHull_cfDrv0 hy s'
  have hR0 := revChart_cfDrv0 hy s'
  have hrI : rightImg (cfDrv0 s' p.2) 0 s' = rightImg (cfDrv p.2) 0 s' :=
    Sec7.Lemma71B.rightImg_congr hw s'.coe_nonneg hEq 0
  have hw0s : cfDrv0 s' p.2 s' = cfDrv p.2 s' := hEq s' ⟨s'.coe_nonneg, le_rfl⟩
  have hjL : 0 < rightImg (cfDrv p.2) 0 s - cfDrv p.2 s := by
    rw [← hss', ← hrI, ← hw0s]; exact hjL0
  have hG : IsClosed (negInv '' fwdHull (cfDrv p.2) s) := by rw [← hss', ← hK0]; exact hG0
  have hcurve : gCurve s' ζ W E p = imgCurve (cfDrv p.2) s (seedLine ζ W p.1) := by
    rw [gCurve_of_mem hpE]
    funext u
    simp only [imgCurve]
    rw [hR0, hss']
  have hpre : gPre s' ζ W E p = preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s) := by
    rw [gPre_of_mem hpE, hQ, hK0, hss']
  have hjun : gXL xL s' E p (Fin.last nL) = junL (cfDrv p.2) s := by
    rw [gXL_of_mem hpE, Fin.snoc_last]
    simp only [junL]
    rw [hrI, hw0s, hss']
  have hT' : ((ENNReal.toNNReal (imgT s' ζ W E p) : ℝ≥0) : WithTop ℝ≥0) =
      kLife (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
        (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)) := by
    rw [← hcurve, ← hpre]
    exact ENNReal.coe_toNNReal hTne
  have hz' : Tendsto (kTrace (imgCurve (cfDrv p.2) s (seedLine ζ W p.1))
      (preContact (seedLine ζ W p.1) (negInv '' fwdHull (cfDrv p.2) s)))
      (𝓝[<] ENNReal.toNNReal (imgT s' ζ W E p)) (𝓝 z) := by
    rw [← hcurve, ← hpre]; exact hz
  have hzalt' : z ∈ H ∨ ∃ x₀ : ℝ, x₀ < junL (cfDrv p.2) s ∧ z = x₀ := by
    rcases hzalt with h1 | ⟨x₀, hx₀, rfl⟩
    · exact Or.inl h1
    · exact Or.inr ⟨x₀, hjun ▸ hx₀, rfl⟩
  have hNRp : ∀ v ∈ Ioc (0 : ℝ) s, histLine p.2 v ≠ 0 := fun v hv =>
    histLine_ne_zero_of_mem_nrSet hpnr hv.1
  obtain ⟨t₀, x₀, ht₀, hx₀, ⟨v, hv, hve⟩, havoid, hlim⟩ :=
    exit_of_imgExit hw hw0 hβ hs0 hNRp hjL hG hα hT' hz' hzalt'
  exact ⟨t₀, x₀, ht₀, hx₀, ⟨v, hv, hve⟩, havoid, hlim⟩


/-- **Proposition 4.9's first exit in the chart `Q` from Zhan's Part A inputs at `16/κ`**
(`Prop411Q.Prop49QExitStatement`; `Sec5.PartAInputsSixteenDiv` gives Aux. lemma 7 at `16/κ`, hence the barrier
no-return). -/
theorem prop49QExitStatement_of_partA (hA : PartAInputsSixteenDiv) : Prop49QExitStatement.{u} :=
  prop49QExitStatement_of_adm (CfNoReturn.Route.counterflowNoReturnAdmStatement_of_partA hA)

/-- **Proposition 4.11 in the chart `Q`** (`Cond44Ref.Prop411QStatement`) from Lemma 4.7 at rational flow times and
Zhan's Part A inputs at `16/κ` (the counterflow's regularity is `CfRegQ.cfRegQStatement`). Conditional helper; it
replaces `prop411QStatement_of_lemma47Q_of_noReturn` on the route of Theorems 1.2–1.3. -/
theorem prop411QStatement_of_lemma47Q_of_partA (h47 : Lemma47QHitStatement.{u}) (hA : PartAInputsSixteenDiv) :
    Prop411QStatement.{u} :=
  prop411QStatement_of_lemma47Q_of_prop49Q cfRegQStatement h47 (prop49QExitStatement_of_partA hA)

end MainAdm

end InteractingSLE.Sec5.Prop49Exit
