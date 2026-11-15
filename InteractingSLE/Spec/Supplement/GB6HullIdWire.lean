/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6HullIdVersion
import InteractingSLE.Spec.Supplement.GB6RelDrv
import InteractingSLE.Spec.Supplement.HullDetGen

/-!
# GB6's hull identity from the plain stopped kernel and path-rule versions

Packet PROVE-GB6-HULLID. PROVE-HULLDET's generic stopped determination
`HullDetGen.ae_isStopDrvMatch_of_isStoppedHullCouplingR` (through the proved corrected Aux. 54, R79) needs a
measurable Galmarino rule for the stop and a regular stop. The wiring
`Wire.gb6HullDetStatement_of_gauge_regularKernel_late` asked the stopped kernel to supply both
(`Wire.GB6RelStopKernelRStatement`). Here they are proved instead:

* the rule is `histRule ρ r` (`GB6HullIdRule`) for the path rule `ρ` of an R-form version (`GB6HullIdVersion`): the
  identity `relStp = histRule ρ r (killed history)` passes from `P` to almost every kernel `K r` through the
  disintegration (`Measure.ae_ae_of_ae_compProd`);
* the stop is regular because the decoded relative driver `relDrv · p = FCDet.decDrv p.2.1` is continuous for every
  code.

So the stopped kernel is needed only in PROVE-GB6-RELDRV's plain form `GB6RelStopKernelStatement` (PROVE-Q3-REL3's
target):

* `ae_isStopDrvMatch_of_versionR`;
* `gb6RelDrvDetStatement_of_versionR_stopKernel : GB6RelVersionRStatement → GB6RelStopKernelStatement →
  GB6RelDrvDetStatement`;
* **`gb6HullDetStatement_of_sourceReadout_stopKernel : GB6SourceReadoutStatement → GB6RelStopKernelStatement →
  GB6HullDetStatement`**.

R48: GB6 serves Theorem 1.4; nothing here takes Theorem 1.2/1.3 as a hypothesis (the canonical driver code `F` is a
binder of the statements).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Supp8.GB6.HullId

open LawUnique Restart Restart.StoppedExtend Sec2.Assembly Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv

/-- **Stopped determination for an R-form version under the plain stopped kernel.** On the record event, the relative
driver of a version stopped by a path rule matches the canonical driver code of the chart field with GB6's word at
every dyadic time before the stop. -/
theorem ae_isStopDrvMatch_of_versionR (hK : GB6RelStopKernelStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [hP : IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hadmL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hadmR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (s : ℝ≥0) {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω))
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode (16 / κ) 0 F) {c : BoundaryWord} (hcJ : c.jumps = J)
    (hcb : ∀ y ∉ J, c.fn y = b y) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsGB6RelVersionR s P W Wα ζα γ α R V) :
    ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R t ω) (V ω) := by
  obtain ⟨hv, ρ, hρm, hρ, hVρ⟩ := hver
  have hRm := hv.1
  have hRc := hv.2.1
  have hR0 := hv.2.2.1
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hMm : MeasurableSet (gb6Rec s Wα ζα ⁻¹' gb6TS s) := hrecm (measurableSet_gb6TS s)
  have hVm : Measurable V := hv.2.2.2.2.1
  have hYm : Measurable (relVar Hc R V) := measurable_relVar hHcm hRm hVm
  obtain ⟨K, hKm, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P (gb6Rec s Wα ζα ⁻¹' gb6TS s) hrecm hYm
  have hcpl := hK κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp
    hfl hα s Hc hHcm hHc c hcJ hcb R V hv K hKm hlaw
  -- the path-rule identity of the stop, transported to almost every kernel
  set E' : Set (RecData × RelSpace) := {q | relStp q.2 = ρ (q.1, fun t => relDrv t q.2)} with hE'def
  have hpath : Measurable fun q : RecData × RelSpace => (q.1, fun t => relDrv t q.2) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun t => (measurable_relDrv t).comp measurable_snd)
  have hE'm : MeasurableSet E' :=
    measurableSet_eq_fun (measurable_relStp.comp measurable_snd) (hρm.comp hpath)
  have hPE' : ∀ᵐ ω ∂(P.restrict (gb6Rec s Wα ζα ⁻¹' gb6TS s)),
      (gb6Rec s Wα ζα ω, relVar Hc R V ω) ∈ E' := by
    filter_upwards [ae_restrict_of_ae hVρ] with ω hω
    have e : (fun t => relDrv t (relVar Hc R V ω)) = fun t => R t ω :=
      funext fun t => relDrv_relVar (hRc ω) (hR0 ω) t
    change relStp (relVar Hc R V ω) = ρ (gb6Rec s Wα ζα ω, fun t => relDrv t (relVar Hc R V ω))
    rw [e]
    exact hω
  have hcE' : ∀ᵐ x ∂((P.restrict (gb6Rec s Wα ζα ⁻¹' gb6TS s)).map (gb6Rec s Wα ζα) ⊗ₘ K), x ∈ E' := by
    rw [← hlaw]
    exact (ae_map_iff (hrecm.prodMk hYm).aemeasurable hE'm).2 hPE'
  have hKE' := Measure.ae_ae_of_ae_compProd hcE'
  set E : Set (RecData × RelSpace) :=
    {q | IsStopDrvMatch (F (gb6WordOfRec κ θ c q.1, relFld q.2)) (fun t => relDrv t q.2) (relStp q.2)} with hEdef
  have hE : MeasurableSet E :=
    measurableSet_isStopDrvMatch (S := RecData × RelSpace)
      (G := fun q => F (gb6WordOfRec κ θ c q.1, relFld q.2))
      (hF.1.comp (((measurable_gb6WordOfRec κ θ c).comp measurable_fst).prodMk
        (measurable_relFld.comp measurable_snd)))
      (fun t => (measurable_relDrv t).comp measurable_snd) (measurable_relStp.comp measurable_snd)
  have hKE : ∀ᵐ r ∂(P.restrict (gb6Rec s Wα ζα ⁻¹' gb6TS s)).map (gb6Rec s Wα ζα),
      ∀ᵐ q ∂(K r), (r, q) ∈ E := by
    filter_upwards [hcpl, hKE'] with r hr hr'
    obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕, VL, VR, B, hSC⟩ := hr
    have h1 : ∀ᵐ p ∂((K r).prod P₀), relStp p.1 = ρ (r, fun t => relDrv t p.1) :=
      ConverseBefore.ae_fst_of_ae (P₀ := P₀) (q := fun q => relStp q = ρ (r, fun t => relDrv t q)) hr'
    have hRe : ∀ᵐ p ∂((K r).prod P₀), relStp p.1 =
        histRule ρ r (killedHistory (fun t (p : RelSpace × Ω₀) => relDrv t p.1) VL VR (fun p => relStp p.1) p) := by
      filter_upwards [h1] with p hp
      exact (histRule_killedHistory hρ (W := fun t (p : RelSpace × Ω₀) => relDrv t p.1) (VL := VL) (VR := VR)
        (e := fun p => relStp p.1) (FCDet.continuous_decDrv _) (FCDet.decDrv_zero _) hp).symm
    have hReg : Aux54.IsRegularStop
        (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0)
        (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0)
        ((K r).prod P₀) (fun t p => relDrv t p.1) VL VR (fun p => relStp p.1) :=
      ae_of_all _ fun p T _ _ => ⟨T + 1, lt_add_one T, (FCDet.continuous_decDrv p.1.2.1).continuousOn⟩
    have hd := Supp8.HullDetGen.ae_isStopDrvMatch_of_isStoppedHullCouplingR (by positivity) hF (gb6WordOfRec κ θ c r)
      (Ω := RelSpace × Ω₀) (Q := (K r).prod P₀) (Hc := fun p => relFld p.1) (X := fun p => relFld p.1)
      (fun p => Sec7.StripSysField.isTranslateAddConst_zero_self _ _) hSC (measurable_histRule hρm r)
      (isHistGalmarino_histRule hρ r) hRe hReg (Wb := fun t p => relDrv t p.1)
      (fun t => (measurable_relDrv t).comp measurable_fst) (measurable_relFld.comp measurable_fst)
      (measurable_relStp.comp measurable_fst) (ae_of_all _ fun _ _ _ => rfl)
    exact ConverseBefore.ae_of_ae_fst (P₀ := P₀)
      (q := fun q => IsStopDrvMatch (F (gb6WordOfRec κ θ c r, relFld q)) (fun t => relDrv t q) (relStp q)) hd
  have hPE := Sec5.MarkovOther.ae_mem_of_compProd_eq_prod hMm hrecm hYm hlaw hE hKE
  filter_upwards [hPE] with ω hω hωM
  have h1 := hω hωM
  simp only [hEdef, mem_ofPred_eq] at h1
  have e : (fun t => relDrv t (relVar Hc R V ω)) = fun t => R t ω :=
    funext fun t => relDrv_relVar (hRc ω) (hR0 ω) t
  rw [e] at h1
  exact h1

/-- **GB6's driver-form determination from R-form versions and the plain stopped kernel.** -/
theorem gb6RelDrvDetStatement_of_versionR_stopKernel
    (hV : GB6RelVersionRStatement.{u}) (hK : GB6RelStopKernelStatement.{u}) : GB6RelDrvDetStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc F hF c hcJ hcb
  obtain ⟨R, V, hver, hexh⟩ :=
    hV κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hcomp hfl hα s
  have hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R m t ω) (V m ω) := fun m =>
    ae_isStopDrvMatch_of_versionR hK hκ hκ4 hθ₁ hθ₂ hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s hHcm
      hHc hF hcJ hcb (hver m)
  have hvae : ∀ m, ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → 0 < V m ω ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < V m ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → ENNReal.ofReal (gb6Clock s W Wα ω t) ≤ V m ω →
        QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal ω) (gb6Clock s W Wα ω t) =
          relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t :=
    fun m => (hver m).1.2.2.2.2.2.2
  have hgood := ae_isGoodDrvCode_gb6 (θ := θ) hκ hb hG hfl hα s hHcm hHc hF hcb
  filter_upwards [ae_all_iff.2 hm, hgood, ae_all_iff.2 hvae, hexh, hcomp, ae_driver_zero_continuousOn hcf,
    ae_driver_zero_continuousOn hfl, hα, ae_gb6RecGood hfl hα s]
    with ω hmω hgω hvω hexω hcω hWω hWαω hαω hg hs hsH W' hW'c hW'K t ht u hu
  have hωM : gb6Rec s Wα ζα ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs, hsH⟩
  have hβ : gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω) = gb6Word κ θ c s (fun t => Wα t ω) := by
    rw [gb6Word, (hg hs).2.1]
  obtain ⟨hζ, hγ, -⟩ := hcω
  have hw : Continuous fun t => W t ω :=
    continuousOn_univ.1 (hWω.2.mono fun t _ => by rw [mem_ofPred_eq, hζ]; exact ENNReal.coe_lt_top)
  obtain ⟨ha0, hsm, hac⟩ := relClock_props_of_traces hαω hWαω.2 hWαω.1 hs hsH hγ hw hWω.1
  have hmatch : ∀ m, IsStopDrvMatch (F (gb6Word κ θ c s (fun t => Wα t ω), Hc ω)) (fun t => R m t ω) (V m ω) :=
    fun m => by
      have := hmω m hωM
      rwa [hβ] at this
  exact drvDec_eq_of_isStopDrvMatch_family (hgω hs hsH) (R := fun m t => R m t ω) (fun m => (hver m).1.2.1 ω)
    (fun m => (hver m).1.2.2.1 ω) hmatch ha0 hsm hac (fun m t ht hle => ((hvω m hs hsH).2.2 t ht hle))
    (hexω hs hsH) hW'c hW'K t ht u hu

/-- **GB6's hull identity (`GB6HullDetStatement`) from the read-back input and the plain stopped kernel.** The two
inputs are PROVE-GB6-VERSION's `SourceC.GB6SourceReadoutStatement` (causal physical read-back of the constructed
relative driver) and PROVE-GB6-RELDRV's `GB6RelStopKernelStatement` (Q3 for GB6, PROVE-Q3-REL3's target); no
Galmarino rule or regularity is asked of the kernel. -/
theorem gb6HullDetStatement_of_sourceReadout_stopKernel
    (hread : SourceC.GB6SourceReadoutStatement.{u}) (hK : GB6RelStopKernelStatement.{u}) :
    Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_relDrvDet
    (gb6RelDrvDetStatement_of_versionR_stopKernel (gb6RelVersionRStatement_of_sourceReadout hread) hK)

end InteractingSLE.Supp8.GB6.HullId
