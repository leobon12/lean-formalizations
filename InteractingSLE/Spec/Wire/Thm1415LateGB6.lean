/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RelDrv
import InteractingSLE.Spec.Supplement.GB6Version
import InteractingSLE.Spec.Supplement.GB6CoordBReadout
import InteractingSLE.Spec.Supplement.HullDetGen
import InteractingSLE.Spec.Supplement.Q3KernelWord

/-!
# GB6 determination through the proved regular-stop form of Aux. 54

The conditional kernel statement includes the own-history rule and regularity
required by R79. It is not asserted from the older kernel statement. Gauge
construction and this regular stopped field law remain mathematical inputs.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)
universe u
namespace InteractingSLE.Wire
open LawUnique
open Restart Restart.StoppedExtend Sec2.Assembly Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv

/-- The relative stopped field law with the exact R79 rule and regularity. -/
def GB6RelStopKernelRStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGB6RelVersion s P W Wα ζα γ α R V →
    ∀ K : Kernel RecData RelSpace, IsMarkovKernel K →
      (P.restrict (gb6Rec s Wα ζα ⁻¹' gb6TS s)).map (fun ω => (gb6Rec s Wα ζα ω, relVar Hc R V ω)) =
        (P.restrict (gb6Rec s Wα ζα ⁻¹' gb6TS s)).map (gb6Rec s Wα ζα) ⊗ₘ K →
      ∀ᵐ r ∂(P.restrict (gb6Rec s Wα ζα ⁻¹' gb6TS s)).map (gb6Rec s Wα ζα),
        ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
          (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (RelSpace × Ω₀)))
          (VL : Fin (flowLineNL (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0) → ℝ≥0 →
            RelSpace × Ω₀ → ℝ)
          (VR : Fin (flowLineNR (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0) → ℝ≥0 →
            RelSpace × Ω₀ → ℝ)
          (B : ℝ≥0 → RelSpace × Ω₀ → ℝ),
          IsStoppedHullCoupling (16 / κ) (flowLineXL (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0)
            (flowLineXR (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0)
            (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0)
            (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0)
            ((K r).prod P₀) 𝓕 (fun t p => relDrv t p.1) VL VR B (fun p => relStp p.1) (fun p => relFld p.1) ∧
          ∃ rule : HistorySpace (flowLineNL (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0)
              (flowLineNR (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0) → ℝ≥0∞,
            Measurable rule ∧ Restart.StoppedExtendWF.IsHistGalmarino rule ∧
            (∀ᵐ p ∂((K r).prod P₀), relStp p.1 =
              rule (killedHistory (fun t p => relDrv t p.1) VL VR (fun p => relStp p.1) p)) ∧
            Restart.Aux54.IsRegularStop
              (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0)
              (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c r).fn (gb6WordOfRec κ θ c r).jumps 0 0)
              ((K r).prod P₀) (fun t p => relDrv t p.1) VL VR (fun p => relStp p.1)

/-- Stopped determination under the R79 regular kernel. -/
theorem ae_isStopDrvMatch_of_version_late (hK : GB6RelStopKernelRStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
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
    (hver : IsGB6RelVersion s P W Wα ζα γ α R V) :
    ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R t ω) (V ω) := by
  have hRm := hver.1
  have hRc := hver.2.1
  have hR0 := hver.2.2.1
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hMm : MeasurableSet (gb6Rec s Wα ζα ⁻¹' gb6TS s) := hrecm (measurableSet_gb6TS s)
  have hVm : Measurable V := hver.2.2.2.2.1
  have hYm : Measurable (relVar Hc R V) := measurable_relVar hHcm hRm hVm
  obtain ⟨K, hKm, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P (gb6Rec s Wα ζα ⁻¹' gb6TS s) hrecm hYm
  have hcpl := hK κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp
    hfl hα s Hc hHcm hHc c hcJ hcb R V hver K hKm hlaw
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
    filter_upwards [hcpl] with r hr
    obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕, VL, VR, B, hSC, rule, hRm, hRG, hRe, hReg⟩ := hr
    have hd := Supp8.HullDetGen.ae_isStopDrvMatch_of_isStoppedHullCouplingR (by positivity) hF (gb6WordOfRec κ θ c r)
      (Ω := RelSpace × Ω₀) (Q := (K r).prod P₀) (Hc := fun p => relFld p.1) (X := fun p => relFld p.1)
      (fun p => Sec7.StripSysField.isTranslateAddConst_zero_self _ _) hSC hRm hRG hRe hReg (Wb := fun t p => relDrv t p.1)
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

/-- Determination from exhausting versions and the regular kernel. -/
theorem gb6RelDrvDetStatement_of_regularKernel_late
    (hV : GB6RelVersionStatement.{u}) (hK : GB6RelStopKernelRStatement.{u}) : GB6RelDrvDetStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc F hF c hcJ hcb
  obtain ⟨R, V, hver, hexh⟩ :=
    hV κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hcomp hfl hα s
  have hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R m t ω) (V m ω) := fun m =>
    ae_isStopDrvMatch_of_version_late hK hκ hκ4 hθ₁ hθ₂ hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s hHcm
      hHc hF hcJ hcb (hver m)
  have hvae : ∀ m, ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → 0 < V m ω ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < V m ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → ENNReal.ofReal (gb6Clock s W Wα ω t) ≤ V m ω →
        QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal ω) (gb6Clock s W Wα ω t) =
          relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t :=
    fun m => (hver m).2.2.2.2.2.2
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
  exact drvDec_eq_of_isStopDrvMatch_family (hgω hs hsH) (R := fun m t => R m t ω) (fun m => (hver m).2.1 ω)
    (fun m => (hver m).2.2.1 ω) hmatch ha0 hsm hac (fun m t ht hle => ((hvω m hs hsH).2.2 t ht hle))
    (hexω hs hsH) hW'c hW'K t ht u hu

/-- Hull determination from the remaining gauge and regular stopped-kernel inputs. -/
theorem gb6HullDetStatement_of_gauge_regularKernel_late
    (hGauge : Supp8.GB6.RelDrv.Version.GB6RelativeGaugeStatement.{u})
    (hK : GB6RelStopKernelRStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  Supp8.GB6.gb6HullDetStatement_of_relDrvDet
    (gb6RelDrvDetStatement_of_regularKernel_late
      (Supp8.GB6.RelDrv.Version.gb6RelVersionStatement_of_relativeGauge hGauge) hK)

end InteractingSLE.Wire
