/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3StopAnnounce
import InteractingSLE.Spec.Supplement.GB6GaugeEVersion

/-!
# GB6's relative safe law for path-rule versions: the wiring

Packet PROVE-GB6-RELSAFE. `Q3Stop.GB6RelSafeStatement` asks K2's inputs for EVERY version of GB6's relative
exploration (`IsGB6RelVersion`: the stop only a stopping time of the completed (record, path) filtration). The
physical adaptedness proved in `RelSafeGB6Read` (the relative filtration traced on `{q ≤ a(t)}` is in the physical
filtration) uses that the stop is a path rule of (record, path) (`HullId.IsGB6RelVersionR`); the wiring
(`Q3Stop.gb6RelDrvDetStatement_of_relSafe`) only uses announced versions, which are R-form. This file states the
input for R-form versions and re-derives the wiring:

* **`GB6RelSafeRStatement`**: `Q3Stop.GB6RelSafeStatement` restricted to R-form versions (implied by it,
  `gb6RelSafeRStatement_of_relSafe`);
* `ae_isStopDrvMatch_of_relSafeR`, `gb6RelDrvDetStatement_of_relSafeR` (the proofs of `Q3StopWire` verbatim, the
  version passed in R-form);
* **`gb6HullDetStatement_of_relSafeR`**: Theorem 1.4's `GB6HullDetStatement` from `GB6RelSafeRStatement` alone (the
  live read-back is PROVE-GB6-VERSION's proved `GaugeE.gb6LiveReadoutStatement`).

**R48.** GB6 serves Theorem 1.4; nothing here takes Theorem 1.2, 1.3, `Theorem12ParamStatement` or
`Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Supp8.Q3Stop

open Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId Sec7.StripSysField

/-- **Named input: GB6's relative safe law for path-rule versions** (`GB6RelSafeStatement` restricted to the R-form
versions, `HullId.IsGB6RelVersionR`). -/
def GB6RelSafeRStatement : Prop :=
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
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), HullId.IsGB6RelVersionR s P W Wα ζα γ α R V →
    ∀ w : WordType, HasRelSafe (16 / κ) w (gb6WordOfRec κ θ c) (gb6TS s)
      (P.map fun ω => (gb6Rec s Wα ζα ω, relVar Hc R V ω))

/-- **The stopped driver match of an announced version from the relative safe law for R-form versions.** -/
theorem ae_isStopDrvMatch_of_relSafeR (hS : GB6RelSafeRStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
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
    (hver : IsGB6RelVersionA s P W Wα ζα γ α R V) :
    ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R t ω) (V ω) := by
  obtain ⟨⟨hv, ρ, hρm, hρ, hVρ⟩, ρs, hρsm, hρs, hρsfin, hρsmono, hann⟩ := hver
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hβ := measurable_gb6WordOfRec κ θ c
  have hk : 0 < 16 / κ := by positivity
  have hV0 : ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → 0 < V ω := by
    filter_upwards [hv.2.2.2.2.2.2, ae_gb6RecGood hfl hα s] with ω hω hg hm
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hg).2 hm
    exact (hω hs hsH).1
  have hw : ∀ w : WordType, ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s →
      wordType (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)) = w →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R t ω) (V ω) := fun w =>
    ae_isStopDrvMatch_of_hasRelSafe hk hF hβ (measurableSet_gb6TS s) w hrecm hHcm hv.1 hv.2.1 hv.2.2.1
      hv.2.2.2.2.1 (hS κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR
        hcomp hfl hα s Hc hHcm hHc c hcJ hcb R V ⟨hv, ρ, hρm, hρ, hVρ⟩ w) hV0 hρm hρ hVρ hρsm hρs hρsfin hρsmono
      (hann.mono fun ω h hm => (h hm).1) (hann.mono fun ω h hm => (h hm).2)
  have hall := (ae_ball_iff (countable_range_wordType_gb6 (16 / κ) κ θ c)).2 fun w _ => hw w
  filter_upwards [hall] with ω hω hm
  exact hω _ ⟨_, rfl⟩ hm rfl

/-- **GB6's driver-form determination from announced versions and the R-form relative safe law.** -/
theorem gb6RelDrvDetStatement_of_relSafeR (hV : Q3Stop.GB6RelVersionAStatement.{u}) (hS : GB6RelSafeRStatement.{u}) :
    GB6RelDrvDetStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc F hF c hcJ hcb
  obtain ⟨R, V, hver, hexh⟩ :=
    hV κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hcomp hfl hα s
  have hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R m t ω) (V m ω) := fun m =>
    ae_isStopDrvMatch_of_relSafeR hS hκ hκ4 hθ₁ hθ₂ hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s hHcm hHc hF hcJ hcb
      (hver m)
  have hvae : ∀ m, ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → 0 < V m ω ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < V m ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → ENNReal.ofReal (gb6Clock s W Wα ω t) ≤ V m ω →
        QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal ω) (gb6Clock s W Wα ω t) =
          relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t :=
    fun m => (hver m).1.1.2.2.2.2.2.2
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
  exact drvDec_eq_of_isStopDrvMatch_family (hgω hs hsH) (R := fun m t => R m t ω) (fun m => (hver m).1.1.2.1 ω)
    (fun m => (hver m).1.1.2.2.1 ω) hmatch ha0 hsm hac (fun m t ht hle => ((hvω m hs hsH).2.2 t ht hle))
    (hexω hs hsH) hW'c hW'K t ht u hu


theorem gb6RelSafeRStatement_of_relSafe (hS : GB6RelSafeStatement.{u}) : GB6RelSafeRStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc c hcJ hcb R V hver
  exact hS κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc c hcJ hcb R V hver.1

/-- **GB6's hull identity from the relative safe law for path-rule versions alone.** -/
theorem gb6HullDetStatement_of_relSafeR (hS : GB6RelSafeRStatement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_relDrvDet (gb6RelDrvDetStatement_of_relSafeR
    (gb6RelVersionAStatement_of_readoutCoord (gb6ReadoutCoordStatement_of_liveReadout GaugeE.gb6LiveReadoutStatement))
    hS)

end InteractingSLE.Supp8.Q3Stop
