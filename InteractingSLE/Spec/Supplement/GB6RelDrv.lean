/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RelDrvLift
import InteractingSLE.Spec.Supplement.GB6RelDetDrv
import InteractingSLE.Spec.Supplement.GB6RelDetGood
import InteractingSLE.Spec.Restart.FCDetTransfer

/-!
# GB6's (Det) in driver form from the relative stopped coupling (Aux. 54 and canonical driver codes)

Packet PROVE-GB6-RELDRV. `GB6RelDrvDetStatement` (PROVE-GB6-RELDET) asks that the decoded canonical driver code of
GB6's conditional field agrees, before the first contact, with the relative driver of the counterflow. Its two
ingredients (PROVE-GB6-RELDET's handoff §4) are (1) the relative stopped coupling — Astra's follow-up 3, Q3, for the
GB6 configuration: conditional on the marked flow prefix, the counterflow read in the flow's own chart is, through
every stop before its first contact, a coupling of the conditional field with the evolving conditional word — and (2)
stopped determination. This file proves (2) and isolates (1) as a named input, in the conditional form in which the
specification states it (p. 518: "Conditional on the marked prefix, the portion of `η` before its first contact with
`α[0, σ]`, in the chart of `U` taking `(y, p)` to `(0, ∞)`, is the complete canonical counterflow of the conditional
component field"):

* `RelSpace = 𝒟'(ℍ) × (driver code) × [0, ∞]`: the chart field, the dyadic code of a relative driver, a stop;
  `relVar Hc R V`;
* `IsGB6RelVersion`: a **measurable version** `(R, V)` of the relative exploration through a stop: `R` continuous,
  measurable, frozen after `V`; `V` a stopping time of the completed natural filtration of the record and the
  relative path (`IsDetUpTo`); almost surely on
  the interior-tip event, `0 < V`, `V` precedes the relative contact, and `R` generates the chart images `Ψ(K'_t)` of
  the counterflow hulls in the relative clock up to `V`;
* **`GB6RelStopKernelStatement`** (named input, ingredient (1)): for every such version and every disintegration `K`
  of `(record, relVar)` over the record, for almost every record `r`, under `K r` (with independent noise for the
  Brownian motion after the stop) the relative exploration is a coupling through the stop of the conditional word
  `β(r)` (`StoppedExtend.IsStoppedHullCoupling`) — Astra's Q3 conclusion (Q3.2)–(Q3.4) and relative locality;
* **`GB6RelVersionStatement`** (named, measurability): a family of such versions exhausting the pre-contact
  relative interval exists;
* **`gb6RelDrvDetStatement_of_stopKernel`**: Aux. lemma 54, `GB6RelVersionStatement` and
  `GB6RelStopKernelStatement` give `GB6RelDrvDetStatement` (ingredient (2):
  `RelDrv.ae_isStopDrvMatch_of_isStoppedHullCoupling` under each conditional law, the record disintegration back to
  `P`, and the pathwise comparison of drivers with the same hulls).

**R48.** The canonical driver code `F` of the statement exists only through Theorems 1.2–1.3; GB6 serves Theorem 1.4.
Nothing here takes Theorem 1.2, 1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Supp8.GB6.RelDrv

open Restart Restart.StoppedExtend Sec2.Assembly Exist.StagedLaw

/-! ### The relative canonical space -/

/-- **GB6's relative canonical space**: the chart field, the dyadic code of a relative driver, and a stop. -/
abbrev RelSpace : Type := DistOn upperHalfPlaneOpens × PCode × ℝ≥0∞

/-- The field coordinate. -/
def relFld (p : RelSpace) : DistOn upperHalfPlaneOpens := p.1

/-- The decoded relative driver. -/
def relDrv (t : ℝ≥0) (p : RelSpace) : ℝ := FCDet.decDrv p.2.1 t

/-- The stop coordinate. -/
def relStp (p : RelSpace) : ℝ≥0∞ := p.2.2

theorem measurable_relFld : Measurable relFld := measurable_fst

theorem measurable_relDrv (t : ℝ≥0) : Measurable (relDrv t) :=
  (FCDet.measurable_decDrv t).comp (measurable_fst.comp measurable_snd)

theorem measurable_relStp : Measurable relStp := measurable_snd.comp measurable_snd

/-- The relative variable of a field, a driver and a stop. -/
def relVar {Ω : Type*} (Hc : Ω → DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) :
    RelSpace :=
  (Hc ω, enc fun t => R t ω, V ω)

theorem measurable_relVar {Ω : Type*} [MeasurableSpace Ω] {Hc : Ω → DistOn upperHalfPlaneOpens}
    (hHc : Measurable Hc) {R : ℝ≥0 → Ω → ℝ} (hR : ∀ t, Measurable (R t)) {V : Ω → ℝ≥0∞} (hV : Measurable V) :
    Measurable (relVar Hc R V) :=
  hHc.prodMk ((Sec2.Assembly2.measurable_enc.comp (measurable_pi_iff.2 hR)).prodMk hV)

theorem relDrv_relVar {Ω : Type*} {Hc : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {ω : Ω} (hc : Continuous fun t => R t ω) (h0 : R 0 ω = 0) (t : ℝ≥0) :
    relDrv t (relVar Hc R V ω) = R t ω := by
  simp only [relDrv, relVar, FCDet.decDrv_enc hc h0]

/-! ### Measurable versions of the relative exploration through a stop -/

/-- The first contact of the physical counterflow (from `∞`) with the flow prefix `α([0, s])`. -/
def gb6Tc {Ω : Type*} (s : ℝ≥0) (γ α : Ω → ℝ≥0 → ℂ) (ω : Ω) : ℝ≥0∞ :=
  firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ)) ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s)

/-- The relative clock `a(t) = hcap(Ψ(K'_t))/2` of one sample. -/
def gb6Clock {Ω : Type*} (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t

/-- **A set of (record, path) pairs determined by the path up to `t`**: membership only depends on the record and on
the path on `[0, t]`. -/
def IsDetUpTo (t : ℝ≥0) (B : Set (RecData × (ℝ≥0 → ℝ))) : Prop :=
  ∀ (r : RecData) (w w' : ℝ≥0 → ℝ), (∀ u ≤ t, w u = w' u) → ((r, w) ∈ B ↔ (r, w') ∈ B)

/-- **A measurable version of GB6's relative exploration through a stop.** `R` is a measurable continuous driver from
`0`, frozen after the measurable stop `V`; `V` is a stopping time of the completed natural filtration of the record of
the flow prefix and of `R` (for every `t`, almost surely `{V ≤ t}` is a measurable event of the record and of the
path on `[0, t]`); almost surely on the interior-tip event `{s < ζα, α(s) ∈ ℍ}`: `V` is positive, `V` precedes the
relative contact (every relative time before `V` is the relative clock of a time before the first contact `T_c`),
and `R` generates the chart images `Ψ(K'_t)` of the counterflow hulls at every relative time `a(t) ≤ V`, `t < T_c`. -/
def IsGB6RelVersion (s : ℝ≥0) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W Wα : ℝ≥0 → Ω → ℝ)
    (ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  (∀ t, Measurable (R t)) ∧ (∀ ω, Continuous fun t => R t ω) ∧ (∀ ω, R 0 ω = 0) ∧
    (∀ ω (t : ℝ≥0), V ω ≤ t → R t ω = R (V ω).toNNReal ω) ∧ Measurable V ∧
    (∀ t : ℝ≥0, ∃ B : Set (RecData × (ℝ≥0 → ℝ)), MeasurableSet B ∧ IsDetUpTo t B ∧
      ∀ᵐ ω ∂P, (V ω ≤ t ↔ (gb6Rec s Wα ζα ω, fun u => R u ω) ∈ B)) ∧
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → 0 < V ω ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → ENNReal.ofReal (gb6Clock s W Wα ω t) ≤ V ω →
        QuantumZipper.fwdHull (fun r : ℝ => R r.toNNReal ω) (gb6Clock s W Wα ω t) =
          relMap (fun r : ℝ => Wα r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) t

/-- **Named input (measurability): exhausting measurable versions of the relative exploration exist.** Binders of
`GB6RelDrvDetStatement`'s setting. There are measurable versions `(R m, V m)` (`IsGB6RelVersion`) such that almost
surely on the interior-tip event every relative clock value before the first contact is below some `V m`. (The
relative driver of one sample exists, `exists_relDriver_of_traces`; this asks for a measurable choice through
stopping times exhausting the pre-contact relative interval.) -/
def GB6RelVersionStatement : Prop :=
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
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ s : ℝ≥0, ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsGB6RelVersion s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω

/-- **Named input: GB6's relative stopped coupling, conditional on the marked prefix** (supplement p. 518–520 and
Astra's follow-up 3, Q3 §§3.1–3.7 for the GB6 configuration: "Conditional on the marked prefix, the portion of `η`
before its first contact with `α[0, σ]`, in the chart of `U` taking `(y, p)` to `(0, ∞)`, is the complete canonical
counterflow of the conditional component field"; Q3: "For each 𝒢-stopping time `S < ζ`, the conditional field outside
`K̃_S`, given `𝒢_S`, is Gaussian with zero-boundary Green covariance and canonical mean (Q3.3)", the relative filled
hull is local, and the relative coordinates satisfy the integrated `SLE_{16/κ}(ρ)` equations (Q3.4)). Binders of
`GB6RelDrvDetStatement`'s setting, a word `c` representing `(b, J)`, and a measurable version `(R, V)` of the relative
exploration through a stop (`IsGB6RelVersion`). For every Markov kernel `K` disintegrating `(record, (Hc, R, V))` on
the record event `gb6TS s` over the record, for almost every record `r`: on `RelSpace × Ω₀`, under `K r ⊗ P₀` (`P₀`
an independent source for the Brownian motion after the stop), the decoded relative driver, read through the first
factor, is a coupling through the stop of the chart field with the counterflow word of `β(r) = gb6WordOfRec κ θ c r`
(`StoppedExtend.IsStoppedHullCoupling`, at `16/κ`, from `0`, angle `0`). -/
def GB6RelStopKernelStatement : Prop :=
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
            ((K r).prod P₀) 𝓕 (fun t p => relDrv t p.1) VL VR B (fun p => relStp p.1) (fun p => relFld p.1)

/-! ### The relative clock of one sample -/

section Sample

variable {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0}

/-- **The relative clock of one sample** (`exists_relDriver_of_traces`' setting, through GB6C's glued chain
`exists_glued_relChain`): before the first contact `T_c` the relative clock starts at `0`, is strictly increasing
and continuous. -/
theorem relClock_props_of_traces (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα})
    (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H) (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w)
    (hw0 : w 0 = 0) :
    relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
        {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} ∧
      ContinuousOn (fun t : ℝ≥0 => relClock (fun r : ℝ => wα r.toNNReal) s (fun r : ℝ => w r.toNNReal) t)
        {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
          ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)} := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Ur : ℝ → ℝ := fun r => wα r.toNNReal with hUr
  set Wr : ℝ → ℝ := fun r => w r.toNNReal with hWr
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs
  set U' : ℝ → ℝ := frozenDrive wα t₂ with hU'def
  have hU' : Continuous U' := continuous_frozenDrive_of_lt hwα ht₂
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans (NNReal.coe_nonneg s) hst₂.le
  have hU'0 : U' 0 = 0 := by rw [hU'def, frozenDrive_zero ht₂0, hwα0]
  have hagree : ∀ r ∈ Icc (0 : ℝ) t₂, Ur r = U' r := fun r hr => (frozenDrive_eq hr).symm
  have hagree_s : ∀ r ∈ Icc (0 : ℝ) s, Ur r = U' r := fun r hr => hagree r ⟨hr.1, hr.2.trans hst₂.le⟩
  have hclock : relClock Ur s Wr = relClock U' s Wr := relClock_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s Wr
  have hhull : QuantumZipper.fwdHull Ur s = QuantumZipper.fwdHull U' s :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have htip : Tendsto (QuantumZipper.fwdMapInv U' s) (𝓝[H] 0) (𝓝 (α s)) := by
    have h1 := IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα hwα0 hs
    have h2 : QuantumZipper.fwdMapInv Ur s = QuantumZipper.fwdMapInv U' s :=
      fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
    rw [← h2]
    exact h1
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U' s))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull Wr T)) := fun T hT => by
    rw [← hhull]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hα hwα hwα0 hγ hw.continuousOn hw0 hs
      ENNReal.coe_lt_top hT
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hTc : 0 < Tc := by
    have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn
      (hα.2.1.mono fun t ht => le_trans (by exact_mod_cast ht.2) hs.le)
    have := firstContactTime_pos hγc.continuousAt hγ.1 hk.isBounded
    rwa [image_image] at this
  have hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → IsFilling (QuantumZipper.fwdHull Wr t) (γ '' Icc 0 t) :=
    fun t _ => hγ.2.2 t ENNReal.coe_lt_top
  obtain ⟨-, -, ha0, hsm, hac, -, -⟩ := exists_glued_relChain hw hw0 hU' hU'0 hs0 htip hTc hd hγK
  refine ⟨by rw [hclock]; exact ha0, ?_, ?_⟩
  · rw [hclock]; exact hsm
  · rw [hclock]; exact hac

end Sample

/-! ### Comparing drivers with the same hulls -/

/-- **Two continuous drivers with the same small hulls start at the same point**: if `W 0 = 0` and the hulls of
`W` and `W'` agree at every time in `(0, δ]`, then `W' 0 = 0` (the hulls of a continuous driver at a small time lie
in a small ball around its starting point, Lawler's Lemma 4.12, `fwdHull_subset_closedBall`, and are nonempty). -/
theorem eq_zero_of_fwdHull_eq_small {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0)
    {δ : ℝ} (hδ : 0 < δ) (h : ∀ u ∈ Ioc (0 : ℝ) δ, QuantumZipper.fwdHull W u = QuantumZipper.fwdHull W' u) :
    W' 0 = 0 := by
  by_contra hc
  set c := W' 0 with hcdef
  have hcpos : 0 < |c| := abs_pos.2 hc
  set ε : ℝ := |c| / 3 with hεdef
  have hε : 0 < ε := by positivity
  set U : ℝ → ℝ := fun r => W' r - c with hUdef
  have hU : Continuous U := hW'.sub continuous_const
  have hU0 : U 0 = 0 := by simp only [hUdef, hcdef, sub_self]
  obtain ⟨δ₁, hδ₁, hW1⟩ := Metric.continuousAt_iff.1 hW.continuousAt (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hU1⟩ := Metric.continuousAt_iff.1 hU.continuousAt (ε / 2) (by positivity)
  set u : ℝ := min (min δ (δ₁ / 2)) (min (δ₂ / 2) ((ε / 6) ^ 2)) with hudef
  have hu0 : 0 < u := by positivity
  have huδ : u ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have huδ₁ : u < δ₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (by linarith)
  have huδ₂ : u < δ₂ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have husq : 3 * Real.sqrt u ≤ ε / 2 := by
    have h1 : u ≤ (ε / 6) ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
    have h2 : Real.sqrt u ≤ ε / 6 := by
      rw [show ε / 6 = Real.sqrt ((ε / 6) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt h1
    linarith
  have hWb : ∀ r ∈ Icc (0 : ℝ) u, |W r| ≤ ε / 2 := fun r hr => by
    have := hW1 (x := r) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]; exact lt_of_le_of_lt hr.2 huδ₁)
    rw [Real.dist_eq, hW0, sub_zero] at this
    exact this.le
  have hUb : ∀ r ∈ Icc (0 : ℝ) u, |U r| ≤ ε / 2 := fun r hr => by
    have := hU1 (x := r) (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]; exact lt_of_le_of_lt hr.2 huδ₂)
    rw [Real.dist_eq, hU0, sub_zero] at this
    exact this.le
  have hK1 := QuantumZipper.CaraR.fwdHull_subset_closedBall hW hu0 hWb
  have hK2 := QuantumZipper.CaraR.fwdHull_subset_closedBall hU hu0 hUb
  obtain ⟨z, hz⟩ := QuantumZipper.CaraR.fwdHull_nonempty hW hW0 hu0
  have hz' : z ∈ QuantumZipper.fwdHull W' u := by rw [← h u ⟨hu0, huδ⟩]; exact hz
  have hW'eq : W' = fun r => U r + c := funext fun r => by simp only [hUdef, sub_add_cancel]
  rw [hW'eq, ConformalImageFull.fwdHull_add_const] at hz'
  obtain ⟨y, hy, hyz⟩ := hz'
  have h1 : ‖z‖ ≤ ε / 2 + 3 * Real.sqrt u := by
    have := hK1 hz
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have h2 : ‖y‖ ≤ ε / 2 + 3 * Real.sqrt u := by
    have := hK2 hy
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hcz : (c : ℂ) = z - y := by rw [← hyz]; ring
  have h3 : |c| ≤ ‖z‖ + ‖y‖ := by
    have : ‖(c : ℂ)‖ = |c| := Complex.norm_real c
    rw [← this, hcz]
    exact norm_sub_le z y
  linarith

/-- **Pathwise comparison.** Let `a` be a clock that starts at `0`, is strictly increasing and continuous before `T`,
and let a good code `p` match drivers `R m` (continuous, from `0`) before stops `V m` that exhaust the clock values
before `T`, each `R m` generating the hulls `K t` at `a(t) ≤ V m`. Then the decoded driver of `p` agrees with every
driver `W'` that is continuous before the clock's range and generates the hulls `K t` at `a(t)`, on `[0, a(t)]` for
every `t < T`. -/
theorem drvDec_eq_of_isStopDrvMatch_family {p : PCode × ℝ≥0∞} (hp : IsGoodDrvCode p) {R : ℕ → ℝ≥0 → ℝ}
    (hRc : ∀ m, Continuous (R m)) (hR0 : ∀ m, R m 0 = 0) {V : ℕ → ℝ≥0∞}
    (hm : ∀ m, IsStopDrvMatch p (R m) (V m)) {a : ℝ≥0 → ℝ} {T : ℝ≥0∞} (ha0 : a 0 = 0)
    (hsm : StrictMonoOn a {t | (t : ℝ≥0∞) < T}) (hac : ContinuousOn a {t | (t : ℝ≥0∞) < T})
    {K : ℝ≥0 → Set ℂ}
    (hRK : ∀ m (t : ℝ≥0), (t : ℝ≥0∞) < T → ENNReal.ofReal (a t) ≤ V m →
      QuantumZipper.fwdHull (fun r : ℝ => R m r.toNNReal) (a t) = K t)
    (hexh : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∃ m, ENNReal.ofReal (a t) < V m) {W' : ℝ≥0 → ℝ}
    (hW'c : ContinuousOn W' {u | ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ (u : ℝ) < a t})
    (hW'K : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal) (a t) = K t) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ∀ u : ℝ≥0, (u : ℝ) ≤ a t → drvDec p u = W' u := by
  intro t ht u hu
  obtain ⟨t₁, htt₁, ht₁T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨t₂, ht₁t₂, ht₂T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₁T
  have htt₁' : t < t₁ := by exact_mod_cast htt₁
  have ht₁t₂' : t₁ < t₂ := by exact_mod_cast ht₁t₂
  have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < T := lt_of_le_of_lt (by simp) ht
  have hnn : ∀ r : ℝ≥0, (r : ℝ≥0∞) < T → 0 ≤ a r := fun r hr => by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h | h
    · rw [← h, ha0]
    · rw [← ha0]; exact (hsm h0T hr h).le
  have hat₁ : a t < a t₁ := hsm ht ht₁T htt₁'
  have hat₂ : a t₁ < a t₂ := hsm ht₁T ht₂T ht₁t₂'
  obtain ⟨m, hmV⟩ := hexh t₂ ht₂T
  have hle : ∀ r : ℝ≥0, r ≤ t₂ → (r : ℝ≥0∞) < T := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht₂T
  -- the code is `R m` before `V m`
  have hcode : drvDec p u = R m u := by
    refine eqOn_drvDec_of_isStopDrvMatch hp (hRc m).continuousOn (hm m) u ?_
    have hu' : (u : ℝ) < a t₂ := lt_of_le_of_lt hu (hat₁.trans hat₂)
    calc (u : ℝ≥0∞) = ENNReal.ofReal (u : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
      _ < ENNReal.ofReal (a t₂) := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (NNReal.coe_nonneg u)).2 hu'
      _ < V m := hmV
  -- `W'` frozen after `a(t₂)` is continuous
  have hat₂0 : 0 ≤ a t₂ := hnn t₂ ht₂T
  set c : ℝ≥0 := ⟨a t₂, hat₂0⟩ with hcdef
  set W'' : ℝ≥0 → ℝ := fun v => W' (min v c) with hW''def
  have hsub : Iic c ⊆ {u : ℝ≥0 | ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ (u : ℝ) < a t} := by
    intro v hv
    obtain ⟨t₃, ht₂t₃, ht₃T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₂T
    have ht₂t₃' : t₂ < t₃ := by exact_mod_cast ht₂t₃
    refine ⟨t₃, ht₃T, lt_of_le_of_lt ?_ (hsm ht₂T ht₃T ht₂t₃')⟩
    have hvc : v ≤ c := hv
    exact_mod_cast hvc
  have hW''c : Continuous W'' :=
    (hW'c.mono hsub).comp_continuous (continuous_id.min continuous_const) fun v => min_le_right v c
  have hW''eq : ∀ v : ℝ≥0, (v : ℝ) ≤ a t₂ → W'' v = W' v := fun v hv => by
    have hvc : v ≤ c := by
      show (v : ℝ) ≤ (c : ℝ)
      exact hv
    simp only [hW''def, min_eq_left hvc]
  -- the hulls of `W''` at the clock values up to `a(t₁)`
  have hW''K : ∀ r : ℝ≥0, r ≤ t₁ →
      QuantumZipper.fwdHull (fun x : ℝ => W'' x.toNNReal) (a r) = K r := by
    intro r hr
    have hrT : (r : ℝ≥0∞) < T := hle r (hr.trans ht₁t₂'.le)
    rw [← hW'K r hrT]
    have har : a r < a t₂ := by
      rcases eq_or_lt_of_le hr with h | h
      · rw [h]; exact hat₂
      · exact (hsm hrT ht₁T h).trans hat₂
    refine fwdHull_eq_of_eqOn (hnn r hrT) har fun x hx => ?_
    have hx' : (x.toNNReal : ℝ) ≤ a t₂ := by rw [Real.coe_toNNReal _ hx.1]; exact hx.2
    exact hW''eq _ hx'
  have hRK' : ∀ r : ℝ≥0, r ≤ t₁ → QuantumZipper.fwdHull (fun x : ℝ => R m x.toNNReal) (a r) = K r := by
    intro r hr
    have hrT : (r : ℝ≥0∞) < T := hle r (hr.trans ht₁t₂'.le)
    refine hRK m r hrT ?_
    have har : a r < a t₂ := by
      rcases eq_or_lt_of_le hr with h | h
      · rw [h]; exact hat₂
      · exact (hsm hrT ht₁T h).trans hat₂
    exact ((ENNReal.ofReal_le_ofReal har.le).trans_lt hmV).le
  -- the clock on `[0, t₁]`, read on `ℝ`
  set σ : ℝ → ℝ := fun r => a r.toNNReal with hσdef
  have hσ0 : σ 0 = 0 := by simp only [hσdef, Real.toNNReal_zero, ha0]
  have hIcc : ∀ r ∈ Icc (0 : ℝ) t₁, r.toNNReal ≤ t₁ := fun r hr => by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
  have hσm : MonotoneOn σ (Icc 0 (t₁ : ℝ)) := by
    intro x hx y hy hxy
    exact hsm.monotoneOn (hle _ ((hIcc x hx).trans ht₁t₂'.le)) (hle _ ((hIcc y hy).trans ht₁t₂'.le))
      (Real.toNNReal_le_toNNReal hxy)
  have hσc : ContinuousOn σ (Icc 0 (t₁ : ℝ)) := by
    refine hac.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
    exact hle _ ((hIcc r hr).trans ht₁t₂'.le)
  have hσnn : ∀ r ∈ Icc 0 (t₁ : ℝ), 0 ≤ σ r := fun r hr => hnn _ (hle _ ((hIcc r hr).trans ht₁t₂'.le))
  have hhull : ∀ r ∈ Icc 0 (t₁ : ℝ), QuantumZipper.fwdHull (fun x : ℝ => R m x.toNNReal) (σ r) =
      QuantumZipper.fwdHull (fun x : ℝ => W'' x.toNNReal) (σ r) := fun r hr => by
    simp only [hσdef]
    rw [hRK' _ (hIcc r hr), hW''K _ (hIcc r hr)]
  -- `W''` starts at `0`
  have hRc' : Continuous fun x : ℝ => R m x.toNNReal := (hRc m).comp continuous_real_toNNReal
  have hW''c' : Continuous fun x : ℝ => W'' x.toNNReal := hW''c.comp continuous_real_toNNReal
  have hR0' : (fun x : ℝ => R m x.toNNReal) 0 = 0 := by simp only [Real.toNNReal_zero, hR0 m]
  have ht₁pos : 0 < a t₁ := by
    rw [← ha0]
    exact hsm h0T ht₁T (lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t) htt₁')
  have hW''0 : (fun x : ℝ => W'' x.toNNReal) 0 = 0 := by
    refine eq_zero_of_fwdHull_eq_small hRc' hW''c' hR0' ht₁pos fun v hv => ?_
    -- every small capacity time is a clock value (intermediate value theorem)
    obtain ⟨r, hr, hrv⟩ := intermediate_value_Icc (NNReal.coe_nonneg t₁) hσc
      (show v ∈ Icc (σ 0) (σ t₁) by
        rw [hσ0]
        refine ⟨hv.1.le, ?_⟩
        simp only [hσdef, Real.toNNReal_coe]
        exact hv.2)
    rw [← hrv]
    exact hhull r hr
  obtain ⟨-, hEq⟩ := Sec6.eqOn_clock_and_driver_of_fwdHull_eq hRc' hW''c' hR0' hW''0 (NNReal.coe_nonneg t₁)
    hσ0 hσm hσc hσnn hhull
  have hut : (u : ℝ) ∈ Icc 0 (σ t₁) := by
    refine ⟨NNReal.coe_nonneg u, ?_⟩
    simp only [hσdef, Real.toNNReal_coe]
    exact hu.trans hat₁.le
  have h1 := hEq hut
  simp only [Real.toNNReal_coe] at h1
  rw [hcode, h1]
  exact hW''eq u (hu.trans (hat₁.trans hat₂).le)

/-! ### The stopped driver match of a version, from the conditional coupling -/

/-- **The stopped driver match of a measurable version** (`GB6RelStopKernelStatement` + Aux. lemma 54 + the canonical
driver code). Disintegrate `(record, relVar Hc R V)` on the record event over the record; under almost every
conditional law the relative exploration is a coupling through the stop of the conditional word, so the stopped
driver match holds there (`ae_isStopDrvMatch_of_isStoppedHullCoupling` on `RelSpace × Ω₀`, then the first factor);
the match is a measurable event of `(record, relVar)` and integrates back to `P`. -/
theorem ae_isStopDrvMatch_of_version (hK : GB6RelStopKernelStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2) (hext : StoppedHullExtendStatement.{0} (16 / κ))
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
    obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕, VL, VR, B, hSC⟩ := hr
    have hd := ae_isStopDrvMatch_of_isStoppedHullCoupling hext hF (gb6WordOfRec κ θ c r)
      (Ω := RelSpace × Ω₀) (Q := (K r).prod P₀) (Hc := fun p => relFld p.1) (X := fun p => relFld p.1)
      (fun p => Sec7.StripSysField.isTranslateAddConst_zero_self _ _) hSC (Wb := fun t p => relDrv t p.1)
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

/-! ### GB6's (Det) in driver form -/

/-- **GB6's (Det) in driver form from the relative stopped coupling.** Aux. lemma 54 (`StoppedHullExtendStatement`,
universe `0`, at every parameter `k > 4`; it is used at `16/κ`), exhausting measurable versions of the relative
exploration (`GB6RelVersionStatement`) and GB6's relative stopped coupling conditional on the marked prefix
(`GB6RelStopKernelStatement`) give `GB6RelDrvDetStatement`. Almost surely: the canonical code is good
(`ae_isGoodDrvCode_gb6`); for each version it matches the version's driver before its stop
(`ae_isStopDrvMatch_of_version`); the versions generate the chart images of the counterflow hulls and exhaust the
pre-contact relative interval; so the decoded code agrees with every continuous generator of those chart images
(`drvDec_eq_of_isStopDrvMatch_family`, with the relative clock of `relClock_props_of_traces`). -/
theorem gb6RelDrvDetStatement_of_stopKernel (hext : ∀ k : ℝ, 4 < k → StoppedHullExtendStatement.{0} k)
    (hV : GB6RelVersionStatement.{u}) (hK : GB6RelStopKernelStatement.{u}) : GB6RelDrvDetStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc F hF c hcJ hcb
  have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  obtain ⟨R, V, hver, hexh⟩ :=
    hV κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hcomp hfl hα s
  have hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s →
      IsStopDrvMatch (F (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω), Hc ω)) (fun t => R m t ω) (V m ω) := fun m =>
    ae_isStopDrvMatch_of_version hK hκ hκ4 hθ₁ hθ₂ (hext _ hκ') hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s hHcm
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

end InteractingSLE.Supp8.GB6.RelDrv
