/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentGRule
import InteractingSLE.Spec.Sec2.TerminalPath
import InteractingSLE.Spec.Coupling.WFSTargets

/-!
# (L1G) from (L1) with its lifetime clause: the Galmarino rule of the exit stop

Packet PROVE-L1G. `StoppedExtendWF.FlowLineStopIdentGStatement` ((L1G), PROVE-DOMAINMARKOV10 §4.3) is
PROVE-DOMAINMARKOV9's (L1) with the stop `e = RLC.exitTime V Γ U` read from the killed history by a measurable
Galmarino rule. `FlowStopIdentGRule` shows that the rule proposed for it, `min (γ.1, exit time)`, is not Galmarino
(capped rules are trivial). The stop `e = min (U, X)` (`U` the lifetime of the flow line `Γ` of `H₀`, `X` its exit time
from `V`) is read from the history in two parts:

* where `Γ (e) ∉ V`, `e` is the first time the trace read from the history (`histTrace y`) hits the closed set `Vᶜ`;
* where `Γ (e) ∈ V`, `e` is the lifetime `U`. The rule then reads `e` as the first time the state read from the
  history (`histState`) reaches the continuation threshold of the word of `(bR, Ĵ)` (`thrSet`).

The second part needs a fact that (L1) alone does not give: at a stop that is not an exit, the state of the stopped
`(bR, Ĵ)`-evolution is a threshold state. Mathematically this is the locality of the continuation threshold: the
colliding marks lie between the seed and a hit point in `V`, and `b = bR` on `O ⊇ V ∩ ℝ`. This file names (L1) with
that clause as one input and proves everything else:

* `IsStoppedFlowLineL`: PROVE-DOMAINMARKOV9's `IsStoppedFlowLine`, plus the **lifetime clause**: almost surely, if the
  path at the stop is still in `V`, the state at the stop is a threshold state;
* `FlowLineStopIdentLStatement` (**named input**): (L1) with `IsStoppedFlowLineL` in place of `IsStoppedFlowLine`;
* `flowRule`: the rule (`0` when the stop is identically `0`, otherwise the minimum of the exit and threshold first-hit
  rules); `measurable_flowRule`, `isStrongGalmarino_flowRule`;
* `flowRule_killedHistory`: the pathwise identity `e = flowRule (killed history at e)`;
* `hitRuleSeq_thrSet_killedHistory_lifetime`: the threshold rule reads the lifetime of an integrated path whose state is
  continuous at a finite lifetime (for the stops "first contact, or the lifetime" of G7, Lemma 7.6 and GB6);
* **`flowLineStopIdentGStatement_of_L`**: (L1G) from the named input;
* `flowLineStopIdentStatement_of_L`: DM9's (L1) from it;
* **`flowLocalityStatement_of_stopIdentL_through`**: `RLC.FlowLocalityStatement` from the named input, the WFS kernel
  target (`WFS.ThroughKernelStatement`, PROVE-WFS-A and later) and Theorems 1.2–1.3 (as hypotheses).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace FlowStopIdentG

open LawUnique StoppedExtend StoppedExtendWF Exist.Staged

variable {nL nR : ℕ}

/-! ### The rule -/

open Classical in
/-- **The Galmarino rule of the exit stop**: `0` when `c₀` holds (the stop is then `0`); otherwise the minimum of the
first hit of `Vᶜ` by the trace read from the history (seed `y`) and the first hit of the continuation threshold of the
weights `(ρL; ρR)` by the state read from the history. -/
def flowRule (c₀ : Prop) (y : ℝ) (V : Set ℂ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    HistorySpace nL nR → ℝ≥0∞ :=
  if c₀ then fun _ => 0 else
    fun γ => min (hitRule (histTrace y) Vᶜ γ) (hitRuleSeq histState (thrSet ρL ρR) γ)

theorem measurable_flowRule (c₀ : Prop) (y : ℝ) (V : Set ℂ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Measurable (flowRule c₀ y V ρL ρR) := by
  unfold flowRule
  split_ifs
  · exact measurable_const
  · exact (measurable_hitRule (fun _ => measurable_histTrace y _) _).min
      (measurable_hitRuleSeq (fun _ => measurable_histState _) _)

theorem isStrongGalmarino_flowRule (c₀ : Prop) (y : ℝ) (V : Set ℂ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    IsStrongGalmarino (flowRule c₀ y V ρL ρR) := by
  unfold flowRule
  split_ifs
  · exact isStrongGalmarino_const 0
  · exact (isStrongGalmarino_hitRule (isNonAnticipating_histTrace y) _).min
      (isStrongGalmarino_hitRuleSeq isNonAnticipating_histState _)

theorem isHistGalmarino_flowRule (c₀ : Prop) (y : ℝ) (V : Set ℂ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    IsHistGalmarino (flowRule c₀ y V ρL ρR) :=
  (isStrongGalmarino_flowRule c₀ y V ρL ρR).isHistGalmarino

/-- Before the exit stop, the path is in `V`. -/
theorem mem_of_lt_exitTime {V : Set ℂ} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < RLC.exitTime V Γ U) : Γ s ∈ V := by
  by_contra hns
  have h : RLC.exitTime V Γ U ≤ s := (min_le_right _ _).trans (iInf₂_le s hns)
  exact absurd hs (not_lt.2 h)

/-- **The rule reads the exit stop from the killed history.** Fix a sample. Suppose the processes before the stop
`e = exitTime V Γ U` form a local path of the force word, that the state is continuous on `[0, e]` when `e` is finite,
that the driver generates `Γ − y` through `e`, and that the lifetime clause holds. Suppose also that `e = 0` when `c₀`
holds and `e > 0` otherwise. Then `e` is the rule's value on the history killed at `e`. -/
theorem flowRule_killedHistory {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {ω : Ω} {c₀ : Prop} {y : ℝ} {V : Set ℂ} (hV : IsOpen V) {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (hpath : Sec2.IsSLEPathUpTo κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (e ω))
    (hcont : ∀ T : ℝ≥0, (T : ℝ≥0∞) = e ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T))
    (hgen : IsGeneratingTrace (fun t => W t ω) (e ω) (fun t => Γ t - y))
    (hlife : ∀ T : ℝ≥0, (T : ℝ≥0∞) = e ω → Γ T ∈ V →
      ForceWord.ThresholdCondition ρL ρR (W T ω) (fun i => VL i T ω) (fun j => VR j T ω))
    (he : e ω = RLC.exitTime V Γ U) (hc0 : c₀ → e ω = 0) (hpos : ¬ c₀ → 0 < e ω) :
    e ω = flowRule c₀ y V ρL ρR (killedHistory W VL VR e ω) := by
  by_cases hc : c₀
  · rw [hc0 hc]
    unfold flowRule
    rw [ite_eq_left hc]
  · have he0 := hpos hc
    have hR : flowRule c₀ y V ρL ρR (killedHistory W VL VR e ω) =
        min (hitRule (histTrace y) Vᶜ (killedHistory W VL VR e ω))
          (hitRuleSeq histState (thrSet ρL ρR) (killedHistory W VL VR e ω)) := by
      unfold flowRule
      rw [ite_eq_right hc]
    rw [hR]
    set γ := killedHistory W VL VR e ω with hγ
    have hγ1 : γ.1 = e ω := rfl
    have hstc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) {t | (t : ℝ≥0∞) < e ω} :=
      hpath.continuousOn_w.prodMk ((continuousOn_pi.2 hpath.continuousOn_vL).prodMk
        (continuousOn_pi.2 hpath.continuousOn_vR))
    have hψT : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < e ω → histTrace y γ (dyadicTime p) = Γ (dyadicTime p) :=
      fun p hp => histTrace_killedHistory hstc hpath.w_zero hgen hp
    have hψS : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < e ω →
        histState γ (dyadicTime p) = (W (dyadicTime p) ω, fun i => VL i (dyadicTime p) ω,
          fun j => VR j (dyadicTime p) ω) :=
      fun p hp => histState_killedHistory hstc hp
    have hΓc : ContinuousOn Γ {t | (t : ℝ≥0∞) ≤ e ω} := by
      have h := hgen.2.1.add (continuousOn_const (c := (y : ℂ)))
      exact h.congr fun t _ => (sub_add_cancel (Γ t) (y : ℂ)).symm
    have hin : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e ω → Γ s ∈ V := fun s hs => mem_of_lt_exitTime (he ▸ hs)
    have hoffS : ∀ m, ∀ s : ℝ≥0, (s : ℝ≥0∞) < e ω →
        (W s ω, fun i => VL i s ω, fun j => VR j s ω) ∉ thrSet ρL ρR m :=
      fun m s hs hm => hpath.not_threshold hs (thresholdCondition_of_mem_thrSet hm)
    have hT1 : e ω ≤ hitRule (histTrace y) Vᶜ γ :=
      le_hitRule_of_off hV.isClosed_compl
        (hΓc.mono fun t (ht : (t : ℝ≥0∞) < e ω) => show (t : ℝ≥0∞) ≤ e ω from le_of_lt ht)
        (fun s hs hns => hns (hin s hs)) (fun p hp _ => hψT p hp)
    have hS1 : e ω ≤ hitRuleSeq histState (thrSet ρL ρR) γ :=
      le_hitRuleSeq_of_off (isClosed_thrSet ρL ρR) hstc hoffS (fun p hp _ => hψS p hp)
    rcases eq_top_or_lt_top (e ω) with htop | hlt
    · rw [htop] at hT1 hS1 ⊢
      rw [top_le_iff.1 hT1, top_le_iff.1 hS1, min_self]
    · set T : ℝ≥0 := (e ω).toNNReal with hTdef
      have hT : (T : ℝ≥0∞) = e ω := ENNReal.coe_toNNReal hlt.ne
      have hTpos : 0 < T := by
        rw [← ENNReal.coe_pos, hT]
        exact he0
      have hγT : γ.1 = T := hγ1.trans hT.symm
      have hlt' : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < e ω := fun s hs => hT ▸ ENNReal.coe_lt_coe.2 hs
      by_cases hΓT : Γ T ∈ V
      · obtain ⟨m₀, hm₀⟩ := exists_mem_thrSet (s := (W T ω, fun i => VL i T ω, fun j => VR j T ω)) (hlife T hT hΓT)
        have hS : hitRuleSeq histState (thrSet ρL ρR) γ = T :=
          hitRuleSeq_eq_of_hit (isClosed_thrSet ρL ρR) hTpos hγT (hcont T hT)
            (fun m s hs => hoffS m s (hlt' s hs)) hm₀ (fun p hp => hψS p (hT ▸ hp))
        rw [hS, hT, min_eq_right hT1]
      · have hTc : ContinuousOn Γ (Iic T) :=
          hΓc.mono fun t ht => hT ▸ ENNReal.coe_le_coe.2 (show t ≤ T from ht)
        have hE : hitRule (histTrace y) Vᶜ γ = T :=
          hitRule_eq_of_hit hV.isClosed_compl hTpos hγT hTc (fun s hs hns => hns (hin s (hlt' s hs))) hΓT
            (fun p hp => hψT p (hT ▸ hp))
        rw [hE, hT, min_eq_left hS1]

/-! ### The threshold rule reads the lifetime of an integrated path -/

/-- **The threshold rule reads the lifetime** of an integrated path whose state is continuous at a finite lifetime (and
the lifetime is positive): on the history killed at the lifetime, `hitRuleSeq histState (thrSet ρL ρR)` is the lifetime.
Combined with a contact rule by `min`, this is the Galmarino form of the stops "first contact, or the lifetime" of
Lemma G7, Lemma 7.6 and GB6 (capping at the history's lifetime would be trivial, `not_isHistGalmarino_of_le_fst`). -/
theorem hitRuleSeq_thrSet_killedHistory_lifetime {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω))
    (hcont : ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T))
    (hpos : 0 < ζ ω) : hitRuleSeq histState (thrSet ρL ρR) (killedHistory W VL VR ζ ω) = ζ ω := by
  have hfp := hp.isForcePath
  have hstc : ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) {t | (t : ℝ≥0∞) < ζ ω} :=
    hfp.continuousOn_w.prodMk ((continuousOn_pi.2 hfp.continuousOn_vL).prodMk (continuousOn_pi.2 hfp.continuousOn_vR))
  have hoff : ∀ m, ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω →
      (W s ω, fun i => VL i s ω, fun j => VR j s ω) ∉ thrSet ρL ρR m :=
    fun m s hs hm => hfp.not_threshold hs (thresholdCondition_of_mem_thrSet hm)
  have hψS : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < ζ ω →
      histState (killedHistory W VL VR ζ ω) (dyadicTime p) =
        (W (dyadicTime p) ω, fun i => VL i (dyadicTime p) ω, fun j => VR j (dyadicTime p) ω) :=
    fun p hp => histState_killedHistory hstc hp
  have hge : ζ ω ≤ hitRuleSeq histState (thrSet ρL ρR) (killedHistory W VL VR ζ ω) :=
    le_hitRuleSeq_of_off (isClosed_thrSet ρL ρR) hstc hoff (fun p hp _ => hψS p hp)
  rcases eq_top_or_lt_top (ζ ω) with htop | hlt
  · rw [htop] at hge ⊢
    exact top_le_iff.1 hge
  · set T : ℝ≥0 := (ζ ω).toNNReal with hTdef
    have hT : (T : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hlt.ne
    have hTpos : 0 < T := by
      rw [← ENNReal.coe_pos, hT]
      exact hpos
    have htend : Tendsto (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (𝓝[<] T)
        (𝓝 (W T ω, fun i => VL i T ω, fun j => VR j T ω)) :=
      ((hcont T hT) T self_mem_Iic).tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
    obtain ⟨m₀, hm₀⟩ := exists_mem_thrSet (s := (W T ω, fun i => VL i T ω, fun j => VR j T ω))
      (hfp.threshold_of_tendsto hTpos hT htend)
    rw [← hT]
    exact hitRuleSeq_eq_of_hit (isClosed_thrSet ρL ρR) hTpos hT.symm (hcont T hT)
      (fun m s hs => hoff m s (hT ▸ ENNReal.coe_lt_coe.2 hs)) hm₀ (fun p hp => hψS p (hT ▸ hp))

/-! ### (L1) with the lifetime clause -/

/-- **A flow line through a stop with the lifetime clause**: PROVE-DOMAINMARKOV9's `IsStoppedFlowLine` (translate,
stopped hull coupling through `e`, generating trace through `e`), and almost surely: if the path at the (finite) stop is
still in `V`, the state at the stop is a threshold state of the flow-line word. -/
def IsStoppedFlowLineL (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ) (V : Set ℂ) {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ)
    (e : Ω → ℝ≥0∞) : Prop :=
  ∃ (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ),
    (∀ ω, IsTranslateAddConst x (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
    IsStoppedHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
      (flowLineRhoR κ b jumps x θ) P 𝓕 W VL VR B e h' ∧
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (e ω) (fun t => η ω t - x)) ∧
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = e ω → η ω T ∈ V →
      ForceWord.ThresholdCondition (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) (W T ω)
        (fun i => VL i T ω) (fun j => VR j T ω)

/-- Forgetting the lifetime clause. -/
theorem IsStoppedFlowLineL.isStoppedFlowLine {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x : ℝ} {V : Set ℂ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ}
    {e : Ω → ℝ≥0∞} (hfl : IsStoppedFlowLineL κ b jumps x θ V P h η e) : IsStoppedFlowLine κ b jumps x θ P h η e := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen, -⟩ := hfl
  exact ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen⟩

/-- **Named input (L1) with the lifetime clause**: in `RLC.FlowLocalityStatement`'s setting, the flow line `Γ` of `H₀`
(data `b`, under `Q₀`), stopped at its exit time from `V`, is under `Q` a stopped flow line of `Ĥ` with the data
`(bR, Ĵ)` (PROVE-DOMAINMARKOV9's `FlowLineStopIdentStatement`), **and** almost surely, when the path at the stop is
still in `V` (the stop is the lifetime `U`, not an exit), the `(bR, Ĵ)`-state at the stop is a threshold state (the
locality of the continuation threshold). -/
def FlowLineStopIdentLStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b bR : ℝ → ℝ) (J Ĵ : Finset ℝ), IsPiecewiseConstantBoundaryData b J →
    IsPiecewiseConstantBoundaryData bR Ĵ → ∀ O : Set ℝ, IsOpen O → (∀ x ∈ O, b x = bR x) →
    ∀ N : Set ℂ, IsOpen N → (∀ z ∈ N, z.im = 0 → z.re ∈ O) →
    ∀ V : Set ℂ, IsOpen V → Bornology.IsBounded V → closure V ⊆ N → ∀ y θ : ℝ,
    ∀ {S : Type u} [MeasurableSpace S] (Q₀ Q : Measure S) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q],
      Q₀ ≪ Q → Q ≪ Q₀ →
    ∀ (H₀ Ĥ : S → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ b J →
      IsGFFWithBoundaryData Q Ĥ bR Ĵ →
      (∀ (x : S) (φ : TestOn upperHalfPlaneOpens), tsupport φ ⊆ N → Ĥ x φ = H₀ x φ) →
    ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), IsFlowLine κ b J y θ Q₀ H₀ Γ U →
      IsStoppedFlowLineL κ bR Ĵ y θ V Q Ĥ Γ fun x => RLC.exitTime V (Γ x) (U x)

/-! ### (L1G) -/

/-- The seed condition: the stop is `0` exactly when the seed is outside `V` or the initial word of `(b, J)` at angle
`θ` is at the continuation threshold. -/
def SeedStop (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (y θ : ℝ) (V : Set ℂ) : Prop :=
  (y : ℂ) ∉ V ∨ ForceWord.ThresholdCondition (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) 0
    (flowLineXL b J y) (flowLineXR b J y)

/-- The exit stop of a flow line vanishes under the seed condition and is positive otherwise (pathwise, from the frozen
path conditions of `(b, J)` and the generating trace through the lifetime). -/
theorem exitTime_seed {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {y θ : ℝ} {V : Set ℂ} (hV : IsOpen V)
    {w : ℝ≥0 → ℝ} {vL : Fin (flowLineNL b J y) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR b J y) → ℝ≥0 → ℝ}
    {β : ℝ≥0 → ℝ} {U : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}
    (hp : IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y) (flowLineRhoL κ b J y θ)
      (flowLineRhoR κ b J y θ) w vL vR β U)
    (hg : IsGeneratingTrace w U fun t => Γ t - y) :
    (SeedStop κ b J y θ V → RLC.exitTime V Γ U = 0) ∧ (¬ SeedStop κ b J y θ V → 0 < RLC.exitTime V Γ U) := by
  have hfp := hp.isForcePath
  have hΓ0 : Γ 0 = y := sub_eq_zero.1 hg.1
  have hinit : (0 : ℝ≥0∞) < U →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) 0
        (flowLineXL b J y) (flowLineXR b J y) := fun hU => by
    have h := hfp.not_threshold (t := 0) (by simpa using hU)
    rwa [hfp.w_zero, show (fun i => vL i 0) = flowLineXL b J y from funext hfp.vL_zero,
      show (fun i => vR i 0) = flowLineXR b J y from funext hfp.vR_zero] at h
  constructor
  · rintro (hy | hthr)
    · refine le_antisymm ((min_le_right _ _).trans (iInf₂_le 0 ?_)) zero_le
      rw [hΓ0]
      exact hy
    · have hU : U = 0 := by
        by_contra hU
        exact hinit (pos_iff_ne_zero.2 hU) hthr
      exact le_antisymm ((min_le_left _ _).trans hU.le) zero_le
  · intro hs
    rw [SeedStop, not_or, not_not] at hs
    have hU : 0 < U := pos_iff_ne_zero.2 fun h0 => hs.2 (hfp.threshold_of_eq_zero h0)
    -- the path stays in `V` near `0`
    have hnhd : {t : ℝ≥0 | (t : ℝ≥0∞) < U} ∈ 𝓝 (0 : ℝ≥0) :=
      (isOpen_Iio.preimage ENNReal.continuous_coe).mem_nhds (by simpa using hU)
    have hca : ContinuousAt Γ 0 := by
      have h1 : ContinuousAt (fun t => Γ t - y) 0 :=
        hg.2.1.continuousAt (mem_of_superset hnhd fun t (ht : (t : ℝ≥0∞) < U) =>
          show (t : ℝ≥0∞) ≤ U from le_of_lt ht)
      have h2 := h1.add (continuousAt_const (y := (y : ℂ)))
      have e : ((fun t => Γ t - y) + fun _ => (y : ℂ)) = Γ := by
        funext t
        simp only [Pi.add_apply, sub_add_cancel]
      rwa [e] at h2
    have hV0 : Γ ⁻¹' V ∈ 𝓝 (0 : ℝ≥0) := hca.preimage_mem_nhds (hV.mem_nhds (by rw [hΓ0]; exact hs.1))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hV0 hnhd)
    have hεU : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
    refine lt_min hU (lt_of_lt_of_le hεU (le_iInf₂ fun s hs' => ?_))
    by_contra hlt
    push Not at hlt
    have hsε : (s : ℝ) < ε := by simpa using hlt
    have hmem : s ∈ Metric.ball (0 : ℝ≥0) ε := by
      rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg s.coe_nonneg]
      exact hsε
    exact hs' (hball hmem).1

/-- **(L1G) from (L1) with the lifetime clause.** The rule is `flowRule` with the seed condition of `(b, J)` and the
weights of `(bR, Ĵ)`. -/
theorem flowLineStopIdentGStatement_of_L (hL : FlowLineStopIdentLStatement.{u}) :
    FlowLineStopIdentGStatement.{u} := by
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ S _ Q₀ Q _ _ hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr Γ U hΓ
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hSC, hgen, hlife⟩ :=
    hL κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN y θ Q₀ Q hQ₀Q hQQ₀ H₀ Ĥ hH₀ hĤ hagr Γ U hΓ
  obtain ⟨h₀', 𝓕₀, W₀, VL₀, VR₀, B₀, -, hC₀, hgen₀⟩ := hΓ
  have hpath₀ := hQQ₀.ae_le hC₀.1.2.2.2.2
  have hgen₀' := hQQ₀.ae_le hgen₀
  set e : S → ℝ≥0∞ := fun x => RLC.exitTime V (Γ x) (U x) with he
  set R := flowRule (SeedStop κ b J y θ V) y V (flowLineRhoL κ bR Ĵ y θ) (flowLineRhoR κ bR Ĵ y θ) with hRdef
  have hR : ∀ᵐ x ∂Q, e x = R (killedHistory W VL VR e x) := by
    filter_upwards [hSC.1.ae_path, hSC.2.1, hgen, hlife, hpath₀, hgen₀'] with x hp hc hg hl hp₀ hg₀
    have hs := exitTime_seed (θ := θ) hV hp₀ hg₀
    exact flowRule_killedHistory (e := e) (ω := x) hV hp hc hg hl rfl hs.1 hs.2
  exact ⟨h', 𝓕, W, VL, VR, B, R, htr, hSC, measurable_flowRule _ _ _ _ _, isHistGalmarino_flowRule _ _ _ _ _, hR, hgen⟩

/-- PROVE-DOMAINMARKOV9's (L1) from (L1) with the lifetime clause. -/
theorem flowLineStopIdentStatement_of_L (hL : FlowLineStopIdentLStatement.{u}) :
    FlowLineStopIdentStatement.{u} :=
  flowLineStopIdentStatement_of_G (flowLineStopIdentGStatement_of_L hL)

/-- **`RLC.FlowLocalityStatement` from (L1) with the lifetime clause**, the WFS kernel target for `0 < κ < 4`
(`WFS.ThroughKernelStatement`, which with the proved continuation gives Aux. lemma 54 for Galmarino stops), and
Theorems 1.2–1.3. -/
theorem flowLocalityStatement_of_stopIdentL_through (hL : FlowLineStopIdentLStatement.{u})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{u, u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : RLC.FlowLocalityStatement.{u} :=
  WFS.flowLocalityStatement_of_through (flowLineStopIdentGStatement_of_L hL) hT h12p h13

end FlowStopIdentG

end Restart

end InteractingSLE
