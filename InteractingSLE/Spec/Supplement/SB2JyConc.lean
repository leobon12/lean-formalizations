/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JyEnd
import InteractingSLE.Spec.Supplement.SB2JyAE
import InteractingSLE.Spec.Supplement.SB2MaSet
import InteractingSLE.Spec.Supplement.SB2WdInd

/-!
# SB2(2): the concrete stage rule in v2 form, with the actual-piece facts discharged

Packet PROVE-SB2-LIFTSET (round 14). The concrete rule (`SB2LjRule`) restated for the v2 data clause
(`RelDataClauseV2`: SB2LIFT's reduced run inputs, the record clause only at a finite start piece), with two
corrections and the actual-piece facts of `StageGeom` **proved**:

* **`exists_EL_rec'`**: `exists_EL_rec` with the admissibility asked only for earlier drivers that are measurable,
  regular, `zeroDrv` on their zero events and generating their stage curves on their driven events — what the
  recursion provides. (`exists_EL_rec`'s hypothesis for *every* measurable family is not provable for the concrete
  rule: the relative run of an arbitrary measurable family has no regular charts.) `exists_EL_concrete'`;
* `StageRelFin`, `StageRelInf`, **`StageFactsV2`**: the per-stage facts left — the density of the actual piece's good
  times before its lifetime, and the relative facts (finite: relative lifetime finite, driver continuous through it,
  an endpoint extension of the generated trace with its relative boundary map; infinite: the same with a closed
  boundary image; both: the relative chart's inverse identity and continuity, the lifted good points in its domain);
* **`liftRel_of_stageFactsV2`**: the lift relation from them, with the actual-piece facts **proved** — tip set as the
  image of its points, compact (finite) / closed (infinite: the correction of `StageGeomInf`) tail times, tail
  position (`tail_of_launch`), density of the tail's `D`-times (`hdense_tail_of_good`), the lifted endpoint
  (`hend_of_launch`), positivity (SB2LIFT's `sb2LowerWalkInputs`), and the upper chart (`sb2LowerUpperChart`);
* `StagesGeomV2`, **`piecesLift2_of_geomV2`**, `GeomAtV2`, **`ConcreteSplitV2At`**,
  **`SB2LowerConcreteSplitV2Statement`** (named input); **`sb2LowerRelDriverDataV2Statement_of_splitV2`**,
  `sb2LowerRelWalkRangeStatement_of_splitV2`, `sb2LowerLaunchLiftStatement_of_splitV2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
open LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### The recursion with the weak admissibility -/

section Rec

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`exists_EL_rec` with the weak admissibility**: the stage is admissible whenever the earlier drivers are
measurable, regular, `zeroDrv` on their zero events and generate their stage curves on their driven events. -/
theorem exists_EL_rec' (ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ) (G Z : ℕ → (ℕ → Ω → Drv) → Set Ω)
    (hdep : ∀ j F F', (∀ i < j, F i = F' i) → ρ j F = ρ j F' ∧ G j F = G j F' ∧ Z j F = Z j F')
    (hok : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ Z i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ G i F, ω ∉ Z i F → (F i ω).2 = capLife (ρ i F ω) ∧
        ∀ T < capLife (ρ i F ω), IsGeneratingTrace (F i ω).1 T (capTrace (ρ i F ω))) →
      StageOK (ρ j F) (G j F) (Z j F)) :
    ∃ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      (∀ j, ∀ ω ∈ Z j EL, EL j ω = zeroDrv) ∧
      ∀ j, ∀ ω ∈ G j EL, ω ∉ Z j EL → (EL j ω).2 = capLife (ρ j EL ω) ∧
        ∀ T < capLife (ρ j EL ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j EL ω)) := by
  set EL := ELrec ρ G Z with hEL
  have hbef : ∀ j, ∀ i < j, before EL j i = EL i := fun j i hi => by simp [before, hi]
  have hsame : ∀ j, ρ j (before EL j) = ρ j EL ∧ G j (before EL j) = G j EL ∧ Z j (before EL j) = Z j EL :=
    fun j => hdep j _ _ (hbef j)
  have hst : ∀ j, StageOK (ρ j (before EL j)) (G j (before EL j)) (Z j (before EL j)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      have hspec : ∀ i < j, Measurable (EL i) ∧ (∀ ω ∈ Z i EL, EL i ω = zeroDrv) ∧
          ∀ ω ∈ G i EL, ω ∉ Z i EL → (EL i ω).2 = capLife (ρ i EL ω) ∧
            ∀ T < capLife (ρ i EL ω), IsGeneratingTrace (EL i ω).1 T (capTrace (ρ i EL ω)) := by
        intro i hi
        obtain ⟨hρ, hG, hZ⟩ := hsame i
        have hs := stageDrv_spec (ih i hi)
        have e : EL i = stageDrv (ρ i (before EL i)) (G i (before EL i)) (Z i (before EL i)) := by
          rw [hEL, ELrec_eq]
        refine ⟨by rw [e]; exact hs.1, fun ω hω => by rw [e]; exact hs.2.1 ω (by rw [hZ]; exact hω),
          fun ω hω hnZ => ?_⟩
        have := hs.2.2 ω (by rw [hG]; exact hω) (by rw [hZ]; exact hnZ)
        rw [e, ← hρ]
        exact this
      have hagree : ∀ i < j, ρ i (before EL j) = ρ i EL ∧ G i (before EL j) = G i EL ∧
          Z i (before EL j) = Z i EL :=
        fun i hi => hdep i _ _ fun i' hi' => hbef j i' (lt_trans hi' hi)
      refine hok j (before EL j) (fun i hi => by rw [hbef j i hi]; exact (hspec i hi).1)
        (fun i hi ω => by rw [hbef j i hi, hEL, ELrec_eq]; exact stageDrv_regular _ _ _ ω) ?_ ?_
      · intro i hi ω hω
        rw [(hagree i hi).2.2] at hω
        rw [hbef j i hi]
        exact (hspec i hi).2.1 ω hω
      · intro i hi ω hω hnZ
        rw [(hagree i hi).2.1] at hω
        rw [(hagree i hi).2.2] at hnZ
        rw [hbef j i hi, (hagree i hi).1]
        exact (hspec i hi).2.2 ω hω hnZ
  have hmeas : ∀ j, Measurable (EL j) := fun j => by rw [hEL, ELrec_eq]; exact (stageDrv_spec (hst j)).1
  refine ⟨EL, hmeas, fun j ω => ?_, fun j ω hω => ?_, fun j ω hω hnZ => ?_⟩
  · rw [hEL, ELrec_eq]; exact stageDrv_regular _ _ _ ω
  · obtain ⟨-, -, hZ⟩ := hsame j
    rw [hEL, ELrec_eq]
    exact (stageDrv_spec (hst j)).2.1 ω (by rw [hZ]; exact hω)
  · obtain ⟨hρ, hG, hZ⟩ := hsame j
    have := (stageDrv_spec (hst j)).2.2 ω (by rw [hG]; exact hω) (by rw [hZ]; exact hnZ)
    rw [hEL, ELrec_eq, ← hρ]
    exact this

end Rec

/-- **`exists_EL_rec'` applied to the concrete rule.** -/
theorem exists_EL_concrete' {Ω : Type*} [MeasurableSpace Ω] (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ)
    (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ) (D₁ : Ω → ℕ → Drv) (ΦG : ℕ → Ω → ExplState → Prop)
    (hok : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ cZ κ θ b₁ J₁ R D₁ i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ cG κ θ b₂ J₂ ΦG i F, ω ∉ cZ κ θ b₁ J₁ R D₁ i F →
        (F i ω).2 = capLife (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω) ∧
        ∀ T < capLife (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω))) →
      StageOK (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j F) (cG κ θ b₂ J₂ ΦG j F) (cZ κ θ b₁ J₁ R D₁ j F)) :
    ∃ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      (∀ j, ∀ ω ∈ cZ κ θ b₁ J₁ R D₁ j EL, EL j ω = zeroDrv) ∧
      ∀ j, ∀ ω ∈ cG κ θ b₂ J₂ ΦG j EL, ω ∉ cZ κ θ b₁ J₁ R D₁ j EL →
        (EL j ω).2 = capLife (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω) ∧
        ∀ T < capLife (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω)) :=
  exists_EL_rec' _ _ _ (hdep_concrete κ θ b₁ J₁ b₂ J₂ R c m D₁ ΦG) hok

/-! ### The per-stage facts left -/

/-- The relative facts at a finite actual piece. -/
def StageRelFin (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  e₂.2 ≠ ⊤ ∧ ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2} ∧
  (∃ (α : ℝ≥0 → ℂ) (f : ℂ → ℂ), (∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) ∧
    α 0 = 0 ∧ ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    (∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ)))) ∧
    ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2}) ∧
  ContinuousOn (stChart s₂).2.1 H ∧ (∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) ∧
  ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H

/-- The relative facts at an infinite actual piece. -/
def StageRelInf (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2} ∧
  (∃ (α : ℝ≥0 → ℂ) (f : ℂ → ℂ), (∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ) ∧
    α 0 = 0 ∧ ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    (∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ)))) ∧
    ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2} ∧
    IsClosed ((fun τ => f (α τ)) '' {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2})) ∧
  ContinuousOn (stChart s₂).2.1 H ∧ (∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) ∧
  ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H

/-- **The per-stage facts left**: the density of the actual piece's good times before its lifetime, and the relative
facts. -/
def StageFactsV2 (c : Chart) (m : ℝ) (s₁ : ExplState) (e₁ : Drv) (s₂ : ExplState) (e₂ : Drv) : Prop :=
  {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁) ∧
    (e₁.2 ≠ ⊤ → StageRelFin c m s₁ e₁ s₂ e₂) ∧ (e₁.2 = ⊤ → StageRelInf c m s₁ e₁ s₂ e₂)

/-- **The lift relation at a concrete stage from the per-stage facts left** (the actual-piece facts proved). -/
theorem liftRel_of_stageFactsV2 {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv} {n : ℕ} {c : Chart}
    {R m : ℝ} {A : Set ℂ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₂ : ExplState} {e₂ : Drv}
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcc : c.IsConformal) (hU : UpperChartOK c)
    (hDom : c.2.1 '' H = H \ fillH A) (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hF : StageFactsV2 c m (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s₂ e₂)
    (hρ : IsDrivenCurve (stCurve c m (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s₂))
    (he₂ : e₂.2 = capLife (stCurve c m (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s₂))
    (hgen : ∀ T < capLife (stCurve c m (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s₂),
      IsGeneratingTrace e₂.1 T
        (capTrace (stCurve c m (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s₂)))
    (hW0 : e₂.1 0 = 0) :
    LiftRel β₀ tL γ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (newPc s₂ e₂) := by
  obtain ⟨hcH, hc1, hoff⟩ := hU
  obtain ⟨hgd, hfin, htop⟩ := hF
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have htail := tail_of_launch hl hβr hK hDom
  have hd₁ := hdense_tail_of_good hP hl hpos hβ htail hgd
  by_cases he₁ : (D n).2 = ⊤
  · obtain ⟨hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc, hcl⟩, hcH₂, hc1₂, hdom⟩ := htop he₁
    exact liftRel_concrete_top2 hγ hcH hc1 hoff (isClosed_tail_times hβ.1 tL (isClosed_tipSet_launch hP hl)) hd₁
      htip htail he₁ hρ he₂ hgen hW hW0 hαeq hα0 hαc hc hgc hcl hcH₂ hc1₂ hdom hgd
  · obtain ⟨hfin₂, hW, ⟨α, f, hαeq, hα0, hαc, hc, hgc⟩, hcH₂, hc1₂, hdom⟩ := hfin he₁
    exact liftRel_concrete_driven hγ hcH hc1 hoff (isCompact_tail_times_launch hP hl he₁ hβ tL) hd₁ htip htail he₁
      hpos hρ he₂ hgen hfin₂ hW hW0 hαeq hα0 hαc hc hgc hcH₂ hc1₂ hdom hgd (hend_of_launch hcc m hP hl hpos)

/-! ### Along the walks -/

/-- **The per-stage facts left along the walks** (one sample): stage `0` of a non-zero-root start (the facts at
positive lifetime; the lift relation itself at zero lifetime), and every even stage `i ≥ 2` whose actual stage
launches with arc status and an admissible seed; at each, the stage is driven (`Gi`). -/
def StagesGeomV2 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ)
    (D₁ D₂ : ℕ → Drv) (Gi : ℕ → Prop) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop :=
  (¬ ZeroRoot κ θ b₁ J₁ R D₁ →
    (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
    Gi 0 ∧
      ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ 0 → StageFactsV2 c m (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁))
        (D₁ (relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ 0) (D₂ 0)) ∧
      ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 = 0 → LiftRel β₀ tL γ
        (newPc (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)))
        (newPc (ExplState.init 0) (D₂ 0)))) ∧
  ∀ i, 2 ≤ i → i % 2 = 0 →
    (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
    stStatus (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) = GW1W.stArcM true →
    ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁))))
      (rightLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)))) θ →
    Gi i ∧ StageFactsV2 c m (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₁ (i + relOff κ θ b₁ J₁ R D₁))
      (wRun κ θ b₂ J₂ D₂ i) (D₂ i)

/-- **The piece lifts from the per-stage facts left** (deterministic, one sample). -/
theorem piecesLift2_of_geomV2 {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R R' : ℝ}
    {c : Chart} {m : ℝ} {A : Set ℂ} {D₁ D₂ : ℕ → Drv} {Gi : ℕ → Prop} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R' m β₀ tL γ) (hcc : c.IsConformal) (hU : UpperChartOK c)
    (hDom : c.2.1 '' H = H \ fillH A) (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hpos : ∀ n, 0 < n → (wRun κ θ b₁ J₁ D₁ (n + 1)).2.2.2.1 n ≠ none → (D₁ n).2 ≠ 0)
    (hG : StagesGeomV2 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ Gi β₀ γ tL) (hreg : ∀ j, IsRegularDriver (D₂ j))
    (hgen : ∀ j, Gi j → ¬ (j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁)) →
      (D₂ j).2 = capLife (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
        (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j)) ∧
      ∀ T < capLife (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
          (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j)),
        IsGeneratingTrace (D₂ j).1 T (capTrace (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
          (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j))))
    (hdrv : ∀ j, Gi j → IsDrivenCurve (stCurve c m (wRun κ θ b₁ J₁ D₁ (j + relOff κ θ b₁ J₁ R D₁))
      (D₁ (j + relOff κ θ b₁ J₁ R D₁)) (wRun κ θ b₂ J₂ D₂ j))) :
    PiecesLift2 κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL := by
  obtain ⟨h0, hi⟩ := hG
  refine ⟨?_, fun hZ hl => ?_⟩
  · intro i hi2 hl hflow hstat hseed
    have hev : i % 2 = 0 := of_decide_eq_true hflow
    obtain ⟨hGi, hF⟩ := hi i hi2 hev hl hstat hseed
    have hnZ : ¬ (i % 2 = 1 ∨ (i = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁)) := by
      rintro (h | ⟨h, -⟩) <;> omega
    obtain ⟨he₂, hg⟩ := hgen i hGi hnZ
    exact liftRel_of_stageFactsV2 hγ hcc hU hDom hK hβ hβr hP hl (hpos _ (by omega) hl) hF (hdrv i hGi) he₂ hg
      (hreg i).2.1
  · obtain ⟨hG0, hF, hz⟩ := h0 hZ hl
    by_cases hd0 : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 = 0
    · exact hz hd0
    · have hnZ : ¬ (0 % 2 = 1 ∨ (0 = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁)) := by
        rintro (h | ⟨-, h⟩)
        · omega
        · exact hZ h
      obtain ⟨he₂, hg⟩ := hgen 0 hG0 hnZ
      have hd := hdrv 0 hG0
      simp only [zero_add] at he₂ hg hd
      exact liftRel_of_stageFactsV2 hγ hcc hU hDom hK hβ hβr hP hl hd0 (hF hd0) hd he₂ hg (hreg 0).2.1

/-! ### The named input and the assembly -/

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- The per-stage facts left, almost surely, for a relative family `EL` and run-read driven events `ΦG`. -/
def GeomAtV2 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (ΦG : ℕ → Ω → ExplState → Prop) (EL : ℕ → Ω → Drv) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        StagesGeomV2 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m
          (lD₁ b jumps E ω) (fun j => EL j ω) (fun j => ω ∈ lG κ b' J' m ΦG j EL) β₀ γ tL

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The concrete rule in v2 form**: run-read driven events making the concrete rule admissible (weak form), such
that every measurable, everywhere regular family that is `zeroDrv` on the zero events and generates the concrete
curves on the driven events has the per-stage facts left almost surely and satisfies the v2 data clause given its
piece lifts. -/
def ConcreteSplitV2At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ ΦG : ℕ → Ω → ExplState → Prop,
    (∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ lZ κ b jumps E u l k ω₀ i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ lG κ b' J' m ΦG i F, ω ∉ lZ κ b jumps E u l k ω₀ i F →
        (F i ω).2 = capLife (lρ κ b jumps E u l k ω₀ c b' J' m i F ω) ∧
        ∀ T < capLife (lρ κ b jumps E u l k ω₀ c b' J' m i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ κ b jumps E u l k ω₀ c b' J' m i F ω))) →
      StageOK (lρ κ b jumps E u l k ω₀ c b' J' m j F) (lG κ b' J' m ΦG j F) (lZ κ b jumps E u l k ω₀ j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAtV2 κ b jumps P E u l k ω₀ c b' J' m ΦG EL ∧
      (PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL → RelDataClauseV2 κ b jumps P E u l k ω₀ c b' J' m EL)

/-- **Named input: SB2(2)'s concrete stage rule in v2 form.** -/
def SB2LowerConcreteSplitV2Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ConcreteSplitV2At κ b jumps P E u l k ω₀ c b' J'

/-- **The head-free reduced v2 data from the concrete rule in v2 form** (the actual-piece facts of the lift relation
from the regular launches, the head hull, the upper chart and SB2LIFT's positivity; Theorem 1.3 at universe `0`). -/
theorem sb2LowerRelDriverDataV2Statement_of_splitV2 (h13₀ : Exist.Theorem13Statement.{0})
    (hS : SB2LowerConcreteSplitV2Statement.{u}) : SB2LowerRelDriverDataV2Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hRLQ] with ω₀ h₀ hC₀ hH₀ hI₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨hcc, hU, hDom⟩ := hC₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨ΦG, hok, hcl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_concrete' κ (-(Real.pi / 2)) b jumps (affData 1 m b')
    (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) ΦG hok
  refine ⟨EL, hmeas, hreg, ?_⟩
  obtain ⟨hgeom, hrest⟩ := hcl EL hmeas hreg hZ hgen
  refine hrest ?_
  filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀]
    with ω hω hHω hIω hRω
  intro β₀ hβ hβ0 hβr tL γ hγ
  exact piecesLift2_of_geomV2 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
    (fun n hn hl => (hIω n).2.2 hn hl) (hω β₀ hβ hβ0 hβr tL γ hγ) (fun j => hreg j ω)
    (fun j hG hnZ => hgen j ω hG hnZ)
    (fun j hG => (hok j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
      (fun i _ => hgen i)).2.2.2 ω hG)

/-- **SB2(2)'s range statement from the concrete rule in v2 form** (and Theorems 1.2–1.3). -/
theorem sb2LowerRelWalkRangeStatement_of_splitV2 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerConcreteSplitV2Statement.{u}) :
    SB2LowerRelWalkRangeStatement.{u} :=
  sb2LowerRelWalkRangeStatement_of_dataV2 h12 h13 h12₀ h13₀ (sb2LowerRelDriverDataV2Statement_of_splitV2 h13₀ hS)

/-- **SB2(2)'s combined target (R104a) from the concrete rule in v2 form and the conditional half.** -/
theorem sb2LowerLaunchLiftStatement_of_splitV2 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerConcreteSplitV2Statement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_dataV2 h12 h13 h12₀ h13₀ (sb2LowerRelDriverDataV2Statement_of_splitV2 h13₀ hS) hcond

end InteractingSLE.Theorem14.SB.Lk
