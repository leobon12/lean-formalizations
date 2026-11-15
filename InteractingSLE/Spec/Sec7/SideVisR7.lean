/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.OuterPhNextShared
import InteractingSLE.Spec.Sec7.SideVisFrontier
import InteractingSLE.Spec.Sec7.SideVisClock

/-!
# R.6's shared-side visits for the outer R.7 pockets

PROVE-SIDE-VISITS. Supplement pp. 476–477 ("For the probability-one
quantifiers … Constancy of the outer phase then extends the conclusion to its
whole positive relative lifetime"). The source splits R.6's selection into

* a **fixed-time transfer**: at each rational original time `r` at which the
  counterflow tip lies in the pocket `C` but off the certified frontiers
  `β_R, β_L`, the R.6 comparison with the nested inner pocket holds almost
  surely ("At each rational original counterflow time the old-germ
  comparisons hold simultaneously … At this rational time compare the
  inherited germs pathwise"), and
* the **visits**: whenever the pocket is visited, some rational original time
  is such a certified visit ("The set of original times with `η(t) ∈ C ∖ β_R`
  is open, so whenever it is nonempty it contains a rational original time.
  For two outer arms use `C ∖ (β_R ∪ β_L)`; Aux. 42 and the finite
  closed-cover argument show that such a time exists"), and its relative
  capacity is positive and live.

This file defines the certified visit events and relative clocks
(`visitEvent`, `visitClock` and their seed-opening forms), states the
fixed-time transfer as the named, **unproved** event-level inputs
`TwoSeedSharedTransferInput(Inf)`, and **proves** that the transfer and the
visits give the shared-side witnesses `OuterPhNext.TwoSeedSharedVisitsInput(Inf)`
on every outer configuration with a no-simple-arc counterflow and seed-proper
frontiers. The visits part is proved here: openness and nonemptiness of the
visit set (`IsErasurePocket`), the no-exhaustion argument
(`exists_rat_mem_offFrontier`) and the live clock bounds
(`erasure_relCap_pos_lt_of_visit`). Nothing evaluates a fixed-time almost-sure
statement at a random time: the transfer is quantified at each deterministic
rational time and intersected before the pathwise selection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.SideVis

open PocketTraversal Lemma71C PocketStop PocketWordAssembly PocketSeedOpen
  PocketCoupling PocketJordan Hsd PhaseClause PocketStopField PocketMarks PocketStopMarked
  Sec5.Prop55Half Theorem14.GB10 R7StopIn HOuter

section Defs

variable {Ω : Type*}

/-- The certified visit event of a bounded change pocket at the original time `t`:
the tip is an interior visit of the pocket and lies off both certified frontiers. -/
def visitEvent (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (βR βL : Ω → ℝ≥0 → ℂ)
    (t : ℝ) : Set Ω :=
  {ω | t ∈ Sec6.visitSet (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) ∧
    negInv (η ω t) ∉ range (βR ω) ∪ range (βL ω)}

/-- The relative capacity of the bounded pocket's erased traversal reached at the
original time `t`. -/
def visitClock (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (t : ℝ)
    (ω : Ω) : ℝ≥0 :=
  (relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) t).toNNReal

/-- The certified visit event of a change pocket opening at the flow seed. -/
def visitEventInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (βR βL : Ω → ℝ≥0 → ℂ)
    (t : ℝ) : Set Ω :=
  {ω | t ∈ Sec6.visitSetInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) ∧
    negInv (η ω t) ∉ range (βR ω) ∪ range (βL ω)}

/-- The relative capacity of the seed-opening pocket's erased traversal reached at
the original time `t`. -/
def visitClockInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (t : ℝ)
    (ω : Ω) : ℝ≥0 :=
  (relCapInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω) t).toNNReal

/-- **Named, unproved R.6 transfer at a fixed rational original time** (bounded outer
pocket): for every coherent phase word with a continuous phase, at each rational
original time, almost surely on the test, a certified visit has zero phase at its
relative capacity. This is the comparison of R.6 with the nested inner pocket that
contains the tip (supplement pp. 476–477), not a selection statement. -/
def TwoSeedSharedTransferInput (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurable Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAll R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ visitEvent R L r η βR βL q →
        δ (visitClock R L r η ψ q ω) ω = 0

/-- **Named, unproved R.6 transfer at a fixed rational original time** for a pocket
opening at the flow seed. -/
def TwoSeedSharedTransferInputInf (k rL rR : ℝ) (𝓦 : MeasurableSpace Ω)
    [MeasurableSpace Ω] (P : Measure Ω) (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0)
    (η : Ω → ℝ → ℂ) (G : Set Ω) (h₀ : Ω → DistOn upperHalfPlaneOpens)
    (u : ℂ → ℝ) (βR βL : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A →
    ∀ ψ : Ω → ℂ → ℂ, (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ∀ n : Ω → ℤ, Measurable[𝓦] n → ∀ (a : ℝ) (δ : ℝ≥0 → Ω → ℝ),
      let γ := travAllInf R L r η ψ
      let c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)
      (∀ q, PocketStopSide.PocketStopPhaseSideLimit k
        (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
        (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) c a h₀ u
        (activeCompl A γ c q) (δ q) q) →
      (∀ᵐ ω ∂P, ω ∈ A → ContinuousOn (δ · ω)
        {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)}) →
      ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ visitEventInf R L r η βR βL q →
        δ (visitClockInf R L r η ψ q ω) ω = 0

end Defs

/-- Inversion keeps the open upper half-plane. -/
theorem negInv_mem_H {z : ℂ} (hz : z ∈ H) : negInv z ∈ H := by
  have hz' : 0 < z.im := hz
  have hn : 0 < Complex.normSq z := Complex.normSq_pos.2 fun h => by simp [h] at hz'
  show 0 < (-z⁻¹).im
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hz' hn

/-- Points of the inverted change pocket are nonzero. -/
theorem ne_zero_of_mem_cfPocket {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : PocketCoord.IsChangeConfigInc R L r)
    {z : ℂ} (hz : z ∈ cfPocket R L r) : z ≠ 0 := by
  obtain ⟨w, hw, rfl⟩ := hz
  intro h0
  have hH := negInv_mem_H (h.changePocket_subset_H hw)
  rw [h0] at hH
  simp [QuantumZipper.H] at hH

/-! ### The visits, pathwise -/

/-- **A certified rational visit of a bounded outer pocket** (pathwise): on an outer
configuration whose counterflow has no trace interval in a simple arc, with
seed-proper frontiers, some rational original time is a certified visit; its
relative capacity is positive and live. -/
theorem exists_rat_visitEvent {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    {βR βL : Ω → ℝ≥0 → ℂ} {ψ : Ω → ℂ → ℂ} {W : ℝ → ℝ} {ω : Ω}
    (hc : IsOuterCfg (R ω) (L ω) r W (η ω)) (hψ : IsCfJordan (R ω) (L ω) r (ψ ω))
    (h42 : NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤)
    (hβR : IsSeedProper (βR ω)) (hβL : IsSeedProper (βL ω)) :
    ∃ q : ℚ, ω ∈ visitEvent R L r η βR βL q ∧ 0 < visitClock R L r η ψ q ω ∧
      (visitClock R L r η ψ q ω : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
  have hP := hc.erase
  set C := cfPocket (R ω) (L ω) r
  set τ := firstHit (η ω) (cfArcR (R ω) (L ω) r 1)
  set σ := firstHit (η ω) (cfArcR (R ω) (L ω) r 0)
  have hVpos : Sec6.visitSet (η ω) C τ σ ⊆ Ioi 0 := fun t ht => hP.nonneg.trans_lt ht.1.1
  have h0 : ∀ t ∈ Sec6.visitSet (η ω) C τ σ, η ω t ≠ 0 := fun t ht =>
    ne_zero_of_mem_cfPocket hc.conf ht.2
  have hne : (Sec6.visitSet (η ω) C τ σ).Nonempty := by
    obtain ⟨t, ht, htC⟩ := hP.noFinal τ ⟨le_rfl, hP.lt⟩
    exact ⟨t, ht, htC⟩
  obtain ⟨q, hq, hoff⟩ := exists_rat_mem_offFrontier hP.cont h42 hβR hβL hP.isOpen_visitSet
    hVpos h0 hne
  have hγ : IsDrivenCurve (relTrav (η ω) C τ σ (ψ ω)) := (hc.props hψ).1
  obtain ⟨hpos, hlive⟩ := erasure_relCap_pos_lt_of_visit hP hγ hq
  exact ⟨q, ⟨hq, hoff⟩, Real.toNNReal_pos.2 hpos, hlive⟩

/-- **A certified rational visit of a seed-opening outer pocket** (pathwise). -/
theorem exists_rat_visitEventInf {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    {βR βL : Ω → ℝ≥0 → ℂ} {ψ : Ω → ℂ → ℂ} {W : ℝ → ℝ} {ω : Ω}
    (hc : IsOuterCfgInf (R ω) (L ω) r W (η ω)) (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (h42 : NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤)
    (hβR : IsSeedProper (βR ω)) (hβL : IsSeedProper (βL ω)) :
    ∃ q : ℚ, ω ∈ visitEventInf R L r η βR βL q ∧ 0 < visitClockInf R L r η ψ q ω ∧
      (visitClockInf R L r η ψ q ω : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω) := by
  have hP := hc.erase
  set C := cfPocket (R ω) (L ω) r
  set τ := firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)
  have hVpos : Sec6.visitSetInf (η ω) C τ ⊆ Ioi 0 := fun t ht => hP.nonneg.trans_lt ht.1
  have h0 : ∀ t ∈ Sec6.visitSetInf (η ω) C τ, η ω t ≠ 0 := fun t ht =>
    ne_zero_of_mem_cfPocket hc.conf ht.2
  have hne : (Sec6.visitSetInf (η ω) C τ).Nonempty := by
    obtain ⟨t, ht, htC⟩ := hP.noFinal τ le_rfl
    exact ⟨t, ht, htC⟩
  obtain ⟨q, hq, hoff⟩ := exists_rat_mem_offFrontier hP.cont h42 hβR hβL hP.isOpen_visitSet
    hVpos h0 hne
  have hγ : IsDrivenCurve (travInf (η ω) C τ (ψ ω)) := (hc.props hψ).1
  obtain ⟨hpos, hlive⟩ := erasureInf_relCap_pos_lt_of_visit hP hγ hq
  exact ⟨q, ⟨hq, hoff⟩, Real.toNNReal_pos.2 hpos, hlive⟩

/-! ### The shared-side witnesses from the transfer and the visits -/

section Witness

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [MeasurableSpace Ω]
  {P : Measure Ω} {k rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {η : Ω → ℝ → ℂ} {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
  {βR βL : Ω → ℝ≥0 → ℂ} {W : Ω → ℝ → ℝ}

/-- **R.6's shared-side witnesses for a bounded outer pocket**: the fixed-time
transfer and the proved certified visits give `OuterPhNext.TwoSeedSharedVisitsInput`.
The witnesses are indexed by `ℕ` through an enumeration of `ℚ`. -/
theorem twoSeedSharedVisitsInput_of_transfer
    (htr : TwoSeedSharedTransferInput k rL rR 𝓦 P R L r η G h₀ u βR βL)
    (hcfg : ∀ ω ∈ G, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (h42 : ∀ᵐ ω ∂P, NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤)
    (hβ : ∀ᵐ ω ∂P, IsSeedProper (βR ω) ∧ IsSeedProper (βL ω)) :
    OuterPhNext.TwoSeedSharedVisitsInput k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont
  refine ⟨fun i => visitClock R L r η ψ ((Denumerable.eqv ℚ).symm i),
    fun i => visitEvent R L r η βR βL ((Denumerable.eqv ℚ).symm i), fun i => ?_, ?_⟩
  · exact htr A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont ((Denumerable.eqv ℚ).symm i)
  · filter_upwards [h42, hβ] with ω hω hβω hωA _
    obtain ⟨q, hq, hpos, hlive⟩ := exists_rat_visitEvent (βR := βR) (βL := βL)
      (hcfg ω (hAG hωA)) (hJ ω hωA) hω hβω.1 hβω.2
    refine ⟨Denumerable.eqv ℚ q, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨hpos, hlive, hq⟩

/-- **R.6's shared-side witnesses for a seed-opening outer pocket.** -/
theorem twoSeedSharedVisitsInputInf_of_transfer
    (htr : TwoSeedSharedTransferInputInf k rL rR 𝓦 P R L r η G h₀ u βR βL)
    (hcfg : ∀ ω ∈ G, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (h42 : ∀ᵐ ω ∂P, NoSimpleArcInterval (fun s : ℝ≥0 => η ω s) ⊤)
    (hβ : ∀ᵐ ω ∂P, IsSeedProper (βR ω) ∧ IsSeedProper (βL ω)) :
    OuterPhNext.TwoSeedSharedVisitsInputInf k rL rR 𝓦 P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hJ hPt n hn a δ _ _ hphase hcont
  refine ⟨fun i => visitClockInf R L r η ψ ((Denumerable.eqv ℚ).symm i),
    fun i => visitEventInf R L r η βR βL ((Denumerable.eqv ℚ).symm i), fun i => ?_, ?_⟩
  · exact htr A hA hAG hPA ψ hJ hPt n hn a δ hphase hcont ((Denumerable.eqv ℚ).symm i)
  · filter_upwards [h42, hβ] with ω hω hβω hωA _
    obtain ⟨q, hq, hpos, hlive⟩ := exists_rat_visitEventInf (βR := βR) (βL := βL)
      (hcfg ω (hAG hωA)) (hJ ω hωA) hω hβω.1 hβω.2
    refine ⟨Denumerable.eqv ℚ q, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact ⟨hpos, hlive, hq⟩

end Witness

end InteractingSLE.Sec7.SideVis
