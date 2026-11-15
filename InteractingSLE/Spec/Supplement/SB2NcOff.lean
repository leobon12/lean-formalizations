/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcX0
import InteractingSLE.Spec.Supplement.SB2MzOffM

/-!
# F2b′: the offset event at a random right end `R`, measurably

Packet PROVE-AUX61-NOJUMP (round 21, D34, component A). PROVE-SB2-LCMEAN's `Mz.exists_measurableSet_relOffEvent` is
for a fixed right end `R` (it is used under the upper kernel). At the `P` level `R = max (A ∩ ℝ)` is random; this
file is the same proof with `R` a measurable random variable:

* `measurableSet_mem_closure_range_rand`, `measurableSet_mem_restartSet_rand`;
* **`exists_measurableSet_relOffEvent_rand`**;
* `measurable_stPt_past`: the walk's point after `n` instructions is measurable for the past `pastSigma n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep Mz
open PiecewiseConstantBoundaryData (rightLim)

theorem measurableSet_mem_closure_range_rand {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {G : Ω → ι → ℂ}
    (hG : ∀ i, Measurable fun ω => G ω i) {Rf : Ω → ℝ} (hRf : Measurable Rf) :
    MeasurableSet {ω | ((Rf ω : ℝ) : ℂ) ∈ closure (range (G ω))} := by
  have hm : Measurable fun ω => ⨅ i, edist ((Rf ω : ℝ) : ℂ) (G ω i) :=
    Measurable.iInf fun i => (Complex.measurable_ofReal.comp hRf).edist (hG i)
  have e : {ω | ((Rf ω : ℝ) : ℂ) ∈ closure (range (G ω))} =
      (fun ω => ⨅ i, edist ((Rf ω : ℝ) : ℂ) (G ω i)) ⁻¹' {0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_closure_range_iff]
  rw [e]
  exact hm (measurableSet_singleton 0)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The restart test of a random point at a measurable run is measurable. -/
theorem measurableSet_mem_restartSet_rand (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type*}
    [MeasurableSpace Ω] {S : Ω → ExplState} (hS : Exist.StagedLaw.IsMeasState S) {Rf : Ω → ℝ}
    (hRf : Measurable Rf) :
    MeasurableSet {ω | Rf ω ∈ GW1W.restartSet κ b jumps (S ω)} := by
  have hpt := hS.2.1
  have hang := hS.2.2.1
  have e : {ω | Rf ω ∈ GW1W.restartSet κ b jumps (S ω)} =
      {ω | Rf ω ∈ PiecewiseConstantBoundaryData.jumpSet b jumps} ∩
      ({ω | stPt (S ω) < Rf ω} ∩
        {ω | -sleLambda κ < rightLim b (Rf ω) + stAngle (S ω) * QuantumZipper.chiC κ}) := by
    ext ω
    simp only [GW1W.restartSet, Finset.mem_filter, mem_ofPred_eq, mem_inter_iff]
  rw [e]
  refine MeasurableSet.inter (hRf (Finset.measurableSet _)) ((measurableSet_lt hpt hRf).inter ?_)
  exact measurableSet_lt measurable_const
    (((measurable_rightLim_of_pcbd hb).comp hRf).add (hang.mul measurable_const))

/-- **The offset event at a random point `R` agrees with a measurable event on the event of regular pieces**
(`Mz.exists_measurableSet_relOffEvent` with `R` a measurable random variable). -/
theorem exists_measurableSet_relOffEvent_rand (hb : IsPiecewiseConstantBoundaryData b jumps) (θ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : ∀ j, Measurable (D j))
    (hDreg : ∀ j ω, IsRegularDriver (D j ω)) {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun i => D i ω) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (D j ω).1 (min (instrTime (boundaryWalkSpec b jumps θ true) j) (D j ω).2))
    {Rf : Ω → ℝ} (hRf : Measurable Rf) (o : ℕ) :
    ∃ S : Set Ω, MeasurableSet S ∧
      ∀ ω ∈ M, (relOffEvent κ θ b jumps (Rf ω) (fun i => D i ω) o ↔ ω ∈ S) := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have hs1 : spec.1 = 0 := rfl
  obtain ⟨F, hFm, hF⟩ := Side.exists_measurable_piece_dense_code hb spec hDm hDreg hM hMreg
  obtain ⟨A, hAm, hA⟩ := Side.exists_measurable_arc_dense_code hb spec hDm hDreg
  -- the entry events
  set Ent' : ℕ → Set Ω := fun n => ⋃ k ∈ Finset.range (n + 1),
    ({ω | ((Rf ω : ℝ) : ℂ) ∈ closure (range (F k ω))} ∪
      {ω | ((Rf ω : ℝ) : ℂ) ∈ closure (range (A k ω))})
    with hEnt'
  have hEntm : ∀ n, MeasurableSet (Ent' n) := fun n =>
    Finset.measurableSet_biUnion _ fun k _ =>
      (measurableSet_mem_closure_range_rand (fun i => hFm k i) hRf).union
        (measurableSet_mem_closure_range_rand (fun i => hAm k i) hRf)
  have hEnt : ∀ ω ∈ M, ∀ n, Ent κ θ b jumps (Rf ω) (fun i => D i ω) n ↔ ω ∈ Ent' n := by
    intro ω hω n
    unfold Ent
    rw [statePhysicalSet_run_eq]
    have hF' := hF ω hω
    have hA' := hA ω
    constructor
    · rintro ((h0 | h1) | h2)
      · refine mem_iUnion₂.2 ⟨0, Finset.mem_range.2 (by omega), Or.inl ?_⟩
        show ((Rf ω : ℝ) : ℂ) ∈ closure (range (F 0 ω))
        rw [hF' 0]
        exact Or.inl h0
      · obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h1
        refine mem_iUnion₂.2 ⟨k, hk, Or.inl ?_⟩
        show ((Rf ω : ℝ) : ℂ) ∈ closure (range (F k ω))
        rw [hF' k]
        exact Or.inr hkR
      · obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h2
        refine mem_iUnion₂.2 ⟨k, hk, Or.inr ?_⟩
        show ((Rf ω : ℝ) : ℂ) ∈ closure (range (A k ω))
        rw [hA' k]
        exact Or.inr hkR
    · intro h
      obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h
      rcases hkR with hkR | hkR
      · have hkR' : ((Rf ω : ℝ) : ℂ) ∈ closure (range (F k ω)) := hkR
        rw [hF' k] at hkR'
        rcases hkR' with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨k, hk, h1⟩))
      · have hkR' : ((Rf ω : ℝ) : ℂ) ∈ closure (range (A k ω)) := hkR
        rw [hA' k] at hkR'
        rcases hkR' with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (mem_iUnion₂.2 ⟨k, hk, h1⟩)
  -- the restart events and the offset at a first entry
  have hrst : ∀ m, MeasurableSet {ω | Rf ω ∈ GW1W.restartSet κ b jumps
      (ExplState.run κ b jumps spec (fun i => D i ω) m)} := fun m =>
    measurableSet_mem_restartSet_rand hb (isMeasState_run hb spec hDm hDreg m) hRf
  set RO : ℕ → Set Ω := fun e => {ω | relOffOf κ θ b jumps (Rf ω) (fun i => D i ω) e = o} with hRO
  have hROm : ∀ e, MeasurableSet (RO e) := by
    intro e
    set T := {ω | Rf ω ∈ GW1W.restartSet κ b jumps
      (ExplState.run κ b jumps spec (fun i => D i ω) (2 * (e / 2) + 1))}
    have hT : MeasurableSet T := hrst _
    have e1 : RO e = (T ∩ {_ω | e % 2 = 1 ∧ 2 * (e / 2) + 2 = o}) ∪
        ((T ∩ {_ω | e % 2 = 1})ᶜ ∩ {_ω | 2 * (e / 2) = o}) := by
      ext ω
      simp only [hRO, relOffOf, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, T, hspec]
      by_cases h1 : e % 2 = 1 <;> by_cases h2 : Rf ω ∈ GW1W.restartSet κ b jumps
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun i => D i ω) (2 * (e / 2) + 1)) <;>
        simp [h1, h2]
    rw [e1]
    exact (hT.inter (MeasurableSet.const _)).union ((hT.inter (MeasurableSet.const _)).compl.inter
      (MeasurableSet.const _))
  refine ⟨⋃ e ∈ Finset.range (o + 2), Ent' e ∩ (⋂ n ∈ Finset.range e, (Ent' n)ᶜ) ∩ RO e,
    Finset.measurableSet_biUnion _ fun e _ => ((hEntm e).inter
      (Finset.measurableSet_biInter _ fun n _ => (hEntm n).compl)).inter (hROm e), fun ω hω => ?_⟩
  rw [relOffEvent_iff]
  simp only [mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff, Finset.mem_range, exists_prop, hRO,
    mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, by omega, ⟨(hEnt ω hω e).1 h1, fun n hn h4 => h2 n hn ((hEnt ω hω n).2 h4)⟩, h3⟩
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, by omega, ⟨(hEnt ω hω e).2 h1, fun n hn h4 => h2 n hn ((hEnt ω hω n).1 h4)⟩, h3⟩


/-- **The walk's point after `n` instructions is measurable for the past.** -/
theorem measurable_stPt_past {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (n : ℕ) :
    Measurable[pastSigma κ b jumps spec E n] fun ω => stPt (ExplState.run κ b jumps spec (fun j => E j ω) n) := by
  have hm := (isMeasState_run (κ := κ) hb spec hEm hreg n).2.1
  refine measurable_of_Iio (mδ := pastSigma κ b jumps spec E n) fun x => ?_
  exact measurableSet_pastSigma_of_runs runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j)
    (hm measurableSet_Iio) fun ω ω' he hω => by
      show stPt (ExplState.run κ b jumps spec (fun j => E j ω') n) < x
      rw [← he n le_rfl]; exact hω

end InteractingSLE.Theorem14.SB.Nc
