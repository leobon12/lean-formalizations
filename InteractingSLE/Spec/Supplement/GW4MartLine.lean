/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4MartFilt
import InteractingSLE.Spec.ZhanGT4.A1CanonFactor

/-!
# GW4's protected martingales, part 5: the phase law in the line filtration and a measurable phase

Packet PROVE-GW4-MART. Two generic steps between the physical lines and Aux. lemma 122's input.

* **`hasPhaseSafeLaw_lineFilt`**: if on every physical line with positive clock value before the lifetime `V` the
  field has, given the line σ-algebra `𝒢L t`, the protected-kernel law of the phase-`c` word at the clock value, then
  the phase-word law (S) holds in the line filtration with lifetime `V` (`hasPhaseSafeLaw_of_lineLaw` for the clocks
  capped at `N`, then `N = q + 1`, as `BW1Lines.hasSafeLaw_life_of_lineKernel`).
* **`exists_measurable_phase_lineFilt`**: if the phase `c` is lattice-valued and every event `{c ∈ B}` agrees almost
  surely on each live line event with an event of that line (`exists_measurableSet_iff_phase_line`), then there is a
  measurable lattice-valued version `c'`, equal to `c` almost surely on every live line event, whose events are events
  of the line filtration at every positive capacity time (follow-up 5 §3.2: "Right continuity of the retained
  filtration makes this constant measurable at time zero").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW4Fix.Mart

open Coupling Restart.DomainMarkov Restart.DomainMarkov.Aux79 Sec7.PhaseSel Sec7.PhaseClause

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ### The phase law in the line filtration -/

section Law

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}

/-- **The phase-word law (S) in the line filtration with lifetime `V`** from the phase line laws before `V`. -/
theorem hasPhaseSafeLaw_lineFilt [IsProbabilityMeasure P] (hκ : 0 < κ) {𝓖 : Filtration ℝ≥0 mΩ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    {a : ℝ≥0 → Ω → ℝ≥0∞} (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t)) {V : Ω → ℝ≥0∞}
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (hA : ∀ q t, MeasurableSet[𝒢L t] (liveLine a V q t))
    (hS : ∀ (C : Set ℂ), IsClosed C → ∀ t, MeasurableSet[𝓖 t]
      {ω | a t ω < V ω ∧ Disjoint C (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ ω, IsForceReg W VL VR V ω) (c : Ω → ℝ)
    (hline : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ≥0), ∀ᵐ ω ∂P, 0 < a t ω → a t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝒢L t] ω =
        cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 (fun ω => (a t ω).toNNReal) ω) :
    HasPhaseSafeLaw κ ρL ρR P (lineFilt 𝒢L a V hA) V W VL VR c X := by
  have hN : ∀ N : ℝ≥0, HasPhaseSafeLaw κ ρL ρR P (lineFilt 𝒢L a V hA) (fun ω => min (V ω) N) W VL VR c X := by
    intro N
    refine hasPhaseSafeLaw_of_lineLaw (Qc := BW1Chain.capClock a N) hκ (𝓖 := 𝓖) hX
      (BW1Chain.continuous_capClock hac N) (BW1Chain.monotone_capClock ham N) (BW1Chain.capClock_zero ha0 N)
      (BW1Chain.measurable_capClock haa N) 𝒢L h𝒢L h𝒢Lm ?_ ?_ ?_ c ?_
    · intro q _ D hD ψ t
      exact measurableSet_capPiece_lineFilt hD N (tsupport ψ) t
        (h𝒢L t _ (BW1Lines.measurableSet_lineSafe_capClock_life haa (hS _ (isClosed_tsupport ψ) t) N))
    · intro q
      have h := BW1Lines.reach_capClock_life (P := P) (F := univ) (a := a) (V := V)
        (fun q => (hreach q).mono fun _ h _ => h) N q
      filter_upwards [h] with ω hω hq using hω (mem_univ ω) hq
    · exact Eventually.of_forall fun ω => BW1Lines.isForceReg_mono (min_le_left _ _) (hreg ω)
    · intro ψ t
      filter_upwards [hline ψ t] with ω hω hpos hS'
      rw [BW1Lines.lineSafe_capClock_life_eq] at hS'
      obtain ⟨haN, haV, hdis⟩ := hS'
      have hcap : BW1Chain.capClock a N t ω = (a t ω).toNNReal := BW1Chain.capClock_eq_of_lt haN
      have hpos' : 0 < a t ω := by
        rw [hcap] at hpos
        exact (ENNReal.coe_pos.2 hpos : (0 : ℝ≥0∞) < (a t ω).toNNReal).trans_le ENNReal.coe_toNNReal_le_self
      rw [show cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 (BW1Chain.capClock a N t) ω =
          cfAt κ W (phaseProc κ ρL ρR W VL VR c) ψ 1 (fun ω => (a t ω).toNNReal) ω by
        simp only [cfAt, hcap]]
      exact hω hpos' haV hdis
  intro ψ q hq D hD hDs
  refine hN (q + 1) ψ q hq D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hqV, hdis⟩ := h1 hωD
  exact ⟨lt_min hqV (ENNReal.coe_lt_coe.2 (lt_add_one q)), hdis⟩

end Law

/-! ### A measurable version of the phase -/

section Version

theorem measurableSet_lattice (d : ℝ) : MeasurableSet {x : ℝ | ∃ j : ℤ, x = j * d} := by
  have e : {x : ℝ | ∃ j : ℤ, x = j * d} = ⋃ j : ℤ, {(j : ℝ) * d} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_singleton_iff]
  rw [e]
  exact MeasurableSet.iUnion fun j => measurableSet_singleton _

omit mΩ in
/-- The live events of the lines are covered by those of the lines at a countable dense set of times. -/
theorem exists_rat_live {a : ℝ≥0 → Ω → ℝ≥0∞} (hac : ∀ ω, Continuous fun t => a t ω) {V : Ω → ℝ≥0∞}
    {t : ℝ≥0} {ω : Ω} (h : 0 < a t ω ∧ a t ω < V ω) :
    ∃ r : ℕ, 0 < a (TopologicalSpace.denseSeq ℝ≥0 r) ω ∧ a (TopologicalSpace.denseSeq ℝ≥0 r) ω < V ω := by
  have ho : IsOpen {s : ℝ≥0 | 0 < a s ω ∧ a s ω < V ω} :=
    (isOpen_lt continuous_const (hac ω)).inter (isOpen_lt (hac ω) continuous_const)
  exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).exists_mem_open ho ⟨t, h⟩

/-- **A measurable lattice-valued version of a phase readable on the lines.** -/
theorem exists_measurable_phase_lineFilt {𝒢L : ℝ≥0 → MeasurableSpace Ω} (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (hnull : ∀ t, Ito.nullSets P ≤ 𝒢L t) {a : ℝ≥0 → Ω → ℝ≥0∞} (hac : ∀ ω, Continuous fun t => a t ω)
    (ham : ∀ t, Measurable (a t)) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hA : ∀ q t, MeasurableSet[𝒢L t] (liveLine a V q t)) {d : ℝ} {c : Ω → ℝ}
    (hlat : ∀ ω, ∃ j : ℤ, c ω = j * d)
    (hread : ∀ (t : ℝ≥0) (B : Set ℝ), MeasurableSet B → ∃ S : Set Ω, MeasurableSet[𝒢L t] S ∧
      ∀ᵐ ω ∂P, 0 < a t ω ∧ a t ω < V ω → (c ω ∈ B ↔ ω ∈ S)) :
    ∃ c' : Ω → ℝ, Measurable c' ∧ (∀ ω, ∃ j : ℤ, c' ω = j * d) ∧
      (∀ t, ∀ᵐ ω ∂P, 0 < a t ω → a t ω < V ω → c' ω = c ω) ∧
      ∀ q : ℝ≥0, 0 < q → ∀ B : Set ℝ, MeasurableSet B →
        MeasurableSet[lineFilt 𝒢L a V hA q] {ω | c' ω ∈ B} := by
  set Et : ℝ≥0 → Set Ω := fun t => {ω | 0 < a t ω ∧ a t ω < V ω} with hEt
  have hEtm : ∀ t, MeasurableSet (Et t) := fun t =>
    (measurableSet_lt measurable_const (ham t)).inter (measurableSet_lt (ham t) hVm)
  set E : Set Ω := ⋃ r : ℕ, Et (TopologicalSpace.denseSeq ℝ≥0 r) with hE
  have hEm : MeasurableSet E := MeasurableSet.iUnion fun r => hEtm _
  have hEtE : ∀ t, Et t ⊆ E := fun t ω hω => by
    obtain ⟨r, hr⟩ := exists_rat_live hac hω
    exact mem_iUnion.2 ⟨r, hr⟩
  -- the indicator of `c` on `E` is null measurable
  have hf : NullMeasurable (E.indicator c) P := by
    intro B hB
    have e : E.indicator c ⁻¹' B =
        (⋃ r : ℕ, Et (TopologicalSpace.denseSeq ℝ≥0 r) ∩ c ⁻¹' B) ∪ (Eᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
      ext ω
      by_cases hω : ω ∈ E
      · simp only [mem_preimage, indicator_of_mem hω, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff,
          mem_ofPred_eq, hω, not_true_eq_false, false_and, or_false]
        constructor
        · intro h
          obtain ⟨r, hr⟩ := mem_iUnion.1 hω
          exact ⟨r, hr, h⟩
        · rintro ⟨r, -, h⟩
          exact h
      · simp only [mem_preimage, indicator_of_notMem hω, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff,
          mem_ofPred_eq, hω, not_false_eq_true, true_and]
        constructor
        · exact Or.inr
        · rintro (⟨r, hr, -⟩ | h)
          · exact absurd (mem_iUnion.2 ⟨r, hr⟩) hω
          · exact h
    rw [e]
    refine NullMeasurableSet.union (NullMeasurableSet.iUnion fun r => ?_) ?_
    · obtain ⟨S, hS, hSe⟩ := hread (TopologicalSpace.denseSeq ℝ≥0 r) B hB
      refine ((hEtm (TopologicalSpace.denseSeq ℝ≥0 r)).inter ((h𝒢Lm _) _ hS)).nullMeasurableSet.congr
        (Filter.eventuallyEqSet_iff.2 ?_)
      filter_upwards [hSe] with ω hω
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hω h1).2 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hω h1).1 h2⟩
    · exact (hEm.compl.inter (MeasurableSet.const _)).nullMeasurableSet
  have hae := hf.aemeasurable
  set c₁ : Ω → ℝ := hae.mk _ with hc₁
  have hc₁m : Measurable c₁ := hae.measurable_mk
  have hc₁e : E.indicator c =ᵐ[P] c₁ := hae.ae_eq_mk
  set Λ : Set Ω := c₁ ⁻¹' {x : ℝ | ∃ j : ℤ, x = j * d} with hΛ
  have hΛm : MeasurableSet Λ := hc₁m (measurableSet_lattice d)
  classical
  set c' : Ω → ℝ := fun ω => if ω ∈ Λ then c₁ ω else 0 with hc'
  have hc'm : Measurable c' := Measurable.ite hΛm hc₁m measurable_const
  have hc'lat : ∀ ω, ∃ j : ℤ, c' ω = j * d := by
    intro ω
    by_cases hω : ω ∈ Λ
    · simp only [hc', hω, ↓reduceIte]
      exact hω
    · simp only [hc', hω, ↓reduceIte]
      exact ⟨0, by simp⟩
  have hc'eq : ∀ t, ∀ᵐ ω ∂P, 0 < a t ω → a t ω < V ω → c' ω = c ω := by
    intro t
    filter_upwards [hc₁e] with ω hω h1 h2
    have hωE : ω ∈ E := hEtE t ⟨h1, h2⟩
    rw [indicator_of_mem hωE] at hω
    have hΛω : ω ∈ Λ := by
      show c₁ ω ∈ {x : ℝ | ∃ j : ℤ, x = j * d}
      rw [← hω]
      exact hlat ω
    simp only [hc', hΛω, ↓reduceIte]
    exact hω.symm
  refine ⟨c', hc'm, hc'lat, hc'eq, fun q hq B hB => ⟨hc'm hB, fun t => ?_⟩⟩
  obtain ⟨S, hS, hSe⟩ := hread t B hB
  refine ZhanGT4.A1Canon.measurableSet_of_ae_eq_of_nullSets_le (h𝒢Lm t) (hnull t)
    ((hc'm hB).inter ((h𝒢Lm t) _ (hA q t))) (hS.inter (hA q t)) ?_
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [hSe, hc'eq t] with ω h1 h2
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hB', hl⟩
    have hpos : 0 < a t ω := lt_of_lt_of_le (ENNReal.coe_pos.2 hq) hl.1
    rw [h2 hpos hl.2] at hB'
    exact ⟨(h1 ⟨hpos, hl.2⟩).1 hB', hl⟩
  · rintro ⟨hS', hl⟩
    have hpos : 0 < a t ω := lt_of_lt_of_le (ENNReal.coe_pos.2 hq) hl.1
    refine ⟨?_, hl⟩
    rw [h2 hpos hl.2]
    exact (h1 ⟨hpos, hl.2⟩).2 hS'

end Version

end InteractingSLE.Theorem14.GW4Fix.Mart
