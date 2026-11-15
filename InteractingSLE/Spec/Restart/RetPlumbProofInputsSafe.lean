/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsClock

/-!
# Safe-event measurability from physical chart prefixes

Packet PROVE-RETPLUMB. The random-capacity hull can be removed from the list of
measurability inputs: a generating trace identifies it with the filling of the
physical prefix. Only the initial-event-supported prefix coordinates and the
physical survival event have to be observed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H fwdHull)
open Supp7 DomainMarkov.Aux79

/-- Strict physical survival implies strict capacity survival for a clock. -/
theorem coe_toNNReal_lt_capLife {C : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hC : IsClockOn C L) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < L) :
    ((C t).toNNReal : ℝ≥0∞) < capLife C L := by
  by_cases hL : L = ⊤
  · simpa only [capLife, hL, ite_eq_left] using ENNReal.coe_lt_top
  · have hLL : (L.toNNReal : ℝ≥0∞) ≤ L := (ENNReal.coe_toNNReal hL).le
    have hlt : t < L.toNNReal := by
      exact ENNReal.coe_lt_coe.1 (ht.trans_eq (ENNReal.coe_toNNReal hL).symm)
    have hCt := hC.strictMonoOn ht.le hLL hlt
    have hCL : 0 < C L.toNNReal := (hC.nonneg ht.le).trans_lt hCt
    simpa only [capLife, ite_eq_right hL, ENNReal.ofReal, ENNReal.coe_lt_coe] using
      (Real.toNNReal_lt_toNNReal_iff hCL).2 hCt

/-- At a good retained pair, survival can be tested in physical time. -/
theorem retClock_lt_retLife_iff {Ω : Type*} [MeasurableSpace Ω]
    {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {u r t : ℝ≥0} {x₂ : ℝ} {ω : Ω} (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hG : ω ∈ G r) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω ↔
      (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω := by
  constructor
  · exact lt_retLifeP_of_retClock_lt hd hG hp₂ hpair
  · intro ht
    rw [retClock_eq hd hG hp₂ hpair, retLife_eq]
    exact coe_toNNReal_lt_capLife (retChartPath_clock hd hG hp₂ hpair).1 ht

/-- A generating inverse-clock trace identifies the hull at the current clock
with the filled physical prefix. This uses the existing inverse-clock image
lemma, rather than a separate random-hull measurability premise. -/
theorem fwdHull_clock_eq_fillH {C : ℝ≥0 → ℝ} {L : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}
    {W : ℝ≥0 → ℝ} (hC : IsClockOn C L) (hc : Continuous Γ)
    (hgen : IsGeneratingTrace W (capLife C L) (fun q => Γ (invClock C L q)))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < L) :
    fwdHull (fun s : ℝ => W s.toNNReal) (C t).toNNReal = fillH (Γ '' Icc 0 t) := by
  have hq := coe_toNNReal_lt_capLife hC ht
  have him := image_invClock_Icc (Γ := Γ) hC hq.le
  rw [hC.invClock_apply ht.le] at him
  have hcompact : IsCompact ((fun q => Γ (invClock C L q)) '' Icc 0 (C t).toNNReal) := by
    rw [him]
    exact isCompact_Icc.image hc
  have hfill := (fillH_eq_iff_isFilling_of_isClosed hcompact.isBounded hcompact.isClosed
    (fun _ hz => hz.1)).1 (hgen.2.2 _ hq)
  simpa only [him] using hfill

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The hull identity for the canonical retained path follows directly from its
generating-trace property. No measurability of the chosen driver is used here. -/
theorem fwdHull_retClock_eq_fillH {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r t : ℝ≥0}
    {x₂ : ℝ} {ω : Ω} (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hG : ω ∈ G r) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    {W : ℝ≥0 → ℝ}
    (hgen : IsGeneratingTrace W (retLife G η₁' η₂' ζ₂ u r ω)
      (retPath G η₁' η₂' ζ₂ u r ω))
    (ht : (t : ℝ≥0∞) < retLifeP η₁' η₂' ζ₂ u r ω) :
    fwdHull (fun s : ℝ => W s.toNNReal) (retClock G η₁' η₂' ζ₂ u r t ω) =
      fillH (retChartPath G η₁' η₂' ζ₂ u r ω '' Icc 0 t) := by
  rw [retLife_eq, retPath, canonRetPath_zero] at hgen
  rw [retClock_eq hd hG hp₂ hpair]
  exact fwdHull_clock_eq_fillH (retChartPath_clock hd hG hp₂ hpair).1
    (retChartPath_continuous_zero hd hG hp₂ hpair).1 hgen ht

/-- Safe events supported on an initial event need no separate hull-measurability
input. The hull identity is only required where the continuation is alive. -/
theorem measurableSet_inter_lineSafe_of_prefix {F : Set Ω}
    {Γ : Ω → ℝ≥0 → ℂ} {Q : ℝ≥0 → Ω → ℝ≥0}
    {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {t : ℝ≥0}
    (hc : ∀ ω ∈ F, Continuous (Γ ω))
    (hm : ∀ s ≤ t, Measurable (F.indicator fun ω => Γ ω s))
    (hlive : MeasurableSet (F ∩ {ω | (Q t ω : ℝ≥0∞) < V ω}))
    (hull : ∀ ω ∈ F, (Q t ω : ℝ≥0∞) < V ω →
      fwdHull (fun s : ℝ => W s.toNNReal ω) (Q t ω) = fillH (Γ ω '' Icc 0 t))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ H) :
    MeasurableSet (F ∩ lineSafe Q W V C t) := by
  classical
  let ΓF : Ω → ℝ≥0 → ℂ := fun ω s => F.indicator (fun ω => Γ ω s) ω
  have he : ∀ ω ∈ F, ΓF ω = Γ ω := fun ω hω => funext fun _ => indicator_of_mem hω _
  have hcF : ∀ ω, Continuous (ΓF ω) := by
    intro ω
    by_cases hω : ω ∈ F
    · rw [he ω hω]
      exact hc ω hω
    · have hz : ΓF ω = fun _ => 0 := funext fun _ => indicator_of_notMem hω _
      rw [hz]
      exact continuous_const
  have hav := measurableSet_disjoint_of_hitting
    (measurable_fillH_image_Icc_of_prefix hcF hm)
    (fun ω => ⟨fillH_subset_H _, isOpen_H_diff_fillH (isCompact_Icc.image (hcF ω)).isBounded⟩)
    hC hCH
  have heq : F ∩ lineSafe Q W V C t =
      (F ∩ {ω | (Q t ω : ℝ≥0∞) < V ω}) ∩
        {ω | Disjoint C (fillH (ΓF ω '' Icc 0 t))} := by
    ext ω
    change (ω ∈ F ∧ ((Q t ω : ℝ≥0∞) < V ω ∧ _)) ↔ ((ω ∈ F ∧ _) ∧ _)
    constructor
    · rintro ⟨hω, hl, hd⟩
      refine ⟨⟨hω, hl⟩, ?_⟩
      change Disjoint C (fillH (ΓF ω '' Icc 0 t))
      rw [he ω hω, ← hull ω hω hl]
      exact hd
    · rintro ⟨⟨hω, hl⟩, hd⟩
      change Disjoint C (fillH (ΓF ω '' Icc 0 t)) at hd
      rw [he ω hω, ← hull ω hω hl] at hd
      exact ⟨hω, hl, hd⟩
  rw [heq]
  exact hlive.inter hav

end InteractingSLE.Restart.RetAux79
