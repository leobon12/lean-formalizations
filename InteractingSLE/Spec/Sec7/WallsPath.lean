/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordInWalls
import InteractingSLE.Spec.Sec7.Aux37WallsR7
import InteractingSLE.Spec.Sec7.Lemma71QSide
import InteractingSLE.Spec.Sec4.SpecialOrder

/-!
# Pathwise wall inputs from rational first exits

PROVE-WALLS-PATH. The missing probabilistic input is stated explicitly as `hfirst`:
at every positive rational own time the counterflow first meets the inverted wall
prefix at its endpoint. No assertion here discharges that restart law. Continuity
extends its consequences to every own time, giving both wall inputs of Aux. 37.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec7.WallsPath

open WangWu (negInv)
open PocketJordan

section Deterministic

variable {R : ℝ≥0 → ℂ} {η : ℝ → ℂ}

/-- Rational first exits imply reverse visits at arbitrary positive own times.
The limit uses a compact counterflow prefix, so no terminal-time limit is assumed. -/
theorem isWallReverseVisit_of_rat_firstHit (hR : Continuous R)
    (hRne : ∀ a : ℝ≥0, 0 < a → R a ≠ 0) (hη : ContinuousOn η (Ici 0))
    (hfirst : ∀ q : ℚ, 0 < q → ∃ T : ℝ,
      Sec4.IsFirstHitPoint η T (negInv '' (R '' Ioc 0 (StripSys.rt q)))
        (negInv (R (StripSys.rt q)))) : IsWallReverseVisit R η := by
  intro t a b ha hab hvisit
  rcases hab.eq_or_lt with he | hab
  · simpa only [← he] using hvisit
  obtain ⟨s, hs, hηs⟩ := hvisit
  obtain ⟨qs, -, hqs, hlim⟩ := Real.exists_seq_rat_strictAnti_tendsto (b : ℝ)
  have hqpos : ∀ n, (0 : ℚ) < qs n := fun n => by
    exact_mod_cast (lt_of_le_of_lt b.coe_nonneg (hqs n))
  have hvis : ∀ n, negInv (R (StripSys.rt (qs n))) ∈ η '' Icc 0 t := by
    intro n
    obtain ⟨T, v, hv, hvhit, -, hbefore⟩ := hfirst (qs n) (hqpos n)
    have haq : a ≤ StripSys.rt (qs n) := by
      change a ≤ (qs n : ℝ).toNNReal
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by exact_mod_cast (hqpos n).le)]
      exact (show (a : ℝ) ≤ b from hab.le).trans (hqs n).le
    have hsA : η s ∈ negInv '' (R '' Ioc 0 (StripSys.rt (qs n))) :=
      hηs ▸ ⟨R a, ⟨a, ⟨ha, haq⟩, rfl⟩, rfl⟩
    have hvs : v ≤ s := Sec4.le_of_forall_notMem_of_mem hbefore hs.1 hsA
    exact ⟨v, ⟨hv.1, hvs.trans hs.2⟩, hvhit⟩
  have hlim' : Tendsto (fun n => StripSys.rt (qs n)) atTop (𝓝 b) := by
    convert (continuous_real_toNNReal.tendsto (b : ℝ)).comp hlim using 1
    · rfl
    · exact congrArg nhds (show (b : ℝ).toNNReal = b from Real.toNNReal_coe).symm
  have hc : ContinuousAt (fun a => negInv (R a)) b :=
    (WangWu.continuousAt_negInv (hRne b (ha.trans hab))).comp hR.continuousAt
  exact (isCompact_Icc.image_of_continuousOn (hη.mono Icc_subset_Ici_self)).isClosed.mem_of_tendsto
    (hc.tendsto.comp hlim') (Eventually.of_forall hvis)

/-- The same rational first-exit law gives every positive-time wall point a visit. -/
theorem walls_of_rat_firstHit (hR : Continuous R)
    (hRne : ∀ a : ℝ≥0, 0 < a → R a ≠ 0) (hη : ContinuousOn η (Ici 0))
    (hfirst : ∀ q : ℚ, 0 < q → ∃ T : ℝ,
      Sec4.IsFirstHitPoint η T (negInv '' (R '' Ioc 0 (StripSys.rt q)))
        (negInv (R (StripSys.rt q)))) :
    IsWallReverseVisit R η ∧ IsWallVisited R η := by
  have hrev := isWallReverseVisit_of_rat_firstHit hR hRne hη hfirst
  refine ⟨hrev, fun b hb => ?_⟩
  obtain ⟨q, hq0, hqb⟩ := exists_rat_btwn (show (0 : ℝ) < b from hb)
  have hq : (0 : ℚ) < q := by exact_mod_cast hq0
  obtain ⟨T, v, hv, hvhit, -, -⟩ := hfirst q hq
  have hr0 : 0 < StripSys.rt q := Real.toNNReal_pos.2 hq0
  have hrb : StripSys.rt q ≤ b := by
    change (q : ℝ).toNNReal ≤ b
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0.le]
    exact hqb.le
  exact ⟨T, hrev T _ b hr0 hrb ⟨v, hv, hvhit⟩⟩

end Deterministic

/-- Increasing common prefixes transfer the wall properties to the unchanged
extremal path. No separate first-exit law for that path is needed. -/
theorem walls_of_prefixes {β : ℝ≥0 → ℂ} {Lr : ℚ → ℝ≥0 → ℂ} {η : ℝ → ℂ}
    (hprefix : ∀ q : ℚ, 0 < q → ∀ t : ℝ≥0, t ≤ StripSys.rt q → Lr q t = β t)
    (hwalls : ∀ q : ℚ, 0 < q → IsWallReverseVisit (Lr q) η ∧ IsWallVisited (Lr q) η) :
    IsWallReverseVisit β η ∧ IsWallVisited β η := by
  have hbound : ∀ b : ℝ≥0, ∃ q : ℚ, 0 < q ∧ b ≤ StripSys.rt q := by
    intro b
    obtain ⟨q, hq⟩ := exists_rat_gt (b : ℝ)
    have hq0 : (0 : ℝ) < q := b.coe_nonneg.trans_lt hq
    refine ⟨q, by exact_mod_cast hq0, ?_⟩
    change b ≤ (q : ℝ).toNNReal
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0.le]
    exact hq.le
  constructor
  · intro t a b ha hab hv
    obtain ⟨q, hq, hbq⟩ := hbound b
    have hval : negInv (Lr q a) ∈ η '' Icc 0 t := by
      rwa [hprefix q hq a (hab.trans hbq)]
    simpa only [hprefix q hq b hbq] using (hwalls q hq).1 t a b ha hab hval
  · intro a ha
    obtain ⟨q, hq, haq⟩ := hbound a
    simpa only [hprefix q hq a haq] using (hwalls q hq).2 a ha

/-- The common-prefix transfer uses a single conull set for the rational family. -/
theorem ae_walls_of_prefixes {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {β : Ω → ℝ≥0 → ℂ} {Lr : ℚ → Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hprefix : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      ∀ t : ℝ≥0, t ≤ StripSys.rt q → Lr q ω t = β ω t)
    (hwalls : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P,
      IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω)) :
    ∀ᵐ ω ∂P, IsWallReverseVisit (β ω) (η ω) ∧ IsWallVisited (β ω) (η ω) := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < q →
      (∀ t : ℝ≥0, t ≤ StripSys.rt q → Lr q ω t = β ω t) ∧
      IsWallReverseVisit (Lr q ω) (η ω) ∧ IsWallVisited (Lr q ω) (η ω) := by
    intro q
    by_cases hq : 0 < q
    · filter_upwards [hprefix q hq, hwalls q hq] with ω hp hw _ using ⟨hp, hw⟩
    · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [ae_all_iff.2 hq] with ω hω
  exact walls_of_prefixes (fun q hq => (hω q hq).1) (fun q hq => (hω q hq).2)

/-- Countably many rational first-exit laws suffice almost surely. The first-exit
law remains an explicit hypothesis, separate from the proved pathwise adapter. -/
theorem ae_walls_of_rat_firstHit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {R : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hR : ∀ᵐ ω ∂P, Continuous (R ω) ∧ ∀ a : ℝ≥0, 0 < a → R ω a ≠ 0)
    (hη : ∀ᵐ ω ∂P, ContinuousOn (η ω) (Ici 0))
    (hfirst : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (StripSys.rt q)))
        (negInv (R ω (StripSys.rt q)))) :
    ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) := by
  have hf : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q → ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (StripSys.rt q)))
        (negInv (R ω (StripSys.rt q))) :=
    ae_all_iff.2 fun q => by
      by_cases hq : 0 < q
      · filter_upwards [hfirst q hq] with ω hω _ using hω
      · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hR, hη, hf] with ω hRω hηω hfω
  exact walls_of_rat_firstHit hRω.1 hRω.2 hηω hfω

/-- Specialization to the landed simple proper wall versions. -/
theorem ae_walls_of_simpleProper_rat_firstHit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {R : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ}
    (hR : ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (R ω))
    (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hfirst : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, ∃ T : ℝ,
      Sec4.IsFirstHitPoint (η ω) T (negInv '' (R ω '' Ioc 0 (StripSys.rt q)))
        (negInv (R ω (StripSys.rt q)))) :
    ∀ᵐ ω ∂P, IsWallReverseVisit (R ω) (η ω) ∧ IsWallVisited (R ω) (η ω) :=
  ae_walls_of_rat_firstHit (hR.mono fun _ hω =>
    ⟨hω.1, fun a ha => StripSysField.mem_H_ne_zero (hω.2.2.2.1 a ha)⟩)
    (Eventually.of_forall hη) hfirst

/-- Constant-angle order for the one-jump strip data, obtained from nonboundary
Proposition 5.5 and the landed conversion to the opposite open side. -/
theorem ae_order_const_prop74 (h55 : Lemma71H.Prop55HalfPlaneStatement.{u})
    {κ A B : ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : StripSys.IsStripSystem κ (prop74Data A B) {0} P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ ({0} : Finset ℝ) →
      prop74Data A B y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ ({0} : Finset ℝ) →
      sleLambda κ ≤ prop74Data A B y + a * chiC κ)
    {θR θL : ℝ} (hθR : θR ∈ Icc (-(π / 2)) (π / 2))
    (hθL : θL ∈ Icc (-(π / 2)) (π / 2)) (hθ : θR < θL)
    (hregR : ∀ ω, Exist.Staged.IsRegularDriver (Es (R7Aux131.constSpec θR) 0 ω))
    (hregL : ∀ ω, Exist.Staged.IsRegularDriver (Es (R7Aux131.constSpec θL) 0 ω))
    {R L : Ω → ℝ≥0 → ℂ}
    (hRc : ∀ ω, Continuous (R ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hRtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (R7Aux131.constSpec θR) 0 ω).1 ⊤ (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hL0 : ∀ ω, L ω 0 = 0)
    (hLtr : ∀ᵐ ω ∂P, IsGeneratingTrace (Es (R7Aux131.constSpec θL) 0 ω).1 ⊤ (L ω)) :
    ∀ᵐ ω ∂P, Disjoint (range (R ω)) (leftSideOf (range (L ω))) := by
  have htrR := Aux37Walls.ae_trace_const hS hcumL hcumR hθR hregR hRc hR0 hRtr
  have htrL := Aux37Walls.ae_trace_const hS hcumL hcumR hθL hregL hLc hL0 hLtr
  have hflR := Aux37Walls.isFlowLine_const hS hθR (htrR.mono fun _ hω => hω.1 ▸ hω.2.1)
  have hflL := Aux37Walls.isFlowLine_const hS hθL (htrL.mono fun _ hω => hω.1 ▸ hω.2.1)
  have hb : sleLambda κ - θR * chiC κ ≤ B := by
    have := hcumR θR hθR 1 (by norm_num) (by simp only [Finset.mem_singleton]; norm_num)
    simp only [prop74Data, not_lt_of_ge zero_le_one, ↓reduceIte] at this
    linarith only [this]
  have ha : sleLambda κ - π * chiC κ + θL * chiC κ ≤ A := by
    have := hcumL θL hθL (-1) (by norm_num) (by simp only [Finset.mem_singleton]; norm_num)
    simp only [prop74Data, neg_lt_zero.mpr zero_lt_one, ↓reduceIte] at this
    have hχ := mul_nonneg Real.pi_pos.le (Sec4.chiC_pos hS.kappa_pos hS.kappa_lt_four).le
    linarith only [this, hχ]
  filter_upwards [h55 κ hS.kappa_pos hS.kappa_lt_four A B θR θL hθ hb ha P h hS.gff
    R L _ _ hflR hflL, htrR, htrL] with ω ho hr hl
  exact Lemma71Q.disjoint_range_leftSideOf_of_subset_closedLeftSide
    ⟨hLc ω, hl.2.2.1, hL0 ω, hl.2.2.2.1, tendsto_norm_atTop_iff_cobounded.2 hl.2.2.2.2⟩
    ⟨hRc ω, hr.2.2.1, hR0 ω, hr.2.2.2.1, tendsto_norm_atTop_iff_cobounded.2 hr.2.2.2.2⟩
    (ho hr.1 hl.1)

end InteractingSLE.Sec7.WallsPath
