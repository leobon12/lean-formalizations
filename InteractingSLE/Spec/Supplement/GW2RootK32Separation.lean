/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Buffer

/-!
# Exact separation tests for the switched physical buffer

Packet PROVE-T14-GW2ROOT2. These are properties of the landed J31 formula,
with its real root translation and its complete prefix. They hold on all
records, including zero time caps. No conditional comparison is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootK32

open Exist.StagedLaw Restart Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD RootG28 RootJ31

theorem mul_fraction_eq {u t : ℝ≥0} (h : u ≤ t) : t * (u / t) = u := by
  by_cases ht : t = 0
  · have hu : u = 0 := le_antisymm (ht ▸ h) bot_le
    simp only [ht, hu, zero_div, mul_zero]
  · exact mul_div_cancel₀ u ht

theorem separationRead_nonneg (x : ℝ) (s v t : ℝ≥0) (p : RecData × RecData) :
    0 ≤ RootJ31.separationRead x s v t p := by
  rw [RootJ31.separationRead_eq_compact]
  exact squareMin_nonneg
    (continuous_prefixIntegrand ((continuous_const (y := (x : ℂ))).add
      (continuous_frozenTraceRead v p.2)).continuousOn
      (continuous_frozenTraceRead s p.1).continuousOn)
    (fun _ => separationValue_nonneg _ _)

/-- Every pair of points in the two closed prefixes bounds their separation
minimum. Division by a zero time cap is handled explicitly. -/
theorem separationRead_le_value (x : ℝ) (s v t : ℝ≥0) (p : RecData × RecData)
    {u w : ℝ≥0} (hu : u ≤ t) (hw : w ≤ s) :
    RootJ31.separationRead x s v t p ≤
      separationValue ((x : ℂ) + frozenTraceRead v p.2 u) (frozenTraceRead s p.1 w) := by
  rw [RootJ31.separationRead_eq_compact]
  have hc : Continuous (prefixIntegrand (fun u => (x : ℂ) + frozenTraceRead v p.2 u)
      (frozenTraceRead s p.1) t s) :=
    continuous_prefixIntegrand
      ((continuous_const (y := (x : ℂ))).add (continuous_frozenTraceRead v p.2)).continuousOn
      (continuous_frozenTraceRead s p.1).continuousOn
  obtain ⟨q, hq, hmin⟩ := exists_squareMin hc
  rw [compactSeparation, hq]
  let z : UnitSquare :=
    (⟨u / t, bot_le, div_le_one_of_le₀ hu bot_le⟩,
      ⟨w / s, bot_le, div_le_one_of_le₀ hw bot_le⟩)
  simpa only [prefixIntegrand, z, mul_fraction_eq hu, mul_fraction_eq hw] using hmin z

theorem separationRead_le_one (x : ℝ) (s v t : ℝ≥0) (p : RecData × RecData) :
    RootJ31.separationRead x s v t p ≤ 1 :=
  (separationRead_le_value x s v t p (u := 0) (w := 0) bot_le bot_le).trans
    (min_le_left _ _)

/-- Positivity of the actual readout is precisely noncontact of all prefix
points, with no strict-endpoint convention hidden in the statement. -/
theorem separationRead_pos_iff (x : ℝ) (s v t : ℝ≥0) (p : RecData × RecData) :
    0 < RootJ31.separationRead x s v t p ↔
      ∀ u ≤ t, ∀ w ≤ s,
        ((x : ℂ) + frozenTraceRead v p.2 u) * frozenTraceRead s p.1 w + 1 ≠ 0 := by
  constructor
  · intro h u hu w hw
    exact (separationValue_pos_iff _ _).mp
      (h.trans_le (separationRead_le_value x s v t p hu hw))
  · intro h
    rw [RootJ31.separationRead_eq_compact]
    apply squareMin_pos
      (continuous_prefixIntegrand ((continuous_const (y := (x : ℂ))).add
        (continuous_frozenTraceRead v p.2)).continuousOn
        (continuous_frozenTraceRead s p.1).continuousOn)
    intro q
    exact (separationValue_pos_iff _ _).mpr
      (h _ (fraction_mul_le t q.1) _ (fraction_mul_le s q.2))

/-- Enlarging the explored prefix can only decrease its separation gauge. -/
theorem antitone_separationRead (x : ℝ) (s v : ℝ≥0) (p : RecData × RecData) :
    Antitone (fun t => RootJ31.separationRead x s v t p) := by
  intro t t' htt'
  change RootJ31.separationRead x s v t' p ≤ RootJ31.separationRead x s v t p
  rw [RootJ31.separationRead_eq_compact x s v t p]
  have hc : Continuous (prefixIntegrand (fun u => (x : ℂ) + frozenTraceRead v p.2 u)
      (frozenTraceRead s p.1) t s) :=
    continuous_prefixIntegrand
      ((continuous_const (y := (x : ℂ))).add (continuous_frozenTraceRead v p.2)).continuousOn
      (continuous_frozenTraceRead s p.1).continuousOn
  obtain ⟨q, hq, _⟩ := exists_squareMin hc
  rw [compactSeparation, hq]
  exact separationRead_le_value x s v t' p
    ((fraction_mul_le t q.1).trans htt') (fraction_mul_le s q.2)

/-- First inversion contact of the full translated reconstructed prefix. -/
def translatedContact (x : ℝ) (s v : ℝ≥0) (p : RecData × RecData) : ℝ≥0∞ :=
  firstContactTime (fun t => sphereInv (((x : ℂ) + frozenTraceRead v p.2 t : ℂ) : OnePoint ℂ))
    ((fun u => (frozenTraceRead s p.1 u : OnePoint ℂ)) '' Icc 0 s)

theorem separationRead_eq_zero_at_contact (x : ℝ) (s v : ℝ≥0) (p : RecData × RecData)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) = translatedContact x s v p) :
    RootJ31.separationRead x s v T p = 0 := by
  have hK : IsCompact ((fun u => (frozenTraceRead s p.1 u : OnePoint ℂ)) '' Icc 0 s) :=
    isCompact_Icc.image
      (OnePoint.continuous_coe.comp (continuous_frozenTraceRead s p.1))
  obtain ⟨u, hu, he⟩ := firstContactTime_mem
    (continuous_sphereInv.comp (OnePoint.continuous_coe.comp
      (continuous_const.add (continuous_frozenTraceRead v p.2)))) hK.isClosed hT.symm
  have hz := (SourceC.sphereInv_eq_iff _ _).mp he.symm
  change ((x : ℂ) + frozenTraceRead v p.2 T) * frozenTraceRead s p.1 u + 1 = 0 at hz
  apply le_antisymm _ (separationRead_nonneg _ _ _ _ _)
  have hle := separationRead_le_value x s v T p le_rfl hu.2
  simpa only [separationValue, hz, norm_zero, zero_div, min_eq_right zero_le_one] using hle

/-- The positive gauge and the strict first-contact convention agree exactly. -/
theorem separationRead_pos_iff_lt_contact (x : ℝ) (s v t : ℝ≥0) (p : RecData × RecData) :
    0 < RootJ31.separationRead x s v t p ↔ (t : ℝ≥0∞) < translatedContact x s v p := by
  constructor
  · intro h
    by_contra hn
    have hle := le_of_not_gt hn
    have hfin : translatedContact x s v p ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hle
    have he := ENNReal.coe_toNNReal hfin
    have ht : (translatedContact x s v p).toNNReal ≤ t := by
      exact ENNReal.coe_le_coe.mp (he ▸ hle)
    have hz := separationRead_eq_zero_at_contact x s v p he
    have hm := antitone_separationRead x s v p ht
    change RootJ31.separationRead x s v t p ≤
      RootJ31.separationRead x s v (translatedContact x s v p).toNNReal p at hm
    rw [hz] at hm
    exact (not_le_of_gt h) hm
  · intro ht
    apply (separationRead_pos_iff x s v t p).mpr
    intro u hu w hw hz
    have hlt : (u : ℝ≥0∞) < translatedContact x s v p :=
      (ENNReal.coe_le_coe.mpr hu).trans_lt ht
    exact notMem_of_lt_firstContactTime hlt
      ⟨w, ⟨bot_le, hw⟩, ((SourceC.sphereInv_eq_iff _ _).mpr hz).symm⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootK32
