/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEMinimum

/-!
# Continuity and positivity of the causal separation readout

On continuous prefixes the rational readout is a compact separation minimum.
Freezing strictly inside the lifetime makes Mathlib's compact-minimum
continuity theorem apply locally without requiring a terminal trace value.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.GaugeE

open ReadD Exist.StagedLaw

/-- The normalized contact test is continuous jointly in both points. -/
theorem continuous_separationValue : Continuous fun p : ℂ × ℂ => separationValue p.1 p.2 :=
  continuous_const.min (((continuous_fst.mul continuous_snd).add_const 1).norm.div
    (continuous_const.add continuous_fst.norm) (fun p => by positivity))

/-- The normalized contact test on a compact rectangle, parametrized by
fractions in the unit square. -/
def prefixIntegrand (X A : ℝ≥0 → ℂ) (t s : ℝ≥0) (p : UnitSquare) : ℝ :=
  separationValue (X (t * p.1.val)) (A (s * p.2.val))

def compactSeparation (X A : ℝ≥0 → ℂ) (t s : ℝ≥0) : ℝ := squareMin (prefixIntegrand X A t s)

theorem fraction_mul_le (t : ℝ≥0) (q : UnitSegment) : t * q.val ≤ t := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left q.property.2 (zero_le : (0 : ℝ≥0) ≤ t)

theorem continuous_prefixIntegrand {X A : ℝ≥0 → ℂ} {t s : ℝ≥0}
    (hX : ContinuousOn X (Iic t)) (hA : ContinuousOn A (Iic s)) :
    Continuous (prefixIntegrand X A t s) := by
  have hx : Continuous fun p : UnitSquare => X (t * p.1.val) :=
    hX.comp_continuous (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
      (fun p => fraction_mul_le t p.1)
  have ha : Continuous fun p : UnitSquare => A (s * p.2.val) :=
    hA.comp_continuous (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
      (fun p => fraction_mul_le s p.2)
  exact continuous_separationValue.comp (hx.prodMk ha)

theorem continuous_compactSeparation {X A : ℝ≥0 → ℂ} (hX : Continuous X) (hA : Continuous A)
    (s : ℝ≥0) : Continuous fun t => compactSeparation X A t s := by
  apply continuous_squareMin
  have hx : Continuous fun p : ℝ≥0 × UnitSquare => X (p.1 * p.2.1.val) :=
    hX.comp (continuous_fst.mul (continuous_subtype_val.comp (continuous_fst.comp continuous_snd)))
  have ha : Continuous fun p : ℝ≥0 × UnitSquare => A (s * p.2.2.val) :=
    hA.comp (continuous_const.mul (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  exact continuous_separationValue.comp (hx.prodMk ha)

/-- The countable Borel readout is the actual compact minimum on continuous
explored and retained prefixes. -/
theorem separationRead_eq_compact (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ)
    (hX : ContinuousOn (fun u => physicalTrace s u (r, w)) (Iic t))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) :
    separationRead s t (r, w) =
      compactSeparation (fun u => physicalTrace s u (r, w)) (fun v => recordTrace v r) t s := by
  have hc := continuous_prefixIntegrand hX hA
  have he := rationalInf_eq_squareMin hc
  have hn := squareMin_nonneg hc (fun p => separationValue_nonneg _ _)
  unfold separationRead
  change (⨅ q : RationalUnit × RationalUnit,
    ENNReal.ofReal (prefixIntegrand (fun u => physicalTrace s u (r, w)) (fun v => recordTrace v r) t s
      (Prod.map fractionCast fractionCast q))).toReal = _
  rw [he, ENNReal.toReal_ofReal hn]
  rfl

/-- On a live continuous reconstructed trace, the separation readout is
continuous before life. No terminal extension is assumed. -/
theorem continuousOn_separationRead (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) {L : ℝ≥0∞}
    (hX : ContinuousOn (fun u => physicalTrace s u (r, w)) {u | (u : ℝ≥0∞) < L})
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) :
    ContinuousOn (fun t => separationRead s t (r, w)) {t | (t : ℝ≥0∞) < L} := by
  intro t ht
  obtain ⟨B, htB, hB⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htB' : t < B := ENNReal.coe_lt_coe.1 htB
  let X := fun u => physicalTrace s u (r, w)
  let A := fun v => recordTrace v r
  let Xf := fun u => X (min u B)
  let Af := fun v => A (min v s)
  have hXB : ContinuousOn X (Iic B) := hX.mono fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt hB
  have hXf : Continuous Xf := hXB.comp_continuous (continuous_id.min continuous_const) (fun u => min_le_right u B)
  have hAf : Continuous Af := hA.comp_continuous (continuous_id.min continuous_const) (fun v => min_le_right v s)
  have he : ∀ u ≤ B, separationRead s u (r, w) = compactSeparation Xf Af u s := by
    intro u hu
    rw [separationRead_eq_compact s u r w (hXB.mono (Iic_subset_Iic.2 hu)) hA]
    apply congrArg squareMin
    funext p
    change separationValue (X (u * p.1.val)) (A (s * p.2.val)) =
      separationValue (X (min (u * p.1.val) B)) (A (min (s * p.2.val) s))
    rw [min_eq_left ((fraction_mul_le u p.1).trans hu), min_eq_left (fraction_mul_le s p.2)]
  have hnear : (fun u => separationRead s u (r, w)) =ᶠ[𝓝 t] (fun u => compactSeparation Xf Af u s) :=
    Filter.mem_of_superset (Iic_mem_nhds htB') (fun u hu => he u hu)
  exact ((continuous_compactSeparation hXf hAf s).continuousAt.congr_of_eventuallyEq hnear).continuousWithinAt

/-- Compact noncontact gives a strictly positive readout. -/
theorem separationRead_pos (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ)
    (hX : ContinuousOn (fun u => physicalTrace s u (r, w)) (Iic t))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s))
    (hsep : ∀ u ≤ t, ∀ v ≤ s, physicalTrace s u (r, w) * recordTrace v r + 1 ≠ 0) :
    0 < separationRead s t (r, w) := by
  rw [separationRead_eq_compact s t r w hX hA]
  apply squareMin_pos (continuous_prefixIntegrand hX hA)
  intro p
  exact (separationValue_pos_iff _ _).2 (hsep _ (fraction_mul_le t p.1) _ (fraction_mul_le s p.2))

/-- Every pair of prefix points bounds the compact separation minimum from
above, including irrational retained time fractions. -/
theorem separationRead_le_value (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (hs : 0 < s)
    (hX : ContinuousOn (fun u => physicalTrace s u (r, w)) (Iic t))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) {v : ℝ≥0} (hv : v ≤ s) :
    separationRead s t (r, w) ≤ separationValue (physicalTrace s t (r, w)) (recordTrace v r) := by
  rw [separationRead_eq_compact s t r w hX hA]
  obtain ⟨p, hp, hmin⟩ := exists_squareMin (continuous_prefixIntegrand hX hA)
  rw [compactSeparation, hp]
  let q : UnitSquare := (⟨1, zero_le_one, le_rfl⟩, ⟨v / s, zero_le, (div_le_one hs).2 hv⟩)
  have hvs : s * (v / s) = v := by field_simp
  simpa only [prefixIntegrand, q, mul_one, hvs] using hmin q

end InteractingSLE.Supp8.GB6.GaugeE
