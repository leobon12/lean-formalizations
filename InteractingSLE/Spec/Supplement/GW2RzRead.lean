/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeETerminal
import InteractingSLE.Spec.Supplement.GW2RootA22Read

/-!
# GW2 at a root `x`: GB6's separation readout read through the re-centred chart (decision D8, layer 4a)

Packet PROVE-GW2-ROOTX, round 3. GB6's announced versions stop the relative coordinates at the level times of a causal
gauge of (record, relative path): the separation readout `ReadD.separationRead`, which reads the physical trace back
from the relative trace through the record's inverse chart. At a root `x` the relative path is re-centred at the root's
chart image, so the physical trace is read back from the relative trace moved by that image:

* `baseRead x s r` (the root's real chart image, from ROOT2's measurable boundary reader), `physicalTraceX`,
  `physicalTraceX_congr`, `separationReadX`, measurability;
* the readout lemmas of GB6 (`GaugeE`/`ReadD`), with the same proofs: `isCausal_separationReadX`,
  `le_separationReadX`, `separationReadX_eq_compact`, `continuousOn_separationReadX`, `separationReadX_pos`,
  `separationReadX_le_value`, `separationReadX_nonneg`, `tendsto_separationReadX_contact`,
  `tendsto_separationReadX_escape`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rz

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.GaugeE Supp8.GB6.RelDrv.Version GW2TipSystem

/-- **The real chart image of the root `x`** read from the record (ROOT2's measurable boundary reader). -/
def baseRead (x : ℝ) (s : ℝ≥0) (r : RecData) : ℝ := (RootA22.boundaryRead s (r, (x : ℂ))).re

theorem measurable_baseRead (x : ℝ) (s : ℝ≥0) : Measurable (baseRead x s) :=
  Complex.measurable_re.comp ((RootA22.measurable_boundaryRead s).comp (measurable_id.prodMk measurable_const))

/-- **The physical trace at a root `x`** read back from a re-centred relative path: the relative trace, moved back by
the root's chart image, pulled back through the record's inverse chart. -/
def physicalTraceX (x : ℝ) (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℂ :=
  inverseRead s (p.1, LP.traceAt t p.2 + (baseRead x s p.1 : ℂ))

theorem measurable_physicalTraceX (x : ℝ) (s t : ℝ≥0) : Measurable (physicalTraceX x s t) :=
  (measurable_inverseRead s).comp (measurable_fst.prodMk (((LP.measurable_traceAt t).comp measurable_snd).add
    (Complex.measurable_ofReal.comp ((measurable_baseRead x s).comp measurable_fst))))

theorem physicalTraceX_congr (x : ℝ) (s t : ℝ≥0) (r : RecData) {w w' : ℝ≥0 → ℝ}
    (h : ∀ u ≤ t, w u = w' u) : physicalTraceX x s t (r, w) = physicalTraceX x s t (r, w') := by
  unfold physicalTraceX
  rw [LP.traceAt_congr h]

/-- **GB6's separation readout at a root `x`**: the rational prefix infimum of the normalized contact test between
the read-back physical trace at `x` and the record's retained trace. -/
def separationReadX (x : ℝ) (s : ℝ≥0) : GaugeReadout := fun t p =>
  (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (separationValue (physicalTraceX x s (t * (q.1.val : ℝ≥0)) p)
      (recordTrace (s * (q.2.val : ℝ≥0)) p.1))).toReal

theorem measurable_separationReadX (x : ℝ) (s t : ℝ≥0) : Measurable (separationReadX x s t) := by
  apply ENNReal.measurable_toReal.comp
  apply Measurable.iInf
  intro q
  apply Measurable.ennreal_ofReal
  unfold separationValue
  exact measurable_const.min
    (((measurable_physicalTraceX x s _).mul ((measurable_recordTrace _).comp measurable_fst)).add_const 1 |>.norm
      |>.div (measurable_const.add (measurable_physicalTraceX x s _).norm))

theorem isCausal_separationReadX (x : ℝ) (s : ℝ≥0) : IsCausal (separationReadX x s) := by
  intro t r w w' h
  unfold separationReadX
  apply congrArg ENNReal.toReal
  apply iInf_congr
  intro q
  have hq : (q.1.val : ℝ≥0) ≤ 1 := by exact_mod_cast q.1.property
  have hqt : t * (q.1.val : ℝ≥0) ≤ t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (zero_le : (0 : ℝ≥0) ≤ t)
  have he := physicalTraceX_congr x s (t * (q.1.val : ℝ≥0)) r (fun u hu => h u (hu.trans hqt))
  exact congrArg (fun z : ℂ => ENNReal.ofReal
    (separationValue z (recordTrace (s * (q.2.val : ℝ≥0)) r))) he

/-- Positivity of a uniform physical separation bound survives the rational
prefix infimum. This does not assert a bound for irregular readouts. -/
theorem le_separationReadX (x : ℝ) (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ q : RationalUnit × RationalUnit, c ≤
      separationValue (physicalTraceX x s (t * (q.1.val : ℝ≥0)) p)
        (recordTrace (s * (q.2.val : ℝ≥0)) p.1)) : c ≤ separationReadX x s t p := by
  let q0 : RationalUnit := ⟨0, zero_le_one⟩
  have hbound : (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
      (separationValue (physicalTraceX x s (t * (q.1.val : ℝ≥0)) p)
        (recordTrace (s * (q.2.val : ℝ≥0)) p.1))) ≤ 1 := by
    exact (iInf_le _ (q0, q0)).trans (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (separationValue_le_one _ _))
  have hle : ENNReal.ofReal c ≤ ⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
      (separationValue (physicalTraceX x s (t * (q.1.val : ℝ≥0)) p)
        (recordTrace (s * (q.2.val : ℝ≥0)) p.1)) :=
    le_iInf fun q => ENNReal.ofReal_le_ofReal (h q)
  have ht := ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hbound) hle
  simpa only [ENNReal.toReal_ofReal hc, separationReadX] using ht

/-- The countable Borel readout is the actual compact minimum on continuous
explored and retained prefixes. -/
theorem separationReadX_eq_compact (x : ℝ) (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ)
    (hX : ContinuousOn (fun u => physicalTraceX x s u (r, w)) (Iic t))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) :
    separationReadX x s t (r, w) =
      compactSeparation (fun u => physicalTraceX x s u (r, w)) (fun v => recordTrace v r) t s := by
  have hc := continuous_prefixIntegrand hX hA
  have he := rationalInf_eq_squareMin hc
  have hn := squareMin_nonneg hc (fun p => separationValue_nonneg _ _)
  unfold separationReadX
  change (⨅ q : RationalUnit × RationalUnit,
    ENNReal.ofReal (prefixIntegrand (fun u => physicalTraceX x s u (r, w)) (fun v => recordTrace v r) t s
      (Prod.map fractionCast fractionCast q))).toReal = _
  rw [he, ENNReal.toReal_ofReal hn]
  rfl

/-- On a live continuous reconstructed trace, the separation readout is
continuous before life. No terminal extension is assumed. -/
theorem continuousOn_separationReadX (x : ℝ) (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) {L : ℝ≥0∞}
    (hX : ContinuousOn (fun u => physicalTraceX x s u (r, w)) {u | (u : ℝ≥0∞) < L})
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) :
    ContinuousOn (fun t => separationReadX x s t (r, w)) {t | (t : ℝ≥0∞) < L} := by
  intro t ht
  obtain ⟨B, htB, hB⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htB' : t < B := ENNReal.coe_lt_coe.1 htB
  let X := fun u => physicalTraceX x s u (r, w)
  let A := fun v => recordTrace v r
  let Xf := fun u => X (min u B)
  let Af := fun v => A (min v s)
  have hXB : ContinuousOn X (Iic B) := hX.mono fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt hB
  have hXf : Continuous Xf := hXB.comp_continuous (continuous_id.min continuous_const) (fun u => min_le_right u B)
  have hAf : Continuous Af := hA.comp_continuous (continuous_id.min continuous_const) (fun v => min_le_right v s)
  have he : ∀ u ≤ B, separationReadX x s u (r, w) = compactSeparation Xf Af u s := by
    intro u hu
    rw [separationReadX_eq_compact x s u r w (hXB.mono (Iic_subset_Iic.2 hu)) hA]
    apply congrArg squareMin
    funext p
    change separationValue (X (u * p.1.val)) (A (s * p.2.val)) =
      separationValue (X (min (u * p.1.val) B)) (A (min (s * p.2.val) s))
    rw [min_eq_left ((fraction_mul_le u p.1).trans hu), min_eq_left (fraction_mul_le s p.2)]
  have hnear : (fun u => separationReadX x s u (r, w)) =ᶠ[𝓝 t] (fun u => compactSeparation Xf Af u s) :=
    Filter.mem_of_superset (Iic_mem_nhds htB') (fun u hu => he u hu)
  exact ((continuous_compactSeparation hXf hAf s).continuousAt.congr_of_eventuallyEq hnear).continuousWithinAt

/-- Compact noncontact gives a strictly positive readout. -/
theorem separationReadX_pos (x : ℝ) (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ)
    (hX : ContinuousOn (fun u => physicalTraceX x s u (r, w)) (Iic t))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s))
    (hsep : ∀ u ≤ t, ∀ v ≤ s, physicalTraceX x s u (r, w) * recordTrace v r + 1 ≠ 0) :
    0 < separationReadX x s t (r, w) := by
  rw [separationReadX_eq_compact x s t r w hX hA]
  apply squareMin_pos (continuous_prefixIntegrand hX hA)
  intro p
  exact (separationValue_pos_iff _ _).2 (hsep _ (fraction_mul_le t p.1) _ (fraction_mul_le s p.2))

/-- Every pair of prefix points bounds the compact separation minimum from
above, including irrational retained time fractions. -/
theorem separationReadX_le_value (x : ℝ) (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (hs : 0 < s)
    (hX : ContinuousOn (fun u => physicalTraceX x s u (r, w)) (Iic t))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) {v : ℝ≥0} (hv : v ≤ s) :
    separationReadX x s t (r, w) ≤ separationValue (physicalTraceX x s t (r, w)) (recordTrace v r) := by
  rw [separationReadX_eq_compact x s t r w hX hA]
  obtain ⟨p, hp, hmin⟩ := exists_squareMin (continuous_prefixIntegrand hX hA)
  rw [compactSeparation, hp]
  let q : UnitSquare := (⟨1, zero_le_one, le_rfl⟩, ⟨v / s, zero_le, (div_le_one hs).2 hv⟩)
  have hvs : s * (v / s) = v := by field_simp
  simpa only [prefixIntegrand, q, mul_one, hvs] using hmin q

theorem separationReadX_nonneg (x : ℝ) (s t : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) :
    0 ≤ separationReadX x s t (r, w) :=
  le_separationReadX x s t (r, w) le_rfl (fun _ => separationValue_nonneg _ _)

/-- A finite physical contact limit gives the required terminal zero limit. -/
theorem tendsto_separationReadX_contact (x : ℝ) (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (hs : 0 < s)
    {T : ℝ≥0} (hX : ContinuousOn (fun u => physicalTraceX x s u (r, w)) (Iio T))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) {z : ℂ} {v : ℝ≥0} (hv : v ≤ s)
    (hz : Tendsto (fun u => physicalTraceX x s u (r, w)) (𝓝[<] T) (𝓝 z))
    (hcontact : z * recordTrace v r + 1 = 0) :
    Tendsto (fun u => separationReadX x s u (r, w)) (𝓝[<] T) (𝓝 0) := by
  have hb := continuous_separationValue.tendsto (z, recordTrace v r) |>.comp (hz.prodMk_nhds tendsto_const_nhds)
  have hzero : separationValue z (recordTrace v r) = 0 := by
    simp only [separationValue, hcontact, norm_zero, zero_div, min_eq_right zero_le_one]
  rw [hzero] at hb
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
  have hupper : ∀ᶠ u : ℝ≥0 in 𝓝[<] T,
      separationReadX x s u (r, w) ≤ separationValue (physicalTraceX x s u (r, w)) (recordTrace v r) := by
    filter_upwards [hu] with u hu
    exact separationReadX_le_value x s u r w hs (hX.mono fun q hq => lt_of_le_of_lt hq hu) hA hv
  exact squeeze_zero' (Eventually.of_forall fun u => separationReadX_nonneg x s u r w) hupper hb

/-- Escape of the reconstructed physical trace also gives the terminal
zero limit, through the retained seed. -/
theorem tendsto_separationReadX_escape (x : ℝ) (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (hs : 0 < s)
    {T : ℝ≥0} (hX : ContinuousOn (fun u => physicalTraceX x s u (r, w)) (Iio T))
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) (hA0 : recordTrace 0 r = 0)
    (hz : Tendsto (fun u => ‖physicalTraceX x s u (r, w)‖) (𝓝[<] T) atTop) :
    Tendsto (fun u => separationReadX x s u (r, w)) (𝓝[<] T) (𝓝 0) := by
  have hb := GaugeE.tendsto_separationValue_escape hz
  have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
  have hupper : ∀ᶠ u : ℝ≥0 in 𝓝[<] T,
      separationReadX x s u (r, w) ≤ separationValue (physicalTraceX x s u (r, w)) 0 := by
    filter_upwards [hu] with u hu
    have h := separationReadX_le_value x s u r w hs (hX.mono fun q hq => lt_of_le_of_lt hq hu) hA (v := 0) zero_le
    rwa [hA0] at h
  exact squeeze_zero' (Eventually.of_forall fun u => separationReadX_nonneg x s u r w) hupper hb


end InteractingSLE.Theorem14.GW2Rz
