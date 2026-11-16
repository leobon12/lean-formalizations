/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermPath

/-!
# The terminal retained pair: the chart, its extended inverse, its lift and the chart field (deterministic)

Packet PROVE-RC-TERM (ruling R124). The chart data of `IsTerminalRetainedContinuation` for the completed second path,
read from the record `r` of its driver (`U = rdrv r`, `T = rtime r`) and the seed `x`:

* `termFwd x r z = f_T(z − x)`, the recentred centred Loewner map;
* `termInv x r`, its inverse on `ℍ`, extended to the real line by its boundary values (`extendFrom`), so that the
  first path can be read at its real points; off `ℍ̄` it is the real point `x`;
* `termLift x r z = Im log f_T′(z − x)`, the continuous branch of `arg φ′` (`logDerivFwd`).

Results, with `D = (· + x) '' (ℍ ∖ K_T)` (the active domain, `Term.activeDomain_eq_image`):

* `bijOn_termInv`, `termFwd_termInv`: the inverse is a bijection of `ℍ` onto `D` and a right inverse of the chart;
* **`termInv_notMem`**: off `ℍ` the extended inverse takes no value in `D` (a boundary value of the inverse Loewner
  map is not an interior point of the complement of the hull);
* `continuousOn_termLift`, **`deriv_termFwd`**: the lift is continuous on `D` and `φ′ = |φ′| e^{i lift}` there;
* **`isChartTransport_term`**: the chart field `Term.termField` of a good record is the frozen chart transport of the
  field by `(termFwd, termInv, termLift)` (the landed `Exist.StagedLaw.isChartTransport_recField` composed with the
  recentring `Exist.isTranslateAddConst_flowField`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RealContact

namespace Term

open Exist.Staged Exist.StagedLaw

/-- The chart of the completed path: the recentred centred Loewner map at the lifetime. -/
def termFwd (x : ℝ) (r : RecData) (z : ℂ) : ℂ := fwdMap (rdrv r) (rtime r) (z - x)

/-- The inverse chart, extended to the real line by its boundary values; off the closed half-plane it is the real
point `x`. -/
def termInv (x : ℝ) (r : RecData) (v : ℂ) : ℂ :=
  if 0 ≤ v.im then extendFrom H (fwdMapInv (rdrv r) (rtime r)) v + x else x

/-- The lift of the chart: the continuous branch `Im log f_T′` of the argument of its derivative. -/
def termLift (x : ℝ) (r : RecData) (z : ℂ) : ℝ := (logDerivFwd (rdrv r) (rtime r) (z - x)).im

variable {x : ℝ} {r : RecData}

theorem termInv_of_mem {v : ℂ} (hv : v ∈ H) : termInv x r v = fwdMapInv (rdrv r) (rtime r) v + x := by
  have h0 : 0 ≤ v.im := le_of_lt hv
  rw [termInv, ite_eq_left h0, extendFrom_fwdMapInv_of_mem (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hv]

theorem termFwd_termInv {v : ℂ} (hv : v ∈ H) : termFwd x r (termInv x r v) = v := by
  rw [termInv_of_mem hv, termFwd, add_sub_cancel_right]
  exact QuantumZipper.RS.fwdMap_fwdMapInv (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) hv

theorem sub_mem_of_mem_image {z : ℂ} {D₀ : Set ℂ} (hz : z ∈ (fun w : ℂ => w + x) '' D₀) : z - x ∈ D₀ := by
  obtain ⟨w, hw, rfl⟩ := hz
  simpa only [add_sub_cancel_right] using hw

/-- The extended inverse is a bijection of `ℍ` onto the translated complement of the hull. -/
theorem bijOn_termInv :
    BijOn (termInv x r) H ((fun z : ℂ => z + x) '' (H \ fwdHull (rdrv r) (rtime r))) := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hT := rtime_nonneg r
  refine ⟨fun v hv => ?_, fun v hv v' hv' hvv' => ?_, fun z hz => ?_⟩
  · rw [termInv_of_mem hv]
    exact ⟨_, QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hT hv, rfl⟩
  · rw [← termFwd_termInv (x := x) (r := r) hv, hvv', termFwd_termInv hv']
  · have hz' := sub_mem_of_mem_image hz
    refine ⟨fwdMap (rdrv r) (rtime r) (z - x), QuantumZipper.FwdHolo.mapsTo_fwdMap hU hT hz', ?_⟩
    rw [termInv_of_mem (QuantumZipper.FwdHolo.mapsTo_fwdMap hU hT hz'),
      QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hT hz', sub_add_cancel]

/-- **Off `ℍ`, the extended inverse takes no value in the domain**: a boundary value of the inverse Loewner map is
not a point of the complement of the hull. -/
theorem termInv_notMem (hB : HasBdryLimits (fwdMapInv (rdrv r) (rtime r))) {v : ℂ} (hv : v ∉ H) :
    termInv x r v ∉ (fun z : ℂ => z + x) '' (H \ fwdHull (rdrv r) (rtime r)) := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hT := rtime_nonneg r
  rintro ⟨z₀, hz₀, hze⟩
  by_cases hv0 : 0 ≤ v.im
  · rw [termInv, ite_eq_left hv0] at hze
    have hz : extendFrom H (fwdMapInv (rdrv r) (rtime r)) v = z₀ := (add_right_cancel hze).symm
    have hvb : v ∈ Hbar := hv0
    have hlim := hB.tendsto hvb
    rw [hz] at hlim
    have hlim' : Tendsto (fwdMapInv (rdrv r) (rtime r)) (𝓝[H] v) (𝓝[H \ fwdHull (rdrv r) (rtime r)] z₀) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, eventually_nhdsWithin_of_forall fun w hw =>
        QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hT hw⟩
    have hf : Tendsto (fwdMap (rdrv r) (rtime r)) (𝓝[H \ fwdHull (rdrv r) (rtime r)] z₀)
        (𝓝 (fwdMap (rdrv r) (rtime r) z₀)) :=
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hU hT).continuousOn z₀ hz₀
    have h1 : Tendsto (fun w => fwdMap (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) w)) (𝓝[H] v)
        (𝓝 (fwdMap (rdrv r) (rtime r) z₀)) := hf.comp hlim'
    have h2 : Tendsto (fun w => fwdMap (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) w)) (𝓝[H] v) (𝓝 v) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun w hw =>
        (QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hT hw).symm)
    have : (𝓝[H] v).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hvb)
    have h3 := tendsto_nhds_unique h1 h2
    exact hv (h3 ▸ QuantumZipper.FwdHolo.mapsTo_fwdMap hU hT hz₀)
  · rw [termInv, ite_eq_right hv0] at hze
    have hz0 : z₀ = 0 := by
      have := add_right_cancel (b := (x : ℂ)) (a := z₀) (c := 0) (by rw [zero_add]; exact hze)
      exact this
    have h0 : 0 < z₀.im := hz₀.1
    rw [hz0, Complex.zero_im] at h0
    exact lt_irrefl 0 h0

/-- The chart is continuous on its domain. -/
theorem continuousOn_termFwd :
    ContinuousOn (termFwd x r) ((fun z : ℂ => z + x) '' (H \ fwdHull (rdrv r) (rtime r))) :=
  (QuantumZipper.FwdHolo.differentiableOn_fwdMap (continuous_rdrv r) (rtime_nonneg r)).continuousOn.comp
    (continuous_id.sub continuous_const).continuousOn fun _ hz => sub_mem_of_mem_image hz

/-- The lift is continuous on the domain. -/
theorem continuousOn_termLift :
    ContinuousOn (termLift x r) ((fun z : ℂ => z + x) '' (H \ fwdHull (rdrv r) (rtime r))) := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hg : ContinuousOn (fun w => (logDerivFwd (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) w)).im + 0) H :=
    Chart.isConformal_id.continuousOn_loewner_lift Chart.continuousOn_id_lift hU hU0 hT
  have hc := hg.comp (continuousOn_termFwd (x := x) (r := r)) fun z hz =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hU hT (sub_mem_of_mem_image hz)
  refine hc.congr fun z hz => ?_
  change (logDerivFwd (rdrv r) (rtime r) (z - x)).im =
    (logDerivFwd (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) (fwdMap (rdrv r) (rtime r) (z - x)))).im + 0
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hT (sub_mem_of_mem_image hz), add_zero]

theorem deriv_termFwd_eq {z : ℂ} (hz : z ∈ (fun w : ℂ => w + x) '' (H \ fwdHull (rdrv r) (rtime r))) :
    deriv (termFwd x r) z = Complex.exp (logDerivFwd (rdrv r) (rtime r) (z - x)) := by
  have h1 : deriv (termFwd x r) z = deriv (fwdMap (rdrv r) (rtime r)) (z - x) :=
    deriv_comp_sub_const (fwdMap (rdrv r) (rtime r)) (x : ℂ) z
  rw [h1]
  exact (QuantumZipper.FwdHolo.hasDerivAt_fwdMap (continuous_rdrv r) (rtime_nonneg r)
    (sub_mem_of_mem_image hz)).deriv

/-- **The lift is a branch of the argument of the derivative**: `φ′ = |φ′| e^{i lift}` on the domain. -/
theorem deriv_termFwd {z : ℂ} (hz : z ∈ (fun w : ℂ => w + x) '' (H \ fwdHull (rdrv r) (rtime r))) :
    deriv (termFwd x r) z =
      (‖deriv (termFwd x r) z‖ : ℂ) * Complex.exp (Complex.I * (termLift x r z : ℂ)) := by
  rw [deriv_termFwd_eq hz, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  change logDerivFwd (rdrv r) (rtime r) (z - x) =
    ((logDerivFwd (rdrv r) (rtime r) (z - x)).re : ℂ) +
      Complex.I * ((logDerivFwd (rdrv r) (rtime r) (z - x)).im : ℂ)
  conv_lhs => rw [← Complex.re_add_im (logDerivFwd (rdrv r) (rtime r) (z - x))]
  ring

/-! ### The chart field -/

/-- **The chart field of a good record is the chart transport of the field** by the chart
`(termFwd, termInv, termLift)`. -/
theorem isChartTransport_term {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (termRec e))) (κ x : ℝ) (h : DistOn upperHalfPlaneOpens) :
    IsChartTransport (termFwd x (termRec e), termInv x (termRec e), termLift x (termRec e)) 1 0
      (QuantumZipper.chiC κ) h (termField κ x (termRec e) h) := by
  intro φ φ' hsupp hφ
  set r := termRec e with hr
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hT := rtime_nonneg r
  -- the record chart is the Loewner chart of the record driver
  have hrc : recChart r = Chart.id.loewner (rdrv r) (rtime r) := by
    have h1 : recChart r = Chart.id.loewner (fun s : ℝ => (retOf ⊤ e).1 s.toNNReal)
        (((min ⊤ e.2).toNNReal : ℝ≥0) : ℝ) := recChart_eq_loewner he hg
    rw [h1, rdrv_termRec he hg]
    rfl
  -- the translated test
  set a : TestOn upperHalfPlaneOpens := Chart.pushTest (Exist.isConformal_shiftChart (-x)) φ with ha
  have hax : ∀ z, a z = φ (z + x) := fun z => by
    rw [ha, Exist.pushTest_shiftChart_apply, Complex.ofReal_neg, sub_neg_eq_add]
  have h1 := Exist.isTranslateAddConst_flowField x 0 h φ a hax
  have himg : ∀ z : ℂ, z ∈ (Chart.id.loewner (rdrv r) (rtime r)).2.1 '' H →
      z + x ∈ (termFwd x r, termInv x r, termLift x r).2.1 '' H := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, termInv_of_mem hv⟩
  have h2 := isChartTransport_recField κ r (Exist.flowField x 0 h)
  rw [hrc] at h2
  have h3 := h2 a φ' (fun z hz => ?_) (fun z hz => ?_)
  · rw [termField, h3, h1]
    have hint : (∫ w : ℂ, (Chart.id.loewner (rdrv r) (rtime r)).2.2
          ((Chart.id.loewner (rdrv r) (rtime r)).2.1 w) * φ' w) =
        ∫ w : ℂ, termLift x r (termInv x r w) * φ' w := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      by_cases hw : w ∈ H
      · have e1 : (Chart.id.loewner (rdrv r) (rtime r)).2.2 ((Chart.id.loewner (rdrv r) (rtime r)).2.1 w) =
            termLift x r (termInv x r w) := by
          rw [termInv_of_mem hw]
          change (logDerivFwd (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) w)).im + 0 =
            (logDerivFwd (rdrv r) (rtime r) (fwdMapInv (rdrv r) (rtime r) w + x - x)).im
          rw [add_zero, add_sub_cancel_right]
        change (Chart.id.loewner (rdrv r) (rtime r)).2.2 ((Chart.id.loewner (rdrv r) (rtime r)).2.1 w) * φ' w =
          termLift x r (termInv x r w) * φ' w
        rw [e1]
      · have h0 : φ' w = 0 := φ'.zero_on_compl hw
        change (Chart.id.loewner (rdrv r) (rtime r)).2.2 ((Chart.id.loewner (rdrv r) (rtime r)).2.1 w) * φ' w =
          termLift x r (termInv x r w) * φ' w
        rw [h0, mul_zero, mul_zero]
    change (1 * (h φ + 0 * ∫ z : ℂ, a z) + 0 * ∫ w : ℂ, φ' w) + QuantumZipper.chiC κ *
        (∫ w : ℂ, (Chart.id.loewner (rdrv r) (rtime r)).2.2 ((Chart.id.loewner (rdrv r) (rtime r)).2.1 w) * φ' w) =
      (1 * h φ + 0 * ∫ w : ℂ, φ' w) + QuantumZipper.chiC κ * ∫ w : ℂ, termLift x r (termInv x r w) * φ' w
    rw [hint]
    ring
  · have hfun : (⇑a : ℂ → ℝ) = (⇑φ) ∘ (Homeomorph.addRight (x : ℂ)) := funext fun w => hax w
    rw [hfun, tsupport_comp_eq_preimage] at hz
    obtain ⟨v, hv, hve⟩ := hsupp hz
    refine ⟨v, hv, ?_⟩
    have hve' : termInv x r v = z + x := hve
    rw [termInv_of_mem hv] at hve'
    exact add_right_cancel hve'
  · rw [hax z, hφ (z + x) (himg z hz)]
    have e1 : (termFwd x r, termInv x r, termLift x r).1 (z + x) =
        (Chart.id.loewner (rdrv r) (rtime r)).1 z := by
      change fwdMap (rdrv r) (rtime r) (z + x - x) = fwdMap (rdrv r) (rtime r) z
      rw [add_sub_cancel_right]
    have e2 : deriv (termFwd x r, termInv x r, termLift x r).1 (z + x) =
        deriv (Chart.id.loewner (rdrv r) (rtime r)).1 z := by
      have h4 : deriv (termFwd x r) (z + x) = deriv (fwdMap (rdrv r) (rtime r)) (z + x - x) :=
        deriv_comp_sub_const (fwdMap (rdrv r) (rtime r)) (x : ℂ) (z + x)
      rw [add_sub_cancel_right] at h4
      exact h4
    rw [e1, e2]

end Term

end InteractingSLE.RealContact
