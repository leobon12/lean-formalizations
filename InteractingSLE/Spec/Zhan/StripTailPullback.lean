/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailRestart
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Sec7.CounterflowProbDilation
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Foundations.Loewner.RealPoints
import QuantumZipper.Proofs.RS.RealAlive
import QuantumZipper.Proofs.RS.GenerationBasic
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBoundary

/-!
# Pulling the endpoint of a restarted strip path back through the finite prefix

Packet PROVE-ZHAN-A4. Astra, *Formalization proofs* L1567–L1569: "The inverse map of the finite prefix is analytic
along the top, and takes finite top points to finite top points. Pullback proves precisely (ii)."

In the chordal chart the top line `ℝ + iπ` of the strip is the half-line `(−∞, −1)`, and at chordal time `a` its
image under the centred forward map is `(−∞, v_a − w_a)`. The extended inverse map `F̄_a` of the finite prefix sends
every real point `y < v_a − w_a` to the real point `x < −1` whose forward flow ends at `y`
(`exists_isForwardSol_eq_of_lt`, `extendFrom_eq_of_isForwardSol`). With the join of traces
(`Sec7.IsGeneratingTraceIcc.join`), dilation (`IsGeneratingTrace.dilate`) and uniqueness of generating traces
(`IsGeneratingTrace.eq_of_le`), the original trace at `a + c r` is `F̄_a(g η̂(r))`, so convergence of the restarted
trace `η̂` to `x̂ < −1` gives convergence of the original one to `F̄_a(g x̂) < −1`.

## Main results

* `fwdMap_ofReal_eq`: the forward map at a real point with a forward solution is the solution's value;
* `exists_isForwardSol_eq_of_lt`: every real `y` left of the end-mark image is the image of a real `x < −1`;
* `extendFrom_eq_of_isForwardSol`: `F̄_a(u_a) = x` for a forward solution `u` from a real point `x`;
* **`IsStripPath.stripConv_of_rs`**: if the restart at a strip time `n` has the strip endpoint property, the
  original strip path satisfies clause (3).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace Zhan

/-! ### Real points left of the end mark -/

section RealPoints

variable {W : ℝ → ℝ} {a : ℝ}

/-- The forward map at a real point with a forward solution is the solution's value. -/
theorem fwdMap_ofReal_eq (hW : Continuous W) (ha : 0 ≤ a) {x : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W x a u) : fwdMap W a x = u a := by
  have hex : ∃ u, IsForwardSol W x a u := ⟨u, hu⟩
  rw [QuantumZipper.fwdMap, dite_eq_left_of_eq_true (eq_true hex)]
  exact eqOn_of_isForwardSol hW hex.choose_spec hu ⟨ha, le_rfl⟩

/-- A real point `x < −1` has a forward solution on `[0, a]` whenever `−1` has one (`W 0 = 0`): reflect, and use
that real points beyond an alive real point are alive (`RS.exists_isForwardSol_of_lt`). -/
theorem exists_isForwardSol_of_lt_neg_one (hW : Continuous W) (hW0 : W 0 = 0) (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IsForwardSol W ((-1 : ℝ) : ℂ) a u) {x : ℝ} (hx : x < -1) :
    ∃ u', IsForwardSol W (x : ℂ) a u' := by
  have h1 : IsForwardSol (fun t => -W t) ((1 : ℝ) : ℂ) a (fun t => -u t) := by
    have := QuantumZipper.RS.isForwardSol_neg hu
    simpa using this
  obtain ⟨v, hv⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hW.neg ha (q := 1) (y := -x)
    (by simp [hW0]) (by linarith) h1
  refine ⟨fun t => -v t, ?_⟩
  have := QuantumZipper.RS.isForwardSol_neg hv
  simpa using this

theorem exists_isForwardSol_of_le_neg_one (hW : Continuous W) (hW0 : W 0 = 0) (ha : 0 ≤ a)
    {u : ℝ → ℂ} (hu : IsForwardSol W ((-1 : ℝ) : ℂ) a u) {x : ℝ} (hx : x ≤ -1) :
    ∃ u', IsForwardSol W (x : ℂ) a u' := by
  rcases hx.lt_or_eq with h | h
  · exact exists_isForwardSol_of_lt_neg_one hW hW0 ha hu h
  · exact ⟨u, by rw [h]; exact hu⟩

/-- Real points move away from the driver: `u_a ≤ x − W_a` for a forward solution from `x < 0`. -/
theorem re_le_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) (ha : 0 ≤ a) {x : ℝ} (hx : x < 0)
    {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) a u) : (u a).re ≤ x - W a := by
  have hneg := InteractingSLE.re_neg_of_isForwardSol hW hW0 hx hu
  have heq := (hu.2 a ⟨ha, le_rfl⟩).2
  have hint : IntervalIntegrable (fun s => 2 / u s) MeasureTheory.volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha]
    exact continuousOn_const.div hu.1 fun s hs => (hu.2 s hs).1
  have hre : (∫ s in (0 : ℝ)..a, 2 / u s).re = ∫ s in (0 : ℝ)..a, (2 / u s).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  have hnp : ∫ s in (0 : ℝ)..a, (2 / u s).re ≤ 0 := by
    have : 0 ≤ ∫ s in (0 : ℝ)..a, -(2 / u s).re := by
      refine intervalIntegral.integral_nonneg ha fun s hs => ?_
      rw [Complex.div_re]
      have h1 := hneg s hs
      have h2 : 0 ≤ Complex.normSq (u s) := Complex.normSq_nonneg _
      have h3 : (2 : ℂ).re * (u s).re / Complex.normSq (u s) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by norm_num; linarith) h2
      have h4 : (2 : ℂ).im * (u s).im / Complex.normSq (u s) = 0 := by norm_num
      linarith
    rw [intervalIntegral.integral_neg] at this
    linarith
  have := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at this
  linarith

/-- The real part of the forward map is continuous on `(−∞, −1]`. -/
theorem continuousOn_re_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IsForwardSol W ((-1 : ℝ) : ℂ) a u) :
    ContinuousOn (fun x : ℝ => (fwdMap W a x).re) (Iic (-1)) := by
  intro x₀ hx₀
  obtain ⟨u₀, hu₀⟩ := exists_isForwardSol_of_le_neg_one hW hW0 ha hu hx₀
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ha hu₀
  set E := Real.exp (2 / δ ^ 2 * a) with hE
  have hE0 : 0 < E := Real.exp_pos _
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (δ / (2 * E)) (ε / (2 * E)), by positivity, fun x hx hxd => ?_⟩
  obtain ⟨ux, hux⟩ := exists_isForwardSol_of_le_neg_one hW hW0 ha hu hx
  have hn : ‖(x : ℂ) - x₀‖ = dist x x₀ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.dist_eq, Real.norm_eq_abs]
  have hzp : ‖(x : ℂ) - x₀‖ * E < δ := by
    rw [hn]
    have h1 : dist x x₀ < δ / (2 * E) := hxd.trans_le (min_le_left _ _)
    have h2 : dist x x₀ * E < δ / (2 * E) * E := mul_lt_mul_of_pos_right h1 hE0
    have h3 : δ / (2 * E) * E = δ / 2 := by field_simp
    linarith
  have hb := norm_sub_le_of_isForwardSol hW hu₀ hux hδ ha le_rfl hlow hzp a ⟨ha, le_rfl⟩
  rw [fwdMap_ofReal_eq hW ha hux, fwdMap_ofReal_eq hW ha hu₀, Real.dist_eq, ← Complex.sub_re]
  calc |(ux a - u₀ a).re| ≤ ‖ux a - u₀ a‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(x : ℂ) - x₀‖ * Real.exp (2 / δ ^ 2 * a) := hb
    _ = dist x x₀ * E := by rw [hn]
    _ < ε / (2 * E) * E := mul_lt_mul_of_pos_right (hxd.trans_le (min_le_right _ _)) hE0
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- **Every real point left of the end-mark image is the image of a real point `x < −1`.** -/
theorem exists_isForwardSol_eq_of_lt (hW : Continuous W) (hW0 : W 0 = 0) (ha : 0 ≤ a) {u : ℝ → ℂ}
    (hu : IsForwardSol W ((-1 : ℝ) : ℂ) a u) {y : ℝ} (hy : y < (u a).re) :
    ∃ x : ℝ, x < -1 ∧ ∃ u', IsForwardSol W (x : ℂ) a u' ∧ u' a = y := by
  set X := min (-2) (y + W a - 1) with hXdef
  have hX : X < -1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  obtain ⟨uX, huX⟩ := exists_isForwardSol_of_lt_neg_one hW hW0 ha hu hX
  have hφX : (fwdMap W a (X : ℂ)).re < y := by
    have := re_le_of_isForwardSol hW hW0 ha (by linarith) huX
    rw [fwdMap_ofReal_eq hW ha huX]
    linarith [min_le_right (-2) (y + W a - 1)]
  have hφ1 : (fwdMap W a ((-1 : ℝ) : ℂ)).re = (u a).re := by rw [fwdMap_ofReal_eq hW ha hu]
  have hcont := (continuousOn_re_fwdMap hW hW0 ha hu).mono (Icc_subset_Iic_self (a := X))
  obtain ⟨x, hx, hφx⟩ := intermediate_value_Icc hX.le hcont
    ⟨hφX.le, by show y ≤ (fwdMap W a ((-1 : ℝ) : ℂ)).re; rw [hφ1]; exact hy.le⟩
  have hφx' : (fwdMap W a (x : ℂ)).re = y := hφx
  have hx1 : x < -1 := lt_of_le_of_ne hx.2 (by
    rintro rfl
    rw [hφ1] at hφx'
    linarith)
  obtain ⟨u', hu'⟩ := exists_isForwardSol_of_lt_neg_one hW hW0 ha hu hx1
  refine ⟨x, hx1, u', hu', ?_⟩
  have him := im_eq_zero_of_isForwardSol_real hW hu' ⟨ha, le_rfl⟩
  have hre : (u' a).re = y := by rw [← hφx', fwdMap_ofReal_eq hW ha hu']
  exact Complex.ext (by simp [hre]) (by simp [him])

/-- **The extended inverse map at the image of a real point**: if `F` extends `F_a = fwdMapInv W a` continuously
to `ℍ̄`, and `u` is a forward solution from the real point `x` on `[0, a]`, then `F(u_a) = x`. -/
theorem extendFrom_eq_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) (ha : 0 ≤ a)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W a) H) (hFc : ContinuousOn F Hbar)
    {x : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) a u) : F (u a) = x := by
  have him := im_eq_zero_of_isForwardSol_real hW hu ⟨ha, le_rfl⟩
  have huH : u a ∈ Hbar := mem_Hbar_of_im_eq_zero him
  have hlim := tendsto_fwdMap_of_isForwardSol hW ha hu
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ha hu
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fwdHull W a := by
    have hc : Continuous fun z : ℂ => ‖z - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * a) := by fun_prop
    have h0 : (fun z : ℂ => ‖z - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * a)) x < δ := by simp [hδ]
    have h1 : ∀ᶠ z in 𝓝 (x : ℂ), ‖z - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * a) < δ :=
      hc.continuousAt.eventually_lt continuousAt_const h0
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzH
    exact ⟨hzH, not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzH hz⟩
  have hid : (fun z => F (fwdMap W a z)) =ᶠ[𝓝[H] (x : ℂ)] id := by
    filter_upwards [hev] with z hz
    rw [hFeq (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ha hz), QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ha hz]
    rfl
  have hlimH : Tendsto (fwdMap W a) (𝓝[H] (x : ℂ)) (𝓝[Hbar] (u a)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, by
      filter_upwards [hev] with z hz
      exact QuantumZipper.H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ha hz)⟩
  have hlim2 : Tendsto (fun z => F (fwdMap W a z)) (𝓝[H] (x : ℂ)) (𝓝 (F (u a))) :=
    (hFc (u a) huH).tendsto.comp hlimH
  have hlim3 : Tendsto (fun z => F (fwdMap W a z)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' hid.symm
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [closure_H]; exact mem_Hbar_of_im_eq_zero (by simp))
  exact tendsto_nhds_unique hlim2 hlim3

end RealPoints

/-! ### The pullback -/

section Pullback

open Strip

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- On a strip-life interval `[0, s]` the driver is continuous on `{t ≤ s}`. -/
theorem IsStripPath.continuousOn_le (h : IsStripPath w v ζ) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    ContinuousOn w (Iic s) := by
  have hm := h.2.1 s hs
  refine (hm.continuousOn_w.comp NNReal.continuous_coe.continuousOn fun t ht =>
    ⟨NNReal.coe_nonneg t, NNReal.coe_le_coe.2 ht⟩).congr fun t _ => ?_
  simp [extPath]

/-- On a strip-life interval `[0, s]` the driver is continuous before `s`. -/
theorem IsStripPath.continuousOn_lt (h : IsStripPath w v ζ) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < s} :=
  (h.continuousOn_le hs).mono fun _ ht => (ENNReal.coe_lt_coe.1 ht).le

/-- The end mark `v − w` is a forward solution from `−1` of the frozen driver. -/
theorem IsStripPath.isForwardSol_end (h : IsStripPath w v ζ) {s' : ℝ≥0} (hs' : IsStripLife w v ζ s')
    {a : ℝ≥0} (has : a ≤ s') :
    IsForwardSol (frozenDrive w s') ((-1 : ℝ) : ℂ) a (fun r => ((extPath v r - extPath w r : ℝ) : ℂ)) := by
  have hm := h.2.1 s' hs'
  have hsub : Icc (0 : ℝ) a ⊆ Icc 0 s' := Icc_subset_Icc_right (NNReal.coe_le_coe.2 has)
  refine ⟨Complex.continuous_ofReal.comp_continuousOn
    ((hm.continuousOn_v.sub hm.continuousOn_w).mono hsub), fun r hr => ⟨?_, ?_⟩⟩
  · exact Complex.ofReal_ne_zero.2 (sub_neg.2 (hm.lt r (hsub hr))).ne
  · have hfz : frozenDrive w s' r = extPath w r := by
      rw [frozenDrive_eq ⟨hr.1, (hsub hr).2⟩]; rfl
    have hint : ∫ u in (0 : ℝ)..r, (2 : ℂ) / ((extPath v u - extPath w u : ℝ) : ℂ) =
        ((∫ u in (0 : ℝ)..r, 2 / (extPath v u - extPath w u) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun u _ => ?_
      push_cast; rfl
    beta_reduce
    rw [hfz, hint, hm.eq r (hsub hr)]
    push_cast; ring

/-- **Pullback** (Astra L1567–L1569). If the restart of a strip path at the strip time `n` has the strip endpoint
property, then every generating trace of the original strip path converges along the strip life to a point
`x < −1`: at chordal time `a + c r` the trace is `F̄_a(g ηh(r))`, and `F̄_a` sends the limit `g xh < −g = v_a − w_a`
of `g ηh` to the real point `x < −1` whose forward flow ends there. -/
theorem IsStripPath.stripConv_of_rs (h : IsStripPath w v ζ) (n : ℝ≥0)
    (hR : HasStripEndpoint (rsW w v n) (rsV w v n) (rsZ w v ζ n)) : StripConv w v ζ := by
  intro η hη
  obtain ⟨ha, -, -⟩ := h.chordT_spec n
  have hg : 0 < rsGap w v n := h.rsGap_pos n
  have hc : 0 < rsScale w v n := h.rsScale_pos n
  set a := chordT w v n with ha_def
  set c := rsScale w v n with hc_def
  set g := rsGap w v n with hg_def
  have hw0 : w 0 = 0 := h.1
  obtain ⟨-, ⟨ηh, hηh⟩, hconv⟩ := hR
  obtain ⟨xh, hxh, hxhconv⟩ := hconv ηh hηh
  -- the prefix up to `a` and the extension of its inverse map
  obtain ⟨s', has', hs'⟩ := h.exists_gt ha
  have h₁ : Sec7.IsGeneratingTraceIcc w a η :=
    Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hη s' hs') (h.continuousOn_lt hs') hw0
      (ENNReal.coe_lt_coe.2 has')
  have hfc : Continuous (frozenDrive w s') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.continuousOn_le hs')
  obtain ⟨hF, -, hFeq, hFc, -, -, hF0⟩ :=
    h₁.extend_props (t₂ := (s' : ℝ)) (NNReal.coe_lt_coe.2 has') hfc hw0
  set F := extendFrom H (fwdMapInv (frozenDrive w s') a) with hFdef
  have hW0' : frozenDrive w s' 0 = 0 := by rw [frozenDrive_zero (NNReal.coe_nonneg s'), hw0]
  -- the limit point `x' = F̄_a(g xh)`
  have hend := h.isForwardSol_end hs' has'.le
  have hyl : g * xh < (((extPath v a - extPath w a : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re, extPath_coe, extPath_coe]
    have : v a - w a = -g := by rw [hg_def, rsGap]; ring
    rw [this]
    nlinarith
  obtain ⟨x', hx', u', hu', hu'a⟩ :=
    exists_isForwardSol_eq_of_lt hfc hW0' (NNReal.coe_nonneg a) hend hyl
  have hFx' : F ((g * xh : ℝ) : ℂ) = x' := by
    rw [← hu'a]
    exact extendFrom_eq_of_isForwardSol hfc hW0' (NNReal.coe_nonneg a) hFeq hFc hu'
  refine ⟨x', hx', fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hFδ⟩ :=
    Metric.continuousWithinAt_iff.1 (hFc ((g * xh : ℝ) : ℂ) (mem_Hbar_of_im_eq_zero (Complex.ofReal_im _))) ε hε
  obtain ⟨r₀, hr₀, hr₀c⟩ := hxhconv (δ / g) (div_pos hδ hg)
  refine ⟨a + c * r₀, (h.isStripLife_rs_iff n r₀).1 hr₀, fun s hs hsl => ?_⟩
  have has : a ≤ s := le_trans le_self_add hs
  set r := (s - a) / c with hr_def
  have hsr : a + c * r = s := by rw [hr_def, mul_div_cancel₀ _ hc.ne', add_tsub_cancel_of_le has]
  have hrl : IsStripLife (rsW w v n) (rsV w v n) (rsZ w v ζ n) r :=
    (h.isStripLife_rs_iff n r).2 (by rw [hsr]; exact hsl)
  have hrr : r₀ ≤ r := by
    have h1 : c * r₀ ≤ c * r := by
      have h2 := hs
      rw [← hsr] at h2
      exact le_of_add_le_add_left h2
    exact le_of_mul_le_mul_left h1 hc
  have hclose := hr₀c r hrr hrl
  -- the original trace at `s = a + c r` is `F̄_a(g ηh r)`
  have hjoin : η s = F ((g : ℂ) * ηh r) := by
    rcases eq_or_ne r 0 with hr0 | hr0
    · have hsa : s = a := by rw [← hsr, hr0, mul_zero, add_zero]
      have hηh0 : ηh r = 0 := by rw [hr0]; exact (hηh r hrl).1.symm ▸ (hηh 0 (by rw [← hr0]; exact hrl)).1
      rw [hηh0, mul_zero, hF0, hsa]
    · have hci : (c⁻¹ : ℝ≥0) ≠ 0 := inv_ne_zero hc.ne'
      have hd := IsGeneratingTrace.dilate hci (hηh r hrl)
      have hsq : (√((c⁻¹ : ℝ≥0) : ℝ))⁻¹ = g := by
        rw [NNReal.coe_inv, hc_def, coe_rsScale, ← hg_def, Real.sqrt_inv, Real.sqrt_sq hg.le, inv_inv]
      have hshift : Sec7.Dilation.dilPath c⁻¹ (rsW w v n) = Sec7.shiftNN w a := by
        funext t
        simp only [Sec7.Dilation.dilPath, rsW, Sec7.shiftNN, ← ha_def, ← hc_def, ← hg_def, hsq,
          mul_inv_cancel_left₀ hc.ne']
        field_simp
      have hT : (r : ℝ≥0∞) / ((c⁻¹ : ℝ≥0) : ℝ≥0∞) = ((c * r : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_inv hc.ne', div_eq_mul_inv, inv_inv, ENNReal.coe_mul, mul_comm]
      rw [hshift, hT] at hd
      have has_lt : a < s := by
        rw [← hsr]
        exact lt_add_of_pos_right _ (mul_pos hc (pos_iff_ne_zero.2 hr0))
      have hsE : ((a : ℝ≥0∞) + ((c * r : ℝ≥0) : ℝ≥0∞)) = (s : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, hsr]
      have hjn := (Sec7.IsGeneratingTraceIcc.join (by rw [hsE]; exact h.continuousOn_lt hsl) hw0 h₁ hd).1
      rw [hsE] at hjn
      have heq := IsGeneratingTrace.eq_of_le (hη s hsl) hjn (h.continuousOn_lt hsl) hw0 le_rfl
      rw [heq, Sec7.joinTrace_of_lt has_lt, hF]
      congr 1
      have hsub : s - a = c * r := by rw [← hsr, add_tsub_cancel_left]
      rw [hsub, inv_mul_cancel_left₀ hc.ne', hsq]
  -- the estimate
  have hmem : (g : ℂ) * ηh r ∈ Hbar := by
    have h1 : ηh r ∈ Hbar :=
      Sec7.IsGeneratingTrace.mem_Hbar (hηh r hrl) ((h.rs n).continuousOn_lt hrl) (rsW_zero w v n) le_rfl
    show 0 ≤ ((g : ℂ) * ηh r).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hg.le h1
  have hdist : dist ((g : ℂ) * ηh r) ((g * xh : ℝ) : ℂ) < δ := by
    rw [dist_eq_norm, Complex.ofReal_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hg]
    calc g * ‖ηh r - xh‖ < g * (δ / g) := mul_lt_mul_of_pos_left hclose hg
      _ = δ := by field_simp
  have hfin := hFδ hmem hdist
  rw [hFx', dist_eq_norm] at hfin
  rw [hjoin]
  exact hfin

end Pullback

end Zhan

end InteractingSLE
