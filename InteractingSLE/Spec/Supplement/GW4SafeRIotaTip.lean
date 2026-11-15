/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaGrowth
import InteractingSLE.Spec.Supplement.GW4SafeRIotaAmbient

/-! # GW4: the actual centered transition is anchored at the driver

Strict relative growth supplies points in arbitrarily short common hull
increments. Their centered images approach zero in both charts. Thus every
boundary limit of the current transition at zero equals zero, including at
physical self-contacts. No cut-time assumption is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Rel

/-- The actual current component driver maps to the current ambient
driver. Uniqueness follows from shrinking hull increments, rather than
uniqueness of the physical point's prime end. -/
theorem Frame.current_transition_tip_eq_zero {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t)
    {x : ℂ} (hx : Tendsto (fun y => fwdMap (fun s : ℝ => w s.toNNReal) t
      ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 y))
      (𝓝[H] 0) (𝓝 x)) : x = 0 := by
  classical
  obtain ⟨T, htT, hLoc⟩ := Frame.exists_isLoc_gt hF hw htExit
  have hc := Frame.continuousOn_rcap hF hw t htExit
  have hcurV : ENNReal.ofReal (F.rcap w t) < V := by
    rw [← hqt, ENNReal.ofReal_coe_nnreal]
    exact hqV
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhdsWithin_iff.1
    (hc.eventually (Iio_mem_nhds hcurV))
  let d : ℝ := min ((T : ℝ) - t) ε / 2
  have hd : 0 < d := half_pos (lt_min (sub_pos.2 (NNReal.coe_lt_coe.2 htT)) hε)
  let u : ℕ → ℝ≥0 := fun n => ((t : ℝ) + d / ((n : ℝ) + 1)).toNNReal
  have hdn : ∀ n : ℕ, 0 < d / ((n : ℝ) + 1) := fun n => div_pos hd (by positivity)
  have hdnle : ∀ n : ℕ, d / ((n : ℝ) + 1) ≤ d := fun n =>
    (div_le_iff₀ (by positivity)).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hucoe : ∀ n, (u n : ℝ) = (t : ℝ) + d / ((n : ℝ) + 1) := fun n =>
    Real.coe_toNNReal _ (add_nonneg t.coe_nonneg (hdn n).le)
  have htu : ∀ n, t < u n := fun n => NNReal.coe_lt_coe.1 (by rw [hucoe]; linarith [hdn n])
  have huT : ∀ n, u n < T := by
    intro n
    apply NNReal.coe_lt_coe.1
    rw [hucoe]
    have hdt : d < (T : ℝ) - t := by
      dsimp only [d]
      linarith [min_le_left ((T : ℝ) - t) ε, NNReal.coe_lt_coe.2 htT]
    linarith [hdnle n]
  have huExit : ∀ n, (u n : ℝ≥0∞) < F.exit w := fun n =>
    (ENNReal.coe_lt_coe.2 (huT n)).trans hLoc.2.2
  have huV : ∀ n, ENNReal.ofReal (F.rcap w (u n)) < V := by
    intro n
    apply hBall ⟨?_, huExit n⟩
    rw [mem_ball, NNReal.dist_eq, hucoe, add_sub_cancel_left, abs_of_pos (hdn n)]
    have hdε : d < ε := by
      dsimp only [d]
      linarith [min_le_right ((T : ℝ) - t) ε]
    exact (hdnle n).trans_lt hdε
  have hut : Tendsto u atTop (𝓝 t) := by
    have hr := (tendsto_const_nhds (x := (t : ℝ))).add
      ((tendsto_const_nhds (x := d)).mul tendsto_one_div_add_atTop_nhds_zero_nat)
    have h := (continuous_real_toNNReal.tendsto (t : ℝ)).comp (by simpa only [mul_zero, add_zero] using hr)
    simpa only [Function.comp_def, u, Real.toNNReal_coe, div_eq_mul_inv, one_div, one_mul] using h
  have hut' : Tendsto u atTop (𝓝[{s : ℝ≥0 | (s : ℝ≥0∞) < F.exit w}] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hut, Eventually.of_forall huExit⟩
  let p : ℕ → ℝ≥0 := fun n => (F.rcap w (u n)).toNNReal
  have hpcoe : ∀ n, (p n : ℝ) = F.rcap w (u n) := fun n =>
    Real.coe_toNNReal _ (Frame.rcap_nonneg hF hw (huExit n))
  have hqp : ∀ n, q < p n := by
    intro n
    apply NNReal.coe_lt_coe.1
    rw [hpcoe, hqt]
    exact Frame.rcap_strictMono hF hLoc htEnt (htu n) (huT n)
  have hpV : ∀ n, (p n : ℝ≥0∞) < V := fun n => by
    simpa only [p, ENNReal.ofReal] using huV n
  have hpq : Tendsto p atTop (𝓝 q) := by
    have hr := (ENNReal.tendsto_toNNReal (a := ENNReal.ofReal (F.rcap w t)) ENNReal.ofReal_ne_top).comp
      (hc.tendsto.comp hut')
    rw [← hqt, ENNReal.ofReal_coe_nnreal, ENNReal.toNNReal_coe] at hr
    simpa only [Function.comp_def, p, ENNReal.ofReal, ENNReal.toNNReal_coe] using hr
  have hRR : Continuous (fun s : ℝ => R s.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun s : ℝ => R s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hWW : Continuous (fun s : ℝ => w s.toNNReal) := hw.1.comp continuous_real_toNNReal
  have hWW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw.2.1
  obtain ⟨t₀, ht₀⟩ := hVer q hqV
  have hKq := Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 ht₀ htEnt htExit hqt
  have hKp : ∀ n, fwdHull (fun s : ℝ => R s.toNNReal) (p n) = F.hullAt w (u n) := by
    intro n
    obtain ⟨v, hv⟩ := hVer (p n) (hpV n)
    exact Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 hv
      (htEnt.trans (htu n).le) (huExit n) (hpcoe n)
  have hex : ∀ n, ∃ a : ℂ, a ∈ fwdHull (fun s : ℝ => R s.toNNReal) (p n) \
      fwdHull (fun s : ℝ => R s.toNNReal) q := fun n => by
    obtain ⟨a, ha, hna⟩ := exists_of_ssubset (QuantumZipper.RS.fwdHull_ssubset hRR hRR0 q.coe_nonneg
      (NNReal.coe_lt_coe.2 (hqp n)))
    exact ⟨a, ha, hna⟩
  choose a ha using hex
  let z : ℕ → ℂ := fun n => relInvC F.c (a n)
  have hz : ∀ n, z n ∈ fwdHull (fun s : ℝ => w s.toNNReal) (u n) \
      fwdHull (fun s : ℝ => w s.toNNReal) t := by
    intro n
    have haH : a n ∈ H := (QuantumZipper.fwdHull_mono (W := fun s : ℝ => R s.toNNReal)).2 _ (ha n).1
    have haK : a n ∈ F.hullAt w (u n) := (hKp n) ▸ (ha n).1
    obtain ⟨b, hb, hba⟩ := haK
    have hzb : z n = b := by
      dsimp only [z]
      rw [← hba, relInvC_relMapC hF.2.2.2.1 hb.2]
    refine ⟨hzb ▸ hb.1, fun hzt => (ha n).2 ?_⟩
    rw [hKq]
    exact ⟨b, ⟨hzb ▸ hzt, hb.2⟩, hba⟩
  let y : ℕ → ℂ := fun n => fwdMap (fun s : ℝ => R s.toNNReal) q (a n)
  have hy0 : Tendsto y atTop (𝓝 0) := tendsto_fwdMap_of_shrinking_increment hRR q.coe_nonneg
    (NNReal.continuous_coe.tendsto q |>.comp hpq) (fun n => NNReal.coe_le_coe.2 (hqp n).le) ha
  have hyH : ∀ n, y n ∈ H := fun n => QuantumZipper.FwdHolo.mapsTo_fwdMap hRR q.coe_nonneg
    ⟨(QuantumZipper.fwdHull_mono (W := fun s : ℝ => R s.toNNReal)).2 _ (ha n).1, (ha n).2⟩
  have hy : Tendsto y atTop (𝓝[H] 0) := tendsto_nhdsWithin_iff.2 ⟨hy0, Eventually.of_forall hyH⟩
  have hInv : ∀ n, (componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 (y n) = z n := by
    intro n
    change relInvC F.c (fwdMapInv (fun s : ℝ => R s.toNNReal) q
      (fwdMap (fun s : ℝ => R s.toNNReal) q (a n))) = _
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hRR hRR0 q.coe_nonneg
      ⟨(QuantumZipper.fwdHull_mono (W := fun s : ℝ => R s.toNNReal)).2 _ (ha n).1, (ha n).2⟩]
  have hz0 := tendsto_fwdMap_of_shrinking_increment hWW t.coe_nonneg
    (NNReal.continuous_coe.tendsto t |>.comp hut) (fun n => NNReal.coe_le_coe.2 (htu n).le) hz
  exact tendsto_nhds_unique ((hx.comp hy).congr fun n => by rw [Function.comp_apply, hInv]) hz0

/-- The anchored transition has an actual full half-plane limit at the
driver, including times at which the physical trace revisits its past. -/
theorem Frame.tendsto_current_transition_tip {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t) :
    Tendsto (fun y => fwdMap (fun s : ℝ => w s.toNNReal) t
      ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 y)) (𝓝[H] 0) (𝓝 0) := by
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hRR : Continuous (fun s : ℝ => R s.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun s : ℝ => R s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hWW : Continuous (fun s : ℝ => w s.toNNReal) := hw.1.comp continuous_real_toNNReal
  have hWW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw.2.1
  obtain ⟨t₀, ht₀⟩ := hVer q hqV
  have hHull := Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 ht₀ htEnt htExit hqt
  have hK : ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).dom : Set ℂ) ⊆
      H \ fwdHull (fun s : ℝ => w s.toNNReal) t := by
    rw [componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0 hHull]
    exact inter_subset_right
  have hcur := ((Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans
    Chart.isConformal_infinitySourceChart).loewner hRR hRR0 q.coe_nonneg
  obtain ⟨E, hE, hEc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 ht₀
  have hLanding := (Sec7.R5Lift.tendsto_of_ext hE hEc 0).1
  obtain ⟨x, -, -, hx⟩ := exists_ambient_transition_limit
    (isLoewnerTrace_of_isGeneratingTrace hw.2.2.1) hWW hWW0 t.coe_nonneg hcur hK hLanding
  rwa [Frame.current_transition_tip_eq_zero hF hw hR hR0 hVer htEnt htExit hqV hqt hx] at hx

end InteractingSLE.Theorem14.GW4Fix
