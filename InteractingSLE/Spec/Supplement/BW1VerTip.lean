/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1VerSample
import InteractingSLE.Spec.Supplement.BW1DetWitness
import InteractingSLE.Spec.Supplement.BW1PropFrozen
import InteractingSLE.Spec.Supplement.BW1InEndDetBase

/-!
# The tip relation of one sample of the relative exploration

Packet PROVE-BW1-INPUTS2. For a good sample with relative coordinates `(D, L)`, a chart `c` whose inverse is the
inverse Loewner map of the record driver at its own time with a proper boundary extension `f`, and the inverse `ℓ` of
the relative clock: before every `V < L`, the tips of the relative driver frozen at `V`, read through `c` and the
inversion, are the physical tips of the counterflow at `ℓ` (`sample_tip`). Two boundary identities of GB6's relative
chart are proved first (`relBdry_eq_zero_iff`, `f_negInv_relBdry`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Ver

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.CoordB Supp8.GB6.GaugeE Sec7.PocketTraversal Sec7.Lemma71C

section Bdry

variable {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {f : ℂ → ℂ} {C : ℝ}
  (hf : ∀ p ∈ Hbar, Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] p) (𝓝 (f p)))
  (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)

include hU hU0 hs hf in
theorem f_eq_fwdMapInv {p : ℂ} (hp : p ∈ H) : f p = QuantumZipper.fwdMapInv U s p := by
  have hne : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hp)
  exact tendsto_nhds_unique (hf p (show (0 : ℝ) ≤ p.im from le_of_lt hp))
    (continuousOn_fwdMapInv hU hU0 hs p hp).tendsto

include hU hU0 hs in
/-- The relative chart's inverse identity. -/
theorem fwdMapInv_negInv_relMap {w : ℂ} (hw : w ∈ relDomain U s) :
    relMap U s w ∈ H ∧ QuantumZipper.fwdMapInv U s (-(relMap U s w)⁻¹) = -w⁻¹ := by
  obtain ⟨hwH, hwK⟩ := (mem_relDomain_iff U s w).1 hw
  refine ⟨relMap_mem_H hU hs hwH hwK, ?_⟩
  have h := relInv_relMap hU hU0 hs hwH hwK
  unfold relInv at h
  calc QuantumZipper.fwdMapInv U s (-(relMap U s w)⁻¹)
      = -(-(QuantumZipper.fwdMapInv U s (-(relMap U s w)⁻¹))⁻¹)⁻¹ := (neg_inv_neg_inv _).symm
    _ = -w⁻¹ := by rw [h]

include hU hU0 hs hf hC in
/-- **GB6's boundary chart vanishes exactly at `0`**, and off `0` the boundary extension of the inverse map undoes
it: `f(−1/Ψ(z)) = −1/z`. -/
theorem relBdry_facts {z : ℂ} (hz : z ∈ relSafe U s) :
    (relBdry U s z = 0 ↔ z = 0) ∧
      (relBdry U s z ≠ 0 → f (-(relBdry U s z)⁻¹) = -z⁻¹) := by
  set y := relBdry U s z with hydef
  have hw := tendsto_vert_relDomain hz
  have hwD : ∀ᶠ n in atTop, vert n z ∈ relDomain U s := (tendsto_nhdsWithin_iff.1 hw).2
  have hy : Tendsto (fun n => relMap U s (vert n z)) atTop (𝓝 y) :=
    (tendsto_relMap_relBdry hU hU0 hs hz).comp hw
  have hvz : Tendsto (fun n => vert n z) atTop (𝓝 z) := tendsto_vert z
  have hinv : ∀ᶠ n in atTop, relMap U s (vert n z) ∈ H ∧
      QuantumZipper.fwdMapInv U s (-(relMap U s (vert n z))⁻¹) = -(vert n z)⁻¹ :=
    hwD.mono fun n hn => fwdMapInv_negInv_relMap hU hU0 hs hn
  have hz0 : z = 0 → y = 0 := fun h => by rw [hydef, h]; exact relBdry_zero hU hU0 hs
  have hmain : z ≠ 0 → y ≠ 0 ∧ f (-y⁻¹) = -z⁻¹ := by
    intro hzne
    have hlimz : Tendsto (fun n => -(vert n z)⁻¹) atTop (𝓝 (-z⁻¹)) :=
      ((continuousAt_inv₀ hzne).tendsto.comp hvz).neg
    have hyne : y ≠ 0 := by
      intro hy0
      rw [hy0] at hy
      have hbig : Tendsto (fun n => ‖-(relMap U s (vert n z))⁻¹‖) atTop atTop := by
        simp only [norm_neg, norm_inv]
        refine tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
        · simpa only [norm_zero] using hy.norm
        · exact hinv.mono fun n hn => norm_pos_iff.2 (ne_zero_of_mem_H hn.1)
      have hbd : ∀ᶠ n in atTop, ‖-(vert n z)⁻¹‖ ≤ ‖-z⁻¹‖ + 1 :=
        (hlimz.norm.eventually (gt_mem_nhds (lt_add_one ‖-z⁻¹‖))).mono fun n hn => hn.le
      obtain ⟨n, hn1, ⟨hn2a, hn2b⟩, hn3⟩ := ((tendsto_atTop.1 hbig (‖-z⁻¹‖ + 1 + C + 1)).and (hinv.and hbd)).exists
      have hξH : -(relMap U s (vert n z))⁻¹ ∈ H := neg_inv_mem_H hn2a
      have hfe := f_eq_fwdMapInv hU hU0 hs hf hξH
      have hc := hC _ (show (0 : ℝ) ≤ (-(relMap U s (vert n z))⁻¹).im from le_of_lt hξH)
      rw [hfe, hn2b] at hc
      have h4 := norm_sub_norm_le (-(relMap U s (vert n z))⁻¹) (-(vert n z)⁻¹)
      rw [norm_sub_rev] at hc
      linarith
    refine ⟨hyne, ?_⟩
    have hξ : Tendsto (fun n => -(relMap U s (vert n z))⁻¹) atTop (𝓝[H] (-y⁻¹)) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuousAt_inv₀ hyne).tendsto.comp hy).neg,
        hinv.mono fun n hn => neg_inv_mem_H hn.1⟩
    have hyH : -y⁻¹ ∈ Hbar := by
      have hyb : y ∈ Hbar := by
        rw [← closure_H]
        exact mem_closure_of_tendsto hy (hinv.mono fun n hn => hn.1)
      exact GW4Traverse.negInv_mem_Hbar hyb
    have h1 := (hf _ hyH).comp hξ
    have h2 : Tendsto (fun n => QuantumZipper.fwdMapInv U s (-(relMap U s (vert n z))⁻¹)) atTop
        (𝓝 (-z⁻¹)) := hlimz.congr' (hinv.mono fun n hn => hn.2.symm)
    exact tendsto_nhds_unique h1 h2
  refine ⟨⟨fun h0 => by_contra fun hne => (hmain hne).1 h0, hz0⟩, fun hy0 => ?_⟩
  exact (hmain fun h => hy0 (hz0 h)).2

end Bdry

section Sample

variable {r : RecData} {A : ℝ≥0 → ℂ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {D : ℝ≥0 → ℝ} {L : ℝ≥0∞}

/-- The relative hulls of the coordinates at the clock values on a compact prefix. -/
theorem IsSampleCoord.hulls_Icc (hC : IsSampleCoord r A w γ D L) {S : ℝ≥0}
    (hS : (S : ℝ≥0∞) < contactT γ A (recS r)) :
    ∀ q ∈ Icc (0 : ℝ) S, fwdHull (Ito.rpath D) (relClock (rdrv r) (recS r) (Ito.rpath w) q) =
      relMap (rdrv r) (recS r) '' fwdHull (Ito.rpath w) q := by
  intro q hq
  have hqS : q.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hq.2
  have hqTc : (q.toNNReal : ℝ≥0∞) < contactT γ A (recS r) := (ENNReal.coe_le_coe.2 hqS).trans_lt hS
  have he := (hC.hulls q.toNNReal hqTc).2.2
  rw [← Real.coe_toNNReal q hq.1]
  exact he

/-- **The relative driver's trace at a clock value is the boundary chart value of the physical trace.** -/
theorem sample_traceAt (hg : IsGoodSample r A w γ) (hC : IsSampleCoord r A w γ D L) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < contactT γ A (recS r)) :
    LP.traceAt (rclk r w t).toNNReal D = relBdry (rdrv r) (recS r) (γ t) := by
  have hs0 : (0 : ℝ) < recS r := by exact_mod_cast hg.pos
  obtain ⟨S, htS, hS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨T, hST, hT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hS
  have hST' : S < T := ENNReal.coe_lt_coe.1 hST
  have htS' : t < S := ENNReal.coe_lt_coe.1 htS
  have hS0 : 0 < S := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ t) htS'
  exact traceAt_of_relHulls (continuous_rdrv r) (rdrv_zero r) hs0 hg.tip hg.cont hg.zero hg.ctrace
    (hS0.trans hST') (hg.disjoint hT) hC.cont hC.zero hS0 hST' (hC.hulls S hS).2.1 (hC.hulls_Icc hS) htS'.le

/-- **The tip relation of one sample.** Before `V < L`, the tips of the relative driver frozen at `V`, read through a
chart `c` inverting to the record's Loewner map at its own time (with a proper boundary extension) and the inversion,
are the physical tips of the counterflow at the inverse clock `ℓ`. -/
theorem sample_tip (hg : IsGoodSample r A w γ) (hC : IsSampleCoord r A w γ D L) {c : Chart}
    (hc : c.2.1 = QuantumZipper.fwdMapInv (rdrv r) (recS r)) {f : ℂ → ℂ} {Cb : ℝ}
    (hf : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) (hCb : ∀ p ∈ Hbar, ‖f p - p‖ ≤ Cb)
    {V : ℝ≥0} (hV0 : 0 < V) (hVL : (V : ℝ≥0∞) < L) {ℓ : ℝ≥0 → ℝ≥0}
    (hℓ : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → (ℓ u : ℝ≥0∞) < contactT γ A (recS r) ∧ rclk r w (ℓ u) = u)
    {u : ℝ≥0} (hu : u < V) (z : ℂ) :
    (c.trans infinitySourceChart).tipAt (fun x => D (min x V)) u z ↔ infinitySourceChart.tipAt w (ℓ u) z := by
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hs0 : (0 : ℝ) < recS r := by exact_mod_cast hg.pos
  have htip := hg.tip
  have ha0 := (sample_readout hg hC).1
  -- a local relative curve beyond `V`
  obtain ⟨t₁, ht₁, hVt₁⟩ := hC.range V hVL
  obtain ⟨t₂, ht₁₂, ht₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₁
  have ht₁₂' : t₁ < t₂ := ENNReal.coe_lt_coe.1 ht₁₂
  have ht₂0 : 0 < t₂ := lt_of_le_of_lt zero_le ht₁₂'
  have hd₂ := hg.disjoint ht₂
  have ht₁0 : 0 < t₁ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₁) with h | h
    · rw [← h, ha0] at hVt₁
      exact absurd hVt₁ (not_lt.2 V.coe_nonneg)
    · exact h
  have hΓl : IsDrivenCurve (localCurve (rdrv r) (recS r) γ t₂) :=
    isDrivenCurve_localCurve hU hU0 hs0 htip hg.cont hg.zero hg.ctrace ht₂0 hd₂
  have hL1 := relClock_lt_localLife hU hU0 hs0 htip hg.cont hg.zero hg.ctrace hd₂ ht₂0 ht₁₂'
  have hgen := hΓl.isGeneratingTrace hL1
  have hlocal : ∀ v : ℝ≥0, (v : ℝ) ≤ rclk r w t₁ →
      drivenDriver (fun _ : Unit => localCurve (rdrv r) (recS r) γ t₂) v () = D v := fun v hv =>
    localDriver_eq_of_relHulls hU hU0 hs0 htip hg.cont hg.zero hg.ctrace ht₂0 hd₂ hC.cont hC.zero ht₁0 ht₁₂'
      (hC.hulls t₁ ht₁).2.1 (hC.hulls_Icc ht₁) hv
  -- the frozen driver generates the local curve's capacity trace up to `V`
  set Dfr : ℝ≥0 → ℝ := fun x => D (min x V) with hDfr
  have hDfrc : Continuous Dfr := hC.cont.comp_continuous (continuous_id.min continuous_const)
    fun x => (ENNReal.coe_le_coe.2 (min_le_right x V)).trans_lt hVL
  have hDfr0 : Dfr 0 = 0 := by simp only [hDfr, zero_min, hC.zero]
  have hVa : (V : ℝ≥0∞) ≤ ENNReal.ofReal (rclk r w t₁) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hVt₁.le
  have hgenV : IsGeneratingTrace Dfr V (capTrace (localCurve (rdrv r) (recS r) γ t₂)) := by
    have hmono : IsGeneratingTrace (segDriver (localCurve (rdrv r) (recS r) γ t₂)) V
        (capTrace (localCurve (rdrv r) (recS r) γ t₂)) :=
      ⟨hgen.1, hgen.2.1.mono fun t ht => le_trans ht hVa, fun t ht => hgen.2.2 t (lt_of_lt_of_le ht hVa)⟩
    refine Sec7.IsGeneratingTrace.congr_lt hmono fun t ht => ?_
    have htV : t < V := ENNReal.coe_lt_coe.1 ht
    have htl : (t : ℝ) ≤ rclk r w t₁ := (NNReal.coe_le_coe.2 htV.le).trans hVt₁.le
    have htL : (t : ℝ≥0∞) < capLife (localCurve (rdrv r) (recS r) γ t₂) :=
      (ht.trans_le hVa).trans hL1
    rw [hDfr]
    simp only [min_eq_left htV.le]
    rw [← hlocal t htl]
    simp only [drivenDriver, htL, ↓reduceIte]
  -- a global generating trace of the frozen driver
  obtain ⟨αr, hαr, -⟩ := BW1Prop.exists_frozen_trace_close hgenV hDfrc.continuousOn hDfr0 hV0
  have hUnn : ∀ x : ℝ, (fun r : ℝ => Dfr (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (V : ℝ≥0∞)).toNNReal)
      (x.toNNReal : ℝ) = (fun r : ℝ => Dfr (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (V : ℝ≥0∞)).toNNReal) x := by
    intro x
    simp only [Real.toNNReal_coe]
  have hΓg0 := BW1In.isGeneratingTrace_of_isLoewnerTrace hUnn hαr
  have hUeq : (fun s : ℝ≥0 => (fun r : ℝ => Dfr (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (V : ℝ≥0∞)).toNNReal)
      (s : ℝ)) = Dfr := by
    funext x
    simp only [Real.toNNReal_coe, ← ENNReal.coe_min, ENNReal.toNNReal_coe, hDfr, min_assoc, min_self]
  rw [hUeq] at hΓg0
  -- the tip relation through traces
  have hfU : ∀ p ∈ Hbar, Tendsto (QuantumZipper.fwdMapInv (rdrv r) (recS r)) (𝓝[H] p) (𝓝 (f p)) := by
    rw [← hc]; exact hf
  have huL : (u : ℝ≥0∞) < L := (ENNReal.coe_lt_coe.2 hu).trans hVL
  obtain ⟨hℓT, hℓa⟩ := hℓ u huL
  have hz₀ : γ (ℓ u) ∈ relSafe (rdrv r) (recS r) :=
    trace_mem_relSafe hU (recS r).coe_nonneg hg.cont hg.zero hg.ctrace
      (Supp8.Q3Rel.disjoint_closure_invHull hU (recS r).coe_nonneg (hg.disjoint hℓT)) le_rfl
  have hΓu : αr (u : ℝ) = relBdry (rdrv r) (recS r) (γ (ℓ u)) := by
    rw [← LP.traceAt_eq_of_isGeneratingTrace hΓg0 hDfrc.continuousOn hDfr0 ENNReal.coe_lt_top]
    rw [LP.traceAt_congr (w' := D) fun x hx => by simp only [hDfr, min_eq_left (hx.trans hu.le)]]
    have h := sample_traceAt hg hC hℓT
    rw [hℓa, Real.toNNReal_coe] at h
    exact h
  have hfacts := relBdry_facts hU hU0 (recS r).coe_nonneg hfU hCb hz₀
  have hiff := BW1Det.tipRel_iff_traces hf hCb hΓg0 hDfrc hDfr0 hg.ctrace hg.cont hg.zero u (ℓ u)
  refine (hiff.2 ⟨?_, ?_⟩) z
  · rw [hΓu]; exact hfacts.1
  · intro hne
    rw [hΓu] at hne ⊢
    exact hfacts.2 hne

end Sample

end InteractingSLE.Theorem14.BW1Ver
