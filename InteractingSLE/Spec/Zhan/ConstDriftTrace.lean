/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftGap
import InteractingSLE.Spec.Zhan.ConstDriftTraceRs

/-!
# The strip endpoint theorem without the constant-drift trace clause

Packet PROVE-ZHAN-A6. PROVE-ZHAN-A5 reduced PROVE-ZHAN-A4's named input `ConstDriftEndpointStatement κ` to three named
statements: the trace clause `ConstDriftTraceStatement κ`, the scale calculation `UpperGapStatement κ` (proved for
`κ > 0` in `ConstDriftGap.lean`) and the height statement `ConstDriftHeightStatement κ`. In PROVE-ZHAN-A4's assembly of
the strip endpoint theorem (`stripEndpointStatement_of_constDrift`, Astra L1554–L1569) the constant-drift theorem is
applied to the restart of a strip evolution at an integer strip time; the restart's trace clause follows from the
original evolution's trace (PROVE-ZHAN-A3) by [Yua22] Corollary 1.3 (`IsStripPath.isGeneratingTrace_rs`,
`ConstDriftTraceRs.lean`). So only the convergence clause of the constant-drift theorem is needed
(`ConstDriftConvStatement`), and it follows from the scale calculation and the height statement exactly as in
PROVE-ZHAN-A5's proof (the bounded hull, Koebe at the upper points, the endpoint argument).

## Main results

* `ConstDriftConvStatement κ`: the convergence clause (3) of the constant-drift endpoint theorem, strip-driver form;
* `constDriftConvStatement_of_upper_height` (conditional helper):
  `UpperGapStatement κ → ConstDriftHeightStatement κ → ConstDriftConvStatement κ`;
* `stripEndpointStatement_of_constDriftConv` (conditional helper):
  `ConstDriftConvStatement κ → StripEndpointStatement κ` (`0 < κ`), PROVE-ZHAN-A4's whole-tail Girsanov assembly
  with the restart's trace from the original one;
* `stripEndpointStatement_of_height` (**conditional helper, one named input**):
  `0 < κ → ConstDriftHeightStatement κ → StripEndpointStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

universe u

namespace InteractingSLE

namespace Zhan

open Strip

/-- **The convergence clause of the constant-drift endpoint theorem** (Astra L1420–L1499, clause (3) of
`HasStripEndpoint`, strip-driver form): for `|σ| < 1` and every filtered Brownian motion `β`, almost surely every strip
path whose strip driver is `√κ β_t + σ t` satisfies `StripConv` (every continuous generating trace on its strip life
converges along it to a point `x < −1`). -/
def ConstDriftConvStatement (κ : ℝ) : Prop :=
  ∀ σ : ℝ, |σ| < 1 → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ)
    (β : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 β P →
      ∀ᵐ ω ∂P, ∀ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞),
        HasStripDriver w v ζ (fun t => Real.sqrt κ * β t ω + σ * t) → StripConv w v ζ

section Conv

variable {κ : ℝ}

/-- **The convergence clause from the scale calculation and the height statement** (conditional helper;
PROVE-ZHAN-A5's proof of `constDriftEndpointStatement_of_trace_upper_height` without its trace clause). -/
theorem constDriftConvStatement_of_upper_height (hU : UpperGapStatement.{u} κ)
    (hH : ConstDriftHeightStatement.{u} κ) : ConstDriftConvStatement.{u} κ := by
  intro σ hσ Ω mΩ P 𝓗 β hβ
  filter_upwards [hU σ hσ P 𝓗 β hβ, hH σ hσ P 𝓗 β hβ, hβ.1.cont, hβ.1.tendsto_div_id_atTop]
    with ω hup hht hc hlaw
  intro w v ζ hd
  have h := hd.1
  have hξ := hd.2
  -- sublinearity and the bounded hull
  set a := (|σ| + 1) / 2 with ha
  have hσa : |σ| < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  set b := (a + 1) / 2 with hb
  have hb0 : 0 < b := by rw [hb]; linarith [abs_nonneg σ]
  have hb1 : b < 1 := by rw [hb]; linarith
  have hab : a ≤ b := by rw [hb]; linarith
  obtain ⟨hR, hbR⟩ := le_tanh_half_log b hb0 hb1
  set R := Real.log ((1 + b) / (1 - b)) with hRdef
  obtain ⟨C, hC⟩ := abs_driver_le_of_sublinear (κ := κ) hσa hc hlaw
  have hξC : ∀ t : ℝ≥0, |stripDriver (extPath w) (extPath v) t| ≤ C + a * t := fun t => by
    rw [hξ t]; exact hC t
  intro η hη
  refine h.stripConv_of_height hη (M := C + R) (fun s hs => ?_) (hht w v ζ η hd hη) fun q => ?_
  · have := h.norm_one_add_trace_mem_Icc hR hbR hab hξC hη hs
    simpa using this
  -- the rational upper points
  have hy : -1 - Real.exp q < -1 := by linarith [Real.exp_pos (q : ℝ)]
  have hlog : Real.log (-1 - (-1 - Real.exp q)) = q := by
    rw [show -1 - (-1 - Real.exp (q : ℝ)) = Real.exp q by ring, Real.log_exp]
  obtain ⟨K, hK⟩ := hup q
  refine h.exists_pos_le_norm_trace_sub_sech hη hy (K := K) fun s' s'' hs's'' hs'' uy huy => ?_
  rw [h.integral_sech_eq_upperGap hy hs's'' hs'' huy]
  refine hK _ (((h.2.1 s' (hs''.mono hs's''.le))).stripClock_nonneg ⟨NNReal.coe_nonneg s', le_rfl⟩)
    _ (h.continuousOn_upperGapOf hy hs's'' hs'' huy) fun t ht => ?_
  rw [h.upperGapOf_ode hy hs's'' hs'' huy ht, hlog]
  congr 2
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have := hξ t.toNNReal
  simp only at this
  rw [Real.coe_toNNReal _ ht0] at this
  exact this

end Conv

section Assembly

variable {nL nR : ℕ} {κ : ℝ}

/-- **Zhan's strip endpoint theorem (ii) from the convergence clause of the constant-drift theorem** (conditional
helper; PROVE-ZHAN-A4's `stripEndpointStatement_of_constDrift` with the restart's trace clause supplied by
`IsStripPath.isGeneratingTrace_rs` from the original evolution's trace). -/
theorem stripEndpointStatement_of_constDriftConv (hκ : 0 < κ) (h : ConstDriftConvStatement.{u} κ) :
    StripEndpointStatement.{u} κ := by
  intro nL nR pL pR ρL ρR τm Ω mΩ P 𝓕 W VL VR B ζ hsep hpre hq hE
  classical
  have hP : IsProbabilityMeasure P :=
    hE.isFilteredBrownianReal.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  refine ae_hasStripEndpoint_of_convergence hκ hsep hpre hE ?_
  -- PROVE-ZHAN-A2's strip filtration and strip Brownian motion
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good_strip hE (ae_hasUnboundedStripClock hκ hsep hpre hE)
  have h0 := stripInit_mem_region_word pL pR ρL ρR τm κ
  have hB' : IsFilteredBrownianReal (stripFilt hE hGm hGc hgood)
      (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B) P :=
    isFilteredBrownianReal_stripBM hE hGm hGc hgood h0 hκ
  have hB'c : ∀ ω, Continuous (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B · ω) :=
    continuous_stripBM hgood h0
  -- noncollision on a measurable full set
  have hnc := ae_stripLife_noncollision hκ hsep hpre hE
  set S : Set Ω := (toMeasurable P {ω | ¬ ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
    (∀ i : Fin nL, VL i.castSucc s ω < W s ω) ∧ ∀ j : Fin nR, W s ω < VR j s ω})ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSc : P Sᶜ = 0 := by rw [hSdef, compl_compl, measure_toMeasurable]; exact ae_iff.1 hnc
  have hSnc : ∀ ω ∈ S, ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
      (∀ i : Fin nL, VL i.castSucc s ω < W s ω) ∧ ∀ j : Fin nR, W s ω < VR j s ω := fun ω hω => by
    by_contra hcon
    exact hω (subset_toMeasurable _ _ hcon)
  set G' : Set Ω := G ∩ S with hG'def
  have hG'm : MeasurableSet G' := hGm.inter hSm
  have hG'c : P G'ᶜ = 0 := by rw [hG'def, compl_inter]; exact measure_union_null hGc hSc
  have hgd : ∀ ω ∈ G', StripGood κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) := fun ω hω =>
    ⟨(hgood ω hω.1).1, (hgood ω hω.1).2.2.2, hSnc ω hω.2⟩
  -- the adapted, continuous drift error
  set e : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G' then errOfState κ (Strip.wordXL pL) (Strip.wordXR pR)
    (Strip.wordRhoL ρL τm) ρR ρL ρR (stateAt pL (Strip.wordXR pR) G W VL VR B t ω) else 0 with hedef
  have heq : ∀ ω ∈ G', ∀ t, e t ω = stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t :=
    fun ω hω t => by
      show (if ω ∈ G' then _ else _) = _
      simp only [hω, ite_true]
      exact errOfState_stateAt hgood hω.1 ρL ρR t
  have hG'H : ∀ t, MeasurableSet[stripFilt hE hGm hGc hgood t] G' := fun t => by
    have h1 : MeasurableSet[usualAugmentation 𝓕 P 0] G' := by
      have := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hG'm.compl hG'c 0).compl
      rwa [compl_compl] at this
    exact (isStoppingTime_chordS hE hGm hGc hgood t).le_measurableSpace_of_const_le (i := 0)
      (fun ω => WithTop.coe_le_coe.2 (by positivity)) _ h1
  have he : ∀ t, Measurable[stripFilt hE hGm hGc hgood t] (e t) := fun t => by
    show Measurable[stripFilt hE hGm hGc hgood t] fun ω => if ω ∈ G' then errOfState κ (Strip.wordXL pL)
      (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR ρL ρR (stateAt pL (Strip.wordXR pR) G W VL VR B t ω) else 0
    exact Measurable.ite (hG'H t) ((measurable_errOfState κ (Strip.wordXL pL) (Strip.wordXR pR)
      (Strip.wordRhoL ρL τm) ρR ρL ρR).comp (measurable_stateAt hE hGm hGc hgood t)) measurable_const
  have hec : ∀ ω, Continuous (e · ω) := by
    intro ω
    by_cases hω : ω ∈ G'
    · have e1 : (e · ω) = fun t : ℝ≥0 =>
          stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t := funext fun t => heq ω hω t
      rw [e1]
      exact ((hgd ω hω).continuousOn_stripErr_Ici ρL ρR).comp_continuous NNReal.continuous_coe
        fun t => NNReal.coe_nonneg t
    · have e1 : (e · ω) = fun _ => (0 : ℝ) := funext fun t => by
        show (if ω ∈ G' then _ else _) = _
        simp only [hω, ite_false]
      rw [e1]
      exact continuous_const
  -- the drift and the side sums
  set σ := (τm - tauPlus κ ρL ρR τm) / 2 + (∑ i, ρL i) / 2 - (∑ j, ρR j) / 2 with hσdef
  have hσ : |σ| < 1 := abs_stripDrift_lt_one hq
  have hsl := one_add_sum_div_two_nonneg hκ hpre.1
  have hsr := one_add_sum_div_two_nonneg hκ hpre.2
  -- every `(n, M)`: the reference tail and the named input, almost surely
  have hnm : ∀ n M : ℕ, ∀ᵐ ω ∂P, ∃ β : ℝ≥0 → ℝ,
      ((∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1) →
        (∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M) →
        ∀ t : ℝ≥0, Real.sqrt κ * β t =
          Real.sqrt κ * (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B
              ((n : ℝ≥0) + 1 + t) ω -
            stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B ((n : ℝ≥0) + 1) ω) +
            ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω) ∧
      ∀ (w v : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), HasStripDriver w v ζ' (fun t => Real.sqrt κ * β t + σ * t) →
        StripConv w v ζ' := by
    intro n M
    obtain ⟨Q, 𝓗', β, hQ, hβ, hid⟩ := Tail.exists_tail_reference hκ hB' hB'c he hec n M
    filter_upwards [hQ.ac'.ae_le (h σ hσ Q 𝓗' β hβ)] with ω hω
    exact ⟨(β · ω), hid ω, hω⟩
  have hnm' : ∀ᵐ ω ∂P, ∀ n M : ℕ, ∃ β : ℝ≥0 → ℝ,
      ((∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1) →
        (∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M) →
        ∀ t : ℝ≥0, Real.sqrt κ * β t =
          Real.sqrt κ * (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B
              ((n : ℝ≥0) + 1 + t) ω -
            stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B ((n : ℝ≥0) + 1) ω) +
            ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω) ∧
      ∀ (w v : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), HasStripDriver w v ζ' (fun t => Real.sqrt κ * β t + σ * t) →
        StripConv w v ζ' := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; exact hnm n
  have hlaw := ProbabilityTheory.IsBrownianReal.tendsto_div_id_atTop hB'.1
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by rw [ae_iff]; exact hG'c
  filter_upwards [hnm', hlaw, hG'ae, ae_hasStripEndpoint_clock_trace hκ hsep hpre hE] with ω hω hsub hωG htr
  obtain ⟨ηo, hηo⟩ := htr.2
  have hg := hgd ω hωG
  set B' := stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B with hB'def
  -- the strip driver as constant drift plus error
  have hξ0 : ∀ t : ℝ≥0, stripDriver (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) t =
      Real.sqrt κ * B' t ω + σ * t +
        ∫ r in (0 : ℝ)..t, stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r :=
    fun t => hg.stripDriver_eq (N := fun t => Real.sqrt κ * B' t ω)
      (fun t => stripDriver_eq_stripBM hκ hgood hωG.1 t) t
  have hξ : ∀ u : ℝ, 0 ≤ u → stripDriver (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) u =
      Real.sqrt κ * B' u.toNNReal ω + σ * u +
        ∫ r in (0 : ℝ)..u, stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r :=
    fun u hu => by
      have := hξ0 u.toNNReal
      rwa [Real.coe_toNNReal _ hu] at this
  have hN := sublinear_of_tendsto (hB'c ω) hsub (Real.sqrt κ)
  obtain ⟨α, hα, T, hT⟩ := hg.exists_linear_escape (N := fun u => Real.sqrt κ * B' u.toNNReal ω) hξ hN
    hsl hsr hσ
  obtain ⟨T', hT'0, M', hbd⟩ := hg.exists_stripErr_bound (ρl := ρL) (ρr := ρR) hα hT
  set n := ⌈T'⌉₊ with hn
  set M := ⌈M'⌉₊ with hM
  have hnT : T' ≤ (n : ℝ) := Nat.le_ceil T'
  have hMM : M' ≤ (M : ℝ) := Nat.le_ceil M'
  have hcut1 : ∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1 := fun u hu => by
    rw [heq ω hωG u]
    exact (hbd u (hnT.trans (by exact_mod_cast hu))).1
  have hcut2 : ∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M := fun u hu => by
    have hnu : (n : ℝ) ≤ u := by exact_mod_cast hu
    have hcongr : ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 =
        ∫ r in (n : ℝ)..(u : ℝ), stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r ^ 2 := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hnu] at hr
      have hr0 : 0 ≤ r := (Nat.cast_nonneg n).trans hr.1
      simp only [heq ω hωG, Real.coe_toNNReal _ hr0]
    have hc2 := (hg.continuousOn_stripErr_Ici ρL ρR).pow 2
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := T') (b := (n : ℝ))
      (c := (u : ℝ)) (f := fun r => stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r ^ 2)
      ((hc2.mono (by rw [uIcc_of_le hnT]; exact fun r hr => hT'0.trans hr.1)).intervalIntegrable)
      ((hc2.mono (by rw [uIcc_of_le hnu]; exact fun r hr => (hT'0.trans hnT).trans hr.1)).intervalIntegrable)
    have hnn : 0 ≤ ∫ r in T'..(n : ℝ),
        stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r ^ 2 :=
      intervalIntegral.integral_nonneg hnT fun r _ => sq_nonneg _
    have := (hbd u (hnT.trans hnu)).2
    rw [hcongr]
    linarith
  obtain ⟨β, hid, hbase⟩ := hω n M
  have hid' := hid hcut1 hcut2
  -- the restart at strip time `n + 1` has the constant-drift strip driver
  have hSD : HasStripDriver (W · ω) (VL (Fin.last nL) · ω) (ζ ω)
      (fun t => stripDriver (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) t) :=
    ⟨hg.isStripPath, fun t => rfl⟩
  have hR := hSD.rs ((n : ℝ≥0) + 1)
  have hR' : HasStripDriver (rsW (W · ω) (VL (Fin.last nL) · ω) ((n : ℝ≥0) + 1))
      (rsV (W · ω) (VL (Fin.last nL) · ω) ((n : ℝ≥0) + 1))
      (rsZ (W · ω) (VL (Fin.last nL) · ω) (ζ ω) ((n : ℝ≥0) + 1)) (fun t => Real.sqrt κ * β t + σ * t) := by
    refine ⟨hR.1, fun t => ?_⟩
    rw [hR.2 t]
    have h1 := hξ0 ((n : ℝ≥0) + 1 + t)
    have h2 := hξ0 ((n : ℝ≥0) + 1)
    have hint := intervalIntegral.integral_interval_sub_left (μ := volume)
      (hg.intervalIntegrable_stripErr ρL ρR le_rfl (NNReal.coe_nonneg ((n : ℝ≥0) + 1 + t)))
      (hg.intervalIntegrable_stripErr ρL ρR le_rfl (NNReal.coe_nonneg ((n : ℝ≥0) + 1)))
    have hcongr : ∫ r in (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ)..(((n : ℝ≥0) + 1 + t : ℝ≥0) : ℝ),
        stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r =
        ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω := by
      push_cast
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le (by linarith [NNReal.coe_nonneg t])] at hr
      have hr0 : 0 ≤ r := by linarith [hr.1, Nat.cast_nonneg (α := ℝ) n]
      simp only [heq ω hωG, Real.coe_toNNReal _ hr0]
    have hβt := hid' t
    simp only at h1 h2 ⊢
    rw [h1, h2]
    have hc : ((((n : ℝ≥0) + 1 + t : ℝ≥0)) : ℝ) = (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) + t := by push_cast; ring
    have hσc : σ * ((((n : ℝ≥0) + 1 + t : ℝ≥0)) : ℝ) = σ * (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) + σ * t := by
      rw [hc]; ring
    linarith
  -- the restart has the trace mapped out of the original one ([Yua22] Corollary 1.3)
  exact hg.isStripPath.stripConv_of_rs ((n : ℝ≥0) + 1)
    ⟨hR'.1.2.2, ⟨_, fun r hr => hg.isStripPath.isGeneratingTrace_rs hηo _ hr⟩, hbase _ _ _ hR'⟩

/-- **Zhan's strip endpoint theorem (ii) from the height statement** (conditional helper; its single hypothesis is the
named statement `ConstDriftHeightStatement κ`, Astra L1471–L1499): the scale calculation is
`upperGapStatement` (`κ > 0`) and the constant-drift trace clause is not needed. -/
theorem stripEndpointStatement_of_height (hκ : 0 < κ) (hH : ConstDriftHeightStatement.{u} κ) :
    StripEndpointStatement.{u} κ :=
  stripEndpointStatement_of_constDriftConv hκ (constDriftConvStatement_of_upper_height (upperGapStatement hκ) hH)

/-- **The constant-drift endpoint theorem from the trace and height statements** (conditional helper;
PROVE-ZHAN-A5's `constDriftEndpointStatement_of_trace_upper_height` with the scale calculation discharged). -/
theorem constDriftEndpointStatement_of_trace_height (hκ : 0 < κ) (hT : ConstDriftTraceStatement.{u} κ)
    (hH : ConstDriftHeightStatement.{u} κ) : ConstDriftEndpointStatement.{u} κ :=
  constDriftEndpointStatement_of_trace_upper_height hT (upperGapStatement hκ) hH

end Assembly

end Zhan

end InteractingSLE
