/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7Band
import InteractingSLE.Spec.Sec7.ContinuityProb5Aux106

/-!
# Aux. lemma 102 with its band switches: `Sec7.Aux102BandStatement` proved

Packet PROVE-SEC7-C7. This file finishes the proof of the named input `Sec7.Aux102BandStatement`
(`ContinuityProb5Aux106.lean`, PROVE-SEC7-C5): Aux. lemma 102 (Specification p. 348, the finite total angular clock
when a side total is at most `−2`) and the finitely many band switches of Aux. lemma 106 (p. 354).

* The band process `N̂ = h(U) − ∫ itoGen h(U)` is almost surely Cauchy at infinity on `{ζ = ∞}`
  (`ae_nhat_cauchy`): Doob's inequality bounds the oscillation after `s` by the expected tail clock
  (`measureReal_osc_le`), and the tail clocks tend to `0` in `L¹` by dominated convergence (`tendsto_clockTail`).
* Pathwise, the drift `∫ itoGen h(U)` is absolutely integrable on `[0, ∞)` by the finite clock and (P4), so
  `h(U_t)` is Cauchy; since `h = 1` on `U ≥ 3/4` and `h = 0` on `U ≤ 1/4`, `U` eventually avoids one of the two
  regions (`eventually_band_of_cauchy`).

## Main results

* `ae_nhat_cauchy`, `eventually_band_of_cauchy`, `ae_eventually_band`;
* **`aux102BandStatement : Sec7.Aux102BandStatement`**;
* `aux106TransienceStatement_of_aux102'`: Aux. 106's transience from the one-force inputs and Aux. 106's positive case.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace Clock

open Zhan

variable {nL nR : ℕ}

section Cauchy

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hκ hE hGm hGc hgood hT hx in
/-- **The band process is almost surely Cauchy at infinity** on `{ζ = ∞}`. -/
theorem ae_nhat_cauchy (hab : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) (k : ℕ) :
    ∀ᵐ ω ∂P, ω ∈ G → ζ ω = ⊤ → ∃ s : ℕ, ∀ r : ℝ≥0, (s : ℝ≥0) ≤ r →
      |Nhat κ ρL ρR W VL VR r ω - Nhat κ ρL ρR W VL VR s ω| ≤ 1 / ((k : ℝ) + 1) := by
  have hP := hE.1.isProbabilityMeasure'
  obtain ⟨K', hK'0, hK'⟩ := exists_bound_hB'
  obtain ⟨K'', -, hK''⟩ := exists_bound_hB''
  have hTm : ∀ ω, Monotone (T · ω) := hT.2.1
  obtain ⟨C, hC⟩ := exists_lintegral_clockY_le hκ hE hGm hGc hgood hT hx hab
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  -- the total clock is integrable
  have hYm : ∀ n, Measurable fun ω => ENNReal.ofReal (clockY xL xR G T W VL VR B ζ n ω) := fun n =>
    (measurable_clockY hE hGm hGc hgood hT hx n).ennreal_ofReal
  have hTot : ∫⁻ ω, clockTot xL xR G T W VL VR B ζ ω ∂P ≤ ENNReal.ofReal C := by
    unfold clockTot
    rw [lintegral_iSup hYm fun m n h ω => ENNReal.ofReal_le_ofReal (clockY_mono hgood hx hTm ω h)]
    exact iSup_le hC
  have hTotfin : ∫⁻ ω, clockTot xL xR G T W VL VR B ζ ω ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTot
  have hTailm : ∀ s : ℕ, Measurable (clockTail xL xR G T W VL VR B ζ s) := fun s =>
    Measurable.iSup fun n => (measurable_clockR hE hGm hGc hgood hT hx n s).ennreal_ofReal
  have hlim : Tendsto (fun s : ℕ => ∫⁻ ω, clockTail xL xR G T W VL VR B ζ s ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (μ := P) (f := fun _ => 0)
      (clockTot xL xR G T W VL VR B ζ) hTailm (fun s => ae_of_all _ (clockTail_le s)) hTotfin
      (by
        filter_upwards [ae_lt_top (Measurable.iSup hYm) hTotfin] with ω hω
        exact tendsto_clockTail hgood hx hTm hω)
    simpa using h
  have hlimR : Tendsto (fun s : ℕ => (∫⁻ ω, clockTail xL xR G T W VL VR B ζ s ω ∂P).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
    rw [ENNReal.toReal_zero] at this
    exact this
  -- the oscillation events
  set E : ℕ → ℕ → Set Ω := fun n s => {ω | ε ≤ ⨆ i : Set.Iic (n : ℝ≥0),
    ‖1 * (bandN κ xL xR ρL ρR G T W VL VR B ζ n i ω -
      bandN κ xL xR ρL ρR G T W VL VR B ζ n (min (i : ℝ≥0) (s : ℝ≥0)) ω)‖} with hEdef
  set Bad := {ω | ω ∈ G ∧ ζ ω = ⊤ ∧ ∀ s : ℕ, ∃ r : ℝ≥0, (s : ℝ≥0) ≤ r ∧
    ε < |Nhat κ ρL ρR W VL VR r ω - Nhat κ ρL ρR W VL VR s ω|} with hBad
  -- `Bad` lies in the `liminf` of the oscillation events
  have hsub : ∀ s : ℕ, Bad ⊆ ⋃ N : ℕ, ⋂ n ∈ Ici N, E n s := by
    intro s ω hω
    obtain ⟨hωG, hζ, hall⟩ := hω
    obtain ⟨r, hsr, hgt⟩ := hall s
    have hrζ : (r : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
    obtain ⟨n₀, hn₀⟩ := exists_forall_le_angLoc (hgood ω hωG) hgood hωG (hTm ω) hrζ
    refine mem_iUnion.2 ⟨max n₀ ⌈(r : ℝ)⌉₊, mem_iInter₂.2 fun n hn => ?_⟩
    have hn' : max n₀ ⌈(r : ℝ)⌉₊ ≤ n := hn
    have hrσ : r ≤ angLoc G T W VL VR B ζ n ω := hn₀ n ((le_max_left _ _).trans hn')
    have hrn : r ≤ (n : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact (Nat.le_ceil (r : ℝ)).trans (by exact_mod_cast (le_max_right _ _).trans hn')
    have hb := abs_bandN_le hκ hE hGc hgood hx hK' hK'' n
    have hbdd : BddAbove (range fun i : Set.Iic (n : ℝ≥0) => ‖1 * (bandN κ xL xR ρL ρR G T W VL VR B ζ n i ω -
        bandN κ xL xR ρL ρR G T W VL VR B ζ n (min (i : ℝ≥0) (s : ℝ≥0)) ω)‖) := by
      refine ⟨2 * (1 + bandKc κ xL xR ρL ρR K' K'' n), forall_mem_range.2 fun i => ?_⟩
      rw [one_mul, Real.norm_eq_abs]
      have h1 := hb i ω
      have h2 := hb (min (i : ℝ≥0) (s : ℝ≥0)) ω
      exact (abs_sub _ _).trans (by linarith)
    show ε ≤ _
    refine le_trans ?_ (le_ciSup hbdd ⟨r, hrn⟩)
    simp only [one_mul, Real.norm_eq_abs, min_eq_right hsr]
    rw [bandN_eq_Nhat hgood hωG hrσ, bandN_eq_Nhat hgood hωG (hsr.trans hrσ)]
    exact hgt.le
  -- the bound for each `s` and `δ`
  have hkey : ∀ s : ℕ, ∀ δ : ℝ, 0 < δ → P Bad ≤ ENNReal.ofReal ((δ / 2 + κ * K' ^ 2 *
      (∫⁻ ω, clockTail xL xR G T W VL VR B ζ s ω ∂P).toReal / (2 * δ)) / ε) := by
    intro s δ hδ
    have hmono : Monotone fun N : ℕ => ⋂ n ∈ Ici N, E n s := fun N N' hNN' =>
      biInter_subset_biInter_left fun n hn => le_trans hNN' hn
    refine (measure_mono (hsub s)).trans ?_
    rw [hmono.measure_iUnion]
    refine iSup_le fun N => (measure_mono (biInter_subset_of_mem (mem_Ici.2 le_rfl))).trans ?_
    have hosc := measureReal_osc_le hκ hE hGm hGc hgood hT hx hK' hK'' N (s : ℝ≥0) (ε := ε) hδ
    have hRint : ∫ ω, clockR xL xR G T W VL VR B ζ N s ω ∂P ≤
        (∫⁻ ω, clockTail xL xR G T W VL VR B ζ s ω ∂P).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (clockR_nonneg hgood hx N s))
        (measurable_clockR hE hGm hGc hgood hT hx N s).aestronglyMeasurable]
      refine ENNReal.toReal_mono (ne_top_of_le_ne_top hTotfin
        (lintegral_mono fun ω => clockTail_le s ω)) (lintegral_mono fun ω => ?_)
      exact le_iSup (fun n => ENNReal.ofReal (clockR xL xR G T W VL VR B ζ n (s : ℝ≥0) ω)) N
    have hreal : P.real (E N s) ≤ (δ / 2 + κ * K' ^ 2 *
        (∫⁻ ω, clockTail xL xR G T W VL VR B ζ s ω ∂P).toReal / (2 * δ)) / ε := by
      rw [le_div_iff₀ hε, mul_comm]
      refine hosc.trans ?_
      gcongr
    rw [← ofReal_measureReal (measure_ne_top P (E N s))]
    exact ENNReal.ofReal_le_ofReal hreal
  -- conclude: `P Bad = 0`
  have hzero : P Bad = 0 := by
    have hbound : ∀ m : ℕ, P Bad ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
      intro m
      set η : ℝ := 1 / ((m : ℝ) + 1)
      have hη : 0 < η := by positivity
      set δ : ℝ := η * ε
      have hδ : 0 < δ := by positivity
      set c : ℝ := η * δ * ε / (κ * K' ^ 2 + 1)
      have hc : 0 < c := by positivity
      obtain ⟨s, hs⟩ := (hlimR.eventually (gt_mem_nhds hc)).exists
      refine (hkey s δ hδ).trans (ENNReal.ofReal_le_ofReal ?_)
      set x := (∫⁻ ω, clockTail xL xR G T W VL VR B ζ s ω ∂P).toReal
      have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
      have hκK : 0 ≤ κ * K' ^ 2 := by positivity
      have h1 : κ * K' ^ 2 * x ≤ η * δ * ε := by
        have : κ * K' ^ 2 * x ≤ (κ * K' ^ 2 + 1) * c := by nlinarith
        calc κ * K' ^ 2 * x ≤ (κ * K' ^ 2 + 1) * c := this
          _ = η * δ * ε := by simp only [c]; field_simp
      rw [div_le_iff₀ hε]
      have h2 : κ * K' ^ 2 * x / (2 * δ) ≤ η * ε / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have h3 : δ / 2 = η * ε / 2 := rfl
      linarith
    have hlim0 : Tendsto (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this
    exact le_antisymm (ge_of_tendsto' hlim0 hbound) bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with ω hω hωG hζ
  by_contra hcon
  push Not at hcon
  exact hω ⟨hωG, hζ, fun s => by
    obtain ⟨r, hr, hlt⟩ := hcon s
    exact ⟨r, hr, hlt⟩⟩

end Cauchy

/-! ### Pathwise: a Cauchy band process gives an eventual band -/

section Pathwise

variable {Ω : Type*} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **A Cauchy band process gives an eventual band.** On a path with infinite lifetime and a finite angular clock,
if `N̂ = h(U) − ∫ itoGen h(U)` is Cauchy at infinity, then eventually `D < 4(V^{R,0} − W)` or eventually
`D < 4(W − V^{L,0})`. -/
theorem eventually_band_of_cauchy (hκ : 0 < κ) (hx : 0 < xR 0 - xL 0) {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω))
    (hζ : ζ ω = ⊤)
    (hcau : ∀ k : ℕ, ∃ s : ℕ, ∀ r : ℝ≥0, (s : ℝ≥0) ≤ r →
      |Nhat κ ρL ρR W VL VR r ω - Nhat κ ρL ρR W VL VR s ω| ≤ 1 / ((k : ℝ) + 1))
    (hclock : ∃ M : ℝ, ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤ M) :
    (∃ T₀ : ℝ≥0, ∀ t, T₀ ≤ t → VR 0 t ω - VL 0 t ω < 4 * (VR 0 t ω - W t ω)) ∨
      (∃ T₀ : ℝ≥0, ∀ t, T₀ ≤ t → VR 0 t ω - VL 0 t ω < 4 * (W t ω - VL 0 t ω)) := by
  obtain ⟨K', hK'0, hK'⟩ := exists_bound_hB'
  obtain ⟨K'', hK''0, hK''⟩ := exists_bound_hB''
  obtain ⟨M, hM⟩ := hclock
  have hF := hp.isForcePath
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζ]; exact ENNReal.coe_lt_top
  set C₁ := bandC₁ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) K' K''
  set C₂ := K' / (xR 0 - xL 0)
  have hC₁ : 0 ≤ C₁ := by simp only [C₁, bandC₁]; positivity
  have hC₂ : 0 ≤ C₂ := div_nonneg hK'0 hx.le
  set g : ℝ → ℝ := fun u => C₁ * (VR 0 u.toNNReal ω - VL 0 u.toNNReal ω)⁻¹ ^ 2 +
    C₂ * errAbs ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) u with hgdef
  set f : ℝ → ℝ := genExpr κ ρL ρR hB' hB'' (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) with hfdef
  have hgi : ∀ t : ℝ≥0, IntervalIntegrable g volume 0 t := fun t =>
    ((intervalIntegrable_clockRate hp hx (hlt t)).const_mul C₁).add
      ((intervalIntegrable_errAbs hp (hlt t)).const_mul C₂)
  have hfi : ∀ t : ℝ≥0, IntervalIntegrable f volume 0 t := fun t =>
    intervalIntegrable_genExpr hp hx continuous_hB' continuous_hB'' (hlt t)
  -- the a.e. bound `|f| ≤ g`
  have hfg : ∀ t : ℝ≥0, ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Icc (0 : ℝ) t → |f u| ≤ g u := by
    intro t
    filter_upwards [ae_not_collision hF (hlt t), Measure.ae_ne volume 0] with u hu hu0 huI
    obtain ⟨hL, hR⟩ := hu ⟨lt_of_le_of_ne huI.1 (Ne.symm hu0), huI.2⟩
    have huζ := Sec2.toNNReal_lt_of_mem_Icc (hlt t) huI
    exact abs_genExpr_hB_le hp hκ.le hx hK' hK'' huζ (lt_of_le_of_ne (hF.vL_le_w huζ 0) (hL 0))
      (lt_of_le_of_ne (hF.w_le_vR huζ 0) (Ne.symm (hR 0)))
  set Fg : ℝ≥0 → ℝ := fun t => ∫ u in (0 : ℝ)..t, g u with hFgdef
  -- increments of `Fg`, and the bound for `Ihat`
  have hinc : ∀ t' t : ℝ≥0, t' ≤ t →
      |Ihat κ ρL ρR W VL VR t ω - Ihat κ ρL ρR W VL VR t' ω| ≤ Fg t - Fg t' := by
    intro t' t htt
    have htt' : (t' : ℝ) ≤ t := by exact_mod_cast htt
    have e1 : Ihat κ ρL ρR W VL VR t ω - Ihat κ ρL ρR W VL VR t' ω = ∫ u in (t' : ℝ)..t, f u :=
      intervalIntegral.integral_interval_sub_left (hfi t) (hfi t')
    have e2 : Fg t - Fg t' = ∫ u in (t' : ℝ)..t, g u :=
      intervalIntegral.integral_interval_sub_left (hgi t) (hgi t')
    have hsub : uIcc (t' : ℝ) t ⊆ uIcc 0 (t : ℝ) := by
      rw [uIcc_of_le htt', uIcc_of_le t.coe_nonneg]; exact Icc_subset_Icc_right le_rfl |>.trans
        (Icc_subset_Icc t'.coe_nonneg le_rfl)
    rw [e1, e2]
    refine (intervalIntegral.abs_integral_le_integral_abs htt').trans ?_
    refine intervalIntegral.integral_mono_ae_restrict htt' ((hfi t).mono_set hsub).abs ((hgi t).mono_set hsub) ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hfg t] with u hu huI
    exact hu ⟨t'.coe_nonneg.trans huI.1, huI.2⟩
  have hmono : Monotone Fg := fun t' t htt => by
    have := (abs_nonneg _).trans (hinc t' t htt)
    linarith
  -- `Fg` is bounded
  have hbdd : BddAbove (range Fg) := by
    refine ⟨C₁ * M + C₂ * errK xL xR ρL ρR, forall_mem_range.2 fun t => ?_⟩
    simp only [hFgdef, hgdef]
    rw [intervalIntegral.integral_add ((intervalIntegrable_clockRate hp hx (hlt t)).const_mul C₁)
      ((intervalIntegrable_errAbs hp (hlt t)).const_mul C₂), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hM t) hC₁)
      (mul_le_mul_of_nonneg_left (integral_errAbs_le hp (hlt t)) hC₂)
  obtain ⟨s₀, hs₀⟩ := exists_lt_of_lt_ciSup (show (⨆ t, Fg t) - 1 / 4 < ⨆ t, Fg t by linarith)
  obtain ⟨s₁, hs₁⟩ := hcau 3
  set S : ℝ≥0 := max s₀ (s₁ : ℝ≥0)
  have hosc : ∀ t' t : ℝ≥0, S ≤ t' → t' ≤ t →
      |hB (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t) -
        hB (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t')| < 1 := by
    intro t' t hSt' htt
    have hs₀t' : s₀ ≤ t' := (le_max_left _ _).trans hSt'
    have hs₁t' : (s₁ : ℝ≥0) ≤ t' := (le_max_right _ _).trans hSt'
    have h1 := hs₁ t (hs₁t'.trans htt)
    have h2 := hs₁ t' hs₁t'
    have h3 := hinc t' t htt
    have h4 : Fg t - Fg t' < 1 / 4 := by
      have := le_ciSup hbdd t
      have := hmono hs₀t'
      linarith
    norm_num at h1 h2
    have e : ∀ r : ℝ≥0, hB (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r) =
        Nhat κ ρL ρR W VL VR r ω + Ihat κ ρL ρR W VL VR r ω := fun r => by simp only [Nhat]; ring
    rw [e, e]
    have := abs_sub_le (Nhat κ ρL ρR W VL VR t ω) (Nhat κ ρL ρR W VL VR s₁ ω) (Nhat κ ρL ρR W VL VR t' ω)
    rw [abs_sub_comm (Nhat κ ρL ρR W VL VR s₁ ω)] at this
    calc |Nhat κ ρL ρR W VL VR t ω + Ihat κ ρL ρR W VL VR t ω -
          (Nhat κ ρL ρR W VL VR t' ω + Ihat κ ρL ρR W VL VR t' ω)|
        ≤ |Nhat κ ρL ρR W VL VR t ω - Nhat κ ρL ρR W VL VR t' ω| +
            |Ihat κ ρL ρR W VL VR t ω - Ihat κ ρL ρR W VL VR t' ω| := by
          rw [show Nhat κ ρL ρR W VL VR t ω + Ihat κ ρL ρR W VL VR t ω -
            (Nhat κ ρL ρR W VL VR t' ω + Ihat κ ρL ρR W VL VR t' ω) =
            (Nhat κ ρL ρR W VL VR t ω - Nhat κ ρL ρR W VL VR t' ω) +
            (Ihat κ ρL ρR W VL VR t ω - Ihat κ ρL ρR W VL VR t' ω) by ring]
          exact abs_add_le _ _
      _ < 1 := by linarith
  -- the band
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hR, hL⟩ := hcon
  push Not at hR hL
  obtain ⟨t₁, ht₁, h₁⟩ := hR S
  obtain ⟨t₂, ht₂, h₂⟩ := hL S
  have hD : ∀ t : ℝ≥0, 0 < gapAt (fun i t => VL i t ω) (fun j t => VR j t ω) t := fun t =>
    hx.trans_le (le_gapAt hp (hlt t))
  have hU₁ : hB (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t₁) = 1 := by
    refine hB_eq_one ?_
    have hd := hD t₁
    simp only [angAt, gapAt] at hd ⊢
    rw [le_div_iff₀ hd]
    linarith
  have hU₂ : hB (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t₂) = 0 := by
    refine hB_eq_zero ?_
    have hd := hD t₂
    simp only [angAt, gapAt] at hd ⊢
    rw [div_le_iff₀ hd]
    linarith
  rcases le_total t₁ t₂ with h | h
  · have := hosc t₁ t₂ ht₁ h
    rw [hU₁, hU₂] at this; norm_num at this
  · have := hosc t₂ t₁ ht₂ h
    rw [hU₁, hU₂] at this; norm_num at this

end Pathwise

/-! ### Assembly -/

section Assembly

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Aux. lemma 106's finitely many band switches** (Specification p. 354): for `κ > 0` and an evolution of a
separated word with a side total at most `−2`, almost surely on `{ζ = ∞}` the driver eventually stays at distance more
than `D/4` from the nearest right mark, or eventually from the nearest left mark. -/
theorem ae_eventually_band (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hsep : ∀ i j, xL i < xR j) (hab : (∑ i, ρL i) ≤ -2 ∨ (∑ j, ρR j) ≤ -2) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ →
      (∃ T₀ : ℝ≥0, ∀ t, T₀ ≤ t → VR 0 t ω - VL 0 t ω < 4 * (VR 0 t ω - W t ω)) ∨
        (∃ T₀ : ℝ≥0, ∀ t, T₀ ≤ t → VR 0 t ω - VL 0 t ω < 4 * (W t ω - VL 0 t ω)) := by
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · filter_upwards [ae_ne_top_of_thresholdCondition hE hthr] with ω hω hζ
    exact absurd hζ hω
  obtain ⟨T, G, hT, hGm, hGc, hgood⟩ := exists_setup hκ hE hthr
  have hx : 0 < xR 0 - xL 0 := sub_pos.2 (hsep 0 0)
  have hcau := ae_all_iff.2 fun k => ae_nhat_cauchy hκ hE hGm hGc hgood hT hx hab k
  have hclock := ae_bddAbove_clock hκ hE hsep hab
  filter_upwards [hcau, hclock, measure_eq_zero_iff_ae_notMem.1 hGc] with ω hc hcl hωG' hζ
  have hωG : ω ∈ G := by simpa using hωG'
  exact eventually_band_of_cauchy hκ hx (hgood ω hωG).1 hζ (fun k => hc k hωG hζ) (hcl hζ)

end Assembly

end Clock

/-- **`Sec7.Aux102BandStatement` is proved** (Aux. lemma 102 with the finitely many band switches of Aux. lemma 106,
Specification pp. 348 and 354): `Clock.ae_bddAbove_clock` and `Clock.ae_eventually_band`. -/
theorem aux102BandStatement : Aux102BandStatement.{u} := by
  intro κ hκ nL nR xL xR ρL ρR _ hsep hab Ω mΩ P _ 𝓕 W VL VR B ζ hE
  filter_upwards [Clock.ae_bddAbove_clock hκ hE hsep hab, Clock.ae_eventually_band hκ hE hsep hab]
    with ω h1 h2 hζ
  exact ⟨h1 hζ, h2 hζ⟩

/-- **Aux. lemma 106's transience without the Aux. 102 input**: `aux106TransienceStatement_of_inputs` with
`aux102BandStatement`. -/
theorem aux106TransienceStatement_of_aux102' (hex : ExistsEvolutionStatement)
    (h1 : SeedOneForceTraceStatement.{u}) (h99 : Aux99Statement.{u})
    (hpos : Aux106PositiveStatement.{u}) : Aux106TransienceStatement.{u} :=
  aux106TransienceStatement_of_inputs hex h1 h99 aux102BandStatement hpos

end Sec7

end InteractingSLE
