/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftHeightRs
import InteractingSLE.Spec.Zhan.ConstDriftKoebe
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# Terminal cluster points on the lower line

Packet PROVE-ZHAN-A7. The strict inequality `mm_eq_zero_or_pi` leaves the minimal height `0`: a terminal cluster
point on the lower line `ℝ` of the strip, i.e. on `(−1, ∞)` in the chordal chart. Here, for a real point `z₀ ∈ (−1, ∞) ∖ {0}`
that is never swallowed during the strip life (`hal`), the restart at the strip time `n` sees `z₀` at the strip
coordinate `log((y − v)/(w − v))` (`y` the real flow of `z₀`), whose absolute value is at least `n − |ξ_n|`: `y − v`
increases if `z₀ > 0`, and `log(y − v) + 2 t(s)` decreases if `z₀ < 0` (in strip time the lower gap moves at speed
`|1 + 2(w − v)/(y − w)| ≥ 1`). The restart's trace is horizontally bounded by its own sublinearity constant, so
(`sub_abs_drv_le`) `n − |ξ_n| ≤ csub(θ_n f) + R` for every `n ≥ 1`, an event of probability zero.

* `exists_lower_cluster`: `mm f = 0` gives a cluster point on `(−1, ∞)` along rational strip times;
* `sub_abs_drv_le`: the bound above.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMapInv fwdMap fwdHull IsForwardSol)
open QuantumZipper.RS (CPath)

namespace InteractingSLE

namespace Zhan

namespace HeightLaw

open Strip Retarget

variable {κ σ : ℝ} {f : CPath} {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem mem_hullSet_abs_log {X : ℝ} {z : ℂ} (hz : z ∈ hullSet X) : |Real.log ‖1 + z‖| ≤ X := by
  have hpos : 0 < ‖1 + z‖ := (Real.exp_pos _).trans_le hz.2.1
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) hz.2.1
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_log hpos hz.2.2
    rwa [Real.log_exp] at this

/-- **A cluster point on the lower line.** If `mm f = 0`, there are rational strip times `q_k ≥ k` along which the
trace converges to a real point `z₀ > −1`. -/
theorem exists_lower_cluster (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) (hm : mm κ σ f = 0) :
    ∃ z0 : ℝ, -1 < z0 ∧ ∃ q : ℕ → ℚ, (∀ k : ℕ, (k : ℚ) ≤ q k) ∧
      Tendsto (fun k => η (chordT w v ((q k : ℝ)).toNNReal)) atTop (𝓝 (z0 : ℂ)) := by
  have hhgt : ∀ t, 0 ≤ t → hgt κ σ f t ∈ Icc 0 Real.pi := fun t ht => hgt_mem_Icc_zero_pi hσ hf h hη ht
  have hseq : ∀ k : ℕ, ∃ q : ℚ, (k : ℚ) ≤ q ∧ hgt κ σ f q < 1 / ((k : ℝ) + 1) := fun k =>
    frequently_lt_of_limInfTopQ_lt hhgt (by
      rw [show limInfTopQ (hgt κ σ f) = mm κ σ f from rfl, hm]; positivity) k
  choose q hqk hqm using hseq
  have hq0 : ∀ k : ℕ, (0 : ℝ) ≤ q k := fun k => by
    have := hqk k; exact_mod_cast (Nat.cast_nonneg k).trans this
  set z : ℕ → ℂ := fun k => η (chordT w v ((q k : ℝ)).toNNReal) with hz
  have hzS : ∀ k, z k ∈ hullSet (csub κ σ (slope σ) f + hullR σ) := fun k =>
    mem_hullSet hσ hf h hη (h.1.chordT_spec _).1
  obtain ⟨z0', hz0S, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (isBounded_hullSet _) hzS
  rw [(isClosed_hullSet _).closure_eq] at hz0S
  have hne := one_add_ne_zero_of_mem_hullSet hz0S
  have harg := tendsto_arg_one_add hlim hne fun k => (hzS (φ k)).1
  have harg0 : arg (1 + z0') = 0 := by
    have hup : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    refine le_antisymm (le_of_tendsto_of_tendsto' harg hup fun k => ?_)
      (Complex.arg_nonneg_iff.2 (by have := hz0S.1; simp only [add_im, one_im, zero_add]; exact this))
    have h1 := hqm (φ k)
    rw [hgt_eq hσ hf h hη (hq0 _)] at h1
    exact h1.le
  obtain ⟨hre, him⟩ := Complex.arg_eq_zero_iff.1 harg0
  have hz0' : z0' = (z0'.re : ℂ) := Complex.ext rfl (by simp only [add_im, one_im, zero_add] at him; simp [him])
  have hre' : -1 < z0'.re := by
    rcases hre.lt_or_eq with hlt | heq
    · simp only [add_re, one_re] at hlt; linarith
    · exfalso; apply hne; exact Complex.ext (by simpa using heq.symm) (by simpa using him)
  refine ⟨z0'.re, hre', fun k => q (φ k), fun (k : ℕ) => ?_, by rw [← hz0']; exact hlim⟩
  exact (show (k : ℚ) ≤ (φ k : ℚ) by exact_mod_cast hφ.id_le k).trans (hqk (φ k))

/-- Points `v + i/(k+1)` approach a real point inside `ℍ`, so `𝓝[ℍ] v` is not trivial. -/
theorem neBot_nhdsWithin_H (x : ℝ) : (𝓝[H] (x : ℂ)).NeBot := by
  have h : Tendsto (fun k : ℕ => (x : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 (x : ℂ)) := by
    have h1 := ((Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
    simpa using (tendsto_const_nhds (x := (x : ℂ))).add h1
  refine mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_of_tendsto h (Eventually.of_forall fun k => ?_))
  show 0 < ((x : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I).im
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add]
  positivity

/-- **A lower cluster point is far away in the restart.** If a real point `z₀ ∈ (−1, ∞) ∖ {0}` is never swallowed
during the strip life and the trace converges to `z₀` along rational strip times `q_k ≥ k`, then for every `n ≥ 1`,
`n − |ξ_n| ≤ csub(θ_n f) + R`. -/
theorem sub_abs_drv_le (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η)
    (hal : ∀ x : ℝ, -1 < x → x ≠ 0 → ∀ s : ℝ≥0, IsStripLife w v ζ s →
      ∃ u : ℝ → ℂ, IsForwardSol (extPath w) (x : ℂ) s u)
    {z0 : ℝ} (hz0 : -1 < z0) (hz00 : z0 ≠ 0) {q : ℕ → ℚ} (hq : ∀ k : ℕ, (k : ℚ) ≤ q k)
    (hlim : Tendsto (fun k => η (chordT w v ((q k : ℝ)).toNNReal)) atTop (𝓝 (z0 : ℂ))) {n : ℕ} (_hn : 0 < n) :
    (n : ℝ) - |drv κ σ f n| ≤ csub κ σ (slope σ) (shiftPath n f) + hullR σ := by
  have hR := hasStripDriver_rs h (n : ℝ≥0)
  have hfR := tendsto_shiftPath hf (n : ℝ≥0)
  have hηR := isGeneratingTrace_rsTrace h hη (n : ℝ≥0)
  set a := chordT w v n with ha_def
  have hal_a := (h.1.chordT_spec (n : ℝ≥0)).1
  obtain ⟨s', has', hs'⟩ := h.1.exists_gt hal_a
  set g := qq κ σ f n with hgdef
  have hg : 0 < g := qq_pos f n
  have hgn : qq κ σ f ((n : ℝ≥0) : ℝ) = g := by rw [hgdef]; simp
  have hw0 : w 0 = 0 := h.1.1
  have h₁ : Sec7.IsGeneratingTraceIcc w a η := Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hη s' hs')
    (h.1.continuousOn_lt hs') hw0 (ENNReal.coe_lt_coe.2 has')
  have hfc : Continuous (frozenDrive w s') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.1.continuousOn_le hs')
  have hW0' : frozenDrive w s' 0 = 0 := by rw [frozenDrive_zero (NNReal.coe_nonneg s'), hw0]
  obtain ⟨-, -, hFeq, hFc, -, -, -⟩ := h₁.extend_props (t₂ := (s' : ℝ)) (NNReal.coe_lt_coe.2 has') hfc hw0
  set F := extendFrom H (fwdMapInv (frozenDrive w s') a) with hFdef
  -- the restarted trace points, from the index `n` on
  have hqk' : ∀ k : ℕ, (k : ℝ) + n ≤ q (k + n) := fun k => by have := hq (k + n); exact_mod_cast this
  have hq0 : ∀ k : ℕ, (0 : ℝ) ≤ q (k + n) := fun k => by
    linarith [hqk' k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set τ : ℕ → ℝ≥0 := fun k => ((q (k + n) : ℝ) - n).toNNReal with hτ
  have hτk : ∀ k : ℕ, (τ k : ℝ) = (q (k + n) : ℝ) - n := fun k =>
    Real.coe_toNNReal _ (by linarith [hqk' k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hqτ : ∀ k : ℕ, ((q (k + n) : ℝ)).toNNReal = (n : ℝ≥0) + τ k := fun k => by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (hq0 k), NNReal.coe_add, hτk]
    simp
  set p : ℕ → ℂ := fun k => rsTrace w v n (chordT (rsW w v n) (rsV w v n) (τ k)) with hp
  have hjoin : ∀ k, η (chordT w v ((q (k + n) : ℝ)).toNNReal) = F ((g : ℂ) * p k) := fun k => by
    rw [hqτ k, trace_chordT_add_eq h hη n hs' has' (τ k), hgn]
  have hpS : ∀ k, p k ∈ hullSet (csub κ σ (slope σ) (shiftPath n f) + hullR σ) := fun k =>
    mem_hullSet hσ hfR hR hηR ((hR.1.chordT_spec (τ k)).1)
  obtain ⟨p0, hp0S, φ, hφ, hplim⟩ := tendsto_subseq_of_bounded (isBounded_hullSet _) hpS
  rw [(isClosed_hullSet _).closure_eq] at hp0S
  -- `F(g p₀) = z₀`
  have hgp0 : (g : ℂ) * p0 ∈ Hbar := by
    show 0 ≤ ((g : ℂ) * p0).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hg.le hp0S.1
  have hgpk : ∀ k, (g : ℂ) * p k ∈ Hbar := fun k => by
    show 0 ≤ ((g : ℂ) * p k).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hg.le (hpS k).1
  have hzlim : Tendsto (fun k => F ((g : ℂ) * p (φ k))) atTop (𝓝 (F ((g : ℂ) * p0))) :=
    (hFc _ hgp0).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.mul hplim, Eventually.of_forall fun k => hgpk (φ k)⟩)
  have hzlim2 : Tendsto (fun k => F ((g : ℂ) * p (φ k))) atTop (𝓝 (z0 : ℂ)) := by
    have := hlim.comp ((tendsto_add_atTop_nat n).comp hφ.tendsto_atTop)
    refine this.congr fun k => ?_
    simp only [Function.comp_apply]
    exact hjoin (φ k)
  have hFz0 : F ((g : ℂ) * p0) = z0 := tendsto_nhds_unique hzlim hzlim2
  -- `g p₀` is real
  have hpim : p0.im = 0 := by
    by_contra hne
    have hpos : 0 < p0.im := lt_of_le_of_ne hp0S.1 (Ne.symm hne)
    have hgH : (g : ℂ) * p0 ∈ H := by
      show 0 < ((g : ℂ) * p0).im
      rw [Complex.im_ofReal_mul]
      exact mul_pos hg hpos
    have := QuantumZipper.RS.fwdMapInv_mem_H hfc hW0' (NNReal.coe_nonneg a) hgH
    rw [← hFeq hgH, hFz0] at this
    have h3 : (0 : ℝ) < ((z0 : ℂ)).im := this
    simp at h3
  -- the flow of `z₀`
  obtain ⟨u, hu⟩ := hal z0 hz0 hz00 a hal_a
  have hrs : ∀ r ∈ Icc (0 : ℝ) a, extPath w r = frozenDrive w s' r := fun r hr =>
    (frozenDrive_eq ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.2 has'.le)⟩).symm
  have huf : IsForwardSol (frozenDrive w s') (z0 : ℂ) a u := QuantumZipper.isForwardSol_congr_drive hrs hu
  -- `g p₀` is the image of `z₀` under the forward map
  have hgpu : (g : ℂ) * p0 = u a := by
    have hreal : (g : ℂ) * p0 = ((g * p0.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hpim]
    have h1 : Tendsto F (𝓝[H] ((g : ℂ) * p0)) (𝓝[H] (z0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun x hx => ?_⟩
      · rw [← hFz0]
        exact (hFc _ hgp0).tendsto.mono_left (nhdsWithin_mono _ fun z hz => show 0 ≤ z.im from le_of_lt hz)
      · rw [hFeq hx]
        exact QuantumZipper.RS.fwdMapInv_mem_H hfc hW0' (NNReal.coe_nonneg a) hx
    have h2 := tendsto_fwdMap_of_isForwardSol_real hfc hW0' (NNReal.coe_nonneg a) huf
    have h4 : Tendsto (fun x => x) (𝓝[H] ((g : ℂ) * p0)) (𝓝 (u a)) := by
      refine (h2.comp h1).congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
      simp only [Function.comp_apply]
      rw [hFeq hx]
      exact QuantumZipper.RS.fwdMap_fwdMapInv hfc hW0' (NNReal.coe_nonneg a) hx
    rw [hreal] at h4 ⊢
    have := neBot_nhdsWithin_H (g * p0.re)
    exact tendsto_nhds_unique (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) h4
  -- the real point path `y = Re u + w` in chordal time
  have hm := h.1.2.1 a hal_a
  have hu_im : ∀ s ∈ Icc (0 : ℝ) a, (u s).im = 0 := fun s hs => im_eq_zero_of_isForwardSol_real hfc huf hs
  have hu_ne : ∀ s ∈ Icc (0 : ℝ) a, (u s).re ≠ 0 := fun s hs h0 =>
    (hu.2 s hs).1 (Complex.ext h0 (hu_im s hs))
  have hureal : ∀ s ∈ Icc (0 : ℝ) a, u s = ((u s).re : ℂ) := fun s hs => Complex.ext rfl (by simp [hu_im s hs])
  have huc : ContinuousOn (fun s => (u s).re) (Icc 0 a) := Complex.continuous_re.comp_continuousOn hu.1
  set y : ℝ → ℝ := fun s => (u s).re + extPath w s with hy
  have hyc : ContinuousOn y (Icc 0 a) := huc.add hm.continuousOn_w
  have hyw : ∀ s, y s - extPath w s = (u s).re := fun s => by simp [hy]
  have hint : IntervalIntegrable (fun r => 2 / (y r - extPath w r)) volume 0 a := by
    refine ContinuousOn.intervalIntegrable_of_Icc (NNReal.coe_nonneg a) ?_
    refine ContinuousOn.congr (f := fun s => 2 / (u s).re)
      ((continuousOn_const (c := (2 : ℝ))).div huc hu_ne) fun r _ => ?_
    show 2 / (y r - extPath w r) = 2 / (u r).re
    rw [hyw]
  have hyeq : ∀ s ∈ Icc (0 : ℝ) a, y s = z0 + ∫ r in (0 : ℝ)..s, 2 / (y r - extPath w r) := by
    intro s hs
    have h1 := (hu.2 s hs).2
    have hci : ∫ r in (0 : ℝ)..s, (2 : ℂ) / u r = ((∫ r in (0 : ℝ)..s, 2 / (u r).re : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      have hr' : r ∈ Icc (0 : ℝ) a := ⟨hr.1, hr.2.trans hs.2⟩
      rw [hureal r hr']
      push_cast
      rfl
    rw [hci] at h1
    have h2 := congrArg Complex.re h1
    simp only [add_re, sub_re, ofReal_re] at h2
    have h3 : ∫ r in (0 : ℝ)..s, 2 / (y r - extPath w r) = ∫ r in (0 : ℝ)..s, 2 / (u r).re := by
      refine intervalIntegral.integral_congr fun r _ => ?_
      show 2 / (y r - extPath w r) = 2 / (u r).re
      rw [hyw]
    rw [h3]
    show (u s).re + extPath w s = _
    rw [h2]
    ring
  have hu0 : (u 0).re = z0 := by
    have := hyeq 0 ⟨le_rfl, NNReal.coe_nonneg a⟩
    simp only [intervalIntegral.integral_same, add_zero, hy, extPath, Real.toNNReal_zero, hw0] at this
    linarith
  have hgap : extPath w a - extPath v a = g := by
    have := rsGap_eq h (n : ℝ≥0)
    rw [rsGap, hgn] at this
    rw [extPath_coe, extPath_coe]
    exact this
  -- the strip coordinate of `p₀`
  have hp0re : p0 = ((((u a).re + g) / g - 1 : ℝ) : ℂ) := by
    apply Complex.ext
    · have := congrArg Complex.re hgpu
      simp only [Complex.re_ofReal_mul] at this
      simp only [ofReal_re]
      field_simp
      linarith
    · simp [hpim]
  -- the order of the real flows: `v < y`
  have hend := h.1.isForwardSol_end hs' has'.le
  have hyv : ∀ s ∈ Icc (0 : ℝ) a, extPath v s < y s := fun s hs => by
    have := flow_re_lt_flow_re hfc hend huf hz0 hs
    simp only [ofReal_re] at this
    simp only [hy]
    linarith
  have ha0 : (a : ℝ) ∈ Icc (0 : ℝ) a := ⟨NNReal.coe_nonneg a, le_rfl⟩
  have hya : 0 < y a - extPath v a := sub_pos.2 (hyv a ha0)
  have hlog1p : Real.log ‖1 + p0‖ = Real.log (y a - extPath v a) - Real.log g := by
    have hya' : y a - extPath v a = (u a).re + g := by
      have : y a = (u a).re + extPath w a := rfl
      rw [this]
      linarith [hgap]
    have e1 : 1 + (((u a).re + g) / g - 1) = (y a - extPath v a) / g := by rw [hya']; ring
    have e : (1 : ℂ) + p0 = (((y a - extPath v a) / g : ℝ) : ℂ) := by
      rw [hp0re, ← e1]
      push_cast
      ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (div_pos hya hg).le, Real.log_div hya.ne' hg.ne']
  have hlogg : Real.log g = drv κ σ f n - n := by rw [hgdef, qq, Real.log_exp]
  have hbound := mem_hullSet_abs_log hp0S
  have hy0 : y 0 - extPath v 0 = 1 + z0 := by
    have hv0 := hm.v_zero
    have hw0' : extPath w 0 = 0 := by simp [extPath, hw0]
    have : y 0 = (u 0).re + extPath w 0 := rfl
    rw [this, hv0, hw0', hu0]
    ring
  have hderiv_y : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt y (2 / (y x - extPath w x)) x := fun x hx =>
    hasDerivAt_of_eq_integral hm.continuousOn_w hyc hint hyeq hx (by
      intro hyx
      exact hu_ne x (Ioo_subset_Icc_self hx) (by rw [← hyw x, hyx, sub_self]))
  rcases lt_or_gt_of_ne hz00 with hneg | hpos
  · -- `z₀ < 0`: `log(y − v) + 2 t(s)` decreases
    have hun : ∀ s ∈ Icc (0 : ℝ) a, (u s).re < 0 := by
      intro s hs
      by_contra hge
      push Not at hge
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hs.1 (huc.mono (Icc_subset_Icc_right hs.2))
        ⟨by rw [hu0]; exact hneg.le, hge⟩
      exact hu_ne r ⟨hr.1, hr.2.trans hs.2⟩ hr0
    set χ : ℝ → ℝ := fun s => Real.log (y s - extPath v s) + 2 * stripClock (extPath w) (extPath v) s with hχ
    have hχc : ContinuousOn χ (Icc 0 a) :=
      ((hyc.sub hm.continuousOn_v).log fun s hs => (sub_pos.2 (hyv s hs)).ne').add
        (continuousOn_const.mul hm.continuousOn_stripClock)
    have hχd : ∀ x ∈ Ioo (0 : ℝ) a, HasDerivAt χ
        ((2 / (y x - extPath w x) - 2 / (extPath v x - extPath w x)) / (y x - extPath v x) +
          2 * ((extPath w x - extPath v x) ^ 2)⁻¹) x := fun x hx =>
      (((hderiv_y x hx).sub (hm.hasDerivAt_v hx)).log (sub_pos.2 (hyv x (Ioo_subset_Icc_self hx))).ne').add
        ((hm.hasDerivAt_stripClock hx).const_mul 2)
    have hanti : AntitoneOn χ (Icc 0 a) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) (a : ℝ)) hχc (fun x hx => ?_) fun x hx => ?_
      · rw [interior_Icc] at hx
        exact (hχd x hx).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hx
        rw [(hχd x hx).deriv]
        have hx' := Ioo_subset_Icc_self hx
        set d := (u x).re
        set A := extPath w x - extPath v x with hA
        have hd : d < 0 := hun x hx'
        have hA0 : 0 < A := sub_pos.2 (hm.lt x hx')
        have hyw' : y x - extPath w x = d := hyw x
        have hvw' : extPath v x - extPath w x = -A := by rw [hA]; ring
        have hyv' : y x - extPath v x = d + A := by rw [hA]; linarith [hyw']
        have hdA : 0 < d + A := by rw [← hyv']; exact sub_pos.2 (hyv x hx')
        rw [hyw', hvw', hyv']
        have hd0 : d ≠ 0 := hd.ne
        have hA0' : A ≠ 0 := hA0.ne'
        have hdA0 : d + A ≠ 0 := hdA.ne'
        have key : (2 / d - 2 / -A) / (d + A) + 2 * (A ^ 2)⁻¹ = 2 * (A + d) / (d * A ^ 2) := by
          field_simp
          ring
        rw [key]
        exact div_nonpos_iff.2 (Or.inl ⟨by linarith, by nlinarith [sq_nonneg A]⟩)
    have h1 := hanti ⟨le_rfl, NNReal.coe_nonneg a⟩ ha0 (NNReal.coe_nonneg a)
    have hclk : stripClock (extPath w) (extPath v) a = n := by
      have := (h.1.chordT_spec (n : ℝ≥0)).2.2
      rw [← ha_def] at this
      exact_mod_cast this
    simp only [hχ, hy0, stripClock, intervalIntegral.integral_same, mul_zero, add_zero] at h1
    rw [show ∫ u in (0 : ℝ)..(a : ℝ), ((extPath w u - extPath v u) ^ 2)⁻¹ = (n : ℝ) from hclk] at h1
    have hl : Real.log (1 + z0) < 0 := Real.log_neg (by linarith) (by linarith)
    have : Real.log ‖1 + p0‖ < -n - drv κ σ f n := by rw [hlog1p, hlogg]; linarith
    have habs := abs_le.1 hbound
    have := neg_abs_le (drv κ σ f n)
    rw [abs_le] at hbound
    linarith
  · -- `z₀ > 0`: `y − v` increases
    have hup : ∀ s ∈ Icc (0 : ℝ) a, 0 < (u s).re := by
      intro s hs
      by_contra hle
      push Not at hle
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hs.1 (huc.mono (Icc_subset_Icc_right hs.2))
        ⟨hle, by rw [hu0]; exact hpos.le⟩
      exact hu_ne r ⟨hr.1, hr.2.trans hs.2⟩ hr0
    have hmono : MonotoneOn (fun s => y s - extPath v s) (Icc 0 a) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (a : ℝ)) (hyc.sub hm.continuousOn_v) (fun x hx => ?_)
        fun x hx => ?_
      · rw [interior_Icc] at hx
        exact ((hderiv_y x hx).sub (hm.hasDerivAt_v hx)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hx
        rw [show (fun s => y s - extPath v s) = y - extPath v from rfl,
          ((hderiv_y x hx).sub (hm.hasDerivAt_v hx)).deriv]
        have hx' := Ioo_subset_Icc_self hx
        have h1 : 0 < 2 / (y x - extPath w x) := by rw [hyw x]; exact div_pos two_pos (hup x hx')
        have h2 : 2 / (extPath v x - extPath w x) < 0 := div_neg_of_pos_of_neg two_pos (sub_neg.2 (hm.lt x hx'))
        linarith
    have h1 := hmono ⟨le_rfl, NNReal.coe_nonneg a⟩ ha0 (NNReal.coe_nonneg a)
    simp only [hy0] at h1
    have hl : 0 < Real.log (y a - extPath v a) := Real.log_pos (by linarith)
    have : (n : ℝ) - drv κ σ f n < Real.log ‖1 + p0‖ := by rw [hlog1p, hlogg]; linarith
    have := le_abs_self (drv κ σ f n)
    rw [abs_le] at hbound
    linarith

/-- **Some positive rational strip time has a tip off the source.** -/
theorem exists_tip_ne_zero (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) :
    ∃ r : ℚ, 0 < r ∧ η (chordT w v ((r : ℝ)).toNNReal) ≠ 0 := by
  by_contra hall
  push Not at hall
  set a1 := chordT w v 1 with ha1
  have hl1 := (h.1.chordT_spec 1).1
  have ha1ss : (a1 : ℝ) = ss κ σ f 1 := by rw [ha1, coe_chordT_eq h]; simp
  have ha1pos : (0 : ℝ) < a1 := by
    rw [ha1ss]
    have := (isRate (κ := κ) (σ := σ) f zero_le_one).clk_lt ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ one_pos
    simpa [ss] using this
  have hssc : Continuous (ss κ σ f) := by
    unfold ss Retarget.clk
    exact continuous_iff_continuousAt.2 fun x =>
      (((continuous_rate f).integral_hasStrictDerivAt 0 x).hasDerivAt).continuousAt
  -- the trace along strip times in `[0, 1]`
  set g : ℝ → ℂ := fun t => η (ss κ σ f t).toNNReal with hg
  have hgc : ContinuousOn g (Icc 0 1) := by
    refine (hη a1 hl1).2.1.comp (continuous_real_toNNReal.comp hssc).continuousOn fun t ht => ?_
    show (((ss κ σ f t).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ a1
    refine ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 ?_)
    rw [ha1ss]
    exact ss_le_ss f ht.1 ht.2
  have hgq : ∀ q : ℚ, 0 < q → g q = 0 := fun q hq => by
    have := hall q hq
    rwa [show chordT w v ((q : ℝ)).toNNReal = (ss κ σ f q).toNNReal by
      apply NNReal.coe_injective
      rw [coe_chordT_eq h, Real.coe_toNNReal _ (ss_nonneg f (by exact_mod_cast hq.le)),
        Real.coe_toNNReal _ (by exact_mod_cast hq.le)]] at this
  have hg0 : ∀ t ∈ Icc (0 : ℝ) 1, g t = 0 := by
    intro t ht
    have hseq : ∀ k : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ 0 < q ∧ |(q : ℝ) - t| < 1 / ((k : ℝ) + 1) := by
      intro k
      rcases ht.2.lt_or_eq with hlt | heq
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < min 1 (t + 1 / ((k : ℝ) + 1)) from
          lt_min hlt (by have h1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := (by positivity); linarith))
        refine ⟨q, ⟨ht.1.trans hq1.le, hq2.le.trans (min_le_left _ _)⟩, by exact_mod_cast ht.1.trans_lt hq1, ?_⟩
        rw [abs_lt]; constructor <;> linarith [min_le_right 1 (t + 1 / ((k : ℝ) + 1)),
          (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity)]
      · refine ⟨1, by simp, one_pos, ?_⟩
        rw [heq]; simp; positivity
    choose q hqI hq0 hqd using hseq
    have hqt : Tendsto (fun k => (q k : ℝ)) atTop (𝓝[Icc 0 1] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hqI⟩
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun k => dist_nonneg) (fun k => (Real.dist_eq _ _ ▸ hqd k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have := (hgc t ht).tendsto.comp hqt
    exact tendsto_nhds_unique this (tendsto_const_nhds.congr fun k => (hgq (q k) (hq0 k)).symm)
  -- the hull at `a₁/2` would be empty
  set b : ℝ≥0 := a1 / 2 with hb
  have hb0 : (0 : ℝ) < b := by rw [hb, NNReal.coe_div]; push_cast; linarith
  have hba : b < a1 := by rw [hb]; exact NNReal.half_lt_self (by exact_mod_cast ha1pos.ne')
  have himg : η '' Icc 0 b = {0} := by
    ext z
    simp only [mem_image, mem_Icc, mem_singleton_iff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsl : IsStripLife w v ζ s := hl1.mono (hs.2.trans hba.le)
      have hm := h.1.2.1 a1 hl1
      set t := stripClock (extPath w) (extPath v) s
      have hsm : (s : ℝ) ∈ Icc 0 (a1 : ℝ) := ⟨s.coe_nonneg, NNReal.coe_le_coe.2 (hs.2.trans hba.le)⟩
      have ht0 : 0 ≤ t := hm.stripClock_nonneg hsm
      have hst : ss κ σ f t = s := by
        rw [← chordalTime_eq_ss h ht0, hm.chordalTime_stripClock hsm]
      have ht1 : t ≤ 1 := by
        have := h.1.stripClock_le hl1 (hs.2.trans hba.le)
        rwa [(h.1.chordT_spec 1).2.2] at this
      have := hg0 t ⟨ht0, ht1⟩
      simp only [hg, hst, Real.toNNReal_coe] at this
      exact this
    · rintro rfl
      exact ⟨0, ⟨le_rfl, bot_le⟩, (hη a1 hl1).1⟩
  have hfill := (hη a1 hl1).2.2 b (ENNReal.coe_lt_coe.2 hba)
  rw [himg] at hfill
  obtain ⟨z, hz, hcc⟩ := hfill.1
  have hH : H \ {(0 : ℂ)} = H := by
    ext x; simp only [Set.mem_sdiff, mem_singleton_iff, and_iff_left_iff_imp]
    intro hx h0; rw [h0] at hx; exact absurd (show (0 : ℝ) < (0 : ℂ).im from hx) (by simp)
  have hconv : Convex ℝ H := convex_halfSpace_gt Complex.imLm.isLinear 0
  rw [hH, (hconv.isPreconnected).connectedComponentIn hz.1] at hcc
  -- `K_b = ∅`, contradicting nonemptiness of the hull at a positive time
  obtain ⟨s', hss', hs'⟩ := h.1.exists_gt hl1
  have hfc : Continuous (frozenDrive w s') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.1.continuousOn_le hs')
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) b = fwdHull (frozenDrive w s') b :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg b) (NNReal.coe_lt_coe.2 (hba.trans hss')) fun r hr =>
      (frozenDrive_eq hr).symm
  obtain ⟨x, hx⟩ := QuantumZipper.CaraR.fwdHull_nonempty hfc
    (by rw [frozenDrive_zero (NNReal.coe_nonneg s'), h.1.1]) hb0
  rw [← hK] at hx
  have hxH : x ∈ H := hx.1
  have : x ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) b := by rw [← hcc]; exact hxH
  exact this.2 hx


/-- **A cluster point at the source lifts to a lower cluster point of a restart.** If the trace converges to `0` along
rational strip times `q_k ≥ k`, there is a rational strip time `r > 0` at which the restarted trace has a cluster point
`p₀ ∈ (−1, ∞) ∖ {0}` along rational strip times. -/
theorem exists_shift_lower_cluster (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {q : ℕ → ℚ} (hq : ∀ k : ℕ, (k : ℚ) ≤ q k)
    (hlim : Tendsto (fun k => η (chordT w v ((q k : ℝ)).toNNReal)) atTop (𝓝 0)) :
    ∃ r : ℚ, 0 < r ∧ ∃ p0 : ℝ, -1 < p0 ∧ p0 ≠ 0 ∧ ∃ q' : ℕ → ℚ, (∀ k : ℕ, (k : ℚ) ≤ q' k) ∧
      Tendsto (fun k => rsTrace w v ((r : ℝ).toNNReal) (chordT (rsW w v ((r : ℝ).toNNReal))
        (rsV w v ((r : ℝ).toNNReal)) ((q' k : ℝ)).toNNReal)) atTop (𝓝 (p0 : ℂ)) := by
  obtain ⟨r, hr0, htip⟩ := exists_tip_ne_zero h hη
  refine ⟨r, hr0, ?_⟩
  set R : ℝ≥0 := ((r : ℝ)).toNNReal with hRdef
  have hRr : (R : ℝ) = r := Real.coe_toNNReal _ (by exact_mod_cast hr0.le)
  have hR := hasStripDriver_rs h R
  have hfR := tendsto_shiftPath hf R
  have hηR := isGeneratingTrace_rsTrace h hη R
  set a := chordT w v R with ha_def
  have hal_a := (h.1.chordT_spec R).1
  obtain ⟨s', has', hs'⟩ := h.1.exists_gt hal_a
  set g := qq κ σ f R with hgdef
  have hg : 0 < g := qq_pos f R
  have hw0 : w 0 = 0 := h.1.1
  have h₁ : Sec7.IsGeneratingTraceIcc w a η := Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hη s' hs')
    (h.1.continuousOn_lt hs') hw0 (ENNReal.coe_lt_coe.2 has')
  have hfc : Continuous (frozenDrive w s') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.1.continuousOn_le hs')
  have hW0' : frozenDrive w s' 0 = 0 := by rw [frozenDrive_zero (NNReal.coe_nonneg s'), hw0]
  obtain ⟨-, -, hFeq, hFc, -, -, hF0⟩ := h₁.extend_props (t₂ := (s' : ℝ)) (NNReal.coe_lt_coe.2 has') hfc hw0
  set F := extendFrom H (fwdMapInv (frozenDrive w s') a) with hFdef
  -- the indices
  set m : ℕ := ⌈(r : ℝ)⌉₊ with hm
  have hqk' : ∀ k : ℕ, (k : ℝ) + r ≤ q (k + m) := fun k => by
    have h1 := hq (k + m)
    have h2 : (r : ℝ) ≤ m := Nat.le_ceil _
    have h3 : ((k + m : ℕ) : ℝ) ≤ (q (k + m) : ℝ) := by exact_mod_cast h1
    push_cast at h3
    linarith
  set qq' : ℕ → ℚ := fun k => q (k + m) - r with hqq'
  have hqq'k : ∀ k : ℕ, (k : ℚ) ≤ qq' k := fun k => by
    have := hqk' k
    simp only [hqq']
    exact_mod_cast (show (k : ℝ) ≤ (q (k + m) : ℝ) - r by linarith)
  set τ : ℕ → ℝ≥0 := fun k => ((qq' k : ℝ)).toNNReal with hτ
  have hτk : ∀ k : ℕ, (τ k : ℝ) = (q (k + m) : ℝ) - r := fun k => by
    rw [hτ]; simp only [hqq']
    rw [Real.coe_toNNReal _ (by push_cast; linarith [hqk' k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
    push_cast; ring
  have hqτ : ∀ k : ℕ, ((q (k + m) : ℝ)).toNNReal = R + τ k := fun k => by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by linarith [hqk' k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
      (show (0 : ℝ) < r by exact_mod_cast hr0)]), NNReal.coe_add, hτk, hRr]
    ring
  set p : ℕ → ℂ := fun k => rsTrace w v R (chordT (rsW w v R) (rsV w v R) (τ k)) with hp
  have hjoin : ∀ k, η (chordT w v ((q (k + m) : ℝ)).toNNReal) = F ((g : ℂ) * p k) := fun k => by
    rw [hqτ k, trace_chordT_add_eq h hη R hs' has' (τ k)]
  have hpS : ∀ k, p k ∈ hullSet (csub κ σ (slope σ) (shiftPath R f) + hullR σ) := fun k =>
    mem_hullSet hσ hfR hR hηR ((hR.1.chordT_spec (τ k)).1)
  obtain ⟨p0, hp0S, φ, hφ, hplim⟩ := tendsto_subseq_of_bounded (isBounded_hullSet _) hpS
  rw [(isClosed_hullSet _).closure_eq] at hp0S
  have hgp0 : (g : ℂ) * p0 ∈ Hbar := by
    show 0 ≤ ((g : ℂ) * p0).im
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hg.le hp0S.1
  have hzlim : Tendsto (fun k => F ((g : ℂ) * p (φ k))) atTop (𝓝 (F ((g : ℂ) * p0))) :=
    (hFc _ hgp0).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨tendsto_const_nhds.mul hplim, Eventually.of_forall fun k => by
        show 0 ≤ ((g : ℂ) * p (φ k)).im
        rw [Complex.im_ofReal_mul]
        exact mul_nonneg hg.le (hpS (φ k)).1⟩)
  have hzlim2 : Tendsto (fun k => F ((g : ℂ) * p (φ k))) atTop (𝓝 0) := by
    have := hlim.comp ((tendsto_add_atTop_nat m).comp hφ.tendsto_atTop)
    refine this.congr fun k => ?_
    simp only [Function.comp_apply]
    exact hjoin (φ k)
  have hF0' : F ((g : ℂ) * p0) = 0 := tendsto_nhds_unique hzlim hzlim2
  -- `p₀` is real, not `0`, and right of `−1`
  have hpim : p0.im = 0 := by
    by_contra hne
    have hpos : 0 < p0.im := lt_of_le_of_ne hp0S.1 (Ne.symm hne)
    have hgH : (g : ℂ) * p0 ∈ H := by
      show 0 < ((g : ℂ) * p0).im
      rw [Complex.im_ofReal_mul]
      exact mul_pos hg hpos
    have := QuantumZipper.RS.fwdMapInv_mem_H hfc hW0' (NNReal.coe_nonneg a) hgH
    rw [← hFeq hgH, hF0'] at this
    exact absurd (show (0 : ℝ) < (0 : ℂ).im from this) (by simp)
  have hp0r : p0 = (p0.re : ℂ) := Complex.ext rfl (by simp [hpim])
  have hne0 : p0.re ≠ 0 := by
    intro h0
    rw [hp0r, h0, Complex.ofReal_zero, mul_zero, hF0] at hF0'
    exact htip hF0'
  have hend := h.1.isForwardSol_end hs' has'.le
  have hgap : extPath v a - extPath w a = -g := by
    have := rsGap_eq h R
    rw [rsGap] at this
    rw [extPath_coe, extPath_coe]
    linarith
  have hgt : -1 < p0.re := by
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · obtain ⟨x, hx, u', hu', hu'a⟩ := exists_isForwardSol_eq_of_lt hfc hW0' (NNReal.coe_nonneg a) hend
        (y := g * p0.re) (by simp only [Complex.ofReal_re]; rw [hgap]; nlinarith)
      have hFx := extendFrom_eq_of_isForwardSol hfc hW0' (NNReal.coe_nonneg a) hFeq hFc hu'
      have hgp : (g : ℂ) * p0 = u' a := by rw [hu'a]; nth_rewrite 1 [hp0r]; push_cast; ring
      rw [hgp, hFx] at hF0'
      have : (x : ℝ) = 0 := by exact_mod_cast hF0'
      linarith
    · have hFx := extendFrom_eq_of_isForwardSol hfc hW0' (NNReal.coe_nonneg a) hFeq hFc hend
      have hgp : (g : ℂ) * p0 = ((extPath v a - extPath w a : ℝ) : ℂ) := by
        rw [hgap]; nth_rewrite 1 [hp0r]; rw [heq]; push_cast; ring
      rw [hgp, hFx] at hF0'
      norm_num at hF0'
  refine ⟨p0.re, hgt, hne0, fun k => qq' (φ k), fun k => ?_, ?_⟩
  · exact (show (k : ℚ) ≤ (φ k : ℚ) by exact_mod_cast hφ.id_le k).trans (hqq'k (φ k))
  · rw [← hp0r]
    exact hplim

end HeightLaw

end Zhan

end InteractingSLE
