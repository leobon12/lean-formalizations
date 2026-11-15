/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftHeightClus

/-!
# The restart along an actual trace, and the strict height inequality at the minimal height

Packet PROVE-ZHAN-A7. Astra L1494–L1499: "Every minimal-height point of `Q` is then raised strictly … Compactness
gives `M_h > M`, a contradiction." For a sublinear path `f`, a strip path with strip driver `drv κ σ f` and a generating
trace `η`, and the restart at the strip time `n` (`rsW`, `rsV`, `rsZ`, PROVE-ZHAN-A4):

* `hasStripDriver_rs`: the restart is a strip path with the strip driver of the restarted Brownian path `shiftPath n f`;
* `rsTrace`: its trace `r ↦ g⁻¹ γ_a(g² r)` (`IsStripPath.isGeneratingTrace_rs`);
* `trace_add_eq`: the join `η(a + u) = F̄_a(γ_a(u))`, `F̄_a` the boundary extension of the inverse map at `a`;
* `chordT_add_eq`: `s(n + τ) = a + g² ŝ(τ)`, `g = q_n`;
* `mm_eq_zero_or_pi` (**the strict inequality at the minimal height**): if `mm (θ_n f) = mm f`, `n ≥ 1`, then
  `mm f ∈ {0, π}` (compactness of the restarted trace points, the height inequality `arg_one_add_lt` in `ℍ`, and the
  real points left of the end mark on the boundary);
* `exists_lower_cluster`: if `mm f = 0`, the trace has a cluster point on `(−1, ∞)` along rational strip times.
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

/-! ### The restart of a strip path with the driver of a path -/

/-- **The restart is a strip path of the restarted Brownian path.** -/
theorem hasStripDriver_rs (h : HasStripDriver w v ζ fun t => drv κ σ f t) (n : ℝ≥0) :
    HasStripDriver (rsW w v n) (rsV w v n) (rsZ w v ζ n) fun t => drv κ σ (shiftPath n f) t := by
  refine ⟨(h.rs n).1, fun t => ?_⟩
  rw [(h.rs n).2 t]
  simp only
  rw [drv_shiftPath n f t.coe_nonneg, NNReal.coe_add]

/-- The trace of the restart. -/
def rsTrace (w v : ℝ≥0 → ℝ) (n : ℝ≥0) (r : ℝ≥0) : ℂ :=
  (((√((rsScale w v n : ℝ≥0) : ℝ))⁻¹ : ℝ) : ℂ) * shiftTip w (chordT w v n) (rsScale w v n * r)

theorem isGeneratingTrace_rsTrace (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) (n : ℝ≥0) :
    ∀ r : ℝ≥0, IsStripLife (rsW w v n) (rsV w v n) (rsZ w v ζ n) r → IsGeneratingTrace (rsW w v n) r (rsTrace w v n) :=
  fun _ hr => h.1.isGeneratingTrace_rs hη n hr

/-- The gap at the restart time is `q_n`. -/
theorem rsGap_eq (h : HasStripDriver w v ζ fun t => drv κ σ f t) (n : ℝ≥0) : rsGap w v n = qq κ σ f n := by
  rw [rsGap, ← gap_chordalTime_eq h n.coe_nonneg, ← (h.1.chordT_spec n).2.1, extPath_coe, extPath_coe]

/-- `s(n + τ) = a + g² ŝ(τ)`. -/
theorem chordT_add_eq (h : HasStripDriver w v ζ fun t => drv κ σ f t) (n τ : ℝ≥0) :
    chordT w v (n + τ) = chordT w v n + rsScale w v n * chordT (rsW w v n) (rsV w v n) τ := by
  apply NNReal.coe_injective
  have hR := hasStripDriver_rs h n
  rw [NNReal.coe_add, NNReal.coe_mul, coe_chordT_eq h, coe_chordT_eq h, coe_chordT_eq hR, coe_rsScale,
    rsGap_eq h, ss_shiftPath n f τ.coe_nonneg, NNReal.coe_add]
  have := qq_pos (κ := κ) (σ := σ) f n
  field_simp
  ring

/-- **The join at the restart time**: `η(a + u) = F̄_a(γ_a(u))`. -/
theorem trace_add_eq (h : IsStripPath w v ζ) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {a s' : ℝ≥0}
    (hs' : IsStripLife w v ζ s') (has' : a < s') {u : ℝ≥0} (hu : IsStripLife w v ζ (a + u)) :
    η (a + u) = extendFrom H (fwdMapInv (frozenDrive w s') a) (shiftTip w a u) := by
  have hw0 : w 0 = 0 := h.1
  have h₁ : Sec7.IsGeneratingTraceIcc w a η :=
    Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hη s' hs') (h.continuousOn_lt hs') hw0
      (ENNReal.coe_lt_coe.2 has')
  have hfc : Continuous (frozenDrive w s') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.continuousOn_le hs')
  obtain ⟨hF, -, -, -, -, -, hF0⟩ := h₁.extend_props (t₂ := (s' : ℝ)) (NNReal.coe_lt_coe.2 has') hfc hw0
  obtain ⟨s'', hss'', hs''⟩ := h.exists_gt hu
  have hT := isGeneratingTrace_shiftTip (hη s'' hs'') (h.continuousOn_lt hs'') hw0 (a := a) (u := u)
    (ENNReal.coe_lt_coe.2 hss'')
  rcases eq_or_ne u 0 with hu0 | hu0
  · subst hu0
    rw [add_zero, hT.1, hF0]
  · have hjn := (Sec7.IsGeneratingTraceIcc.join (by rw [← ENNReal.coe_add]; exact h.continuousOn_lt hu) hw0
      h₁ hT).1
    rw [← ENNReal.coe_add] at hjn
    have heq := IsGeneratingTrace.eq_of_le (hη (a + u) hu) hjn (h.continuousOn_lt hu) hw0 le_rfl
    have hlt : a < a + u := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hu0)
    rw [heq, Sec7.joinTrace_of_lt hlt, hF, add_tsub_cancel_left]

/-- **The join through the restarted trace**: `η(s(n + τ)) = F̄_a(g · η̂(ŝ(τ)))`. -/
theorem trace_chordT_add_eq (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) (n : ℝ≥0) {s' : ℝ≥0}
    (hs' : IsStripLife w v ζ s') (has' : chordT w v n < s') (τ : ℝ≥0) :
    η (chordT w v (n + τ)) = extendFrom H (fwdMapInv (frozenDrive w s') (chordT w v n))
      ((qq κ σ f n : ℂ) * rsTrace w v n (chordT (rsW w v n) (rsV w v n) τ)) := by
  have hl : IsStripLife w v ζ (chordT w v n + rsScale w v n * chordT (rsW w v n) (rsV w v n) τ) := by
    rw [← chordT_add_eq h n τ]
    exact (h.1.chordT_spec _).1
  rw [chordT_add_eq h n τ, trace_add_eq h.1 hη hs' has' hl]
  congr 1
  have hc := h.1.rsScale_pos n
  have hsq : √((rsScale w v n : ℝ≥0) : ℝ) = qq κ σ f n := by
    rw [coe_rsScale, rsGap_eq h, Real.sqrt_sq (qq_pos f n).le]
  rw [rsTrace, hsq, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (qq_pos f n).ne', Complex.ofReal_one,
    one_mul]

/-- The restarted Brownian path is sublinear. -/
theorem tendsto_shiftPath (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0)) (n : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => (shiftPath n f).1 t / (t : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ≥0 => n + t) atTop atTop :=
    tendsto_atTop_mono (fun t => (le_add_self : t ≤ n + t)) tendsto_id
  have h2 : Tendsto (fun t : ℝ≥0 => ((n + t : ℝ≥0) : ℝ) / (t : ℝ)) atTop (𝓝 1) := by
    have h3 : Tendsto (fun t : ℝ≥0 => 1 + (n : ℝ) / (t : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop (NNReal.tendsto_coe_atTop.2 tendsto_id))
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
    push_cast
    rw [add_div, div_self this, add_comm]
  have h4 : Tendsto (fun t : ℝ≥0 => f.1 n / (t : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have h5 := ((hf.comp h1).mul h2).sub h4
  simp only [mul_one, sub_zero] at h5
  refine h5.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  have hnt : ((n + t : ℝ≥0) : ℝ) ≠ 0 := by
    have : (0 : ℝ≥0) < n + t := lt_of_lt_of_le ht le_add_self
    exact_mod_cast this.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [Function.comp_apply, shiftPath]
  rw [sub_div, div_mul_div_cancel₀ hnt]

/-- The inverse map of the frozen driver agrees with the explicit inverse map on `ℍ`. -/
theorem fwdMapInv_frozen_eq_cdrv (h : HasStripDriver w v ζ fun t => drv κ σ f t) {n : ℕ} {s' : ℝ≥0}
    (hs' : IsStripLife w v ζ s') (has' : chordT w v n < s') {N : ℝ} (hnN : (n : ℝ) ≤ N) {z : ℂ}
    (hz : z ∈ H) :
    fwdMapInv (frozenDrive w s') (chordT w v n) z = fwdMapInv (cdrv κ σ f N) (ss κ σ f n) z := by
  have hN : 0 ≤ N := (Nat.cast_nonneg n).trans hnN
  have hfc : Continuous (frozenDrive w s') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.1.continuousOn_le hs')
  have ha : ((chordT w v n : ℝ≥0) : ℝ) = ss κ σ f n := by
    rw [coe_chordT_eq h]; simp
  rw [← ha]
  refine LP.fwdMapInv_eq_of_eqOn_Icc hfc (continuous_cdrv f hN)
    (by rw [frozenDrive_zero (NNReal.coe_nonneg s'), h.1.1]) (cdrv_zero f hN) (NNReal.coe_nonneg _)
    (fun r hr => ?_) hz
  have hrs' : r ≤ s' := hr.2.trans (NNReal.coe_le_coe.2 has'.le)
  rw [frozenDrive_eq ⟨hr.1, hrs'⟩]
  refine extPath_w_eq_cdrv h hN ⟨hr.1, ?_⟩
  rw [ha] at hr
  exact hr.2.trans (ss_le_ss f (Nat.cast_nonneg n) hnN)

/-- The bounded closed set of the bounded hull. -/
def hullSet (X : ℝ) : Set ℂ := {z | z ∈ Hbar ∧ ‖1 + z‖ ∈ Icc (Real.exp (-X)) (Real.exp X)}

theorem isClosed_hullSet (X : ℝ) : IsClosed (hullSet X) :=
  QuantumZipper.isClosed_Hbar.inter (isClosed_Icc.preimage (continuous_norm.comp (continuous_const.add continuous_id)))

theorem isBounded_hullSet (X : ℝ) : Bornology.IsBounded (hullSet X) := by
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + Real.exp X)).subset fun z hz => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖z‖ ≤ ‖1 + z‖ + 1 := by
    calc ‖z‖ = ‖(1 + z) - 1‖ := by ring_nf
      _ ≤ ‖1 + z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖1 + z‖ + 1 := by simp
  linarith [hz.2.2]

theorem one_add_ne_zero_of_mem_hullSet {X : ℝ} {z : ℂ} (hz : z ∈ hullSet X) : 1 + z ≠ 0 := fun h0 => by
  have := hz.2.1
  rw [h0, norm_zero] at this
  exact (Real.exp_pos _).not_ge this

theorem mem_hullSet (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {s : ℝ≥0} (hs : IsStripLife w v ζ s) :
    η s ∈ hullSet (csub κ σ (slope σ) f + hullR σ) :=
  ⟨trace_mem_Hbar h hη hs, by have := norm_one_add_mem hσ hf h hη hs; simpa using this⟩

theorem tendsto_arg_one_add {u : ℕ → ℂ} {z : ℂ} (hu : Tendsto u atTop (𝓝 z)) (hz : 1 + z ≠ 0)
    (hH : ∀ k, u k ∈ Hbar) : Tendsto (fun k => arg (1 + u k)) atTop (𝓝 (arg (1 + z))) := by
  refine (continuousWithinAt_arg_Hbar hz).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add hu,
    Eventually.of_forall fun k => ?_⟩)
  show 0 ≤ (1 + u k).im
  simp only [add_im, one_im, zero_add]
  exact hH k

/-- **The strict height inequality at the minimal height**: if the restart at the strip time `n ≥ 1` has the same
terminal minimal height, that height is `0` or `π`. -/
theorem mm_eq_zero_or_pi (hσ : |σ| < 1) (hf : Tendsto (fun t : ℝ≥0 => f.1 t / (t : ℝ)) atTop (𝓝 0))
    (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {n : ℕ} (hn : 0 < n)
    (heq : mm κ σ (shiftPath n f) = mm κ σ f) : mm κ σ f = 0 ∨ mm κ σ f = Real.pi := by
  set m := mm κ σ f with hm
  have hR := hasStripDriver_rs h (n : ℝ≥0)
  have hfR := tendsto_shiftPath hf (n : ℝ≥0)
  have hηR := isGeneratingTrace_rsTrace h hη (n : ℝ≥0)
  have hhgt : ∀ t, 0 ≤ t → hgt κ σ f t ∈ Icc 0 Real.pi := fun t ht => hgt_mem_Icc_zero_pi hσ hf h hη ht
  have hhgtR : ∀ t, 0 ≤ t → hgt κ σ (shiftPath n f) t ∈ Icc 0 Real.pi := fun t ht =>
    hgt_mem_Icc_zero_pi hσ hfR hR hηR ht
  have hmI : m ∈ Icc 0 Real.pi := limInfTopQ_mem hhgt
  by_contra hcon
  push Not at hcon
  have hm0 : 0 < m := lt_of_le_of_ne hmI.1 (Ne.symm hcon.1)
  have hmπ : m < Real.pi := lt_of_le_of_ne hmI.2 hcon.2
  -- the restart data
  set a := chordT w v n with ha_def
  have hal := (h.1.chordT_spec (n : ℝ≥0)).1
  obtain ⟨s', has', hs'⟩ := h.1.exists_gt hal
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
  -- the rational strip times along which the heights approach `m` from above
  have hseq : ∀ k : ℕ, ∃ q : ℚ, ((k + n : ℕ) : ℚ) ≤ q ∧ hgt κ σ f q < m + 1 / ((k : ℝ) + 1) := fun k =>
    frequently_lt_of_limInfTopQ_lt hhgt (by
      rw [show limInfTopQ (hgt κ σ f) = m from rfl]
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith) (k + n)
  choose q hqk hqm using hseq
  have hqk' : ∀ k : ℕ, (k : ℝ) + n ≤ q k := fun k => by have := hqk k; exact_mod_cast this
  have hq0 : ∀ k : ℕ, (0 : ℝ) ≤ q k := fun k => by linarith [hqk' k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set τ : ℕ → ℝ≥0 := fun k => ((q k : ℝ) - n).toNNReal with hτ
  have hτk : ∀ k : ℕ, (τ k : ℝ) = (q k : ℝ) - n := fun k =>
    Real.coe_toNNReal _ (by linarith [hqk' k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hqτ : ∀ k : ℕ, ((q k : ℝ)).toNNReal = (n : ℝ≥0) + τ k := fun k => by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (hq0 k), NNReal.coe_add, hτk]
    simp
  -- the restarted trace points and the join
  set p : ℕ → ℂ := fun k => rsTrace w v n (chordT (rsW w v n) (rsV w v n) (τ k)) with hp
  have hjoin : ∀ k, η (chordT w v ((q k : ℝ)).toNNReal) = F ((g : ℂ) * p k) := fun k => by
    rw [hqτ k, trace_chordT_add_eq h hη n hs' has' (τ k), hgn]
  have hpS : ∀ k, p k ∈ hullSet (csub κ σ (slope σ) (shiftPath n f) + hullR σ) := fun k =>
    mem_hullSet hσ hfR hR hηR ((hR.1.chordT_spec (τ k)).1)
  obtain ⟨p0, hp0S, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (isBounded_hullSet _) hpS
  rw [(isClosed_hullSet _).closure_eq] at hp0S
  have hφt : Tendsto (fun k => (φ k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  -- (a) the height of `p0` is at least `m`
  have ha0 : m ≤ arg (1 + p0) := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨N, hN⟩ := eventually_lt_of_lt_limInfTopQ (c := m - δ) hhgtR
      (by rw [show limInfTopQ (hgt κ σ (shiftPath n f)) = mm κ σ (shiftPath n f) from rfl, heq]; linarith)
    have hlimarg := tendsto_arg_one_add hlim (one_add_ne_zero_of_mem_hullSet hp0S) fun k => (hpS (φ k)).1
    have hev : ∀ᶠ k in atTop, m - δ ≤ arg (1 + p (φ k)) := by
      filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop N] with k hk
      have hr : (N : ℚ) ≤ q (φ k) - n := by
        have := hqk' (φ k)
        have h2 : ((N : ℕ) : ℝ) ≤ (φ k : ℝ) := by exact_mod_cast hk
        exact_mod_cast (show ((N : ℕ) : ℝ) ≤ (q (φ k) : ℝ) - n by linarith)
      have h1 := hN _ hr
      have h3 : (((q (φ k) - n : ℚ)) : ℝ) = (τ (φ k) : ℝ) := by rw [hτk]; push_cast; ring
      rw [h3, hgt_eq hσ hfR hR hηR (NNReal.coe_nonneg _), Real.toNNReal_coe] at h1
      exact h1.le
    have := ge_of_tendsto hlimarg hev
    linarith
  -- (b) the limit point of the original trace has height at most `m`
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
      ⟨tendsto_const_nhds.mul hlim, Eventually.of_forall fun k => hgpk (φ k)⟩)
  have hzS : ∀ k, F ((g : ℂ) * p k) ∈ hullSet (csub κ σ (slope σ) f + hullR σ) := fun k => by
    rw [← hjoin k]
    exact mem_hullSet hσ hf h hη (h.1.chordT_spec _).1
  have hz0S : F ((g : ℂ) * p0) ∈ hullSet (csub κ σ (slope σ) f + hullR σ) :=
    (isClosed_hullSet _).mem_of_tendsto hzlim (Eventually.of_forall fun k => hzS (φ k))
  have hb0 : arg (1 + F ((g : ℂ) * p0)) ≤ m := by
    have hlz := tendsto_arg_one_add hzlim (one_add_ne_zero_of_mem_hullSet hz0S) fun k => (hzS (φ k)).1
    have hup : Tendsto (fun k => m + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 m) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).const_add m
      simpa using this
    refine le_of_tendsto_of_tendsto' hlz hup fun k => ?_
    have h1 := hqm (φ k)
    rw [hgt_eq hσ hf h hη (hq0 _), hjoin] at h1
    exact h1.le
  -- (c) the strict inequality in `ℍ`, and the boundary
  rcases (show (0 : ℝ) ≤ p0.im from hp0S.1).lt_or_eq with hpos | hzero
  · have hp0H : p0 ∈ H := hpos
    have hgH : (g : ℂ) * p0 ∈ H := by
      show 0 < ((g : ℂ) * p0).im
      rw [Complex.im_ofReal_mul]
      exact mul_pos hg hpos
    have hFz : F ((g : ℂ) * p0) = fwdMapInv (cdrv κ σ f n) (ss κ σ f n) ((g : ℂ) * p0) := by
      rw [hFeq hgH]
      exact fwdMapInv_frozen_eq_cdrv h hs' has' le_rfl hgH
    have hlt := arg_one_add_lt (κ := κ) (σ := σ) f hn (le_refl (n : ℝ)) hp0H
    rw [← hgdef, ← hFz] at hlt
    linarith
  · have hp0r : p0 = (p0.re : ℂ) := Complex.ext rfl (by simp [← hzero])
    have hre : (1 + p0).re < 0 := by
      by_contra hge
      push Not at hge
      have : arg (1 + p0) = 0 := Complex.arg_eq_zero_iff.2 ⟨hge, by simp [← hzero]⟩
      linarith
    have hpre : p0.re < -1 := by simp only [add_re, one_re] at hre; linarith
    have hend := h.1.isForwardSol_end hs' has'.le
    have hgap : extPath v a - extPath w a = -g := by
      have := rsGap_eq h (n : ℝ≥0)
      rw [rsGap, hgn] at this
      rw [extPath_coe, extPath_coe]
      linarith
    obtain ⟨x, hx, u', hu', hu'a⟩ := exists_isForwardSol_eq_of_lt hfc hW0' (NNReal.coe_nonneg a) hend
      (y := g * p0.re) (by simp only [Complex.ofReal_re]; rw [hgap]; nlinarith)
    have hFx := extendFrom_eq_of_isForwardSol hfc hW0' (NNReal.coe_nonneg a) hFeq hFc hu'
    have hgp : (g : ℂ) * p0 = u' a := by rw [hu'a]; nth_rewrite 1 [hp0r]; push_cast; ring
    rw [hgp, hFx] at hb0
    have : arg (1 + (x : ℂ)) = Real.pi := by
      rw [show (1 : ℂ) + x = ((1 + x : ℝ) : ℂ) by push_cast; ring]
      exact Complex.arg_ofReal_of_neg (by linarith)
    linarith

end HeightLaw

end Zhan

end InteractingSLE
