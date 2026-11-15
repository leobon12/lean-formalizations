/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Green
import InteractingSLE.Spec.Coupling.SafeCompact

/-!
# Aux. lemma 50 for `κ ≥ 8`: freezing small pieces at their safe exit times (deterministic part)

Packet PROVE-AUX50C. Specification Aux. lemma 50, proof, (HGV3)–(HGV5) (`source/spec/p193-240.md` L845–L870,
pp. 237–238): along a continuous driver the Green kernel `G_{D_s}(a, b) = G_ℍ(f_s a, f_s b)` decreases in `s`, "if
a point is swallowed without being on the trace, its whole open component is newly disconnected, and Green
convergence retains the Green function of that pocket", and it vanishes once one of the two points is swallowed.

For a continuous driver `w` with `w 0 = 0`:

* `safeExitTime_anti`: the safe exit time of a smaller compact set is later;
* `lt_swallowTime_of_safeExit`: a point of a compact set is still alive at the set's safe exit time;
* **`eventually_le_safeExitTime_ball`**: for a point `z` alive at `t ≤ N`, the safe exit times (at level `n`) of all
  compact sets inside `B̄(z, 4·2⁻ⁿ)` are eventually `≥ t`, uniformly;
* **`tendsto_aGreen_VT`**: if times `s_n ≤ N` stay below the later of the two swallowing times of `a, b` and
  eventually pass every time `≤ N` at which `a` or `b` is alive, then `G_{s_n}(a, b) → V_N(a, b)`, QuantumZipper's
  retained kernel (the left limit at a common swallowing time, `0` for different swallowing times, `G_N(a, b)` if both
  are alive at `N`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper QuantumZipper.K3 Coupling

variable {w : ℝ≥0 → ℝ}

/-! ### Safe exit times of small pieces -/

/-- The safe exit time of a smaller set is later. -/
theorem safeExitTime_anti {K K' : Set ℂ} (hKK : K' ⊆ K) {δ N : ℝ} {σ₀ : ℝ≥0} {ζ : ℝ≥0∞} :
    safeExitTime K δ N σ₀ ζ w ≤ safeExitTime K' δ N σ₀ ζ w :=
  csInf_le_csInf (OrderBot.bddBelow _) nonempty_not_isSafeAt fun _ ht hs => ht (hs.subset hKK)

theorem continuous_rpath_of (hw : Continuous w) : Continuous (Ito.rpath w) :=
  hw.comp continuous_real_toNNReal

/-- A point of `ℍ` outside the hull at `T ≥ 0` is swallowed after `T`. -/
theorem lt_swallowTime_of_not_mem {W : ℝ → ℝ} {z : ℂ} (hz : z ∈ H) {T : ℝ} (hzK : z ∉ fwdHull W T) :
    ENNReal.ofReal T < swallowTime W z := by
  by_contra hle
  exact hzK ⟨hz, not_lt.1 hle⟩

/-- **A point of a compact set is alive at the set's safe exit time.** -/
theorem lt_swallowTime_of_safeExit (hw : Continuous w) {K : Set ℂ} (hKH : K ⊆ H) {δ N : ℝ} (hδ : 0 < δ)
    {σ₀ : ℝ≥0} (h0 : IsSafeAt K δ N σ₀ ⊤ w 0) {z : ℂ} (hz : z ∈ K) :
    ENNReal.ofReal (safeExitTime K δ N σ₀ ⊤ w : ℝ) < swallowTime (Ito.rpath w) z := by
  have hs := isSafeAt_safeExitTime hw.continuousOn hKH hδ ENNReal.coe_lt_top h0
  obtain ⟨u, hu⟩ := (hs.2.2.2 z hz).1
  exact lt_swallowTime_of_not_mem (hKH hz)
    (Ito.notMem_fwdHull_of_isForwardSol (continuous_rpath_of hw) (hKH hz) (NNReal.coe_nonneg _) hu)

/-- **Uniform lower bound for the safe exit times of small pieces.** If `z ∈ ℍ` is alive at `t ≤ N`, then for all
large `n`, every compact `K ⊆ B̄(z, 4·2⁻ⁿ) ∩ ℍ` and every margin `m ≤ Im z + 4` has
`t ≤ safeExitTime K (m/(n+1)) n N ⊤ w`. -/
theorem eventually_le_safeExitTime_ball (hw : Continuous w) {z : ℂ} (hz : z ∈ H) {N t : ℝ≥0} (htN : t ≤ N)
    (halive : ENNReal.ofReal (t : ℝ) < swallowTime (Ito.rpath w) z) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Set ℂ, K ⊆ closedBall z (4 / 2 ^ n) → ∀ m : ℝ, m ≤ z.im + 4 →
      t ≤ safeExitTime K (m / ((n : ℝ) + 1)) n N ⊤ w := by
  have hW := continuous_rpath_of hw
  have hopen : IsOpen (H \ fwdHull (Ito.rpath w) t) := FwdHolo.isOpen_compl_fwdHull hW t.coe_nonneg
  have hzD : z ∈ H \ fwdHull (Ito.rpath w) t := ⟨hz, fun h => (not_le.2 halive) h.2⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen z hzD
  have hK₀ : closedBall z (r / 2) ⊆ H \ fwdHull (Ito.rpath w) t :=
    (closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK₀H : closedBall z (r / 2) ⊆ H := hK₀.trans sdiff_subset
  have halive₀ : ∀ u ∈ closedBall z (r / 2), ∃ v, IsForwardSol (Ito.rpath w) u t v := fun u hu =>
    exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg (hK₀ hu).1 (hK₀ hu).2
  have h1 := eventually_le_safeExitTime hw.continuousOn (isCompact_closedBall z (r / 2)) hK₀H (z.im + 4)
    htN ENNReal.coe_lt_top halive₀
  have h2 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) / 2 ^ n ≤ r / 2 := by
    have : Tendsto (fun n : ℕ => (4 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul 4
      simpa [div_eq_mul_inv, one_div, inv_pow] using this
    exact this.eventually (ge_mem_nhds (by positivity))
  filter_upwards [h1, h2] with n hn hrn K hK m hm
  refine hn.trans ((safeExitTime_anti (hK.trans (closedBall_subset_closedBall hrn))).trans ?_)
  refine safeExitTime_mono ?_ le_rfl le_rfl
  exact div_le_div_of_nonneg_right hm (by positivity)

/-! ### The kernel at the frozen times -/

/-- **The kernel at the frozen times converges to the retained kernel.** Let `a, b ∈ ℍ` and times `s_n ≤ N` that stay
strictly below the later of the two swallowing times and eventually pass every time `t ≤ N` at which `a` or `b` is
alive. Then `G_{s_n}(a, b) → V_N(a, b)`. -/
theorem tendsto_aGreen_VT (hw : Continuous w) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) {N : ℝ≥0}
    {s : ℕ → ℝ≥0} (hsN : ∀ n, s n ≤ N)
    (hsb : ∀ n, ENNReal.ofReal (s n : ℝ) < max (swallowTime (Ito.rpath w) a) (swallowTime (Ito.rpath w) b))
    (hlow : ∀ t : ℝ≥0, t ≤ N → (ENNReal.ofReal (t : ℝ) < swallowTime (Ito.rpath w) a ∨
      ENNReal.ofReal (t : ℝ) < swallowTime (Ito.rpath w) b) → ∀ᶠ n in atTop, t ≤ s n) :
    Tendsto (fun n => aGreen (Ito.rpath w) (s n) a b) atTop (𝓝 (VT (Ito.rpath w) N a b)) := by
  have hW := continuous_rpath_of hw
  set W := Ito.rpath w with hWdef
  set τa := swallowTime W a with hτa
  set τb := swallowTime W b with hτb
  -- Case A: both alive at `N`
  by_cases hA : ENNReal.ofReal (N : ℝ) < τa ∧ ENNReal.ofReal (N : ℝ) < τb
  · have hev := hlow N le_rfl (Or.inl hA.1)
    have haN : a ∈ actDom W N := mem_actDom_iff.2 ⟨ha, hA.1⟩
    have hbN : b ∈ actDom W N := mem_actDom_iff.2 ⟨hb, hA.2⟩
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    rw [le_antisymm (hsN n) hn, aGreen_eq_VT hW N.coe_nonneg haN hbN]
  -- otherwise the earlier swallowing time is at most `N`
  have hmin : min τa τb ≤ ENNReal.ofReal (N : ℝ) := by
    by_contra hc
    exact hA ⟨lt_of_lt_of_le (not_le.1 hc) (min_le_left _ _), lt_of_lt_of_le (not_le.1 hc) (min_le_right _ _)⟩
  by_cases hne : τa ≠ τb
  · -- Case B: different swallowing times: the kernel eventually vanishes, and so does `V_N`
    have hV : VT W N a b = 0 := by
      unfold VT; rw [VTe_eq_zero_of_swallowTime_ne hW ha hb hne hmin]; rfl
    rw [hV]
    -- the earlier point is swallowed eventually
    have key : ∀ {x y : ℂ}, x ∈ H → y ∈ H → swallowTime W x < swallowTime W y →
        swallowTime W x ≤ ENNReal.ofReal (N : ℝ) →
        (∀ t : ℝ≥0, t ≤ N → ENNReal.ofReal (t : ℝ) < swallowTime W y → ∀ᶠ n in atTop, t ≤ s n) →
        ∀ᶠ n in atTop, x ∉ actDom W (s n) := by
      intro x y hx hy hxy hxN hlowy
      have htop : swallowTime W x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxN
      set β := (swallowTime W x).toReal with hβ
      have hβeq : ENNReal.ofReal β = swallowTime W x := ENNReal.ofReal_toReal htop
      have hβ0 : 0 ≤ β := ENNReal.toReal_nonneg
      have hβN : β ≤ N := by rwa [← ENNReal.ofReal_le_ofReal_iff N.coe_nonneg, hβeq]
      -- a time `t ∈ [β, N]` at which `y` is alive
      obtain ⟨t, hβt, htN, hty⟩ : ∃ t : ℝ≥0, β ≤ t ∧ t ≤ N ∧ ENNReal.ofReal (t : ℝ) < swallowTime W y := by
        by_cases hyN : ENNReal.ofReal (N : ℝ) < swallowTime W y
        · exact ⟨N, hβN, le_rfl, hyN⟩
        · push Not at hyN
          have hytop : swallowTime W y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hyN
          set γ := (swallowTime W y).toReal
          have hγeq : ENNReal.ofReal γ = swallowTime W y := ENNReal.ofReal_toReal hytop
          have hβγ : β < γ := by
            rw [← hβeq, ← hγeq] at hxy
            exact (ENNReal.ofReal_lt_ofReal_iff'.1 hxy).1
          have hγN : γ ≤ N := by rwa [← ENNReal.ofReal_le_ofReal_iff N.coe_nonneg, hγeq]
          refine ⟨⟨(β + γ) / 2, by linarith⟩, ?_, ?_, ?_⟩
          · show β ≤ (β + γ) / 2; linarith
          · show (β + γ) / 2 ≤ (N : ℝ); linarith
          · rw [← hγeq]
            exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by show (β + γ) / 2 < γ; linarith)
      filter_upwards [hlowy t htN hty] with n hn hxD
      have h1 := (mem_actDom_iff.1 hxD).2
      rw [← hβeq] at h1
      have h2 : β ≤ (s n : ℝ) := hβt.trans (by exact_mod_cast hn)
      exact absurd h1 (not_lt.2 (ENNReal.ofReal_le_ofReal h2))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine tendsto_const_nhds.congr' ?_
      have hxN : swallowTime W a ≤ ENNReal.ofReal (N : ℝ) := by
        have := hmin; rwa [min_eq_left hlt.le] at this
      filter_upwards [key ha hb hlt hxN fun t ht h' => hlow t ht (Or.inr h')] with n hn
      rw [aGreen_of_not_mem_left hn]
    · refine tendsto_const_nhds.congr' ?_
      have hxN : swallowTime W b ≤ ENNReal.ofReal (N : ℝ) := by
        have := hmin; rwa [min_eq_right hlt.le] at this
      filter_upwards [key hb ha hlt hxN fun t ht h' => hlow t ht (Or.inl h')] with n hn
      rw [aGreen_of_not_mem_right hn]
  -- Case C: a common swallowing time `β ≤ N`
  push Not at hne
  have hβN' : τa ≤ ENNReal.ofReal (N : ℝ) := by rw [← min_self τa]; nth_rw 2 [hne]; exact hmin
  have htop : τa ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hβN'
  set β := τa.toReal with hβ
  have hβeq : ENNReal.ofReal β = τa := ENNReal.ofReal_toReal htop
  have hβN : β ≤ N := by rwa [← ENNReal.ofReal_le_ofReal_iff N.coe_nonneg, hβeq]
  -- the frozen times are admissible
  have hmax : max τa τb = τa := by rw [hne, max_self]
  have hmem : ∀ n, (s n : ℝ) ∈ vtIdx W N a b := fun n => by
    have h := hsb n
    rw [hmax] at h
    have h' : ENNReal.ofReal (s n : ℝ) < τb := by rw [← hne]; exact h
    exact ⟨NNReal.coe_nonneg _, by exact_mod_cast hsN n, h, h'⟩
  have hnotin : ∀ n, a ∈ actDom W (s n) ∧ b ∈ actDom W (s n) := fun n =>
    ⟨mem_actDom_iff.2 ⟨ha, (hmem n).2.2.1⟩, mem_actDom_iff.2 ⟨hb, (hmem n).2.2.2⟩⟩
  have hval : ∀ n, aGreen W (s n) a b = (vtKer W (s n) a b).toReal := fun n => by
    unfold aGreen; simp only [(hnotin n).1, (hnotin n).2, and_self, ↓reduceIte]
  have hVfin : VTe W N a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le _ (hmem 0))
  simp only [hval, VT]
  refine (ENNReal.tendsto_toReal hVfin).comp ?_
  -- `vtKer` along the frozen times decreases to the infimum
  refine (ENNReal.tendsto_nhds hVfin).2 fun ε hε => ?_
  have hlt : VTe W N a b < VTe W N a b + ε := ENNReal.lt_add_right hVfin hε.ne'
  obtain ⟨t₀, ht₀, hlt₀⟩ : ∃ t₀ ∈ vtIdx W N a b, vtKer W t₀ a b < VTe W N a b + ε := by
    by_contra hc
    push Not at hc
    exact absurd (le_iInf₂ hc) (not_le.2 hlt)
  have ht₀β : ENNReal.ofReal t₀ < τa := ht₀.2.2.1
  have hev := hlow ⟨t₀, ht₀.1⟩ (by exact_mod_cast ht₀.2.1) (Or.inl ht₀β)
  filter_upwards [hev] with n hn
  refine ⟨?_, ?_⟩
  · exact tsub_le_self.trans (iInf₂_le _ (hmem n))
  · exact (vtKer_antitoneOn hW ha hb ht₀ (hmem n) (by exact_mod_cast hn)).trans hlt₀.le

/-- **Core convergence**: along admissible times that are cofinal in the admissible set, `G_{s_n}(a, b) → V_N(a, b)`
(the kernel decreases along admissible times to its infimum `V_N`). -/
theorem tendsto_aGreen_VT_of_mem (hw : Continuous w) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) {N : ℝ≥0}
    {s : ℕ → ℝ≥0} (hmem : ∀ n, (s n : ℝ) ∈ vtIdx (Ito.rpath w) N a b)
    (hcof : ∀ t₀ ∈ vtIdx (Ito.rpath w) N a b, ∀ᶠ n in atTop, t₀ ≤ s n) :
    Tendsto (fun n => aGreen (Ito.rpath w) (s n) a b) atTop (𝓝 (VT (Ito.rpath w) N a b)) := by
  have hW := continuous_rpath_of hw
  set W := Ito.rpath w with hWdef
  have hnotin : ∀ n, a ∈ actDom W (s n) ∧ b ∈ actDom W (s n) := fun n =>
    ⟨mem_actDom_iff.2 ⟨ha, (hmem n).2.2.1⟩, mem_actDom_iff.2 ⟨hb, (hmem n).2.2.2⟩⟩
  have hval : ∀ n, aGreen W (s n) a b = (vtKer W (s n) a b).toReal := fun n => by
    unfold aGreen; simp only [(hnotin n).1, (hnotin n).2, and_self, ↓reduceIte]
  have hVfin : VTe W N a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf₂_le _ (hmem 0))
  simp only [hval, VT]
  refine (ENNReal.tendsto_toReal hVfin).comp ?_
  refine (ENNReal.tendsto_nhds hVfin).2 fun ε hε => ?_
  have hlt : VTe W N a b < VTe W N a b + ε := ENNReal.lt_add_right hVfin hε.ne'
  obtain ⟨t₀, ht₀, hlt₀⟩ : ∃ t₀ ∈ vtIdx W N a b, vtKer W t₀ a b < VTe W N a b + ε := by
    by_contra hc
    push Not at hc
    exact absurd (le_iInf₂ hc) (not_le.2 hlt)
  filter_upwards [hcof t₀ ht₀] with n hn
  refine ⟨tsub_le_self.trans (iInf₂_le _ (hmem n)), ?_⟩
  exact (vtKer_antitoneOn hW ha hb ht₀ (hmem n) hn).trans hlt₀.le

/-- **At a birth**: if `b` is swallowed at `β ≤ N` and times `s_n < β` increase to `β`, then
`G_{s_n}(a, b) → V_N(a, b)` for every `a ∈ ℍ` (a point swallowed earlier gives `0`, a point alive at `β` gives `0`
by `K3.VTe_eq_zero_of_swallowTime_ne`, a point swallowed with `b` gives the bubble limit). -/
theorem tendsto_aGreen_VT_of_birth (hw : Continuous w) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) {N : ℝ≥0}
    {β : ℝ≥0} (hβN : β ≤ N) (hbβ : swallowTime (Ito.rpath w) b = ENNReal.ofReal (β : ℝ)) {s : ℕ → ℝ≥0}
    (hsβ : ∀ n, s n < β) (hlim : Tendsto s atTop (𝓝 β)) :
    Tendsto (fun n => aGreen (Ito.rpath w) (s n) a b) atTop (𝓝 (VT (Ito.rpath w) N a b)) := by
  have hW := continuous_rpath_of hw
  set W := Ito.rpath w with hWdef
  have hβ0 : 0 < (β : ℝ) := lt_of_le_of_lt (NNReal.coe_nonneg _) (by exact_mod_cast hsβ 0)
  have hlt_of : ∀ {x : ℝ≥0}, x < β → ENNReal.ofReal (x : ℝ) < ENNReal.ofReal (β : ℝ) := fun hx =>
    (ENNReal.ofReal_lt_ofReal_iff hβ0).2 (by exact_mod_cast hx)
  by_cases hab : ENNReal.ofReal (β : ℝ) ≤ swallowTime W a
  · refine tendsto_aGreen_VT_of_mem hw ha hb (fun n => ?_) fun t₀ ht₀ => ?_
    · exact ⟨NNReal.coe_nonneg _, by exact_mod_cast (hsβ n).le.trans hβN, (hlt_of (hsβ n)).trans_le hab,
        hbβ ▸ hlt_of (hsβ n)⟩
    · have ht₀β : t₀ < β := by
        have := ht₀.2.2.2; rw [hbβ] at this; exact (ENNReal.ofReal_lt_ofReal_iff'.1 this).1
      have ht₀' : (⟨t₀, ht₀.1⟩ : ℝ≥0) < β := by exact_mod_cast ht₀β
      filter_upwards [hlim.eventually (lt_mem_nhds ht₀')] with n hn
      exact_mod_cast hn.le
  · push Not at hab
    have hV : VT W N a b = 0 := by
      unfold VT
      rw [VTe_eq_zero_of_swallowTime_ne hW ha hb (by rw [hbβ]; exact hab.ne) ((min_le_left _ _).trans
        (hab.le.trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hβN))))]
      rfl
    rw [hV]
    have htop : swallowTime W a ≠ ⊤ := ne_top_of_lt hab
    set γ := (swallowTime W a).toReal with hγ
    have hγeq : ENNReal.ofReal γ = swallowTime W a := ENNReal.ofReal_toReal htop
    have hγβ : γ < β := by
      rw [← hγeq] at hab; exact (ENNReal.ofReal_lt_ofReal_iff'.1 hab).1
    have hγ0 : 0 ≤ γ := ENNReal.toReal_nonneg
    have hγ' : (⟨γ, hγ0⟩ : ℝ≥0) < β := by exact_mod_cast hγβ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hlim.eventually (lt_mem_nhds hγ')] with n hn
    refine (aGreen_of_not_mem_left fun hD => ?_).symm
    have h1 := (mem_actDom_iff.1 hD).2
    rw [← hγeq] at h1
    exact absurd h1 (not_lt.2 (ENNReal.ofReal_le_ofReal (by exact_mod_cast hn.le)))

end Aux50Ge8

end InteractingSLE
