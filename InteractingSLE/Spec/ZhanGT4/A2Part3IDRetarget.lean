/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripRetarget
import InteractingSLE.Spec.Supplement.BR3RefPath
import InteractingSLE.Spec.Supplement.BR3RefGap
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import InteractingSLE.Spec.Supplement.GW0

/-!
# A.2 part 3, (I1): the retargeted noncollision for a deterministic word

Packet PROVE-ZHAN-A2P3-ID. Source: Astra, *Follow-up proofs*, §A.2 L572–L594
(`source/external/AstraIG1/ig1_followup_proofs.txt`; R38, R53).

Reflected form (all marks on the right, `nL = 0`). Let `(W, V)` be an integrated `SLE_κ(ρ)` evolution of a
distinct word `0 < x₀ < … < x_{j+m}` and retarget at the mark `x_k`, `k = j` (`LP.retargetIdx j m`, `j ≥ 1`), by
`ψ(z) = z/(x_k − z)`. If LP9's transformed word has all group-end sums `≥ κ/2 − 2` on both sides (high-force
noncollision, Aux. lemma 6) and every right partial sum before the target exceeds `−2`, then almost surely:

* **(a)** the nearest mark `x₀` never meets the driver before the separation time (the first meeting of the target
  with the driver);
* **(b)** the new horizon `T̃ = sup_{s < τ_sep} C(s)` is infinite.

Proof. `Sec5.Aux22Strip.exists_retarget_integrated` continues the retargeted process to an integrated evolution of
the transformed word on `P ⊗ P`, agreeing with it before `T̃`. Aux. lemma 6 (`ae_lifetime_eq_top`, `ae_w_lt_vR`, and
its reflection) gives it infinite lifetime and keeps its nearest right mark (the image of `x₀`) and its nearest left
mark (the old target `−1`) off the driver at positive times. Pathwise:

* (a): a meeting of `x₀` with the driver at an original time `t > 0` is a meeting of their images at the new time
  `C(t) > 0`;
* (b): if `T̃ < ∞`, the gap of the new driver to the old target, `X̃ = α/q` (`q = V_k − W`,
  `α = x_k e^{−2∫ q⁻²}`), lies in `[c, N]` along the original time (compactness of `[0, T̃]`). If `τ_sep = ∞` this
  forces `T̃ = ∞` (`BR3Ref.newHorizon_eq_top_of_gap`); otherwise `∫ q⁻² ≤ T̃/c²`, so `α` and hence `q = α/X̃` stay
  above a positive constant (the argument of `BR3Ref.far_gap_of_code`, `exists_gap_lower` here), which contradicts the
  meeting at `τ_sep < ζ` (`lt_sepTime_of_forall`) and, at `τ_sep = ζ < ∞`, the threshold limit of Aux. lemma 3 (only
  a group through the target can be a threshold).

Main result: **`ae_gap_and_newHorizon_top`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2P3ID

open Zhan.Retarget Theorem14.BR3Ref

/-! ### The clock -/

section Clock

variable {xk : ℝ} {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞}

/-- A path read in the new clock at the new time `C(t)` is its value at the original time `t`. -/
theorem newPath_clk (h : SepUpTo w vk T) (hxk : 0 < xk) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (F : ℝ → ℝ) :
    newPath xk w vk F (clk (rate xk w vk) t).toNNReal = F t := by
  have hR := (h.isSep_of_lt ht).isRate hxk
  have hC0 : 0 ≤ clk (rate xk w vk) t := hR.clk_nonneg ⟨t.coe_nonneg, le_rfl⟩
  have hinv : invClk (rate xk w vk) ((clk (rate xk w vk) t).toNNReal : ℝ) = t := by
    rw [Real.coe_toNNReal _ hC0]
    exact hR.invClk_clk ⟨t.coe_nonneg, le_rfl⟩
  simp only [newPath, hinv]

/-- The new time of a positive original time is positive. -/
theorem clk_pos (h : SepUpTo w vk T) (hxk : 0 < xk) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) (ht0 : 0 < t) :
    0 < clk (rate xk w vk) t := by
  have hR := (h.isSep_of_lt ht).isRate hxk
  have h0 : clk (rate xk w vk) 0 = 0 := by simp [clk]
  have := hR.clk_lt ⟨le_rfl, t.coe_nonneg⟩ ⟨t.coe_nonneg, le_rfl⟩ (by exact_mod_cast ht0)
  rwa [h0] at this

/-- **A finite new horizon with the gap to the old target in `[c, N]` keeps the target gap bounded below** (the
argument of `BR3Ref.far_gap_of_code`): `∫₀ˢ q⁻² ≤ C(s)/c² ≤ T̃/c²`, so `α_s ≥ x_k e^{−2T̃/c²}` and
`q_s = α_s/X̃_s ≥ α_s/N`. -/
theorem exists_gap_lower (hd : PullData w vk xk T) (hTn : newHorizon xk w vk T ≠ ⊤) {c N : ℝ} (hc : 0 < c)
    (hN : 0 < N)
    (hX : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → c ≤ alpha xk w vk s / gap w vk s ∧ alpha xk w vk s / gap w vk s ≤ N) :
    ∃ δ > 0, ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → δ ≤ vk s - w s := by
  have hpos := hd.pos
  set Tn := (newHorizon xk w vk T).toNNReal with hTndef
  have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk T := ENNReal.coe_toNNReal hTn
  set δ : ℝ := xk * Real.exp (-2 * ((Tn : ℝ) / c ^ 2)) / N with hδ
  refine ⟨δ, by positivity, fun s hs => ?_⟩
  have hS := hd.sep.isSep_of_lt hs
  have hRt := hS.isRate hpos
  have hq : 0 < gap w vk s := hS.pos s ⟨s.coe_nonneg, le_rfl⟩
  have hclk : clk (rate xk w vk) s ≤ Tn := by
    have hu := clk_lt_newHorizon hd.sep hpos hs
    have h0 : 0 ≤ clk (rate xk w vk) s := hRt.clk_nonneg ⟨s.coe_nonneg, le_rfl⟩
    rw [← hTn', ← ENNReal.ofReal_coe_nnreal] at hu
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 hu).le
  have hint : ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹ ≤ (Tn : ℝ) / c ^ 2 := by
    have hi1 : IntervalIntegrable (fun u => (gap w vk u ^ 2)⁻¹) volume 0 s :=
      (hS.continuousOn_inv_sq.mono (by rw [uIcc_of_le s.coe_nonneg])).intervalIntegrable
    have hi2 := hRt.intervalIntegrable (a := 0) (b := s) ⟨le_rfl, s.coe_nonneg⟩ ⟨s.coe_nonneg, le_rfl⟩
    calc ∫ u in (0 : ℝ)..s, (gap w vk u ^ 2)⁻¹ ≤ ∫ u in (0 : ℝ)..s, (1 / c ^ 2) * rate xk w vk u := by
          refine intervalIntegral.integral_mono_on s.coe_nonneg hi1 (hi2.const_mul _) fun u hu => ?_
          have hu' : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
            lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hu.2)) hs
          have hb := (hX u.toNNReal hu').1
          rw [Real.coe_toNNReal _ hu.1] at hb
          have hqu : 0 < gap w vk u := hS.pos u hu
          have e : rate xk w vk u = (alpha xk w vk u / gap w vk u) ^ 2 * (gap w vk u ^ 2)⁻¹ := by
            unfold rate; field_simp
          rw [e]
          have hc2 : c ^ 2 ≤ (alpha xk w vk u / gap w vk u) ^ 2 := by gcongr
          have hinv : 0 ≤ (gap w vk u ^ 2)⁻¹ := by positivity
          have hc2' : 0 < c ^ 2 := by positivity
          calc (gap w vk u ^ 2)⁻¹ = (1 / c ^ 2) * (c ^ 2 * (gap w vk u ^ 2)⁻¹) := by field_simp
            _ ≤ (1 / c ^ 2) * ((alpha xk w vk u / gap w vk u) ^ 2 * (gap w vk u ^ 2)⁻¹) := by gcongr
      _ = (1 / c ^ 2) * clk (rate xk w vk) s := by rw [intervalIntegral.integral_const_mul]; rfl
      _ ≤ (1 / c ^ 2) * Tn := by gcongr
      _ = (Tn : ℝ) / c ^ 2 := by ring
  have halpha : xk * Real.exp (-2 * ((Tn : ℝ) / c ^ 2)) ≤ alpha xk w vk s := by
    unfold alpha
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hpos.le
    linarith
  have hb2 := (hX s hs).2
  have hXpos : 0 < alpha xk w vk s / gap w vk s := hc.trans_le (hX s hs).1
  have hgap_eq : gap w vk s = alpha xk w vk s / (alpha xk w vk s / gap w vk s) := by
    have ha : alpha xk w vk s ≠ 0 := (alpha_pos hpos w vk s).ne'
    field_simp
  have : δ ≤ gap w vk s := by
    rw [hgap_eq, hδ]
    calc xk * Real.exp (-2 * ((Tn : ℝ) / c ^ 2)) / N ≤ alpha xk w vk s / N := by gcongr
      _ ≤ alpha xk w vk s / (alpha xk w vk s / gap w vk s) := by
          gcongr
          exact (alpha_pos hpos w vk s).le
  simpa [gap] using this

end Clock

/-! ### The pathwise conclusions -/

section Path

variable {κ : ℝ} {j m : ℕ} {xL : Fin 0 → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin 0 → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **A threshold state has the target at the driver** when there are no left marks and every right partial sum
before the target exceeds `−2`: the right marks at the driver form an initial segment, which must reach the
target. -/
theorem vR_eq_of_threshold (hpre : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    {w₀ : ℝ} {vL₀ : Fin 0 → ℝ} {vR₀ : Fin (j + 1 + m) → ℝ} (hmono : Monotone vR₀) (hge : ∀ i, w₀ ≤ vR₀ i)
    (hth : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) : vR₀ (LP.retargetIdx j m) = w₀ := by
  by_contra hne
  rcases hth with hL | hR
  · have h0 : ∑ i ∈ univ.filter (fun i => vL₀ i = w₀), ρL i = 0 := by simp
    rw [h0] at hL
    norm_num at hL
  · have hdown : ∀ i i' : Fin (j + 1 + m), i' ≤ i → vR₀ i = w₀ → vR₀ i' = w₀ := fun i i' hii' hi =>
      le_antisymm ((hmono hii').trans hi.le) (hge i')
    have hlt : ∀ i, vR₀ i = w₀ → (i : ℕ) < j := by
      intro i hi
      by_contra hji
      have hki : LP.retargetIdx j m ≤ i := by
        rw [Fin.le_def]
        simp only [LP.retargetIdx, Fin.val_castAdd, Fin.val_last]
        omega
      exact hne (hdown i _ hki hi)
    have := neg_two_lt_sum_filter_of_down (ρ := ρR) (fun i => vR₀ i = w₀) hdown fun i hi => hpre i (hlt i hi)
    linarith

/-- **(b) along one path**: the new horizon is infinite (the part of `gap_and_horizon_of_agree` that uses only the
old target). -/
theorem horizon_of_agree (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hpre : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin 0 → ℝ) (vR₀ : Fin (j + 1 + m) → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    {gw : ℝ≥0 → ℝ} {gl : Fin (0 + (m + 1)) → ℝ≥0 → ℝ} {gr : Fin j → ℝ≥0 → ℝ}
    (hgw : Continuous gw) (hgl : Continuous (gl ⟨0, by omega⟩)) (hgl0 : gl ⟨0, by omega⟩ 0 < gw 0)
    (hL : ∀ u : ℝ≥0, 0 < u → gl ⟨0, by omega⟩ u < gw u)
    (hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) < Sec5.Aux22Strip.retargetHorizon xR w vR ζ →
      newW xR w vR u = gw u ∧ (∀ i, newVL xR w vL vR i u = gl i u) ∧ ∀ i, newVR xR w vR i u = gr i u) :
    Sec5.Aux22Strip.retargetHorizon xR w vR ζ = ⊤ := by
  set k := LP.retargetIdx j m with hk
  set xk := LP.retargetPos xR with hxk
  set vk := vR k with hvk
  set sep := sepTime w vk ζ with hsepdef
  have hfp := hp.isForcePath
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo (sepTime_le w vk ζ)) hD hj
    fun t ht => lt_of_lt_sepTime ht
  have hd : PullData w vk xk sep := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  have hTdef : Sec5.Aux22Strip.retargetHorizon xR w vR ζ = newHorizon xk w vk sep := rfl
  have e0 : (Fin.natAdd 0 (0 : Fin (m + 1)) : Fin (0 + (m + 1))) = ⟨0, by omega⟩ := Fin.ext (by simp)
  by_contra hTn
  rw [hTdef] at hTn
  set Tn := (newHorizon xk w vk sep).toNNReal with hTndef
  have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk sep := ENNReal.coe_toNNReal hTn
  have hfc : ContinuousOn (fun u => gw u - gl ⟨0, by omega⟩ u) (Icc 0 Tn) := (hgw.sub hgl).continuousOn
  have hfpos : ∀ u ∈ Icc 0 Tn, 0 < gw u - gl ⟨0, by omega⟩ u := by
    intro u _
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | h0
    · rw [← h0]; linarith
    · linarith [hL u h0]
  obtain ⟨c, hc, hcle⟩ := Sec7.exists_pos_le_of_continuousOn_Icc hfc hfpos
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  have hX : ∀ s : ℝ≥0, (s : ℝ≥0∞) < sep →
      c ≤ alpha xk w vk s / gap w vk s ∧ alpha xk w vk s / gap w vk s ≤ max C 1 := by
    intro s hs
    obtain ⟨hu, he⟩ := newTime_gap (vL := vL) hd hs
    have huT : (clk (rate xk w vk) s).toNNReal ≤ Tn := by
      rw [← hTn'] at hu; exact (ENNReal.coe_lt_coe.1 hu).le
    obtain ⟨h1, h2, -⟩ := hag _ hu
    rw [← he, h1, h2, e0]
    refine ⟨hcle _ ⟨zero_le, huT⟩, ?_⟩
    have := hC _ ⟨zero_le, huT⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  rcases eq_or_ne sep ⊤ with hsT | hsT
  · -- an infinite separation time
    have hsepT : SepUpTo w vk ⊤ := hsT ▸ hd.sep
    have hX' : ∀ s : ℝ≥0, c ≤ alpha xk w vk s / gap w vk s := fun s =>
      (hX s (by rw [hsT]; exact ENNReal.coe_lt_top)).1
    have := newHorizon_eq_top_of_gap hsepT hd.pos hc hX'
    exact hTn (by rw [hsT]; exact this)
  · obtain ⟨δ, hδ, hgap⟩ := exists_gap_lower hd hTn hc (lt_max_of_lt_right one_pos) hX
    set S := sep.toNNReal with hSdef
    have hS : (S : ℝ≥0∞) = sep := ENNReal.coe_toNNReal hsT
    have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {s | (s : ℝ≥0∞) < ζ} → (S : ℝ≥0∞) < ζ → ContinuousAt f S :=
      fun hf hSζ => hf.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hSζ)
    -- the gap bound passes to the left limit at `S`
    have hleft : ∀ {L : ℝ}, 0 < S → Tendsto (fun s => vk s - w s) (𝓝[<] S) (𝓝 L) → δ ≤ L := by
      intro L hS0 hL'
      have : NeBot (𝓝[<] S) := nhdsLT_neBot_of_exists_lt ⟨0, hS0⟩
      refine ge_of_tendsto hL' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hgap s (by rw [← hS]; exact_mod_cast hs)
    rcases (sepTime_le w vk ζ).lt_or_eq with hlt | heq
    · -- `τ_sep < ζ`: the target is still strictly right of the driver at `τ_sep`
      have hSζ : (S : ℝ≥0∞) < ζ := by rw [hS]; exact hlt
      have hc' : ContinuousOn (fun s => vk s - w s) {s | (s : ℝ≥0∞) < ζ} :=
        (hfp.continuousOn_vR k).sub hfp.continuousOn_w
      have hall : ∀ s ≤ S, w s < vk s := by
        intro s hsS
        rcases hsS.lt_or_eq with hs | hs
        · have := hgap s (by rw [← hS]; exact_mod_cast hs); linarith
        · rw [hs]
          rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ S) with h0 | h0
          · rw [← h0, hfp.w_zero, hvk, hfp.vR_zero]; exact hd.pos
          · have := hleft h0 ((hca hc' hSζ).tendsto.mono_left nhdsWithin_le_nhds)
            linarith
      have := lt_sepTime_of_forall hc' hSζ hall
      rw [← hsepdef, ← hS] at this
      exact lt_irrefl _ this
    · -- `τ_sep = ζ < ∞`: the threshold limit has the target at the driver
      have hζS : (S : ℝ≥0∞) = ζ := by rw [hS]; exact heq
      have hS0 : 0 < S := by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ S) with h0 | h0
        · exfalso
          have hz : ζ = 0 := by rw [← hζS, ← h0]; rfl
          have hth := hfp.threshold_of_eq_zero hz
          have := vR_eq_of_threshold hpre hD.2.2.monotone (fun i => hD.1.2.2.2 i) hth
          exact hd.pos.ne' this
        · exact h0
      obtain ⟨w₀, vL₀, vR₀, htend, hth⟩ := hlim S hS0 hζS
      have : NeBot (𝓝[<] S) := nhdsLT_neBot_of_exists_lt ⟨0, hS0⟩
      have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] S, (t : ℝ≥0∞) < ζ := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        rw [← hζS]; exact_mod_cast ht
      have hw : Tendsto w (𝓝[<] S) (𝓝 w₀) := htend.fst_nhds
      have hvR : ∀ i, Tendsto (vR i) (𝓝[<] S) (𝓝 (vR₀ i)) := fun i =>
        tendsto_pi_nhds.1 htend.snd_nhds.snd_nhds i
      have hmono : Monotone vR₀ := fun i i' hii' =>
        le_of_tendsto_of_tendsto (hvR i) (hvR i') (hev.mono fun t ht => hfp.monotone_vR ht hii')
      have hge : ∀ i, w₀ ≤ vR₀ i := fun i =>
        le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
      have hk0 := vR_eq_of_threshold hpre hmono hge hth
      have := hleft hS0 ((hvR k).sub hw)
      rw [hk0, sub_self] at this
      linarith

/-- **(a) and (b) along one path.** Let an integrated path of a distinct word without left marks agree, before the
new horizon, with a continuous path `(g_w, g_l, g_r)` whose nearest right mark and nearest left mark (the old target)
stay off the driver at positive times. Then the nearest original mark stays strictly right of the driver before the
separation time, and the new horizon is infinite. -/
theorem gap_and_horizon_of_agree (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hx0 : 0 < xR ⟨0, by omega⟩)
    (hpre : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin 0 → ℝ) (vR₀ : Fin (j + 1 + m) → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    {gw : ℝ≥0 → ℝ} {gl : Fin (0 + (m + 1)) → ℝ≥0 → ℝ} {gr : Fin j → ℝ≥0 → ℝ}
    (hgw : Continuous gw) (hgl : Continuous (gl ⟨0, by omega⟩)) (hgl0 : gl ⟨0, by omega⟩ 0 < gw 0)
    (hR : ∀ u : ℝ≥0, 0 < u → gw u < gr ⟨0, by omega⟩ u)
    (hL : ∀ u : ℝ≥0, 0 < u → gl ⟨0, by omega⟩ u < gw u)
    (hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) < Sec5.Aux22Strip.retargetHorizon xR w vR ζ →
      newW xR w vR u = gw u ∧ (∀ i, newVL xR w vL vR i u = gl i u) ∧ ∀ i, newVR xR w vR i u = gr i u) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < sepTime w (vR (LP.retargetIdx j m)) ζ → w t < vR ⟨0, by omega⟩ t) ∧
      Sec5.Aux22Strip.retargetHorizon xR w vR ζ = ⊤ := by
  set k := LP.retargetIdx j m with hk
  set xk := LP.retargetPos xR with hxk
  set vk := vR k with hvk
  set sep := sepTime w vk ζ with hsepdef
  have hfp := hp.isForcePath
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo (sepTime_le w vk ζ)) hD hj
    fun t ht => lt_of_lt_sepTime ht
  have hd : PullData w vk xk sep := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  have hTdef : Sec5.Aux22Strip.retargetHorizon xR w vR ζ = newHorizon xk w vk sep := rfl
  have e0 : (Fin.natAdd 0 (0 : Fin (m + 1)) : Fin (0 + (m + 1))) = ⟨0, by omega⟩ := Fin.ext (by simp)
  refine ⟨fun t ht => ?_, ?_⟩
  · -- (a): a meeting at `t > 0` is a meeting of the images at the new time `C(t) > 0`
    have htζ : (t : ℝ≥0∞) < ζ := ht.trans_le (sepTime_le _ _ _)
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
    · rw [← h0, hfp.w_zero, hfp.vR_zero]; exact hx0
    · by_contra hcon
      have heq : w t = vR ⟨0, by omega⟩ t := le_antisymm (hfp.w_le_vR htζ _) (not_lt.1 hcon)
      set u := (clk (rate xk w vk) t).toNNReal with hu
      have hu0 : 0 < u := Real.toNNReal_pos.2 (clk_pos hd.sep hd.pos ht h0)
      have huT : (u : ℝ≥0∞) < Sec5.Aux22Strip.retargetHorizon xR w vR ζ := hd.clk_lt ht
      obtain ⟨h1, -, h3⟩ := hag u huT
      have e1 : newW xR w vR u = mobPath xk w vk w t := newPath_clk hd.sep hd.pos ht _
      have e2 : newVR xR w vR ⟨0, by omega⟩ u =
          mobPath xk w vk (vR (Fin.castAdd m (⟨0, by omega⟩ : Fin j).castSucc)) t :=
        newPath_clk hd.sep hd.pos ht _
      have e3 : (Fin.castAdd m (⟨0, by omega⟩ : Fin j).castSucc : Fin (j + 1 + m)) = ⟨0, by omega⟩ := Fin.ext rfl
      have := hR u hu0
      rw [← h1, ← h3 ⟨0, by omega⟩, e1, e2, e3] at this
      simp only [mobPath, Real.toNNReal_coe] at this
      rw [heq] at this
      exact lt_irrefl _ this
  · exact horizon_of_agree hp hD hj hpre hlim hgw hgl hgl0 hL hag
end Path

/-! ### The probabilistic statement -/

/-- An almost sure property of the first coordinate under `P ⊗ P` holds `P`-almost surely. -/
theorem ae_of_ae_prod_fst {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Φ : Ω → Prop} (h : ∀ᵐ p ∂(P.prod P), Φ p.1) : ∀ᵐ ω ∂P, Φ ω := by
  rw [ae_iff] at h ⊢
  have e : {p : Ω × Ω | ¬ Φ p.1} = {ω | ¬ Φ ω} ×ˢ (univ : Set Ω) := by ext p; simp
  rw [e, Measure.prod_prod, measure_univ, mul_one] at h
  exact h

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {j m : ℕ} {xL : Fin 0 → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin 0 → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ}
  {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **(I1)'s retargeted noncollision for a deterministic word** (reflected form, no left marks). For a distinct word
`0 < x₀ < … < x_{j+m}`, `j ≥ 1`, whose right partial sums before the target `x_j` exceed `−2` and whose LP9 transform
at `x_j` has all group-end sums `≥ κ/2 − 2`, every integrated evolution satisfies almost surely: `W < V₀` before the
separation time, and the new horizon of the separation time is infinite. -/
theorem ae_gap_and_newHorizon_top (hκ : 0 < κ) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hx0 : 0 < xR ⟨0, by omega⟩)
    (hpre : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hnL : Sec4.HasGroupEndSums (κ / 2 - 2) (LP.retargetρL κ ρL ρR) (-LP.retargetXL xL xR))
    (hnR : Sec4.HasGroupEndSums (κ / 2 - 2) (LP.retargetρR ρR) (LP.retargetXR xR))
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ≥0∞) < sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω) →
        W t ω < VR ⟨0, by omega⟩ t ω) ∧
      Sec5.Aux22Strip.retargetHorizon xR (W · ω) (fun i t => VR i t ω) (ζ ω) = ⊤ := by
  have hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := fun h =>
    (LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj).ne'
      (vR_eq_of_threshold hpre hD.2.2.monotone (fun i => hD.1.2.2.2 i) h)
  obtain ⟨𝓖, B', gW, gL, gR, ζG, hG, hag⟩ := Sec5.Aux22Strip.exists_retarget_integrated hκ hD hj hE hseed
  have hF' := (LP.isDistinctForceWord_retarget hD hj).1
  have hζG := hG.ae_lifetime_eq_top hκ hF' hnL hnR
  have hRn := hG.ae_w_lt_vR hκ hF' hnR hζG (by omega : 0 < j)
  have hFr : IsOrderedForceWord (-LP.retargetXR xR) (-LP.retargetXL xL xR) :=
    ⟨hF'.2.2.1.neg, fun i => by simp [hF'.2.2.2 i], hF'.1.neg, fun i => by simp [hF'.2.1 i]⟩
  have hLn := hG.reflect.ae_w_lt_vR hκ hFr hnL hζG (by omega : 0 < 0 + (m + 1))
  have hpath := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hE.ae_isIntegratedSLEPath
  have hlimE := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae (hE.ae_tendsto_threshold hκ)
  refine ae_of_ae_prod_fst (P := P)
    (Φ := fun ω => (∀ t : ℝ≥0, (t : ℝ≥0∞) < sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω) →
        W t ω < VR ⟨0, by omega⟩ t ω) ∧
      Sec5.Aux22Strip.retargetHorizon xR (W · ω) (fun i t => VR i t ω) (ζ ω) = ⊤) ?_
  filter_upwards [hag, hζG, hRn, hLn, hpath, hlimE, hG.ae_isIntegratedSLEPath] with p hagp hζp hRp hLp hpp hlp hGp
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ζG p} = univ := by ext t; simp [hζp]
  have hGf := hGp.isForcePath
  have hgw : Continuous fun u => gW u p := continuousOn_univ.1 (hset ▸ hGf.continuousOn_w)
  have hgl : Continuous fun u => gL ⟨0, by omega⟩ u p := continuousOn_univ.1 (hset ▸ hGf.continuousOn_vL _)
  have hgl0 : gL ⟨0, by omega⟩ 0 p < gW 0 p := by
    rw [hGf.vL_zero, hGf.w_zero]
    have e0 : (⟨0, by omega⟩ : Fin (0 + (m + 1))) = Fin.natAdd 0 (0 : Fin (m + 1)) := Fin.ext (by simp)
    rw [e0, LP.retargetXL, Fin.append_right, Fin.cons_zero]
    norm_num
  refine gap_and_horizon_of_agree hpp hD hj hx0 hpre hlp hgw hgl hgl0 (fun u hu => hRp u hu)
    (fun u hu => ?_) hagp.2
  have := hLp u hu
  simpa using this

/-- **(b) alone, with only the old target protected.** For a distinct word as in `ae_gap_and_newHorizon_top`, but
with LP9's transformed word only required to have all group-end sums `> −2` on the right (`GW0`'s infinite lifetime)
and `≥ κ/2 − 2` on the left (the old target and the marks beyond it), the new horizon is almost surely infinite. Used
with an auxiliary weight-zero mark before a target that is the nearest mark. -/
theorem ae_newHorizon_top_weak (hκ : 0 < κ) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hpre : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hnL : Sec4.HasGroupEndSums (κ / 2 - 2) (LP.retargetρL κ ρL ρR) (-LP.retargetXL xL xR))
    (hnR : Theorem14.GW0.RightGroupEndsAdmissible (LP.retargetXR xR) (LP.retargetρR ρR))
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, Sec5.Aux22Strip.retargetHorizon xR (W · ω) (fun i t => VR i t ω) (ζ ω) = ⊤ := by
  have hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := fun h =>
    (LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj).ne'
      (vR_eq_of_threshold hpre hD.2.2.monotone (fun i => hD.1.2.2.2 i) h)
  obtain ⟨𝓖, B', gW, gL, gR, ζG, hG, hag⟩ := Sec5.Aux22Strip.exists_retarget_integrated hκ hD hj hE hseed
  have hF' := (LP.isDistinctForceWord_retarget hD hj).1
  have hnL' : Theorem14.GW0.LeftGroupEndsAdmissible (LP.retargetXL xL xR) (LP.retargetρL κ ρL ρR) :=
    fun i hi => by
      have := hnL i fun i' hii' => by have := hi i' hii'; simp only [Pi.neg_apply]; linarith
      linarith
  have hζG := Theorem14.GW0.ae_lifetime_eq_top_of_neg_two_lt hF' hnL' hnR hG
  have hFr : IsOrderedForceWord (-LP.retargetXR xR) (-LP.retargetXL xL xR) :=
    ⟨hF'.2.2.1.neg, fun i => by simp [hF'.2.2.2 i], hF'.1.neg, fun i => by simp [hF'.2.1 i]⟩
  have hLn := hG.reflect.ae_w_lt_vR hκ hFr hnL hζG (by omega : 0 < 0 + (m + 1))
  have hpath := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hE.ae_isIntegratedSLEPath
  have hlimE := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae (hE.ae_tendsto_threshold hκ)
  refine ae_of_ae_prod_fst (P := P)
    (Φ := fun ω => Sec5.Aux22Strip.retargetHorizon xR (W · ω) (fun i t => VR i t ω) (ζ ω) = ⊤) ?_
  filter_upwards [hag, hζG, hLn, hpath, hlimE, hG.ae_isIntegratedSLEPath] with p hagp hζp hLp hpp hlp hGp
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < ζG p} = univ := by ext t; simp [hζp]
  have hGf := hGp.isForcePath
  have hgw : Continuous fun u => gW u p := continuousOn_univ.1 (hset ▸ hGf.continuousOn_w)
  have hgl : Continuous fun u => gL ⟨0, by omega⟩ u p := continuousOn_univ.1 (hset ▸ hGf.continuousOn_vL _)
  have hgl0 : gL ⟨0, by omega⟩ 0 p < gW 0 p := by
    rw [hGf.vL_zero, hGf.w_zero]
    have e0 : (⟨0, by omega⟩ : Fin (0 + (m + 1))) = Fin.natAdd 0 (0 : Fin (m + 1)) := Fin.ext (by simp)
    rw [e0, LP.retargetXL, Fin.append_right, Fin.cons_zero]
    norm_num
  refine horizon_of_agree hpp hD hj hpre hlp hgw hgl hgl0 (fun u hu => ?_) hagp.2
  have := hLp u hu
  simpa using this

end Prob

end InteractingSLE.ZhanGT4.A2P3ID
