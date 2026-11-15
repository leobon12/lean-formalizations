/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BnLaw

/-!
# The contact clause in GB6's setting: the theorem (decision D17 (B))

Packet PROVE-GW2-BUF (round 11). **`gapVanishes_contact_gb6`**. GB6's setting is a counterflow `(wα, α)` read at
`s` with `α s ∈ ℍ`, and an explored curve `(w, γ)` with a complete transient trace. Suppose a canonical driver `Wc`
has the relative hulls before the first contact (the stage law of D17 (B)). Suppose its generating trace lives at
least up to the relative life `L = contactLife` (the supremum of the bounded relative clock). Then:

* either the contact is on the right: `V̂^{0,L}_s < 0`, `junctionR ≤ Re ηc(L)`, and every mark `x ≤ Re ηc(L)`
  has a vanishing gap along `Wc` at `L`;
* or the mirror statement holds on the left.

Proof:
* relative times `a(t_n) ↑ L` with `ηc(a(t_n)) ∈ ℍ` (`Supp9D.exists_mem_H_of_isGeneratingTrace`, then the
  intermediate value theorem for the clock);
* the points `γ(t_n)` are interior and safe, with `ηc(a(t_n)) = relMap (γ t_n)` (`canonical_eq_relBdry`);
* `−1/γ(t_n)` converges to a point of `α([0, s])`: the first-contact point, or `α(0) = 0` by transience;
* `contact_side_H` gives the side;
* earlier real chart values lie strictly between the junctions (`GW2BmSide`), the off-condition of
  `GW2BmTip.gapVanishes_of_canonical_off`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel Restart

/-- **The contact clause in GB6's setting, from a canonical driver with the relative hulls.** -/
theorem gapVanishes_contact_gb6 {wα w : ℝ≥0 → ℝ} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hwα : Continuous wα) (hwα0 : wα 0 = 0) (hα : IsGeneratingTrace wα ⊤ α) (hsH : α s ∈ H)
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsGeneratingTrace w ⊤ γ)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) {Wc : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} {ηc : ℝ≥0 → ℂ}
    (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (hη : IsGeneratingTrace Wc ζc ηc)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s →
      fwdHull (rp Wc) (relClk wα w s t) = relMap (rp wα) s '' fwdHull (rp w) t)
    (hbdd : ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s → relClk wα w s t ≤ M)
    (hLζ : ENNReal.ofReal (contactLife wα w α γ s) ≤ ζc) :
    (baseL (rp wα) s < 0 ∧ junctionR (rp wα) s ≤ (ηc (contactLife wα w α γ s).toNNReal).re ∧
        ∀ x : ℝ, x ≤ (ηc (contactLife wα w α γ s).toNNReal).re →
          GapVanishes (rp Wc) x (contactLife wα w α γ s)) ∨
      (0 < baseR (rp wα) s ∧ (ηc (contactLife wα w α γ s).toNNReal).re ≤ junctionL (rp wα) s ∧
        ∀ x : ℝ, (ηc (contactLife wα w α γ s).toNNReal).re ≤ x →
          GapVanishes (fun r => -rp Wc r) (-x) (contactLife wα w α γ s)) := by
  have hs := s_pos_of_tip hα hsH
  have hU := continuous_rp hwα
  have hU0 : rp wα 0 = 0 := by simp [rp, hwα0]
  have hWc' := continuous_rp hWc
  have hWc0' : rp Wc 0 = 0 := by simp [rp, hWc0]
  obtain ⟨ha0, hsm, hac⟩ := relClk_props hwα hwα0 hα hsH hw hw0 hγ
  have hTc : 0 < contactTc α γ s := contactTc_pos hα hγ
  set Tc := contactTc α γ s with hTcdef
  set a := relClk wα w s with hadef
  set L := contactLife wα w α γ s with hLdef
  have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := by rw [ENNReal.coe_zero]; exact hTc
  obtain ⟨M, hM⟩ := hbdd
  set A : Set ℝ := a '' {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} with hAdef
  have hLA : L = sSup A := rfl
  have hAne : A.Nonempty := ⟨a 0, 0, h0Tc, rfl⟩
  have hAbdd : BddAbove A := ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hM t ht⟩
  have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t ≤ L := fun t ht => le_csSup hAbdd ⟨t, ht, rfl⟩
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t < L := by
    intro t ht
    obtain ⟨t', htt', ht'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact (hsm ht ht' (ENNReal.coe_lt_coe.1 htt')).trans_le (hle t' ht')
  have hL0 : 0 < L := by have := hlt 0 h0Tc; rw [ha0] at this; exact this
  -- every relative time before `L` is a clock value before contact
  have hexists : ∀ u ∈ Ico 0 L, ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u := by
    intro u hu
    obtain ⟨_, ⟨t', ht', rfl⟩, hut'⟩ := exists_lt_of_lt_csSup hAne (show u < sSup A from hu.2)
    have hcont : ContinuousOn a (Icc 0 t') :=
      hac.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht'
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t') hcont
      ⟨by rw [ha0]; exact hu.1, hut'.le⟩
    exact ⟨t, lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht', hteq⟩
  obtain ⟨hηL, hcL⟩ := isLoewnerTraceLT_canonical hη hL0 hLζ
  have hB : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      γ t ∈ relSafe (rp wα) s ∧ ηc (a t).toNNReal = relBdry (rp wα) s (γ t) := fun t ht =>
    canonical_eq_relBdry hwα hwα0 hα hsH hw hw0 hγ hWc hWc0 hηL hK hle ht
  -- interior relative times increasing to `L`
  have hseq : ∀ n : ℕ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ L - 1 / ((n : ℝ) + 1) < a t ∧ ηc (a t).toNNReal ∈ H := by
    intro n
    set lo : ℝ := max (L - 1 / ((n : ℝ) + 1)) (L / 2) with hlodef
    have hlo0 : 0 < lo := lt_max_of_lt_right (half_pos hL0)
    have hloL : lo < L := max_lt (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                                     linarith) (by linarith)
    obtain ⟨_, ⟨t', ht', rfl⟩, hlo⟩ := exists_lt_of_lt_csSup hAne (show lo < sSup A from hloL)
    have hat'0 : 0 ≤ a t' := hlo0.le.trans hlo.le
    have hxy : lo.toNNReal < (a t').toNNReal := (Real.toNNReal_lt_toNNReal_iff (hlo0.trans hlo)).2 hlo
    have hy : (((a t').toNNReal : ℝ≥0) : ℝ≥0∞) < ζc :=
      ((ENNReal.ofReal_lt_ofReal_iff hL0).2 (hlt t' ht')).trans_le hLζ
    obtain ⟨z, hz, hzH⟩ := Supp9D.exists_mem_H_of_isGeneratingTrace hη hWc.continuousOn hWc0 hxy hy
    have hz1 : lo < (z : ℝ) := by
      have := hz.1
      rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hlo0.le] at this
    have hz2 : (z : ℝ) < a t' := by
      have := hz.2
      rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hat'0] at this
    have hcont : ContinuousOn a (Icc 0 t') :=
      hac.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht'
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t') hcont
      ⟨by rw [ha0]; exact z.coe_nonneg, hz2.le⟩
    refine ⟨t, lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht', ?_, ?_⟩
    · rw [hteq]; linarith [le_max_left (L - 1 / ((n : ℝ) + 1)) (L / 2)]
    · rw [hteq, Real.toNNReal_coe]; exact hzH
  choose tn htnT htnL htnH using hseq
  have hv : Tendsto (fun n => a (tn n)) atTop (𝓝 L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => L - 1 / ((n : ℝ) + 1)) (h := fun _ => L)
      ?_ tendsto_const_nhds (fun n => (htnL n).le) (fun n => hle _ (htnT n))
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub L
    simpa using this
  -- the physical points
  set P : ℕ → ℂ := fun n => γ (tn n) with hPdef
  have hPsafe : ∀ n, P n ∈ relSafe (rp wα) s := fun n => (hB _ (htnT n)).1
  have hPH : ∀ n, P n ∈ H := fun n => by
    have h1 := (hB _ (htnT n)).2
    have h2 := htnH n
    rw [h1] at h2
    exact (relBdry_mem_H_iff hU hU0 hs.le (hPsafe n)).1 h2
  have hPA : ∀ n, -(P n)⁻¹ ∉ fwdHull (rp wα) s := fun n hK' =>
    (hPsafe n).2 (subset_closure ⟨-(P n)⁻¹, hK', GB6.neg_inv_neg_inv _⟩)
  have hrel : ∀ n, relMap (rp wα) s (P n) = ηc (a (tn n)).toNNReal := fun n => by
    rw [(hB _ (htnT n)).2, relBdry_eq hU hs.le (hPH n) (hPsafe n).2]
  have hL' : Tendsto (fun n => relMap (rp wα) s (P n)) atTop (𝓝 (ηc L.toNNReal)) := by
    have hcw : ContinuousWithinAt (fun u : ℝ => ηc u.toNNReal) (Icc 0 L) L := hcL L ⟨hL0.le, le_rfl⟩
    have hvI : Tendsto (fun n => a (tn n)) atTop (𝓝[Icc 0 L] L) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hv, Eventually.of_forall fun n => ⟨?_, hle _ (htnT n)⟩⟩
      have := htnL n
      have h1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      by_contra hneg
      rw [not_le] at hneg
      have hmono := hsm h0Tc (htnT n)
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ tn n) with h | h
      · rw [← h, ha0] at hneg; exact lt_irrefl _ hneg
      · have := hmono h; rw [ha0] at this; linarith
    exact (hcw.tendsto.comp hvI).congr fun n => (hrel n).symm
  -- `t_n → T_c`
  have hsnTc : ∀ T' : ℝ≥0, (T' : ℝ≥0∞) < Tc → ∀ᶠ n in atTop, T' < tn n := by
    intro T' hT'
    filter_upwards [hv.eventually (lt_mem_nhds (hlt T' hT'))] with n hn
    by_contra hle'
    rw [not_lt] at hle'
    have := hsm.monotoneOn (htnT n) hT' hle'
    linarith
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hαc : ContinuousOn α (Icc 0 s) := hα.2.1.mono fun t _ => show ((t : ℝ≥0) : ℝ≥0∞) ≤ ⊤ from le_top
  obtain ⟨zs, hzs, hzsA⟩ : ∃ zs, Tendsto (fun n => -(P n)⁻¹) atTop (𝓝 zs) ∧ zs ∈ α '' Icc 0 s := by
    rcases eq_top_or_lt_top Tc with hTop | hfin
    · have hsninf : Tendsto tn atTop atTop := by
        rw [Filter.tendsto_atTop]
        intro T'
        exact (hsnTc T' (by rw [hTop]; exact ENNReal.coe_lt_top)).mono fun n h => h.le
      have hn := htr.comp hsninf
      refine ⟨0, ?_, ⟨0, ⟨le_rfl, zero_le⟩, hα.1⟩⟩
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have e : (fun n => ‖-(P n)⁻¹‖) = fun n => (‖γ (tn n)‖)⁻¹ := by
        funext n; simp only [hPdef, norm_neg, norm_inv]
      rw [e]
      exact tendsto_inv_atTop_zero.comp hn
    · obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, Tc = T := ⟨Tc.toNNReal, (ENNReal.coe_toNNReal hfin.ne).symm⟩
      have hsnT' : Tendsto tn atTop (𝓝 T) := by
        refine tendsto_order.2 ⟨fun b hb => hsnTc b (by rw [hT]; exact_mod_cast hb), fun b hb =>
          Eventually.of_forall fun n => lt_trans ?_ hb⟩
        have := htnT n; rw [hT] at this; exact_mod_cast this
      have hAcl : IsClosed ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) := by
        rw [← image_image (fun z : ℂ => (z : OnePoint ℂ)) α]
        exact ((isCompact_Icc.image_of_continuousOn hαc).image OnePoint.continuous_coe).isClosed
      have hηs : Continuous fun t => sphereInv (γ t : OnePoint ℂ) :=
        continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc)
      obtain ⟨t₀, ht₀, hαt₀⟩ := firstContactTime_mem hηs hAcl (T := T) hT
      have hγT : γ T ≠ 0 := by
        intro h0
        have h00 : sphereInv ((0 : ℂ) : OnePoint ℂ) = OnePoint.infty := by simp [sphereInv_coe]
        simp only at hαt₀
        rw [h0, h00] at hαt₀
        exact OnePoint.coe_ne_infty _ hαt₀
      simp only at hαt₀
      rw [sphereInv_coe_of_ne hγT] at hαt₀
      have heq : α t₀ = -(γ T)⁻¹ := OnePoint.coe_injective hαt₀
      refine ⟨α t₀, ?_, ⟨t₀, ht₀, rfl⟩⟩
      rw [heq]
      exact ((continuousAt_inv₀ hγT).neg.tendsto).comp ((hγc.tendsto T).comp hsnT')
  obtain ⟨hLim, hside⟩ := contact_side_H hwα hwα0 hα hPH hPA hzs hzsA hL'
  -- the earlier real chart values
  have hoffR : baseL (rp wα) s < 0 → ∀ u ∈ Ico 0 L, ∀ r : ℝ, junctionR (rp wα) s ≤ r →
      (fun u : ℝ => ηc u.toNNReal) u ≠ r := by
    intro hbL u hu r hr h
    obtain ⟨t, ht, hteq⟩ := hexists u hu
    have h1 := (hB t ht).2
    rw [hteq] at h1
    have := lt_junctionR_of_relBdry_eq hU hU0 hs.le (hB t ht).1 (h1.symm.trans h) hbL
    linarith
  have hoffL : 0 < baseR (rp wα) s → ∀ u ∈ Ico 0 L, ∀ r : ℝ, r ≤ junctionL (rp wα) s →
      (fun u : ℝ => ηc u.toNNReal) u ≠ r := by
    intro hbR u hu r hr h
    obtain ⟨t, ht, hteq⟩ := hexists u hu
    have h1 := (hB t ht).2
    rw [hteq] at h1
    have := junctionL_lt_of_relBdry_eq hU hU0 hs.le (hB t ht).1 (h1.symm.trans h) hbR
    linarith
  rcases hside with ⟨hbL, hjR⟩ | ⟨hbR, hjL⟩
  · left
    refine ⟨hbL, hjR, fun x hx => ?_⟩
    have hjR0 : 0 < junctionR (rp wα) s := by unfold junctionR; exact neg_pos.2 (inv_lt_zero.2 hbL)
    exact gapVanishes_of_canonical_off hWc' hWc0' hL0 (fun _ _ => rfl) hηL hcL hLim hjR0 hjR (hoffR hbL) hx
  · right
    refine ⟨hbR, hjL, fun x hx => ?_⟩
    have hjL0 : junctionL (rp wα) s < 0 := by unfold junctionL; exact neg_lt_zero.2 (inv_pos.2 hbR)
    exact gapVanishes_neg_of_canonical_off hWc' hWc0' hL0 (fun _ _ => rfl) hηL hcL hLim hjL0 hjL (hoffL hbR) hx

end InteractingSLE.Theorem14.GW2Bh
