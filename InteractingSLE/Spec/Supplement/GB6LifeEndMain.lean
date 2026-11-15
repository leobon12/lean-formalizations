/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LifeEnd

/-!
# Proposition GB6, step (e): the endpoint argument from the base statement

Packet PROVE-GB6D. **`gb6EndpointStatement_of_base`**: `GB6BaseStatement → GB6EndpointStatement` (the argument is in the
module docstring of `GB6LifeEnd.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp8

namespace GB6

/-- **The endpoint argument, core** (the setup of `isGB6ChartContinuation_of_relHulls` given as hypotheses: the flow
driver frozen after `s` as `U'`, the relative clock `a` strictly increasing and continuous before `T_c`, with supremum
`ζ` approximated from below). -/
theorem gb6Endpoint_core (hB : GB6BaseStatement) {wα w V : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ Γ : ℝ≥0 → ℂ} {s : ℝ≥0}
    (hα : IsGeneratingTrace wα Tα α) (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0)
    (hs : (s : ℝ≥0∞) < Tα) (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) (hΓ : IsGeneratingTrace V ⊤ Γ) (hV : Continuous V) (hV0 : V 0 = 0)
    (hΓtr : Tendsto (fun t => ‖Γ t‖) atTop atTop) {U' : ℝ → ℝ} (hU' : Continuous U') (hU'0 : U' 0 = 0)
    (hagree_s : ∀ r ∈ Icc (0 : ℝ) s, wα r.toNNReal = U' r)
    (hhull : QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) s = QuantumZipper.fwdHull U' s)
    (hγc : Continuous γ) (hαc : ContinuousOn α (Icc 0 s))
    (hsm : StrictMonoOn (fun t : ℝ≥0 => relClock U' s (fun r : ℝ => w r.toNNReal) t)
      {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)})
    (hac : ContinuousOn (fun t : ℝ≥0 => relClock U' s (fun r : ℝ => w r.toNNReal) t)
      {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)})
    (ha0 : relClock U' s (fun r : ℝ => w r.toNNReal) 0 = 0)
    (hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) → 0 ≤ relClock U' s (fun r : ℝ => w r.toNNReal) t)
    (hK' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      QuantumZipper.fwdHull (fun r : ℝ => V r.toNNReal) (relClock U' s (fun r : ℝ => w r.toNNReal) t) =
        relMap U' s '' QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t)
    (hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) →
      ∀ x ∈ QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) t, -x⁻¹ ∉ QuantumZipper.fwdHull U' s)
    (hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) → γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U' s)
    {ζ : ℝ} (hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) → relClock U' s (fun r : ℝ => w r.toNNReal) t ≤ ζ)
    (hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) → relClock U' s (fun r : ℝ => w r.toNNReal) t < ζ)
    (happ : ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
        ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) ∧ ζ - ε < relClock U' s (fun r : ℝ => w r.toNNReal) t)
    (hζpos : 0 < ζ) :
    ∃ u : ℝ≥0, (Γ u).im = 0 ∧
      (junctionR (fun r : ℝ => wα r.toNNReal) s ≤ (Γ u).re ∨ (Γ u).re ≤ junctionL (fun r : ℝ => wα r.toNNReal) s) := by
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set a : ℝ≥0 → ℝ := fun t => relClock U' s (fun r : ℝ => w r.toNNReal) t with hadef
  have hΓc : Continuous Γ := by
    have := hΓ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hdense := (transientDenseQ_of_isGeneratingTrace hΓ hV hV0 hΓtr).2
  -- relative times `v_n ↑ ζ` with `Γ(v_n) ∈ ℍ`, as clock values
  have hseq : ∀ n : ℕ, ∃ sn : ℝ≥0, (sn : ℝ≥0∞) < Tc ∧ ζ - 1 / ((n : ℝ) + 1) < a sn ∧ a sn ≤ ζ ∧
      Γ (a sn).toNNReal ∈ H := by
    intro n
    have hεpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨tn, htn, htnlt⟩ := happ (min (1 / ((n : ℝ) + 1)) (ζ / 2)) (lt_min hεpos (by linarith))
    have hlo : max (ζ - 1 / ((n : ℝ) + 1)) (ζ / 2) < a tn := by
      rw [max_lt_iff]
      constructor
      · linarith [min_le_left (1 / ((n : ℝ) + 1)) (ζ / 2)]
      · linarith [min_le_right (1 / ((n : ℝ) + 1)) (ζ / 2)]
    obtain ⟨q₁, hq₁, hq₁'⟩ := exists_rat_btwn hlo
    obtain ⟨q₂, hq₂, hq₂'⟩ := exists_rat_btwn hq₁'
    have hq₁0 : (0 : ℝ) ≤ q₁ := by linarith [le_max_right (ζ - 1 / ((n : ℝ) + 1)) (ζ / 2)]
    obtain ⟨q, hq1, hq2, hqH⟩ := hdense q₁ q₂ (by exact_mod_cast hq₁0) (by exact_mod_cast hq₂)
    have hcont : ContinuousOn a (Icc 0 tn) :=
      hac.mono fun t ht => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) htn
    have hq1' : (q₁ : ℝ) < q := by exact_mod_cast hq1
    have hq2' : (q : ℝ) < q₂ := by exact_mod_cast hq2
    have hmem : (q : ℝ) ∈ Icc (a 0) (a tn) := ⟨by rw [show a 0 = 0 from ha0]; linarith, by linarith⟩
    obtain ⟨sn, hsn, hsnq⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ tn) hcont hmem
    have hsnT : (sn : ℝ≥0∞) < Tc := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hsn.2) htn
    refine ⟨sn, hsnT, ?_, hle sn hsnT, ?_⟩
    · rw [hsnq]; linarith [le_max_left (ζ - 1 / ((n : ℝ) + 1)) (ζ / 2)]
    · rw [hsnq]; exact hqH
  choose sn hsnT hsnζ hsnle hsnH using hseq
  have hv : Tendsto (fun n => a (sn n)) atTop (𝓝 ζ) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => ζ - 1 / ((n : ℝ) + 1)) (h := fun _ => ζ)
      ?_ tendsto_const_nhds (fun n => (hsnζ n).le) hsnle
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_sub ζ
    simpa using this
  have hrt : ∀ n, γ (sn n) ∈ H ∧ Γ (a (sn n)).toNNReal = relMap U' s (γ (sn n)) := fun n =>
    relTrace_eq hw hw0 hU' hU'0 (NNReal.coe_nonneg s) hγ hV hV0 hΓ hsm hnn hK' hdom hγdom (hsnT n) (hsnH n)
  set L := Γ ζ.toNNReal with hLdef
  have hΓv : Tendsto (fun n => Γ (a (sn n)).toNNReal) atTop (𝓝 L) :=
    (hΓc.tendsto _).comp ((continuous_real_toNNReal.tendsto ζ).comp hv)
  -- `s_n → T_c`
  have hsnTc : ∀ T' : ℝ≥0, (T' : ℝ≥0∞) < Tc → ∀ᶠ n in atTop, T' < sn n := by
    intro T' hT'
    filter_upwards [hv.eventually (lt_mem_nhds (hlt T' hT'))] with n hn
    by_contra hle'
    push Not at hle'
    have := hsm.monotoneOn (hsnT n) hT' hle'
    linarith
  -- the physical points and their limit on the flow prefix
  set z : ℕ → ℂ := fun n => -(γ (sn n))⁻¹ with hzdef
  have hzK : ∀ n, z n ∈ H \ QuantumZipper.fwdHull U' s := fun n =>
    ⟨neg_inv_mem_H (hrt n).1, hγdom _ (hsnT n) (hrt n).1⟩
  obtain ⟨zs, hzs, hzsA⟩ : ∃ zs, Tendsto z atTop (𝓝 zs) ∧ zs ∈ α '' Icc 0 s := by
    rcases eq_top_or_lt_top Tc with hTop | hfin
    · have hsninf : Tendsto sn atTop atTop := by
        rw [tendsto_atTop]
        intro T'
        exact (hsnTc T' (by rw [hTop]; exact ENNReal.coe_lt_top)).mono fun n h => h.le
      have hn := htr.comp hsninf
      refine ⟨0, ?_, ⟨0, ⟨le_rfl, zero_le⟩, hα.1⟩⟩
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have e : (fun n => ‖z n‖) = fun n => (‖γ (sn n)‖)⁻¹ := by
        funext n; simp only [hzdef, norm_neg, norm_inv]
      rw [e]
      exact tendsto_inv_atTop_zero.comp hn
    · obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, Tc = T := ⟨Tc.toNNReal, (ENNReal.coe_toNNReal hfin.ne).symm⟩
      have hsnT' : Tendsto sn atTop (𝓝 T) := by
        refine tendsto_order.2 ⟨fun b hb => hsnTc b (by rw [hT]; exact_mod_cast hb), fun b hb =>
          Eventually.of_forall fun n => lt_trans ?_ hb⟩
        have := hsnT n; rw [hT] at this; exact_mod_cast this
      have hAcl : IsClosed ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s) := by
        rw [← image_image (fun z : ℂ => (z : OnePoint ℂ)) α]
        exact ((isCompact_Icc.image_of_continuousOn hαc).image OnePoint.continuous_coe).isClosed
      have hη : Continuous fun t => sphereInv (γ t : OnePoint ℂ) :=
        continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγc)
      obtain ⟨t₀, ht₀, hαt₀⟩ := firstContactTime_mem hη hAcl (T := T) hT
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
  -- `L` is real
  have hfz : ∀ n, QuantumZipper.fwdMap U' s (z n) = -(Γ (a (sn n)).toNNReal)⁻¹ := fun n => by
    rw [(hrt n).2, relMap, neg_inv_neg_inv]
  have hLnotH : L ∉ H := by
    intro hLH
    have hzeq : ∀ n, z n = QuantumZipper.fwdMapInv U' s (-(Γ (a (sn n)).toNNReal)⁻¹) := fun n => by
      rw [← hfz n, QuantumZipper.RS.fwdMapInv_fwdMap hU' hU'0 (NNReal.coe_nonneg s) (hzK n)]
    have h1 : Tendsto (fun n => -(Γ (a (sn n)).toNNReal)⁻¹) atTop (𝓝[H] (-L⁻¹)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hΓv.inv₀ (ne_zero_of_mem_H hLH)).neg,
        Eventually.of_forall fun n => neg_inv_mem_H (hsnH n)⟩
    have h2 := (continuousOn_fwdMapInv hU' hU'0 (NNReal.coe_nonneg s) _ (neg_inv_mem_H hLH)).tendsto
    have hlim : Tendsto z atTop (𝓝 (QuantumZipper.fwdMapInv U' s (-L⁻¹))) := by
      have e : z = fun n => QuantumZipper.fwdMapInv U' s (-(Γ (a (sn n)).toNNReal)⁻¹) := funext hzeq
      rw [e]; exact h2.comp h1
    have hq := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU' hU'0 (NNReal.coe_nonneg s) (neg_inv_mem_H hLH)
    rw [← tendsto_nhds_unique hzs hlim] at hq
    have hfill := Sec5.CrossRestart.inter_H_subset_of_isFilling (hα.2.2 s hs) ⟨hzsA, hq.1⟩
    rw [hhull] at hfill
    exact hq.2 hfill
  have hLHbar : L ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hΓ hV.continuousOn hV0 le_top
  have hLim : L.im = 0 := le_antisymm (not_lt.1 hLnotH) hLHbar
  -- `L ≠ 0` (uniform displacement)
  have hL0 : L ≠ 0 := by
    intro hL0
    obtain ⟨M', hM'⟩ : ∃ M', ∀ r ∈ Icc (0 : ℝ) s, |U' r| ≤ M' := by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hU'.continuousOn
      exact ⟨C, fun r hr => by simpa [Real.norm_eq_abs] using hC r hr⟩
    have hdisp : ∀ n, ‖QuantumZipper.fwdMap U' s (z n) - z n‖ ≤ 24 * M' + 8 * Real.sqrt s := fun n =>
      norm_fwdMap_sub_self_le hU' hU'0 (NNReal.coe_nonneg s) hM' (hzK n) ⟨NNReal.coe_nonneg s, le_rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, ∀ n, ‖z n‖ ≤ B := by
      obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto z hzs).exists_norm_le
      exact ⟨B, fun n => hB _ ⟨n, rfl⟩⟩
    have hinf : Tendsto (fun n => ‖QuantumZipper.fwdMap U' s (z n)‖) atTop atTop := by
      have e : (fun n => ‖QuantumZipper.fwdMap U' s (z n)‖) = fun n => (‖Γ (a (sn n)).toNNReal‖)⁻¹ := by
        funext n; rw [hfz, norm_neg, norm_inv]
      rw [e]
      have h0 : Tendsto (fun n => ‖Γ (a (sn n)).toNNReal‖) atTop (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => norm_pos_iff.2 (ne_zero_of_mem_H (hsnH n))⟩
        have := (continuous_norm.tendsto L).comp hΓv
        rw [hL0, norm_zero] at this
        exact this
      exact tendsto_inv_nhdsGT_zero.comp h0
    obtain ⟨n, hn⟩ := (hinf.eventually_gt_atTop (B + (24 * M' + 8 * Real.sqrt s))).exists
    have h1 : ‖QuantumZipper.fwdMap U' s (z n)‖ ≤ ‖QuantumZipper.fwdMap U' s (z n) - z n‖ + ‖z n‖ := by
      have := norm_add_le (QuantumZipper.fwdMap U' s (z n) - z n) (z n)
      rwa [sub_add_cancel] at this
    linarith [hdisp n, hB n]
  -- the base statement at `y = −1/L`
  have hLre : L = (L.re : ℂ) := Complex.ext rfl (by simp [hLim])
  have hLre0 : L.re ≠ 0 := fun h => hL0 (by rw [hLre, h, Complex.ofReal_zero])
  set y : ℝ := -(L.re)⁻¹ with hydef
  have hy0 : y ≠ 0 := neg_ne_zero.2 (inv_ne_zero hLre0)
  have hyconv : Tendsto (fun n => QuantumZipper.fwdMap (fun r : ℝ => wα r.toNNReal) s (z n)) atTop (𝓝 (y : ℂ)) := by
    have e : ∀ n, QuantumZipper.fwdMap (fun r : ℝ => wα r.toNNReal) s (z n) = QuantumZipper.fwdMap U' s (z n) :=
      fun n => fwdMap_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s
    simp_rw [e, hfz]
    have hy : (y : ℂ) = -L⁻¹ := by
      rw [hLre, hydef]; push_cast; ring
    rw [hy]
    exact (hΓv.inv₀ hL0).neg
  have hzK' : ∀ n, z n ∈ H \ QuantumZipper.fwdHull (fun r : ℝ => wα r.toNNReal) s := fun n => by
    rw [hhull]; exact hzK n
  obtain ⟨hyL, hyR⟩ := hB wα Tα α s hα hwα hwα0 hs z zs y hzK' hzs hzsA hyconv
  refine ⟨ζ.toNNReal, hLim, ?_⟩
  have hLy : L.re = -y⁻¹ := by rw [hydef, inv_neg, inv_inv, neg_neg]
  show junctionR _ s ≤ L.re ∨ L.re ≤ junctionL _ s
  rw [hLy]
  rcases lt_or_gt_of_ne hy0 with hyn | hyp
  · left
    have hbL : baseL (fun r : ℝ => wα r.toNNReal) s < 0 := lt_of_le_of_lt hyL hyn
    unfold junctionR
    have := (inv_le_inv_of_neg hyn hbL).2 hyL
    linarith
  · right
    have hbR : 0 < baseR (fun r : ℝ => wα r.toNNReal) s := lt_of_lt_of_le hyp hyR
    unfold junctionL
    have := (inv_le_inv₀ hbR hyp).2 hyR
    linarith

/-- **GB6, step (e), deterministic half, from the base statement.** -/
theorem gb6EndpointStatement_of_base (hB : GB6BaseStatement) : GB6EndpointStatement := by
  intro wα w V Tα α γ Γ s hα hwα hwα0 hs hsH hγ hw hw0 htr hΓ hV hV0 hΓtr hK hbdd
  set Tc := firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ)) ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)
    with hTcdef
  set Ur : ℝ → ℝ := fun r => wα r.toNNReal with hUr
  set Wr : ℝ → ℝ := fun r => w r.toNNReal with hWr
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  -- the flow driver frozen after a time `t₂ ∈ (s, Tα)`
  obtain ⟨t₂, hst₂, ht₂⟩ := exists_real_btwn_of_lt hs
  set U' : ℝ → ℝ := frozenDrive wα t₂ with hU'def
  have hU' : Continuous U' := continuous_frozenDrive_of_lt hwα ht₂
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans (NNReal.coe_nonneg s) hst₂.le
  have hU'0 : U' 0 = 0 := by rw [hU'def, frozenDrive_zero ht₂0, hwα0]
  have hagree : ∀ r ∈ Icc (0 : ℝ) t₂, Ur r = U' r := fun r hr => (frozenDrive_eq hr).symm
  have hagree_s : ∀ r ∈ Icc (0 : ℝ) s, Ur r = U' r := fun r hr => hagree r ⟨hr.1, hr.2.trans hst₂.le⟩
  have hrel : relMap Ur s = relMap U' s := relMap_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s
  have hclock : relClock Ur s Wr = relClock U' s Wr := relClock_eq_of_eqOn (NNReal.coe_nonneg s) hagree_s Wr
  have hhull : QuantumZipper.fwdHull Ur s = QuantumZipper.fwdHull U' s :=
    fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
  have htip : Tendsto (QuantumZipper.fwdMapInv U' s) (𝓝[H] 0) (𝓝 (α s)) := by
    have h1 := IsGeneratingTrace.tendsto_fwdMapInv_tip hα hwα hwα0 hs
    have h2 : QuantumZipper.fwdMapInv Ur s = QuantumZipper.fwdMapInv U' s :=
      fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg s) hst₂ hagree
    rw [← h2]
    exact h1
  have hd : ∀ T : ℝ≥0, (T : ℝ≥0∞) < Tc → Disjoint (closure (QuantumZipper.fwdHull U' s))
      (closure ((fun w : ℂ => -w⁻¹) '' QuantumZipper.fwdHull Wr T)) := fun T hT => by
    rw [← hhull]
    exact disjoint_closure_fwdHull_of_lt_firstContactTime hα hwα hwα0 hγ hw.continuousOn hw0 hs
      ENNReal.coe_lt_top hT
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hαc : ContinuousOn α (Icc 0 s) := hα.2.1.mono fun t ht => le_trans (by exact_mod_cast ht.2) hs.le
  have hTc : 0 < Tc := by
    have hk : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hαc
    have := firstContactTime_pos hγc.continuousAt hγ.1 hk.isBounded
    rwa [image_image] at this
  have hγK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → IsFilling (QuantumZipper.fwdHull Wr t) (γ '' Icc 0 t) :=
    fun t _ => hγ.2.2 t ENNReal.coe_lt_top
  obtain ⟨-, -, ha0, hsm, hac, -, -⟩ := exists_glued_relChain hw hw0 hU' hU'0 hs0 htip hTc hd hγK
  set a : ℝ≥0 → ℝ := fun t => relClock U' s Wr t with hadef
  have h0Tc : ((0 : ℝ≥0) : ℝ≥0∞) < Tc := by rw [ENNReal.coe_zero]; exact hTc
  have hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t := fun t ht => by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact ha0.ge
    · have := hsm h0Tc ht h
      rw [show a 0 = 0 from ha0] at this
      exact this.le
  have hK' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      QuantumZipper.fwdHull (fun r : ℝ => V r.toNNReal) (a t) = relMap U' s '' QuantumZipper.fwdHull Wr t :=
    fun t ht => by rw [← hrel]; show _ = _; rw [hadef]; simp only; rw [← hclock]; exact hK t ht
  have hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
      ∀ x ∈ QuantumZipper.fwdHull Wr t, -x⁻¹ ∉ QuantumZipper.fwdHull U' s := fun t ht x hx hxK =>
    Set.disjoint_left.1 (hd t ht) (subset_closure hxK) (subset_closure ⟨x, hx, rfl⟩)
  have hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U' s := by
    intro t ht hγt
    obtain ⟨T', htT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have hmem : γ t ∈ QuantumZipper.fwdHull Wr T' :=
      Sec5.CrossRestart.inter_H_subset_of_isFilling (hγ.2.2 T' ENNReal.coe_lt_top)
        ⟨⟨t, ⟨zero_le, (ENNReal.coe_lt_coe.1 htT').le⟩, rfl⟩, hγt⟩
    exact hdom T' hT' _ hmem
  -- the supremum of the bounded clock
  obtain ⟨M, hM⟩ := hbdd
  have hM' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t ≤ M := fun t ht => by
    have := hM t ht; rw [hclock] at this; exact this
  set A : Set ℝ := a '' {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} with hAdef
  have hAne : A.Nonempty := ⟨a 0, 0, h0Tc, rfl⟩
  have hAbdd : BddAbove A := ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hM' t ht⟩
  set ζ := sSup A with hζdef
  have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t ≤ ζ := fun t ht => le_csSup hAbdd ⟨t, ht, rfl⟩
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → a t < ζ := by
    intro t ht
    obtain ⟨t', htt', ht'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact (hsm ht ht' (ENNReal.coe_lt_coe.1 htt')).trans_le (hle t' ht')
  have hζpos : 0 < ζ := by have := hlt 0 h0Tc; rw [show a 0 = 0 from ha0] at this; exact this
  have happ : ∀ ε > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ ζ - ε < a t := by
    intro ε hε
    obtain ⟨_, ⟨t, ht, rfl⟩, htlt⟩ := exists_lt_of_lt_csSup hAne (show ζ - ε < ζ by linarith)
    exact ⟨t, ht, htlt⟩
  exact gb6Endpoint_core hB hα hwα hwα0 hs hγ hw hw0 htr hΓ hV hV0 hΓtr hU' hU'0 hagree_s hhull hγc hαc hsm hac ha0
    hnn hK' hdom hγdom hle hlt happ hζpos

end GB6

end Supp8

end InteractingSLE
