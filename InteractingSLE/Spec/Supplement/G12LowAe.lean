/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12LowLim

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the budget is almost surely finite on the picture

Packet PROVE-G12C. For an integrated `SLE_κ(ρ)` evolution, an inner right mark `x_k > 0` and a farther right mark
`x_{j₀}`, with reference weight `S ≤ −2` at `k` and `b₊ = S + ρ_Y + 4 − κ/2 > 0`: almost surely, whenever the
picture `LowPic` holds after a rational restart time `q` up to `T_e` with drift energy `≤ κC`, the two-mark budget
`∫_q^t β` stays bounded for `t ∈ [q, T_e)` (`ae_lowBudget_bounded`).

Proof: for fixed `q`, `C` and a level `K`, the event that the budget exceeds `K` on the picture is contained in
`⋃_N ⋂_{n ≥ N} {Z_n ≥ K/(2c₃)}` (`exists_le_lowStop`, `budget_le_lowZ`), whose probability is at most
`2c₃(C + 3)/K` (`measureReal_lowZ_ge_le`); letting `K → ∞` and taking the countable union over `(q, C)` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12Low

open G12 (GCoord coordG densG locG coordAtG clockAt rhoY)
open Supp8.GB5 (IsGBGood)
open GB7a Girsanov

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {k j₀ : Fin nR} {S : ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {q : ℝ≥0} {C n : ℕ}

section Fixed

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
  (hTn : ∀ n ω, T n ω ≤ n) (hTm : ∀ ω, Monotone fun n => T n ω) (hy : 0 < xR j₀) (hxk : 0 < xR k)
  (hkj : k ≤ j₀) (hkjx : xR k < xR j₀)

include hgood hTn hy hxk hkj hkjx in
theorem intervalIntegrable_lowBudget {ω : Ω} (hω : ω ∈ G) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) :
    IntervalIntegrable (lowBudget W VR k j₀ ω) volume a b := by
  have hF := (hgood ω hω).1.isForcePath
  have hIcc : ∀ s ∈ Icc a b, s ∈ Icc (0 : ℝ) (lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω) :=
    fun s hs => ⟨ha.trans hs.1, hs.2.trans hb⟩
  have hmaps : MapsTo Real.toNNReal (Icc a b) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := fun r hr =>
    lt_zeta_of_le hgood (fun ω => lowStop_le_locG ω) hω (Sec2.toNNReal_le_of_mem_Icc (hIcc r hr))
  have hcw : ContinuousOn (fun s : ℝ => W s.toNNReal ω) (Icc a b) :=
    hF.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps
  have hcv : ∀ j, ContinuousOn (fun s : ℝ => VR j s.toNNReal ω) (Icc a b) := fun j =>
    (hF.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps
  have hopos : ∀ s ∈ Icc a b, 0 < VR k s.toNNReal ω - W s.toNNReal ω := fun s hs =>
    (lowDelta_pos hxk).trans_le (lowDelta_le_gap hgood hω (Sec2.toNNReal_le_of_mem_Icc (hIcc s hs)))
  have hepos : ∀ s ∈ Icc a b, 0 < VR j₀ s.toNNReal ω - VR k s.toNNReal ω := fun s hs => by
    have hm := (lowKc_subset hxk hkjx (mem_lowKc hgood hTn hy hkj hkjx
      (Sec2.toNNReal_le_of_mem_Icc (hIcc s hs)))).2
    rwa [lowE_coord hω] at hm
  have hu : ∀ s ∈ Icc a b, VR j₀ s.toNNReal ω - W s.toNNReal ω ≠ 0 := fun s hs => by
    have h1 := hopos s hs
    have h2 := hepos s hs
    intro h
    linarith
  have hc : ContinuousOn (fun s : ℝ => 4 * (VR j₀ s.toNNReal ω - VR k s.toNNReal ω) /
      ((VR j₀ s.toNNReal ω - W s.toNNReal ω) ^ 2 * (VR k s.toNNReal ω - W s.toNNReal ω)) +
        4 * (VR j₀ s.toNNReal ω - VR k s.toNNReal ω) / (VR j₀ s.toNNReal ω - W s.toNNReal ω) ^ 3) (Icc a b) :=
    ContinuousOn.add (ContinuousOn.div (continuousOn_const.mul ((hcv j₀).sub (hcv k)))
      ((((hcv j₀).sub hcw).pow 2).mul ((hcv k).sub hcw)) fun s hs =>
        mul_ne_zero (pow_ne_zero 2 (hu s hs)) (hopos s hs).ne')
      (ContinuousOn.div (continuousOn_const.mul ((hcv j₀).sub (hcv k))) (((hcv j₀).sub hcw).pow 3)
        fun s hs => pow_ne_zero 3 (hu s hs))
  exact hc.intervalIntegrable_of_Icc hab

include hE hGm hGc hgood hT hTn hTm hy hxk hkj hkjx in
/-- **The probability bound for a fixed restart time, energy and level.** -/
theorem measure_lowBad_le [IsProbabilityMeasure P] (hord : IsOrderedForceWord xL xR) (hκ : 0 < κ)
    (hS : S ≤ -2) (hbp : 0 < lowBp κ S (rhoY xR ρR j₀)) {K : ℝ} (hK : 0 < K) :
    P {ω | ω ∈ G ∧ ∃ Te : ℝ≥0, LowPic κ ρL xR ρR k j₀ S W VL VR ζ q C ω Te ∧
        ∃ t : ℝ≥0, q ≤ t ∧ t < Te ∧ K < ∫ s in (q : ℝ)..t, lowBudget W VR k j₀ ω s} ≤
      ENNReal.ofReal (((C : ℝ) + 3) / (K / (2 * lowC3 κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))))) := by
  set c₃ := lowC3 κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))
  have hbm : lowBm κ S < 0 := by simp only [lowBm]; linarith
  have hc3 : 0 < c₃ := lowC3_pos hκ hbm hbp
  set N₀ := ⌈(q : ℝ)⌉₊
  set Bn : ℕ → Set Ω := fun n =>
    {ω | K / (2 * c₃) ≤ lowZ κ xL xR ρL ρR k j₀ S G W VL VR B ζ T q C n ω} with hBn
  set A : ℕ → Set Ω := fun N => ⋂ (n : ℕ) (_ : max N N₀ ≤ n), Bn n with hA
  have hAmono : Monotone A := fun N M hNM => by
    refine iInter₂_mono' fun n hn => ⟨n, (max_le_max hNM le_rfl).trans hn, le_rfl⟩
  have hqn : ∀ n, N₀ ≤ n → q ≤ (n : ℝ≥0) := fun n hn => by
    rw [← NNReal.coe_le_coe]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hn)
  -- the inclusion
  have hsub : {ω | ω ∈ G ∧ ∃ Te : ℝ≥0, LowPic κ ρL xR ρR k j₀ S W VL VR ζ q C ω Te ∧
      ∃ t : ℝ≥0, q ≤ t ∧ t < Te ∧ K < ∫ s in (q : ℝ)..t, lowBudget W VR k j₀ ω s} ⊆ ⋃ N, A N := by
    rintro ω ⟨hω, Te, hpic, t, hqt, htTe, hKt⟩
    obtain ⟨N, hN⟩ := exists_le_lowStop hE hGm hGc hgood hord hTm hκ hkj hkjx hω hpic hqt htTe
    refine mem_iUnion.2 ⟨N, mem_iInter₂.2 fun n hn => ?_⟩
    have htσ := hN n ((le_max_left _ _).trans hn)
    have hqσ : q ≤ lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω := hqt.trans htσ
    have hb := budget_le_lowZ hE hGm hGc hgood hTn hy hxk hkj hkjx hκ hS hbp hω hqσ
    have hqt' : (q : ℝ) ≤ t := hqt
    have htσ' : (t : ℝ) ≤ lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω := htσ
    have hi1 := intervalIntegrable_lowBudget hgood hTn hy hxk hkj hkjx hω q.coe_nonneg hqt' htσ'
    have hi2 := intervalIntegrable_lowBudget hgood hTn hy hxk hkj hkjx hω t.coe_nonneg htσ' le_rfl
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hnn : 0 ≤ ∫ s in (t : ℝ)..(lowStop κ ρL xR ρR k j₀ S G W VL VR B ζ T q C n ω : ℝ),
        lowBudget W VR k j₀ ω s :=
      intervalIntegral.integral_nonneg htσ' fun s hs =>
        lowBudget_nonneg hgood hTn hy hxk hkj hkjx hω ⟨t.coe_nonneg.trans hs.1, hs.2⟩
    show K / (2 * c₃) ≤ _
    refine le_trans ?_ hb
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  refine (measure_mono hsub).trans ?_
  rw [Monotone.measure_iUnion hAmono]
  refine iSup_le fun N => ?_
  have hNn : max N N₀ ≤ max N N₀ := le_rfl
  refine (measure_mono (iInter₂_subset (max N N₀) hNn)).trans ?_
  have hK' : 0 < K / (2 * c₃) := by positivity
  have h := measureReal_lowZ_ge_le hE hGm hGc hgood hT hTn hy hxk hkj hkjx hκ hS hbp (C := C)
    (n := max N N₀) (hqn (max N N₀) (le_max_right N N₀)) hK'
  calc P (Bn (max N N₀)) = ENNReal.ofReal (P.real (Bn (max N N₀))) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

end Fixed

/-- **On the picture the two-mark budget is almost surely bounded** (for every rational restart time and every
energy level). -/
theorem ae_lowBudget_bounded [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hkj : k ≤ j₀) (hkjx : xR k < xR j₀)
    (hxk : 0 < xR k) (hS : S ≤ -2) (hbp : 0 < lowBp κ S (rhoY xR ρR j₀)) :
    ∀ᵐ ω ∂P, ∀ (q : ℚ) (C : ℕ) (Te : ℝ≥0),
      LowPic κ ρL xR ρR k j₀ S W VL VR ζ (q : ℝ).toNNReal C ω Te →
        ∃ K : ℝ, ∀ t : ℝ≥0, (q : ℝ).toNNReal ≤ t → t < Te →
          ∫ s in (((q : ℝ).toNNReal : ℝ≥0) : ℝ)..t, lowBudget W VR k j₀ ω s ≤ K := by
  classical
  have hy : 0 < xR j₀ := hxk.trans hkjx
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- the lifetime vanishes: no picture
    filter_upwards [hE.2.2.2.2] with ω hp q C Te hpic
    exfalso
    have hζ : ζ ω = 0 := by
      by_contra hne
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
      have := hp.isForcePath.not_threshold h0
      have hw : W 0 ω = 0 := hp.isForcePath.w_zero
      have hL : (fun i => VL i 0 ω) = xL := funext hp.isForcePath.vL_zero
      have hR : (fun i => VR i 0 ω) = xR := funext hp.isForcePath.vR_zero
      simp only [hw, hL, hR] at this
      exact this hseed
    have h1 := hpic.2.1
    rw [hζ, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at h1
    exact absurd hpic.1 (by rw [h1]; exact not_lt.2 (zero_le (a := (q : ℝ).toNNReal)))
  obtain ⟨T, hTann, hTn⟩ := Coupling.exists_isAnnouncingSeq_le hE hκ hseed
  obtain ⟨hT, hTm, hTζ, hTcov⟩ := hTann
  have hae : ∀ᵐ ω ∂P, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, ae_all_iff.2 hTζ, hTcov]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨G, hGm, hGc, hgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω := by
    refine ⟨(toMeasurable P {ω | ¬ IsGBGood κ xL xR ρL ρR W VL VR B ζ T ω})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  set c₃ := lowC3 κ (lowBm κ S) (lowBp κ S (rhoY xR ρR j₀))
  have hbm : lowBm κ S < 0 := by simp only [lowBm]; linarith
  have hc3 : 0 < c₃ := lowC3_pos hκ hbm hbp
  set Bad : ℚ → ℕ → ℕ → Set Ω := fun q C K => {ω | ω ∈ G ∧ ∃ Te : ℝ≥0,
    LowPic κ ρL xR ρR k j₀ S W VL VR ζ (q : ℝ).toNNReal C ω Te ∧ ∃ t : ℝ≥0, (q : ℝ).toNNReal ≤ t ∧ t < Te ∧
      (K : ℝ) + 1 < ∫ s in (((q : ℝ).toNNReal : ℝ≥0) : ℝ)..t, lowBudget W VR k j₀ ω s} with hBad
  have hnull : ∀ q C, P (⋂ K, Bad q C K) = 0 := by
    intro q C
    set c := ((C : ℝ) + 3) * (2 * c₃) with hc
    have hle : ∀ K : ℕ, P (⋂ K', Bad q C K') ≤ ENNReal.ofReal (c / ((K : ℝ) + 1)) := fun K => by
      refine (measure_mono (iInter_subset _ K)).trans ?_
      refine (measure_lowBad_le (q := (q : ℝ).toNNReal) (C := C) hE hGm hGc hgood hT hTn hTm hy hxk hkj hkjx hord
        hκ hS hbp (K := (K : ℝ) + 1) (by positivity)).trans (le_of_eq ?_)
      congr 1
      rw [hc, div_div_eq_mul_div]
    have h0 : Tendsto (fun K : ℕ => c / ((K : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun K => ?_
      simp only [Function.comp, Nat.cast_add, Nat.cast_one]
    have htend : Tendsto (fun K : ℕ => ENNReal.ofReal (c / ((K : ℝ) + 1))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal h0
    exact le_antisymm (ge_of_tendsto' htend hle) (zero_le (a := P (⋂ K, Bad q C K)))
  have hall : ∀ᵐ ω ∂P, ∀ q C, ω ∉ ⋂ K, Bad q C K := by
    rw [ae_all_iff]; intro q
    rw [ae_all_iff]; intro C
    exact compl_mem_ae_iff.2 (hnull q C)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := compl_compl G ▸ compl_mem_ae_iff.2 hGc
  filter_upwards [hall, hGae] with ω hω hωG q C Te hpic
  by_contra hcon
  push Not at hcon
  refine hω q C (mem_iInter.2 fun K => ⟨hωG, Te, hpic, ?_⟩)
  obtain ⟨t, h1, h2, h3⟩ := hcon ((K : ℝ) + 1)
  exact ⟨t, h1, h2, h3⟩

end G12Low

end Supp7

end InteractingSLE
