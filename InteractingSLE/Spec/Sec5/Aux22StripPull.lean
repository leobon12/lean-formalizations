/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripAvoid
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Aux. lemma 22 in the strip, step 4a: pulling the strip endpoint back through the change of target

Packet PROVE-SEC5-L (specification §4.1, proof of Aux. lemma 22, p. 115: "The inverse of each displayed map extends
analytically at every such point and maps it to a finite point of `I` … the actual endpoint pulls back as asserted").

Setting (PROVE-SEC7-C10's R6): an original driver `w` with target mark `vk` started at `xk > 0`, separated before `τ`
(`Zhan.Retarget.PullData w vk xk τ`); the new driver `newDrv` in the new clock `C`; `ψ⁻¹(q) = xk q/(1 + q)`
(`Sec7.targetChangeInv`). Given a trace `η_G` of the new driver on `[0, u]` for every `u < S`, avoiding `ℝ \ {0}`,
and converging to `y ≠ −1` as `u ↑ S`, with `S` at most the new horizon:

* `PullData.mono`, `newHorizon_le_clk`;
* `eq_pullTrace_of_lt`: the original trace is the pull-back `ψ⁻¹(η_G(C(t)))` at every time whose new clock has room
  below `S` (uniqueness of generating traces, `IsGeneratingTrace.eq_of_le`);
* **`exists_hit_of_le`**: the original trace reaches `ψ⁻¹(y)` at a finite time `t ≤ τ` and avoids `ℝ \ {0}` before
  (when the new horizon is `S` and `τ = ∞`, the pulled-back trace would be bounded on `[0, ∞)`, which a capacity
  bound excludes).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (IsForwardSol H)

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Zhan.Retarget

variable {w vk : ℝ≥0 → ℝ} {xk : ℝ} {τ : ℝ≥0∞}

theorem PullData.mono (hd : PullData w vk xk τ) {T : ℝ≥0∞} (hT : T ≤ τ) : PullData w vk xk T :=
  ⟨hd.pos, hd.w_zero, fun S hS0 hST => hd.sep S hS0 (lt_of_lt_of_le hST hT),
    fun t ht => hd.target t (lt_of_lt_of_le ht hT)⟩

/-- The new horizon of a time before `τ` is at most its clock. -/
theorem newHorizon_le_clk (hd : PullData w vk xk τ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    newHorizon xk w vk t ≤ ENNReal.ofReal (clk (rate xk w vk) t) := by
  refine iSup₂_le fun s hs => ENNReal.ofReal_le_ofReal ?_
  exact hd.clk_mono (ENNReal.coe_lt_coe.1 hs).le ht

/-- **The original trace is the pull-back of the new one** at every time `t < t'` where `t' < τ` and the clock of
`t'` is below `S`. -/
theorem eq_pullTrace_of_lt (hd : PullData w vk xk τ) {ζ : ℝ≥0∞} (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hτζ : τ ≤ ζ) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {S : ℝ≥0} {ηG : ℝ≥0 → ℂ}
    (hgen : ∀ u : ℝ≥0, u < S → (u : ℝ≥0∞) < newHorizon xk w vk τ → IsGeneratingTrace (newDrv xk w vk) u ηG)
    {t t' : ℝ≥0} (htt' : t < t') (ht' : (t' : ℝ≥0∞) < τ) (hC : clk (rate xk w vk) t' < S) :
    η t = pullTrace xk w vk ηG t := by
  have hd' : PullData w vk xk t' := PullData.mono hd ht'.le
  have hc0 : 0 ≤ clk (rate xk w vk) t' := (hd.isRate ht').clk_nonneg ⟨t'.coe_nonneg, le_rfl⟩
  have hu : (clk (rate xk w vk) t').toNNReal < S := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hc0]; exact hC
  have hG := hgen _ hu (hd.clk_lt ht')
  have hle : newHorizon xk w vk t' ≤ (((clk (rate xk w vk) t').toNNReal : ℝ≥0) : ℝ≥0∞) :=
    newHorizon_le_clk hd ht'
  have hG' : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk t') ηG := hG.mono_horizon hle
  have hpull : IsGeneratingTrace w t (pullTrace xk w vk ηG) :=
    ⟨pullTrace_zero hG', fun s hs => (hd'.continuousAt_pullTrace hG'
      (lt_of_le_of_lt (show (s : ℝ≥0∞) ≤ t from hs) (ENNReal.coe_lt_coe.2 htt'))).continuousWithinAt,
      fun s hs => hd'.isFilling_pullTrace hG' (hs.trans (ENNReal.coe_lt_coe.2 htt'))⟩
  have htζ : (t : ℝ≥0∞) ≤ ζ := ((ENNReal.coe_lt_coe.2 htt').trans ht').le.trans hτζ
  exact IsGeneratingTrace.eq_of_le (hη.mono_horizon htζ) hpull
    (hwc.mono fun s (hs : (s : ℝ≥0∞) < t) => lt_of_lt_of_le hs htζ) hd.w_zero le_rfl

/-! ### `ψ⁻¹` on the real line -/

theorem targetChangeInv_ofReal (xk y : ℝ) :
    Sec7.targetChangeInv xk (y : ℂ) = ((xk * y / (1 + y) : ℝ) : ℂ) := by
  simp [Sec7.targetChangeInv]

/-- `ψ⁻¹` of a point that is not a nonzero real is not a nonzero real. -/
theorem targetChangeInv_ne_ofReal {q : ℂ} (hq : ∀ z : ℝ, z ≠ 0 → q ≠ z) {r : ℝ} (hr : r ≠ 0) :
    Sec7.targetChangeInv xk q ≠ r := by
  intro h
  by_cases hq1 : 1 + q = 0
  · rw [Sec7.targetChangeInv, hq1, div_zero] at h
    exact hr (by exact_mod_cast h.symm)
  · have h1 : (xk : ℂ) * q = r * (1 + q) := by
      rw [Sec7.targetChangeInv, div_eq_iff hq1] at h; exact h
    have hne : ((xk - r : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have h0' : xk = r := by exact_mod_cast sub_eq_zero.1 (by exact_mod_cast h0)
      rw [h0'] at h1
      have : (r : ℂ) = 0 := by linear_combination -h1
      exact hr (by exact_mod_cast this)
    have hq' : q = ((r / (xk - r) : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff (by exact_mod_cast hne)]
      push_cast at hne ⊢
      linear_combination h1
    refine hq _ (div_ne_zero hr (by intro h0; exact hne (by exact_mod_cast h0))) hq'

/-- A trace that converges at `S` to a point other than `−1` and avoids `−1` before `S` stays a positive distance
from `−1` on `[0, S)`. -/
theorem exists_pos_le_norm_add_one {S : ℝ≥0} {ηG : ℝ≥0 → ℂ} (hcont : ∀ u : ℝ≥0, u < S → ContinuousAt ηG u)
    (hne : ∀ u : ℝ≥0, u < S → ηG u ≠ -1) {y : ℂ} (hy : y ≠ -1) (hconv : Tendsto ηG (𝓝[<] S) (𝓝 y)) :
    ∃ c > 0, ∀ u : ℝ≥0, u < S → c ≤ ‖ηG u + 1‖ := by
  have hd : 0 < ‖y + 1‖ := norm_pos_iff.2 fun h => hy (eq_neg_of_add_eq_zero_left h)
  rcases eq_zero_or_pos S with hS0 | hS0
  · exact ⟨1, one_pos, fun u hu => absurd hu (by rw [hS0]; exact not_lt_zero)⟩
  have hev : ∀ᶠ u in 𝓝[<] S, ‖ηG u - y‖ < ‖y + 1‖ / 2 :=
    (Metric.tendsto_nhds.1 hconv) _ (half_pos hd) |>.mono fun u hu => by rwa [dist_eq_norm] at hu
  obtain ⟨l, hlS, hl⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hS0).1 hev
  have hcpt : IsCompact (Icc (0 : ℝ≥0) l) := isCompact_Icc
  have hfc : ContinuousOn (fun u => ‖ηG u + 1‖) (Icc 0 l) := fun u hu =>
    ((hcont u (lt_of_le_of_lt hu.2 hlS)).add continuousAt_const).norm.continuousWithinAt
  obtain ⟨u₀, hu₀, hmin⟩ := hcpt.exists_isMinOn ⟨0, le_rfl, zero_le⟩ hfc
  have hm : 0 < ‖ηG u₀ + 1‖ := norm_pos_iff.2 fun h =>
    hne u₀ (lt_of_le_of_lt hu₀.2 hlS) (eq_neg_of_add_eq_zero_left h)
  refine ⟨min (‖y + 1‖ / 2) ‖ηG u₀ + 1‖, lt_min (half_pos hd) hm, fun u hu => ?_⟩
  rcases le_or_gt u l with h | h
  · exact (min_le_right _ _).trans (hmin ⟨zero_le, h⟩)
  · refine (min_le_left _ _).trans ?_
    have h1 := hl ⟨h, hu⟩
    have h2 : ‖y + 1‖ ≤ ‖ηG u + 1‖ + ‖ηG u - y‖ := by
      have := norm_sub_le (ηG u + 1) (ηG u - y)
      rwa [show ηG u + 1 - (ηG u - y) = y + 1 by ring] at this
    simp only [mem_ofPred_eq] at h1
    linarith

/-- **The pull-back of the strip endpoint, when the new trace converges no later than the new horizon.** -/
theorem exists_hit_of_le (hd : PullData w vk xk τ) {ζ : ℝ≥0∞} (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hτζ : τ ≤ ζ) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {S : ℝ≥0} (hS0 : 0 < S) {ηG : ℝ≥0 → ℂ} {y : ℝ}
    (hy : y ≠ -1)
    (hgen : ∀ u : ℝ≥0, u < S → (u : ℝ≥0∞) < newHorizon xk w vk τ → IsGeneratingTrace (newDrv xk w vk) u ηG)
    (havoid : ∀ u : ℝ≥0, u < S → ∀ z : ℝ, z ≠ 0 → ηG u ≠ z) (hconv : Tendsto ηG (𝓝[<] S) (𝓝 (y : ℂ)))
    (hS : (S : ℝ≥0∞) ≤ newHorizon xk w vk τ) :
    ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η s ≠ z) ∧
      η t = Sec7.targetChangeInv xk y := by
  have hxk := hd.pos
  have hS' : ∀ u : ℝ≥0, u < S → (u : ℝ≥0∞) < newHorizon xk w vk τ := fun u hu =>
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hu) hS
  have hy' : (y : ℂ) ≠ -1 := fun h => hy (by exact_mod_cast h)
  -- continuity of `ηG` before `S`
  have hGc : ∀ u : ℝ≥0, u < S → ContinuousAt ηG u := by
    intro u hu
    obtain ⟨u', huu', hu'S⟩ := exists_between hu
    have hg := hgen u' hu'S (hS' u' hu'S)
    have hopen : IsOpen {r : ℝ≥0 | (r : ℝ≥0∞) < u'} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact hg.2.1.continuousAt (Filter.mem_of_superset (hopen.mem_nhds (ENNReal.coe_lt_coe.2 huu'))
      fun r hr => show (r : ℝ≥0∞) ≤ u' from le_of_lt hr)
  have hGne : ∀ u : ℝ≥0, u < S → ηG u ≠ -1 := fun u hu h =>
    havoid u hu (-1) (by norm_num) (by rw [h]; push_cast; ring)
  -- the clock is below `S` before a time `T` and tends to `S` at `T`
  have hclk0 : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → 0 ≤ clk (rate xk w vk) t := fun ht =>
    (hd.isRate ht).clk_nonneg ⟨NNReal.coe_nonneg _, le_rfl⟩
  obtain ⟨T, hT0, hTτ, hbefore, hlim⟩ : ∃ T : ℝ≥0, 0 < T ∧ (T : ℝ≥0∞) ≤ τ ∧
      (∀ t : ℝ≥0, t < T → ∃ t' : ℝ≥0, t < t' ∧ (t' : ℝ≥0∞) < τ ∧ clk (rate xk w vk) t' < S) ∧
      Tendsto (fun t : ℝ≥0 => (clk (rate xk w vk) t).toNNReal) (𝓝[<] T) (𝓝[<] S) := by
    rcases hS.lt_or_eq with hlt | heq
    · -- `S` is before the new horizon: `T = C⁻¹(S)`
      obtain ⟨S₁, hS₁τ, hR, hSlt, hmem, hcinv⟩ := newTime_spec hd.sep hd.pos hlt
      set T : ℝ≥0 := (invClk (rate xk w vk) S).toNNReal with hTdef
      have hT' : (T : ℝ) = invClk (rate xk w vk) S := Real.coe_toNNReal _ hmem.1
      have hTS₁ : T < S₁ := by
        rw [← NNReal.coe_lt_coe, hT']
        exact hR.invClk_lt ⟨S.coe_nonneg, hSlt⟩
      have hCT : clk (rate xk w vk) T = S := by rw [hT']; exact hcinv
      have hTmem : (T : ℝ) ∈ Icc 0 (S₁ : ℝ) := ⟨T.coe_nonneg, by exact_mod_cast hTS₁.le⟩
      have hClt : ∀ t : ℝ≥0, t < T → clk (rate xk w vk) t < S := fun t ht => by
        rw [← hCT]
        exact hR.clk_lt ⟨t.coe_nonneg, by exact_mod_cast (ht.trans hTS₁).le⟩ hTmem (by exact_mod_cast ht)
      have hT0 : 0 < T := by
        rcases eq_zero_or_pos T with h | h
        · rw [h, NNReal.coe_zero, clk_zero] at hCT
          exact absurd hCT.symm (by exact_mod_cast hS0.ne')
        · exact h
      refine ⟨T, hT0, (ENNReal.coe_lt_coe.2 hTS₁).le.trans hS₁τ.le, fun t ht => ?_, ?_⟩
      · obtain ⟨t', htt', ht'T⟩ := exists_between ht
        exact ⟨t', htt', (ENNReal.coe_lt_coe.2 (ht'T.trans hTS₁)).trans hS₁τ, hClt t' ht'T⟩
      · have h2 : ContinuousOn (fun t : ℝ≥0 => clk (rate xk w vk) t) (Iic S₁) :=
          hR.continuousOn_clk.comp NNReal.continuous_coe.continuousOn fun t ht =>
            ⟨t.coe_nonneg, by exact_mod_cast ht⟩
        have hcont : ContinuousWithinAt (fun t : ℝ≥0 => clk (rate xk w vk) t) (Iio T) T :=
          (h2 T hTS₁.le).mono fun t ht => (le_of_lt (mem_Iio.1 ht)).trans hTS₁.le
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have h3 := (continuous_real_toNNReal.tendsto _).comp hcont.tendsto
          rwa [hCT, Real.toNNReal_coe] at h3
        · filter_upwards [self_mem_nhdsWithin] with t (ht : t < T)
          show (clk (rate xk w vk) t).toNNReal < S
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ((hR.clk_nonneg ⟨t.coe_nonneg,
            by exact_mod_cast (ht.trans hTS₁).le⟩))]
          exact hClt t ht
    · -- `S` is the new horizon
      have hτ : τ ≠ ⊤ := by
        intro hτ
        have hζ : ζ = ⊤ := top_le_iff.1 (hτ ▸ hτζ)
        obtain ⟨c, hc, hcle⟩ := exists_pos_le_norm_add_one hGc hGne hy' hconv
        have hrel : ∀ t : ℝ≥0, η t = pullTrace xk w vk ηG t ∧ (clk (rate xk w vk) t).toNNReal < S := by
          intro t
          have ht1 : ((t + 1 : ℝ≥0) : ℝ≥0∞) < τ := by rw [hτ]; exact ENNReal.coe_lt_top
          have hC1 : clk (rate xk w vk) (t + 1 : ℝ≥0) < S := by
            have := hd.clk_lt ht1
            rw [← heq] at this
            have h' := ENNReal.coe_lt_coe.1 this
            rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hclk0 ht1)] at h'
          refine ⟨eq_pullTrace_of_lt hd hwc hτζ hη hgen (lt_add_one t) ht1 hC1, ?_⟩
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hclk0 (lt_of_le_of_lt (by simp) ht1))]
          exact lt_of_le_of_lt (hd.clk_mono (le_of_lt (lt_add_one t)) ht1) hC1
        set B : ℝ := xk * (1 + 1 / c) with hB
        have hbnd : ∀ t : ℝ≥0, ‖η t‖ ≤ B := fun t => by
          rw [(hrel t).1]
          exact norm_targetChangeInv_le hxk hc (hcle _ (hrel t).2)
        set t₀ : ℝ≥0 := (B ^ 2 / 2 + 1).toNNReal with ht₀
        have h := two_mul_le_sq_of_isGeneratingTrace hwc hd.w_zero hη (t := t₀)
          (by rw [hζ]; exact ENNReal.coe_lt_top) (B := B) fun s _ => hbnd s
        rw [ht₀, Real.coe_toNNReal _ (by positivity)] at h
        linarith
      set T : ℝ≥0 := τ.toNNReal with hTdef
      have hT' : (T : ℝ≥0∞) = τ := ENNReal.coe_toNNReal hτ
      have hhor : newHorizon xk w vk τ ≠ ⊤ := by rw [← heq]; exact ENNReal.coe_ne_top
      have hCS : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → clk (rate xk w vk) t < S := fun t ht => by
        have := hd.clk_lt ht
        rw [← heq] at this
        have h' := ENNReal.coe_lt_coe.1 this
        rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hclk0 ht)] at h'
      have hT0 : 0 < T := by
        rcases eq_zero_or_pos T with h | h
        · have h0 : τ = 0 := by rw [← hT', h, ENNReal.coe_zero]
          rw [h0, newHorizon_zero] at heq
          exact absurd heq (by exact_mod_cast hS0.ne')
        · exact h
      refine ⟨T, hT0, hT'.le, fun t ht => ?_, ?_⟩
      · obtain ⟨t', htt', ht'T⟩ := exists_between ht
        have ht'τ : (t' : ℝ≥0∞) < τ := by rw [← hT']; exact ENNReal.coe_lt_coe.2 ht'T
        exact ⟨t', htt', ht'τ, hCS t' ht'τ⟩
      · have hF : IsLeftOf (𝓝[<] T) τ := by rw [← hT']; exact isLeftOf_nhdsLT T
        have h1 := hd.tendsto_clk_of_ne_top hF hhor
        rw [← heq, ENNReal.toNNReal_coe] at h1
        refine tendsto_nhdsWithin_iff.2 ⟨h1.mono_right nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with t (ht : t < T)
        have htτ : (t : ℝ≥0∞) < τ := by rw [← hT']; exact ENNReal.coe_lt_coe.2 ht
        show (clk (rate xk w vk) t).toNNReal < S
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hclk0 htτ)]
        exact hCS t htτ
  -- the pull-back relation before `T`
  have hrel : ∀ s : ℝ≥0, s < T → η s = Sec7.targetChangeInv xk (ηG (clk (rate xk w vk) s).toNNReal) ∧
      (clk (rate xk w vk) s).toNNReal < S := by
    intro s hs
    obtain ⟨t', hst', ht'τ, hC'⟩ := hbefore s hs
    refine ⟨eq_pullTrace_of_lt hd hwc hτζ hη hgen hst' ht'τ hC', ?_⟩
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hclk0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hst'.le) ht'τ))]
    exact lt_of_le_of_lt (hd.clk_mono hst'.le ht'τ) hC'
  refine ⟨T, hTτ, fun s hs z hz => ?_, ?_⟩
  · rw [(hrel s hs).1]
    exact targetChangeInv_ne_ofReal (havoid _ (hrel s hs).2) hz
  · -- the limit at `T`
    have hlimη : Tendsto η (𝓝[<] T) (𝓝 (Sec7.targetChangeInv xk y)) := by
      have h1 : Tendsto (fun s : ℝ≥0 => Sec7.targetChangeInv xk (ηG (clk (rate xk w vk) s).toNNReal)) (𝓝[<] T)
          (𝓝 (Sec7.targetChangeInv xk y)) :=
        ((continuousAt_targetChangeInv hy').tendsto.comp hconv).comp hlim
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : s < T)
      exact ((hrel s hs).1).symm
    have hTζ : (T : ℝ≥0∞) ≤ ζ := hTτ.trans hτζ
    have hcontT : Tendsto η (𝓝[<] T) (𝓝 (η T)) :=
      ((hη.2.1 T hTζ).mono fun s (hs : s < T) =>
        show (s : ℝ≥0∞) ≤ ζ from (ENNReal.coe_le_coe.2 hs.le).trans hTζ).tendsto
    have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
    exact tendsto_nhds_unique hcontT hlimη

end Aux22Strip

end Sec5

end InteractingSLE
