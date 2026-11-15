/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFinLife

/-!
# Physical contact at the finite end of strip life

Packet PROVE-ZHAN-A2P3-PC. Aux. 3 and the real-ray lemma discharge the whole
strip-end case, including an original lifetime simultaneous with the strip end.
No geometric assumption about contact with the small prefix is used here.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

section End

variable {a : ℝ} {nL : ℕ} {xL ρL : Fin nL → ℝ}
  {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin 0 → ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

/-- A strictly negative left word with no right marks has positive lifetime. -/
theorem lifetime_pos_of_strict_left_word
    (hp : IsIntegratedSLEPath a xL ![] ρL ![] w vL vR b ζ)
    (hx : ∀ i, xL i < 0) : 0 < ζ := by
  by_contra h
  have hζ : ζ = 0 := le_antisymm (not_lt.1 h) bot_le
  have ht := hp.isForcePath.threshold_of_eq_zero hζ
  have hf : Finset.univ.filter (fun i => xL i = 0) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro i _ he
    exact (hx i).ne he
  simp only [ForceWord.ThresholdCondition, hf, Finset.sum_empty, Finset.univ_eq_empty,
    Finset.filter_empty, or_self] at ht
  norm_num at ht

/-- A terminal threshold with no right marks swallows some original left mark. -/
theorem exists_left_realSwallowAt_of_terminal_limit
    (hp : IsIntegratedSLEPath a xL ![] ρL ![] w vL vR b ζ)
    {T : ℝ≥0} (hTpos : 0 < T) (hTζ : (T : ℝ≥0∞) = ζ)
    {w₀ : ℝ} {v₀ : Fin nL → ℝ} {vR₀ : Fin 0 → ℝ}
    (hlim : Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t))
      (𝓝[<] T) (𝓝 (w₀, v₀, vR₀)))
    (hthr : ForceWord.ThresholdCondition ρL ![] w₀ v₀ vR₀)
    {U : ℝ → ℝ} (he : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal) :
    ∃ j : Fin nL, RealSwallowAt U (xL j) T := by
  rcases hp.isForcePath.exists_gap_of_tendsto hTpos hTζ hlim hthr with
    ⟨j, -, -⟩ | ⟨j, hgap, heq⟩
  · exact j.elim0
  · have hw := continuous_fst.tendsto (w₀, v₀, vR₀) |>.comp hlim
    have hv := (continuous_apply j).tendsto v₀ |>.comp
      ((continuous_fst.comp continuous_snd).tendsto (w₀, v₀, vR₀) |>.comp hlim)
    have hgap0 : Tendsto (fun t => vL j t - w t) (𝓝[<] T) (𝓝 0) := by
      simpa only [Function.comp_def, heq, sub_self] using hv.sub hw
    exact ⟨j, realSwallowAt_of_left_gap_tendsto hp hTpos hTζ.le hgap he hgap0⟩

end End

universe u

/-- **The strip-end case, proved.** For any integrated left-word evolution whose
marks lie at or left of `r < 0`, stopping at its finite strip end supplies
physical contact, regardless of the small curve used to define contact. -/
theorem ae_finitePhysicalContact_of_contact_eq_lifeEnd
    {a : ℝ} {nL : ℕ} {xL ρL : Fin nL → ℝ} {r : ℝ} (ha : 0 < a) (hr : r < 0)
    (hx : ∀ i, xL i ≤ r) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL ![] ρL ![] P 𝓕 W VL VR B ζ)
    (j : Fin nL) :
    ∀ᵐ ω ∂P, ∀ (x : ℝ) (w₁ : ℝ≥0 → ℝ) (q : ℝ≥0),
      lifeEnd (W · ω) (VL j · ω) (ζ ω) ≠ ⊤ →
      contactTime 0 (Strip.extPath (W · ω)) (lifeEnd (W · ω) (VL j · ω) (ζ ω))
        x (Strip.extPath w₁) q = lifeEnd (W · ω) (VL j · ω) (ζ ω) →
      FinitePhysicalContact x r w₁ (W · ω) (VL j · ω) (ζ ω) q := by
  filter_upwards [hE.ae_isIntegratedSLEPath, hE.ae_tendsto_threshold ha]
    with ω hp hterm x w₁ q hfin hc
  let T : ℝ≥0 := (lifeEnd (W · ω) (VL j · ω) (ζ ω)).toNNReal
  have hT : (T : ℝ≥0∞) = lifeEnd (W · ω) (VL j · ω) (ζ ω) :=
    ENNReal.coe_toNNReal hfin
  have hζpos := lifetime_pos_of_strict_left_word hp (fun i => (hx i).trans_lt hr)
  have hf := hp.isForcePath
  have hTpos : 0 < T := by
    have hs : Strip.IsStripLife (W · ω) (VL j · ω) (ζ ω) 0 := by
      refine ⟨by simpa only [ENNReal.coe_zero] using hζpos, fun s hs => ?_⟩
      have hs0 : s = 0 := le_antisymm hs bot_le
      rw [hs0]
      change VL j 0 ω < W 0 ω
      rw [hf.vL_zero j, hf.w_zero]
      exact (hx j).trans_lt hr
    have hlt := lt_lifeEnd_of_isStripLife hf.continuousOn_w (hf.continuousOn_vL j) hs
    rw [← hT] at hlt
    exact ENNReal.coe_lt_coe.1 hlt
  have hTζ : (T : ℝ≥0∞) ≤ ζ ω := hT ▸ lifeEnd_le_lifetime _ _ _
  rcases hTζ.lt_or_eq with hlt | heq
  · obtain ⟨t₂, hTt₂, ht₂⟩ := exists_real_btwn_of_lt hlt
    let U := frozenDrive (W · ω) t₂
    have hU : Continuous U := continuous_frozenDrive_of_lt hf.continuousOn_w ht₂
    have hU0 : U 0 = 0 := by
      rw [show U = frozenDrive (W · ω) t₂ from rfl,
        frozenDrive_zero (T.coe_nonneg.trans hTt₂.le), hf.w_zero]
    have hUeq : ∀ s : ℝ, 0 ≤ s → s < T → U s = W s.toNNReal ω :=
      fun s hs hsT => frozenDrive_eq ⟨hs, hsT.le.trans hTt₂.le⟩
    have hsw := realSwallowAt_of_lifeEnd_lt_lifetime hp hTpos hT hlt hUeq
    exact finitePhysicalContact_of_swallow_of_contact_eq_lifeEnd hT hc hU hU0
      hUeq ((hx j).trans_lt hr) (hx j) hsw
  · obtain ⟨w₀, v₀, vR₀, hlim, hthr⟩ := hterm T hTpos heq
    let U := FiniteEndpoint.extDriver (W · ω) T w₀
    have hU : Continuous U := FiniteEndpoint.continuous_extDriver
      (hf.continuousOn_w.mono fun t ht => by
        exact (ENNReal.coe_lt_coe.2 ht).trans_le heq.le)
      (continuous_fst.tendsto (w₀, v₀, vR₀) |>.comp hlim)
    have hUeq : ∀ s : ℝ, 0 ≤ s → s < T → U s = W s.toNNReal ω :=
      fun s hs hsT => FiniteEndpoint.extDriver_of_lt hs hsT
    have hU0 : U 0 = 0 := by
      rw [hUeq 0 le_rfl (NNReal.coe_pos.2 hTpos), Real.toNNReal_zero, hf.w_zero]
    obtain ⟨k, hsw⟩ := exists_left_realSwallowAt_of_terminal_limit hp hTpos heq hlim hthr hUeq
    exact finitePhysicalContact_of_swallow_of_contact_eq_lifeEnd hT hc hU hU0
      hUeq ((hx k).trans_lt hr) (hx k) hsw

end InteractingSLE.ZhanGT4.A2X.P3
