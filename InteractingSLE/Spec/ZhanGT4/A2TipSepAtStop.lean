/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepCore
import InteractingSLE.Spec.Zhan.StripTimeGap

/-!
# A.2, part 2, step 1: the conditional separation at a stopping time of the usual augmentation

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs*, §A.2 L548–L553 (R38, R53, R70).

"Condition on a stopped large-curve prefix before lifetime. … Thus the small strip endpoint theorem applies to the
completed conditional image. Its endpoint lies strictly between `W₂` and `g₂(p₂)`, so its crosscut separates the large
tip from infinity."

* `tipSeparated_of_endpoint_path`: the pathwise separation (`tipSeparated_of_endpoint`) for the large driver of the
  pair, continuous only before its lifetime (clamped after a later time);
* `ae_tipSeparated_at_stop_G3_of_law`, `ae_tipSeparated_at_stop_eight_of_law`: for the large evolution of a pair and
  any filtration `𝓗` carrying the conditional image law (`𝓕₂` itself, or `usualAugmentation 𝓕₂ P` for the pairs of
  R70), at every `𝓗`-stopping time `τ`, almost surely, if `0 < τ` lies in the strip life, the large tip at `τ` is
  separated from `∞` by every small crosscut — from the image endpoint input `ImageEndpoint…Statement` applied to the
  conditional image law at `τ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

/-! ### Deterministic transfers -/

/-- A mark solving the Loewner equation on `[0, T]` and staying off the driver is the centred real flow of its start. -/
theorem isForwardSol_of_mark_le {A : ℝ → ℝ} {v : ℝ≥0 → ℝ} {y T : ℝ}
    (hvc : ContinuousOn (fun s : ℝ => v s.toNNReal) (Icc 0 T)) (hAc : Continuous A)
    (hne : ∀ s ∈ Icc (0 : ℝ) T, v s.toNNReal ≠ A s)
    (heq : ∀ s ∈ Icc (0 : ℝ) T, v s.toNNReal = y + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - A r)) :
    IsForwardSol A (y : ℂ) T (fun s => ((v s.toNNReal - A s : ℝ) : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp_continuousOn (hvc.sub hAc.continuousOn), fun s hs => ⟨?_, ?_⟩⟩
  · exact Complex.ofReal_ne_zero.2 (sub_ne_zero.2 (hne s hs))
  · have h1 : (∫ r in (0 : ℝ)..s, (2 : ℂ) / ((v r.toNNReal - A r : ℝ) : ℂ)) =
        ((∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - A r) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r _ => ?_
      push_cast; rfl
    show ((v s.toNNReal - A s : ℝ) : ℂ) = _
    rw [h1, heq s hs]
    push_cast
    ring

/-- The image chain depends on the stopped large curve only through its hull and map at `τ`. -/
theorem isImageChainUpTo_of_congr {xj : ℝ} {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk wk' : ℝ → ℝ} {τ : ℝ}
    {x' : ℝ} {w' clk : ℝ → ℝ} {ζ' : ℝ≥0∞} (hH : physHull xk wk τ = physHull xk wk' τ)
    (hM : physMap xk wk τ = physMap xk wk' τ) (h : IsImageChainUpTo xj wj ζj xk wk τ x' w' clk ζ') :
    IsImageChainUpTo xj wj ζj xk wk' τ x' w' clk ζ' := by
  have hc : contactTime xj wj ζj xk wk τ = contactTime xj wj ζj xk wk' τ := by simp only [contactTime, hH]
  unfold IsImageChainUpTo at h ⊢
  rw [← hc, ← hM]
  exact h

/-- `TipSeparated` depends on the driver only through its hull and map at `s`. -/
theorem tipSeparated_of_congr {W W' : ℝ → ℝ} {s : ℝ} {J : Set ℂ} (hK : fwdHull W s = fwdHull W' s)
    (hf : ∀ z, fwdMap W s z = fwdMap W' s z) (h : TipSeparated W s J) : TipSeparated W' s J := by
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun z hz hzε => ?_⟩
  rw [← hK] at hz ⊢
  exact h z hz (by rwa [hf])

/-- **The pathwise separation for the large curve of the pair**: driver `w₂` continuous before `ζ₂` with `w₂ 0 = 0`,
the mark `v` of the small source `y` solving the Loewner equation and staying left of `w₂` up to `τ < ζ₂`. -/
theorem tipSeparated_of_endpoint_path {w₂ v : ℝ≥0 → ℝ} {ζ₂ : ℝ≥0∞} {y : ℝ} {τ : ℝ≥0}
    (hw : ContinuousOn w₂ {t | (t : ℝ≥0∞) < ζ₂}) (hw0 : w₂ 0 = 0) (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ₂})
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₂ → v t = y + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w₂ s.toNNReal))
    (hτζ : (τ : ℝ≥0∞) < ζ₂) (hvw : ∀ r ≤ τ, v r < w₂ r) (hτ : 0 < τ) (hy0 : y < 0)
    {w₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞} {γ : ℝ → ℂ} (hγ : IsSmallCrosscut y w₁ ζ₁ γ) {w' clk : ℝ → ℝ} {ζ' : ℝ≥0∞}
    (hch : IsImageChainUpTo y (Strip.extPath w₁) ζ₁ 0 (Strip.extPath w₂) τ (v τ) w' clk ζ')
    (hend : ImageEndpointAlt w' ζ' (w₂ τ - v τ)) : TipSeparated (Strip.extPath w₂) τ (γ '' Ioo 0 1) := by
  obtain ⟨t', hτt', ht'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτζ
  have hτt'' : τ < t' := ENNReal.coe_lt_coe.1 hτt'
  have hcont : ContinuousOn (Strip.extPath w₂) (Icc 0 (t' : ℝ)) := Strip.continuousOn_extPath hw ht'ζ
  set A := Ito.clampDrv (Strip.extPath w₂) t' with hAdef
  have hA : Continuous A := Ito.continuous_clampDrv t'.2 hcont
  have hAeq : EqOn A (Strip.extPath w₂) (Icc 0 t') := Ito.clampDrv_eqOn
  have hAr : ∀ r : ℝ, 0 ≤ r → r ≤ τ → A r = w₂ r.toNNReal := fun r h0 h1 =>
    hAeq ⟨h0, h1.trans (NNReal.coe_le_coe.2 hτt''.le)⟩
  have hA0 : A 0 = 0 := by rw [hAr 0 le_rfl τ.2, Real.toNNReal_zero, hw0]
  have hAτ : A τ = w₂ τ := by rw [hAr τ τ.2 le_rfl, Real.toNNReal_coe]
  have hK : fwdHull A τ = fwdHull (Strip.extPath w₂) τ :=
    LocalExt.fwdHull_congr_of_eqOn_of_lt τ.2 (NNReal.coe_lt_coe.2 hτt'') hAeq
  have hf : ∀ z, fwdMap A τ z = fwdMap (Strip.extPath w₂) τ z := fun z =>
    Ito.fwdMap_congr_of_eqOn_of_le hAeq (NNReal.coe_le_coe.2 hτt''.le)
  -- the small source is alive for the large curve
  have hvc' : ContinuousOn (fun s : ℝ => v s.toNNReal) (Icc 0 (τ : ℝ)) := Strip.continuousOn_extPath hvc hτζ
  have hsol : IsForwardSol A (y : ℂ) τ (fun s => ((v s.toNNReal - A s : ℝ) : ℂ)) := by
    refine isForwardSol_of_mark_le hvc' hA (fun s hs => ?_) (fun s hs => ?_)
    · rw [hAr s hs.1 hs.2]
      exact (hvw _ (Real.toNNReal_le_iff_le_coe.2 hs.2)).ne
    · have hsζ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₂ :=
        (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans_lt hτζ
      rw [hveq _ hsζ, Real.coe_toNNReal _ hs.1]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      rw [hAr r hr.1 (hr.2.trans hs.2)]
  have hy : (y : ℂ) ∉ closure (fwdHull A τ) := not_mem_closure_fwdHull_of_isForwardSol hA τ.2 hsol
  have hsrc : v τ < A τ := by rw [hAτ]; exact hvw τ le_rfl
  have hH : physHull 0 (Strip.extPath w₂) τ = physHull 0 A τ := by
    rw [A2X.P3.physHull_zero, A2X.P3.physHull_zero, hK]
  have hM : physMap 0 (Strip.extPath w₂) τ = physMap 0 A τ := by
    have hext : Strip.extPath w₂ τ = w₂ τ := by simp [Strip.extPath]
    funext z
    simp only [physMap, hf]
    rw [hAτ, hext]
  have hch' := isImageChainUpTo_of_congr hH hM hch
  have hend' : ImageEndpointAlt w' ζ' (A τ - v τ) := by rw [hAτ]; exact hend
  exact tipSeparated_of_congr hK hf
    (tipSeparated_of_endpoint hA hA0 (NNReal.coe_pos.2 hτ) hy0 hy hsrc hγ hch' hend')


/-! ### At a stopping time of the usual augmentation -/

/-- **The conditional separation at a stopping time, (G3)** (L548–L553): for the large (G3) evolution and a filtration
`𝓗` in which the large-to-small conditional image law of the pair holds, at every `𝓗`-stopping time `τ`, almost surely,
if `0 < τ` is in the strip life of the mark `x`, the large tip at `τ` is separated from `∞` by every small crosscut. -/
theorem ae_tipSeparated_at_stop_G3_of_law {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8)
    (hI : ImageEndpointG3Statement.{u} κ) {y x : ℝ} (hyx : y < x) (hx : x < 0) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕₂ 𝓗 : Filtration ℝ≥0 mΩ} {W₂ : ℝ≥0 → Ω → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ} {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞}
    {W₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hlaw : IsCondImageLaw (kh κ) P 𝓗 (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0 W₂
      (fun t ω => VL₂ 1 t ω) (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω])
      (smallG3RhoL κ) (smallG3RhoR κ))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓗 fun ω => (τ ω : WithTop ℝ≥0)) :
    ∀ᵐ ω ∂P, 0 < τ ω → Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (τ ω) →
      ∀ γ : ℝ → ℂ, IsSmallCrosscut y (W₁ · ω) (ζ₁ ω) γ →
        TipSeparated (Strip.extPath (W₂ · ω)) (τ ω) (γ '' Ioo 0 1) := by
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hRW, hch⟩ := hlaw τ hτ
  have hpath := hE.2.2.2.2
  -- the mark of `y` stays left of the driver, strictly left of the mark of `x`
  have hord : ∀ᵐ ω ∂P, Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (τ ω) →
      (∀ r ≤ τ ω, VL₂ 1 r ω < W₂ r ω) ∧ VL₂ 1 (τ ω) ω < VL₂ 0 (τ ω) ω := by
    filter_upwards [hpath] with ω hp hF
    have hFP := hp.isForcePath
    have hvw : ∀ r ≤ τ ω, VL₂ 1 r ω < W₂ r ω := fun r hr =>
      lt_of_le_of_lt (hFP.antitone_vL ((ENNReal.coe_le_coe.2 hr).trans_lt hF.1) (show (0 : Fin 2) ≤ 1 by decide))
        (hF.2 r hr)
    exact ⟨hvw, hFP.vL_lt_vL_of_lt hF.1 (i := 0) (j := 1) (by simpa using hyx) hvw⟩
  have hend := hI hκ4 hκ8 hτ.measurableSpace P _ _ _ 𝓖 W' VL' VR' B' ζ' hRW (by
    filter_upwards [hord] with ω hω hF
    obtain ⟨-, hxy⟩ := hω hF
    have hxw : VL₂ 0 (τ ω) ω < W₂ (τ ω) ω := hF.2 _ le_rfl
    refine ⟨rfl, rfl, ?_, ?_⟩
    · show 0 < VL₂ 0 (τ ω) ω - VL₂ 1 (τ ω) ω
      linarith
    · show VL₂ 0 (τ ω) ω - VL₂ 1 (τ ω) ω < W₂ (τ ω) ω - VL₂ 1 (τ ω) ω
      linarith)
  filter_upwards [hpath, hch, hend, hord] with ω hp hchω hendω hordω hτ0 hF γ hγ
  have hFP := hp.isForcePath
  exact tipSeparated_of_endpoint_path (v := (VL₂ 1 · ω)) hFP.continuousOn_w hFP.w_zero (hFP.continuousOn_vL 1)
    (fun t ht => by simpa using hFP.vL_eq ht 1) hF.1 (hordω hF).1 hτ0 (by linarith) hγ (hchω hF) (hendω hF)

/-- **The conditional separation at a stopping time, (Eight)** (L548–L553 with §A.3.1), for any filtration `𝓗` carrying
the conditional image law. -/
theorem ae_tipSeparated_at_stop_eight_of_law {κ : ℝ} (hκ8 : 8 ≤ κ) (hI : ImageEndpointEightStatement.{u} κ)
    {x : ℝ} (hx : x < 0) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕₂ 𝓗 : Filtration ℝ≥0 mΩ} {W₂ : ℝ≥0 → Ω → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Ω → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Ω → ℝ}
    {B₂ : ℝ≥0 → Ω → ℝ} {ζ₂ : Ω → ℝ≥0∞} {W₁ : ℝ≥0 → Ω → ℝ} {ζ₁ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ ![x] ![] ![0] ![] P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hlaw : IsCondImageLaw (kh κ) P 𝓗 (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0 W₂
      (fun t ω => VL₂ 0 t ω) (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ)
      (smallEightRhoR κ))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓗 fun ω => (τ ω : WithTop ℝ≥0)) :
    ∀ᵐ ω ∂P, 0 < τ ω → Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) (τ ω) →
      ∀ γ : ℝ → ℂ, IsSmallCrosscut x (W₁ · ω) (ζ₁ ω) γ →
        TipSeparated (Strip.extPath (W₂ · ω)) (τ ω) (γ '' Ioo 0 1) := by
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hRW, hch⟩ := hlaw τ hτ
  have hpath := hE.2.2.2.2
  have hend := hI hκ8 hτ.measurableSpace P _ _ _ 𝓖 W' VL' VR' B' ζ' hRW (by
    refine Eventually.of_forall fun ω hF => ⟨rfl, rfl, ?_⟩
    show 0 < W₂ (τ ω) ω - VL₂ 0 (τ ω) ω
    exact sub_pos.2 (hF.2 _ le_rfl))
  filter_upwards [hpath, hch, hend] with ω hp hchω hendω hτ0 hF γ hγ
  have hFP := hp.isForcePath
  exact tipSeparated_of_endpoint_path (v := (VL₂ 0 · ω)) hFP.continuousOn_w hFP.w_zero (hFP.continuousOn_vL 0)
    (fun t ht => by simpa using hFP.vL_eq ht 0) hF.1 hF.2 hτ0 hx hγ (hchω hF) (hendω hF)

end InteractingSLE.ZhanGT4.A2TipSep
