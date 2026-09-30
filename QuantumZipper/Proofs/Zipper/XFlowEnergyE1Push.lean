import QuantumZipper.Proofs.Zipper.XFlowEnergyE1Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-E1, step 2: the uniform `ρ → 0` energy bound for a general circle

`push0_flow`: `|E(flowMu p ρ − flowMu p 0)| ≤ M ρ^{1/4}` for `ρ ∈ (0, 1]`, with `M` uniform over
`FBox T rl R₀` (in particular over `flowBox m`). This is the D33 `RegUnif.push0_unif`
(`UnifUC1Push.lean`) with `fc(d, 2^{-k})` replaced by `fc(d, r)`: the constants depending on the
circle are replaced by uniform ones,

* Frostman constant `frostC T rl R₀` (`RegCont.isFrostman_pfc_frostC` with `rl ≤ r`,
  `‖d‖ + r ≤ R₀`);
* strip constant `200/√rl ≥ 200/√r` (`CoordRegComp.stripBound_foldedCircle`);
* `∫ |log Im| dfc(d, r) ≤ 200/√rl + |log R₀|` (`integral_abs_log_im_fc_unif`).

Sources: as `push0_unif` (Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1, transported
through the Loewner map as in `CoordReg.abs_energy_push_le`); uniformity is own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace F1

open CircleFubini FrostmanReg SmoothConv CoordReg B2 RegUnif

variable {W : ℝ → ℝ}

theorem stripBound_mono_const {ν : Measure ℂ} {c c' γ : ℝ} (h : CoordReg.StripBound ν c γ)
    (hc : c ≤ c') : CoordReg.StripBound ν c' γ := fun t ht ht1 =>
  (h t ht ht1).trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ht.le _))

/-- **PUSH0 for a general circle, uniform over `FBox T rl R₀`.** -/
theorem push0_flow (hW : Continuous W) (hW0 : W 0 = 0) {T rl R₀ : ℝ} (hT : 0 ≤ T)
    (hrl : 0 < rl) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : ℝ × ℝ × ℂ × ℝ, FBox T rl R₀ p → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |kernelCov2 neumannH (flowMu W p ρ, flowMu W p 0) (flowMu W p ρ, flowMu W p 0)| ≤
        M * ρ ^ (1 / 4 : ℝ) := by
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  set Ra := RegCont.revBound (2 * Mw) T R₀ with hRa
  have hRa0 : 0 ≤ Ra := RegCont.revBound_nonneg (by linarith) hT
  set Bf := RegCont.revBound (2 * Mw) T (Ra + 1) with hBf
  set Mx := Real.sqrt ((Ra + 1) ^ 2 + 4 * T) with hMx
  set Bx := max (2 * Bf) (2 * (Ra + 1)) with hBx
  set K := |Real.log Mx| + 2 * |Real.log Bx| with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨C₀, hC₀, hLA⟩ := integral_abs_log_im_fc_le (Ra + 1)
  set L0 := 200 / Real.sqrt rl + |Real.log R₀| with hL0
  have hL00 : 0 ≤ L0 := by positivity
  set Lb := L0 + |Real.log Ra| with hLb
  set CF := RegCont.frostC T rl R₀ with hCF
  have hCF0 : 0 ≤ CF := by rw [hCF]; unfold RegCont.frostC; positivity
  set c := 200 / Real.sqrt rl with hc
  have hc0 : 0 ≤ c := by positivity
  set M₁ := 2 * (K * 1 + 3 * (C₀ * 1 + Lb)) + 3 * 1 * (C₀ + 2) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  refine ⟨6 * CF + 2 * M₁ * c, by positivity, fun p hp ρ hρ hρ1 => ?_⟩
  have hu : 0 ≤ p.1 := hp.1
  have hs : 0 ≤ p.2.1 := hp.2.1
  have hus : p.1 + p.2.1 ≤ T := hp.2.2.1
  have hr : rl ≤ p.2.2.2 := hp.2.2.2.1
  have hR : ‖p.2.2.1‖ + p.2.2.2 ≤ R₀ := hp.2.2.2.2
  have hr0 : 0 < p.2.2.2 := hrl.trans_le hr
  set V := vrev W (p.1 + p.2.1) with hVdef
  have hV : Continuous V := continuous_vrev hW _
  have hRm := TwoPoint.measurable_revMap hV hs
  set α := flowNu W p with hαdef
  have hαeq : α = (foldedCircle p.2.2.1 p.2.2.2).map (revMap V p.2.1) := rfl
  have hαP : IsProbabilityMeasure α := by
    rw [hαeq]; infer_instance
  have hfacts := e1_flowNu_ae_facts hW hMw hrl hp
  have hSm := measurableSet_closedBall_inter_Hbar Ra
  have hsuppae : ∀ᵐ x ∂α, x ∈ closedBall 0 Ra ∩ Hbar := by
    rw [hαeq]
    refine (ae_map_iff hRm.aemeasurable hSm).2 (hfacts.mono fun z hz => ?_)
    exact ⟨mem_closedBall_zero_iff.2 hz.2.2.2.2, show (0 : ℝ) ≤ _ from le_of_lt hz.2.2.2.1⟩
  have hsupp : α (closedBall 0 Ra ∩ Hbar)ᶜ = 0 := ae_iff.1 hsuppae
  have hαH : ∀ᵐ x ∂α, x ∈ H := by
    rw [hαeq]
    exact (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2 (hfacts.mono fun z hz => hz.2.2.2.1)
  have hF : QuantumZipper.IsFrostman α (1 / 3) CF := fun w r hr' =>
    RegCont.isFrostman_pfc_frostC hV hs (by linarith) hrl hr hR w r hr'
  -- `|log Im|` on `α`
  have hlm : Measurable fun x : ℂ => |Real.log x.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  have hl0 : Integrable (fun z : ℂ => |Real.log z.im|) (foldedCircle p.2.2.1 p.2.2.2) :=
    (TwoPoint.integrable_log_im_foldedCircle p.2.2.1 hr0).abs
  have hlpt : ∀ᵐ z ∂foldedCircle p.2.2.1 p.2.2.2,
      |Real.log (revMap V p.2.1 z).im| ≤ |Real.log z.im| + |Real.log Ra| :=
    hfacts.mono fun z hz => abs_log_le_of_mem' hz.1 hz.2.2.1
      ((Complex.im_le_norm _).trans hz.2.2.2.2)
  have hlc : Integrable (fun z => |Real.log (revMap V p.2.1 z).im|)
      (foldedCircle p.2.2.1 p.2.2.2) :=
    Integrable.mono' (hl0.add (integrable_const _)) (hlm.comp hRm).aestronglyMeasurable
      (hlpt.mono fun z hz => by rw [Real.norm_eq_abs, abs_abs]; exact hz)
  have hlα : Integrable (fun z : ℂ => |Real.log z.im|) α := by
    rw [hαeq, integrable_map_measure hlm.aestronglyMeasurable hRm.aemeasurable]
    exact hlc
  have hL0le := integral_abs_log_im_fc_unif hrl hr hR
  have hLα : ∫ x, |Real.log x.im| ∂α ≤ Lb := by
    rw [hαeq, integral_map hRm.aemeasurable hlm.aestronglyMeasurable]
    calc ∫ z, |Real.log (revMap V p.2.1 z).im| ∂foldedCircle p.2.2.1 p.2.2.2
        ≤ ∫ z, (|Real.log z.im| + |Real.log Ra|) ∂foldedCircle p.2.2.1 p.2.2.2 :=
          integral_mono_ae hlc (hl0.add (integrable_const _)) hlpt
      _ = ∫ z, |Real.log z.im| ∂foldedCircle p.2.2.1 p.2.2.2 + |Real.log Ra| := by
          rw [integral_add hl0 (integrable_const _)]; simp
      _ ≤ Lb := by rw [hLb]; linarith
  have hS : CoordReg.StripBound α c (1 / 4) :=
    stripBound_mono_const (CoordRegComp.stripBound_map hRm
      (hfacts.mono fun z hz => ⟨hz.1, hz.2.2.1⟩) hl0
      (CoordRegComp.stripBound_foldedCircle p.2.2.1 hr0))
      (div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 hrl) (Real.sqrt_le_sqrt hr))
  -- the harmonic correction of `ψ_u = revMap (vrev W u) u`
  have hVu : Continuous (vrev W p.1) := continuous_vrev hW p.1
  have hKb := abs_hK_le_explicit hVu hu (R := Ra + 1) (Bf := Bf) (M := Mx) (B := Bx)
    (fun z _ hz => (RegCont.norm_revMap_le_revBound hVu hu
      (fun r _ => abs_vrev_le hMw ⟨hu, by linarith⟩ r) _ hz).trans
        (RegCont.revBound_mono (by linarith)))
    (Real.sqrt_le_sqrt (by linarith)) (le_max_left _ _) (le_max_right _ _) (by linarith)
  have key := abs_energy_push_le_explicit hVu hu (K := K) hK0 hKb hC₀ hLA hsupp hαH hF
    (by norm_num) hlα hS hρ hρ1
  -- identify `flowMu`
  have hαR : ∀ᵐ z ∂α, ‖z‖ ≤ Ra := hsuppae.mono fun z hz => mem_closedBall_zero_iff.1 hz.1
  have hmuρ : flowMu W p ρ =
      (α.bind fun z => foldedCircle z ρ).map (revMap (vrev W p.1) p.1) := by
    refine Measure.map_congr ?_
    filter_upwards [bind_fc_mem_H_norm α hρ hαR] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hu hx.1
  have hmu0 : flowMu W p 0 = α.map (revMap (vrev W p.1) p.1) := by
    show (RegCont.bindFc α 0).map (fwdMapInv W p.1) = _
    rw [bindFc_zero_of_ae_H hαH]
    refine Measure.map_congr ?_
    filter_upwards [hαH] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hu hx
  rw [hmuρ, hmu0]
  refine key.trans ?_
  have h1 : (α Set.univ).toReal = 1 := by simp
  have h2 : α.real univ = 1 := probReal_univ
  rw [h1, h2]
  have hpow : ρ ^ (1 / 3 : ℝ) ≤ ρ ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hρ.le hρ1 (by norm_num) (by norm_num)
  have hp4 : 0 ≤ ρ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hρ.le _
  have hM1le : 2 * (K * 1 + 3 * (C₀ * 1 + ∫ z, |Real.log z.im| ∂α)) + 3 * 1 * (C₀ + 2) ≤ M₁ := by
    rw [hM₁]; linarith
  have e1 : 2 * (CF * ρ ^ (1 / 3 : ℝ) / (1 / 3)) * 1 = 6 * CF * ρ ^ (1 / 3 : ℝ) := by ring
  rw [e1]
  have t1 : 6 * CF * ρ ^ (1 / 3 : ℝ) ≤ 6 * CF * ρ ^ (1 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have t2 : 2 * (2 * (K * 1 + 3 * (C₀ * 1 + ∫ z, |Real.log z.im| ∂α)) + 3 * 1 * (C₀ + 2)) *
      (c * ρ ^ (1 / 4 : ℝ)) ≤ 2 * M₁ * (c * ρ ^ (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  nlinarith [t1, t2]

end F1
end QuantumZipper
