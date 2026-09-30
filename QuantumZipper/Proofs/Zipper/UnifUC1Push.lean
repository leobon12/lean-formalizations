import QuantumZipper.Proofs.Zipper.UnifUC1PushK
import QuantumZipper.Proofs.Zipper.UnifRC3Mix
import QuantumZipper.Proofs.GFF.CoordRegCompBasic
import QuantumZipper.Proofs.LQG.RegularSample

/-!
# UNIF-RC3-PUSH0 (decision D33): the uniform `ρ → 0` energy bound

For a continuous driver `W` (`W 0 = 0`), `T ≥ 0`, a folded circle `fc(d, 2^{-k})` and
`p = (u, s) ∈ tri T`, the circle-smoothed pushed circle `muUS W d k p ρ` satisfies

`|E(muUS p ρ − muUS p 0)| ≤ M ρ^{1/4}` for all `ρ ∈ (0, 1]`, with `M` **independent of `p`**

(`push0_unif`). Proof: `muUS p ρ = (ψ_u)_* (α ⋆ fc(·,ρ))`, `ψ_u = fwdMapInv W u = revMap (vrev W u) u`
on `ℍ`, `α = alphaUS W d k p`; apply `abs_energy_push_le_explicit` (the explicit-constant form of
`CoordReg.abs_energy_push_le`) with constants that are uniform over `p ∈ tri T`:

* support of `α` in `closedBall 0 Ra ∩ Hbar`, `Ra = revBound (2 sup|W|) T (‖d‖ + 2^{-k})`
  (`norm_revMap_le_revBound`, `abs_vrev_le`);
* Frostman `(1/3, frostC T 2^{-k} (‖d‖ + 2^{-k}))` (`RegCont.isFrostman_pfc_frostC`);
* `∫ |log Im| dα ≤ ∫ |log Im| dfc + |log Ra|` (`Im z ≤ Im R z ≤ Ra`);
* strip bound of `α` = that of `fc` (`CoordRegComp.stripBound_map`, `stripBound_foldedCircle`);
* the harmonic-correction constant of `ψ_u` from `abs_hK_le_explicit`, with the uniform bound
  `revBound (2 sup|W|) T (Ra + 1)` of `revMap (vrev W u) u`.

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 (energy of circle-average differences,
here transported through the Loewner map as in `CoordReg.abs_energy_push_le`, an own argument);
the uniformity bookkeeping is an own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace RegUnif

open CircleFubini FrostmanReg SmoothConv CoordReg B2

variable {W : ℝ → ℝ}

/-- Pointwise facts of the second unzip map along `fc(d, 2^{-k})`. -/
theorem alphaUS_ae_facts (hW : Continuous W) {T Mw : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw)
    (d : ℂ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T) :
    ∀ᵐ z ∂foldedCircle d (radius k), z ∈ H ∧ ‖z‖ ≤ ‖d‖ + radius k ∧
      z.im ≤ (revMap (vrev W (p.1 + p.2)) p.2 z).im ∧ revMap (vrev W (p.1 + p.2)) p.2 z ∈ H ∧
      ‖revMap (vrev W (p.1 + p.2)) p.2 z‖ ≤ RegCont.revBound (2 * Mw) T (‖d‖ + radius k) := by
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d (radius_pos k),
    TwoPoint.foldedCircle_ae_norm_le d (radius_pos k).le] with z hz hzn
  have hV := continuous_vrev hW (p.1 + p.2)
  refine ⟨hz, hzn, im_le_im_revMap _ hV z hz hp.2.1, TwoPoint.im_revMap_pos hV hz hp.2.1, ?_⟩
  exact (RegCont.norm_revMap_le_revBound hV hp.2.1
    (fun r _ => abs_vrev_le hM ⟨add_nonneg hp.1 hp.2.1, hp.2.2⟩ r) _ hzn).trans
    (RegCont.revBound_mono (by linarith [hp.1, hp.2.2]))

/-- `α ⋆ fc(·, 0) = α` for `α` carried by `ℍ`. -/
theorem bindFc_zero_of_ae_H {α : Measure ℂ} [IsFiniteMeasure α] (hα : ∀ᵐ z ∂α, z ∈ H) :
    RegCont.bindFc α 0 = α := by
  ext S hS
  rw [CircleFubini.bind_circle_apply α hS]
  simp_rw [RegSample.fc_zero, Measure.dirac_apply' _ hS]
  rw [← lintegral_indicator_one hS]
  refine lintegral_congr_ae (hα.mono fun z hz => ?_)
  have : foldH z = z := ite_eq_left_iff.2 fun h => absurd (le_of_lt hz) h
  simp only [this]

/-- **UNIF-RC3-PUSH0.** Uniform `ρ → 0` bound for the smoothed pushed circles. -/
theorem push0_unif (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) (d : ℂ) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ tri T, ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      |kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p 0) (muUS W d k p ρ, muUS W d k p 0)| ≤
        M * ρ ^ (1 / 4 : ℝ) := by
  obtain ⟨Mw, hMw'⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hMw : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw := fun t ht => by
    simpa [Real.norm_eq_abs] using hMw' t ht
  have hMw0 : 0 ≤ Mw := (abs_nonneg _).trans (hMw 0 ⟨le_rfl, hT⟩)
  set rk := radius k with hrkdef
  have hrk : 0 < rk := radius_pos k
  set R0 := ‖d‖ + rk with hR0
  set Ra := RegCont.revBound (2 * Mw) T R0 with hRa
  have hRa0 : 0 ≤ Ra := RegCont.revBound_nonneg (by linarith) hT
  set Bf := RegCont.revBound (2 * Mw) T (Ra + 1) with hBf
  set Mx := Real.sqrt ((Ra + 1) ^ 2 + 4 * T) with hMx
  set Bx := max (2 * Bf) (2 * (Ra + 1)) with hBx
  set K := |Real.log Mx| + 2 * |Real.log Bx| with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨C₀, hC₀, hLA⟩ := integral_abs_log_im_fc_le (Ra + 1)
  set L0 := ∫ z, |Real.log z.im| ∂foldedCircle d rk with hL0
  have hL00 : 0 ≤ L0 := integral_nonneg fun _ => abs_nonneg _
  set Lb := L0 + |Real.log Ra| with hLb
  set CF := RegCont.frostC T rk R0 with hCF
  have hCF0 : 0 ≤ CF := by rw [hCF]; unfold RegCont.frostC; positivity
  set c := 200 / Real.sqrt rk with hc
  have hc0 : 0 ≤ c := by positivity
  set M₁ := 2 * (K * 1 + 3 * (C₀ * 1 + Lb)) + 3 * 1 * (C₀ + 2) with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  refine ⟨6 * CF + 2 * M₁ * c, by positivity, fun p hp ρ hρ hρ1 => ?_⟩
  obtain ⟨u, s⟩ := p
  obtain ⟨hu, hs, hus⟩ := hp
  have hp : ((u, s) : ℝ × ℝ) ∈ tri T := ⟨hu, hs, hus⟩
  set V := vrev W (u + s) with hVdef
  have hV : Continuous V := continuous_vrev hW _
  have hRm := TwoPoint.measurable_revMap hV hs
  set α := alphaUS W d k (u, s) with hαdef
  have hαeq : α = (foldedCircle d rk).map (revMap V s) := rfl
  have hαP : IsProbabilityMeasure α := by
    rw [hαeq]; infer_instance
  have hfacts := alphaUS_ae_facts hW hMw d k hp
  have hSm := measurableSet_closedBall_inter_Hbar Ra
  have hsuppae : ∀ᵐ x ∂α, x ∈ closedBall 0 Ra ∩ Hbar := by
    rw [hαeq]
    refine (ae_map_iff hRm.aemeasurable hSm).2 (hfacts.mono fun z hz => ?_)
    exact ⟨mem_closedBall_zero_iff.2 hz.2.2.2.2, show (0 : ℝ) ≤ _ from le_of_lt hz.2.2.2.1⟩
  have hsupp : α (closedBall 0 Ra ∩ Hbar)ᶜ = 0 := ae_iff.1 hsuppae
  have hαH : ∀ᵐ x ∂α, x ∈ H := by
    rw [hαeq]
    exact (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2 (hfacts.mono fun z hz => hz.2.2.2.1)
  have hF : QuantumZipper.IsFrostman α (1 / 3) CF := fun w r hr =>
    RegCont.isFrostman_pfc_frostC hV hs (by linarith) hrk le_rfl le_rfl w r hr
  -- `|log Im|` on `α`
  have hlm : Measurable fun x : ℂ => |Real.log x.im| :=
    continuous_abs.measurable.comp (Real.measurable_log.comp Complex.measurable_im)
  have hl0 : Integrable (fun z : ℂ => |Real.log z.im|) (foldedCircle d rk) :=
    (TwoPoint.integrable_log_im_foldedCircle d hrk).abs
  have hlpt : ∀ᵐ z ∂foldedCircle d rk,
      |Real.log (revMap V s z).im| ≤ |Real.log z.im| + |Real.log Ra| :=
    hfacts.mono fun z hz => abs_log_le_of_mem' hz.1 hz.2.2.1
      ((Complex.im_le_norm _).trans hz.2.2.2.2)
  have hlc : Integrable (fun z => |Real.log (revMap V s z).im|) (foldedCircle d rk) :=
    Integrable.mono' (hl0.add (integrable_const _)) (hlm.comp hRm).aestronglyMeasurable
      (hlpt.mono fun z hz => by rw [Real.norm_eq_abs, abs_abs]; exact hz)
  have hlα : Integrable (fun z : ℂ => |Real.log z.im|) α := by
    rw [hαeq, integrable_map_measure hlm.aestronglyMeasurable hRm.aemeasurable]
    exact hlc
  have hLα : ∫ x, |Real.log x.im| ∂α ≤ Lb := by
    rw [hαeq, integral_map hRm.aemeasurable hlm.aestronglyMeasurable]
    calc ∫ z, |Real.log (revMap V s z).im| ∂foldedCircle d rk
        ≤ ∫ z, (|Real.log z.im| + |Real.log Ra|) ∂foldedCircle d rk :=
          integral_mono_ae hlc (hl0.add (integrable_const _)) hlpt
      _ = Lb := by rw [integral_add hl0 (integrable_const _)]; simp [hLb, hL0]
  have hS : CoordReg.StripBound α c (1 / 4) :=
    CoordRegComp.stripBound_map hRm (hfacts.mono fun z hz => ⟨hz.1, hz.2.2.1⟩) hl0
      (CoordRegComp.stripBound_foldedCircle d hrk)
  -- the harmonic correction of `ψ_u = revMap (vrev W u) u`
  have hVu : Continuous (vrev W u) := continuous_vrev hW u
  have hKb := abs_hK_le_explicit hVu hu (R := Ra + 1) (Bf := Bf) (M := Mx) (B := Bx)
    (fun z _ hz => (RegCont.norm_revMap_le_revBound hVu hu
      (fun r _ => abs_vrev_le hMw ⟨hu, by linarith⟩ r) _ hz).trans
        (RegCont.revBound_mono (by linarith)))
    (Real.sqrt_le_sqrt (by linarith)) (le_max_left _ _) (le_max_right _ _) (by linarith)
  have key := abs_energy_push_le_explicit hVu hu (K := K) hK0 hKb hC₀ hLA hsupp hαH hF
    (by norm_num) hlα hS hρ hρ1
  -- identify `muUS`
  have hαR : ∀ᵐ z ∂α, ‖z‖ ≤ Ra := hsuppae.mono fun z hz => mem_closedBall_zero_iff.1 hz.1
  have hmuρ : muUS W d k (u, s) ρ = (α.bind fun z => foldedCircle z ρ).map (revMap (vrev W u) u) := by
    refine Measure.map_congr ?_
    filter_upwards [bind_fc_mem_H_norm α hρ hαR] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hu hx.1
  have hmu0 : muUS W d k (u, s) 0 = α.map (revMap (vrev W u) u) := by
    show (RegCont.bindFc α 0).map (fwdMapInv W u) = _
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

end RegUnif
end QuantumZipper
