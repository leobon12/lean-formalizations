import QuantumZipper.Proofs.Zipper.SWCoreV1
import QuantumZipper.Proofs.Zipper.UnifSWHarmScale
import QuantumZipper.Proofs.Zipper.D3PlusN1Model
import QuantumZipper.Proofs.GFF.Admissible

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-V (2): energy distance between a pushed and the round semicircle

Task SWC-V (`handoff/SW-CORE.md` §5, item (i)). Sheffield–Wang, arXiv:1605.06171, Lemma 3.4
(3.17)–(3.19), p. 15, and the comparison (3.20): for a map `ψ`, a real point `t` with
`ψ(t)` real, a radius `r > 0` and `D > 0` (the derivative `ψ'(t)`), write
`T u = (ψ(t + r u) − ψ(t)) / (r D)` (the rescaled pushed semicircle). If `T` moves the closed unit
disc by at most `Δ ≤ 1`, is `½`-co-Lipschitz there and preserves `Im ≥ 0`, then

  `|kernelCov2 neumannH (fc(t,r).map ψ, fc(ψ t, r D)) (…)| ≤ 2 · holderK 24 2 · Δ^{1/6}`
                                                              (`swcv_kernelCov2_push`).

This is the variance of `X(fc(t,r).map ψ) − X(fc(ψ t, r ψ'(t)))` for the free field. For maps of a
rational `BdryClass`, Cauchy estimates give `Δ ≤ C r` uniformly (task SWC-V-CLASS), hence the
variance bound `≲ r^{1/6}` uniformly over the class. Proof: both measures are images of
`fc(0,1)`, `fc(t,r).map ψ = (fc(0,1).map T).map (u ↦ ψ t + r D u)`, the Neumann energy of a
balanced admissible pair is invariant under real affine maps (`RegUnif.kernelCov2_map_affine`),
and the unit-scale bound is `swcv_kernelCov2_unit`. Own assembly.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif TwoPoint

/-- `fc(s, ρ)` is the image of the unit folded circle under `u ↦ s + ρ u`. -/
theorem swcv_fc_eq_map (s : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    foldedCircle (s : ℂ) ρ = (foldedCircle 0 1).map (swhAff s ρ) := by
  unfold foldedCircle
  rw [circleUnif_eq_map_swhAff s ρ, Measure.map_map measurable_foldH (measurable_swhAff s ρ),
    Measure.map_map (measurable_swhAff s ρ) measurable_foldH]
  congr 1
  funext u
  exact foldH_swhAff s hρ u

/-- The rescaled map. -/
def swcvT (ψ : ℂ → ℂ) (t r D : ℝ) (u : ℂ) : ℂ := (ψ ((t : ℂ) + r * u) - ψ t) / (r * D)

/-- **Energy distance between the pushed and the round semicircle** (SW Lemma 3.4 / (3.20),
energy form). -/
theorem swcv_kernelCov2_push {ψ : ℂ → ℂ} {t r D Δ : ℝ} (hr : 0 < r) (hD : 0 < D)
    (hψt : (ψ t).im = 0) (hψc : ContinuousOn ψ (closedBall (t : ℂ) r)) (hΔ : 0 ≤ Δ)
    (hΔ1 : Δ ≤ 1)
    (hdisp : ∀ u ∈ closedBall (0 : ℂ) 1, ‖swcvT ψ t r D u - u‖ ≤ Δ)
    (hco : ∀ u ∈ closedBall (0 : ℂ) 1, ∀ v ∈ closedBall (0 : ℂ) 1,
      ‖u - v‖ / 2 ≤ ‖swcvT ψ t r D u - swcvT ψ t r D v‖)
    (him : ∀ u ∈ closedBall (0 : ℂ) 1, 0 ≤ u.im → 0 ≤ (swcvT ψ t r D u).im) :
    |kernelCov2 neumannH ((foldedCircle (t : ℂ) r).map ψ,
        foldedCircle (((ψ t).re : ℝ) : ℂ) (r * D))
        ((foldedCircle (t : ℂ) r).map ψ, foldedCircle (((ψ t).re : ℝ) : ℂ) (r * D))| ≤
      2 * (holderK 24 2 * Δ ^ ((1 / 3 : ℝ) / 2)) := by
  classical
  have hrD : 0 < r * D := mul_pos hr hD
  set B := closedBall (0 : ℂ) 1 with hB
  set T := swcvT ψ t r D with hTdef
  set μ₀ : Measure ℂ := foldedCircle 0 1 with hμ₀
  -- continuity of `T` on the unit disc
  have haffB : ∀ u ∈ B, (t : ℂ) + r * u ∈ closedBall (t : ℂ) r := fun u hu => by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    have : ‖u‖ ≤ 1 := by simpa [hB] using hu
    nlinarith
  have hTc : ContinuousOn T B := by
    have h1 : ContinuousOn (fun u : ℂ => ψ ((t : ℂ) + r * u)) B :=
      hψc.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn haffB
    exact (h1.sub continuousOn_const).div_const _
  set Tm : ℂ → ℂ := B.piecewise T id with hTm
  have hTmm : Measurable Tm :=
    ContinuousOn.measurable_piecewise hTc continuous_id.continuousOn measurableSet_closedBall
  have hTmB : ∀ u ∈ B, Tm u = T u := fun u hu => piecewise_eq_of_mem _ _ _ hu
  have hdisp' : ∀ u ∈ B, ‖Tm u - u‖ ≤ Δ := fun u hu => by rw [hTmB u hu]; exact hdisp u hu
  have hco' : ∀ u ∈ B, ∀ v ∈ B, ‖u - v‖ / 2 ≤ ‖Tm u - Tm v‖ := fun u hu v hv => by
    rw [hTmB u hu, hTmB v hv]; exact hco u hu v hv
  have hb' : ∀ u ∈ B, ‖Tm u‖ ≤ 2 := fun u hu => by
    have h1 := hdisp' u hu
    have h2 : ‖u‖ ≤ 1 := by simpa [hB] using hu
    calc ‖Tm u‖ = ‖(Tm u - u) + u‖ := by ring_nf
      _ ≤ ‖Tm u - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ 2 := by linarith
  have hunit := swcv_kernelCov2_unit hTmm hΔ hdisp' hco' hb'
  -- the unit folded circle lives in `B ∩ Hbar`
  have haeB : ∀ᵐ u ∂μ₀, u ∈ B := swcv_ae_norm_fc01.mono fun u hu => by
    rw [hB, mem_closedBall, dist_zero_right, hu]
  have haeH : ∀ᵐ u ∂μ₀, u ∈ Hbar := by
    have hHm : MeasurableSet {x : ℂ | x ∈ Hbar} :=
      measurableSet_le measurable_const Complex.measurable_im
    rw [hμ₀, foldedCircle, ae_map_iff measurable_foldH.aemeasurable hHm]
    exact Eventually.of_forall fun w => CircleFubini.foldH_mem_Hbar' w
  -- the pushed measure as an affine image of `μ₀.map Tm`
  set s0 : ℝ := (ψ t).re with hs0
  have hψt' : ψ t = (s0 : ℂ) := Complex.ext (by simp [hs0]) (by simp [hψt])
  set ψm : ℂ → ℂ := (closedBall (t : ℂ) r).piecewise ψ id with hψm
  have hψmm : Measurable ψm :=
    ContinuousOn.measurable_piecewise hψc continuous_id.continuousOn measurableSet_closedBall
  have hfc : foldedCircle (t : ℂ) r = μ₀.map (swhAff t r) := swcv_fc_eq_map t hr
  have hpush : (foldedCircle (t : ℂ) r).map ψ = (μ₀.map Tm).map (swhAff s0 (r * D)) := by
    have e1 : (foldedCircle (t : ℂ) r).map ψ = (foldedCircle (t : ℂ) r).map ψm := by
      have hnullT : (μ₀.map (swhAff t r)) (closedBall (t : ℂ) r)ᶜ = 0 := by
        rw [Measure.map_apply (measurable_swhAff t r) measurableSet_closedBall.compl]
        exact measure_mono_null (fun u hu hu1 => hu (haffB u hu1)) (ae_iff.1 haeB)
      rw [hfc]
      have hsub : {x : ℂ | ¬ ψ x = ψm x} ⊆ (closedBall (t : ℂ) r)ᶜ := fun x hx hxc => by
        apply hx
        rw [hψm, piecewise_eq_of_mem _ _ _ hxc]
      exact Measure.map_congr (ae_iff.2 (measure_mono_null hsub hnullT))
    rw [e1, hfc, Measure.map_map hψmm (measurable_swhAff t r),
      Measure.map_map (measurable_swhAff s0 (r * D)) hTmm]
    refine Measure.map_congr ?_
    filter_upwards [haeB] with u hu
    simp only [Function.comp_apply]
    have hmem : swhAff t r u ∈ closedBall (t : ℂ) r := haffB u hu
    rw [hψm, piecewise_eq_of_mem _ _ _ hmem, hTmB u hu, hTdef]
    unfold swhAff swcvT
    have hne : ((r : ℂ) * (D : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_mul]; exact Complex.ofReal_ne_zero.2 hrD.ne'
    rw [← hψt']
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
    have hD0 : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hD.ne'
    push_cast
    field_simp
    ring
  have hround : foldedCircle (s0 : ℂ) (r * D) = μ₀.map (swhAff s0 (r * D)) :=
    swcv_fc_eq_map s0 hrD
  -- admissibility of the unit pair
  have hK : IsCompact (B ∩ Hbar) := (isCompact_closedBall 0 1).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hKc : μ₀ (B ∩ Hbar)ᶜ = 0 := by
    have h := ae_iff.1 (haeB.and haeH)
    simpa [compl_def] using h
  have hadm0 : IsAdmissibleH μ₀ := D3Plus.isAdmissibleH_foldedCircle' 0 one_pos
  have hadm1 : IsAdmissibleH (μ₀.map Tm) := by
    refine isAdmissibleH_map hadm0 hK hKc hTmm ((hTc.congr fun u hu => hTmB u hu).mono
      inter_subset_left) ?_ (by norm_num : (0 : ℝ) < 1 / 2) fun x hx y hy => ?_
    · rintro _ ⟨u, ⟨hu, huH⟩, rfl⟩
      rw [hTmB u hu]
      exact him u hu huH
    · have := hco' x hx.1 y hy.1
      linarith
  have hmass : (μ₀.map Tm) univ = μ₀ univ := by
    rw [Measure.map_apply hTmm MeasurableSet.univ, preimage_univ]
  have hinv := kernelCov2_map_affine s0 hrD ⟨(μ₀.map Tm, μ₀), hadm1, hadm0, hmass⟩
  simp only at hinv
  rw [hpush, hround, hinv]
  exact hunit

end SWCore
end QuantumZipper
