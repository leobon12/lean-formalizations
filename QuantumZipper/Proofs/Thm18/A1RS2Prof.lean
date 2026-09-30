import QuantumZipper.Proofs.Thm18.A1RS2Z

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (6): continuity of continuous profiles against the smeared-loop family (deterministic)

**`continuousOn_integral_smearFam`**: for a good driver `W` and `f` continuous on `ℍ̄`,
`(p, ρ) ↦ ∫ f dν_{p,ρ}` (`ν_{p,ρ} = smearFam W left p ρ`) is continuous on `smearU × [0, ∞)`,
including the radius `ρ = 0`. This is the continuous-profile part (the `G` of `Z = X + α₀(−log|·|)
+ G`) of the continuity of `ρ ↦ evalReg Z ν_{p,ρ}` at `ρ = 0⁺`.

Dominated convergence in the two angles (`a1rfNu_eq_map_angles'`), with the joint continuity of
`(t, w) ↦ f_t(ψ(w))` (`sidePush_continuousAt`) and of `(t, u) ↦ f_t⁻¹(u)` on `[0, T] × ℍ`
(`RegUnif.continuousOn_fwdMapInv_joint`). Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

set_option maxHeartbeats 800000 in
/-- **Continuity of `∫ f dν_{p,ρ}` on `smearU × [0, ∞)` for `f` continuous on `ℍ̄`.** -/
theorem continuousOn_integral_smearFam {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool)
    {f : ℂ → ℝ} (hf : ContinuousOn f Hbar) (hfm : Measurable f) :
    ContinuousOn (fun x : (Fin 4 → ℝ) × ℝ => ∫ w, f w ∂(smearFam W left x.1 x.2))
      (smearU ×ˢ Ici 0) := by
  have hHH : ∀ {z : ℂ}, z ∈ H → z ∈ Hbar := fun {z} hz => show 0 ≤ z.im from le_of_lt hz
  set m2 : Measure (ℝ × ℝ) := G1RC.circM.prod E6.XAreaPC.angMeas with hm2
  set Φ : ℝ → ℂ → ℂ := fun t w => fwdMap W t (g1zSideMap left W w) with hΦ
  set u : ℝ → (Fin 4 → ℝ) × ℝ → ℂ := fun θ x => foldH (circleMap (parD x.1) (x.1 3) θ) with hu
  set v : ℝ × ℝ → (Fin 4 → ℝ) × ℝ → ℂ := fun q x =>
    foldH (circleMap (Φ (x.1 0) (u q.1 x)) x.2 q.2) with hv
  set F : (Fin 4 → ℝ) × ℝ → ℝ × ℝ → ℝ := fun x q => f (fwdMapInv W (x.1 0) (v q x)) with hF
  have hucont : ∀ θ, Continuous (u θ) := by
    intro θ
    have h1 : Continuous fun x : (Fin 4 → ℝ) × ℝ => parD x.1 := continuous_parD.comp continuous_fst
    simp only [hu, circleMap]
    exact CircleFubini.continuous_foldH'.comp (h1.add ((Complex.continuous_ofReal.comp
      ((continuous_apply 3).comp continuous_fst)).mul continuous_const))
  have hcm : ∀ (c : ℂ) (r : ℝ), Measurable fun θ : ℝ => foldH (circleMap c r θ) := fun c r =>
    measurable_foldH.comp (measurable_circleMap _ _)
  -- the angle representation
  have hA : ∀ x : (Fin 4 → ℝ) × ℝ, 0 < x.1 0 → 0 < x.1 3 →
      ∫ w, f w ∂(smearFam W left x.1 x.2) = ∫ q, F x q ∂m2 ∧
      AEStronglyMeasurable (F x) m2 := by
    intro x ht hs
    obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht left
    have hψm : Measurable fun q : ℝ × ℝ =>
        fwdMapInv W (x.1 0) (foldH (circleMap (g (foldH (circleMap (parD x.1) (x.1 3) q.1)))
          x.2 q.2)) :=
      (A1RF.measurable_smear (RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le) x.2).comp
        ((hgm.comp ((hcm _ _).comp measurable_fst)).prodMk measurable_snd)
    have hae : (fun q : ℝ × ℝ => f (fwdMapInv W (x.1 0) (foldH (circleMap
        (g (foldH (circleMap (parD x.1) (x.1 3) q.1))) x.2 q.2)))) =ᵐ[m2] F x := by
      have h1 := (Measure.quasiMeasurePreserving_fst (μ := G1RC.circM)
        (ν := E6.XAreaPC.angMeas)).ae (ae_circM_mem_H (parD x.1) hs)
      filter_upwards [h1] with q hq
      have e := hEq hq
      simp only at e
      simp only [hF, hv, hΦ, hu, e]
    refine ⟨?_, ((hfm.comp hψm).aestronglyMeasurable).congr hae⟩
    have e0 : smearFam W left x.1 x.2 = a1rfNu W (x.1 0) left (parD x.1) (x.1 3) x.2 := rfl
    rw [e0, a1rfNu_eq_map_angles' hG ht hgm hEq _ hs, integral_map hψm.aemeasurable
      hfm.aestronglyMeasurable]
    exact integral_congr_ae hae
  intro x₀ hx₀
  obtain ⟨⟨ht₀, hs₀⟩, hρ₀⟩ := hx₀
  have hρ₀' : (0 : ℝ) ≤ x₀.2 := hρ₀
  set D : Set ((Fin 4 → ℝ) × ℝ) := smearU ×ˢ Ici 0 with hD
  -- bounds near `x₀`
  have c0 : Continuous fun x : (Fin 4 → ℝ) × ℝ => x.1 0 := (continuous_apply 0).comp continuous_fst
  have c3 : Continuous fun x : (Fin 4 → ℝ) × ℝ => x.1 3 := (continuous_apply 3).comp continuous_fst
  have cd : Continuous fun x : (Fin 4 → ℝ) × ℝ => ‖parD x.1‖ :=
    continuous_norm.comp (continuous_parD.comp continuous_fst)
  have e1 : ∀ᶠ x in 𝓝 x₀, x.1 0 ∈ Ioo (x₀.1 0 / 2) (2 * x₀.1 0) :=
    c0.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have e3 : ∀ᶠ x in 𝓝 x₀, x.1 3 ∈ Ioo (x₀.1 3 / 2) (2 * x₀.1 3) :=
    c3.continuousAt.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  have e4 : ∀ᶠ x in 𝓝 x₀, x.2 < x₀.2 + 1 :=
    continuous_snd.continuousAt.eventually (Iio_mem_nhds (by linarith))
  have e2 : ∀ᶠ x in 𝓝 x₀, ‖parD x.1‖ < ‖parD x₀.1‖ + 1 :=
    cd.continuousAt.eventually (Iio_mem_nhds (by linarith))
  set R : ℝ := ‖parD x₀.1‖ + 1 + 2 * x₀.1 3 with hR
  have hT0 : 0 < 2 * x₀.1 0 := by linarith
  obtain ⟨B, hB⟩ := sidePush_bound hG left (T := 2 * x₀.1 0) R
  obtain ⟨Ci, -, hinv⟩ := norm_fwdMapInv_le_unif hG.1 hG.2.1 hT0
  set Bf : ℝ := B + (x₀.2 + 1) + Ci with hBf
  have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) Bf) :=
    (isCompact_closedBall (0 : ℂ) Bf).inter_left isClosed_Hbar
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono inter_subset_left)
  have hcont : ContinuousWithinAt (fun x => ∫ q, F x q ∂m2) D x₀ := by
    refine continuousWithinAt_of_dominated (bound := fun _ => C) ?_ ?_ (integrable_const C) ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hA x hx.1.1 hx.1.2).2
    · filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, nhdsWithin_le_nhds e3,
        nhdsWithin_le_nhds e4, self_mem_nhdsWithin] with x h1 h2 h3 h4 hxD
      have hs : 0 < x.1 3 := by linarith [h3.1]
      have ht : 0 < x.1 0 := by linarith [h1.1]
      have hx2 : 0 ≤ x.2 := hxD.2
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := G1RC.circM)
        (ν := E6.XAreaPC.angMeas)).ae (ae_circM_mem_H (parD x.1) hs)] with q hq
      have hun : ‖u q.1 x‖ ≤ R := by
        simp only [hu]
        rw [TwoPoint.norm_foldH]
        have := TwoPoint.norm_circleMap_le_add (parD x.1) hs.le q.1
        rw [hR]; linarith [h3.2]
      have hΦb : ‖Φ (x.1 0) (u q.1 x)‖ ≤ B := hB (x.1 0) ⟨ht, h1.2.le⟩ (u q.1 x) hq hun
      have hvb : ‖v q x‖ ≤ B + (x₀.2 + 1) := by
        simp only [hv]
        rw [TwoPoint.norm_foldH]
        have := TwoPoint.norm_circleMap_le_add (Φ (x.1 0) (u q.1 x)) hx2 q.2
        linarith
      have hib := hinv (x.1 0) ⟨ht, h1.2.le⟩ (v q x)
      refine hC _ ⟨F1.fwdMapInv_mem_Hbar W _ _, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      rw [hBf]; linarith
    · -- a.e. pair of angles: both folded-circle points lie in `ℍ`
      obtain ⟨-, -, g, hgm, hEq⟩ := A1R.sidePush_props hG ht₀ left
      have hmeas : MeasurableSet {q : ℝ × ℝ | foldH (circleMap (parD x₀.1) (x₀.1 3) q.1) ∈ H →
          foldH (circleMap (g (foldH (circleMap (parD x₀.1) (x₀.1 3) q.1))) x₀.2 q.2) ∈ H} := by
        have m1 : Measurable fun q : ℝ × ℝ => foldH (circleMap (parD x₀.1) (x₀.1 3) q.1) :=
          (hcm _ _).comp measurable_fst
        have m2' : Measurable fun q : ℝ × ℝ =>
            foldH (circleMap (g (foldH (circleMap (parD x₀.1) (x₀.1 3) q.1))) x₀.2 q.2) :=
          (A1RF.measurable_smear measurable_id x₀.2).comp ((hgm.comp m1).prodMk measurable_snd)
        exact (m1 isOpen_H.measurableSet).compl.union (m2' isOpen_H.measurableSet) |>.congr
          (by ext q; simp [imp_iff_not_or])
      have hae2 : ∀ᵐ q ∂m2, foldH (circleMap (parD x₀.1) (x₀.1 3) q.1) ∈ H →
          foldH (circleMap (g (foldH (circleMap (parD x₀.1) (x₀.1 3) q.1))) x₀.2 q.2) ∈ H := by
        refine (Measure.ae_prod_iff_ae_ae hmeas).2 (ae_of_all _ fun θ₁ => ?_)
        by_cases hθ : foldH (circleMap (parD x₀.1) (x₀.1 3) θ₁) ∈ H
        · have hgH : g (foldH (circleMap (parD x₀.1) (x₀.1 3) θ₁)) ∈ H := by
            rw [← hEq hθ]; exact (A1R.sidePush_props hG ht₀ left).2.1 hθ
          rcases hρ₀'.lt_or_eq with hpos | hzero
          · have h := TwoPoint.foldedCircle_ae_mem_H (g (foldH (circleMap (parD x₀.1) (x₀.1 3)
              θ₁))) hpos
            rw [E6.XAreaPC.foldedCircle_eq_map_angMeas] at h
            filter_upwards [(ae_map_iff (hcm _ _).aemeasurable isOpen_H.measurableSet).1 h]
              with θ₂ h2 _
            exact h2
          · refine ae_of_all _ fun θ₂ _ => ?_
            show 0 < (foldH (circleMap _ x₀.2 θ₂)).im
            rw [TwoPoint.im_foldH, ← hzero, circleMap_zero_radius]
            exact abs_pos.2 (ne_of_gt hgH)
        · exact ae_of_all _ fun θ₂ h => absurd h hθ
      have h1 := (Measure.quasiMeasurePreserving_fst (μ := G1RC.circM)
        (ν := E6.XAreaPC.angMeas)).ae (ae_circM_mem_H (parD x₀.1) hs₀)
      filter_upwards [h1, hae2] with q hq hq2
      have hu₀ : u q.1 x₀ ∈ H := hq
      have hv₀ : v q x₀ ∈ H := by
        have e := hEq hq
        simp only at e
        simp only [hv, hΦ, hu, e]
        exact hq2 hq
      -- continuity of the inner point
      have hΦc : ContinuousAt (fun x : (Fin 4 → ℝ) × ℝ => Φ (x.1 0) (u q.1 x)) x₀ :=
        (sidePush_continuousAt hG left ht₀ hu₀).comp
          (f := fun x : (Fin 4 → ℝ) × ℝ => (x.1 0, u q.1 x))
          (c0.continuousAt.prodMk (hucont q.1).continuousAt)
      have hvc : ContinuousAt (v q) x₀ := by
        have : v q = fun x => foldH (Φ (x.1 0) (u q.1 x) +
            (x.2 : ℂ) * Complex.exp ((q.2 : ℂ) * Complex.I)) := by
          funext x; simp [hv, circleMap]
        rw [this]
        exact CircleFubini.continuous_foldH'.continuousAt.comp (hΦc.add
          ((Complex.continuous_ofReal.continuousAt.comp continuous_snd.continuousAt).mul
            continuousAt_const))
      have hin : ContinuousAt (fun x : (Fin 4 → ℝ) × ℝ => ((x.1 0, v q x) : ℝ × ℂ)) x₀ :=
        c0.continuousAt.prodMk hvc
      have hev1 : ∀ᶠ x in 𝓝 x₀, ((x.1 0, v q x) : ℝ × ℂ) ∈ Icc 0 (2 * x₀.1 0) ×ˢ H := by
        filter_upwards [e1, hvc.eventually (isOpen_H.mem_nhds hv₀)] with x h1 hH
        exact ⟨⟨by linarith [h1.1], h1.2.le⟩, hH⟩
      have hJ : ContinuousWithinAt (fun p : ℝ × ℂ => fwdMapInv W p.1 p.2)
          (Icc 0 (2 * x₀.1 0) ×ˢ H) (x₀.1 0, v q x₀) :=
        RegUnif.continuousOn_fwdMapInv_joint hG.1 hG.2.1 (2 * x₀.1 0) _
          ⟨⟨ht₀.le, by linarith⟩, hv₀⟩
      have key : Tendsto ((fun p : ℝ × ℂ => fwdMapInv W p.1 p.2) ∘
          fun x : (Fin 4 → ℝ) × ℝ => ((x.1 0, v q x) : ℝ × ℂ)) (𝓝 x₀)
          (𝓝 (fwdMapInv W (x₀.1 0) (v q x₀))) :=
        hJ.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hin.tendsto, hev1⟩)
      have hev2 : ∀ᶠ x in 𝓝 x₀, ((fun p : ℝ × ℂ => fwdMapInv W p.1 p.2) ∘
          fun x : (Fin 4 → ℝ) × ℝ => ((x.1 0, v q x) : ℝ × ℂ)) x ∈ Hbar :=
        Eventually.of_forall fun x => F1.fwdMapInv_mem_Hbar W _ _
      have hfc : ContinuousWithinAt f Hbar (fwdMapInv W (x₀.1 0) (v q x₀)) :=
        hf _ (F1.fwdMapInv_mem_Hbar W _ _)
      have key2 := hfc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨key, hev2⟩)
      exact (show ContinuousAt (fun x => F x q) x₀ from key2).continuousWithinAt
  refine hcont.congr (fun x hx => (hA x hx.1.1 hx.1.2).1) (hA x₀ ht₀ hs₀).1

end A1RS
end R18
end QuantumZipper
