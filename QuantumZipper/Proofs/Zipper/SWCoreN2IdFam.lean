import QuantumZipper.Proofs.Zipper.SWCoreNA2Unif
import QuantumZipper.Proofs.Zipper.SWCoreNA2Fam
import QuantumZipper.Proofs.Zipper.SWCoreV6

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2-ID (1): generic tools for the pathwise identification of pushed semicircle averages

Task SWC-N2-ID (helper of SWC-N2, `handoff/SW-CORE.md` §5, step (c)). For a jointly continuous
finite-parameter family of parametrized folded circles `Φ : ℝⁿ → ℝ → ℍ̄` with the box bounds of
`swcNA2_familyBounds` (bounded, `1`-Frostman, Lipschitz in the parameter), almost surely the
regularized pairing `q ↦ evalReg x (circM.map (Φ q))` is continuous in **all** parameters at once
and equals the raw value `X(circM.map (Φ q))` for each fixed `q` (`swcN2_ae_evalReg`). This is
the Kolmogorov modification of `swcNA2_tendstoUniformlyOn_avgReg` read pointwise
(Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1-type argument; Sheffield–Wang,
arXiv:1605.06171, Lemma 3.5 setting, p. 16).

Also: folding facts for circles with a real centre, the identity
`fc(s,r).map ψ = circM.map (ψ ∘ fold ∘ circleMap)` for maps continuous on the disc, and the
Frostman bound for a co-Lipschitz image of a folded circle (the arc bound of
`RegCont.foldedCircle_closedBall_le_arc`, as in the proof of `swcv_class_reg`). Own elementary
bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal Real

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

/-- Folding does not change the distance to a real point. -/
theorem swcN2_norm_foldH_sub_real (w : ℂ) (s : ℝ) : ‖foldH w - s‖ = ‖w - s‖ := by
  unfold foldH
  split_ifs
  · rfl
  · have : (starRingEnd ℂ) w - (s : ℂ) = (starRingEnd ℂ) (w - s) := by simp
    rw [this, Complex.norm_conj]

/-- Folding two points on the same side does not change their distance. -/
theorem swcN2_norm_foldH_sub_foldH {w w' : ℂ} (h : 0 ≤ w.im ↔ 0 ≤ w'.im) :
    ‖foldH w - foldH w'‖ = ‖w - w'‖ := by
  unfold foldH
  by_cases hw : 0 ≤ w.im
  · rw [if_pos hw, if_pos (h.1 hw)]
  · rw [if_neg hw, if_neg (fun h' => hw (h.2 h')), ← map_sub, Complex.norm_conj]

theorem swcN2_circleMap_im (s : ℝ) (R θ : ℝ) : (circleMap (s : ℂ) R θ).im = R * Real.sin θ := by
  simp [circleMap, Complex.exp_ofReal_mul_I_im]

/-- Two folded circle points with real centres and positive radii at the same angle. -/
theorem swcN2_norm_fold_circle_sub {s s' R R' : ℝ} (hR : 0 < R) (hR' : 0 < R') (θ : ℝ) :
    ‖foldH (circleMap (s : ℂ) R θ) - foldH (circleMap (s' : ℂ) R' θ)‖ ≤ |s - s'| + |R - R'| := by
  rw [swcN2_norm_foldH_sub_foldH (by
    rw [swcN2_circleMap_im, swcN2_circleMap_im]
    constructor <;> intro h
    · by_contra hc; push_neg at hc
      have : Real.sin θ < 0 := by
        by_contra h2; push_neg at h2; nlinarith
      nlinarith
    · by_contra hc; push_neg at hc
      have : Real.sin θ < 0 := by
        by_contra h2; push_neg at h2; nlinarith
      nlinarith)]
  have e : circleMap (s : ℂ) R θ - circleMap (s' : ℂ) R' θ =
      ((s - s' : ℝ) : ℂ) + ((R - R' : ℝ) : ℂ) * Complex.exp (θ * Complex.I) := by
    simp [circleMap]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]

/-- A folded circle point with a real centre stays on the circle. -/
theorem swcN2_fold_circle_mem {s R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    foldH (circleMap (s : ℂ) R θ) ∈ closedBall (s : ℂ) R := by
  rw [mem_closedBall, dist_eq_norm, swcN2_norm_foldH_sub_real, circleMap_sub_center,
    norm_circleMap_zero, abs_of_nonneg hR]

theorem swcN2_measurable_fold_circle (y : ℂ) (R : ℝ) :
    Measurable fun θ : ℝ => foldH (circleMap y R θ) :=
  (CircleFubini.continuous_foldH'.comp (continuous_circleMap y R)).measurable

/-- `fc(d, r)` as the image of the normalized angle measure. -/
theorem swcN2_fc_eq_map (y : ℂ) (R : ℝ) :
    foldedCircle y R = circM.map (fun θ => foldH (circleMap y R θ)) := by
  unfold foldedCircle
  rw [circleUnif_eq_map, Measure.map_map CircleFubini.continuous_foldH'.measurable
    (continuous_circleMap y R).measurable]
  rfl

/-- **Pushed folded circle with a real centre** as an image of the angle measure. -/
theorem swcN2_fc_map_eq {ψ : ℂ → ℂ} {s R : ℝ} (hR : 0 ≤ R)
    (hψ : ContinuousOn ψ (closedBall (s : ℂ) R)) :
    (foldedCircle (s : ℂ) R).map ψ = circM.map (fun θ => ψ (foldH (circleMap (s : ℂ) R θ))) := by
  classical
  set g : ℝ → ℂ := fun θ => foldH (circleMap (s : ℂ) R θ) with hg
  have hgm : Measurable g := swcN2_measurable_fold_circle _ _
  set ψm : ℂ → ℂ := (closedBall (s : ℂ) R).piecewise ψ id with hψm
  have hψmm : Measurable ψm :=
    ContinuousOn.measurable_piecewise hψ continuous_id.continuousOn measurableSet_closedBall
  have hnull : (circM.map g) (closedBall (s : ℂ) R)ᶜ = 0 := by
    rw [Measure.map_apply hgm measurableSet_closedBall.compl]
    convert measure_empty (μ := circM)
    ext θ
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact swcN2_fold_circle_mem hR θ
  have hsub : {x : ℂ | ¬ ψ x = ψm x} ⊆ (closedBall (s : ℂ) R)ᶜ := fun x hx hxc => by
    apply hx
    rw [hψm, piecewise_eq_of_mem _ _ _ hxc]
  rw [swcN2_fc_eq_map, Measure.map_congr (ae_iff.2 (measure_mono_null hsub hnull)),
    Measure.map_map hψmm hgm]
  congr 1
  funext θ
  simp only [comp_apply, hψm]
  rw [piecewise_eq_of_mem _ _ _ (swcN2_fold_circle_mem hR θ)]

/-- **Frostman bound** for a co-Lipschitz image of a folded circle (exponent `1`). -/
theorem swcN2_frostman {y : ℂ} {R c : ℝ} (hR : 0 < R) (hc : 0 < c) {F : ℝ → ℂ}
    (hF : Measurable F)
    (hco : ∀ θ θ', c * ‖foldH (circleMap y R θ) - foldH (circleMap y R θ')‖ ≤ ‖F θ - F θ'‖) :
    TwoPoint.IsFrostman (circM.map F) 1 (12 / (c * R)) := by
  intro p s hs
  set g : ℝ → ℂ := fun θ => foldH (circleMap y R θ) with hg
  rw [Measure.map_apply hF measurableSet_closedBall, Real.rpow_one]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  by_cases hex : ∃ θ₀, F θ₀ ∈ closedBall p s
  · obtain ⟨θ₀, hθ₀⟩ := hex
    have hsub : F ⁻¹' closedBall p s ⊆ g ⁻¹' closedBall (g θ₀) (2 * s / c) := by
      intro θ hθ
      rw [mem_preimage, mem_closedBall, dist_eq_norm, le_div_iff₀ hc]
      have a1 : ‖F θ - p‖ ≤ s := by rw [← dist_eq_norm]; exact hθ
      have a2 : ‖F θ₀ - p‖ ≤ s := by rw [← dist_eq_norm]; exact hθ₀
      have h2 : ‖F θ - F θ₀‖ ≤ 2 * s := by
        calc ‖F θ - F θ₀‖ = ‖(F θ - p) - (F θ₀ - p)‖ := by ring_nf
          _ ≤ ‖F θ - p‖ + ‖F θ₀ - p‖ := norm_sub_le _ _
          _ ≤ 2 * s := by linarith
      have := hco θ θ₀
      simp only [hg] at this ⊢
      linarith
    have hfc : circM (g ⁻¹' closedBall (g θ₀) (2 * s / c)) =
        foldedCircle y R (closedBall (g θ₀) (2 * s / c)) := by
      rw [swcN2_fc_eq_map, Measure.map_apply (swcN2_measurable_fold_circle y R)
        measurableSet_closedBall]
    calc circM (F ⁻¹' closedBall p s) ≤ circM (g ⁻¹' closedBall (g θ₀) (2 * s / c)) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (6 * (2 * s / c) / R) := by
          rw [hfc]
          exact RegCont.foldedCircle_closedBall_le_arc _ _ hR (by positivity)
      _ = ENNReal.ofReal (12 / (c * R) * s) := by congr 1; field_simp; ring
  · push_neg at hex
    have : F ⁻¹' closedBall p s = ∅ := by
      ext θ; simp only [mem_preimage, mem_empty_iff_false, iff_false]; exact hex θ
    rw [this, measure_empty]
    exact bot_le

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Pathwise continuity and identification along a finite-parameter family**: almost surely,
`q ↦ evalReg x (circM.map (Φ q))` is continuous on all of `ℝⁿ`, and for each `q` it equals the
raw value `X(circM.map (Φ q))` almost surely. -/
theorem swcN2_ae_evalReg {Φ : (Fin n → ℝ) → ℝ → ℂ} (hΦ : Continuous (uncurry Φ))
    (hΦH : ∀ q θ, Φ q θ ∈ Hbar)
    (hb : ∀ R : ℕ, ∃ B C H : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ 0 ≤ H ∧ ∀ q ∈ KolmD.boxD (d := n) R,
      (∀ θ, ‖Φ q θ‖ ≤ B) ∧ TwoPoint.IsFrostman (circM.map (Φ q)) 1 C ∧
      ∀ q' ∈ KolmD.boxD (d := n) R, ∀ θ, ‖Φ q θ - Φ q' θ‖ ≤ H * ‖q - q'‖ ^ (1 : ℝ))
    (hX : IsFreeGFFModConstH X P) :
    (∀ᵐ ω ∂P, Continuous fun q => evalReg (X ω) (circM.map (Φ q))) ∧
      ∀ q, ∀ᵐ ω ∂P, evalReg (X ω) (circM.map (Φ q)) = X ω (circM.map (Φ q)) := by
  obtain ⟨β, hβ, hB⟩ := swcNA2_familyBounds hΦ hΦH one_pos le_rfl one_pos le_rfl hb
  obtain ⟨Y₀, hc, hV, hU⟩ := swcNA2_tendstoUniformlyOn_avgReg (m := circM)
    (S := Icc 0 (2 * π)) hΦ hΦH isCompact_Icc circM_compl hβ hB hX
  have hE : ∀ᵐ ω ∂P, ∀ q, evalReg (X ω) (circM.map (Φ q)) = Y₀ q ω := by
    filter_upwards [hU] with ω h q
    exact ((h {q} isCompact_singleton).tendsto_at (mem_singleton q)).limUnder_eq
  refine ⟨?_, fun q => ?_⟩
  · filter_upwards [hE] with ω h
    simp only [h]
    exact hc ω
  · filter_upwards [hE, hV q] with ω h1 h2
    rw [h1, h2]

end SWCore
end QuantumZipper
