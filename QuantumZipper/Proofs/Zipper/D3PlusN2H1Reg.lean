import QuantumZipper.Proofs.Zipper.D3PlusN2H1RadFam
import QuantumZipper.Proofs.Zipper.D3PlusN2HarmP1
import QuantumZipper.Proofs.Zipper.D3PlusN2Cutoff
import QuantumZipper.Proofs.LQG.RegularClosure

/-!
# N2-H1: the regularized evaluation of the local field

Task N2-H1. For a local measure `ν` of the half-disc of radius `r`, and **given the
regularization of the free field at `ν`** (a.s. `∫ avgReg (X ω) k dν → X ω ν`), almost surely
`evalReg (locZField X r ω) ν = locZField X r ω ν`, i.e. the regularized evaluation of the local
field `Z = X − (harmonic part) − X(P₀)` is its raw coordinate `X ν − X (bal 0 r ν)`.

Route (own argument on top of the Markov decomposition `K3.markov_decomposition`, Sheffield,
*Gaussian free fields for mathematicians*, PTRF 139 (2007), Thm. 2.17, and the regular version
`WedgeTK.IsRegVersion` of the free field):
* on the countably many local dyadic folded circles, `Z (fc) = X (fc) − ∫ h dfc − X(P₀)` a.s.
  (Markov decomposition, `h = K3.harmH X 0 r r₁` continuous);
* hence, `avgReg Z k w = F(w, 2^{-k}) − ∫ h dfc(w, 2^{-k}) − X(P₀)` for `w` in the support of
  `ν` and `k` large (regularity of `X`, continuity of `h` and of folded-circle integrals);
* integrate against `ν` and let `k → ∞`: `∫ h dfc(w, 2^{-k}) → h w` boundedly, and the
  hypothesis gives `∫ avgReg X k dν → X ν`; the Markov decomposition at `ν` concludes.

The hypothesis is genuinely needed: the project has no a.s. convergence of `evalReg` at
arbitrary admissible measures (only good/Frostman measures, cf. `DECISIONS.md` D17,
`F2.EvalRegRawStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- The Markov identity on the countably many local dyadic folded circles. -/
theorem ae_locZField_dyadic_fc (hX : IsFreeGFFModConstH X P) {r r₁ : ℝ} (hr : 0 < r)
    (hr₁ : 0 < r₁) (hr₁r : r₁ < r) :
    ∀ᵐ ω ∂P, ∀ n k : ℕ, ∀ c ∈ Set.range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      locZField X r ω (foldedCircle c (radius k)) = X ω (foldedCircle c (radius k)) -
        ∫ u, K3.harmH X 0 r r₁ ω u ∂foldedCircle c (radius k) -
        X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro k
  rw [ae_ball_iff (countable_range_dyadicRoundC n)]
  intro c _
  by_cases hc : ‖c‖ + radius k ≤ r₁
  · have hadm := isAdmissibleH_foldedCircle' c (radius_pos k)
    have hsupp : foldedCircle c (radius k) (Metric.closedBall ((0 : ℝ) : ℂ) r₁)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.2 (Metric.closedBall_subset_closedBall hc))
        (foldedCircle_compl_closedBall (radius_pos k))
    have hloc : K3.IsLocalH 0 r (foldedCircle c (radius k)) := ⟨hadm, r₁, hr₁r, hsupp⟩
    filter_upwards [K3.markov_decomposition hX hr hr₁ hr₁r hadm hsupp] with ω h _
    rw [locZField_apply_of_local X ω hloc, h, measure_univ, ENNReal.toReal_one, one_mul]
    ring
  · exact ae_of_all _ fun ω h => absurd h hc

/-- Folded-circle integrals of a continuous function at vanishing radius. -/
theorem integral_fc_zero_radius {g : ℂ → ℝ} (hg : Continuous g) {w : ℂ} (hw : w ∈ Hbar) :
    ∫ u, g u ∂foldedCircle w 0 = g w := by
  rw [RegClosure.integral_fc_eq hg.continuousOn]
  simp only [circleMap_zero_radius, Function.const_apply, foldH_of_mem_Hbar hw,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp

theorem tendsto_integral_fc_radius {g : ℂ → ℝ} (hg : Continuous g) {w : ℂ} (hw : w ∈ Hbar) :
    Tendsto (fun k => ∫ u, g u ∂foldedCircle w (radius k)) atTop (𝓝 (g w)) := by
  have hc := (RegClosure.continuousOn_integral_fc_fun hg.continuousOn).continuousAt
    (x := (w, 0)) (by simp)
  rw [← integral_fc_zero_radius hg hw]
  exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds))

/-- The regularized circle averages of the local field, away from the boundary arc. -/
theorem avgReg_locZField_eq {r r₁ x₀ : ℝ} {ω : Ω} {F : ℂ × ℝ → ℝ} {H : ℂ → ℝ}
    (hF : IsRegularWith (X ω) F) (hH : Continuous H)
    (hA : ∀ n k : ℕ, ∀ c ∈ Set.range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      locZField X r ω (foldedCircle c (radius k)) = X ω (foldedCircle c (radius k)) -
        ∫ u, H u ∂foldedCircle c (radius k) - x₀)
    {k : ℕ} {w : ℂ} (hw : w ∈ Hbar) (hwk : ‖w‖ + radius k < r₁) :
    avgReg (locZField X r ω) k w = F (w, radius k) - ∫ u, H u ∂foldedCircle w (radius k) - x₀ := by
  unfold avgReg
  apply Tendsto.limUnder_eq
  have hev : ∀ᶠ n in atTop, ‖dyadicRoundC n w‖ + radius k ≤ r₁ := by
    have hδ : 0 < r₁ - (‖w‖ + radius k) := by linarith
    filter_upwards [(RegClosure.tendsto_dyadicRoundC w).eventually (Metric.ball_mem_nhds w hδ)]
      with n hn
    rw [dist_eq_norm] at hn
    have := norm_sub_norm_le (dyadicRoundC n w) w
    linarith
  have h1 : Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n w) (radius k))) atTop
      (𝓝 (F (w, radius k))) := hF.2.1 k w hw
  have h2 : Tendsto (fun n => ∫ u, H u ∂foldedCircle (dyadicRoundC n w) (radius k)) atTop
      (𝓝 (∫ u, H u ∂foldedCircle w (radius k))) := by
    have hc : Continuous (fun q : ℂ × ℝ => ∫ u, H u ∂foldedCircle q.1 q.2) :=
      continuousOn_univ.1 (RegClosure.continuousOn_integral_fc_fun hH.continuousOn)
    have hp : Tendsto (fun n => (dyadicRoundC n w, radius k)) atTop (𝓝 (w, radius k)) :=
      (RegClosure.tendsto_dyadicRoundC w).prodMk_nhds tendsto_const_nhds
    have h3 := (hc.tendsto (w, radius k)).comp hp
    simp only [Function.comp_def] at h3
    exact h3
  refine ((h1.sub h2).sub_const x₀).congr' ?_
  filter_upwards [hev] with n hn
  rw [hA n k (dyadicRoundC n w) (Set.mem_range_self w) hn]

theorem radius_le_one' (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

/-- **Regularized evaluation of the local field** at a local measure `ν`, given the
regularization of the free field at `ν`. -/
theorem ae_evalReg_locZField (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r)
    {ν : Measure ℂ} (hν : K3.IsLocalH 0 r ν)
    (hreg : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν) atTop (𝓝 (X ω ν))) :
    ∀ᵐ ω ∂P, evalReg (locZField X r ω) ν = locZField X r ω ν := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hν' := hν
  obtain ⟨hadm, r', hr'r, hνr⟩ := hν'
  have hfin : IsFiniteMeasure ν := hadm.1
  set m := max r' 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hmr : m < r := max_lt hr'r hr
  set r₁ := (m + r) / 2 with hr₁_def
  have hr₁ : 0 < r₁ := by rw [hr₁_def]; linarith
  have hr₁r : r₁ < r := by rw [hr₁_def]; linarith
  have hmr₁ : m < r₁ := by rw [hr₁_def]; linarith
  have hνr₁ : ν (Metric.closedBall ((0 : ℝ) : ℂ) r₁)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (Metric.closedBall_subset_closedBall
      ((le_max_left r' 0).trans hmr₁.le))) hνr
  have hHc : ∀ ω, Continuous (K3.harmH X 0 r r₁ ω) := K3.continuous_harmH hX hr hr₁ hr₁r
  obtain ⟨k0, hk0⟩ : ∃ k0, ∀ k ≥ k0, radius k < r₁ - m :=
    eventually_atTop.1 ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith)))
  have hνa : ∀ᵐ w ∂ν, w ∈ Hbar ∧ ‖w‖ ≤ m := by
    filter_upwards [ae_mem_Hbar_of_admissible hadm, ae_iff.2 hνr] with w h1 h2
    have : ‖w‖ ≤ r' := by simpa using h2
    exact ⟨h1, this.trans (le_max_left _ _)⟩
  filter_upwards [hG.reg, ae_locZField_dyadic_fc hX hr hr₁ hr₁r, hreg,
    K3.markov_decomposition hX hr hr₁ hr₁r hadm hνr₁] with ω hF hA hR hM
  have hS : ∀ k ≥ k0, ∫ z, avgReg (locZField X r ω) k z ∂ν =
      ∫ z, avgReg (X ω) k z ∂ν -
        ∫ w, (∫ u, K3.harmH X 0 r r₁ ω u ∂foldedCircle w (radius k)) ∂ν -
        (ν Set.univ).toReal * X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) := by
    intro k hk
    have hae : (fun z => avgReg (locZField X r ω) k z) =ᵐ[ν] fun z =>
        (avgReg (X ω) k z - ∫ u, K3.harmH X 0 r r₁ ω u ∂foldedCircle z (radius k)) -
          X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)) := by
      filter_upwards [hνa] with w hw
      rw [avgReg_locZField_eq hF (hHc ω) hA hw.1 (by linarith [hk0 k hk, hw.2]),
        hF.avgReg_eq k hw.1]
    have hI1 : Integrable (fun z => avgReg (X ω) k z) ν := by
      refine (integrable_of_continuousOn_Hbar (g := fun z => G ω (z, radius k))
        ((hG.cont ω).comp (continuousOn_id.prodMk continuousOn_const)
          (fun z hz => ⟨hz, radius_pos k⟩)) hadm).congr ?_
      filter_upwards [hνa] with w hw
      rw [hF.avgReg_eq k hw.1]
    have hI2 : Integrable
        (fun z => ∫ u, K3.harmH X 0 r r₁ ω u ∂foldedCircle z (radius k)) ν :=
      integrable_of_continuousOn_Hbar
        ((continuousOn_univ.1 (RegClosure.continuousOn_integral_fc_fun
          (hHc ω).continuousOn)).comp (continuous_id.prodMk continuous_const)).continuousOn hadm
    rw [integral_congr_ae hae, integral_sub, integral_sub hI1 hI2, integral_const, smul_eq_mul,
      measureReal_def]
    · exact hI1.sub hI2
    · exact integrable_const _
  have hD : Tendsto (fun k => ∫ w, (∫ u, K3.harmH X 0 r r₁ ω u ∂foldedCircle w (radius k)) ∂ν)
      atTop (𝓝 (∫ w, K3.harmH X 0 r r₁ ω w ∂ν)) := by
    obtain ⟨M, hMb⟩ := (isCompact_closedBall (0 : ℂ) (m + 1)).exists_bound_of_continuousOn
      (hHc ω).continuousOn
    refine tendsto_integral_of_dominated_convergence (fun _ => M) (fun k => ?_)
      (integrable_const M) (fun k => ?_) ?_
    · exact ((continuousOn_univ.1 (RegClosure.continuousOn_integral_fc_fun
        (hHc ω).continuousOn)).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hνa] with w hw
      have hb : ∀ᵐ u ∂foldedCircle w (radius k), ‖K3.harmH X 0 r r₁ ω u‖ ≤ M := by
        filter_upwards [ae_iff.2 (foldedCircle_compl_closedBall (d := w) (radius_pos k))] with u hu
        have hu' : ‖u‖ ≤ ‖w‖ + radius k := by simpa using hu
        exact hMb u (by
          rw [mem_closedBall_zero_iff]; linarith [radius_le_one' k, hw.2])
      have := norm_integral_le_of_norm_le_const hb
      simpa using this
    · filter_upwards [hνa] with w hw using tendsto_integral_fc_radius (hHc ω) hw.1
  have hlim : Tendsto (fun k => ∫ z, avgReg (locZField X r ω) k z ∂ν) atTop
      (𝓝 (X ω ν - ∫ w, K3.harmH X 0 r r₁ ω w ∂ν -
        (ν Set.univ).toReal * X ω (K3.halfDiscPoisson 0 r ((0 : ℝ) : ℂ)))) :=
    ((hR.sub hD).sub_const _).congr' (eventually_atTop.2 ⟨k0, fun k hk => (hS k hk).symm⟩)
  unfold evalReg
  rw [hlim.limUnder_eq, locZField_apply_of_local X ω hν, hM]
  ring

end D3Plus
end QuantumZipper
