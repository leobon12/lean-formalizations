import QuantumZipper.Proofs.Zipper.E1Main
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.Loewner.ReverseFlow
import QuantumZipper.Proofs.LQG.CoordChangeKernel

/-!
# E4-L3, deterministic inputs I: dominated convergence along the reverse flow

`handoff/E4.md`, item L3 (right-side law continuity), for Sheffield, arXiv:1012.4797, proof of
Lemma 5.6 (pp. 66–68). Fix a continuous driver `V` and a normalizer `ϖ` carried by a compact
`K ⊆ ℍ`. As `s ↑ τ`:

* `revMap_bounds`: `‖revMap V s z‖ ≤ R` and `Im (revMap V s z) ≥ δ > 0` for `z ∈ K`,
  `s ∈ [0, τ]`;
* `tendsto_integral_comp_revMap`: `∫ G (a s) (revMap V s z) dϖ(z) → ∫ G a₀ (revMap V τ z) dϖ(z)`
  when `a s → a₀` and `G` is continuous on `[a₀ − 1, a₀ + 1] × ℍ` (dominated convergence);
* `continuous_neuPot`: the Neumann potential of a Frostman measure with bounded support is
  continuous (from the Hölder bound `TwoPoint.abs_neuPot_sub_le`);
* `varpiT_facts`, `fc_facts`: probability, admissibility, Frostman (exponent `≤ 1`) and bounded
  support for `ϖ_s = ϖ.map (revMap V s)` and for the folded circles;
* `tendsto_qt`: `q_s → q_τ` (`log ‖(revMap V s)'‖ = Re ∫₀ˢ 2/u_r²`, dominated convergence).

These are own elementary arguments (dominated convergence; no published source is needed).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace E4Grid

open E1 TwoPoint

variable {V : ℝ → ℝ}

/-- Uniform bounds for the reverse flow on a compact subset of `ℍ` over `[0, τ]`. -/
theorem revMap_bounds (hV : Continuous V) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (τ : ℝ) : ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ z ∈ K, δ ≤ z.im ∧ ‖z‖ ≤ R ∧
      ∀ s ∈ Icc (0 : ℝ) τ, ‖revMap V s z‖ ≤ R ∧ δ ≤ (revMap V s z).im := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · exact ⟨1, 1, one_pos, one_pos, by simp [hKe]⟩
  obtain ⟨z₁, hz₁K, hz₁⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := τ)).exists_bound_of_continuousOn
    hV.continuousOn
  set δ := z₁.im with hδdef
  have hδ : 0 < δ := hKH hz₁K
  have hτ' : 0 ≤ 2 * |τ| / δ := by positivity
  refine ⟨δ, |R₀| + |M| + 2 * |τ| / δ + 1, hδ, by positivity, fun z hz => ?_⟩
  have hzδ : δ ≤ z.im := hz₁ hz
  have hzR : ‖z‖ ≤ |R₀| := by
    have := hR₀ z hz; rw [norm_norm] at this; exact this.trans (le_abs_self _)
  refine ⟨hzδ, by linarith [abs_nonneg M], fun s hs => ⟨?_, ?_⟩⟩
  · have h1 := RegCont.norm_revMap_sub_self_le hV (hKH hz) hs.1 (M := |M|) fun r hr => by
      have := hM r ⟨hr.1, hr.2.trans hs.2⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have h2 : 2 * s / z.im ≤ 2 * |τ| / δ :=
      div_le_div₀ (by positivity) (by linarith [le_abs_self τ, hs.2]) hδ hzδ
    calc ‖revMap V s z‖ ≤ ‖z‖ + ‖revMap V s z - z‖ := by
          have := norm_add_le z (revMap V s z - z); simpa using this
      _ ≤ _ := by linarith
  · exact hzδ.trans (im_le_im_revMap V hV z (hKH hz) hs.1)

theorem ae_mem_of_compl_null {ϖ : Measure ℂ} {K : Set ℂ} (hϖK : ϖ Kᶜ = 0) :
    ∀ᵐ z ∂ϖ, z ∈ K := ae_iff.2 hϖK

theorem tendsto_revMap_nhdsLT (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun s => revMap V s z) (𝓝[<] τ) (𝓝 (revMap V τ z)) :=
  ((ReverseFlow.continuousOn_revMap_time V hV z hz τ (show (0 : ℝ) ≤ τ from hτ.le)).continuousAt
    (Ici_mem_nhds hτ)).tendsto.mono_left nhdsWithin_le_nhds

/-- **Dominated convergence along the reverse flow.** -/
theorem tendsto_integral_comp_revMap (hV : Continuous V) {ϖ : Measure ℂ} [IsFiniteMeasure ϖ]
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0) {τ : ℝ} (hτ : 0 < τ)
    {G : ℝ → ℂ → ℝ} (hGm : Measurable (Function.uncurry G)) {a : ℝ → ℝ} {a₀ : ℝ}
    (ha : Tendsto a (𝓝[<] τ) (𝓝 a₀))
    (hGc : ContinuousOn (Function.uncurry G) (Icc (a₀ - 1) (a₀ + 1) ×ˢ H)) :
    Tendsto (fun s => ∫ z, G (a s) (revMap V s z) ∂ϖ) (𝓝[<] τ)
      (𝓝 (∫ z, G a₀ (revMap V τ z) ∂ϖ)) := by
  obtain ⟨δ, R, hδ, -, hb⟩ := revMap_bounds hV hK hKH τ
  set S : Set (ℝ × ℂ) := Icc (a₀ - 1) (a₀ + 1) ×ˢ (Metric.closedBall 0 R ∩ {w | δ ≤ w.im})
  have hSc : IsCompact S := isCompact_Icc.prod ((isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const Complex.continuous_im))
  have hSH : S ⊆ Icc (a₀ - 1) (a₀ + 1) ×ˢ H :=
    prod_mono le_rfl fun w hw => show 0 < w.im from hδ.trans_le hw.2
  obtain ⟨B, hB⟩ := hSc.exists_bound_of_continuousOn (hGc.mono hSH)
  have hKae := ae_mem_of_compl_null hϖK
  have hev : ∀ᶠ s in 𝓝[<] τ, s ∈ Ioo 0 τ ∧ a s ∈ Icc (a₀ - 1) (a₀ + 1) :=
    (show ∀ᶠ s in 𝓝[<] τ, s ∈ Ioo 0 τ from Ioo_mem_nhdsLT hτ).and
      (ha (Icc_mem_nhds (by linarith) (by linarith)))
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
    (integrable_const B) ?_
  · filter_upwards [hev] with s hs
    exact (hGm.comp (measurable_const.prodMk
      (measurable_revMap hV hs.1.1.le))).aestronglyMeasurable
  · filter_upwards [hev] with s hs
    filter_upwards [hKae] with z hz
    obtain ⟨-, -, h⟩ := hb z hz
    obtain ⟨h1, h2⟩ := h s ⟨hs.1.1.le, hs.1.2.le⟩
    exact hB (a s, revMap V s z) ⟨hs.2, by simpa using h1, h2⟩
  · filter_upwards [hKae] with z hz
    have hzH : z ∈ H := hKH hz
    have hc : ContinuousAt (Function.uncurry G) (a₀, revMap V τ z) :=
      hGc.continuousAt (prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
        (isOpen_H.mem_nhds (im_revMap_pos hV hzH hτ.le)))
    exact hc.tendsto.comp (ha.prodMk_nhds (tendsto_revMap_nhdsLT hV hzH hτ))

/-- The Neumann potential of a Frostman measure with bounded support is continuous. -/
theorem continuous_neuPot {κ : Measure ℂ} [IsFiniteMeasure κ] {α C B : ℝ}
    (hF : TwoPoint.IsFrostman κ α C) (hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C) (hB0 : 0 ≤ B)
    (hB : ∀ᵐ y ∂κ, ‖y‖ ≤ B) : Continuous (neuPot κ) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set X := ‖x‖ + 1
  set K0 := 2 * (κ.real univ + 4 * C / α) +
    2 * (2 * (C / α) + 2 * (Real.log (X + B + 1) * κ.real univ))
  have hev : ∀ᶠ x' in 𝓝 x, ‖x'‖ ≤ X := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with x' hx'
    rw [Metric.mem_ball, dist_eq_norm] at hx'
    have := norm_le_norm_add_norm_sub' x' x
    simp only [X]; linarith
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun x' => K0 * ‖x' - x‖ ^ (α / 2)) (𝓝 x) (𝓝 0) := by
    have h0 : Tendsto (fun x' => ‖x' - x‖) (𝓝 x) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 tendsto_id
    have h2 := ((Real.continuousAt_rpow_const 0 (α / 2) (Or.inr (by positivity))).tendsto.comp
      h0).const_mul K0
    simpa [Real.zero_rpow (by positivity : α / 2 ≠ 0)] using h2
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  filter_upwards [hev] with x' hx'
  rw [Real.dist_eq]
  exact abs_neuPot_sub_le hF hα hα1 hC hB0 hB hx' (by simp only [X]; linarith)

/-- A Frostman bound with exponent `α` gives one with exponent `min α 1`. -/
theorem isFrostman_min_one {ν : Measure ℂ} [IsFiniteMeasure ν] {α C : ℝ} (hα : 0 < α)
    (h : TwoPoint.IsFrostman ν α C) :
    TwoPoint.IsFrostman ν (min α 1) (max C (ν.real univ)) := by
  have hC0 : 0 ≤ C := by
    have := h 0 1 one_pos
    rw [Real.one_rpow, mul_one] at this
    exact ENNReal.toReal_nonneg.trans this
  intro w r hr
  rcases le_or_gt r 1 with h1 | h1
  · calc (ν (Metric.closedBall w r)).toReal ≤ C * r ^ α := h w r hr
      _ ≤ max C (ν.real univ) * r ^ (min α 1) :=
        mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_ge hr h1 (min_le_left _ _))
          (by positivity) (le_max_of_le_left hC0)
  · calc (ν (Metric.closedBall w r)).toReal ≤ ν.real univ := measureReal_mono (subset_univ _)
      _ ≤ max C (ν.real univ) * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_rpow h1.le (by positivity))
          (le_max_of_le_right measureReal_nonneg)

/-- Standing facts about a probability measure used below. -/
structure GoodMeas (ν : Measure ℂ) : Prop where
  prob : IsProbabilityMeasure ν
  adm : IsAdmissibleH ν
  frost : ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ TwoPoint.IsFrostman ν α C
  bdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ y ∂ν, ‖y‖ ≤ B

theorem GoodMeas.continuous_neuPot {ν : Measure ℂ} (h : GoodMeas ν) : Continuous (neuPot ν) := by
  have := h.prob
  obtain ⟨α, C, hα, hα1, hC, hF⟩ := h.frost
  obtain ⟨B, hB0, hB⟩ := h.bdd
  exact E4Grid.continuous_neuPot hF hα hα1 hC hB0 hB

/-- `ϖ_s` is a good measure. -/
theorem varpiT_good (hV : Continuous V) {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0) {α C : ℝ} (hα : 0 < α)
    (hF : IsFrostman ϖ α C) {s : ℝ} (hs : 0 ≤ s) : GoodMeas (varpiT V s ϖ) := by
  have hm := measurable_revMap hV hs
  have hP : IsProbabilityMeasure (varpiT V s ϖ) := by
    simp only [varpiT]; infer_instance
  obtain ⟨R, hR⟩ := B2.map_revMap_support_of_compact hV hs hK hKH hϖK
  obtain ⟨C', hC'⟩ := B2.isFrostman_map_revMap_of_compact hV hs hK hKH hϖK hα.le hF
  refine ⟨hP, FrostmanReg.isAdmissibleH_of_frostman hR hC' hα, ?_, ?_⟩
  · exact ⟨min α 1, max C' ((varpiT V s ϖ).real univ), lt_min hα one_pos, min_le_right _ _,
      le_max_of_le_right measureReal_nonneg, isFrostman_min_one hα fun p ρ hρ => hC' p ρ hρ⟩
  · refine ⟨|R|, abs_nonneg _, ?_⟩
    filter_upwards [ae_mem_of_compl_null hR] with y hy
    exact (mem_closedBall_zero_iff.1 hy.1).trans (le_abs_self _)

/-- The folded circles of positive radius are good measures. -/
theorem fc_good (w : ℂ) {r : ℝ} (hr : 0 < r) : GoodMeas (foldedCircle w r) := by
  refine ⟨inferInstance, ?_, ⟨1, 6 / r, one_pos, le_rfl, by positivity, fun p t ht => ?_⟩,
    ⟨‖w‖ + r, by positivity, TwoPoint.foldedCircle_ae_norm_le w hr.le⟩⟩
  · rw [← CoordReg.foldedCircle_foldH]
    exact isAdmissibleH_foldedCircle (CircleFubini.foldH_mem_Hbar' _) hr
  · have := RegCont.foldedCircle_closedBall_le_arc w p hr ht.le
    rw [Real.rpow_one, show 6 / r * t = 6 * t / r by ring]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) this

/-! ## `q_s → q_τ` -/

theorem tendsto_log_norm_deriv_revMap (hV : Continuous V) {z : ℂ} (hz : z ∈ H) {τ : ℝ}
    (hτ : 0 < τ) :
    Tendsto (fun s => Real.log ‖deriv (revMap V s) z‖) (𝓝[<] τ)
      (𝓝 (Real.log ‖deriv (revMap V τ) z‖)) := by
  have hII : IntervalIntegrable (fun r => 2 / revMap V r z ^ 2) MeasureTheory.volume 0 τ :=
    RegCont.intervalIntegrable_two_div_sq_revMap hV hz hτ.le
  have hc : ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, 2 / revMap V r z ^ 2) (uIcc 0 τ) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hτ.le]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hτ.le).1 hII)
  have hc' : ContinuousWithinAt (fun s => ∫ r in (0 : ℝ)..s, 2 / revMap V r z ^ 2)
      (Iio τ) τ := by
    refine (hc τ right_mem_uIcc).mono_of_mem_nhdsWithin ?_
    rw [uIcc_of_le hτ.le]
    exact mem_of_superset (Ioo_mem_nhdsLT hτ) Ioo_subset_Icc_self
  have hre := (Complex.continuous_re.tendsto _).comp hc'.tendsto
  rw [log_norm_deriv_revMap V hV hτ.le hz]
  refine hre.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
  rw [log_norm_deriv_revMap V hV hs.1.le hz]; rfl

theorem tendsto_qt (κ : ℝ) (hV : Continuous V) {ϖ : Measure ℂ} [IsFiniteMeasure ϖ] {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun s => B2.qt κ V s ϖ) (𝓝[<] τ) (𝓝 (B2.qt κ V τ ϖ)) := by
  obtain ⟨δ, R, hδ, -, hb⟩ := revMap_bounds hV hK hKH τ
  have hKae := ae_mem_of_compl_null hϖK
  refine Tendsto.const_mul _ (tendsto_integral_filter_of_dominated_convergence
    (fun _ => 2 * τ / δ ^ 2) ?_ ?_ (integrable_const _) ?_)
  · exact Eventually.of_forall fun s =>
      (Real.measurable_log.comp (measurable_deriv _).norm).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
    filter_upwards [hKae] with z hz
    have hzH : z ∈ H := hKH hz
    rw [Real.norm_eq_abs]
    refine (RegCont.abs_log_norm_deriv_revMap_le_small hV hs.1.le hzH).trans ?_
    have hzδ := (hb z hz).1
    have : δ ^ 2 ≤ z.im ^ 2 := pow_le_pow_left₀ hδ.le hzδ 2
    exact div_le_div₀ (by positivity) (by linarith [hs.2]) (by positivity) this
  · filter_upwards [hKae] with z hz
    exact tendsto_log_norm_deriv_revMap hV (hKH hz) hτ

end E4Grid
end QuantumZipper
