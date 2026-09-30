import QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# RG-1 (energy estimate FOLD-BOUND) and RG-4 (linear splitting)

Blueprint `THM11_BLUEPRINT.md` §7.

## RG-1

Let `μ` be a finite measure on `ℂ` carried by `ℍ` (`μ {Im ≤ 0} = 0`), with bounded
zero-boundary Green potential `∫⁻ G⁺(x, ·) dμ ≤ U` for `x ∈ ℍ`, and a Frostman bound
`μ (B(x,s)) ≤ K s^α` at centres of height `≥ h`, radii `s ≤ h/2`. Let
`ν = μ.bind (foldedCircle · r)` be its folded-circle smoothing at radius `r`, `4r ≤ h`. Then
(`abs_energy_foldSmooth_le`)

  `|𝓔_G(ν − μ)| ≤ (2U + 8 μ(ℂ)) μ{Im < 2h} + (1/α + 4·2^α) K r^α μ(ℂ)`.

Proof. Write `P_η(x) = ∫⁻ G⁺(x,·) dη` and `SP_η(z) = ∫⁻ P_η d(foldedCircle z r)`. Then
`𝓔 = ∫ (SP_ν − SP_μ − P_ν + P_μ) dμ`. The smoothed potential is bounded,
`P_ν ≤ U + 8 μ(ℂ)` on `Hbar`: for `Im z ≥ r` the circle average of `G(·,x)` is `≤ G(z,x)`
(mean value), and for `Im z < r` the folded-circle average of `G(·,x)` is `≤ 8`
(`G(v,x) ≤ 4 + log⁺(r/|v−x|)` when `Im v ≤ 2r`, and circle averages of `log⁺(r/|·−c|)` are
`≤ log 3`). For `Im z ≥ r` the mean value formula gives `G(z,y) = k(z,y) + log⁺(r/|y−z|)`
with `k` the circle average, hence `P_η(z) = SP_η(z) + ∫⁻ log⁺(r/|y−z|) dη(y)`, and the
integrand is `∫ log⁺ dμ − ∫ log⁺ dν`, which the Frostman bound controls when `Im z ≥ 2h`.

## RG-4

Additivity of `avgReg`, `evalReg`, `pairTest`, `pairRaw` in the field when the limits exist,
linearity of `evalReg` in the measure and of `pairTest` in the test function, and
`pairRaw (ofFun g + x) ρ = ∫ ρ g + pairRaw x ρ`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Real ComplexConjugate ENNReal NNReal Topology

namespace QuantumZipper

namespace FoldBound

/-! ## Folding and circles -/

theorem fb_foldH_mem_Hbar (u : ℂ) : foldH u ∈ Hbar := by
  show 0 ≤ (foldH u).im
  unfold foldH
  split_ifs with h
  · exact h
  · simp only [Complex.conj_im]; linarith [not_le.mp h]

theorem fb_measurable_fc (r : ℝ) : Measurable fun w => foldedCircle w r :=
  Measure.measurable_of_measurable_coe _ fun _ hs => measurable_foldedCircle_apply r hs

/-- The folded-circle averaging kernel at radius `r`. -/
def fbKernel (r : ℝ) : ProbabilityTheory.Kernel ℂ ℂ := ⟨fun w => foldedCircle w r, fb_measurable_fc r⟩

theorem fb_foldH_im (u : ℂ) : (foldH u).im = |u.im| := by
  unfold foldH
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · have h' : u.im < 0 := not_le.mp h
    simp [abs_of_neg h']

theorem fb_norm_foldH_sub_le {u w : ℂ} (hw : w ∈ Hbar) : ‖foldH u - w‖ ≤ ‖u - w‖ := by
  unfold foldH
  split_ifs with h
  · exact le_rfl
  · have hu : u.im < 0 := not_le.mp h
    have hw' : 0 ≤ w.im := hw
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
    nlinarith [mul_nonneg (neg_nonneg.mpr hu.le) hw']

theorem fb_circleUnif_singleton (z : ℂ) {r : ℝ} (hr : r ≠ 0) (x : ℂ) :
    circleUnif z r {x} = 0 := by
  rw [CircleMV.circleUnif_eq_circMeas]
  exact LQGDimension.Coupling.circMeas_singleton hr x

theorem fb_fc_singleton (z : ℂ) {r : ℝ} (hr : r ≠ 0) (x : ℂ) : foldedCircle z r {x} = 0 := by
  rw [foldedCircle, Measure.map_apply measurable_foldH (measurableSet_singleton x)]
  refine measure_mono_null (t := {x} ∪ {conj x}) ?_
    (measure_union_null (fb_circleUnif_singleton z hr x) (fb_circleUnif_singleton z hr _))
  intro u hu
  simp only [mem_preimage, mem_singleton_iff] at hu
  unfold foldH at hu
  split_ifs at hu
  · exact Or.inl hu
  · right
    show u = conj x
    rw [← hu, Complex.conj_conj]

theorem fb_fc_compl_Hbar (w : ℂ) (r : ℝ) : foldedCircle w r Hbarᶜ = 0 := by
  rw [foldedCircle, Measure.map_apply measurable_foldH isClosed_Hbar.measurableSet.compl]
  have : foldH ⁻¹' Hbarᶜ = ∅ := by
    ext u; simp [fb_foldH_mem_Hbar u]
  rw [this, measure_empty]

theorem fb_ae_fc (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz : z ∈ Hbar) :
    ∀ᵐ v ∂foldedCircle z r, v ∈ Hbar ∧ ‖v - z‖ ≤ r ∧ v.im ≤ z.im + r := by
  rw [foldedCircle]
  have hS : MeasurableSet {v : ℂ | v ∈ Hbar ∧ ‖v - z‖ ≤ r ∧ v.im ≤ z.im + r} := by
    have : MeasurableSet (Hbar ∩ ({v : ℂ | ‖v - z‖ ≤ r} ∩ {v : ℂ | v.im ≤ z.im + r})) :=
      isClosed_Hbar.measurableSet.inter
        ((measurableSet_le (measurable_id.sub_const z).norm measurable_const).inter
          (measurableSet_le Complex.measurable_im measurable_const))
    exact this
  refine (ae_map_iff measurable_foldH.aemeasurable hS).2 ?_
  filter_upwards [CircleMV.ae_circleUnif z r] with u hu
  rw [abs_of_nonneg hr] at hu
  refine ⟨fb_foldH_mem_Hbar u, (fb_norm_foldH_sub_le hz).trans hu.le, ?_⟩
  rw [fb_foldH_im]
  have h1 : |(u - z).im| ≤ ‖u - z‖ := Complex.abs_im_le_norm _
  rw [hu, Complex.sub_im, abs_le] at h1
  have hz' : 0 ≤ z.im := hz
  exact abs_le.2 ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem fb_greenH_of_im_eq_zero {x : ℂ} (hx : x.im = 0) (y : ℂ) : greenH x y = 0 := by
  have hc : conj x = x := Complex.conj_eq_iff_im.2 hx
  have : ‖x - conj y‖ = ‖x - y‖ := by
    rw [← Complex.norm_conj (x - y), map_sub, hc]
  simp [greenH, this]

theorem fb_measurable_logPos (r : ℝ) (c : ℂ) :
    Measurable fun y : ℂ => ENNReal.ofReal (Real.log (r / ‖y - c‖)) :=
  ENNReal.measurable_ofReal.comp
    (Real.measurable_log.comp (measurable_const.div (measurable_id.sub_const c).norm))

/-! ## Circle averages of `log⁺ (r / |· - c|)` -/

theorem fb_lintegral_logPos_circle_le (w c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ u, ENNReal.ofReal (Real.log (r / ‖u - c‖)) ∂circleUnif w r ≤
      ENNReal.ofReal (Real.log 3) := by
  rcases le_or_gt (2 * r) ‖w - c‖ with hfar | hnear
  · have hz : ∀ᵐ u ∂circleUnif w r, ENNReal.ofReal (Real.log (r / ‖u - c‖)) = 0 := by
      filter_upwards [CircleMV.ae_circleUnif w r] with u hu
      rw [abs_of_pos hr] at hu
      have h1 : r ≤ ‖u - c‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub w u c
        rw [norm_sub_rev w u, hu] at this
        linarith
      exact ENNReal.ofReal_eq_zero.2
        (Real.log_nonpos (by positivity) ((div_le_one (hr.trans_le h1)).2 h1))
    exact (lintegral_congr_ae hz).trans_le (by simp)
  · have hint : Integrable (fun u => Real.log (3 * r) - Real.log ‖u - c‖) (circleUnif w r) :=
      (integrable_const _).sub (CircleMV.integrable_log_norm_sub_circleUnif w c r)
    have hne : ∀ᵐ u ∂circleUnif w r, u ≠ c := by
      rw [ae_iff]; simpa using fb_circleUnif_singleton w hr.ne' c
    have hnn : 0 ≤ᵐ[circleUnif w r] fun u => Real.log (3 * r) - Real.log ‖u - c‖ := by
      filter_upwards [CircleMV.ae_circleUnif w r, hne] with u hu huc
      rw [abs_of_pos hr] at hu
      have hpos : 0 < ‖u - c‖ := norm_pos_iff.2 (sub_ne_zero.2 huc)
      have hle : ‖u - c‖ ≤ 3 * r := by
        calc ‖u - c‖ ≤ ‖u - w‖ + ‖w - c‖ := norm_sub_le_norm_sub_add_norm_sub u w c
          _ ≤ 3 * r := by rw [hu]; linarith
      simp only [Pi.zero_apply]
      linarith [Real.log_le_log hpos hle]
    calc ∫⁻ u, ENNReal.ofReal (Real.log (r / ‖u - c‖)) ∂circleUnif w r
        ≤ ∫⁻ u, ENNReal.ofReal (Real.log (3 * r) - Real.log ‖u - c‖) ∂circleUnif w r := by
          refine lintegral_mono_ae ?_
          filter_upwards [hne] with u huc
          have hpos : 0 < ‖u - c‖ := norm_pos_iff.2 (sub_ne_zero.2 huc)
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.log_div hr.ne' hpos.ne']
          linarith [Real.log_le_log hr (by linarith : r ≤ 3 * r)]
      _ = ENNReal.ofReal (∫ u, (Real.log (3 * r) - Real.log ‖u - c‖) ∂circleUnif w r) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ ≤ ENNReal.ofReal (Real.log 3) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_sub (integrable_const _) (CircleMV.integrable_log_norm_sub_circleUnif w c r),
            integral_const, integral_log_norm_sub_circleUnif w c hr]
          simp only [probReal_univ, smul_eq_mul, one_mul]
          rw [Real.log_mul (by norm_num) hr.ne']
          linarith [Real.log_le_log hr (le_max_left r ‖w - c‖)]

theorem fb_lintegral_logPos_fc_le {w : ℂ} (hw : w ∈ Hbar) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫⁻ v, ENNReal.ofReal (Real.log (r / ‖v - c‖)) ∂foldedCircle w r ≤
      (Metric.ball c (2 * r)).indicator (fun _ => (4 : ℝ≥0∞)) w := by
  have hm := fb_measurable_logPos r c
  by_cases hwc : w ∈ Metric.ball c (2 * r)
  · rw [indicator_of_mem hwc, foldedCircle, lintegral_map hm measurable_foldH]
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
    calc ∫⁻ u, ENNReal.ofReal (Real.log (r / ‖foldH u - c‖)) ∂circleUnif w r
        ≤ ∫⁻ u, (ENNReal.ofReal (Real.log (r / ‖u - c‖)) +
            ENNReal.ofReal (Real.log (r / ‖u - conj c‖))) ∂circleUnif w r := by
          refine lintegral_mono fun u => ?_
          unfold foldH
          split_ifs
          · exact le_self_add
          · rw [CircleMV.norm_foldH_sub_conj]; exact le_add_self
      _ = _ := lintegral_add_left hm _
      _ ≤ ENNReal.ofReal (Real.log 3) + ENNReal.ofReal (Real.log 3) :=
          add_le_add (fb_lintegral_logPos_circle_le w c hr) (fb_lintegral_logPos_circle_le w _ hr)
      _ ≤ 4 := by
          rw [← ENNReal.ofReal_add (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))]
          calc ENNReal.ofReal (Real.log 3 + Real.log 3) ≤ ENNReal.ofReal 4 :=
                ENNReal.ofReal_le_ofReal (by linarith)
            _ = 4 := by simp
  · rw [indicator_of_notMem hwc]
    have hfar : 2 * r ≤ ‖w - c‖ := by
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hwc; exact hwc
    have hz : ∀ᵐ v ∂foldedCircle w r, ENNReal.ofReal (Real.log (r / ‖v - c‖)) = 0 := by
      filter_upwards [fb_ae_fc w hr.le hw] with v hv
      have h1 : r ≤ ‖v - c‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub w v c
        rw [norm_sub_rev w v] at this
        linarith [hv.2.1]
      exact ENNReal.ofReal_eq_zero.2
        (Real.log_nonpos (by positivity) ((div_le_one (hr.trans_le h1)).2 h1))
    exact (lintegral_congr_ae hz).trans_le (by simp)

/-! ## Frostman bound for the logarithmic defect (layer cake) -/

theorem fb_lintegral_logPos_le_of_frostman {μ : Measure ℂ} {c : ℂ} {K α r : ℝ} (hα : 0 < α)
    (hK : 0 ≤ K) (hr : 0 < r)
    (hF : ∀ s : ℝ, 0 < s → s ≤ r → μ (Metric.ball c s) ≤ ENNReal.ofReal (K * s ^ α)) :
    ∫⁻ y, ENNReal.ofReal (Real.log (r / ‖y - c‖)) ∂μ ≤ ENNReal.ofReal (K * r ^ α / α) := by
  have hf : ∀ y : ℂ, ENNReal.ofReal (Real.log (r / ‖y - c‖)) =
      ENNReal.ofReal (max 0 (Real.log (r / ‖y - c‖))) := fun y => by
    rcases le_total 0 (Real.log (r / ‖y - c‖)) with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  simp_rw [hf]
  have hmeas : AEMeasurable (fun y : ℂ => max 0 (Real.log (r / ‖y - c‖))) μ :=
    (measurable_const.max
      (Real.measurable_log.comp (measurable_const.div (measurable_id.sub_const c).norm))).aemeasurable
  rw [lintegral_eq_lintegral_meas_lt μ (f := fun y => max 0 (Real.log (r / ‖y - c‖)))
    (ae_of_all _ fun y => le_max_left _ _) hmeas]
  have hball : ∀ t ∈ Ioi (0:ℝ), μ {y | t < max 0 (Real.log (r / ‖y - c‖))} ≤
      ENNReal.ofReal (K * r ^ α * Real.exp (-α * t)) := by
    intro t ht
    have ht : 0 < t := ht
    have hsub : {y | t < max 0 (Real.log (r / ‖y - c‖))} ⊆ Metric.ball c (r * Real.exp (-t)) := by
      intro y hy
      simp only [mem_ofPred_eq] at hy
      have hy' : t < Real.log (r / ‖y - c‖) := by
        rcases lt_max_iff.1 hy with h | h
        · exact absurd h (not_lt.2 ht.le)
        · exact h
      have hn : 0 < ‖y - c‖ := by
        rcases (norm_nonneg (y - c)).eq_or_lt with h | h
        · rw [← h, div_zero, Real.log_zero] at hy'; linarith
        · exact h
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 := (Real.lt_log_iff_exp_lt (div_pos hr hn)).1 hy'
      rw [lt_div_iff₀ hn] at h1
      rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos t)]
      linarith [mul_comm (Real.exp t) ‖y - c‖]
    have hs1 : r * Real.exp (-t) ≤ r :=
      mul_le_of_le_one_right hr.le (Real.exp_le_one_iff.2 (neg_nonpos.2 ht.le))
    calc μ {y | t < max 0 (Real.log (r / ‖y - c‖))}
        ≤ μ (Metric.ball c (r * Real.exp (-t))) := measure_mono hsub
      _ ≤ ENNReal.ofReal (K * (r * Real.exp (-t)) ^ α) := hF _ (by positivity) hs1
      _ = ENNReal.ofReal (K * r ^ α * Real.exp (-α * t)) := by
          congr 1
          rw [Real.mul_rpow hr.le (Real.exp_pos _).le, ← Real.exp_mul,
            show -t * α = -α * t by ring]
          ring
  calc ∫⁻ t in Ioi 0, μ {y | t < max 0 (Real.log (r / ‖y - c‖))}
      ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (K * r ^ α * Real.exp (-α * t)) :=
        setLIntegral_mono' measurableSet_Ioi hball
    _ = ENNReal.ofReal (∫ t in Ioi 0, K * r ^ α * Real.exp (-α * t)) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (exp_neg_integrableOn_Ioi 0 hα).const_mul _
        · exact ae_of_all _ fun t => by positivity
    _ = ENNReal.ofReal (K * r ^ α / α) := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero,
          neg_div_neg_eq]
        ring_nf

/-! ## Folded-circle averages of `greenH` -/

/-- Mean value on a circle in `Hbar`: `k(z,y) + log⁺(r/|y−z|) = G(z,y)`. -/
theorem fb_greenH_fc_high {z y : ℂ} {r : ℝ} (hr : 0 < r) (hrz : r ≤ z.im) (hy : y ∈ Hbar)
    (hyz : y ≠ z) :
    (∫⁻ v, ENNReal.ofReal (greenH v y) ∂foldedCircle z r) +
        ENNReal.ofReal (Real.log (r / ‖y - z‖)) = ENNReal.ofReal (greenH z y) := by
  have hz : z ∈ Hbar := (show (0:ℝ) ≤ z.im by linarith)
  have hH : ∀ᵐ v ∂circleUnif z r, v ∈ Hbar := by
    have := fb_ae_fc z hr.le hz
    rw [foldedCircle_eq_circleUnif hr.le hrz] at this
    exact this.mono fun v hv => hv.1
  rw [foldedCircle_eq_circleUnif hr.le hrz]
  have hint : Integrable (fun v => greenH v y) (circleUnif z r) :=
    (CircleMV.integrable_log_norm_sub_circleUnif z (conj y) r).sub (CircleMV.integrable_log_norm_sub_circleUnif z y r)
  have hnn : 0 ≤ᵐ[circleUnif z r] fun v => greenH v y := by
    have hne : ∀ᵐ v ∂circleUnif z r, v ≠ y := by
      rw [ae_iff]; simpa using fb_circleUnif_singleton z hr.ne' y
    filter_upwards [hH, hne] with v hv hvy
    exact greenH_nonneg hv hy hvy
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_greenH_circleUnif z y hr]
  have ht : 0 < ‖z - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hyz.symm)
  have hS : r ≤ ‖z - conj y‖ := by
    have h1 := Complex.abs_im_le_norm (z - conj y)
    simp only [Complex.sub_im, Complex.conj_im] at h1
    have hy' : 0 ≤ y.im := hy
    rw [abs_of_nonneg (by linarith)] at h1; linarith
  rw [max_eq_right hS, norm_sub_rev y z]
  unfold greenH
  rcases le_total r ‖z - y‖ with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos
      (Real.log_nonpos (by positivity) ((div_le_one ht).2 h)), add_zero]
  · rw [max_eq_left h, ← ENNReal.ofReal_add, Real.log_div hr.ne' ht.ne']
    · congr 1; ring
    · linarith [Real.log_le_log hr hS]
    · rw [Real.log_div hr.ne' ht.ne']; linarith [Real.log_le_log ht h]

/-- Pointwise bound near `ℝ`: if `0 ≤ Im v ≤ 2r`, then `G(v,x) ≤ 4 + log⁺(r/|v−x|)`. -/
theorem fb_greenH_le_low {v x : ℂ} {r : ℝ} (hr : 0 < r) (hv : v.im ≤ 2 * r) (hv0 : v ∈ Hbar)
    (hx : x ∈ Hbar) (hvx : v ≠ x) :
    ENNReal.ofReal (greenH v x) ≤ 4 + ENNReal.ofReal (Real.log (r / ‖v - x‖)) := by
  have hv0' : 0 ≤ v.im := hv0
  have ht : 0 < ‖v - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hvx)
  have hS0 : 0 < ‖v - conj x‖ := ht.trans_le (norm_sub_le_norm_sub_conj hv0 hx)
  have hS : ‖v - conj x‖ ≤ ‖v - x‖ + 4 * r := by
    rw [norm_sub_conj_comm v x]
    have hvv : ‖v - conj v‖ = 2 * v.im := by
      rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    calc ‖x - conj v‖ = ‖(x - v) + (v - conj v)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖x - v‖ + ‖v - conj v‖ := norm_add_le _ _
      _ ≤ ‖v - x‖ + 4 * r := by rw [norm_sub_rev x v, hvv]; linarith
  have hlog : greenH v x ≤ Real.log (‖v - x‖ + 4 * r) - Real.log ‖v - x‖ := by
    unfold greenH; linarith [Real.log_le_log hS0 hS]
  rcases le_total r ‖v - x‖ with h | h
  · have h4 : Real.log (‖v - x‖ + 4 * r) - Real.log ‖v - x‖ ≤ 4 := by
      rw [← Real.log_div (by positivity) ht.ne']
      have h1 := Real.log_le_sub_one_of_pos
        (show 0 < (‖v - x‖ + 4 * r) / ‖v - x‖ by positivity)
      have h2 : (‖v - x‖ + 4 * r) / ‖v - x‖ - 1 = 4 * r / ‖v - x‖ := by
        field_simp; ring
      have h3 : 4 * r / ‖v - x‖ ≤ 4 := by rw [div_le_iff₀ ht]; linarith
      linarith
    calc ENNReal.ofReal (greenH v x) ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal (by linarith)
      _ = 4 := by simp
      _ ≤ _ := le_self_add
  · have h5 : Real.log 5 ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 5); linarith
    have hl : Real.log (‖v - x‖ + 4 * r) ≤ Real.log 5 + Real.log r := by
      rw [← Real.log_mul (by norm_num) hr.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    have hq : 0 ≤ Real.log (r / ‖v - x‖) := Real.log_nonneg ((one_le_div ht).2 h)
    calc ENNReal.ofReal (greenH v x) ≤ ENNReal.ofReal (4 + Real.log (r / ‖v - x‖)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Real.log_div hr.ne' ht.ne']; linarith
      _ = 4 + ENNReal.ofReal (Real.log (r / ‖v - x‖)) := by
          rw [ENNReal.ofReal_add (by norm_num) hq]; simp

/-- FOLD-POT: folded-circle averages of `G(·,x)` at centres of height `< r` are `≤ 8`. -/
theorem fb_lintegral_greenH_fc_low {z x : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ Hbar)
    (hzr : z.im < r) (hx : x ∈ Hbar) :
    ∫⁻ v, ENNReal.ofReal (greenH v x) ∂foldedCircle z r ≤ 8 := by
  have hne : ∀ᵐ v ∂foldedCircle z r, v ≠ x := by
    rw [ae_iff]; simpa using fb_fc_singleton z hr.ne' x
  calc ∫⁻ v, ENNReal.ofReal (greenH v x) ∂foldedCircle z r
      ≤ ∫⁻ v, (4 + ENNReal.ofReal (Real.log (r / ‖v - x‖))) ∂foldedCircle z r := by
        refine lintegral_mono_ae ?_
        filter_upwards [fb_ae_fc z hr.le hz, hne] with v hv hvx
        exact fb_greenH_le_low hr (by linarith [hv.2.2]) hv.1 hx hvx
    _ = 4 + ∫⁻ v, ENNReal.ofReal (Real.log (r / ‖v - x‖)) ∂foldedCircle z r := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 4 + 4 := by
        gcongr
        exact (fb_lintegral_logPos_fc_le hz x hr).trans
          (Set.indicator_le_self' (fun _ _ => zero_le) z)
    _ = 8 := by norm_num

/-! ## Potentials -/

/-- The zero-boundary Green potential `x ↦ ∫⁻ G⁺(x,·) dη`. -/
def fbPot (η : Measure ℂ) (x : ℂ) : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (greenH x y) ∂η

/-- The folded-circle average at radius `r` of the potential. -/
def fbSPot (η : Measure ℂ) (r : ℝ) (z : ℂ) : ℝ≥0∞ := ∫⁻ v, fbPot η v ∂foldedCircle z r

theorem fb_measurable_pot (η : Measure ℂ) [SFinite η] : Measurable (fbPot η) :=
  (ENNReal.measurable_ofReal.comp measurable_greenH).lintegral_prod_right'

theorem fb_measurable_spot (η : Measure ℂ) [SFinite η] (r : ℝ) : Measurable (fbSPot η r) :=
  (fb_measurable_pot η).lintegral_kernel (κ := fbKernel r)

theorem fb_spot_le {η : Measure ℂ} {r : ℝ} {B : ℝ≥0∞} (hp : ∀ x ∈ Hbar, fbPot η x ≤ B)
    (z : ℂ) : fbSPot η r z ≤ B := by
  unfold fbSPot
  calc ∫⁻ v, fbPot η v ∂foldedCircle z r ≤ ∫⁻ _, B ∂foldedCircle z r :=
        lintegral_mono_ae ((ae_iff.2 (fb_fc_compl_Hbar z r) : ∀ᵐ v ∂foldedCircle z r, v ∈ Hbar).mono
          fun v hv => hp v hv)
    _ = B := by rw [lintegral_const, measure_univ, mul_one]

theorem fb_lintegral_bind (μ : Measure ℂ) (r : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ.bind fun w => foldedCircle w r) = ∫⁻ z, ∫⁻ v, f v ∂foldedCircle z r ∂μ :=
  Measure.lintegral_bind (fb_measurable_fc r).aemeasurable hf.aemeasurable

theorem fb_bind_apply (μ : Measure ℂ) (r : ℝ) {s : Set ℂ} (hs : MeasurableSet s) :
    (μ.bind fun w => foldedCircle w r) s = ∫⁻ w, foldedCircle w r s ∂μ :=
  Measure.bind_apply hs (fb_measurable_fc r).aemeasurable

/-- A bounded Green potential excludes atoms. -/
theorem fb_measure_singleton {μ : Measure ℂ} [IsFiniteMeasure μ] {U : ℝ≥0}
    (hH : μ {z | z.im ≤ 0} = 0) (hU : ∀ x ∈ H, fbPot μ x ≤ U) (y : ℂ) : μ {y} = 0 := by
  rcases le_or_gt y.im 0 with hy | hy
  · exact measure_mono_null (Set.singleton_subset_iff.2 hy) hH
  by_contra hne
  set c := (μ {y}).toReal with hcdef
  have hc : 0 < c := ENNReal.toReal_pos hne (measure_ne_top _ _)
  set t := y.im * Real.exp (-(((U : ℝ) + 1) / c)) with htdef
  have ht : 0 < t := by positivity
  have hx : y + t * Complex.I ∈ H := by
    show 0 < (y + t * Complex.I).im
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    linarith
  have hG : ((U : ℝ) + 1) / c ≤ greenH (y + t * Complex.I) y := by
    unfold greenH
    have e1 : ‖y + ↑t * Complex.I - conj y‖ = 2 * y.im + t := by
      have : y + ↑t * Complex.I - conj y = ((2 * y.im + t : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp <;> ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have e2 : ‖y + ↑t * Complex.I - y‖ = t := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht]
    rw [e1, e2]
    have hlt : Real.log t = Real.log y.im - ((U : ℝ) + 1) / c := by
      rw [htdef, Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    have := Real.log_le_log hy (by linarith : y.im ≤ 2 * y.im + t)
    linarith
  have key : μ {y} * ENNReal.ofReal (greenH (y + t * Complex.I) y) ≤ U := by
    calc μ {y} * ENNReal.ofReal (greenH (y + t * Complex.I) y)
        = ∫⁻ w, ({y} : Set ℂ).indicator
            (fun _ => ENNReal.ofReal (greenH (y + t * Complex.I) y)) w ∂μ := by
          rw [lintegral_indicator_const (measurableSet_singleton y), mul_comm]
      _ ≤ ∫⁻ w, ENNReal.ofReal (greenH (y + t * Complex.I) w) ∂μ := by
          refine lintegral_mono fun w => ?_
          by_cases hw : w = y
          · rw [hw, indicator_of_mem (mem_singleton y)]
          · rw [indicator_of_notMem (show w ∉ ({y} : Set ℂ) from hw)]; exact zero_le
      _ ≤ U := hU _ hx
  have hle : ENNReal.ofReal ((U : ℝ) + 1) ≤ U := by
    refine le_trans ?_ key
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {y}),
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_left hG hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  linarith

theorem fb_pot_le {μ : Measure ℂ} {U : ℝ≥0} (hU : ∀ x ∈ H, fbPot μ x ≤ U) {x : ℂ}
    (hx : x ∈ Hbar) : fbPot μ x ≤ U := by
  rcases (show (0:ℝ) ≤ x.im from hx).lt_or_eq with h | h
  · exact hU x h
  · simp [fbPot, fb_greenH_of_im_eq_zero h.symm]

/-- The smoothed potential is bounded: `P_ν ≤ U + 8 μ(ℂ)` on `Hbar`. -/
theorem fb_pot_bind_le {μ : Measure ℂ} [IsFiniteMeasure μ] {U : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (hH : μ {z | z.im ≤ 0} = 0) (hU : ∀ x ∈ H, fbPot μ x ≤ U) {x : ℂ} (hx : x ∈ Hbar) :
    fbPot (μ.bind fun w => foldedCircle w r) x ≤ U + 8 * μ univ := by
  unfold fbPot
  rw [fb_lintegral_bind μ r (f := fun y => ENNReal.ofReal (greenH x y))
    (ENNReal.measurable_ofReal.comp (measurable_greenH.comp (measurable_const.prodMk measurable_id)))]
  have hae : ∀ᵐ z ∂μ, z ∈ Hbar ∧ z ≠ x := by
    have h1 : ∀ᵐ z ∂μ, z ∈ Hbar := by
      rw [ae_iff]; exact measure_mono_null (fun z hz => (not_le.mp (show ¬ (0:ℝ) ≤ z.im from hz)).le) hH
    have h2 : ∀ᵐ z ∂μ, z ≠ x := by
      rw [ae_iff]; simpa using fb_measure_singleton hH hU x
    filter_upwards [h1, h2] with z h1 h2 using ⟨h1, h2⟩
  calc ∫⁻ z, ∫⁻ v, ENNReal.ofReal (greenH x v) ∂foldedCircle z r ∂μ
      ≤ ∫⁻ z, (ENNReal.ofReal (greenH x z) + 8) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with z hz
        simp_rw [greenH_symm x]
        rcases le_or_gt r z.im with hrz | hrz
        · rw [← fb_greenH_fc_high hr hrz hx hz.2.symm]
          exact le_self_add.trans le_self_add
        · exact (fb_lintegral_greenH_fc_low hr hz.1 hrz hx).trans le_add_self
    _ = fbPot μ x + 8 * μ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]; rfl
    _ ≤ U + 8 * μ univ := by gcongr; exact fb_pot_le hU hx

/-- For `Im z ≥ r`: `P_η(z) = SP_η(z) + ∫⁻ log⁺(r/|y−z|) dη(y)`. -/
theorem fb_pot_eq_spot_add {η : Measure ℂ} [SFinite η] (hηH : η Hbarᶜ = 0) {z : ℂ}
    (hzat : η {z} = 0) {r : ℝ} (hr : 0 < r) (hrz : r ≤ z.im) :
    fbPot η z = fbSPot η r z + ∫⁻ y, ENNReal.ofReal (Real.log (r / ‖y - z‖)) ∂η := by
  have hswap : fbSPot η r z = ∫⁻ y, ∫⁻ v, ENNReal.ofReal (greenH v y) ∂foldedCircle z r ∂η := by
    unfold fbSPot fbPot
    exact lintegral_lintegral_swap (ENNReal.measurable_ofReal.comp measurable_greenH).aemeasurable
  rw [hswap, ← lintegral_add_right _ (fb_measurable_logPos r z)]
  unfold fbPot
  refine lintegral_congr_ae ?_
  have h1 : ∀ᵐ y ∂η, y ∈ Hbar := ae_iff.2 hηH
  have h2 : ∀ᵐ y ∂η, y ≠ z := by rw [ae_iff]; simpa using hzat
  filter_upwards [h1, h2] with y hy hyz
  exact (fb_greenH_fc_high hr hrz hy hyz).symm

/-- `kernelCov greenH` as the real part of an `ℝ≥0∞` double integral. -/
theorem fb_kernelCov_eq {η₁ η₂ : Measure ℂ} [IsFiniteMeasure η₁] [IsFiniteMeasure η₂]
    (h1 : η₁ Hbarᶜ = 0) (h2 : η₂ Hbarᶜ = 0) (hat : ∀ x, η₂ {x} = 0) {B : ℝ≥0∞} (hB : B < ∞)
    (hpot : ∀ x ∈ Hbar, fbPot η₂ x ≤ B) :
    kernelCov greenH η₁ η₂ = (∫⁻ x, fbPot η₂ x ∂η₁).toReal := by
  unfold kernelCov
  have hae1 : ∀ᵐ x ∂η₁, x ∈ Hbar := ae_iff.2 h1
  have hinner : ∀ᵐ x ∂η₁, ∫ y, greenH x y ∂η₂ = (fbPot η₂ x).toReal := by
    filter_upwards [hae1] with x hx
    refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · have hae2 : ∀ᵐ y ∂η₂, y ∈ Hbar := ae_iff.2 h2
      have hne : ∀ᵐ y ∂η₂, y ≠ x := by rw [ae_iff]; simpa using hat x
      filter_upwards [hae2, hne] with y hy hyx
      exact greenH_nonneg hx hy hyx.symm
    · exact (measurable_greenH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [integral_congr_ae hinner]
  exact integral_toReal (fb_measurable_pot η₂).aemeasurable
    (hae1.mono fun x hx => (hpot x hx).trans_lt hB)

theorem fb_integrable_toReal {μ : Measure ℂ} [IsFiniteMeasure μ] {f : ℂ → ℝ≥0∞}
    (hf : Measurable f) {B : ℝ≥0∞} (hB : B < ∞) (hfB : ∀ᵐ z ∂μ, f z ≤ B) :
    Integrable (fun z => (f z).toReal) μ :=
  Integrable.of_bound hf.ennreal_toReal.aestronglyMeasurable B.toReal (hfB.mono fun z hz => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hB.ne hz)

theorem fb_lintegral_toReal {μ : Measure ℂ} {f : ℂ → ℝ≥0∞} (hf : Measurable f) {B : ℝ≥0∞}
    (hB : B < ∞) (hfB : ∀ᵐ z ∂μ, f z ≤ B) :
    (∫⁻ z, f z ∂μ).toReal = ∫ z, (f z).toReal ∂μ :=
  (integral_toReal hf.aemeasurable (hfB.mono fun _ hz => hz.trans_lt hB)).symm

/-! ## RG-1: the energy estimate -/

/-- **RG-1 (FOLD-BOUND energy estimate).** Let `μ` be a finite measure carried by `ℍ`, with
Green potential bounded by `U` on `ℍ` and a Frostman bound `μ(B(x,s)) ≤ K s^α` for
`Im x ≥ h`, `s ≤ h/2`. For `0 < r`, `4r ≤ h`, the folded-circle smoothing
`ν = μ.bind (foldedCircle · r)` satisfies
`|𝓔_G(ν − μ)| ≤ (2U + 8μ(ℂ)) μ{Im < 2h} + (1/α + 4·2^α) K r^α μ(ℂ)`. -/
theorem abs_energy_foldSmooth_le {μ : Measure ℂ} [IsFiniteMeasure μ] {U : ℝ≥0} {K α h r : ℝ}
    (hH : μ {z | z.im ≤ 0} = 0)
    (hU : ∀ x ∈ H, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂μ ≤ U)
    (hK : 0 ≤ K) (hα : 0 < α) (hr : 0 < r) (hrh : 4 * r ≤ h)
    (hF : ∀ x : ℂ, h ≤ x.im → ∀ s : ℝ, 0 < s → s ≤ h / 2 →
      μ (Metric.ball x s) ≤ ENNReal.ofReal (K * s ^ α)) :
    |kernelCov2 greenH (μ.bind fun w => foldedCircle w r, μ)
        (μ.bind fun w => foldedCircle w r, μ)| ≤
      (2 * (U : ℝ) + 8 * (μ univ).toReal) * (μ {z | z.im < 2 * h}).toReal +
        (1 / α + 4 * 2 ^ α) * K * r ^ α * (μ univ).toReal := by
  have hU' : ∀ x ∈ H, fbPot μ x ≤ U := hU
  obtain ⟨ν, hν⟩ : ∃ ν, ν = μ.bind fun w => foldedCircle w r := ⟨_, rfl⟩
  rw [← hν]
  have hνuniv : ν univ = μ univ := by
    rw [hν, fb_bind_apply μ r MeasurableSet.univ]; simp
  have : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_lt_top _ _⟩
  have hμH : μ Hbarᶜ = 0 := measure_mono_null (fun z hz => (not_le.mp (show ¬ (0:ℝ) ≤ z.im from hz)).le) hH
  have hνH : ν Hbarᶜ = 0 := by
    rw [hν, fb_bind_apply μ r isClosed_Hbar.measurableSet.compl]; simp [fb_fc_compl_Hbar]
  have hμat : ∀ x, μ {x} = 0 := fb_measure_singleton hH hU'
  have hνat : ∀ x, ν {x} = 0 := fun x => by
    rw [hν, fb_bind_apply μ r (measurableSet_singleton x)]; simp [fb_fc_singleton _ hr.ne']
  set m := (μ univ).toReal with hmdef
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set Bν : ℝ := (U : ℝ) + 8 * m with hBνdef
  have hBνe : (U : ℝ≥0∞) + 8 * μ univ = ENNReal.ofReal Bν := by
    rw [hBνdef, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_mul (by norm_num), hmdef, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    norm_num
  have hpμ : ∀ x ∈ Hbar, fbPot μ x ≤ ENNReal.ofReal (U : ℝ) := fun x hx => by
    rw [ENNReal.ofReal_coe_nnreal]; exact fb_pot_le hU' hx
  have hpν : ∀ x ∈ Hbar, fbPot ν x ≤ ENNReal.ofReal Bν := fun x hx => by
    rw [← hBνe, hν]; exact fb_pot_bind_le hr hH hU' hx
  have hsμ : ∀ z, fbSPot μ r z ≤ ENNReal.ofReal (U : ℝ) := fb_spot_le hpμ
  have hsν : ∀ z, fbSPot ν r z ≤ ENNReal.ofReal Bν := fb_spot_le hpν
  have haeH : ∀ᵐ z ∂μ, z ∈ Hbar := ae_iff.2 hμH
  have hb : ∀ η : Measure ℂ, [SFinite η] → ∫⁻ x, fbPot η x ∂ν = ∫⁻ z, fbSPot η r z ∂μ :=
    fun η _ => by rw [hν]; exact fb_lintegral_bind μ r (fb_measurable_pot η)
  have k1 : kernelCov greenH ν ν = ∫ z, (fbSPot ν r z).toReal ∂μ := by
    rw [fb_kernelCov_eq hνH hνH hνat ENNReal.ofReal_lt_top hpν, hb ν]
    exact fb_lintegral_toReal (fb_measurable_spot _ r) ENNReal.ofReal_lt_top (ae_of_all _ hsν)
  have k2 : kernelCov greenH ν μ = ∫ z, (fbSPot μ r z).toReal ∂μ := by
    rw [fb_kernelCov_eq hνH hμH hμat ENNReal.ofReal_lt_top hpμ, hb μ]
    exact fb_lintegral_toReal (fb_measurable_spot _ r) ENNReal.ofReal_lt_top (ae_of_all _ hsμ)
  have k3 : kernelCov greenH μ ν = ∫ z, (fbPot ν z).toReal ∂μ := by
    rw [fb_kernelCov_eq hμH hνH hνat ENNReal.ofReal_lt_top hpν]
    exact fb_lintegral_toReal (fb_measurable_pot _) ENNReal.ofReal_lt_top (haeH.mono hpν)
  have k4 : kernelCov greenH μ μ = ∫ z, (fbPot μ z).toReal ∂μ := by
    rw [fb_kernelCov_eq hμH hμH hμat ENNReal.ofReal_lt_top hpμ]
    exact fb_lintegral_toReal (fb_measurable_pot _) ENNReal.ofReal_lt_top (haeH.mono hpμ)
  have i1 := fb_integrable_toReal (fb_measurable_spot ν r) ENNReal.ofReal_lt_top
    (ae_of_all μ hsν)
  have i2 := fb_integrable_toReal (fb_measurable_spot μ r) ENNReal.ofReal_lt_top
    (ae_of_all μ hsμ)
  have i3 := fb_integrable_toReal (fb_measurable_pot ν) ENNReal.ofReal_lt_top (haeH.mono hpν)
  have i4 := fb_integrable_toReal (fb_measurable_pot μ) ENNReal.ofReal_lt_top (haeH.mono hpμ)
  have hE : kernelCov2 greenH (ν, μ) (ν, μ) = ∫ z, ((fbSPot ν r z).toReal - (fbSPot μ r z).toReal
      - (fbPot ν z).toReal + (fbPot μ z).toReal) ∂μ := by
    unfold kernelCov2
    simp only
    rw [k1, k2, k3, k4, integral_add (f := fun z => (fbSPot ν r z).toReal - (fbSPot μ r z).toReal
        - (fbPot ν z).toReal) ((i1.sub i2).sub i3) i4,
      integral_sub (f := fun z => (fbSPot ν r z).toReal - (fbSPot μ r z).toReal) (i1.sub i2) i3,
      integral_sub i1 i2]
  set C := (1 / α + 4 * 2 ^ α) * K * r ^ α with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hmeasA : MeasurableSet {z : ℂ | z.im < 2 * h} :=
    measurableSet_lt Complex.measurable_im measurable_const
  have hbound : ∀ᵐ z ∂μ, ‖(fbSPot ν r z).toReal - (fbSPot μ r z).toReal - (fbPot ν z).toReal
      + (fbPot μ z).toReal‖ ≤
      {z : ℂ | z.im < 2 * h}.indicator (fun _ => 2 * (U : ℝ) + 8 * m) z + C := by
    filter_upwards [haeH] with z hz
    have a1 := ENNReal.toReal_le_of_le_ofReal (by positivity) (hsν z)
    have a2 := ENNReal.toReal_le_of_le_ofReal (NNReal.coe_nonneg U) (hsμ z)
    have a3 := ENNReal.toReal_le_of_le_ofReal (by positivity) (hpν z hz)
    have a4 := ENNReal.toReal_le_of_le_ofReal (NNReal.coe_nonneg U) (hpμ z hz)
    have b1 : 0 ≤ (fbSPot ν r z).toReal := ENNReal.toReal_nonneg
    have b2 : 0 ≤ (fbSPot μ r z).toReal := ENNReal.toReal_nonneg
    have b3 : 0 ≤ (fbPot ν z).toReal := ENNReal.toReal_nonneg
    have b4 : 0 ≤ (fbPot μ z).toReal := ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs]
    by_cases hlow : z.im < 2 * h
    · rw [indicator_of_mem (show z ∈ {z : ℂ | z.im < 2 * h} from hlow), abs_le]
      constructor <;> linarith
    · rw [indicator_of_notMem (show z ∉ {z : ℂ | z.im < 2 * h} from hlow), zero_add]
      have hzh : 2 * h ≤ z.im := not_lt.mp hlow
      have hrz : r ≤ z.im := by linarith
      have e1 := fb_pot_eq_spot_add hνH (hνat z) hr hrz
      have e2 := fb_pot_eq_spot_add hμH (hμat z) hr hrz
      set Lν := ∫⁻ y, ENNReal.ofReal (Real.log (r / ‖y - z‖)) ∂ν with hLν
      set Lμ := ∫⁻ y, ENNReal.ofReal (Real.log (r / ‖y - z‖)) ∂μ with hLμ
      have hLν_le : Lν ≤ ENNReal.ofReal Bν :=
        calc Lν ≤ fbSPot ν r z + Lν := le_add_self
          _ = fbPot ν z := e1.symm
          _ ≤ _ := hpν z hz
      have hLμ_le : Lμ ≤ ENNReal.ofReal (U : ℝ) :=
        calc Lμ ≤ fbSPot μ r z + Lμ := le_add_self
          _ = fbPot μ z := e2.symm
          _ ≤ _ := hpμ z hz
      rw [e1, e2, ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsν z))
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLν_le),
        ENNReal.toReal_add (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hsμ z))
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLμ_le)]
      have hFz : ∀ s : ℝ, 0 < s → s ≤ r → μ (Metric.ball z s) ≤ ENNReal.ofReal (K * s ^ α) :=
        fun s hs hsr => hF z (by linarith) s hs (by linarith)
      have hLμb : Lμ.toReal ≤ K * r ^ α / α :=
        ENNReal.toReal_le_of_le_ofReal (by positivity)
          (fb_lintegral_logPos_le_of_frostman hα hK hr hFz)
      have hLνb : Lν.toReal ≤ 4 * (K * (2 * r) ^ α) := by
        refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
        calc Lν = ∫⁻ w, ∫⁻ v, ENNReal.ofReal (Real.log (r / ‖v - z‖)) ∂foldedCircle w r ∂μ := by
              rw [hLν, hν]; exact fb_lintegral_bind μ r (fb_measurable_logPos r z)
          _ ≤ ∫⁻ w, (Metric.ball z (2 * r)).indicator (fun _ => (4 : ℝ≥0∞)) w ∂μ :=
              lintegral_mono_ae (haeH.mono fun w hw => fb_lintegral_logPos_fc_le hw z hr)
          _ = 4 * μ (Metric.ball z (2 * r)) := lintegral_indicator_const measurableSet_ball 4
          _ ≤ 4 * ENNReal.ofReal (K * (2 * r) ^ α) := by
              gcongr
              exact hF z (by linarith) _ (by positivity) (by linarith)
          _ = ENNReal.ofReal (4 * (K * (2 * r) ^ α)) := by
              rw [ENNReal.ofReal_mul (p := 4) (by norm_num)]; congr 1; simp
      have h2r : (2 * r) ^ α = 2 ^ α * r ^ α := Real.mul_rpow (by norm_num) hr.le
      have hC : C = K * r ^ α / α + 4 * (K * (2 * r) ^ α) := by
        rw [h2r, hCdef]; field_simp
      have c1 : 0 ≤ Lμ.toReal := ENNReal.toReal_nonneg
      have c2 : 0 ≤ Lν.toReal := ENNReal.toReal_nonneg
      rw [abs_le, hC]
      constructor <;> linarith
  have hg : Integrable (fun z => {z : ℂ | z.im < 2 * h}.indicator
      (fun _ => 2 * (U : ℝ) + 8 * m) z + C) μ :=
    ((integrable_const _).indicator hmeasA).add (integrable_const _)
  calc |kernelCov2 greenH (ν, μ) (ν, μ)|
      = ‖∫ z, ((fbSPot ν r z).toReal - (fbSPot μ r z).toReal
          - (fbPot ν z).toReal + (fbPot μ z).toReal) ∂μ‖ := by rw [hE, Real.norm_eq_abs]
    _ ≤ ∫ z, ({z : ℂ | z.im < 2 * h}.indicator (fun _ => 2 * (U : ℝ) + 8 * m) z + C) ∂μ :=
        norm_integral_le_of_norm_le hg hbound
    _ = (2 * (U : ℝ) + 8 * m) * (μ {z | z.im < 2 * h}).toReal + C * m := by
        rw [integral_add ((integrable_const _).indicator hmeasA) (integrable_const _),
          integral_indicator_const _ hmeasA, integral_const, smul_eq_mul, smul_eq_mul,
          measureReal_def, measureReal_def]
        ring

/-- RG-1 in the blueprint's form: a Frostman bound `μ(B(x,s)) ≤ M h'^{-p} s^α` for every height
`h' > 0` (centres with `Im x ≥ h'`, radii `s ≤ h'/2`), and `h ≥ 4r`. -/
theorem abs_energy_foldSmooth_le_blueprint {μ : Measure ℂ} [IsFiniteMeasure μ] {U : ℝ≥0}
    {M p α h r : ℝ} (hH : μ {z | z.im ≤ 0} = 0)
    (hU : ∀ x ∈ H, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂μ ≤ U)
    (hM : 0 ≤ M) (hα : 0 < α) (hr : 0 < r) (hrh : 4 * r ≤ h)
    (hF : ∀ h' : ℝ, 0 < h' → ∀ x : ℂ, h' ≤ x.im → ∀ s : ℝ, 0 < s → s ≤ h' / 2 →
      μ (Metric.ball x s) ≤ ENNReal.ofReal (M * h' ^ (-p) * s ^ α)) :
    |kernelCov2 greenH (μ.bind fun w => foldedCircle w r, μ)
        (μ.bind fun w => foldedCircle w r, μ)| ≤
      (2 * (U : ℝ) + 8 * (μ univ).toReal) * (μ {z | z.im < 2 * h}).toReal +
        (1 / α + 4 * 2 ^ α) * (M * h ^ (-p)) * r ^ α * (μ univ).toReal :=
  abs_energy_foldSmooth_le hH hU (mul_nonneg hM (Real.rpow_nonneg (by linarith) _)) hα hr hrh
    (hF h (by linarith))

/-! ## RG-4: linear splitting -/

/-- `x` is regularizable at `ν`: all scale-`k` averages are `ν`-integrable and their integrals
converge (so `evalReg x ν` is a genuine limit). -/
def RegConv (x : FieldSample) (ν : Measure ℂ) : Prop :=
  (∀ k, Integrable (avgReg x k) ν) ∧ ∃ ℓ, Tendsto (fun k => ∫ w, avgReg x k w ∂ν) atTop (𝓝 ℓ)

theorem RegConv.tendsto {x : FieldSample} {ν : Measure ℂ} (h : RegConv x ν) :
    Tendsto (fun k => ∫ w, avgReg x k w ∂ν) atTop (𝓝 (evalReg x ν)) := by
  obtain ⟨ℓ, hℓ⟩ := h.2
  have : evalReg x ν = ℓ := hℓ.limUnder_eq
  rw [this]; exact hℓ

/-- Linearity of `evalReg` in the measure (addition). -/
theorem RegConv.add_measure {x : FieldSample} {μ ν : Measure ℂ} (hμ : RegConv x μ)
    (hν : RegConv x ν) :
    RegConv x (μ + ν) ∧ evalReg x (μ + ν) = evalReg x μ + evalReg x ν := by
  have heq : ∀ k, ∫ w, avgReg x k w ∂(μ + ν) = ∫ w, avgReg x k w ∂μ + ∫ w, avgReg x k w ∂ν :=
    fun k => integral_add_measure (hμ.1 k) (hν.1 k)
  have ht : Tendsto (fun k => ∫ w, avgReg x k w ∂(μ + ν)) atTop
      (𝓝 (evalReg x μ + evalReg x ν)) := by
    simp_rw [heq]; exact hμ.tendsto.add hν.tendsto
  exact ⟨⟨fun k => (hμ.1 k).add_measure (hν.1 k), _, ht⟩, ht.limUnder_eq⟩

/-- Linearity of `evalReg` in the measure (scaling). -/
theorem RegConv.smul_measure {x : FieldSample} {μ : Measure ℂ} (hμ : RegConv x μ) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : RegConv x (c • μ) ∧ evalReg x (c • μ) = c.toReal * evalReg x μ := by
  have heq : ∀ k, ∫ w, avgReg x k w ∂(c • μ) = c.toReal * ∫ w, avgReg x k w ∂μ :=
    fun k => by rw [integral_smul_measure, smul_eq_mul]
  have ht : Tendsto (fun k => ∫ w, avgReg x k w ∂(c • μ)) atTop
      (𝓝 (c.toReal * evalReg x μ)) := by
    simp_rw [heq]; exact hμ.tendsto.const_mul _
  exact ⟨⟨fun k => (hμ.1 k).smul_measure hc, _, ht⟩, ht.limUnder_eq⟩

/-- The measure `ρ⁺ dz` of `pairTest`. -/
abbrev posMeas (ρ : ℂ → ℝ) : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (ρ z)

/-- The raw pairing `pairRaw x ρ = x (ρ⁺ dz) - x (ρ⁻ dz)` (`Field/Law.lean`), written out: the
lemmas below are stated for this expression, which is `pairRaw x ρ` by definition. -/
abbrev rawPair (x : FieldSample) (ρ : ℂ → ℝ) : ℝ := x (posMeas ρ) - x (posMeas (-ρ))

end FoldBound

end QuantumZipper
