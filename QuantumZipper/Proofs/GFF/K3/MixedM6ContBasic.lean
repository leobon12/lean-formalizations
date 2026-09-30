import QuantumZipper.Proofs.GFF.K3.MixedM6Pre
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Joint continuity of the annulus features (GFF-K3 node M6, preparation)

For fixed inner radius `s > 0`, the annulus feature `annulusFeat D z s t ∈ L²` depends continuously
on `(z, t)` at every `t > s` (dominated convergence: the field is bounded by `2/s`, and off the
four circles `‖x − z₀‖, ‖x − z̄₀‖ ∈ {s, t₀}` (a null set) the indicator conditions are locally
constant). By Heine–Cantor this is uniform in `t` on a compact interval.

Own elementary argument (cost rule; standard dominated convergence in `L²`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- One term of the annulus field as a function of the centre and the outer radius. -/
def annTermP (s : ℝ) (x : ℂ) (p : ℂ × ℝ) : ℂ :=
  if s < ‖x - p.1‖ ∧ ‖x - p.1‖ < p.2 then -(x - p.1) / ((‖x - p.1‖ ^ 2 : ℝ) : ℂ) else 0

theorem annulusField_eq_annTermP (z : ℂ) (s t : ℝ) (x : ℂ) :
    annulusField z s t x = annTermP s x (z, t) + annTermP s x (conj z, t) := rfl

theorem tendsto_annTermP {s : ℝ} (hs : 0 < s) (x c0 : ℂ) {t0 : ℝ} (h1 : ‖x - c0‖ ≠ s)
    (h2 : ‖x - c0‖ ≠ t0) :
    Tendsto (annTermP s x) (𝓝 (c0, t0)) (𝓝 (annTermP s x (c0, t0))) := by
  have hn : Continuous fun p : ℂ × ℝ => ‖x - p.1‖ := by fun_prop
  unfold annTermP
  by_cases hc : s < ‖x - c0‖ ∧ ‖x - c0‖ < t0
  · rw [if_pos hc]
    have hev : ∀ᶠ p in 𝓝 (c0, t0), s < ‖x - p.1‖ ∧ ‖x - p.1‖ < p.2 :=
      ((isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_snd)).mem_nhds hc
    have hne : ((‖x - c0‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < ‖x - c0‖ := hs.trans hc.1
      exact_mod_cast (pow_pos this 2).ne'
    refine Tendsto.congr' (hev.mono fun p hp => (if_pos hp).symm) ?_
    have hcont : ContinuousAt (fun p : ℂ × ℝ => -(x - p.1) / ((‖x - p.1‖ ^ 2 : ℝ) : ℂ))
        (c0, t0) := by
      refine ContinuousAt.div (by fun_prop) ?_ hne
      exact (Complex.continuous_ofReal.comp
        (by fun_prop : Continuous fun p : ℂ × ℝ => ‖x - p.1‖ ^ 2)).continuousAt
    exact hcont
  · rw [if_neg hc]
    have hc' : ‖x - c0‖ < s ∨ t0 < ‖x - c0‖ := by
      rcases not_and_or.mp hc with h | h
      · exact Or.inl (lt_of_le_of_ne (not_lt.mp h) h1)
      · exact Or.inr (lt_of_le_of_ne (not_lt.mp h) (Ne.symm h2))
    have hev : ∀ᶠ p in 𝓝 (c0, t0), ‖x - p.1‖ < s ∨ p.2 < ‖x - p.1‖ :=
      ((isOpen_lt hn continuous_const).union (isOpen_lt continuous_snd hn)).mem_nhds hc'
    refine tendsto_const_nhds.congr' (hev.mono fun p hp => ?_)
    refine (if_neg ?_).symm
    rintro ⟨h3, h4⟩
    rcases hp with hp | hp <;> linarith

theorem tendsto_annulusField {s : ℝ} (hs : 0 < s) (x z0 : ℂ) {t0 : ℝ}
    (h1 : ‖x - z0‖ ≠ s) (h2 : ‖x - z0‖ ≠ t0) (h3 : ‖x - conj z0‖ ≠ s)
    (h4 : ‖x - conj z0‖ ≠ t0) :
    Tendsto (fun p : ℂ × ℝ => annulusField p.1 s p.2 x) (𝓝 (z0, t0))
      (𝓝 (annulusField z0 s t0 x)) := by
  simp only [annulusField_eq_annTermP]
  refine (tendsto_annTermP hs x z0 h1 h2).add ?_
  have hc : Continuous fun p : ℂ × ℝ => (conj p.1, p.2) := by fun_prop
  exact (tendsto_annTermP hs x (conj z0) h3 h4).comp (hc.tendsto' _ _ rfl)

theorem norm_annulusVal_le (z : ℂ) {s : ℝ} (hs : 0 < s) (t : ℝ) (p : ℂ × Fin 2) :
    ‖annulusVal z s t p‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (2 * s⁻¹) := by
  have hA : ‖annulusField z s t p.1‖ ≤ 2 * s⁻¹ := by
    rw [annulusField_eq, two_mul]
    exact (norm_add_le _ _).trans (add_le_add (norm_annulusTerm_le z hs _)
      (norm_annulusTerm_le _ hs _))
  unfold annulusVal
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans hA
  · exact (Complex.abs_im_le_norm _).trans hA

theorem annulusFeat_eq_toLp {D : Set ℂ} (hb : Bornology.IsBounded D) (z : ℂ) {s : ℝ} (hs : 0 < s)
    (t : ℝ) : annulusFeat D z s t = (memLp_annulusVal hb z hs (s' := t)).toLp _ := by
  unfold annulusFeat
  exact dif_pos _

theorem coeFn_annulusFeat {D : Set ℂ} (hb : Bornology.IsBounded D) (z : ℂ) {s : ℝ} (hs : 0 < s)
    (t : ℝ) : ⇑(annulusFeat D z s t) =ᵐ[gradMeasure D] annulusVal z s t := by
  rw [annulusFeat_eq_toLp hb z hs t]
  exact MemLp.coeFn_toLp _

/-- **Joint continuity of the annulus features** in `(centre, outer radius)`. -/
theorem continuousAt_annulusFeat {D : Set ℂ} (hb : Bornology.IsBounded D) {s : ℝ} (hs : 0 < s)
    (z0 : ℂ) (t0 : ℝ) :
    ContinuousAt (fun p : ℂ × ℝ => annulusFeat D p.1 s p.2) (z0, t0) := by
  have : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  set c0 : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * (2 * s⁻¹) with hc0
  unfold ContinuousAt
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hae' : ∀ p : ℂ × ℝ, eLpNorm (⇑(annulusFeat D p.1 s p.2) - ⇑(annulusFeat D z0 s t0)) 2
      (gradMeasure D) = eLpNorm (annulusVal p.1 s p.2 - annulusVal z0 s t0) 2 (gradMeasure D) :=
    fun p => eLpNorm_congr_ae ((coeFn_annulusFeat hb p.1 hs p.2).sub
      (coeFn_annulusFeat hb z0 hs t0))
  simp only [hae']
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (two_ne_zero) ENNReal.ofNat_ne_top]
  -- the null set of the four circles
  set N : Set ℂ := sphere z0 s ∪ sphere z0 t0 ∪ sphere (conj z0) s ∪ sphere (conj z0) t0
  have hN : volume N = 0 := by
    simp only [N, measure_union_null_iff, Measure.addHaar_sphere, and_self]
  have hNμ : gradMeasure D (N ×ˢ univ) = 0 := by
    rw [Measure.prod_prod]
    have : (volume.restrict D) N = 0 :=
      nonpos_iff_eq_zero.mp ((Measure.restrict_le_self N).trans hN.le)
    rw [this, zero_mul]
  have hae : ∀ᵐ a ∂(gradMeasure D), a.1 ∉ N := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hNμ] with a ha h
    exact ha ⟨h, trivial⟩
  have hlim : Tendsto (fun p : ℂ × ℝ => ∫⁻ a, ‖(annulusVal p.1 s p.2 - annulusVal z0 s t0) a‖ₑ ^
      (2 : ℝ≥0∞).toReal ∂(gradMeasure D)) (𝓝 (z0, t0)) (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _a, (0 : ℝ≥0∞) ∂(gradMeasure D) := by simp
    rw [h0]
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun _ => ENNReal.ofReal (2 * c0) ^ (2 : ℝ≥0∞).toReal) (Eventually.of_forall fun p => ?_)
      (Eventually.of_forall fun p => Eventually.of_forall fun a => ?_) ?_ ?_
    · exact (((measurable_annulusVal _ _ _).sub (measurable_annulusVal _ _ _)).enorm).pow_const _
    · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm_eq_enorm]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [Pi.sub_apply]
      refine (norm_sub_le _ _).trans ?_
      rw [two_mul]
      exact add_le_add (norm_annulusVal_le _ hs _ _) (norm_annulusVal_le _ hs _ _)
    · rw [lintegral_const]
      exact ENNReal.mul_ne_top (by finiteness) (measure_ne_top _ _)
    · filter_upwards [hae] with a ha
      obtain ⟨x, i⟩ := a
      simp only [N, mem_union, mem_sphere, dist_eq_norm, not_or] at ha
      have hA := tendsto_annulusField hs x z0 ha.1.1.1 ha.1.1.2 ha.1.2 ha.2
      have hT : Tendsto (fun p : ℂ × ℝ => annulusVal p.1 s p.2 (x, i)) (𝓝 (z0, t0))
          (𝓝 (annulusVal z0 s t0 (x, i))) := by
        simp only [annulusVal]
        split_ifs
        · exact ((Complex.continuous_re.tendsto _).comp hA).const_mul _
        · exact ((Complex.continuous_im.tendsto _).comp hA).const_mul _
      have := ((hT.sub_const (annulusVal z0 s t0 (x, i))).enorm).ennrpow_const (2 : ℝ≥0∞).toReal
      simpa [sub_self] using this
  have hc : ContinuousAt (fun y : ℝ≥0∞ => y ^ (1 / (2 : ℝ≥0∞).toReal)) 0 :=
    (ENNReal.continuous_rpow_const).continuousAt
  have := hc.tendsto.comp hlim
  simpa [Function.comp_def] using this

/-- **Uniformity in the outer radius.** -/
theorem exists_norm_annulusFeat_sub_lt {D : Set ℂ} (hb : Bornology.IsBounded D) {s a b : ℝ}
    (hs : 0 < s) (z0 : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z' : ℂ, ‖z' - z0‖ < δ → ∀ t ∈ Icc a b,
      ‖annulusFeat D z0 s t - annulusFeat D z' s t‖ < ε := by
  have hK : IsCompact (closedBall z0 1 ×ˢ Icc a b) := (isCompact_closedBall _ _).prod isCompact_Icc
  have hU := hK.uniformContinuousOn_of_continuous
    (fun p _ => (continuousAt_annulusFeat hb hs p.1 p.2).continuousWithinAt)
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.mp hU ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun z' hz' t ht => ?_⟩
  have h1 : (z0, t) ∈ closedBall z0 1 ×ˢ Icc a b := ⟨mem_closedBall_self zero_le_one, ht⟩
  have h2 : (z', t) ∈ closedBall z0 1 ×ˢ Icc a b :=
    ⟨by rw [mem_closedBall, dist_eq_norm]; exact (hz'.trans_le (min_le_right _ _)).le, ht⟩
  have hd : dist (z0, t) (z', t) < δ := by
    rw [Prod.dist_eq, dist_self, dist_comm, dist_eq_norm]
    exact max_lt (hz'.trans_le (min_le_left _ _)) hδ
  have := hδU _ h1 _ h2 hd
  rwa [dist_eq_norm] at this

end QuantumZipper.K3
