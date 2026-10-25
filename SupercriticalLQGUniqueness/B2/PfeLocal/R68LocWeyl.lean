import SupercriticalLQGUniqueness.B2.PfeLocal.L6Obs
import SupercriticalLQGUniqueness.B2.PfeAxioms.S2Locality
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Regularity
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import LQGMetric.Papers.DFGPS.L2_12Moll

 












set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 
theorem r68_compactPathInf_weyl_le_local (Φ D E : LSCMetric) {ξ : ℝ} (hξ : 0 < ξ)
    (f g : C(ℂ, ℝ)) (hforget : Continuous (PfeWeyl.euclidForget Φ)) (hlen : Φ.IsLengthSpace)
    (hD : ∀ p, D p = weylScale ξ f Φ p) (hE : ∀ p, E p = weylScale ξ g Φ p)
    (m M : ℝ) (hfb : ∀ z, m ≤ f z ∧ f z ≤ M) {N : Set ℂ} {c : ℝ}
    (hfg : ∀ x ∈ N, ξ * f x ≤ ξ * g x + c) {K A B : Set ℂ} (hKN : K ⊆ N) :
    compactPathInf D K A B ≤ ENNReal.ofReal (Real.exp c) * compactPathInf E K A B := by
  set κ : ℝ≥0∞ := ENNReal.ofReal (Real.exp c) with hκ
  have hκ0 : κ ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos c)).ne'
  have hκt : κ ≠ ∞ := ENNReal.ofReal_ne_top
  set g' : C(ℂ, ℝ) := g + ContinuousMap.const ℂ (c / ξ) with hg'
  let E'' : LSCMetric := B2.LscTop.smulMetric ⟨Real.exp c, Real.exp_pos c⟩ E
  have hE''v : ∀ x y : ℂ, E'' (x, y) = κ * E (x, y) := fun x y => rfl
  have hE'' : ∀ p, E'' p = weylScale ξ g' Φ p := by
    intro p
    rw [hg', Uniqueness.Objects.Producer.weylScale_add_const, ← hE p,
      show ξ * (c / ξ) = c by field_simp]
    rfl
  by_contra hnot
  have hlt : κ * compactPathInf E K A B < compactPathInf D K A B := lt_of_not_ge hnot
  have hlt' : compactPathInf E K A B < compactPathInf D K A B / κ :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hκ0) (Or.inl hκt)).2 (by rw [mul_comm]; exact hlt)
  unfold compactPathInf at hlt'
  obtain ⟨P, s, t, hP, htr, hAs, hBt, hcost⟩ := (by simpa only [iInf_lt_iff] using hlt')
  have hPΦ : Φ.IsCurve P s t :=
    Uniqueness.Toolkit.WeylShift.curve_back_all_continuous Φ E ξ hξ.le g hforget hE hP
  have hPD : D.IsCurve P s t :=
    PfeAxioms.isCurve_weyl_of_bounded Φ D ξ hξ.le f hforget hD m M hfb hlen hPΦ
  have hlenD : D.len P s t = PfeAxioms.weylWL Φ ξ f P s t :=
    PfeAxioms.len_eq_weylWL_of_eqOn Φ D ξ f f hforget hD hPΦ (fun _ _ => rfl)
  have hlenE'' : E''.len P s t = PfeAxioms.weylWL Φ ξ g' P s t :=
    PfeAxioms.len_eq_weylWL_of_eqOn Φ E'' ξ g' g' hforget hE'' hPΦ (fun _ _ => rfl)
  have hscale : E''.len P s t = κ * E.len P s t :=
    Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale E E'' κ hE''v P s t
  have hmono : PfeAxioms.weylWL Φ ξ f P s t ≤ PfeAxioms.weylWL Φ ξ g' P s t := by
    unfold PfeAxioms.weylWL
    refine HigherDimLQGMetric.weightedLength_mono_weight fun u hu => ?_
    show Real.exp (ξ * f (P u)) ≤ Real.exp (ξ * g' (P u))
    refine Real.exp_le_exp.2 ?_
    have h1 := hfg (P u) (hKN (htr u hu))
    have h2 : ξ * g' (P u) = ξ * g (P u) + c := by
      simp only [hg', ContinuousMap.add_apply, ContinuousMap.const_apply]
      field_simp
    linarith
  have h1 : compactPathInf D K A B ≤ D.len P s t := l5_compactPathInf_le D P s t hPD htr hAs hBt
  have h2 : D.len P s t ≤ κ * E.len P s t := by
    rw [hlenD, ← hscale, hlenE'']; exact hmono
  have h3 : κ * E.len P s t < compactPathInf D K A B :=
    calc κ * E.len P s t < κ * (compactPathInf D K A B / κ) :=
          (ENNReal.mul_lt_mul_iff_right hκ0 hκt).2 hcost
      _ ≤ compactPathInf D K A B := ENNReal.mul_div_le
  exact (not_lt_of_ge (h1.trans h2)) h3

 
theorem r68_eventually_mollCont_close {εn : ℕ → ℝ} (hεp : ∀ n, 0 < εn n)
    (hε0 : Tendsto εn atTop (𝓝 0)) (F F' : C(ℂ, ℝ)) {M M' : ℝ} (hM : ∀ z, |F z| ≤ M)
    (hM' : ∀ z, |F' z| ≤ M') {R θ : ℝ} (hR : 0 < R) (hθ : 0 < θ)
    (hFF : ∀ z ∈ closedBall (0 : ℂ) R, |F z - F' z| ≤ θ) :
    ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) R,
      |LQGMetric.LFPP.mollCont (εn n) (hεp n).ne' F M hM z -
        LQGMetric.LFPP.mollCont (εn n) (hεp n).ne' F' M' hM' z| ≤ 2 * θ := by
  set H : C(ℂ, ℝ) := F - F' with hH
  have hHM : ∀ z, |H z| ≤ M + M' := fun z => by
    simp only [hH, ContinuousMap.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM z) (hM' z))
  have hsub : ∀ n z, LQGMetric.LFPP.mollCont (εn n) (hεp n).ne' F M hM z -
      LQGMetric.LFPP.mollCont (εn n) (hεp n).ne' F' M' hM' z =
        LQGMetric.heatMollify (εn n) (LQGMetric.ofCont H) z := by
    intro n z
    have hs : 0 < εn n ^ 2 / 2 := by have := hεp n; positivity
    show LQGMetric.heatMollify (εn n) (LQGMetric.ofCont F) z -
      LQGMetric.heatMollify (εn n) (LQGMetric.ofCont F') z = _
    rw [LQGMetric.heatMollify_ofCont F M hM _ (hεp n).ne' z,
      LQGMetric.heatMollify_ofCont F' M' hM' _ (hεp n).ne' z,
      LQGMetric.heatMollify_ofCont H (M + M') hHM _ (hεp n).ne' z, ← integral_sub]
    · congr 1; funext w; simp only [hH, ContinuousMap.sub_apply]; ring
    · exact (LQGMetric.integrable_heatKernel_mul_of_bdd F M hM _ hs z).congr
        (Eventually.of_forall fun w => mul_comm _ _)
    · exact (LQGMetric.integrable_heatKernel_mul_of_bdd F' M' hM' _ hs z).congr
        (Eventually.of_forall fun w => mul_comm _ _)
  have hconv := LQGMetric.DFGPS.tendstoUniformlyOn_heatMollify_seq (εn := εn)
    (fun n => (hεp n).ne') hε0 (fn := fun _ => H) (f := H) (fun _ => hHM) hHM
    (fun R' _ => Metric.tendstoUniformlyOn_iff.2 fun η hη =>
      Eventually.of_forall fun n x _ => by simpa using hη) hR
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv θ hθ] with n hn z hz
  rw [hsub n z]
  have h1 := hn z hz
  rw [Real.dist_eq] at h1
  have h2 : |H z| ≤ θ := by simpa only [hH, ContinuousMap.sub_apply] using hFF z hz
  calc |LQGMetric.heatMollify (εn n) (LQGMetric.ofCont H) z|
      ≤ |H z| + |H z - LQGMetric.heatMollify (εn n) (LQGMetric.ofCont H) z| := by
        have := abs_sub_abs_le_abs_sub (LQGMetric.heatMollify (εn n) (LQGMetric.ofCont H) z) (H z)
        rw [abs_sub_comm (LQGMetric.heatMollify _ _ z) (H z)] at this
        linarith
    _ ≤ θ + θ := add_le_add h2 h1.le
    _ = 2 * θ := by ring

end SupercriticalLQGUniqueness.B2.PfeLocal
