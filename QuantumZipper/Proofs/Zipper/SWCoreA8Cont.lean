import QuantumZipper.Proofs.Zipper.SWCoreA8Fib
import QuantumZipper.Proofs.Zipper.SWCoreA6AddAn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A8 (3): pathwise continuity in `(t, z)` and density of rational parameters

For a continuous driver `W` with `W 0 = 0` and a regular sample `x`:

* `a8_cont_phi`: `(t,z) ↦ ∫ g d(fc(z,r).map f_t⁻¹)` is continuous on `[0,T] × [A,B] × [C,D]`
  for `g` continuous on `Hbar` and `r ≤ C/2` (dominated convergence over the circle);
* `a8_cont_rnd`: `(t,z) ↦ evalReg x (fc(f_t⁻¹ z, r|(f_t⁻¹)'(z)|))` is continuous there;
* `a8_le_of_rat`: a continuous function bounded at the rational points of the box (rational
  `T`, `A, B, C, D`) is bounded on the box.

Own elementary arguments.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

/-- Rational approximation inside a rational interval. -/
theorem a8_ratSeq {a b : ℚ} (hab : (a : ℝ) ≤ b) {x : ℝ} (hx : x ∈ Icc (a : ℝ) b) :
    ∃ u : ℕ → ℚ, (∀ n, ((u n : ℚ) : ℝ) ∈ Icc (a : ℝ) b) ∧
      Tendsto (fun n => ((u n : ℚ) : ℝ)) atTop (𝓝 x) := by
  have hv : ∀ n : ℕ, ∃ v : ℚ, x < v ∧ (v : ℝ) < x + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
  choose v hv1 hv2 using hv
  refine ⟨fun n => max a (min (v n) b), fun n => ?_, ?_⟩
  · push_cast
    exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  · have hvt : Tendsto (fun n => (v n : ℝ)) atTop (𝓝 x) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun n => (hv1 n).le) (fun n => (hv2 n).le)
      simpa using (tendsto_const_nhds (x := x)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Continuous fun y : ℝ => max (a : ℝ) (min y b) := by fun_prop
    have h := (hc.tendsto x).comp hvt
    rw [min_eq_left hx.2, max_eq_right hx.1] at h
    refine h.congr fun n => ?_
    simp

theorem zQ_eq (z : ℚ × ℚ) : zQ z = ((z.1 : ℝ) : ℂ) + ((z.2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [zQ]

/-- **Density of the rational parameters.** -/
theorem a8_le_of_rat {Tq A B C D : ℚ} (hT : (0 : ℝ) ≤ Tq) (hAB : (A : ℝ) ≤ B)
    (hCD : (C : ℝ) ≤ D) {g : ℝ × ℂ → ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) Tq ×ˢ rectC (A : ℝ) B C D)) {ε : ℝ}
    (hD : ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) Tq → ∀ z : ℚ × ℚ, zQ z ∈ rectC (A : ℝ) B C D →
      g (q, zQ z) ≤ ε) :
    ∀ p ∈ Icc (0 : ℝ) Tq ×ˢ rectC (A : ℝ) B C D, g p ≤ ε := by
  rintro ⟨t, z⟩ ⟨ht, hz⟩
  obtain ⟨u, hu, hut⟩ := a8_ratSeq (a := 0) (b := Tq) (by simpa using hT)
    (x := t) (by simpa using ht)
  obtain ⟨v, hv, hvt⟩ := a8_ratSeq hAB hz.1
  obtain ⟨w, hw, hwt⟩ := a8_ratSeq hCD hz.2
  have hmem : ∀ n, zQ (v n, w n) ∈ rectC (A : ℝ) B C D := fun n => by
    refine ⟨?_, ?_⟩ <;> simp only [zQ]
    · exact hv n
    · exact hw n
  have hu' : ∀ n, ((u n : ℚ) : ℝ) ∈ Icc (0 : ℝ) Tq := fun n => by simpa using hu n
  have hzt : Tendsto (fun n => zQ (v n, w n)) atTop (𝓝 z) := by
    simp_rw [zQ_eq]
    have := (Complex.continuous_ofReal.tendsto _).comp hvt |>.add
      (((Complex.continuous_ofReal.tendsto _).comp hwt).mul_const Complex.I)
    rwa [Complex.re_add_im] at this
  have hs : Tendsto (fun n => (((u n : ℚ) : ℝ), zQ (v n, w n))) atTop
      (𝓝[Icc (0 : ℝ) Tq ×ˢ rectC (A : ℝ) B C D] (t, z)) :=
    tendsto_nhdsWithin_iff.2 ⟨hut.prodMk_nhds hzt, Eventually.of_forall fun n => ⟨hu' n, hmem n⟩⟩
  exact le_of_tendsto' ((hg (t, z) ⟨ht, hz⟩).tendsto.comp hs) fun n => hD _ (hu' n) _ (hmem n)

theorem a8_rect_H {A B C D : ℝ} (hC : 0 < C) : rectC A B C D ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le hC hz.2.1

theorem a8_circ_mem {A B C D : ℝ} {z : ℂ} (hz : z ∈ rectC A B C D) {r : ℝ} (hr : 0 ≤ r)
    (hrC : r ≤ C / 2) (θ : ℝ) :
    circleMap z r θ ∈ rectC (A - C / 2) (B + C / 2) (C / 2) (D + C / 2) := by
  have h := circleMap_sub_center z r θ
  have hn : ‖circleMap z r θ - z‖ = r := by rw [h, norm_circleMap_zero, abs_of_nonneg hr]
  have h1 := Complex.abs_re_le_norm (circleMap z r θ - z)
  have h2 := Complex.abs_im_le_norm (circleMap z r θ - z)
  rw [hn, Complex.sub_re, abs_le] at h1
  rw [hn, Complex.sub_im, abs_le] at h2
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hz
  exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

variable {W : ℝ → ℝ}

/-- **Joint continuity of pushed circle pairings.** -/
theorem a8_cont_phi (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} {A B C D : ℝ} (hC : 0 < C)
    {r : ℝ} (hr : 0 < r) (hrC : r ≤ C / 2) {g : ℂ → ℝ} (hg : ContinuousOn g Hbar)
    (hgm : Measurable g) :
    ContinuousOn (fun p : ℝ × ℂ => ∫ u, g u ∂((foldedCircle p.2 r).map (fwdMapInv W p.1)))
      (Icc (0 : ℝ) T ×ˢ rectC A B C D) := by
  set Kw := rectC (A - C / 2) (B + C / 2) (C / 2) (D + C / 2) with hKw
  have hC2 : (0 : ℝ) < C / 2 := by linarith
  have hKwH : Kw ⊆ H := a8_rect_H hC2
  have hImc := E6.isCompact_flowImage hW hW0 T (swA6_isCompact_rectC _ _ _ _) hKwH
  have hImH := E6.flowImage_subset_H hW hW0 T hKwH
  have hHHbar : H ⊆ Hbar := fun w hw => le_of_lt (show 0 < w.im from hw)
  obtain ⟨Cb, hCb⟩ := hImc.exists_bound_of_continuousOn (hg.mono (hImH.trans hHHbar))
  have hjoint := RegUnif.continuousOn_fwdMapInv_joint hW hW0 T
  have hmemI : ∀ p ∈ Icc (0 : ℝ) T ×ˢ rectC A B C D, ∀ θ,
      fwdMapInv W p.1 (circleMap p.2 r θ) ∈ E6.flowImage W T Kw := fun p hp θ =>
    ⟨(p.1, circleMap p.2 r θ), ⟨hp.1, a8_circ_mem hp.2 hr.le hrC θ⟩, rfl⟩
  -- the circle parametrization
  have hrep : ∀ p ∈ Icc (0 : ℝ) T ×ˢ rectC A B C D,
      ∫ u, g u ∂((foldedCircle p.2 r).map (fwdMapInv W p.1)) =
        ∫ θ, g (fwdMapInv W p.1 (circleMap p.2 r θ)) ∂swA6CircM := by
    intro p hp
    have hrz : r ≤ p.2.im := by linarith [hp.2.2.1]
    have hae := RegCont.aemeasurable_fwdMapInv hW hW0 hp.1.1 p.2 hr
    rw [foldedCircle_eq_circleUnif hr.le hrz, swA6_circleUnif_eq_map] at hae ⊢
    have hcm : AEMeasurable (circleMap p.2 r) swA6CircM :=
      (continuous_circleMap _ _).measurable.aemeasurable
    rw [AEMeasurable.map_map_of_aemeasurable hae hcm]
    have hcont : Continuous fun θ => fwdMapInv W p.1 (circleMap p.2 r θ) := by
      refine (hjoint.comp_continuous (continuous_const.prodMk (continuous_circleMap _ _))
        fun θ => ⟨hp.1, hKwH (a8_circ_mem hp.2 hr.le hrC θ)⟩ :)
    exact integral_map hcont.measurable.aemeasurable hgm.aestronglyMeasurable
  refine ContinuousOn.congr ?_ hrep
  refine continuousOn_of_dominated (bound := fun _ => Cb) (fun p hp => ?_)
    (fun p hp => Eventually.of_forall fun θ => hCb _ (hmemI p hp θ)) (integrable_const Cb)
    (Eventually.of_forall fun θ => ?_)
  · have hcont : Continuous fun θ => fwdMapInv W p.1 (circleMap p.2 r θ) :=
      (hjoint.comp_continuous (continuous_const.prodMk (continuous_circleMap _ _))
        fun θ => ⟨hp.1, hKwH (a8_circ_mem hp.2 hr.le hrC θ)⟩ :)
    exact (hgm.comp hcont.measurable).aestronglyMeasurable
  · have hin : ContinuousOn (fun p : ℝ × ℂ => (p.1, circleMap p.2 r θ))
        (Icc (0 : ℝ) T ×ˢ rectC A B C D) := by
      refine (continuous_fst.prodMk ?_).continuousOn
      simp only [circleMap]; fun_prop
    have h2 := hjoint.comp hin fun p hp => ⟨hp.1, hKwH (a8_circ_mem hp.2 hr.le hrC θ)⟩
    exact hg.comp h2 fun p hp => hHHbar (hImH (hmemI p hp θ))

/-- **Joint continuity of the round value.** -/
theorem a8_cont_rnd (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) {A B C D : ℚ}
    (hC : (0 : ℝ) < C) {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) {r : ℝ}
    (hr : 0 < r) :
    ContinuousOn (fun p : ℝ × ℂ => evalReg x (foldedCircle (fwdMapInv W p.1 p.2)
      (r * ‖deriv (fwdMapInv W p.1) p.2‖))) (Icc (0 : ℝ) T ×ˢ rectC (A : ℝ) B C D) := by
  obtain ⟨ρ, M, m, hρ, hm, hcls⟩ := flow_mem_areaClass hW hW0 hT (a := A) (b := B) (d := D) hC
  have hRH : rectC (A : ℝ) B C D ⊆ H := a8_rect_H hC
  have hHHbar : H ⊆ Hbar := fun w hw => le_of_lt (show 0 < w.im from hw)
  have hpos : ∀ p ∈ Icc (0 : ℝ) T ×ˢ rectC (A : ℝ) B C D, 0 < ‖deriv (fwdMapInv W p.1) p.2‖ :=
    fun p hp => lt_of_lt_of_le hm ((hcls p.1 hp.1).2.2.2 p.2 hp.2)
  have hψ : ContinuousOn (fun p : ℝ × ℂ => fwdMapInv W p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ rectC (A : ℝ) B C D) :=
    (RegUnif.continuousOn_fwdMapInv_joint hW hW0 T).mono (prod_mono subset_rfl hRH)
  have hlog := (RegUnif.continuousOn_log_deriv_fwdMapInv_joint hW hW0 T).mono
    (prod_mono subset_rfl hRH)
  have hd : ContinuousOn (fun p : ℝ × ℂ => ‖deriv (fwdMapInv W p.1) p.2‖)
      (Icc (0 : ℝ) T ×ˢ rectC (A : ℝ) B C D) :=
    (Real.continuous_exp.comp_continuousOn hlog).congr fun p hp => by
      simp only [Function.comp_def]
      rw [Real.exp_log (hpos p hp)]
  have hmemH : ∀ p ∈ Icc (0 : ℝ) T ×ˢ rectC (A : ℝ) B C D, fwdMapInv W p.1 p.2 ∈ H :=
    fun p hp => RS.fwdMapInv_mem_H hW hW0 hp.1.1 (hRH hp.2)
  refine ContinuousOn.congr (f := fun p : ℝ × ℂ => F (fwdMapInv W p.1 p.2,
    r * ‖deriv (fwdMapInv W p.1) p.2‖)) ?_ fun p hp =>
      hF.evalReg_fc_of_mem (hHHbar (hmemH p hp)) (mul_pos hr (hpos p hp))
  exact hF.1.comp (hψ.prodMk (continuousOn_const.mul hd)) fun p hp =>
    ⟨hHHbar (hmemH p hp), mul_pos hr (hpos p hp)⟩

end SWCore
end QuantumZipper
