import QuantumZipper.Proofs.Thm18.ASep3Inner
import QuantumZipper.Proofs.Zipper.GenUCMod

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 9): `GenFam` for the circle-smoothed pushed circle, in time, and with the scale

At a fixed dyadic folded circle `fc(w, r)`, the level-`j` regularization of the rescaled field
`rescale X Q s` at the pushed circle `ν_t = fc(w, r).map f_t⁻¹` reads `X` at
`(bindFc ν_t 2^{-j}).map (s ·)` (the scale analogue of the family behind
`ASep.ae_tendsto_PsiK_all`, RegCont's `PsiK`). This file proves that these measures form a
Kolmogorov family in `(t, ρ)` (`genFam_bindνT`, via `GenUC.genFam_of_moduli` from the radius
modulus `RegCont.abs_kernelCov2_bindFc_le` and the time modulus
`RegCont.abs_kernelCov2_bindFc_time_le`, crude bound `RegUnif.abs_kernelCov2_le_four_potMax` for
large time increments), and then in `(t, s, ρ)` (`genFam_bindνT_dil`, `genFam_dil`).

Own elementary bookkeeping (moduli: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1;
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open GenUC TwoPoint

/-- The circle-smoothed pushed circle at time `p 0`. -/
abbrev bindνT (W : ℝ → ℝ) (w : ℂ) (r : ℝ) (p : Fin 1 → ℝ) (ρ : ℝ) : Measure ℂ :=
  RegCont.bindFc (RegCont.νT W w r (p 0)) ρ

/-- **`GenFam` for the circle-smoothed pushed circle, in time.** -/
theorem genFam_bindνT {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T a CH : ℝ}
    (hT : 0 < T) (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    {w : ℂ} {r : ℝ} (hr : 0 < r) {S : Set (Fin 1 → ℝ)} (hS : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T) :
    ∃ K c : ℝ, GenFam S (bindνT W w r) 1 K c := by
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  set R : ℝ := ‖w‖ + r with hRdef
  set CF : ℝ := RegCont.frostC T r R with hCF
  have hCF0 : 0 ≤ CF := RegUnif.frostC_nonneg hT.le hr
  set Bf : ℝ := RegCont.revBound (2 * M) T R with hBf
  have hBf0 : 0 ≤ Bf := RegCont.revBound_nonneg (by linarith) hT.le
  have hfacts : ∀ t ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (RegCont.νT W w r t) ∧
      TwoPoint.IsFrostman (RegCont.νT W w r t) (1 / 3) CF ∧
      ∀ᵐ z ∂RegCont.νT W w r t, ‖z‖ ≤ Bf := fun t ht => by
    obtain ⟨i1, f1, b1⟩ := RegUnif.νT_box_facts hW hW0 hr hM ht le_rfl le_rfl
    exact ⟨i1, fun x y hy => f1 x y hy, b1.mono fun z hz => hz.2⟩
  have hprob : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, IsProbabilityMeasure (bindνT W w r p ρ) :=
    fun p hp ρ _ => by
      have := (hfacts _ (hS p hp)).1
      exact ⟨by rw [CircleFubini.bind_circle_univ, measure_univ]⟩
  -- crude and small-increment constants
  set C₁ : ℝ := 2 * holderK (24 * CF) (Bf + 1) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have := holderK_nonneg (by positivity : 0 ≤ 24 * CF) (by linarith : (0 : ℝ) ≤ Bf + 1)
    positivity
  set h₀ : ℝ := min (1 / 2) (((CH + 1)⁻¹) ^ (1 / a)) with hh₀
  have hh₀ : 0 < h₀ := lt_min (by norm_num) (by positivity)
  set Kt : ℝ := RegCont.timeConstRad M T r R * (CH + 1) ^ (1 / 12 : ℝ) with hKt
  set Pc : ℝ := 4 * potMax (24 * CF) (Bf + 1) with hPc
  have hPc0 : 0 ≤ Pc := by
    have := potMax_nonneg (by positivity : 0 ≤ 24 * CF) (by linarith : (0 : ℝ) ≤ Bf + 1)
    positivity
  have hKt0 : 0 ≤ Kt := by
    have : 0 ≤ RegCont.timeConstRad M T r R := by
      unfold RegCont.timeConstRad
      have := holderK_nonneg (by positivity : 0 ≤ 24 * CF) (by linarith : (0 : ℝ) ≤ Bf + 1)
      have := potMax_nonneg (by positivity : 0 ≤ 24 * CF) (by linarith : (0 : ℝ) ≤ Bf + 1)
      positivity
    positivity
  set β : ℝ := a / 12 with hβ
  have hβ0 : 0 < β := by positivity
  set C₂ : ℝ := Kt + Pc / h₀ ^ β with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine genFam_of_moduli (M := 1) (fun p hp ρ hρ => ?_) (fun p hp ρ hρ => ?_) (D₀ := T)
    (fun p hp p' hp' => ?_) hC₁0 (by norm_num : (0 : ℝ) < (1 / 3) / 2)
    (fun p hp ρ hρ ρ' hρ' => ?_) hC₂0 hβ0 (fun p hp p' hp' ρ hρ => ?_)
  · have := (hfacts _ (hS p hp)).1
    exact RegCont.isAdmissibleH_bindFc (hfacts _ (hS p hp)).2.1 (hfacts _ (hS p hp)).2.2 hρ.1
  · have := (hfacts _ (hS p hp)).1
    show (RegCont.νT W w r (p 0)).bind (fun y => foldedCircle y ρ) univ = 1
    rw [CircleFubini.bind_circle_univ, measure_univ]
  · refine (dist_pi_le_iff hT.le).2 fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [Real.dist_eq]
    have h1 := hS p hp; have h2 := hS p' hp'
    exact abs_sub_le_iff.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2],
      by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  · have := (hfacts _ (hS p hp)).1
    exact RegCont.abs_kernelCov2_bindFc_le hBf0 hCF0 (hfacts _ (hS p hp)).2.1
      (hfacts _ (hS p hp)).2.2 hρ.1 hρ'.1 hρ.2 hρ'.2
  · -- the time modulus at a fixed radius
    have hd : |p 0 - p' 0| ≤ dist p p' := by
      have := dist_le_pi_dist p p' 0; rwa [Real.dist_eq] at this
    have key : ∀ t t' : ℝ, t ∈ Icc (0 : ℝ) T → t' ∈ Icc (0 : ℝ) T → t ≤ t' →
        |kernelCov2 neumannH (RegCont.bindFc (RegCont.νT W w r t) ρ,
          RegCont.bindFc (RegCont.νT W w r t') ρ) (RegCont.bindFc (RegCont.νT W w r t) ρ,
          RegCont.bindFc (RegCont.νT W w r t') ρ)| ≤ C₂ * (t' - t) ^ β := by
      intro t t' ht ht' htt
      set h := t' - t with hh
      have hh0 : 0 ≤ h := by rw [hh]; linarith
      rcases le_or_gt h h₀ with hsm | hlg
      · have hh12 : h ≤ 1 / 2 := hsm.trans (min_le_left _ _)
        have hε : ∀ q ∈ Icc (0 : ℝ) h, |W (t + h - q) - W (t + h)| ≤ CH * h ^ a := by
          intro q hq
          have e : t + h = t' := by rw [hh]; ring
          rw [e]
          have hq1 : t' - q ∈ Icc (0 : ℝ) T := ⟨by linarith [hq.2, ht.1], by linarith [hq.1, ht'.2]⟩
          have eq : |t' - q - t'| = q := by
            rw [show t' - q - t' = -q by ring, abs_neg, abs_of_nonneg hq.1]
          have h1 := hH (t' - q) hq1 t' ht' (by rw [eq]; linarith [hq.2])
          rw [eq] at h1
          exact h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.1 hq.2 ha.le) hCH)
        have hha : h ≤ h ^ a := Real.self_le_rpow_of_le_one hh0 (by linarith) ha1
        have hpow : h ^ a ≤ (CH + 1)⁻¹ := by
          calc h ^ a ≤ h₀ ^ a := Real.rpow_le_rpow hh0 hsm ha.le
            _ ≤ ((((CH + 1)⁻¹) ^ (1 / a))) ^ a :=
                Real.rpow_le_rpow hh₀.le (min_le_right _ _) ha.le
            _ = (CH + 1)⁻¹ := by
                rw [← Real.rpow_mul (by positivity), one_div_mul_cancel ha.ne', Real.rpow_one]
        have hsum : CH * h ^ a + h ≤ (CH + 1) * h ^ a := by nlinarith
        have hle1 : CH * h ^ a + h ≤ 1 := by
          have := mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤ CH + 1)
          rw [mul_inv_cancel₀ (by linarith)] at this
          linarith
        have hT1 := RegCont.abs_kernelCov2_bindFc_time_le hW hW0 hr hM (w := w) (R := R) le_rfl le_rfl ht.1 hh0
          (by rw [hh]; linarith [ht'.2]) hε hle1 hρ.1 hρ.2
        have e : t + h = t' := by rw [hh]; ring
        rw [e] at hT1
        refine hT1.trans ?_
        calc RegCont.timeConstRad M T r R * (CH * h ^ a + h) ^ (1 / 12 : ℝ)
            ≤ RegCont.timeConstRad M T r R * ((CH + 1) * h ^ a) ^ (1 / 12 : ℝ) := by
              gcongr
              · have : 0 ≤ Kt := hKt0
                exact nonneg_of_mul_nonneg_left (by simpa [hKt] using this)
                  (by positivity)
          _ = Kt * h ^ β := by
              rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hh0, hKt, hβ]
              ring_nf
          _ ≤ C₂ * h ^ β := by
              gcongr; rw [hC₂]; linarith [div_nonneg hPc0 (by positivity : (0 : ℝ) ≤ h₀ ^ β)]
      · have := (hfacts t ht).1
        have := (hfacts t' ht').1
        have ht1 : IsProbabilityMeasure (RegCont.bindFc (RegCont.νT W w r t) ρ) :=
          ⟨by rw [CircleFubini.bind_circle_univ, measure_univ]⟩
        have ht2 : IsProbabilityMeasure (RegCont.bindFc (RegCont.νT W w r t') ρ) :=
          ⟨by rw [CircleFubini.bind_circle_univ, measure_univ]⟩
        have hF1 := RegCont.isFrostman_bindFc (hfacts t ht).2.1 hρ.1
        have hF2 := RegCont.isFrostman_bindFc (hfacts t' ht').2.1 hρ.1
        have hc := RegUnif.abs_kernelCov2_le_four_potMax (by positivity : 0 ≤ 24 * CF)
          (by linarith : (0 : ℝ) ≤ Bf + 1) (fun x y hy => hF1 x y hy) (fun x y hy => hF2 x y hy)
          ((RegCont.ae_norm_bindFc_le hρ.1 (hfacts t ht).2.2).mono fun z hz => by
            linarith [hρ.2])
          ((RegCont.ae_norm_bindFc_le hρ.1 (hfacts t' ht').2.2).mono fun z hz => by
            linarith [hρ.2])
        refine hc.trans ?_
        have h1 : 1 ≤ (h / h₀) ^ β := Real.one_le_rpow (by rw [le_div_iff₀ hh₀]; linarith) hβ0.le
        have e : (h / h₀) ^ β = h ^ β / h₀ ^ β := Real.div_rpow hh0 hh₀.le _
        calc 4 * potMax (24 * CF) (Bf + 1) = Pc := rfl
          _ ≤ Pc * (h / h₀) ^ β := le_mul_of_one_le_right hPc0 h1
          _ = Pc / h₀ ^ β * h ^ β := by rw [e]; ring
          _ ≤ C₂ * h ^ β := by
              gcongr; rw [hC₂]; linarith
    rcases le_total (p 0) (p' 0) with hle | hle
    · refine (key _ _ (hS p hp) (hS p' hp') hle).trans ?_
      gcongr
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hd
      exact hd
    · rw [RegCont.kernelCov2_swap]
      refine (key _ _ (hS p' hp') (hS p hp) hle).trans ?_
      gcongr
      rw [abs_of_nonneg (by linarith)] at hd
      exact hd

/-- **`GenFam` for the dilated circle-smoothed pushed circle** `((t, s), ρ) ↦
(bindFc (fc(w, r).map f_t⁻¹) ρ).map (s ·)`, `s ∈ [s₀, s₁]`. -/
theorem genFam_bindνT_dil {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T a CH : ℝ}
    (hT : 0 < T) (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    {w : ℂ} {r : ℝ} (hr : 0 < r) {S : Set (Fin 1 → ℝ)} (hS : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T)
    {s₀ s₁ : ℝ} (hs₀ : 0 < s₀) :
    ∃ K c : ℝ, GenFam (dilSet S s₀ s₁) (dilFam (bindνT W w r)) 1 K c := by
  obtain ⟨K, c, hF⟩ := genFam_bindνT hW hW0 hT ha ha1 hCH hH hr hS
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  have hCF0 : 0 ≤ RegCont.frostC T r (‖w‖ + r) := RegUnif.frostC_nonneg hT.le hr
  have hBf0 : 0 ≤ RegCont.revBound (2 * M) T (‖w‖ + r) :=
    RegCont.revBound_nonneg (by linarith) hT.le
  have hfacts : ∀ t ∈ Icc (0 : ℝ) T, IsProbabilityMeasure (RegCont.νT W w r t) ∧
      TwoPoint.IsFrostman (RegCont.νT W w r t) (1 / 3) (RegCont.frostC T r (‖w‖ + r)) ∧
      ∀ᵐ z ∂RegCont.νT W w r t, ‖z‖ ≤ RegCont.revBound (2 * M) T (‖w‖ + r) := fun t ht => by
    obtain ⟨i1, f1, b1⟩ := RegUnif.νT_box_facts hW hW0 hr hM ht le_rfl le_rfl
    exact ⟨i1, fun x y hy => f1 x y hy, b1.mono fun z hz => hz.2⟩
  have hdiam : ∀ p ∈ S, ∀ p' ∈ S, dist p p' ≤ T := by
    intro p hp p' hp'
    refine (dist_pi_le_iff hT.le).2 fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [Real.dist_eq]
    have h1 := hS p hp; have h2 := hS p' hp'
    exact abs_sub_le_iff.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2],
      by linarith [h1.1, h1.2, h2.1, h2.2]⟩
  exact genFam_dil hF hs₀ (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)
    (by positivity : (0 : ℝ) ≤ 24 * RegCont.frostC T r (‖w‖ + r))
    (by linarith : (0 : ℝ) ≤ RegCont.revBound (2 * M) T (‖w‖ + r) + 1) hT.le
    (fun p hp ρ hρ => by
      have := (hfacts _ (hS p hp)).1
      exact RegCont.isFrostman_bindFc (hfacts _ (hS p hp)).2.1 hρ.1)
    (fun p hp ρ hρ => by
      have := (hfacts _ (hS p hp)).1
      exact (RegCont.ae_norm_bindFc_le hρ.1 (hfacts _ (hS p hp)).2.2).mono fun z hz => by
        linarith [hρ.2])
    hdiam

end ASep
end QuantumZipper
