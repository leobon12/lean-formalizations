import QuantumZipper.Proofs.Field.PairAffBasic

/-!
# PAIR-AFF, part 2: the three-parameter increment variance and Kolmogorov moment bound

For `q : Fin 3 → ℝ` put `s = min |q₀| δ'`, `t = q₁`, `b = max b₀ (min q₂ b₁)` and
`μ_q = (η ∘ aff(t,b)⁻¹) ∗ fc(·, s)` (`qμ`). For a free boundary GFF modulo constants `X`,

  `Var(X μ_q - X μ_{q'}) ≤ L ‖q - q'‖`

(`Setup.kernelCov2_qμ_le`), since the smoothed potentials satisfy
`|Π_{μ_q} - Π_{μ_{q'}}| ≤ 8π M' |s - s'| + 4 (2π M' + η(ℂ)) (|t - t'| + |R| |b - b'|)`
(`PairAffBasic`), and `kernelCov2 (μ, μ') (μ, μ') = ∫ (Π_μ - Π_{μ'}) d(μ - μ')`. Hence the
sixteenth-moment bound `Setup.momentBound3` of the dyadic Kolmogorov criterion
`KolmD.exists_continuous_modification_D` with `d = 3`.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3.1, Prop. 3.1 (increment-variance bound for circle averages followed by Kolmogorov–Čentsov;
here in the three parameters radius, translation, dilation); own elementary proof of the
variance bound (cost rule of AGENT_GUIDE).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real ComplexConjugate Topology

namespace QuantumZipper
namespace PairLim

open SmoothConv

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}

/-! ## 1. Potentials of affine images -/

theorem measurable_Nr_left (s : ℝ) (x : ℂ) : Measurable fun w => Nr s w x := by
  unfold Nr; exact (measurable_logmax s x).neg.sub (measurable_logmax s (conj x))

theorem Pot_map_aff (t b s : ℝ) (x : ℂ) :
    Pot (η.map (aff t b)) s x = ∫ w, Nr s (aff t b w) x ∂η := by
  unfold Pot
  exact integral_map (measurable_aff t b).aemeasurable (measurable_Nr_left s x).aestronglyMeasurable

theorem Setup.lintegral_inv_norm_aff_le (hS : Setup M R δ η) {t b b₀ : ℝ} (hb₀ : 0 < b₀)
    (hb : b₀ ≤ b) (c : ℂ) :
    ∫⁻ w, ENNReal.ofReal ‖aff t b w - c‖⁻¹ ∂η ≤
      ENNReal.ofReal ((Maff M b₀ : ℝ) * (2 * π) + (η univ).toReal) := by
  have := hS.good.isFiniteMeasure
  rw [← lintegral_map (measurable_inv_norm_sub c) (measurable_aff t b)]
  refine (lintegral_inv_norm_sub_le (map_aff_le hS.good.1 hb₀ hb) c).trans (le_of_eq ?_)
  rw [map_aff_univ, ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ENNReal.ofReal_coe_nnreal]

theorem Setup.ae_aff_ne (hS : Setup M R δ η) {t b b₀ : ℝ} (hb₀ : 0 < b₀) (hb : b₀ ≤ b) (c : ℂ) :
    ∀ᵐ w ∂η, aff t b w ≠ c := by
  have h := measure_singleton_of_le (map_aff_le (t := t) hS.good.1 hb₀ hb) c
  rw [Measure.map_apply (measurable_aff t b) (measurableSet_singleton c)] at h
  rw [ae_iff]
  exact measure_mono_null (fun w hw => by simpa using hw) h

/-- **Lipschitz bound in `(t, b)`** for the smoothed potentials of the affine images. -/
theorem Setup.abs_Pot_aff_sub_le (hS : Setup M R δ η) {b₀ t t' b b' s : ℝ} (hb₀ : 0 < b₀)
    (hb : b₀ ≤ b) (hb' : b₀ ≤ b') (hs : 0 ≤ s) (x : ℂ) :
    |Pot (η.map (aff t b)) s x - Pot (η.map (aff t' b')) s x| ≤
      (|t - t'| + |b - b'| * |R|) * (4 * ((Maff M b₀ : ℝ) * (2 * π) + (η univ).toReal)) := by
  have := hS.good.isFiniteMeasure
  set D := |t - t'| + |b - b'| * |R| with hD
  set K := (Maff M b₀ : ℝ) * (2 * π) + (η univ).toReal with hK
  have hD0 : 0 ≤ D := by positivity
  have hK0 : 0 ≤ K := by positivity
  have hi : ∀ {t b : ℝ}, b₀ ≤ b → Integrable (fun w => Nr s (aff t b w) x) η := fun {t b} hb =>
    (integrable_map_measure (measurable_Nr_left s x).aestronglyMeasurable
      (measurable_aff t b).aemeasurable).1 (integrable_Nr hs (hS.map_aff hb₀ hb).good x)
  rw [Pot_map_aff, Pot_map_aff, ← integral_sub (hi hb) (hi hb')]
  have h1 := norm_integral_le_lintegral_norm (μ := η)
    (fun w => Nr s (aff t b w) x - Nr s (aff t' b' w) x)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
  set I : ℝ → ℝ → ℂ → ℂ → ℝ≥0∞ := fun t b c w => ENNReal.ofReal ‖aff t b w - c‖⁻¹ with hI
  have hIm : ∀ t b c, Measurable (I t b c) := fun t b c =>
    (measurable_inv_norm_sub c).comp (measurable_aff t b)
  calc ∫⁻ w, ENNReal.ofReal ‖Nr s (aff t b w) x - Nr s (aff t' b' w) x‖ ∂η
      ≤ ∫⁻ w, ENNReal.ofReal D *
          (I t b x w + I t' b' x w + I t b (conj x) w + I t' b' (conj x) w) ∂η := by
        refine lintegral_mono_ae ?_
        filter_upwards [hS.good.ae_mem, hS.ae_aff_ne (t := t) hb₀ hb x,
          hS.ae_aff_ne (t := t') hb₀ hb' x, hS.ae_aff_ne (t := t) hb₀ hb (conj x),
          hS.ae_aff_ne (t := t') hb₀ hb' (conj x)] with w hw h1 h2 h3 h4
        have hwR : ‖w‖ ≤ R := by simpa using hw.1
        have hdist : ‖aff t b w - aff t' b' w‖ ≤ D := by
          have e : aff t b w - aff t' b' w = ((t - t' : ℝ) : ℂ) + ((b - b' : ℝ) : ℂ) * w := by
            simp only [aff]; push_cast; ring
          rw [e]
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hwR.trans (le_abs_self R)) (abs_nonneg _))
        have hreal := (abs_Nr_sub_le s h1 h2 h3 h4).trans
          (mul_le_mul_of_nonneg_right hdist (by positivity))
        rw [Real.norm_eq_abs]
        refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
        simp only [hI]
        rw [ENNReal.ofReal_mul hD0]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = ENNReal.ofReal D * (∫⁻ w, I t b x w ∂η + ∫⁻ w, I t' b' x w ∂η +
          ∫⁻ w, I t b (conj x) w ∂η + ∫⁻ w, I t' b' (conj x) w ∂η) := by
        rw [lintegral_const_mul (f := fun w => I t b x w + I t' b' x w + I t b (conj x) w +
            I t' b' (conj x) w) _ ((((hIm _ _ _).add (hIm _ _ _)).add (hIm _ _ _)).add
            (hIm _ _ _)),
          lintegral_add_left (f := fun w => I t b x w + I t' b' x w + I t b (conj x) w)
            (((hIm _ _ _).add (hIm _ _ _)).add (hIm _ _ _)),
          lintegral_add_left (f := fun w => I t b x w + I t' b' x w) ((hIm _ _ _).add (hIm _ _ _)),
          lintegral_add_left (hIm _ _ _)]
    _ ≤ ENNReal.ofReal D * (ENNReal.ofReal K + ENNReal.ofReal K + ENNReal.ofReal K +
          ENNReal.ofReal K) := by
        gcongr
        · exact hS.lintegral_inv_norm_aff_le hb₀ hb x
        · exact hS.lintegral_inv_norm_aff_le hb₀ hb' x
        · exact hS.lintegral_inv_norm_aff_le hb₀ hb (conj x)
        · exact hS.lintegral_inv_norm_aff_le hb₀ hb' (conj x)
    _ = ENNReal.ofReal (D * (4 * K)) := by
        rw [ENNReal.ofReal_mul hD0, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

/-! ## 2. Increment variance from a uniform bound on the potentials -/

theorem Setup.kernelCov_smooth_right (hS : Setup M R δ η) {b : ℝ} (hb0 : 0 ≤ b) (hbδ : b ≤ δ)
    (μ : Measure ℂ) : kernelCov neumannH μ (smooth η b) = ∫ x, Pot η b x ∂μ := by
  unfold kernelCov
  exact integral_congr_ae (ae_of_all _ fun x => hS.integral_neumannH_smooth hb0 hbδ x)

theorem Setup.integrable_Pot₂ {R' : ℝ} {η' : Measure ℂ} (hS : Setup M R δ η)
    (hS' : Setup M R' δ η') {a b : ℝ} (ha0 : 0 ≤ a) (haδ : a ≤ δ) (hb0 : 0 ≤ b) (hbδ : b ≤ δ) :
    Integrable (Pot η' b) (smooth η a) :=
  have := (hS'.smooth_good hb0 hbδ).isFiniteMeasure
  (integrable_neumannH_prod_sc
    ((hS.smooth_good ha0 haδ).mono (R' := max R R' + 1) (by linarith [le_max_left R R']))
    ((hS'.smooth_good hb0 hbδ).mono (R' := max R R' + 1)
      (by linarith [le_max_right R R']))).integral_prod_left
    |>.congr (ae_of_all _ fun x => hS'.integral_neumannH_smooth hb0 hbδ x)

theorem Setup.kernelCov2_le_of_pot {R' : ℝ} {η' : Measure ℂ} (hS : Setup M R δ η)
    (hS' : Setup M R' δ η') (hm : η' univ = η univ) {a a' B : ℝ} (ha0 : 0 ≤ a) (haδ : a ≤ δ)
    (ha0' : 0 ≤ a') (haδ' : a' ≤ δ) (hB : ∀ x, |Pot η a x - Pot η' a' x| ≤ B) :
    kernelCov2 neumannH (smooth η a, smooth η' a') (smooth η a, smooth η' a') ≤
      2 * B * (η univ).toReal := by
  have hD : ∀ ν : Measure ℂ, IsFiniteMeasure ν → Integrable (Pot η a) ν →
      Integrable (Pot η' a') ν → ν univ = η univ →
      |∫ x, Pot η a x ∂ν - ∫ x, Pot η' a' x ∂ν| ≤ B * (η univ).toReal := by
    intro ν _ h1 h2 hν
    rw [← integral_sub h1 h2]
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun x => Pot η a x - Pot η' a' x) (C := B)
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB x)
    rwa [Real.norm_eq_abs, measureReal_def, hν] at h
  simp only [kernelCov2, hS.kernelCov_smooth_right ha0 haδ, hS'.kernelCov_smooth_right ha0' haδ']
  have h1 := abs_le.1 (hD (smooth η a) (hS.smooth_good ha0 haδ).isFiniteMeasure
    (hS.integrable_Pot ha0 haδ ha0 haδ) (hS.integrable_Pot₂ hS' ha0 haδ ha0' haδ')
    (smooth_univ _ _))
  have h2 := abs_le.1 (hD (smooth η' a') (hS'.smooth_good ha0' haδ').isFiniteMeasure
    (hS'.integrable_Pot₂ hS ha0' haδ' ha0 haδ) (hS'.integrable_Pot ha0' haδ' ha0' haδ')
    (by rw [smooth_univ, hm]))
  linarith [h1.2, h2.1]

/-! ## 3. Gaussian increments -/

section Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem Setup.map_diff_eq_gaussianReal₂ {R' : ℝ} {η' : Measure ℂ} (hS : Setup M R δ η)
    (hS' : Setup M R' δ η') (hm : η' univ = η univ) (hX : IsFreeGFFModConstH X P)
    {a a' : ℝ} (ha0 : 0 ≤ a) (haδ : a ≤ δ) (ha0' : 0 ≤ a') (haδ' : a' ≤ δ) :
    P.map (fun ω => X ω (smooth η a) - X ω (smooth η' a')) =
      gaussianReal 0 (kernelCov2 neumannH (smooth η a, smooth η' a')
        (smooth η a, smooth η' a')).toNNReal := by
  have hadz := (hS.smooth_good ha0 haδ).isAdmissibleH
  have hadw := (hS'.smooth_good ha0' haδ').isAdmissibleH
  have hmass : smooth η a univ = smooth η' a' univ := by rw [smooth_univ, smooth_univ, hm]
  have hG : HasGaussianLaw (fun ω => X ω (smooth η a) - X ω (smooth η' a')) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(smooth η a, smooth η' a'), hadz, hadw, hmass⟩
  have hmeas : AEMeasurable (fun ω => X ω (smooth η a) - X ω (smooth η' a')) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω (smooth η a) - X ω (smooth η' a')] = 0 :=
    hX.centered _ _ hadz hadw hmass
  have hcov : cov[fun ω => X ω (smooth η a) - X ω (smooth η' a'),
      fun ω => X ω (smooth η a) - X ω (smooth η' a'); P] =
      kernelCov2 neumannH (smooth η a, smooth η' a') (smooth η a, smooth η' a') :=
    hX.covariance_eq (smooth η a, smooth η' a') (smooth η a, smooth η' a') hadz hadw hmass hadz
      hadw hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hmeas, hcov]

end Gauss

/-! ## 4. The three-parameter family -/

/-- Radius coordinate `min |q₀| δ`. -/
def qs (δ : ℝ) (q : Fin 3 → ℝ) : ℝ := min |q 0| δ

/-- Dilation coordinate `max b₀ (min q₂ b₁)`. -/
def qb (b₀ b₁ : ℝ) (q : Fin 3 → ℝ) : ℝ := max b₀ (min (q 2) b₁)

/-- The affine image of `η` with translation `q₁` and dilation `qb b₀ b₁ q`. -/
def qν (η : Measure ℂ) (b₀ b₁ : ℝ) (q : Fin 3 → ℝ) : Measure ℂ :=
  η.map (aff (q 1) (qb b₀ b₁ q))

theorem abs_coord_sub_le (q q' : Fin 3 → ℝ) (i : Fin 3) : |q i - q' i| ≤ ‖q - q'‖ := by
  simpa using norm_le_pi_norm (q - q') i

theorem abs_qs_sub_le (q q' : Fin 3 → ℝ) : |qs δ q - qs δ q'| ≤ ‖q - q'‖ := by
  unfold qs
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg (|q 0| - |q' 0|))]
  exact (abs_abs_sub_abs_le _ _).trans (abs_coord_sub_le q q' 0)

theorem abs_qb_sub_le {b₀ b₁ : ℝ} (q q' : Fin 3 → ℝ) :
    |qb b₀ b₁ q - qb b₀ b₁ q'| ≤ ‖q - q'‖ := by
  unfold qb
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg (min (q 2) b₁ - min (q' 2) b₁))]
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg (q 2 - q' 2))]
  exact abs_coord_sub_le q q' 2

theorem le_qb {b₀ b₁ : ℝ} (q : Fin 3 → ℝ) : b₀ ≤ qb b₀ b₁ q := le_max_left _ _

theorem Setup.setup_qν (hS : Setup M R δ η) {b₀ b₁ : ℝ} (hb₀ : 0 < b₀) (q : Fin 3 → ℝ) :
    Setup (Maff M b₀) (|q 1| + qb b₀ b₁ q * R) (min (b₀ * δ) 1) (qν η b₀ b₁ q) :=
  hS.map_aff hb₀ (le_qb q)

/-- The Lipschitz constant of the increment variance. -/
def Lq (M : ℝ≥0) (R : ℝ) (η : Measure ℂ) (b₀ : ℝ) : ℝ :=
  2 * (8 * π * Maff M b₀ + 4 * ((Maff M b₀ : ℝ) * (2 * π) + (η univ).toReal) * (1 + |R|)) *
    (η univ).toReal

theorem Lq_nonneg (M : ℝ≥0) (R : ℝ) (η : Measure ℂ) (b₀ : ℝ) : 0 ≤ Lq M R η b₀ := by
  unfold Lq; have := Real.pi_pos; positivity

/-- **Three-parameter increment variance bound.** -/
theorem Setup.kernelCov2_q_le (hS : Setup M R δ η) {b₀ b₁ : ℝ} (hb₀ : 0 < b₀)
    (q q' : Fin 3 → ℝ) :
    kernelCov2 neumannH
      (smooth (qν η b₀ b₁ q) (qs (min (b₀ * δ) 1) q),
        smooth (qν η b₀ b₁ q') (qs (min (b₀ * δ) 1) q'))
      (smooth (qν η b₀ b₁ q) (qs (min (b₀ * δ) 1) q),
        smooth (qν η b₀ b₁ q') (qs (min (b₀ * δ) 1) q')) ≤ Lq M R η b₀ * ‖q - q'‖ := by
  have := hS.good.isFiniteMeasure
  set δ' := min (b₀ * δ) 1 with hδ'
  have hS1 := hS.setup_qν (b₁ := b₁) hb₀ q
  have hS2 := hS.setup_qν (b₁ := b₁) hb₀ q'
  have hs0 : 0 ≤ qs δ' q := le_min (abs_nonneg _) hS1.pos.le
  have hs0' : 0 ≤ qs δ' q' := le_min (abs_nonneg _) hS1.pos.le
  have hs1 : qs δ' q ≤ δ' := min_le_right _ _
  have hs1' : qs δ' q' ≤ δ' := min_le_right _ _
  have hm : qν η b₀ b₁ q' univ = qν η b₀ b₁ q univ := by rw [qν, qν, map_aff_univ, map_aff_univ]
  set K := (Maff M b₀ : ℝ) * (2 * π) + (η univ).toReal with hK
  set B := 8 * π * Maff M b₀ * |qs δ' q - qs δ' q'| +
    (|q 1 - q' 1| + |qb b₀ b₁ q - qb b₀ b₁ q'| * |R|) * (4 * K) with hB
  have hPot : ∀ x, |Pot (qν η b₀ b₁ q) (qs δ' q) x - Pot (qν η b₀ b₁ q') (qs δ' q') x| ≤ B := by
    intro x
    have e1 := hS1.abs_Pot_sub_le' hs0 hs1 hs0' hs1' x
    have e2 := hS.abs_Pot_aff_sub_le (t := q 1) (t' := q' 1) (s := qs δ' q') hb₀ (le_qb (b₁ := b₁) q)
      (le_qb (b₁ := b₁) q') hs0' x
    simp only [qν] at e1 ⊢
    exact (abs_sub_le _ _ _).trans (add_le_add e1 e2)
  have hk := hS1.kernelCov2_le_of_pot hS2 hm hs0 hs1 hs0' hs1' hPot
  rw [qν, map_aff_univ] at hk
  refine hk.trans ?_
  have hπ := Real.pi_pos
  have hK0 : 0 ≤ K := by positivity
  have hsd := abs_qs_sub_le (δ := δ') q q'
  have htd := abs_coord_sub_le q q' 1
  have hbd := abs_qb_sub_le (b₀ := b₀) (b₁ := b₁) q q'
  have a1 : 8 * π * Maff M b₀ * |qs δ' q - qs δ' q'| ≤ 8 * π * Maff M b₀ * ‖q - q'‖ :=
    mul_le_mul_of_nonneg_left hsd (by positivity)
  have a2 : |q 1 - q' 1| + |qb b₀ b₁ q - qb b₀ b₁ q'| * |R| ≤ ‖q - q'‖ * (1 + |R|) := by
    nlinarith [mul_le_mul_of_nonneg_right hbd (abs_nonneg R)]
  have a3 := mul_le_mul_of_nonneg_right a2 (show 0 ≤ 4 * K by positivity)
  have hB' : B ≤ (8 * π * Maff M b₀ + 4 * K * (1 + |R|)) * ‖q - q'‖ := by
    rw [hB]; nlinarith
  have hm0 : 0 ≤ (η univ).toReal := ENNReal.toReal_nonneg
  have := mul_le_mul_of_nonneg_left hB' (show 0 ≤ 2 * (η univ).toReal by positivity)
  unfold Lq
  rw [← hK]
  nlinarith

section Moment

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

open KolmD in
/-- **Kolmogorov moment bound** for the three-parameter family. -/
theorem Setup.momentBound3 (hS : Setup M R δ η) (hX : IsFreeGFFModConstH X P) {b₀ b₁ : ℝ}
    (hb₀ : 0 < b₀) (R' : ℕ) :
    MomentBoundD (fun q ω => X ω (smooth (qν η b₀ b₁ q) (qs (min (b₀ * δ) 1) q))) P
      (Lq M R η b₀ ^ 8 * gaussianAbsMoment 16) R' := by
  intro q _ q' _
  have hS1 := hS.setup_qν (b₁ := b₁) hb₀ q
  have hS2 := hS.setup_qν (b₁ := b₁) hb₀ q'
  have hm : qν η b₀ b₁ q' univ = qν η b₀ b₁ q univ := by rw [qν, qν, map_aff_univ, map_aff_univ]
  have h0 : 0 ≤ qs (min (b₀ * δ) 1) q := le_min (abs_nonneg _) hS1.pos.le
  have h0' : 0 ≤ qs (min (b₀ * δ) 1) q' := le_min (abs_nonneg _) hS1.pos.le
  rw [RegSample.lintegral_pow16_of_map_eq
    (U := fun ω => X ω (smooth (qν η b₀ b₁ q) (qs (min (b₀ * δ) 1) q)) -
      X ω (smooth (qν η b₀ b₁ q') (qs (min (b₀ * δ) 1) q')))
    ((hX.measurable_coord _).sub (hX.measurable_coord _))
    (hS1.map_diff_eq_gaussianReal₂ hS2 hm hX h0 (min_le_right _ _) h0' (min_le_right _ _))]
  apply ENNReal.ofReal_le_ofReal
  set L := Lq M R η b₀ with hL
  have hL0 : 0 ≤ L := Lq_nonneg _ _ _ _
  have hkb := hS.kernelCov2_q_le (b₁ := b₁) hb₀ q q'
  have hnn : 0 ≤ L * ‖q - q'‖ := by positivity
  have hv : ((kernelCov2 neumannH
      (smooth (qν η b₀ b₁ q) (qs (min (b₀ * δ) 1) q),
        smooth (qν η b₀ b₁ q') (qs (min (b₀ * δ) 1) q'))
      (smooth (qν η b₀ b₁ q) (qs (min (b₀ * δ) 1) q),
        smooth (qν η b₀ b₁ q') (qs (min (b₀ * δ) 1) q'))).toNNReal : ℝ) ≤ L * ‖q - q'‖ := by
    rw [Real.coe_toNNReal']; exact max_le hkb hnn
  have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 8
  calc _ ≤ (L * ‖q - q'‖) ^ 8 * gaussianAbsMoment 16 :=
        mul_le_mul_of_nonneg_right h8 (gaussianAbsMoment_nonneg 16)
    _ = L ^ 8 * gaussianAbsMoment 16 * ‖q - q'‖ ^ 8 := by ring

end Moment

end PairLim
end QuantumZipper
