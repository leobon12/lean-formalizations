import QuantumZipper.Proofs.Zipper.RegContMain

/-!
# JOINTMOD, step 1: the space modulus of the unzipped circles, uniformly in time

Task JOINTMOD (handoff `handoff/REG-UNIF.md`, item 1). For a continuous driver `W`, `W 0 = 0`,
`|W| ≤ M` on `[0,T]`, and `ν_t(w,r) = (fc(w,r)).map (fwdMapInv W t)` (`RegCont.νT`), the Neumann
energy of `ν_t(w,r) − ν_t(w',r')` is at most an explicit constant `spaceConst M T r₀ R` times
`δ^{1/12}`, `δ = ‖w − w'‖ + |r − r'| ≤ 1`, **uniformly in `t ∈ [0,T]`** and in the circles with
`r, r' ≥ r₀`, `‖w‖ + r, ‖w'‖ + r' ≤ R`:

```
theorem abs_kernelCov2_νT_space_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {w w' : ℂ} {r r' : ℝ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r') (hwR : ‖w‖ + r ≤ R)
    (hwR' : ‖w'‖ + r' ≤ R) (hδ1 : ‖w - w'‖ + |r - r'| ≤ 1) :
    |kernelCov2 neumannH (νT W w r t, νT W w' r' t) (νT W w r t, νT W w' r' t)| ≤
      spaceConst M T r₀ R * (‖w - w'‖ + |r - r'|) ^ (1 / 12 : ℝ)
```

The proof is the coupling argument of `TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`
(repeated here, since that statement only asserts the existence of a driver-dependent constant),
with the driver-dependent inputs replaced by explicit ones: the Frostman constant
`frostC T r₀ R` (`RegCont.isFrostman_pfc_frostC`) and the bound `revBound (2M) T R` on the reverse
maps of the time-reversed drivers `q ↦ W(t − q) − W t` (`RegCont.norm_revMap_le_revBound`).
Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (energy/Hölder bounds for circle averages); the uniformity in `t` is an **own
elementary argument** (monotonicity of the explicit constants in `t`).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace RegUnif

open TwoPoint RegCont

variable {W : ℝ → ℝ}

/-- The explicit constant of the space modulus, uniform in `t ∈ [0,T]`. -/
def spaceConst (M T r₀ R : ℝ) : ℝ :=
  2 * holderK (frostC T r₀ R) (revBound (2 * M) T R) *
      Real.sqrt (R ^ 2 + 4 * T) ^ ((1 / 3 : ℝ) / 2) +
    144 * potMax (frostC T r₀ R) (revBound (2 * M) T R) / Real.sqrt r₀

theorem frostC_nonneg {T r₀ R : ℝ} (hT : 0 ≤ T) (hr₀ : 0 < r₀) : 0 ≤ frostC T r₀ R := by
  have := hT; unfold frostC; positivity

theorem spaceConst_nonneg {M T r₀ R : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hr₀ : 0 < r₀) :
    0 ≤ spaceConst M T r₀ R := by
  have h1 := frostC_nonneg (R := R) hT hr₀
  have h2 := revBound_nonneg (R₀ := R) (by linarith : (0 : ℝ) ≤ 2 * M) hT
  have := holderK_nonneg h1 h2
  have := potMax_nonneg h1 h2
  unfold spaceConst
  positivity

/-- **The coupling bound with explicit inputs.** For a continuous driver `V` and time `t ≥ 0`,
if all pushed circles `pfc V t z ρ` (`r₀ ≤ ρ`, `‖z‖ + ρ ≤ R`) are `1/3`-Frostman with constant `CF`
and `‖revMap V t‖ ≤ Bf` on the ball of radius `R`, then the energy of
`pfc V t w r − pfc V t w' r'` is at most `(2 KH Mq^{1/6} + 144 Pm/√r₀) δ^{1/12}` for any
`Mq ≥ √(R² + 4t)`. (The proof of `TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`.) -/
theorem abs_kernelCov2_pfc_le_explicit {V : ℝ → ℝ} (hV : Continuous V) {t : ℝ} (ht : 0 ≤ t)
    {r₀ R CF Bf Mq : ℝ} (hr₀ : 0 < r₀) (hCF : 0 ≤ CF) (hBf0 : 0 ≤ Bf)
    (hFr : ∀ (z : ℂ) (ρ : ℝ), r₀ ≤ ρ → ‖z‖ + ρ ≤ R → IsFrostman (pfc V t z ρ) (1 / 3) CF)
    (hBf : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap V t z‖ ≤ Bf) (hMq : Real.sqrt (R ^ 2 + 4 * t) ≤ Mq)
    {w w' : ℂ} {r r' : ℝ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r') (hwR : ‖w‖ + r ≤ R)
    (hwR' : ‖w'‖ + r' ≤ R) (hδ1 : ‖w - w'‖ + |r - r'| ≤ 1) :
    |kernelCov2 neumannH (pfc V t w r, pfc V t w' r') (pfc V t w r, pfc V t w' r')| ≤
      (2 * holderK CF Bf * Mq ^ ((1 / 3 : ℝ) / 2) + 144 * potMax CF Bf / Real.sqrt r₀) *
        (‖w - w'‖ + |r - r'|) ^ (1 / 12 : ℝ) := by
  have hπ := Real.pi_pos
  set M := Real.sqrt (R ^ 2 + 4 * t) with hM
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hMq0 : 0 ≤ Mq := hM0.trans hMq
  set Pm := potMax CF Bf
  set KH := holderK CF Bf
  have hPm0 : 0 ≤ Pm := potMax_nonneg hCF hBf0
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hBf0
  have hr0 : 0 < r := hr₀.trans_le hr
  have hr0' : 0 < r' := hr₀.trans_le hr'
  set δ := ‖w - w'‖ + |r - r'| with hδdef
  rcases eq_or_lt_of_le (show 0 ≤ δ by positivity) with hδ0 | hδ
  · have hw : w = w' := by
      have := norm_nonneg (w - w'); have := abs_nonneg (r - r')
      rw [← sub_eq_zero, ← norm_eq_zero]; linarith
    have hrr : r = r' := by
      have := norm_nonneg (w - w'); have := abs_nonneg (r - r')
      rw [← sub_eq_zero, ← abs_eq_zero]; linarith
    subst hw hrr
    have : kernelCov2 neumannH (pfc V t w r, pfc V t w r) (pfc V t w r, pfc V t w r) = 0 := by
      unfold kernelCov2; ring
    rw [this, abs_zero, ← hδ0, Real.zero_rpow (by norm_num), mul_zero]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = pfc V t w r := ⟨_, rfl⟩
  obtain ⟨ν', hν'⟩ : ∃ ν', ν' = pfc V t w' r' := ⟨_, rfl⟩
  rw [← hν, ← hν']
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have : IsFiniteMeasure ν' := by rw [hν']; infer_instance
  have hFν : IsFrostman ν (1 / 3) CF := hν ▸ hFr w r hr hwR
  have hFν' : IsFrostman ν' (1 / 3) CF := hν' ▸ hFr w' r' hr' hwR'
  have hBν : ∀ᵐ y ∂ν, ‖y‖ ≤ Bf := hν ▸ pfc_ae_norm_le hV ht hr0.le hwR hBf
  have hBν' : ∀ᵐ y ∂ν', ‖y‖ ≤ Bf := hν' ▸ pfc_ae_norm_le hV ht hr0'.le hwR' hBf
  have hmν : ν.real univ = 1 := hν ▸ pfc_real_univ hV ht w r
  have hmν' : ν'.real univ = 1 := hν' ▸ pfc_real_univ hV ht w' r'
  set τ := Real.sqrt δ with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 hδ
  have hI1 : |∫ θ in Ico 0 (2 * π), (neuPot ν (revMap V t (foldH (circleMap w r θ))) -
        neuPot ν (revMap V t (foldH (circleMap w' r' θ))))| ≤
      2 * π * (KH * (δ * M / τ) ^ ((1 / 3 : ℝ) / 2)) + 2 * Pm * (72 * π * Real.sqrt (τ / r₀)) :=
    abs_integral_neuPot_coupling_le hV ht hr₀ hCF hBf0 hBf hτ hr hr' hwR hwR' le_rfl
    ν hFν hBν hmν
  have hI2 : |∫ θ in Ico 0 (2 * π), (neuPot ν' (revMap V t (foldH (circleMap w r θ))) -
        neuPot ν' (revMap V t (foldH (circleMap w' r' θ))))| ≤
      2 * π * (KH * (δ * M / τ) ^ ((1 / 3 : ℝ) / 2)) + 2 * Pm * (72 * π * Real.sqrt (τ / r₀)) :=
    abs_integral_neuPot_coupling_le hV ht hr₀ hCF hBf0 hBf hτ hr hr' hwR hwR' le_rfl
    ν' hFν' hBν' hmν'
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hFm : ∀ (z : ℂ) (ρ : ℝ), Measurable fun θ => revMap V t (foldH (circleMap z ρ θ)) :=
    fun z ρ => (measurable_revMap hV ht).comp (measurable_foldH.comp (measurable_circleMap z ρ))
  have hint : ∀ (κ : Measure ℂ) [IsFiniteMeasure κ], IsFrostman κ (1 / 3) CF →
      (∀ᵐ y ∂κ, ‖y‖ ≤ Bf) → κ.real univ = 1 → ∀ (z : ℂ) (ρ : ℝ), r₀ ≤ ρ → ‖z‖ + ρ ≤ R →
      Integrable (fun θ => neuPot κ (revMap V t (foldH (circleMap z ρ θ))))
        (volume.restrict (Ico (0 : ℝ) (2 * π))) := by
    intro κ _ hFκ hBκ hmκ z ρ hρ hzR
    refine Integrable.of_bound ((measurable_neuPot κ).comp (hFm z ρ)).aestronglyMeasurable Pm
      (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs]
    have := abs_neuPot_le hFκ (by norm_num) hCF hBf0 hBκ (hBf _ ((norm_foldH _).le.trans
      ((norm_circleMap_le_add z (hr₀.trans_le hρ).le θ).trans hzR)))
    rwa [hmκ] at this
  have e1 := integral_sub (hint ν hFν hBν hmν w r hr hwR) (hint ν hFν hBν hmν w' r' hr' hwR')
  have e2 := integral_sub (hint ν' hFν' hBν' hmν' w r hr hwR)
    (hint ν' hFν' hBν' hmν' w' r' hr' hwR')
  have hexp : kernelCov2 neumannH (ν, ν') (ν, ν') = (2 * π)⁻¹ *
      ((∫ θ in Ico 0 (2 * π), (neuPot ν (revMap V t (foldH (circleMap w r θ))) -
          neuPot ν (revMap V t (foldH (circleMap w' r' θ))))) -
        ∫ θ in Ico 0 (2 * π), (neuPot ν' (revMap V t (foldH (circleMap w r θ))) -
          neuPot ν' (revMap V t (foldH (circleMap w' r' θ))))) := by
    show kernelCov neumannH ν ν - kernelCov neumannH ν ν' - kernelCov neumannH ν' ν +
      kernelCov neumannH ν' ν' = _
    rw [kernelCov_pfc hV ht hν ν, kernelCov_pfc hV ht hν ν', kernelCov_pfc hV ht hν' ν,
      kernelCov_pfc hV ht hν' ν', e1, e2]
    ring
  have hdiv : δ * M / τ = Real.sqrt δ * M := by
    rw [hτdef, mul_div_right_comm, Real.div_sqrt]
  have hpow1 : (δ * M / τ) ^ ((1 / 3 : ℝ) / 2) = M ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ) := by
    rw [hdiv, Real.mul_rpow (Real.sqrt_nonneg _) hM0, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hδ.le, show (1 / 2 : ℝ) * ((1 / 3 : ℝ) / 2) = 1 / 12 by norm_num]
    ring
  have hpow2 : Real.sqrt (τ / r₀) ≤ δ ^ (1 / 12 : ℝ) / Real.sqrt r₀ := by
    rw [Real.sqrt_div (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hδ.le]
    refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  have hMM : M ^ ((1 / 3 : ℝ) / 2) ≤ Mq ^ ((1 / 3 : ℝ) / 2) :=
    Real.rpow_le_rpow hM0 hMq (by norm_num)
  rw [hexp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have hsub := abs_sub _ _ |>.trans (add_le_add hI1 hI2)
  rw [hpow1] at hsub
  have hsr : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have h3 := mul_le_mul_of_nonneg_left hpow2 (by positivity : (0 : ℝ) ≤ 2 * Pm * (72 * π))
  have hδp : 0 ≤ δ ^ (1 / 12 : ℝ) := by positivity
  have h4 : KH * (M ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ)) ≤
      KH * (Mq ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMM hδp) hKH0
  calc (2 * π)⁻¹ * |_ - _| ≤ (2 * π)⁻¹ *
        (2 * (2 * π * (KH * (M ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ))) +
          2 * Pm * (72 * π * Real.sqrt (τ / r₀)))) := by
        refine mul_le_mul_of_nonneg_left (hsub.trans (le_of_eq ?_)) (by positivity)
        ring
    _ ≤ (2 * π)⁻¹ *
        (2 * (2 * π * (KH * (Mq ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ))) +
          2 * Pm * (72 * π) * (δ ^ (1 / 12 : ℝ) / Real.sqrt r₀))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [h3, h4]
    _ = (2 * KH * Mq ^ ((1 / 3 : ℝ) / 2) + 144 * Pm / Real.sqrt r₀) * δ ^ (1 / 12 : ℝ) := by
        field_simp
        ring

/-- **Space modulus of the unzipped circles, uniform in `t ∈ [0,T]`.** -/
theorem abs_kernelCov2_νT_space_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {w w' : ℂ} {r r' : ℝ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r') (hwR : ‖w‖ + r ≤ R)
    (hwR' : ‖w'‖ + r' ≤ R) (hδ1 : ‖w - w'‖ + |r - r'| ≤ 1) :
    |kernelCov2 neumannH (νT W w r t, νT W w' r' t) (νT W w r t, νT W w' r' t)| ≤
      spaceConst M T r₀ R * (‖w - w'‖ + |r - r'|) ^ (1 / 12 : ℝ) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  set V : ℝ → ℝ := fun q => W (t - q) - W t with hVdef
  have hV : Continuous V := by fun_prop
  have hVM : ∀ s ∈ Icc (0 : ℝ) t, |V s| ≤ 2 * M := by
    intro s hs
    have h1 := hM (t - s) ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
    have h2 := hM t ht
    calc |W (t - s) - W t| ≤ |W (t - s)| + |W t| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hBf : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap V t z‖ ≤ revBound (2 * M) T R := fun z hz =>
    (norm_revMap_le_revBound hV ht.1 hVM R hz).trans (revBound_mono ht.2)
  have hr0 : 0 < r := hr₀.trans_le hr
  have hr0' : 0 < r' := hr₀.trans_le hr'
  rw [νT_eq_pfc hW hW0 ht.1 w hr0, νT_eq_pfc hW hW0 ht.1 w' hr0']
  exact abs_kernelCov2_pfc_le_explicit hV ht.1 hr₀ (frostC_nonneg hT hr₀)
    (revBound_nonneg (by linarith) hT)
    (fun z ρ hρ hzR => isFrostman_pfc_frostC hV ht.1 ht.2 hr₀ hρ hzR) hBf
    (Real.sqrt_le_sqrt (by linarith [ht.2])) hr hr' hwR hwR' hδ1

end RegUnif
end QuantumZipper
