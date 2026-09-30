import QuantumZipper.Proofs.Zipper.JointModSpace
import QuantumZipper.Proofs.LQG.RegularSample

/-!
# JOINTMOD, step 2: four-parameter Kolmogorov step for a fixed driver

Task JOINTMOD (handoff `handoff/REG-UNIF.md`, item 1). Fix a continuous driver `W`, `W 0 = 0`,
locally `a`-Hölder on `[0,T]`. For `q ∈ ℝ⁴` put (with the circle parameters of
`RegSample.cen`, `RegSample.rad`, and the clamped time `tP T q = max (min (q 3) T) 0`)

`ν4 W T q = (fc(cen q, rad q)).map (fwdMapInv W (tP T q))`.

On every box `‖q‖_∞ ≤ R` the Neumann energies of `ν4 q − ν4 q'` are `≤ K ‖q − q'‖^{a/12}`: in time
by `RegCont.abs_kernelCov2_fwdMapInv_time_le` (uniform in the circle) and in space by
`abs_kernelCov2_νT_space_le` (uniform in time, `JointModSpace`), with the trivial bound
`4·potMax` for large increments. Gaussian moments and the dyadic Kolmogorov criterion
`KolmG.exists_continuous_modification_G` (`d = 4`) give a continuous modification:

```
theorem exists_contMod_ν4 (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) {a CH : ℝ} (ha : 0 < a)
    (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) :
    ∃ Y : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, (fun ω => Y q ω) =ᵐ[P] fun ω => X ω (ν4 W T q)) ∧
      ∀ᵐ ω ∂P, ∀ q, Tendsto (fun n => X ω (ν4 W T (rndD n q))) atTop (𝓝 (Y q ω))
```

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (continuous modification of circle averages); Revuz–Yor, *Continuous Martingales and
Brownian Motion*, 3rd ed., Ch. I, Thm (2.1) (Kolmogorov–Čentsov), in the dyadic form of `KolmG`.
The combination of the time and space moduli is the same as in `RegCont.momentBound_μq`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open TwoPoint RegCont KolmD KolmG RegSample

variable {W : ℝ → ℝ}

/-! ## Uniform facts and the crude bound -/

/-- The common bound of the Neumann potentials. -/
def potC (M T r₀ R : ℝ) : ℝ := potMax (frostC T r₀ R) (revBound (2 * M) T R)

theorem potC_nonneg {M T r₀ R : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hr₀ : 0 < r₀) :
    0 ≤ potC M T r₀ R :=
  potMax_nonneg (frostC_nonneg hT hr₀) (revBound_nonneg (by linarith) hT)

theorem νT_box_facts (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ} (hr₀ : 0 < r₀)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {w : ℂ} {r : ℝ}
    (hr : r₀ ≤ r) (hwR : ‖w‖ + r ≤ R) :
    IsProbabilityMeasure (νT W w r t) ∧ IsFrostman (νT W w r t) (1 / 3) (frostC T r₀ R) ∧
      ∀ᵐ z ∂νT W w r t, z ∈ H ∧ ‖z‖ ≤ revBound (2 * M) T R := by
  have hr0 : 0 < r := hr₀.trans_le hr
  refine ⟨(Measure.isProbabilityMeasure_map_iff (aemeasurable_fwdMapInv hW hW0 ht.1 w hr0)).2
      inferInstance, isFrostman_fwdMapInv_foldedCircle hW hW0 ht.1 ht.2 hr₀ hr hwR, ?_⟩
  refine (ae_map_iff (aemeasurable_fwdMapInv hW hW0 ht.1 w hr0)
    (show MeasurableSet {z : ℂ | z ∈ H ∧ ‖z‖ ≤ revBound (2 * M) T R} from
      (isOpen_H.measurableSet).inter
        (isClosed_le continuous_norm continuous_const).measurableSet)).2 ?_
  filter_upwards [foldedCircle_ae_mem_H w hr0, foldedCircle_ae_norm_le w hr0.le] with u hu hun
  exact fwdMapInv_mem_H_bound hW hW0 hM ht.1 ht.2 hu (hun.trans hwR)

theorem abs_kernelCov2_le_four_potMax {μ μ' : Measure ℂ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hF : IsFrostman μ (1 / 3) C) (hF' : IsFrostman μ' (1 / 3) C)
    (hBμ : ∀ᵐ y ∂μ, ‖y‖ ≤ B) (hBμ' : ∀ᵐ y ∂μ', ‖y‖ ≤ B) :
    |kernelCov2 neumannH (μ, μ') (μ, μ')| ≤ 4 * potMax C B := by
  have b := fun (ν κ : Measure ℂ) [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
      (hFκ : IsFrostman κ (1 / 3) C) (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B) (hBν : ∀ᵐ y ∂ν, ‖y‖ ≤ B) =>
    abs_kernelCov_le_potMax (μ := ν) (κ := κ) hC hB hFκ hBκ (by rw [probReal_univ]) hBν
  have e1 := b μ μ hF hBμ hBμ
  have e2 := b μ μ' hF' hBμ' hBμ
  have e3 := b μ' μ hF hBμ hBμ'
  have e4 := b μ' μ' hF' hBμ' hBμ'
  unfold kernelCov2
  simp only
  rw [abs_le] at e1 e2 e3 e4 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]

theorem crude_νT (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ} (hr₀ : 0 < r₀)
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {t t' : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (ht' : t' ∈ Icc (0 : ℝ) T) {w w' : ℂ} {r r' : ℝ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (hwR : ‖w‖ + r ≤ R) (hwR' : ‖w'‖ + r' ≤ R) :
    |kernelCov2 neumannH (νT W w r t, νT W w' r' t') (νT W w r t, νT W w' r' t')| ≤
      4 * potC M T r₀ R := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  obtain ⟨i1, f1, b1⟩ := νT_box_facts hW hW0 hr₀ hM ht hr hwR
  obtain ⟨i2, f2, b2⟩ := νT_box_facts hW hW0 hr₀ hM ht' hr' hwR'
  exact abs_kernelCov2_le_four_potMax (frostC_nonneg hT hr₀) (revBound_nonneg (by linarith) hT)
    f1 f2 (b1.mono fun z hz => hz.2) (b2.mono fun z hz => hz.2)

/-! ## Time and space moduli, uniform on boxes -/

theorem timeConst_nonneg {M T r₀ R : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (hr₀ : 0 < r₀) :
    0 ≤ timeConst M T r₀ R := by
  have h1 := frostC_nonneg (R := R) hT hr₀
  have h2 := revBound_nonneg (R₀ := R) (by linarith : (0 : ℝ) ≤ 2 * M) hT
  have := holderK_nonneg h1 h2
  have := potMax_nonneg h1 h2
  unfold timeConst
  positivity

/-- The time constant, uniform in the circles of the box. -/
def timeK (M T r₀ R CH : ℝ) : ℝ :=
  (timeConst M T r₀ R + 8 * potC M T r₀ R) * (CH + 1) ^ (1 / 12 : ℝ)

/-- **Time modulus, uniform in the circle.** -/
theorem abs_kernelCov2_νT_time_unif (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R a CH : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) (ha : 0 < a) (ha1 : a ≤ 1)
    (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    {w : ℂ} {r : ℝ} (hr : r₀ ≤ r) (hwR : ‖w‖ + r ≤ R) {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hs' : s' ∈ Icc (0 : ℝ) T) :
    |kernelCov2 neumannH (νT W w r s, νT W w r s') (νT W w r s, νT W w r s')| ≤
      timeK M T r₀ R CH * |s - s'| ^ (a / 12) := by
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  set Pm := potC M T r₀ R with hPm
  have hPm0 : 0 ≤ Pm := potC_nonneg hM0 hT hr₀
  set TCR := timeConst M T r₀ R with hTCR
  have hTCR0 : 0 ≤ TCR := timeConst_nonneg hM0 hT hr₀
  set E := (CH + 1) ^ (1 / 12 : ℝ) with hE
  have hE1 : 1 ≤ E := Real.one_le_rpow (by linarith) (by norm_num)
  have main : ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T, s ≤ s' →
      |kernelCov2 neumannH (νT W w r s, νT W w r s') (νT W w r s, νT W w r s')| ≤
        (TCR + 8 * Pm) * E * |s - s'| ^ (a / 12) := by
    intro s hs s' hs' hss
    set h := s' - s with hh
    have hh0 : 0 ≤ h := by rw [hh]; linarith
    have habs : |s - s'| = h := by rw [abs_sub_comm, abs_of_nonneg hh0]
    rw [habs]
    have hc := crude_νT hW hW0 hr₀ hM hs hs' hr hr hwR hwR
    have hpowa : 0 ≤ h ^ (a / 12) := Real.rpow_nonneg hh0 _
    by_cases hsmall : h ≤ 1 / 2
    · set ε := CH * h ^ a with hε
      have hε0 : 0 ≤ ε := by positivity
      have hεb : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε := by
        intro q hq
        have e : s + h = s' := by rw [hh]; ring
        rw [e]
        have hmem : s' - q ∈ Icc (0 : ℝ) T := ⟨by linarith [hq.2, hs.1], by linarith [hq.1, hs'.2]⟩
        have hd : |s' - q - s'| = q := by
          rw [show s' - q - s' = -q by ring, abs_neg, abs_of_nonneg hq.1]
        have := hH (s' - q) hmem s' hs' (by rw [hd]; linarith [hq.2])
        rw [hd] at this
        exact this.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hq.1 hq.2 ha.le) hCH)
      have hh1 : h ≤ 1 := by linarith
      have hha : h ≤ h ^ a := Real.self_le_rpow_of_le_one hh0 hh1 ha1
      have hsum : ε + h ≤ (CH + 1) * h ^ a := by rw [hε]; nlinarith
      have hkey : ((CH + 1) * h ^ a) ^ (1 / 12 : ℝ) = E * h ^ (a / 12) := by
        rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hh0 _), ← Real.rpow_mul hh0]
        congr 2; ring
      by_cases hδ1 : ε + h ≤ 1
      · have hb := abs_kernelCov2_fwdMapInv_time_le hW hW0 hr₀ hM hr hwR hs.1 hh0
          (by rw [hh]; linarith [hs'.2]) hεb hδ1
        rw [show s + h = s' by rw [hh]; ring] at hb
        refine hb.trans ?_
        calc TCR * (ε + h) ^ (1 / 12 : ℝ) ≤ TCR * ((CH + 1) * h ^ a) ^ (1 / 12 : ℝ) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hsum (by norm_num))
                hTCR0
          _ = TCR * E * h ^ (a / 12) := by rw [hkey]; ring
          _ ≤ (TCR + 8 * Pm) * E * h ^ (a / 12) := by gcongr; linarith
      · push Not at hδ1
        have h1 : 1 ≤ E * h ^ (a / 12) := by
          rw [← hkey]; exact Real.one_le_rpow (by linarith) (by norm_num)
        calc _ ≤ 4 * Pm := hc
          _ ≤ 4 * Pm * (E * h ^ (a / 12)) := le_mul_of_one_le_right (by positivity) h1
          _ ≤ (TCR + 8 * Pm) * E * h ^ (a / 12) := by
              have hX0 : 0 ≤ E * h ^ (a / 12) := by positivity
              nlinarith [mul_nonneg hTCR0 hX0, mul_nonneg hPm0 hX0]
    · push Not at hsmall
      have h1 : (1 / 2 : ℝ) ≤ h ^ (a / 12) := by
        have e1 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ (a / 12) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        have e2 : (1 / 2 : ℝ) ^ (a / 12) ≤ h ^ (a / 12) :=
          Real.rpow_le_rpow (by norm_num) hsmall.le (by positivity)
        rw [Real.rpow_one] at e1
        linarith
      calc _ ≤ 4 * Pm := hc
        _ ≤ 8 * Pm * h ^ (a / 12) := by nlinarith
        _ ≤ (TCR + 8 * Pm) * E * h ^ (a / 12) := by
            have : 8 * Pm ≤ (TCR + 8 * Pm) * E := by nlinarith
            exact mul_le_mul_of_nonneg_right this hpowa
  show _ ≤ (TCR + 8 * Pm) * E * _
  rcases le_total s s' with hss | hss
  · exact main s hs s' hs' hss
  · rw [kernelCov2_swap, abs_sub_comm]; exact main s' hs' s hs hss

/-- The space constant for exponents `β ≤ 1/12`. -/
def spaceK (M T r₀ R : ℝ) : ℝ := spaceConst M T r₀ R + 4 * potC M T r₀ R

/-- **Space modulus, uniform in time, all increments.** -/
theorem abs_kernelCov2_νT_space_unif (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R β : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 12)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {w w' : ℂ} {r r' : ℝ} (hr : r₀ ≤ r) (hr' : r₀ ≤ r')
    (hwR : ‖w‖ + r ≤ R) (hwR' : ‖w'‖ + r' ≤ R) :
    |kernelCov2 neumannH (νT W w r t, νT W w' r' t) (νT W w r t, νT W w' r' t)| ≤
      spaceK M T r₀ R * (‖w - w'‖ + |r - r'|) ^ β := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hPm0 := potC_nonneg (R := R) hM0 hT hr₀
  have hS0 := spaceConst_nonneg (R := R) hM0 hT hr₀
  set δ := ‖w - w'‖ + |r - r'| with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hpow : 0 ≤ δ ^ β := Real.rpow_nonneg hδ0 _
  unfold spaceK
  by_cases hδ1 : δ ≤ 1
  · refine (abs_kernelCov2_νT_space_le hW hW0 hr₀ hM ht hr hr' hwR hwR' hδ1).trans ?_
    have h1 : δ ^ (1 / 12 : ℝ) ≤ δ ^ β := Real.rpow_le_rpow_of_exponent_ge' hδ0 hδ1 hβ0 hβ
    have := mul_le_mul_of_nonneg_left h1 hS0
    nlinarith [mul_nonneg hPm0 hpow]
  · push Not at hδ1
    have h1 : 1 ≤ δ ^ β := Real.one_le_rpow hδ1.le hβ0
    have hc := crude_νT hW hW0 hr₀ hM ht ht hr hr' hwR hwR'
    nlinarith [mul_nonneg hS0 hpow]

end RegUnif
end QuantumZipper
