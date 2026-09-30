import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.GFF.CoordRegKolm

/-!
# REG-CONT, step 3: Kolmogorov for the two-parameter family, fixed driver

Blueprint `E_BRANCH_BLUEPRINT.md` §3, node REG-CONT; handoff `handoff/REG-CONT.md`, step 3.
Fix a continuous driver `W`, `W 0 = 0`, locally Hölder of exponent `a ∈ (0,1]` on `[0,T]`.
For `q = (s, ρ) ∈ ℝ²` put `μ_q = bindFc ν_{s̄} ρ̄` (`s̄ ∈ [0,T]`, `ρ̄ ∈ [0,1]` the clamped
parameters) and `Z q = X(μ_q)` (raw values of the free field). The increments are centred
Gaussians whose variances are the Neumann energies of step 1–2 (`RegContEnergy`):
`≤ K_t |s − s'|^{a/12}` at equal radius, `≤ K_ρ |ρ − ρ'|^{1/6}` at equal time; with
`E|A − C|^{2m} ≤ 2^{2m−1}(E|A − B|^{2m} + E|B − C|^{2m})` and Gaussian moments this gives
`E|Z q − Z q'|^{2m} ≤ K ‖q − q'‖^{m a/12}`, and the dyadic Kolmogorov criterion
`KolmG.exists_continuous_modification_G` (`d = 2`) gives a continuous modification `Ẑ`.
At `ρ = 2^{-k}` and rational `s`, almost surely `Z(s, 2^{-k}) = ∫ avgReg X k dν_s`
(`ae_integral_avgReg_eq`), so the averages `Ψ_k(s)` are uniformly Cauchy over the rational
times (`UCq`), by the uniform continuity of `Ẑ` on a compact box:

```
theorem ae_UCq (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) {a CH : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, |t - t'| ≤ 1 / 2 → |W t - W t'| ≤ CH * |t - t'| ^ a)
    (w : ℂ) {r : ℝ} (hr : 0 < r) : ∀ᵐ ω ∂P, UCq W w r T (X ω)
```

Sources: Hu, Miller, Peres, *Thick points of the Gaussian free field*, Ann. Probab. 38 (2010),
Prop. 2.1 (Kolmogorov for circle averages); Revuz–Yor, *Continuous Martingales and Brownian
Motion*, 3rd ed., Ch. I, Thm (2.1) (Kolmogorov criterion), in the dyadic form of `KolmG`.
-/

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegCont

open TwoPoint KolmD KolmG

variable {W : ℝ → ℝ}

/-! ## Parameters -/

/-- The time parameter, clamped to `[0,T]`. -/
def sPar (T : ℝ) (q : Fin 2 → ℝ) : ℝ := max (min (q 0) T) 0

/-- The radius parameter, clamped to `[0,1]`. -/
def ρPar (q : Fin 2 → ℝ) : ℝ := max (min (q 1) 1) 0

theorem sPar_mem {T : ℝ} (hT : 0 ≤ T) (q : Fin 2 → ℝ) : sPar T q ∈ Icc 0 T :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) hT⟩

theorem ρPar_mem (q : Fin 2 → ℝ) : ρPar q ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_right _ _, max_le (min_le_right _ _) zero_le_one⟩

theorem abs_clamp_sub_le (a b c : ℝ) :
    |max (min a c) 0 - max (min b c) 0| ≤ |a - b| :=
  (abs_max_sub_max_le_abs _ _ _).trans ((abs_min_sub_min_le_max _ _ _ _).trans
    (by simp))

theorem abs_coord_sub_le (q q' : Fin 2 → ℝ) (i : Fin 2) : |q i - q' i| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') i
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

/-- The measure `μ_q = ν_{s̄}^{ρ̄}`. -/
def μq (W : ℝ → ℝ) (w : ℂ) (r T : ℝ) (q : Fin 2 → ℝ) : Measure ℂ :=
  bindFc (νT W w r (sPar T q)) (ρPar q)

/-! ## Admissibility and Gaussian laws -/

theorem ae_mem_Hbar_bindFc (ν : Measure ℂ) [IsFiniteMeasure ν] (ρ : ℝ) :
    ∀ᵐ x ∂bindFc ν ρ, x ∈ Hbar := by
  rw [ae_iff, CircleFubini.bind_circle_apply ν (A := {a : ℂ | ¬ a ∈ Hbar})
    isClosed_Hbar.measurableSet.compl]
  refine (lintegral_congr fun y => ?_).trans lintegral_zero
  exact ae_iff.1 (RegClosure.fc_ae_mem_Hbar y ρ)

theorem isAdmissibleH_bindFc {ν : Measure ℂ} [IsFiniteMeasure ν] {C B : ℝ}
    (hF : TwoPoint.IsFrostman ν (1 / 3) C) (hB : ∀ᵐ y ∂ν, ‖y‖ ≤ B) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsAdmissibleH (bindFc ν ρ) := by
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) ν
  have hF' : IsFrostman (bindFc ν ρ) (1 / 3) (24 * C) := isFrostman_bindFc hF hρ
  refine FrostmanReg.isAdmissibleH_of_frostman (R := B + ρ) ?_ hF' (by norm_num)
  have h1 : ∀ᵐ x ∂bindFc ν ρ, x ∈ Metric.closedBall (0 : ℂ) (B + ρ) ∩ Hbar := by
    filter_upwards [ae_norm_bindFc_le hρ hB, ae_mem_Hbar_bindFc ν ρ] with x h1 h2
    exact ⟨mem_closedBall_zero_iff.2 h1, h2⟩
  exact ae_iff.1 h1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem map_diff_eq_gaussianReal (hX : IsFreeGFFModConstH X P) {a b : Measure ℂ}
    (ha : IsAdmissibleH a) (hb : IsAdmissibleH b) (hmass : a univ = b univ) :
    P.map (fun ω => X ω a - X ω b) =
      gaussianReal 0 (kernelCov2 neumannH (a, b) (a, b)).toNNReal := by
  have hG : HasGaussianLaw (fun ω => X ω a - X ω b) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(a, b), ha, hb, hmass⟩
  have hm : AEMeasurable (fun ω => X ω a - X ω b) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hc : P[fun ω => X ω a - X ω b] = 0 := hX.centered _ _ ha hb hmass
  have hcov := hX.covariance_eq (a, b) (a, b) ha hb hmass ha hb hmass
  rw [hG.map_eq_gaussianReal, hc, ← covariance_self hm, hcov]

theorem lintegral_pow_diff_le (hX : IsFreeGFFModConstH X P) {a b : Measure ℂ}
    (ha : IsAdmissibleH a) (hb : IsAdmissibleH b) (hmass : a univ = b univ) (m : ℕ) {V : ℝ}
    (hV : |kernelCov2 neumannH (a, b) (a, b)| ≤ V) :
    ∫⁻ ω, ENNReal.ofReal (|X ω a - X ω b| ^ (2 * m)) ∂P ≤
      ENNReal.ofReal (V ^ m * gaussianAbsMoment (2 * m)) := by
  rw [lintegral_pow_two_mul_of_map_eq (U := fun ω => X ω a - X ω b)
    ((hX.measurable_coord _).sub (hX.measurable_coord _)) m
    (map_diff_eq_gaussianReal hX ha hb hmass)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (gaussianAbsMoment_nonneg _))
  refine pow_le_pow_left₀ (NNReal.coe_nonneg _) ?_ m
  rw [Real.coe_toNNReal']
  exact max_le ((le_abs_self _).trans hV) ((abs_nonneg _).trans hV)

/-! ## Energy bounds for the family `μ_q` -/

theorem kernelCov2_swap (a b : Measure ℂ) :
    kernelCov2 neumannH (a, b) (a, b) = kernelCov2 neumannH (b, a) (b, a) := by
  unfold kernelCov2; ring

theorem abs_kernelCov_le_potMax {μ κ : Measure ℂ} [IsProbabilityMeasure μ] [IsFiniteMeasure κ]
    {C B : ℝ} (hC : 0 ≤ C) (hB0 : 0 ≤ B) (hF : TwoPoint.IsFrostman κ (1 / 3) C)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B) (hmκ : κ.real univ = 1) (hBμ : ∀ᵐ y ∂μ, ‖y‖ ≤ B) :
    |kernelCov neumannH μ κ| ≤ potMax C B := by
  show |∫ x, neuPot κ x ∂μ| ≤ potMax C B
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := neuPot κ) (C := potMax C B) ?_
  · rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
    exact h
  filter_upwards [hBμ] with x hx
  rw [Real.norm_eq_abs]
  have := abs_neuPot_le hF (by norm_num) hC hB0 hBκ (x := x) (X := B) hx
  rw [hmκ] at this
  unfold potMax
  linarith

/-- Energy bounds in both directions, with explicit Hölder exponents. -/
theorem energy_bounds (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) (w : ℂ) {r : ℝ}
    (hr : 0 < r) {a CH : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) :
    ∃ Kt Kρ : ℝ, 0 ≤ Kt ∧ 0 ≤ Kρ ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T, ∀ ρ ∈ Icc (0 : ℝ) 1,
        |kernelCov2 neumannH (bindFc (νT W w r s) ρ, bindFc (νT W w r s') ρ)
          (bindFc (νT W w r s) ρ, bindFc (νT W w r s') ρ)| ≤ Kt * |s - s'| ^ (a / 12)) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
        |kernelCov2 neumannH (bindFc (νT W w r s) ρ, bindFc (νT W w r s) ρ')
          (bindFc (νT W w r s) ρ, bindFc (νT W w r s) ρ')| ≤ Kρ * |ρ - ρ'| ^ ((1 / 3 : ℝ) / 2)) := by
  obtain ⟨C, B, hC, hB, hfacts⟩ := νT_facts hW hW0 T w hr
  obtain ⟨M, hM⟩ := exists_abs_le_on_Icc hW T
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT.le⟩)
  set TCR := timeConstRad M T r (‖w‖ + r) with hTCR
  set Pm := potMax (24 * C) (B + 1) with hPm
  have hPm0 : 0 ≤ Pm := potMax_nonneg (by positivity) (by linarith)
  have hTCR0 : 0 ≤ TCR := by
    have hfc : 0 ≤ frostC T r (‖w‖ + r) := by unfold frostC; positivity
    have hrb : 0 ≤ revBound (2 * M) T (‖w‖ + r) + 1 := by
      linarith [revBound_nonneg (R₀ := ‖w‖ + r) (by linarith : (0 : ℝ) ≤ 2 * M) hT.le]
    have h1 := holderK_nonneg (by positivity : 0 ≤ 24 * frostC T r (‖w‖ + r)) hrb
    have h2 := potMax_nonneg (by positivity : 0 ≤ 24 * frostC T r (‖w‖ + r)) hrb
    rw [hTCR]; unfold timeConstRad; positivity
  set E := (CH + 1) ^ (1 / 12 : ℝ) with hE
  have hE1 : 1 ≤ E := Real.one_le_rpow (by linarith) (by norm_num)
  refine ⟨(TCR + 8 * Pm) * E, 2 * holderK (24 * C) (B + 1), by positivity,
    by have := holderK_nonneg (by positivity : 0 ≤ 24 * C) (by linarith : 0 ≤ B + 1); positivity,
    ?_, ?_⟩
  · -- time direction
    -- crude bound
    have crude : ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T, ∀ ρ ∈ Icc (0 : ℝ) 1,
        |kernelCov2 neumannH (bindFc (νT W w r s) ρ, bindFc (νT W w r s') ρ)
          (bindFc (νT W w r s) ρ, bindFc (νT W w r s') ρ)| ≤ 4 * Pm := by
      intro s hs s' hs' ρ hρ
      obtain ⟨hP1, hF1, hB1⟩ := hfacts s hs
      obtain ⟨hP2, hF2, hB2⟩ := hfacts s' hs'
      haveI : IsProbabilityMeasure (bindFc (νT W w r s) ρ) :=
        ⟨by rw [CircleFubini.bind_circle_univ, measure_univ]⟩
      haveI : IsProbabilityMeasure (bindFc (νT W w r s') ρ) :=
        ⟨by rw [CircleFubini.bind_circle_univ, measure_univ]⟩
      have hsupp : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ], (∀ᵐ z ∂μ, z ∈ H ∧ ‖z‖ ≤ B) →
          ∀ᵐ y ∂bindFc μ ρ, ‖y‖ ≤ B + 1 := fun μ _ hμ =>
        (ae_norm_bindFc_le hρ.1 (hμ.mono fun z hz => hz.2)).mono fun y hy => by linarith [hρ.2]
      have b := fun (μ κ : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure κ]
          (hFκ : TwoPoint.IsFrostman κ (1 / 3) (24 * C)) (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + 1)
          (hBμ : ∀ᵐ y ∂μ, ‖y‖ ≤ B + 1) =>
        abs_kernelCov_le_potMax (μ := μ) (κ := κ) (by positivity) (by linarith) hFκ hBκ
          (by rw [probReal_univ]) hBμ
      set A := bindFc (νT W w r s) ρ
      set A' := bindFc (νT W w r s') ρ
      have hFA : TwoPoint.IsFrostman A (1 / 3) (24 * C) := isFrostman_bindFc hF1 hρ.1
      have hFA' : TwoPoint.IsFrostman A' (1 / 3) (24 * C) := isFrostman_bindFc hF2 hρ.1
      have hBA := hsupp _ hB1
      have hBA' := hsupp _ hB2
      have e1 := b A A hFA hBA hBA
      have e2 := b A A' hFA' hBA' hBA
      have e3 := b A' A hFA hBA hBA'
      have e4 := b A' A' hFA' hBA' hBA'
      unfold kernelCov2
      simp only
      rw [abs_le] at e1 e2 e3 e4 ⊢
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
    -- the main estimate for `s ≤ s'`
    have main : ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T, s ≤ s' → ∀ ρ ∈ Icc (0 : ℝ) 1,
        |kernelCov2 neumannH (bindFc (νT W w r s) ρ, bindFc (νT W w r s') ρ)
          (bindFc (νT W w r s) ρ, bindFc (νT W w r s') ρ)| ≤
          (TCR + 8 * Pm) * E * |s - s'| ^ (a / 12) := by
      intro s hs s' hs' hss ρ hρ
      set h := s' - s with hh
      have hh0 : 0 ≤ h := by rw [hh]; linarith
      have habs : |s - s'| = h := by rw [abs_sub_comm, abs_of_nonneg hh0]
      rw [habs]
      have hc := crude s hs s' hs' ρ hρ
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
        · have hb := abs_kernelCov2_bindFc_time_le (w := w) (r := r) (R := ‖w‖ + r) hW hW0 hr hM
            (le_refl r) (le_refl (‖w‖ + r)) hs.1 hh0
            (by rw [hh]; linarith [hs'.2]) hεb hδ1 hρ.1 hρ.2
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
    intro s hs s' hs' ρ hρ
    rcases le_total s s' with hss | hss
    · exact main s hs s' hs' hss ρ hρ
    · rw [kernelCov2_swap, abs_sub_comm]; exact main s' hs' s hs hss ρ hρ
  · -- radius direction
    intro s hs ρ hρ ρ' hρ'
    obtain ⟨hP1, hF1, hB1⟩ := hfacts s hs
    exact abs_kernelCov2_bindFc_le hB hC hF1 (hB1.mono fun z hz => hz.2) hρ.1 hρ'.1 hρ.2 hρ'.2

/-! ## Moments and Kolmogorov -/

theorem admissible_μq (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) (w : ℂ) {r : ℝ}
    (hr : 0 < r) (q : Fin 2 → ℝ) :
    IsAdmissibleH (μq W w r T q) ∧ μq W w r T q univ = 1 := by
  obtain ⟨C, B, hC, hB, hfacts⟩ := νT_facts hW hW0 T w hr
  obtain ⟨hP, hF, hae⟩ := hfacts _ (sPar_mem hT.le q)
  exact ⟨isAdmissibleH_bindFc hF (hae.mono fun z hz => hz.2) (ρPar_mem q).1,
    by rw [μq, bindFc, CircleFubini.bind_circle_univ, measure_univ]⟩

theorem add_pow_abs_le (u v : ℝ) (n : ℕ) :
    |u + v| ^ n ≤ 2 ^ (n - 1) * (|u| ^ n + |v| ^ n) :=
  (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le u v) n).trans
    (add_pow_le (abs_nonneg _) (abs_nonneg _) n)

/-- **Moment bound** `E|Z q − Z q'|^{2m} ≤ K ‖q − q'‖^{m a/12}`. -/
theorem momentBound_μq (hX : IsFreeGFFModConstH X P) (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) (w : ℂ) {r : ℝ} (hr : 0 < r) {a CH : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) (m : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ q q' : Fin 2 → ℝ,
      ∫⁻ ω, ENNReal.ofReal (|X ω (μq W w r T q) - X ω (μq W w r T q')| ^ (2 * m)) ∂P ≤
        ENNReal.ofReal (K * ‖q - q'‖ ^ ((m : ℝ) * (a / 12))) := by
  obtain ⟨Kt, Kρ, hKt, hKρ, ht, hρ⟩ := energy_bounds hW hW0 hT w hr ha ha1 hCH hH
  set β := a / 12 with hβ
  have hβ0 : 0 ≤ β := by positivity
  set c := gaussianAbsMoment (2 * m) with hc
  have hc0 : 0 ≤ c := gaussianAbsMoment_nonneg _
  refine ⟨2 ^ (2 * m - 1) * c * (Kt ^ m + Kρ ^ m), by positivity, fun q q' => ?_⟩
  set q'' : Fin 2 → ℝ := Function.update q 0 (q' 0) with hq''
  have hs'' : sPar T q'' = sPar T q' := by simp [sPar, q'']
  have hρ'' : ρPar q'' = ρPar q := by
    simp [ρPar, q'', Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  set Δ := ‖q - q'‖ with hΔ
  have hΔ0 : 0 ≤ Δ := norm_nonneg _
  have v1 : |kernelCov2 neumannH (μq W w r T q, μq W w r T q'') (μq W w r T q, μq W w r T q'')| ≤
      Kt * Δ ^ β := by
    simp only [μq, hs'', hρ'']
    refine (ht _ (sPar_mem hT.le q) _ (sPar_mem hT.le q') _ (ρPar_mem q)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _)
      ((abs_clamp_sub_le _ _ _).trans (abs_coord_sub_le q q' 0)) hβ0) hKt
  have v2 : |kernelCov2 neumannH (μq W w r T q'', μq W w r T q') (μq W w r T q'', μq W w r T q')| ≤
      Kρ * Δ ^ β := by
    simp only [μq, hs'', hρ'']
    refine (hρ _ (sPar_mem hT.le q') _ (ρPar_mem q) _ (ρPar_mem q')).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hKρ
    have h1 : |ρPar q - ρPar q'| ≤ 1 := by
      have := ρPar_mem q; have := ρPar_mem q'
      rw [abs_le]; constructor <;> linarith [(ρPar_mem q).1, (ρPar_mem q).2, (ρPar_mem q').1,
        (ρPar_mem q').2]
    refine (Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) h1 hβ0 (by rw [hβ]; linarith)).trans ?_
    exact Real.rpow_le_rpow (abs_nonneg _)
      ((abs_clamp_sub_le _ _ _).trans (abs_coord_sub_le q q' 1)) hβ0
  obtain ⟨ad1, ms1⟩ := admissible_μq hW hW0 hT w hr q
  obtain ⟨ad2, ms2⟩ := admissible_μq hW hW0 hT w hr q''
  obtain ⟨ad3, ms3⟩ := admissible_μq hW hW0 hT w hr q'
  have hm1 := lintegral_pow_diff_le hX ad1 ad2 (ms1.trans ms2.symm) m v1
  have hm2 := lintegral_pow_diff_le hX ad2 ad3 (ms2.trans ms3.symm) m v2
  set A := fun ω => X ω (μq W w r T q)
  set B := fun ω => X ω (μq W w r T q'')
  set Cc := fun ω => X ω (μq W w r T q')
  have hmeas : Measurable fun ω => ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) :=
    ((continuous_abs.measurable.comp
      ((hX.measurable_coord _).sub (hX.measurable_coord _))).pow_const _).ennreal_ofReal
  have hpt : ∀ ω, ENNReal.ofReal (|A ω - Cc ω| ^ (2 * m)) ≤ ENNReal.ofReal (2 ^ (2 * m - 1)) *
      (ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) + ENNReal.ofReal (|B ω - Cc ω| ^ (2 * m))) := by
    intro ω
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := add_pow_abs_le (A ω - B ω) (B ω - Cc ω) (2 * m)
    rwa [show A ω - B ω + (B ω - Cc ω) = A ω - Cc ω by ring] at this
  have epow : ∀ K : ℝ, (K * Δ ^ β) ^ m = K ^ m * Δ ^ ((m : ℝ) * β) := fun K => by
    rw [mul_pow, ← Real.rpow_natCast (Δ ^ β), ← Real.rpow_mul hΔ0, mul_comm β]
  calc ∫⁻ ω, ENNReal.ofReal (|A ω - Cc ω| ^ (2 * m)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 ^ (2 * m - 1)) *
          (ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) + ENNReal.ofReal (|B ω - Cc ω| ^ (2 * m))) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ (2 * m - 1)) * ((∫⁻ ω, ENNReal.ofReal (|A ω - B ω| ^ (2 * m)) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (|B ω - Cc ω| ^ (2 * m)) ∂P) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmeas]
    _ ≤ ENNReal.ofReal (2 ^ (2 * m - 1)) * (ENNReal.ofReal ((Kt * Δ ^ β) ^ m * c) +
          ENNReal.ofReal ((Kρ * Δ ^ β) ^ m * c)) := by gcongr
    _ = ENNReal.ofReal (2 ^ (2 * m - 1) * c * (Kt ^ m + Kρ ^ m) * Δ ^ ((m : ℝ) * β)) := by
        have h1 : 0 ≤ (Kt * Δ ^ β) ^ m * c := by positivity
        have h2 : 0 ≤ (Kρ * Δ ^ β) ^ m * c := by positivity
        rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_mul (by positivity), epow, epow]
        congr 1; ring

omit [MeasurableSpace Ω] in
/-- The Kolmogorov exponents: `θ = 2^{-β/4}`, `m = ⌈8/β⌉ + 1` (as in `CoordReg.kolm_exponents`). -/
theorem kolm_exponents' {β : ℝ} (hβ : 0 < β) :
    0 < (2 : ℝ) ^ (-β / 4) ∧ (2 : ℝ) ^ (-β / 4) < 1 ∧
      16 * ((1 / 2 : ℝ) ^ (((⌈8 / β⌉₊ + 1 : ℕ) : ℝ) * β) /
        ((2 : ℝ) ^ (-β / 4)) ^ (2 * (⌈8 / β⌉₊ + 1))) < 1 := by
  set m : ℕ := ⌈8 / β⌉₊ + 1 with hm
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith), ?_⟩
  have hmβ : 8 < (m : ℝ) * β := by
    have h1 : 8 / β ≤ (⌈8 / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (m : ℝ) = ⌈8 / β⌉₊ + 1 := by rw [hm]; push_cast; ring
    rw [h2]
    have : 8 / β * β = 8 := div_mul_cancel₀ _ hβ.ne'
    nlinarith
  have e1 : (1 / 2 : ℝ) ^ ((m : ℝ) * β) = (2 : ℝ) ^ (-((m : ℝ) * β)) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have e2 : ((2 : ℝ) ^ (-β / 4)) ^ (2 * m) = (2 : ℝ) ^ (-β / 4 * (2 * m : ℕ)) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have e3 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  rw [e1, e2, e3, ← Real.rpow_sub (by norm_num), ← Real.rpow_add (by norm_num)]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  push_cast
  nlinarith

/-- **REG-CONT step 3 (fixed driver).** Almost surely the averages `Ψ_k(s) = ∫ avgReg X k dν_s`
are uniformly Cauchy over the rational times `s ∈ [0,T]`. -/
theorem ae_UCq (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) {a CH : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, UCq W w r T (X ω) := by
  set β := a / 12 with hβ
  have hβ0 : 0 < β := by positivity
  obtain ⟨hθ0, hθ1, hρ⟩ := kolm_exponents' hβ0
  obtain ⟨K, hK, hmom⟩ := momentBound_μq hX hW hW0 hT w hr ha ha1 hCH hH (⌈8 / β⌉₊ + 1)
  obtain ⟨Y, hYc, hYeq, -⟩ := exists_continuous_modification_G (d := 2)
    (Z := fun q ω => X ω (μq W w r T q)) (P := P) (by norm_num) hθ0 hθ1
    (fun q => (hX.measurable_coord _).aemeasurable) (by positivity) hρ
    (fun R => ⟨K, hK, fun q _ q' _ => hmom q q'⟩)
  have hid : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
      Y ![(q : ℝ), radius k] ω = PsiK W w r q k (X ω) := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro q
    by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
    · obtain ⟨C, B, hC, hB, hfacts⟩ := νT_facts hW hW0 T w hr
      obtain ⟨hP, hF, hae⟩ := hfacts q hq
      have h1 : ∀ᵐ z ∂νT W w r q, z ∈ Metric.closedBall (0 : ℂ) B ∩ Hbar :=
        hae.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
      filter_upwards [hYeq ![(q : ℝ), radius k], Regularization.ae_integral_avgReg_eq hX k
        (νT W w r q) ((isCompact_closedBall _ _).inter_right isClosed_Hbar) inter_subset_right
        (ae_iff.1 h1)] with ω h1 h2 _
      rw [h1, PsiK, h2]
      have hs : sPar T ![(q : ℝ), radius k] = q := by
        simp [sPar, min_eq_left hq.2, max_eq_left hq.1]
      have hρk : ρPar ![(q : ℝ), radius k] = radius k := by
        simp [ρPar, min_eq_left (radius_le_one k), max_eq_left (radius_pos k).le]
      show X ω (μq W w r T _) = _
      rw [μq, hs, hρk]
    · exact ae_of_all _ fun ω h => absurd h hq
  filter_upwards [hid] with ω hid n
  have hUC := (isCompact_closedBall (0 : Fin 2 → ℝ) (T + 1)).uniformContinuousOn_of_continuous
    (hYc ω).continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hUC (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun k hk k' hk' q hq => ?_⟩
  rw [← hid k q hq, ← hid k' q hq]
  have hmem : ∀ j : ℕ, ![(q : ℝ), radius j] ∈ Metric.closedBall (0 : Fin 2 → ℝ) (T + 1) := by
    intro j
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
    intro i
    fin_cases i
    · have : ‖((q : ℝ))‖ ≤ T + 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hq.1]; linarith [hq.2]
      simpa using this
    · have : ‖radius j‖ ≤ T + 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (radius_pos j)]; linarith [radius_le_one j]
      simpa using this
  have hrN : ∀ j, N ≤ j → radius j ≤ radius N := fun j hj =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have hd : dist ![(q : ℝ), radius k] ![(q : ℝ), radius k'] < δ := by
    rw [dist_pi_lt_iff hδ]
    intro i
    fin_cases i
    · simp [hδ]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [Real.dist_eq, abs_sub_lt_iff]
      have h1 := hrN k hk; have h2 := hrN k' hk'
      have h3 : radius N < δ := hN
      have := radius_pos k; have := radius_pos k'
      constructor <;> linarith
  have := hδ' _ (hmem k) _ (hmem k') hd
  rw [Real.dist_eq] at this
  exact this.le

end RegCont
end QuantumZipper
