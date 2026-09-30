import QuantumZipper.Proofs.Zipper.RegCont
import QuantumZipper.Proofs.Loewner.TwoPointEnergy
import QuantumZipper.Proofs.GFF.CircleFubini

/-!
# REG-CONT, step 1: energy modulus in time

Blueprint `E_BRANCH_BLUEPRINT.md` §3, node REG-CONT; handoff `handoff/REG-CONT.md`, step 1.
With `ψ_s = fwdMapInv W s` and `ν_s = (fc(w,r)).map ψ_s`, the Neumann energy of `ν_s − ν_{s+h}` is
bounded by an explicit constant times `(ε + h)^{1/12}`, where `ε` bounds the oscillation of `W`
on `[s, s+h]`:

```
theorem abs_kernelCov2_fwdMapInv_time_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {w : ℂ} {r : ℝ} (hr : r₀ ≤ r)
    (hwR : ‖w‖ + r ≤ R) {s h ε : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) (hsh : s + h ≤ T)
    (hε : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) (hδ1 : ε + h ≤ 1) :
    |kernelCov2 neumannH (νT W w r s, νT W w r (s + h)) (νT W w r s, νT W w r (s + h))| ≤
      timeConst M T r₀ R * (ε + h) ^ (1 / 12 : ℝ)
```

with `νT W w r s = (foldedCircle w r).map (fwdMapInv W s)` and the explicit constant
`timeConst M T r₀ R = 2·holderK CF Bf·(2√(R²+8T))^{1/6} + 72·potMax CF Bf/√r₀`,
`CF = 18/√r₀ + 12√(R²+4T)/r₀`, `Bf = revBound (2M) T R` (polynomial in `M`, so its moments under
Brownian `W` are finite).

**Proof** (the coupling of `TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`, with the two circles
replaced by one circle and the two maps `f = ψ_s`, `f' = ψ_{s+h}`). By the flow property
`fwdMapInv_add`, `f' u = f(ψ̃ u)` with `ψ̃ = revMap Ṽ h` and `‖ψ̃ u − u‖ ≤ ε + 2h/Im u`
(`norm_revMap_sub_self_le`). Off the strip `{|Im u| < τ}` the two-point upper bound
(`norm_revMap_sub_mul_le_upper`) gives `‖f u − f' u‖ ≤ 2δ√(R²+8T)/τ²` (`δ = ε + h`, `τ ≤ 1`); the
strip has parameter measure `≤ 36π√(τ/r₀)` (`volume_strip_le`). The Neumann potentials of the
Frostman measures `ν_s, ν_{s+h}` are bounded and `1/6`-Hölder (`abs_neuPot_le`,
`abs_neuPot_sub_le`). Take `τ = δ^{1/4}`.

**Step 2 (radius).** With `ν^ρ = bindFc ν ρ = ν.bind fc(·,ρ)`:

```
theorem abs_kernelCov2_bindFc_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {B C : ℝ}
    (hB0 : 0 ≤ B) (hC : 0 ≤ C) (hF : TwoPoint.IsFrostman ν (1 / 3) C) (hB : ∀ᵐ y ∂ν, ‖y‖ ≤ B)
    {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ') (hρ1 : ρ ≤ 1) (hρ1' : ρ' ≤ 1) :
    |kernelCov2 neumannH (bindFc ν ρ, bindFc ν ρ') (bindFc ν ρ, bindFc ν ρ')| ≤
      2 * holderK (24 * C) (B + 1) * |ρ - ρ'| ^ ((1 / 3 : ℝ) / 2)
```

Proof: `ν^ρ` is `1/3`-Frostman with constant `24 C` uniformly in `ρ` (`isFrostman_bindFc`:
a circle of radius `ρ` gives mass `≤ 6t/ρ` to a `t`-ball, `volume_arc_le`), and the circle
average `fcPot κ ρ y = ∫ neuPot κ dfc(y,ρ)` is `1/6`-Hölder in `(y, ρ)` (same-angle coupling,
`abs_fcPot_sub_le`). **Time at fixed radius** (`abs_kernelCov2_bindFc_time_le`): the same bound as
step 1 for `ν_s^ρ` vs `ν_{s+h}^ρ`, `ρ ∈ [0,1]`, with constant `timeConstRad M T r₀ R`, via the
general time-coupling lemma `abs_integral_νT_time_sub_le` applied to `G = fcPot κ ρ`.

Source: this is the Kolmogorov-continuity input of Hu, Miller, Peres, *Thick points of the
Gaussian free field*, Ann. Probab. 38 (2010), Prop. 2.1 (energy of the difference of two
circle-average measures is Hölder in the parameters), transported through the Loewner flow; the
coupling estimate follows the proof of `TwoPoint.abs_kernelCov2_revMap_foldedCircle_le`
(own argument, no published source for the Loewner-transported version).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace RegCont

open TwoPoint UnzipInvariance

variable {W : ℝ → ℝ}

/-! ## An explicit bound for `revMap` on bounded sets -/

/-- Explicit form of the constant of `TwoPoint.exists_norm_revMap_le`. -/
def revBound (M T R₀ : ℝ) : ℝ := 4 * (2 * M + T + 1) + |R₀| + 2 * M + T

private lemma revMap_eq_zero_of_not_im_pos' {V : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : ¬ 0 < z.im) : revMap V T z = 0 := by
  unfold revMap
  rw [dif_neg]
  rintro ⟨u, hu⟩
  obtain ⟨h1, h2⟩ := hu.2 0 ⟨le_rfl, hT⟩
  rw [h2, intervalIntegral.integral_same] at h1
  exact hz (by simpa using h1)

/-- `‖revMap V T z‖ ≤ revBound M T R₀` for `‖z‖ ≤ R₀` and `|V| ≤ M` on `[0,T]`
(the proof of `TwoPoint.exists_norm_revMap_le`, with the bound `M` given). -/
theorem norm_revMap_le_revBound {V : ℝ → ℝ} (hV : Continuous V) {T M : ℝ} (hT : 0 ≤ T)
    (hM' : ∀ s ∈ Icc (0 : ℝ) T, |V s| ≤ M) (R₀ : ℝ) {z : ℂ} (hzR : ‖z‖ ≤ R₀) :
    ‖revMap V T z‖ ≤ revBound M T R₀ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, hT⟩)
  unfold revBound
  set K := 4 * (2 * M + T + 1) + |R₀| with hK
  have hK4 : 4 ≤ K := by nlinarith [abs_nonneg R₀]
  by_cases hz : 0 < z.im
  swap
  · rw [revMap_eq_zero_of_not_im_pos' hT hz, norm_zero]; linarith
  by_cases hle : ‖revMap V T z‖ ≤ K
  · linarith
  push Not at hle
  have hcont : ContinuousOn (fun s => ‖revMap V s z‖) (Icc 0 T) :=
    (ReverseFlow.continuousOn_revMap_time V hV z hz).norm.mono Icc_subset_Ici_self
  have h0 : ‖revMap V 0 z‖ ≤ K := by
    obtain ⟨u, hu⟩ := exists_isReverseSol V hV z hz 0 le_rfl
    rw [revMap_eq V hV z le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2,
      intervalIntegral.integral_same, sub_zero]
    calc ‖z - (V 0 : ℂ)‖ ≤ ‖z‖ + ‖(V 0 : ℂ)‖ := norm_sub_le _ _
      _ ≤ |R₀| + M := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (hzR.trans (le_abs_self _)) (hM' 0 ⟨le_rfl, hT⟩)
      _ ≤ K := by linarith
  obtain ⟨s₀, hs₀, hs₀eq'⟩ := intermediate_value_Icc hT hcont ⟨h0, hle.le⟩
  have hs₀eq : ‖revMap V s₀ z‖ = K := hs₀eq'
  have hsplit : revMap V T z =
      revMap (fun r => V (s₀ + r) - V s₀) (T - s₀) (revMap V s₀ z) := by
    have := ReverseFlow.revMap_add V hV z hz hs₀.1 (sub_nonneg.2 hs₀.2)
    rwa [add_sub_cancel] at this
  have hW' : Continuous fun r => V (s₀ + r) - V s₀ :=
    (hV.comp (continuous_const.add continuous_id)).sub continuous_const
  have hM'' : ∀ r ∈ Icc (0 : ℝ) (T - s₀), |V (s₀ + r) - V s₀| ≤ 2 * M := fun r hr => by
    have h1 := abs_le.1 (hM' (s₀ + r) ⟨by linarith [hs₀.1, hr.1], by linarith [hr.2]⟩)
    have h2 := abs_le.1 (hM' s₀ hs₀)
    rw [abs_le]; constructor <;> linarith
  have hzH : revMap V s₀ z ∈ H := im_revMap_pos hV hz hs₀.1
  have hfar := WeldingUniqueness.norm_revMap_sub_far hW' (sub_nonneg.2 hs₀.2) hM'' hzH
    (by rw [hs₀eq]; nlinarith [abs_nonneg R₀, hs₀.1])
  rw [hs₀eq] at hfar
  rw [hsplit]
  set u₀ := revMap V s₀ z
  set a := revMap (fun r => V (s₀ + r) - V s₀) (T - s₀) u₀
  set c : ℂ := ((V (s₀ + (T - s₀)) - V s₀ : ℝ) : ℂ)
  have e : a = (a - (u₀ - c)) + u₀ - c := by ring
  have hc : ‖c‖ ≤ 2 * M := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM'' (T - s₀) ⟨sub_nonneg.2 hs₀.2, le_rfl⟩
  have hdiv : 4 * (T - s₀) / K ≤ T := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hs₀.1]
  calc ‖a‖ = ‖(a - (u₀ - c)) + u₀ - c‖ := by rw [← e]
    _ ≤ ‖a - (u₀ - c)‖ + ‖u₀‖ + ‖c‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_add_le (a - (u₀ - c)) u₀])
    _ ≤ T + K + 2 * M := by
        rw [show ‖u₀‖ = K from hs₀eq]
        exact add_le_add (add_le_add (hfar.trans hdiv) le_rfl) hc
    _ = K + 2 * M + T := by ring

theorem revBound_mono {M T T' R₀ : ℝ} (hTT : T ≤ T') : revBound M T R₀ ≤ revBound M T' R₀ := by
  unfold revBound; linarith

theorem revBound_nonneg {M T R₀ : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) : 0 ≤ revBound M T R₀ := by
  unfold revBound; have := abs_nonneg R₀; linarith

/-! ## A generic coupling estimate for `∫ neuPot κ ∘ F − ∫ neuPot κ ∘ F'` -/

/-- If `‖F θ − F' θ‖ ≤ Δ` off a set `Bad` of parameter measure `≤ β`, both maps bounded by
`Bf`, then the integrals of the Neumann potential of a Frostman probability measure along `F`
and `F'` differ by `≤ 2π·holderK·Δ^{1/6} + β·2·potMax`. -/
theorem abs_integral_neuPot_sub_le_of_disp {F F' : ℝ → ℂ} (hFm : Measurable F)
    (hF'm : Measurable F') {Bf CF Δ β : ℝ} (hCF : 0 ≤ CF) (hBf0 : 0 ≤ Bf)
    (hFb : ∀ θ, ‖F θ‖ ≤ Bf) (hF'b : ∀ θ, ‖F' θ‖ ≤ Bf) {Bad : Set ℝ} (hBadm : MeasurableSet Bad)
    (hvolB : (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad ≤ β)
    (hdisp : ∀ θ, θ ∉ Bad → ‖F θ - F' θ‖ ≤ Δ) (hΔ : 0 ≤ Δ)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ (1 / 3) CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ Bf) (hmκ : κ.real univ = 1) :
    |∫ θ in Ico 0 (2 * π), (neuPot κ (F θ) - neuPot κ (F' θ))| ≤
      2 * π * (holderK CF Bf * Δ ^ ((1 / 3 : ℝ) / 2)) + β * (2 * potMax CF Bf) := by
  have hπ := Real.pi_pos
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  set Pm := potMax CF Bf
  set KH := holderK CF Bf
  have hPm0 : 0 ≤ Pm := potMax_nonneg hCF hBf0
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hBf0
  have hPb : ∀ x : ℂ, ‖x‖ ≤ Bf → |neuPot κ x| ≤ Pm := fun x hx => by
    have := abs_neuPot_le hFκ (by norm_num) hCF hBf0 hBκ hx
    rwa [hmκ] at this
  have hH : ∀ x x' : ℂ, ‖x‖ ≤ Bf → ‖x'‖ ≤ Bf →
      |neuPot κ x - neuPot κ x'| ≤ KH * ‖x - x'‖ ^ ((1 / 3 : ℝ) / 2) := fun x x' hx hx' => by
    have := abs_neuPot_sub_le hFκ (by norm_num) (by norm_num) hCF hBf0 hBκ hx hx'
    rwa [hmκ] at this
  have hi : ∀ G : ℝ → ℂ, Measurable G → (∀ θ, ‖G θ‖ ≤ Bf) →
      Integrable (fun θ => neuPot κ (G θ)) (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    fun G hG hGb => Integrable.of_bound ((measurable_neuPot κ).comp hG).aestronglyMeasurable Pm
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hPb _ (hGb θ))
  set D := KH * Δ ^ ((1 / 3 : ℝ) / 2) with hD
  have hpt : ∀ θ, |neuPot κ (F θ) - neuPot κ (F' θ)| ≤
      D + Bad.indicator (fun _ => 2 * Pm) θ := by
    intro θ
    by_cases hθ : θ ∈ Bad
    · rw [Set.indicator_of_mem hθ]
      have a1 := abs_le.1 (hPb _ (hFb θ))
      have a2 := abs_le.1 (hPb _ (hF'b θ))
      have : 0 ≤ D := by rw [hD]; positivity
      rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem hθ, add_zero]
      refine (hH _ _ (hFb θ) (hF'b θ)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hdisp θ hθ) (by norm_num)) hKH0
  have hint := (hi F hFm hFb).sub (hi F' hF'm hF'b)
  have hrhs : Integrable (fun θ => D + Bad.indicator (fun _ => 2 * Pm) θ)
      (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    (integrable_const D).add ((integrable_const (2 * Pm)).indicator hBadm)
  have hvolI : (volume.restrict (Ico (0 : ℝ) (2 * π))).real univ = 2 * π := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  calc |∫ θ in Ico 0 (2 * π), (neuPot κ (F θ) - neuPot κ (F' θ))|
      ≤ ∫ θ in Ico 0 (2 * π), |neuPot κ (F θ) - neuPot κ (F' θ)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ in Ico 0 (2 * π), (D + Bad.indicator (fun _ => 2 * Pm) θ) :=
        integral_mono hint.abs hrhs hpt
    _ = 2 * π * D + (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad * (2 * Pm) := by
        rw [integral_add (integrable_const D) ((integrable_const (2 * Pm)).indicator hBadm),
          integral_const, integral_indicator_const _ hBadm, hvolI, smul_eq_mul, smul_eq_mul]
    _ ≤ 2 * π * D + β * (2 * Pm) := by
        have := mul_le_mul_of_nonneg_right hvolB (by positivity : (0 : ℝ) ≤ 2 * Pm)
        linarith

/-! ## The energy modulus in time -/

/-- `ν_s = (fc(w,r)).map ψ_s`, `ψ_s = fwdMapInv W s`. -/
abbrev νT (W : ℝ → ℝ) (w : ℂ) (r s : ℝ) : Measure ℂ := (foldedCircle w r).map (fwdMapInv W s)

/-- The Frostman constant of `isFrostman_fwdMapInv_foldedCircle`. -/
def frostC (T r₀ R : ℝ) : ℝ := 18 / Real.sqrt r₀ + 12 * Real.sqrt (R ^ 2 + 4 * T) / r₀

/-- The constant of the energy modulus in time. -/
def timeConst (M T r₀ R : ℝ) : ℝ :=
  2 * holderK (frostC T r₀ R) (revBound (2 * M) T R) *
      (2 * Real.sqrt (R ^ 2 + 8 * T)) ^ ((1 / 3 : ℝ) / 2) +
    72 * potMax (frostC T r₀ R) (revBound (2 * M) T R) / Real.sqrt r₀

theorem νT_eq_pfc (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) (w : ℂ) {r : ℝ}
    (hr : 0 < r) : νT W w r s = pfc (fun q => W (s - q) - W s) s w r := by
  refine Measure.map_congr ?_
  filter_upwards [foldedCircle_ae_mem_H w hr] with x hx
  exact fwdMapInv_eq_revMap_timeRev W hW hW0 hs hx

theorem isFrostman_pfc_frostC {V : ℝ → ℝ} (hV : Continuous V) {t T : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) {w : ℂ} {r r₀ R : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hwR : ‖w‖ + r ≤ R) :
    TwoPoint.IsFrostman (pfc V t w r) (1 / 3) (frostC T r₀ R) := by
  have hF := isFrostman_revMap_foldedCircle hV ht hr₀ hr hwR
  intro p ρ hρ
  refine (hF p ρ hρ).trans ?_
  have hsq : Real.sqrt (R ^ 2 + 4 * t) ≤ Real.sqrt (R ^ 2 + 4 * T) :=
    Real.sqrt_le_sqrt (by linarith)
  have hpow : 0 ≤ ρ ^ (1 / 3 : ℝ) := Real.rpow_nonneg hρ.le _
  unfold frostC
  gcongr

/-- **Energy modulus in time** (REG-CONT step 1). -/
theorem abs_kernelCov2_fwdMapInv_time_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {w : ℂ} {r : ℝ} (hr : r₀ ≤ r)
    (hwR : ‖w‖ + r ≤ R) {s h ε : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) (hsh : s + h ≤ T)
    (hε : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) (hδ1 : ε + h ≤ 1) :
    |kernelCov2 neumannH (νT W w r s, νT W w r (s + h)) (νT W w r s, νT W w r (s + h))| ≤
      timeConst M T r₀ R * (ε + h) ^ (1 / 12 : ℝ) := by
  have hπ := Real.pi_pos
  have hr0 : 0 < r := hr₀.trans_le hr
  have hT : 0 ≤ T := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hε0 : 0 ≤ ε := by simpa using hε 0 ⟨le_rfl, hh⟩
  rcases eq_or_lt_of_le (show 0 ≤ ε + h by linarith) with hδ0 | hδ
  · have hh0 : h = 0 := by linarith
    subst hh0
    rw [add_zero]
    have : kernelCov2 neumannH (νT W w r s, νT W w r s) (νT W w r s, νT W w r s) = 0 := by
      unfold kernelCov2; ring
    rw [this, abs_zero, ← hδ0, Real.zero_rpow (by norm_num), mul_zero]
  have hsh0 : 0 ≤ s + h := by linarith
  rw [νT_eq_pfc hW hW0 hs w hr0, νT_eq_pfc hW hW0 hsh0 w hr0]
  set V : ℝ → ℝ := fun q => W (s - q) - W s with hVdef
  set V' : ℝ → ℝ := fun q => W (s + h - q) - W (s + h) with hV'def
  have hVc : Continuous V := by fun_prop
  have hV'c : Continuous V' := by fun_prop
  have hVb : ∀ q ∈ Icc (0 : ℝ) s, |V q| ≤ 2 * M := fun q hq => by
    have h1 := abs_le.1 (hM (s - q) ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have h2 := abs_le.1 (hM s ⟨hs, by linarith⟩)
    rw [abs_le]; constructor <;> linarith
  have hV'b : ∀ q ∈ Icc (0 : ℝ) (s + h), |V' q| ≤ 2 * M := fun q hq => by
    have h1 := abs_le.1 (hM (s + h - q) ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have h2 := abs_le.1 (hM (s + h) ⟨hsh0, hsh⟩)
    rw [abs_le]; constructor <;> linarith
  set Bf := revBound (2 * M) T R with hBfdef
  have hBf0 : 0 ≤ Bf := revBound_nonneg (by linarith) hT
  have hBfV : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap V s z‖ ≤ Bf := fun z hz =>
    (norm_revMap_le_revBound hVc hs hVb R hz).trans (revBound_mono (by linarith))
  have hBfV' : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap V' (s + h) z‖ ≤ Bf := fun z hz =>
    (norm_revMap_le_revBound hV'c hsh0 hV'b R hz).trans (revBound_mono hsh)
  set CF := frostC T r₀ R with hCFdef
  have hCF : 0 ≤ CF := by rw [hCFdef]; unfold frostC; positivity
  set M2 := Real.sqrt (R ^ 2 + 8 * T) with hM2
  have hM20 : 0 ≤ M2 := Real.sqrt_nonneg _
  set Pm := potMax CF Bf
  set KH := holderK CF Bf
  have hPm0 : 0 ≤ Pm := potMax_nonneg hCF hBf0
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hBf0
  have htc : timeConst M T r₀ R =
      2 * KH * (2 * M2) ^ ((1 / 3 : ℝ) / 2) + 72 * Pm / Real.sqrt r₀ := rfl
  rw [htc]
  set δ := ε + h with hδdef
  -- the pushed-forward measures
  obtain ⟨ν, hν⟩ : ∃ ν, ν = pfc V s w r := ⟨_, rfl⟩
  obtain ⟨ν', hν'⟩ : ∃ ν', ν' = pfc V' (s + h) w r := ⟨_, rfl⟩
  rw [← hν, ← hν']
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have : IsFiniteMeasure ν' := by rw [hν']; infer_instance
  have hFν : TwoPoint.IsFrostman ν (1 / 3) CF := hν ▸ isFrostman_pfc_frostC hVc hs (by linarith) hr₀ hr hwR
  have hFν' : TwoPoint.IsFrostman ν' (1 / 3) CF := hν' ▸ isFrostman_pfc_frostC hV'c hsh0 hsh hr₀ hr hwR
  have hBν : ∀ᵐ y ∂ν, ‖y‖ ≤ Bf := hν ▸ pfc_ae_norm_le hVc hs hr0.le hwR hBfV
  have hBν' : ∀ᵐ y ∂ν', ‖y‖ ≤ Bf := hν' ▸ pfc_ae_norm_le hV'c hsh0 hr0.le hwR hBfV'
  have hmν : ν.real univ = 1 := hν ▸ pfc_real_univ hVc hs w r
  have hmν' : ν'.real univ = 1 := hν' ▸ pfc_real_univ hV'c hsh0 w r
  -- the strip width `τ = δ^{1/4}`
  set τ := δ ^ (1 / 4 : ℝ) with hτdef
  have hτ : 0 < τ := Real.rpow_pos_of_pos hδ _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hττ : τ * τ = δ ^ (1 / 2 : ℝ) := by
    rw [hτdef, ← Real.rpow_add hδ]; norm_num
  have hδsq : δ ^ (1 / 2 : ℝ) * δ ^ (1 / 2 : ℝ) = δ := by
    rw [← Real.rpow_add hδ]; norm_num
  set Bad : Set ℝ := {θ | |(circleMap w r θ).im| < τ} with hBad
  have hBadm : MeasurableSet Bad :=
    (isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp (continuous_circleMap w r)))
      continuous_const).measurableSet
  have hvolB : (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad ≤
      36 * π * Real.sqrt (τ / r₀) := by
    rw [measureReal_def, Measure.restrict_apply hBadm]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hsub : Bad ∩ Ico 0 (2 * π) ⊆
        {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap w r θ).im| < τ} := fun θ hθ => ⟨hθ.2, hθ.1⟩
    refine (measure_mono hsub).trans ((volume_strip_le w hr0 hτ).trans
      (ENNReal.ofReal_le_ofReal ?_))
    have : Real.sqrt (τ / r) ≤ Real.sqrt (τ / r₀) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hτ.le hr₀ hr)
    nlinarith
  -- measurability and bounds of the two parametrizations
  have hFm : ∀ (U : ℝ → ℝ) (t : ℝ), Continuous U → 0 ≤ t →
      Measurable fun θ => revMap U t (foldH (circleMap w r θ)) := fun U t hU ht =>
    (measurable_revMap hU ht).comp (measurable_foldH.comp (measurable_circleMap w r))
  have hnormu : ∀ θ, ‖foldH (circleMap w r θ)‖ ≤ R := fun θ =>
    (norm_foldH _).le.trans ((norm_circleMap_le_add w hr0.le θ).trans hwR)
  -- the displacement off the strip
  have hdisp : ∀ θ, θ ∉ Bad → ‖revMap V s (foldH (circleMap w r θ)) -
      revMap V' (s + h) (foldH (circleMap w r θ))‖ ≤ 2 * M2 * δ ^ (1 / 2 : ℝ) := by
    intro θ hθ
    simp only [hBad, mem_setOf_eq, not_lt] at hθ
    set u := foldH (circleMap w r θ) with hu_def
    have hu : τ ≤ u.im := by rw [hu_def, im_foldH]; exact hθ
    have hu0 : u ∈ H := show 0 < u.im by linarith
    have hunorm : ‖u‖ ≤ R := hnormu θ
    set v := revMap V' h u with hv_def
    have hflow : revMap V' (s + h) u = revMap V s v := by
      have h1 := fwdMapInv_add hW hW0 hs hh hu0
      have h2 := fwdMapInv_eq_revMap_timeRev W hW hW0 hsh0 hu0
      have h3 := fwdMapInv_eq_revMap_timeRev W hW hW0 hs (im_revMap_pos hV'c hu0 hh)
      exact h2.symm.trans (h1.trans h3)
    have hvτ : τ ≤ v.im := hu.trans (im_le_im_revMap V' hV'c u hu0 hh)
    have huR0 : u.im ≤ R := (Complex.im_le_norm u).trans hunorm
    have hR2 : R ^ 2 ≤ R ^ 2 + 4 * T := by linarith
    have huR : u.im ≤ Real.sqrt (R ^ 2 + 4 * T) :=
      (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))
    have hvR : v.im ≤ Real.sqrt (R ^ 2 + 4 * T) := by
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      have h1 := im_revMap_sq_le hV'c hu0 hh
      have h2 : u.im ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hu0.le huR0 2
      linarith
    have key := norm_revMap_sub_mul_le_upper hVc hs hτ hu hvτ huR hvR
    have hsqrt : Real.sqrt (Real.sqrt (R ^ 2 + 4 * T) ^ 2 + 4 * s) ≤ M2 := by
      rw [Real.sq_sqrt (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hnear := norm_revMap_sub_self_le hV'c hu0 hh hε
    have huv : ‖u - v‖ ≤ 2 * δ / τ := by
      rw [norm_sub_rev, le_div_iff₀ hτ]
      have e1 : 2 * h / u.im * τ ≤ 2 * h := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        exact mul_le_mul_of_nonneg_left hu (by linarith)
      have e2 : ε * τ ≤ ε := by
        have := mul_le_mul_of_nonneg_left hτ1 hε0
        linarith
      have e3 := mul_le_mul_of_nonneg_right hnear hτ.le
      have e4 : (ε + 2 * h / u.im) * τ = ε * τ + 2 * h / u.im * τ := by ring
      rw [hδdef]; linarith
    have hA : ‖revMap V s u - revMap V' (s + h) u‖ * τ ≤ 2 * δ / τ * M2 := by
      rw [hflow]
      exact key.trans (mul_le_mul huv hsqrt (Real.sqrt_nonneg _) (by positivity))
    have hB : ‖revMap V s u - revMap V' (s + h) u‖ * (τ * τ) ≤
        2 * M2 * δ ^ (1 / 2 : ℝ) * (τ * τ) := by
      have e : 2 * δ / τ * M2 * τ = 2 * δ * M2 := by
        rw [mul_right_comm, div_mul_cancel₀ _ hτ.ne']
      have h' := mul_le_mul_of_nonneg_right hA hτ.le
      calc ‖revMap V s u - revMap V' (s + h) u‖ * (τ * τ)
          = ‖revMap V s u - revMap V' (s + h) u‖ * τ * τ := by ring
        _ ≤ 2 * δ / τ * M2 * τ := h'
        _ = 2 * M2 * (δ ^ (1 / 2 : ℝ) * δ ^ (1 / 2 : ℝ)) := by rw [e, hδsq]; ring
        _ = 2 * M2 * δ ^ (1 / 2 : ℝ) * (τ * τ) := by rw [hττ]; ring
    exact le_of_mul_le_mul_right hB (mul_pos hτ hτ)
  have hΔ0 : 0 ≤ 2 * M2 * δ ^ (1 / 2 : ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hδ.le _)
  have hFb : ∀ θ, ‖revMap V s (foldH (circleMap w r θ))‖ ≤ Bf := fun θ => hBfV _ (hnormu θ)
  have hF'b : ∀ θ, ‖revMap V' (s + h) (foldH (circleMap w r θ))‖ ≤ Bf := fun θ =>
    hBfV' _ (hnormu θ)
  have hC1 := abs_integral_neuPot_sub_le_of_disp (hFm V s hVc hs) (hFm V' (s + h) hV'c hsh0)
    hCF hBf0 hFb hF'b hBadm hvolB hdisp hΔ0 ν hFν hBν hmν
  have hC2 := abs_integral_neuPot_sub_le_of_disp (hFm V s hVc hs) (hFm V' (s + h) hV'c hsh0)
    hCF hBf0 hFb hF'b hBadm hvolB hdisp hΔ0 ν' hFν' hBν' hmν'
  -- expansion of the energy
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hint : ∀ (κ : Measure ℂ) [IsFiniteMeasure κ], TwoPoint.IsFrostman κ (1 / 3) CF →
      (∀ᵐ y ∂κ, ‖y‖ ≤ Bf) → κ.real univ = 1 → ∀ (U : ℝ → ℝ) (t : ℝ), Continuous U → 0 ≤ t →
      (∀ θ, ‖revMap U t (foldH (circleMap w r θ))‖ ≤ Bf) →
      Integrable (fun θ => neuPot κ (revMap U t (foldH (circleMap w r θ))))
        (volume.restrict (Ico (0 : ℝ) (2 * π))) := by
    intro κ _ hFκ hBκ hmκ U t hU ht hb
    refine Integrable.of_bound ((measurable_neuPot κ).comp (hFm U t hU ht)).aestronglyMeasurable
      Pm (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs]
    have := abs_neuPot_le hFκ (by norm_num) hCF hBf0 hBκ (hb θ)
    rwa [hmκ] at this
  have e1 := integral_sub (hint ν hFν hBν hmν V s hVc hs hFb)
    (hint ν hFν hBν hmν V' (s + h) hV'c hsh0 hF'b)
  have e2 := integral_sub (hint ν' hFν' hBν' hmν' V s hVc hs hFb)
    (hint ν' hFν' hBν' hmν' V' (s + h) hV'c hsh0 hF'b)
  have hexp : kernelCov2 neumannH (ν, ν') (ν, ν') = (2 * π)⁻¹ *
      ((∫ θ in Ico 0 (2 * π), (neuPot ν (revMap V s (foldH (circleMap w r θ))) -
          neuPot ν (revMap V' (s + h) (foldH (circleMap w r θ))))) -
        ∫ θ in Ico 0 (2 * π), (neuPot ν' (revMap V s (foldH (circleMap w r θ))) -
          neuPot ν' (revMap V' (s + h) (foldH (circleMap w r θ))))) := by
    show kernelCov neumannH ν ν - kernelCov neumannH ν ν' - kernelCov neumannH ν' ν +
      kernelCov neumannH ν' ν' = _
    rw [kernelCov_pfc hVc hs hν ν, kernelCov_pfc hVc hs hν ν', kernelCov_pfc hV'c hsh0 hν' ν,
      kernelCov_pfc hV'c hsh0 hν' ν', e1, e2]
    ring
  -- the algebra of `τ = δ^{1/4}`
  have hpow1 : (2 * M2 * δ ^ (1 / 2 : ℝ)) ^ ((1 / 3 : ℝ) / 2) =
      (2 * M2) ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le,
      show (1 / 2 : ℝ) * ((1 / 3 : ℝ) / 2) = 1 / 12 by norm_num]
  have hsr : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have hpow2 : Real.sqrt (τ / r₀) ≤ δ ^ (1 / 12 : ℝ) / Real.sqrt r₀ := by
    rw [Real.sqrt_div hτ.le, Real.sqrt_eq_rpow τ, hτdef, ← Real.rpow_mul hδ.le]
    refine div_le_div_of_nonneg_right ?_ hsr.le
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  rw [hexp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have hsub := (abs_sub _ _).trans (add_le_add hC1 hC2)
  rw [hpow1] at hsub
  set x := δ ^ (1 / 12 : ℝ) with hx
  have h3 : 36 * π * Real.sqrt (τ / r₀) * (2 * Pm) ≤ 36 * π * (x / Real.sqrt r₀) * (2 * Pm) := by
    gcongr
  have hπne : π ≠ 0 := hπ.ne'
  have hsrne : Real.sqrt r₀ ≠ 0 := hsr.ne'
  calc (2 * π)⁻¹ * |_ - _| ≤ (2 * π)⁻¹ *
        (2 * (2 * π * (KH * ((2 * M2) ^ ((1 / 3 : ℝ) / 2) * x))) +
          2 * (36 * π * (x / Real.sqrt r₀) * (2 * Pm))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = (2 * KH * (2 * M2) ^ ((1 / 3 : ℝ) / 2) + 72 * Pm / Real.sqrt r₀) * x := by
        field_simp
        ring

/-! ## Step 2: the energy modulus in the smoothing radius -/

/-- `ν^ρ = ν.bind fc(·,ρ)`: the circle average at radius `ρ` of the measure `ν`. -/
abbrev bindFc (ν : Measure ℂ) (ρ : ℝ) : Measure ℂ := ν.bind fun y => foldedCircle y ρ

theorem cube_rpow_third {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- A folded circle charges `closedBall p t` only if its centre is within `ρ + t` of `p` or `p̄`. -/
theorem foldedCircle_closedBall_le_indicator (y p : ℂ) {ρ t : ℝ} (hρ : 0 ≤ ρ) :
    foldedCircle y ρ (Metric.closedBall p t) ≤
      (Metric.closedBall p (ρ + t) ∪ Metric.closedBall (starRingEnd ℂ p) (ρ + t)).indicator 1 y := by
  by_cases hy : y ∈ Metric.closedBall p (ρ + t) ∪ Metric.closedBall (starRingEnd ℂ p) (ρ + t)
  · rw [Set.indicator_of_mem hy]; exact prob_le_one
  · rw [Set.indicator_of_notMem hy, foldedCircle_apply' y ρ Metric.isClosed_closedBall.measurableSet]
    have hempty : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧
        foldH (circleMap y ρ θ) ∈ Metric.closedBall p t} = ∅ := by
      ext θ
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ hθ
      rw [Metric.mem_closedBall, dist_eq_norm] at hθ
      have hc : ‖y - circleMap y ρ θ‖ = ρ := by
        rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hρ]
      apply hy
      rcases foldH_near hθ with h | h
      · left
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖y - p‖ ≤ ‖y - circleMap y ρ θ‖ + ‖circleMap y ρ θ - p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ρ + t := by rw [hc]; linarith
      · right
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖y - starRingEnd ℂ p‖ ≤ ‖y - circleMap y ρ θ‖ + ‖circleMap y ρ θ - starRingEnd ℂ p‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ ρ + t := by rw [hc]; linarith
    rw [hempty, measure_empty, mul_zero]

/-- A folded circle of radius `ρ` gives mass `≤ 6t/ρ` to a ball of radius `t`. -/
theorem foldedCircle_closedBall_le_arc (y p : ℂ) {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) :
    foldedCircle y ρ (Metric.closedBall p t) ≤ ENNReal.ofReal (6 * t / ρ) := by
  have hπ := Real.pi_pos
  rw [foldedCircle_apply' y ρ Metric.isClosed_closedBall.measurableSet]
  have hsub : {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ foldH (circleMap y ρ θ) ∈ Metric.closedBall p t} ⊆
      {θ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap y ρ θ - p‖ ≤ t} ∪
        {θ | θ ∈ Ico 0 (2 * π) ∧ ‖circleMap y ρ θ - starRingEnd ℂ p‖ ≤ t} := by
    rintro θ ⟨h1, h2⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at h2
    rcases foldH_near h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, h⟩
  have ha : (0 : ℝ) ≤ 6 * π * t / ρ := by positivity
  have hvol := (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (volume_arc_le y p hρ t) (volume_arc_le y (starRingEnd ℂ p) hρ t)))
  rw [← ENNReal.ofReal_add ha ha] at hvol
  calc (ENNReal.ofReal (2 * π))⁻¹ * volume _ ≤
        ENNReal.ofReal ((2 * π)⁻¹) * ENNReal.ofReal (6 * π * t / ρ + 6 * π * t / ρ) := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity)]
        exact mul_le_mul' le_rfl hvol
    _ = ENNReal.ofReal (6 * t / ρ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

/-- **Frostman bound for circle averages**, uniform in the radius: if `ν` is `1/3`-Frostman
with constant `C`, so is `ν^ρ` with constant `24 C`. -/
theorem isFrostman_bindFc {ν : Measure ℂ} [IsFiniteMeasure ν] {C : ℝ}
    (hF : TwoPoint.IsFrostman ν (1 / 3) C) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    TwoPoint.IsFrostman (bindFc ν ρ) (1 / 3) (24 * C) := by
  intro p t ht
  have hC : 0 ≤ C := by
    have := hF 0 1 one_pos
    rw [Real.one_rpow, mul_one] at this
    exact ENNReal.toReal_nonneg.trans this
  set U := Metric.closedBall p (ρ + t) ∪ Metric.closedBall (starRingEnd ℂ p) (ρ + t) with hUdef
  have hUm : MeasurableSet U :=
    Metric.isClosed_closedBall.measurableSet.union Metric.isClosed_closedBall.measurableSet
  have hU : (ν U).toReal ≤ 2 * C * (ρ + t) ^ (1 / 3 : ℝ) := by
    have h1 := hF p (ρ + t) (by linarith)
    have h2 := hF (starRingEnd ℂ p) (ρ + t) (by linarith)
    have hle : (ν U).toReal ≤ (ν (Metric.closedBall p (ρ + t))).toReal +
        (ν (Metric.closedBall (starRingEnd ℂ p) (ρ + t))).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      exact ENNReal.toReal_mono (by finiteness) (measure_union_le _ _)
    linarith
  have hbind : bindFc ν ρ (Metric.closedBall p t) =
      ∫⁻ y, foldedCircle y ρ (Metric.closedBall p t) ∂ν :=
    CircleFubini.bind_circle_apply ν Metric.isClosed_closedBall.measurableSet
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) ν
  set a := t ^ (1 / 3 : ℝ) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg ht.le _
  have ha3 : a ^ 3 = t := cube_rpow_third ht.le
  have hs0 : 0 ≤ (ρ + t) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hs3 : ((ρ + t) ^ (1 / 3 : ℝ)) ^ 3 = ρ + t := cube_rpow_third (by linarith)
  rcases le_or_gt ρ t with hρt | hρt
  · have h1 : bindFc ν ρ (Metric.closedBall p t) ≤ ν U := by
      rw [hbind]
      calc ∫⁻ y, foldedCircle y ρ (Metric.closedBall p t) ∂ν ≤ ∫⁻ y, U.indicator 1 y ∂ν :=
            lintegral_mono fun y => foldedCircle_closedBall_le_indicator y p hρ
        _ = ν U := lintegral_indicator_one hUm
    have h2 : (ρ + t) ^ (1 / 3 : ℝ) ≤ 2 * a :=
      le_of_pow_le_pow_left₀ three_ne_zero (by positivity) (by rw [hs3]; nlinarith)
    calc (bindFc ν ρ (Metric.closedBall p t)).toReal ≤ (ν U).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) h1
      _ ≤ 2 * C * (ρ + t) ^ (1 / 3 : ℝ) := hU
      _ ≤ 24 * C * a := by nlinarith
  · have hρ0 : 0 < ρ := ht.trans hρt
    set b := ρ ^ (1 / 3 : ℝ) with hb
    have hb0 : 0 ≤ b := Real.rpow_nonneg hρ _
    have hb3 : b ^ 3 = ρ := cube_rpow_third hρ
    have hab : a ≤ b := Real.rpow_le_rpow ht.le hρt.le (by norm_num)
    have h1 : bindFc ν ρ (Metric.closedBall p t) ≤ ENNReal.ofReal (6 * t / ρ) * ν U := by
      rw [hbind, ← lintegral_indicator_const hUm]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ U
      · rw [Set.indicator_of_mem hy]; exact foldedCircle_closedBall_le_arc y p hρ0 ht.le
      · rw [Set.indicator_of_notMem hy]
        have := foldedCircle_closedBall_le_indicator y p (t := t) hρ
        rwa [Set.indicator_of_notMem hy] at this
    have h2 : (ρ + t) ^ (1 / 3 : ℝ) ≤ 2 * b :=
      le_of_pow_le_pow_left₀ three_ne_zero (by positivity) (by rw [hs3]; nlinarith)
    have h3 : t * b ≤ a * ρ := by
      rw [← ha3, ← hb3]
      nlinarith [mul_nonneg (mul_nonneg ha0 hb0) (sub_nonneg.2 (pow_le_pow_left₀ ha0 hab 2))]
    have h4 : (bindFc ν ρ (Metric.closedBall p t)).toReal ≤ 6 * t / ρ * (ν U).toReal := by
      have := ENNReal.toReal_mono (by finiteness) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    have h5 : 6 * t / ρ * (ν U).toReal ≤ 6 * t / ρ * (2 * C * (2 * b)) :=
      mul_le_mul_of_nonneg_left (hU.trans (by nlinarith)) (by positivity)
    refine h4.trans (h5.trans ?_)
    rw [show 6 * t / ρ * (2 * C * (2 * b)) = 24 * C * (t * b) / ρ by ring, div_le_iff₀ hρ0]
    nlinarith

theorem ae_norm_bindFc_le {ν : Measure ℂ} [IsFiniteMeasure ν] {B ρ : ℝ} (hρ : 0 ≤ ρ)
    (hB : ∀ᵐ y ∂ν, ‖y‖ ≤ B) : ∀ᵐ x ∂bindFc ν ρ, ‖x‖ ≤ B + ρ := by
  rw [ae_iff, CircleFubini.bind_circle_apply ν (A := {a : ℂ | ¬‖a‖ ≤ B + ρ})
    (measurableSet_le measurable_norm measurable_const).compl]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hB] with y hy
  have := foldedCircle_ae_norm_le y hρ
  rw [ae_iff] at this
  refine measure_mono_null (fun x hx => ?_) this
  simp only [mem_setOf_eq, not_le] at hx ⊢
  linarith

theorem bindFc_real_univ {ν : Measure ℂ} [IsProbabilityMeasure ν] (ρ : ℝ) :
    (bindFc ν ρ).real univ = 1 := by
  rw [measureReal_def, CircleFubini.bind_circle_univ, measure_univ, ENNReal.toReal_one]

/-- The circle-average potential of `κ` at radius `ρ` moves by `≤ holderK·|ρ−ρ'|^{1/6}`. -/
theorem abs_kernelCov_bindFc_sub_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {B CF : ℝ}
    (hB0 : 0 ≤ B) (hCF : 0 ≤ CF) (hB : ∀ᵐ y ∂ν, ‖y‖ ≤ B) {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ')
    (hρ1 : ρ ≤ 1) (hρ1' : ρ' ≤ 1) (κ : Measure ℂ) [IsFiniteMeasure κ]
    (hFκ : TwoPoint.IsFrostman κ (1 / 3) CF) (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + 1)
    (hmκ : κ.real univ = 1) :
    |kernelCov neumannH (bindFc ν ρ) κ - kernelCov neumannH (bindFc ν ρ') κ| ≤
      holderK CF (B + 1) * |ρ - ρ'| ^ ((1 / 3 : ℝ) / 2) := by
  have hπ := Real.pi_pos
  have hB1 : 0 ≤ B + 1 := by linarith
  set Pm := potMax CF (B + 1)
  set KH := holderK CF (B + 1)
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hB1
  have hPb : ∀ x : ℂ, ‖x‖ ≤ B + 1 → |neuPot κ x| ≤ Pm := fun x hx => by
    have := abs_neuPot_le hFκ (by norm_num) hCF hB1 hBκ hx
    rwa [hmκ] at this
  have hH : ∀ x x' : ℂ, ‖x‖ ≤ B + 1 → ‖x'‖ ≤ B + 1 →
      |neuPot κ x - neuPot κ x'| ≤ KH * ‖x - x'‖ ^ ((1 / 3 : ℝ) / 2) := fun x x' hx hx' => by
    have := abs_neuPot_sub_le hFκ (by norm_num) (by norm_num) hCF hB1 hBκ hx hx'
    rwa [hmκ] at this
  have hg : Measurable (neuPot κ) := measurable_neuPot κ
  have hint : ∀ σ, 0 ≤ σ → σ ≤ 1 → Integrable (neuPot κ) (bindFc ν σ) := fun σ hσ hσ1 => by
    have := CircleFubini.isFiniteMeasure_bind_circle (r := σ) ν
    refine Integrable.of_bound hg.aestronglyMeasurable Pm ?_
    filter_upwards [ae_norm_bindFc_le hσ hB] with x hx
    rw [Real.norm_eq_abs]; exact hPb x (by linarith)
  obtain ⟨i1, e1⟩ := CircleFubini.integral_bind_circle ν (hint ρ hρ hρ1)
  obtain ⟨i2, e2⟩ := CircleFubini.integral_bind_circle ν (hint ρ' hρ' hρ1')
  show |∫ x, neuPot κ x ∂bindFc ν ρ - ∫ x, neuPot κ x ∂bindFc ν ρ'| ≤ _
  rw [e1, e2, ← integral_sub i1 i2]
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hvolI : (volume.restrict (Ico (0 : ℝ) (2 * π))).real univ = 2 * π := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  set d := KH * |ρ - ρ'| ^ ((1 / 3 : ℝ) / 2) with hd
  have hpt : ∀ y : ℂ, ‖y‖ ≤ B →
      |∫ x, neuPot κ x ∂foldedCircle y ρ - ∫ x, neuPot κ x ∂foldedCircle y ρ'| ≤ d := by
    intro y hy
    have hnb : ∀ σ, 0 ≤ σ → σ ≤ 1 → ∀ θ, ‖foldH (circleMap y σ θ)‖ ≤ B + 1 := fun σ hσ hσ1 θ =>
      (norm_foldH _).le.trans ((norm_circleMap_le_add y hσ θ).trans (by linarith))
    have hiθ : ∀ σ, 0 ≤ σ → σ ≤ 1 → Integrable (fun θ => neuPot κ (foldH (circleMap y σ θ)))
        (volume.restrict (Ico (0 : ℝ) (2 * π))) := fun σ hσ hσ1 =>
      Integrable.of_bound (hg.comp (measurable_foldH.comp (measurable_circleMap y σ))).aestronglyMeasurable
        Pm (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hPb _ (hnb σ hσ hσ1 θ))
    rw [integral_foldedCircle_eq hg, integral_foldedCircle_eq hg, ← mul_sub,
      ← integral_sub (hiθ ρ hρ hρ1) (hiθ ρ' hρ' hρ1'), abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
    have hθ : ∀ θ, |neuPot κ (foldH (circleMap y ρ θ)) - neuPot κ (foldH (circleMap y ρ' θ))| ≤ d := by
      intro θ
      refine (hH _ _ (hnb ρ hρ hρ1 θ) (hnb ρ' hρ' hρ1' θ)).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)) hKH0
      refine (norm_foldH_sub_le _ _).trans ((norm_circleMap_sub_le y y ρ ρ' θ).trans ?_)
      simp
    calc (2 * π)⁻¹ * |∫ θ in Ico 0 (2 * π), (neuPot κ (foldH (circleMap y ρ θ)) -
          neuPot κ (foldH (circleMap y ρ' θ)))|
        ≤ (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), d := by
          refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans
            (integral_mono ((hiθ ρ hρ hρ1).sub (hiθ ρ' hρ' hρ1')).abs (integrable_const d) hθ))
            (by positivity)
      _ = d := by
          rw [integral_const, hvolI, smul_eq_mul]
          field_simp
  calc |∫ y, (∫ x, neuPot κ x ∂foldedCircle y ρ - ∫ x, neuPot κ x ∂foldedCircle y ρ') ∂ν|
      ≤ ∫ y, |∫ x, neuPot κ x ∂foldedCircle y ρ - ∫ x, neuPot κ x ∂foldedCircle y ρ'| ∂ν :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _y, d ∂ν := integral_mono_ae (i1.sub i2).abs (integrable_const d)
        (hB.mono fun y hy => hpt y hy)
    _ = d := by simp

/-- **Energy modulus in the radius** (REG-CONT step 2). For a `1/3`-Frostman probability measure
`ν` supported in `closedBall 0 B` and `ρ, ρ' ∈ [0,1]`,
`|kernelCov2 neumannH (ν^ρ, ν^{ρ'}) (ν^ρ, ν^{ρ'})| ≤ 2·holderK(24 C, B+1)·|ρ − ρ'|^{1/6}`. -/
theorem abs_kernelCov2_bindFc_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {B C : ℝ}
    (hB0 : 0 ≤ B) (hC : 0 ≤ C) (hF : TwoPoint.IsFrostman ν (1 / 3) C) (hB : ∀ᵐ y ∂ν, ‖y‖ ≤ B)
    {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ') (hρ1 : ρ ≤ 1) (hρ1' : ρ' ≤ 1) :
    |kernelCov2 neumannH (bindFc ν ρ, bindFc ν ρ') (bindFc ν ρ, bindFc ν ρ')| ≤
      2 * holderK (24 * C) (B + 1) * |ρ - ρ'| ^ ((1 / 3 : ℝ) / 2) := by
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) ν
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ') ν
  have hC24 : 0 ≤ 24 * C := by positivity
  have hsupp : ∀ σ, 0 ≤ σ → σ ≤ 1 → ∀ᵐ y ∂bindFc ν σ, ‖y‖ ≤ B + 1 := fun σ hσ hσ1 =>
    (ae_norm_bindFc_le hσ hB).mono fun y hy => by linarith
  have h1 := abs_kernelCov_bindFc_sub_le hB0 hC24 hB hρ hρ' hρ1 hρ1' (bindFc ν ρ)
    (isFrostman_bindFc hF hρ) (hsupp ρ hρ hρ1) (bindFc_real_univ ρ)
  have h2 := abs_kernelCov_bindFc_sub_le hB0 hC24 hB hρ hρ' hρ1 hρ1' (bindFc ν ρ')
    (isFrostman_bindFc hF hρ') (hsupp ρ' hρ' hρ1') (bindFc_real_univ ρ')
  have e : kernelCov2 neumannH (bindFc ν ρ, bindFc ν ρ') (bindFc ν ρ, bindFc ν ρ') =
      (kernelCov neumannH (bindFc ν ρ) (bindFc ν ρ) - kernelCov neumannH (bindFc ν ρ') (bindFc ν ρ)) -
      (kernelCov neumannH (bindFc ν ρ) (bindFc ν ρ') -
        kernelCov neumannH (bindFc ν ρ') (bindFc ν ρ')) := by
    unfold kernelCov2; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

/-! ## The time modulus at a fixed smoothing radius -/

/-- The generic coupling estimate: `G` bounded by `Pm` and `1/6`-Hölder with constant `KH` on
`closedBall 0 Bf`. -/
theorem abs_integral_comp_sub_le_of_disp {G : ℂ → ℝ} (hGm : Measurable G) {F F' : ℝ → ℂ}
    (hFm : Measurable F) (hF'm : Measurable F') {Bf Pm KH Δ β : ℝ} (hPm : 0 ≤ Pm)
    (hKH : 0 ≤ KH) (hFb : ∀ θ, ‖F θ‖ ≤ Bf) (hF'b : ∀ θ, ‖F' θ‖ ≤ Bf)
    (hGb : ∀ x : ℂ, ‖x‖ ≤ Bf → |G x| ≤ Pm)
    (hGH : ∀ x x' : ℂ, ‖x‖ ≤ Bf → ‖x'‖ ≤ Bf → |G x - G x'| ≤ KH * ‖x - x'‖ ^ ((1 / 3 : ℝ) / 2))
    {Bad : Set ℝ} (hBadm : MeasurableSet Bad)
    (hvolB : (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad ≤ β)
    (hdisp : ∀ θ, θ ∉ Bad → ‖F θ - F' θ‖ ≤ Δ) (hΔ : 0 ≤ Δ) :
    |∫ θ in Ico 0 (2 * π), (G (F θ) - G (F' θ))| ≤
      2 * π * (KH * Δ ^ ((1 / 3 : ℝ) / 2)) + β * (2 * Pm) := by
  have hπ := Real.pi_pos
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hi : ∀ H : ℝ → ℂ, Measurable H → (∀ θ, ‖H θ‖ ≤ Bf) →
      Integrable (fun θ => G (H θ)) (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    fun H hH hHb => Integrable.of_bound (hGm.comp hH).aestronglyMeasurable Pm
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hGb _ (hHb θ))
  set D := KH * Δ ^ ((1 / 3 : ℝ) / 2) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hpt : ∀ θ, |G (F θ) - G (F' θ)| ≤ D + Bad.indicator (fun _ => 2 * Pm) θ := by
    intro θ
    by_cases hθ : θ ∈ Bad
    · rw [Set.indicator_of_mem hθ]
      have a1 := abs_le.1 (hGb _ (hFb θ))
      have a2 := abs_le.1 (hGb _ (hF'b θ))
      rw [abs_le]; constructor <;> linarith
    · rw [Set.indicator_of_notMem hθ, add_zero]
      refine (hGH _ _ (hFb θ) (hF'b θ)).trans ?_
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hdisp θ hθ) (by norm_num)) hKH
  have hint := (hi F hFm hFb).sub (hi F' hF'm hF'b)
  have hrhs : Integrable (fun θ => D + Bad.indicator (fun _ => 2 * Pm) θ)
      (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    (integrable_const D).add ((integrable_const (2 * Pm)).indicator hBadm)
  have hvolI : (volume.restrict (Ico (0 : ℝ) (2 * π))).real univ = 2 * π := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  calc |∫ θ in Ico 0 (2 * π), (G (F θ) - G (F' θ))|
      ≤ ∫ θ in Ico 0 (2 * π), |G (F θ) - G (F' θ)| := abs_integral_le_integral_abs
    _ ≤ ∫ θ in Ico 0 (2 * π), (D + Bad.indicator (fun _ => 2 * Pm) θ) :=
        integral_mono hint.abs hrhs hpt
    _ = 2 * π * D + (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad * (2 * Pm) := by
        rw [integral_add (integrable_const D) ((integrable_const (2 * Pm)).indicator hBadm),
          integral_const, integral_indicator_const _ hBadm, hvolI, smul_eq_mul, smul_eq_mul]
    _ ≤ 2 * π * D + β * (2 * Pm) := by
        have := mul_le_mul_of_nonneg_right hvolB (by positivity : (0 : ℝ) ≤ 2 * Pm)
        linarith

/-- **Time modulus for a general test function.** For `G` measurable, bounded by `Pm` and
`1/6`-Hölder with constant `KH` on `closedBall 0 (revBound (2M) T R)`,
`|∫ G dν_s − ∫ G dν_{s+h}| ≤ (KH·(2√(R²+8T))^{1/6} + 36·Pm/√r₀)·(ε + h)^{1/12}`. -/
theorem abs_integral_νT_time_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {w : ℂ} {r : ℝ} (hr : r₀ ≤ r)
    (hwR : ‖w‖ + r ≤ R) {s h ε : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) (hsh : s + h ≤ T)
    (hε : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) (hδ1 : ε + h ≤ 1)
    {G : ℂ → ℝ} (hGm : Measurable G) {Pm KH : ℝ} (hPm : 0 ≤ Pm) (hKH : 0 ≤ KH)
    (hGb : ∀ x : ℂ, ‖x‖ ≤ revBound (2 * M) T R → |G x| ≤ Pm)
    (hGH : ∀ x x' : ℂ, ‖x‖ ≤ revBound (2 * M) T R → ‖x'‖ ≤ revBound (2 * M) T R →
      |G x - G x'| ≤ KH * ‖x - x'‖ ^ ((1 / 3 : ℝ) / 2)) :
    |∫ x, G x ∂νT W w r s - ∫ x, G x ∂νT W w r (s + h)| ≤
      (KH * (2 * Real.sqrt (R ^ 2 + 8 * T)) ^ ((1 / 3 : ℝ) / 2) + 36 * Pm / Real.sqrt r₀) *
        (ε + h) ^ (1 / 12 : ℝ) := by
  have hπ := Real.pi_pos
  have hr0 : 0 < r := hr₀.trans_le hr
  have hT : 0 ≤ T := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hε0 : 0 ≤ ε := by simpa using hε 0 ⟨le_rfl, hh⟩
  rcases eq_or_lt_of_le (show 0 ≤ ε + h by linarith) with hδ0 | hδ
  · have hh0 : h = 0 := by linarith
    subst hh0
    rw [add_zero, sub_self, abs_zero, ← hδ0, Real.zero_rpow (by norm_num), mul_zero]
  have hsh0 : 0 ≤ s + h := by linarith
  rw [νT_eq_pfc hW hW0 hs w hr0, νT_eq_pfc hW hW0 hsh0 w hr0]
  set V : ℝ → ℝ := fun q => W (s - q) - W s with hVdef
  set V' : ℝ → ℝ := fun q => W (s + h - q) - W (s + h) with hV'def
  have hVc : Continuous V := by fun_prop
  have hV'c : Continuous V' := by fun_prop
  have hVb : ∀ q ∈ Icc (0 : ℝ) s, |V q| ≤ 2 * M := fun q hq => by
    have h1 := abs_le.1 (hM (s - q) ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have h2 := abs_le.1 (hM s ⟨hs, by linarith⟩)
    rw [abs_le]; constructor <;> linarith
  have hV'b : ∀ q ∈ Icc (0 : ℝ) (s + h), |V' q| ≤ 2 * M := fun q hq => by
    have h1 := abs_le.1 (hM (s + h - q) ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have h2 := abs_le.1 (hM (s + h) ⟨hsh0, hsh⟩)
    rw [abs_le]; constructor <;> linarith
  set Bf := revBound (2 * M) T R with hBfdef
  have hBfV : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap V s z‖ ≤ Bf := fun z hz =>
    (norm_revMap_le_revBound hVc hs hVb R hz).trans (revBound_mono (by linarith))
  have hBfV' : ∀ z : ℂ, ‖z‖ ≤ R → ‖revMap V' (s + h) z‖ ≤ Bf := fun z hz =>
    (norm_revMap_le_revBound hV'c hsh0 hV'b R hz).trans (revBound_mono hsh)
  set M2 := Real.sqrt (R ^ 2 + 8 * T) with hM2
  have hM20 : 0 ≤ M2 := Real.sqrt_nonneg _
  set δ := ε + h with hδdef
  set τ := δ ^ (1 / 4 : ℝ) with hτdef
  have hτ : 0 < τ := Real.rpow_pos_of_pos hδ _
  have hτ1 : τ ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hττ : τ * τ = δ ^ (1 / 2 : ℝ) := by
    rw [hτdef, ← Real.rpow_add hδ]; norm_num
  have hδsq : δ ^ (1 / 2 : ℝ) * δ ^ (1 / 2 : ℝ) = δ := by
    rw [← Real.rpow_add hδ]; norm_num
  set Bad : Set ℝ := {θ | |(circleMap w r θ).im| < τ} with hBad
  have hBadm : MeasurableSet Bad :=
    (isOpen_lt (continuous_abs.comp (Complex.continuous_im.comp (continuous_circleMap w r)))
      continuous_const).measurableSet
  have hvolB : (volume.restrict (Ico (0 : ℝ) (2 * π))).real Bad ≤
      36 * π * Real.sqrt (τ / r₀) := by
    rw [measureReal_def, Measure.restrict_apply hBadm]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hsub : Bad ∩ Ico 0 (2 * π) ⊆
        {θ : ℝ | θ ∈ Ico 0 (2 * π) ∧ |(circleMap w r θ).im| < τ} := fun θ hθ => ⟨hθ.2, hθ.1⟩
    refine (measure_mono hsub).trans ((volume_strip_le w hr0 hτ).trans
      (ENNReal.ofReal_le_ofReal ?_))
    have : Real.sqrt (τ / r) ≤ Real.sqrt (τ / r₀) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hτ.le hr₀ hr)
    nlinarith
  have hFm : ∀ (U : ℝ → ℝ) (t : ℝ), Continuous U → 0 ≤ t →
      Measurable fun θ => revMap U t (foldH (circleMap w r θ)) := fun U t hU ht =>
    (measurable_revMap hU ht).comp (measurable_foldH.comp (measurable_circleMap w r))
  have hnormu : ∀ θ, ‖foldH (circleMap w r θ)‖ ≤ R := fun θ =>
    (norm_foldH _).le.trans ((norm_circleMap_le_add w hr0.le θ).trans hwR)
  have hdisp : ∀ θ, θ ∉ Bad → ‖revMap V s (foldH (circleMap w r θ)) -
      revMap V' (s + h) (foldH (circleMap w r θ))‖ ≤ 2 * M2 * δ ^ (1 / 2 : ℝ) := by
    intro θ hθ
    simp only [hBad, mem_setOf_eq, not_lt] at hθ
    set u := foldH (circleMap w r θ) with hu_def
    have hu : τ ≤ u.im := by rw [hu_def, im_foldH]; exact hθ
    have hu0 : u ∈ H := show 0 < u.im by linarith
    have hunorm : ‖u‖ ≤ R := hnormu θ
    set v := revMap V' h u with hv_def
    have hflow : revMap V' (s + h) u = revMap V s v := by
      have h1 := fwdMapInv_add hW hW0 hs hh hu0
      have h2 := fwdMapInv_eq_revMap_timeRev W hW hW0 hsh0 hu0
      have h3 := fwdMapInv_eq_revMap_timeRev W hW hW0 hs (im_revMap_pos hV'c hu0 hh)
      exact h2.symm.trans (h1.trans h3)
    have hvτ : τ ≤ v.im := hu.trans (im_le_im_revMap V' hV'c u hu0 hh)
    have huR0 : u.im ≤ R := (Complex.im_le_norm u).trans hunorm
    have hR2 : R ^ 2 ≤ R ^ 2 + 4 * T := by linarith
    have huR : u.im ≤ Real.sqrt (R ^ 2 + 4 * T) :=
      (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))
    have hvR : v.im ≤ Real.sqrt (R ^ 2 + 4 * T) := by
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      have h1 := im_revMap_sq_le hV'c hu0 hh
      have h2 : u.im ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hu0.le huR0 2
      linarith
    have key := norm_revMap_sub_mul_le_upper hVc hs hτ hu hvτ huR hvR
    have hsqrt : Real.sqrt (Real.sqrt (R ^ 2 + 4 * T) ^ 2 + 4 * s) ≤ M2 := by
      rw [Real.sq_sqrt (by positivity)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hnear := norm_revMap_sub_self_le hV'c hu0 hh hε
    have huv : ‖u - v‖ ≤ 2 * δ / τ := by
      rw [norm_sub_rev, le_div_iff₀ hτ]
      have e1 : 2 * h / u.im * τ ≤ 2 * h := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        exact mul_le_mul_of_nonneg_left hu (by linarith)
      have e2 : ε * τ ≤ ε := by
        have := mul_le_mul_of_nonneg_left hτ1 hε0
        linarith
      have e3 := mul_le_mul_of_nonneg_right hnear hτ.le
      have e4 : (ε + 2 * h / u.im) * τ = ε * τ + 2 * h / u.im * τ := by ring
      rw [hδdef]; linarith
    have hA : ‖revMap V s u - revMap V' (s + h) u‖ * τ ≤ 2 * δ / τ * M2 := by
      rw [hflow]
      exact key.trans (mul_le_mul huv hsqrt (Real.sqrt_nonneg _) (by positivity))
    have hB : ‖revMap V s u - revMap V' (s + h) u‖ * (τ * τ) ≤
        2 * M2 * δ ^ (1 / 2 : ℝ) * (τ * τ) := by
      have e : 2 * δ / τ * M2 * τ = 2 * δ * M2 := by
        rw [mul_right_comm, div_mul_cancel₀ _ hτ.ne']
      have h' := mul_le_mul_of_nonneg_right hA hτ.le
      calc ‖revMap V s u - revMap V' (s + h) u‖ * (τ * τ)
          = ‖revMap V s u - revMap V' (s + h) u‖ * τ * τ := by ring
        _ ≤ 2 * δ / τ * M2 * τ := h'
        _ = 2 * M2 * (δ ^ (1 / 2 : ℝ) * δ ^ (1 / 2 : ℝ)) := by rw [e, hδsq]; ring
        _ = 2 * M2 * δ ^ (1 / 2 : ℝ) * (τ * τ) := by rw [hττ]; ring
    exact le_of_mul_le_mul_right hB (mul_pos hτ hτ)
  have hΔ0 : 0 ≤ 2 * M2 * δ ^ (1 / 2 : ℝ) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hδ.le _)
  have hFb : ∀ θ, ‖revMap V s (foldH (circleMap w r θ))‖ ≤ Bf := fun θ => hBfV _ (hnormu θ)
  have hF'b : ∀ θ, ‖revMap V' (s + h) (foldH (circleMap w r θ))‖ ≤ Bf := fun θ =>
    hBfV' _ (hnormu θ)
  have hC := abs_integral_comp_sub_le_of_disp hGm (hFm V s hVc hs) (hFm V' (s + h) hV'c hsh0)
    hPm hKH hFb hF'b hGb hGH hBadm hvolB hdisp hΔ0
  -- the two integrals as parameter integrals
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hpar : ∀ (U : ℝ → ℝ) (t : ℝ), Continuous U → 0 ≤ t →
      ∫ x, G x ∂pfc U t w r =
        (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), G (revMap U t (foldH (circleMap w r θ))) :=
    fun U t hU ht => by
      rw [pfc, integral_map (measurable_revMap hU ht).aemeasurable hGm.aestronglyMeasurable]
      exact integral_foldedCircle_eq (hGm.comp (measurable_revMap hU ht)) w r
  have hiθ : ∀ (U : ℝ → ℝ) (t : ℝ), Continuous U → 0 ≤ t →
      (∀ θ, ‖revMap U t (foldH (circleMap w r θ))‖ ≤ Bf) →
      Integrable (fun θ => G (revMap U t (foldH (circleMap w r θ))))
        (volume.restrict (Ico (0 : ℝ) (2 * π))) := fun U t hU ht hb =>
    Integrable.of_bound (hGm.comp (hFm U t hU ht)).aestronglyMeasurable Pm
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hGb _ (hb θ))
  rw [hpar V s hVc hs, hpar V' (s + h) hV'c hsh0, ← mul_sub,
    ← integral_sub (hiθ V s hVc hs hFb) (hiθ V' (s + h) hV'c hsh0 hF'b), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have hpow1 : (2 * M2 * δ ^ (1 / 2 : ℝ)) ^ ((1 / 3 : ℝ) / 2) =
      (2 * M2) ^ ((1 / 3 : ℝ) / 2) * δ ^ (1 / 12 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hδ.le _), ← Real.rpow_mul hδ.le,
      show (1 / 2 : ℝ) * ((1 / 3 : ℝ) / 2) = 1 / 12 by norm_num]
  have hsr : 0 < Real.sqrt r₀ := Real.sqrt_pos.2 hr₀
  have hpow2 : Real.sqrt (τ / r₀) ≤ δ ^ (1 / 12 : ℝ) / Real.sqrt r₀ := by
    rw [Real.sqrt_div hτ.le, Real.sqrt_eq_rpow τ, hτdef, ← Real.rpow_mul hδ.le]
    refine div_le_div_of_nonneg_right ?_ hsr.le
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num)
  rw [hpow1] at hC
  set x := δ ^ (1 / 12 : ℝ) with hx
  have h3 : 36 * π * Real.sqrt (τ / r₀) * (2 * Pm) ≤ 36 * π * (x / Real.sqrt r₀) * (2 * Pm) := by
    gcongr
  have hπne : π ≠ 0 := hπ.ne'
  have hsrne : Real.sqrt r₀ ≠ 0 := hsr.ne'
  calc (2 * π)⁻¹ * |_| ≤ (2 * π)⁻¹ *
        (2 * π * (KH * ((2 * M2) ^ ((1 / 3 : ℝ) / 2) * x)) +
          36 * π * (x / Real.sqrt r₀) * (2 * Pm)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = (KH * (2 * M2) ^ ((1 / 3 : ℝ) / 2) + 36 * Pm / Real.sqrt r₀) * x := by
        field_simp

/-- The circle-average potential `y ↦ ∫ neuPot κ d fc(y,ρ)`. -/
def fcPot (κ : Measure ℂ) (ρ : ℝ) (y : ℂ) : ℝ := ∫ x, neuPot κ x ∂foldedCircle y ρ

theorem measurable_fcPot (κ : Measure ℂ) [IsFiniteMeasure κ] (ρ : ℝ) :
    Measurable (fcPot κ ρ) :=
  ((measurable_neuPot κ).stronglyMeasurable.integral_kernel
    (κ := CircleFubini.circleKernel ρ)).measurable

section FcPot

variable {κ : Measure ℂ} [IsFiniteMeasure κ] {CF B : ℝ}

theorem abs_fcPot_le (hCF : 0 ≤ CF) (hB0 : 0 ≤ B) (hFκ : TwoPoint.IsFrostman κ (1 / 3) CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + 1) (hmκ : κ.real univ = 1) {y : ℂ} {ρ : ℝ} (hy : ‖y‖ ≤ B)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : |fcPot κ ρ y| ≤ potMax CF (B + 1) := by
  have hB1 : 0 ≤ B + 1 := by linarith
  unfold fcPot
  refine (abs_integral_le_integral_abs).trans ?_
  have : ∫ _x, potMax CF (B + 1) ∂foldedCircle y ρ = potMax CF (B + 1) := by simp
  rw [← this]
  refine integral_mono_ae ?_ (integrable_const _) ?_
  · refine Integrable.of_bound (continuous_abs.measurable.comp (measurable_neuPot κ)).aestronglyMeasurable
      (potMax CF (B + 1)) ?_
    filter_upwards [foldedCircle_ae_norm_le y hρ] with x hx
    rw [Real.norm_eq_abs, abs_abs]
    have := abs_neuPot_le hFκ (by norm_num) hCF hB1 hBκ (x := x) (X := B + 1) (by linarith)
    rwa [hmκ] at this
  · filter_upwards [foldedCircle_ae_norm_le y hρ] with x hx
    have := abs_neuPot_le hFκ (by norm_num) hCF hB1 hBκ (x := x) (X := B + 1) (by linarith)
    rwa [hmκ] at this

theorem abs_fcPot_sub_le (hCF : 0 ≤ CF) (hB0 : 0 ≤ B) (hFκ : TwoPoint.IsFrostman κ (1 / 3) CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + 1) (hmκ : κ.real univ = 1) {y y' : ℂ} {ρ ρ' : ℝ}
    (hy : ‖y‖ ≤ B) (hy' : ‖y'‖ ≤ B) (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ') (hρ1 : ρ ≤ 1) (hρ1' : ρ' ≤ 1) :
    |fcPot κ ρ y - fcPot κ ρ' y'| ≤
      holderK CF (B + 1) * (‖y - y'‖ + |ρ - ρ'|) ^ ((1 / 3 : ℝ) / 2) := by
  have hπ := Real.pi_pos
  have hB1 : 0 ≤ B + 1 := by linarith
  set Pm := potMax CF (B + 1)
  set KH := holderK CF (B + 1)
  have hKH0 : 0 ≤ KH := holderK_nonneg hCF hB1
  have hPb : ∀ x : ℂ, ‖x‖ ≤ B + 1 → |neuPot κ x| ≤ Pm := fun x hx => by
    have := abs_neuPot_le hFκ (by norm_num) hCF hB1 hBκ hx
    rwa [hmκ] at this
  have hH : ∀ x x' : ℂ, ‖x‖ ≤ B + 1 → ‖x'‖ ≤ B + 1 →
      |neuPot κ x - neuPot κ x'| ≤ KH * ‖x - x'‖ ^ ((1 / 3 : ℝ) / 2) := fun x x' hx hx' => by
    have := abs_neuPot_sub_le hFκ (by norm_num) (by norm_num) hCF hB1 hBκ hx hx'
    rwa [hmκ] at this
  have hg : Measurable (neuPot κ) := measurable_neuPot κ
  have : IsFiniteMeasure (volume.restrict (Ico (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ico_lt_top.ne
  have hvolI : (volume.restrict (Ico (0 : ℝ) (2 * π))).real univ = 2 * π := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ico, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  set d := KH * (‖y - y'‖ + |ρ - ρ'|) ^ ((1 / 3 : ℝ) / 2) with hd
  have hnb : ∀ z : ℂ, ‖z‖ ≤ B → ∀ σ, 0 ≤ σ → σ ≤ 1 → ∀ θ,
      ‖foldH (circleMap z σ θ)‖ ≤ B + 1 := fun z hz σ hσ hσ1 θ =>
    (norm_foldH _).le.trans ((norm_circleMap_le_add z hσ θ).trans (by linarith))
  have hiθ : ∀ z : ℂ, ‖z‖ ≤ B → ∀ σ, 0 ≤ σ → σ ≤ 1 →
      Integrable (fun θ => neuPot κ (foldH (circleMap z σ θ)))
        (volume.restrict (Ico (0 : ℝ) (2 * π))) := fun z hz σ hσ hσ1 =>
    Integrable.of_bound (hg.comp (measurable_foldH.comp (measurable_circleMap z σ))).aestronglyMeasurable
      Pm (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact hPb _ (hnb z hz σ hσ hσ1 θ))
  unfold fcPot
  rw [integral_foldedCircle_eq hg, integral_foldedCircle_eq hg, ← mul_sub,
    ← integral_sub (hiθ y hy ρ hρ hρ1) (hiθ y' hy' ρ' hρ' hρ1'), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  have hθ : ∀ θ, |neuPot κ (foldH (circleMap y ρ θ)) - neuPot κ (foldH (circleMap y' ρ' θ))| ≤ d := by
    intro θ
    refine (hH _ _ (hnb y hy ρ hρ hρ1 θ) (hnb y' hy' ρ' hρ' hρ1' θ)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)) hKH0
    exact (norm_foldH_sub_le _ _).trans (norm_circleMap_sub_le y y' ρ ρ' θ)
  calc (2 * π)⁻¹ * |∫ θ in Ico 0 (2 * π), (neuPot κ (foldH (circleMap y ρ θ)) -
        neuPot κ (foldH (circleMap y' ρ' θ)))|
      ≤ (2 * π)⁻¹ * ∫ θ in Ico 0 (2 * π), d := by
        refine mul_le_mul_of_nonneg_left ((abs_integral_le_integral_abs).trans
          (integral_mono ((hiθ y hy ρ hρ hρ1).sub (hiθ y' hy' ρ' hρ' hρ1')).abs
            (integrable_const d) hθ)) (by positivity)
    _ = d := by
        rw [integral_const, hvolI, smul_eq_mul]
        field_simp

end FcPot

/-- `kernelCov neumannH (μ^ρ) κ = ∫ fcPot κ ρ dμ`. -/
theorem kernelCov_bindFc_eq {μ : Measure ℂ} [IsFiniteMeasure μ] {B CF : ℝ} (hB0 : 0 ≤ B)
    (hCF : 0 ≤ CF) (hBμ : ∀ᵐ y ∂μ, ‖y‖ ≤ B) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (κ : Measure ℂ) [IsFiniteMeasure κ] (hFκ : TwoPoint.IsFrostman κ (1 / 3) CF)
    (hBκ : ∀ᵐ y ∂κ, ‖y‖ ≤ B + 1) (hmκ : κ.real univ = 1) :
    kernelCov neumannH (bindFc μ ρ) κ = ∫ y, fcPot κ ρ y ∂μ := by
  have hB1 : 0 ≤ B + 1 := by linarith
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) μ
  have hint : Integrable (neuPot κ) (bindFc μ ρ) := by
    refine Integrable.of_bound (measurable_neuPot κ).aestronglyMeasurable (potMax CF (B + 1)) ?_
    filter_upwards [ae_norm_bindFc_le hρ hBμ] with x hx
    rw [Real.norm_eq_abs]
    have := abs_neuPot_le hFκ (by norm_num) hCF hB1 hBκ (x := x) (X := B + 1) (by linarith)
    rwa [hmκ] at this
  exact (CircleFubini.integral_bind_circle μ hint).2

/-- The constant of the time modulus at a fixed radius. -/
def timeConstRad (M T r₀ R : ℝ) : ℝ :=
  2 * (holderK (24 * frostC T r₀ R) (revBound (2 * M) T R + 1) *
      (2 * Real.sqrt (R ^ 2 + 8 * T)) ^ ((1 / 3 : ℝ) / 2) +
    36 * potMax (24 * frostC T r₀ R) (revBound (2 * M) T R + 1) / Real.sqrt r₀)

/-- **Energy modulus in time at a fixed radius** `ρ ∈ [0,1]` (the time direction of the
two-parameter family `(s, ρ) ↦ ν_s^ρ`). -/
theorem abs_kernelCov2_bindFc_time_le (hW : Continuous W) (hW0 : W 0 = 0) {T M r₀ R : ℝ}
    (hr₀ : 0 < r₀) (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ M) {w : ℂ} {r : ℝ} (hr : r₀ ≤ r)
    (hwR : ‖w‖ + r ≤ R) {s h ε : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) (hsh : s + h ≤ T)
    (hε : ∀ q ∈ Icc (0 : ℝ) h, |W (s + h - q) - W (s + h)| ≤ ε) (hδ1 : ε + h ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    |kernelCov2 neumannH (bindFc (νT W w r s) ρ, bindFc (νT W w r (s + h)) ρ)
        (bindFc (νT W w r s) ρ, bindFc (νT W w r (s + h)) ρ)| ≤
      timeConstRad M T r₀ R * (ε + h) ^ (1 / 12 : ℝ) := by
  have hr0 : 0 < r := hr₀.trans_le hr
  have hT : 0 ≤ T := by linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hR0 : 0 ≤ R := by linarith [norm_nonneg w]
  set Bf := revBound (2 * M) T R with hBfdef
  have hBf0 : 0 ≤ Bf := revBound_nonneg (by linarith) hT
  set CF := frostC T r₀ R with hCFdef
  have hCF : 0 ≤ CF := by rw [hCFdef]; unfold frostC; positivity
  have hCF24 : 0 ≤ 24 * CF := by positivity
  -- facts about `ν_t` for `t ∈ [0,T]`
  have hfacts : ∀ t, 0 ≤ t → t ≤ T → IsProbabilityMeasure (νT W w r t) ∧
      TwoPoint.IsFrostman (νT W w r t) (1 / 3) CF ∧ (∀ᵐ y ∂νT W w r t, ‖y‖ ≤ Bf) := by
    intro t ht htT
    have hVc : Continuous fun q => W (t - q) - W t := by fun_prop
    have hVb : ∀ q ∈ Icc (0 : ℝ) t, |W (t - q) - W t| ≤ 2 * M := fun q hq => by
      have h1 := abs_le.1 (hM (t - q) ⟨by linarith [hq.2], by linarith [hq.1]⟩)
      have h2 := abs_le.1 (hM t ⟨ht, htT⟩)
      rw [abs_le]; constructor <;> linarith
    rw [νT_eq_pfc hW hW0 ht w hr0]
    refine ⟨(Measure.isProbabilityMeasure_map_iff (measurable_revMap hVc ht).aemeasurable).2 inferInstance,
      isFrostman_pfc_frostC hVc ht htT hr₀ hr hwR, pfc_ae_norm_le hVc ht hr0.le hwR ?_⟩
    exact fun z hz => (norm_revMap_le_revBound hVc ht hVb R hz).trans (revBound_mono htT)
  obtain ⟨hP1, hF1, hB1⟩ := hfacts s hs (by linarith)
  obtain ⟨hP2, hF2, hB2⟩ := hfacts (s + h) (by linarith) hsh
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) (νT W w r s)
  have := CircleFubini.isFiniteMeasure_bind_circle (r := ρ) (νT W w r (s + h))
  set a := bindFc (νT W w r s) ρ with ha
  set b := bindFc (νT W w r (s + h)) ρ with hb
  have hsupp : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ], (∀ᵐ y ∂μ, ‖y‖ ≤ Bf) →
      ∀ᵐ y ∂bindFc μ ρ, ‖y‖ ≤ Bf + 1 := fun μ _ hμ =>
    (ae_norm_bindFc_le hρ hμ).mono fun y hy => by linarith
  -- the time estimate for `κ ∈ {a, b}`
  have hD : ∀ (κ : Measure ℂ) [IsFiniteMeasure κ], TwoPoint.IsFrostman κ (1 / 3) (24 * CF) →
      (∀ᵐ y ∂κ, ‖y‖ ≤ Bf + 1) → κ.real univ = 1 →
      |kernelCov neumannH a κ - kernelCov neumannH b κ| ≤ timeConstRad M T r₀ R / 2 *
        (ε + h) ^ (1 / 12 : ℝ) := by
    intro κ _ hFκ hBκ hmκ
    rw [ha, hb, kernelCov_bindFc_eq hBf0 hCF24 hB1 hρ hρ1 κ hFκ hBκ hmκ,
      kernelCov_bindFc_eq hBf0 hCF24 hB2 hρ hρ1 κ hFκ hBκ hmκ]
    have hPm := potMax_nonneg hCF24 (by linarith : 0 ≤ Bf + 1)
    have hKH := holderK_nonneg hCF24 (by linarith : 0 ≤ Bf + 1)
    have key := abs_integral_νT_time_sub_le hW hW0 hr₀ hM hr hwR hs hh hsh hε hδ1
      (measurable_fcPot κ ρ) hPm hKH
      (fun x hx => abs_fcPot_le hCF24 hBf0 hFκ hBκ hmκ hx hρ hρ1)
      (fun x x' hx hx' => by
        have := abs_fcPot_sub_le hCF24 hBf0 hFκ hBκ hmκ hx hx' hρ hρ hρ1 hρ1
        rwa [sub_self, abs_zero, add_zero] at this)
    refine key.trans (le_of_eq ?_)
    unfold timeConstRad
    ring
  have h1 := hD a (isFrostman_bindFc hF1 hρ) (hsupp _ hB1) (bindFc_real_univ ρ)
  have h2 := hD b (isFrostman_bindFc hF2 hρ) (hsupp _ hB2) (bindFc_real_univ ρ)
  have e : kernelCov2 neumannH (a, b) (a, b) =
      (kernelCov neumannH a a - kernelCov neumannH b a) -
      (kernelCov neumannH a b - kernelCov neumannH b b) := by
    unfold kernelCov2; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

end RegCont
end QuantumZipper
