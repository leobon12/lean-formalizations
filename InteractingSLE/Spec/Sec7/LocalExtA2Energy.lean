/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Pair
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# The local comparison of Aux. lemma 55: the tested mean and the energy of the source in the local regime

Packet PROVE-LOCEXT-A2, steps 3–4 (deterministic part). Source: Aux. lemma 55, proof (`source/spec/p241-288.md`
L163–L180, p. 248): "`E[Z | 𝓕_t] = exp(−(M_t − m, v) − ½{‖f‖²_∇ − G_{ℍ∖K_t}(v, v)})` … The Loewner Green identity gives
`∫₀^{t∧S} a_s² ds = ‖f‖²_∇ − G_{ℍ∖K_{t∧S}}(v, v)`."

For a driver `W` in the local regime up to `T` (`IsLocalRegime`) and `s ∈ [0, T]`:

* `abs_couplingMean_src_le`: the coupling mean `𝔥_s(z)` is bounded on the source, uniformly in `s`;
* `tendsto_integral_couplingMean_mul_vApprox`: `∫ 𝔥_s v_n → ∫ 𝔥_s v` (the tested means of the approximations);
* `greenH_fwdMap_mem_Icc_src`: `0 ≤ G(f_s y, f_s z) ≤ G_ℍ(y, z)` on the source;
* `tendsto_loewnerGreenEnergy_vApprox`: `E_s(v_n) → E_s(v)` (the Loewner Green energies of the approximations);
* **`loewnerGreenEnergy_vSrc_eq`** (the Loewner Green identity of (HL4)):
  `E_s(v) = G_{ℍ∖K_s}(v, v) = ‖f‖²_∇ − ∫₀ˢ A(u)² du`, with `‖f‖²_∇ = srcNorm = ∫ v f` (Green inversion) and
  `A = srcDrift`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H Hbar fwdMap fwdHull greenH logDerivFwd chiC)

section Energy

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {W : ℝ → ℝ} {T : ℝ}

/-! ### The mean on the source -/

/-- `|2/f_u(z)²| ≤ 32/(121 r²)` on the source. -/
theorem norm_two_div_fwdMap_sq_src_le (h : IsLocalRegime W r T) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖)
    {u : ℝ} (hu : u ∈ Icc 0 T) : ‖2 / fwdMap W u z ^ 2‖ ≤ 32 / (121 * r ^ 2) := by
  have hn := h.le_norm_fwdMap_src hz hz6 hu
  have hr := h.r_pos
  have hpos : 0 < ‖fwdMap W u z‖ := lt_of_lt_of_le (by positivity) hn
  rw [norm_div, norm_pow, Complex.norm_two, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `|log f_s'(z)| ≤ 32 T/(121 r²)` on the source. -/
theorem norm_logDerivFwd_src_le (h : IsLocalRegime W r T) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖)
    {s : ℝ} (hs : s ∈ Icc 0 T) : ‖logDerivFwd W s z‖ ≤ 32 / (121 * r ^ 2) * T := by
  rw [QuantumZipper.logDerivFwd, norm_neg]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
    (C := 32 / (121 * r ^ 2)) (f := fun u => 2 / fwdMap W u z ^ 2) fun u hu => by
      rw [uIoc_of_le hs.1] at hu
      exact norm_two_div_fwdMap_sq_src_le h hz hz6 ⟨hu.1.le, hu.2.trans hs.2⟩
  rw [sub_zero, abs_of_nonneg hs.1] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hs.2 (by have := h.r_pos; positivity))

/-- **The coupling mean is bounded on the source**, uniformly in `s ∈ [0, T]`. -/
theorem abs_couplingMean_src_le (h : IsLocalRegime W r T) {u : ℂ → ℝ} {C : ℝ} (hC : ∀ w ∈ H, |u w| ≤ C)
    {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖) {s : ℝ} (hs : s ∈ Icc 0 T) :
    |couplingMean κ W s u z| ≤ C + |chiC κ| * (32 / (121 * r ^ 2) * T) := by
  have halive := (h.mono hs).mem_of_lt_norm hz (by linarith [h.r_pos])
  have hfH : fwdMap W s z ∈ H := Ito.im_fwdMap_pos h.cont hs.1 halive ⟨hs.1, le_rfl⟩
  rw [couplingMean]
  refine (abs_sub _ _).trans (add_le_add (hC _ hfH) ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (norm_logDerivFwd_src_le h hz hz6 hs))
    (abs_nonneg _)

theorem srcSet_subset (h : IsLocalRegime W r T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    srcSet r ⊆ H \ fwdHull W s := fun _ hz => (h.mono hs).mem_of_lt_norm hz.1 hz.2

theorem continuousOn_couplingMean_srcSet (h : IsLocalRegime W r T) {u : ℂ → ℝ} (hu : ContinuousOn u H) {s : ℝ}
    (hs : s ∈ Icc 0 T) : ContinuousOn (couplingMean κ W s u) (srcSet r) := by
  have hsub := srcSet_subset h hs
  have h1 : ContinuousOn (fwdMap W s) (srcSet r) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap h.cont hs.1).continuousOn.mono hsub
  have h2 : ContinuousOn (fun z => u (fwdMap W s z)) (srcSet r) :=
    hu.comp h1 fun z hz => Ito.im_fwdMap_pos h.cont hs.1 (hsub hz) ⟨hs.1, le_rfl⟩
  have h3 : ContinuousOn (fun z => (logDerivFwd W s z).im) (srcSet r) := fun z hz =>
    (Complex.continuous_im.continuousAt.comp
      (continuousAt_logDerivFwd h.cont hs.1 (hsub hz))).continuousWithinAt
  exact h2.sub (continuousOn_const.mul h3)

open Classical in
/-- `𝔥_s φ` is measurable when `φ` is measurable and vanishes off the source set. -/
theorem measurable_couplingMean_mul (h : IsLocalRegime W r T) {u : ℂ → ℝ} (hu : ContinuousOn u H) {s : ℝ}
    (hs : s ∈ Icc 0 T) {φ : ℂ → ℝ} (hφm : Measurable φ) (hφ : ∀ z, φ z ≠ 0 → z ∈ srcSet r) :
    Measurable fun z => couplingMean κ W s u z * φ z := by
  have hg : Measurable ((srcSet r).piecewise (couplingMean κ W s u) fun _ => 0) :=
    (continuousOn_couplingMean_srcSet h hu hs).measurable_piecewise continuousOn_const
      (isOpen_srcSet r).measurableSet
  have e : (fun z => couplingMean κ W s u z * φ z) =
      ((srcSet r).piecewise (couplingMean κ W s u) fun _ => 0) * φ := funext fun z => by
    by_cases hz : φ z = 0
    · simp [hz]
    · simp only [Pi.mul_apply, Set.piecewise_eq_of_mem _ _ _ (hφ z hz)]
  rw [e]
  exact hg.mul hφm

theorem vSrc_ne_zero_of_vApprox_ne_zero {n : ℕ} {z : ℂ}
    (hz : vApprox κ xL xR ρL ρR r n z ≠ 0) : vSrc κ xL xR ρL ρR r z ≠ 0 := fun h0 => by
  have := abs_vApprox_le (κ := κ) (ρL := ρL) (ρR := ρR) (xL := xL) (xR := xR) (r := r) n z
  rw [h0, abs_zero] at this
  exact hz (abs_nonpos_iff.1 this)

theorem measurable_vApprox (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) :
    Measurable (vApprox κ xL xR ρL ρR r n) :=
  ((contDiff_cutIm n (k := 0)).continuous.mul (contDiff_vDens hF hr).continuous).measurable

/-- **The tested means of the approximations converge**: `∫ 𝔥_s v_{n_k} → ∫ 𝔥_s v`. -/
theorem tendsto_integral_couplingMean_mul_vApprox (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {u : ℂ → ℝ} (hu : ContinuousOn u H) {C : ℝ} (hC : ∀ w ∈ H, |u w| ≤ C) {s : ℝ}
    (hs : s ∈ Icc 0 T) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => ∫ z, couplingMean κ W s u z * vApprox κ xL xR ρL ρR r (n k) z) atTop
      (𝓝 (∫ z, couplingMean κ W s u z * vSrc κ xL xR ρL ρR r z)) := by
  set M := C + |chiC κ| * (32 / (121 * r ^ 2) * T) with hM
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC Complex.I (by simp [QuantumZipper.H]))
  have hM0 : 0 ≤ M := add_nonneg hC0 (mul_nonneg (abs_nonneg _)
    (mul_nonneg (by have := h.r_pos; positivity) h.T_nonneg))
  refine tendsto_integral_of_dominated_convergence (fun z => M * |vSrc κ xL xR ρL ρR r z|)
    (fun k => (measurable_couplingMean_mul h hu hs (measurable_vApprox hF hr (n k))
      fun z hz => (mem_srcSet_of_vSrc_ne_zero hF hr (vSrc_ne_zero_of_vApprox_ne_zero hz)).1).aestronglyMeasurable)
    ((integrable_vSrc hF hr).abs.const_mul M) (fun k => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : vApprox κ xL xR ρL ρR r (n k) z = 0
    · rw [hz, abs_zero, mul_zero]; exact mul_nonneg hM0 (abs_nonneg _)
    · obtain ⟨hzS, hz6, -⟩ := mem_srcSet_of_vSrc_ne_zero hF hr (vSrc_ne_zero_of_vApprox_ne_zero hz)
      exact mul_le_mul (abs_couplingMean_src_le h hC hzS.1 hz6 hs) (abs_vApprox_le _ z) (abs_nonneg _)
        ((abs_nonneg _).trans (abs_couplingMean_src_le h hC hzS.1 hz6 hs))
  · exact tendsto_const_nhds.mul ((tendsto_vApprox z).comp hn)

/-! ### The Loewner Green kernel on the source -/

theorem im_two_div_nonpos {w : ℂ} (hw : 0 ≤ w.im) : (2 / w).im ≤ 0 := by
  rw [Complex.div_im]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, zero_div, zero_sub]
  exact neg_nonpos.2 (div_nonneg (mul_nonneg zero_le_two hw) (Complex.normSq_nonneg _))

/-- **`0 ≤ G(f_s y, f_s z) ≤ G_ℍ(y, z)`** for distinct points alive at `s` (the Loewner Green identity (3.16) with
its nonnegative integrand). -/
theorem greenH_fwdMap_mem_Icc_src (h : IsLocalRegime W r T) {s : ℝ} (hs : s ∈ Icc 0 T) {y z : ℂ}
    (hy : y ∈ H \ fwdHull W s) (hz : z ∈ H \ fwdHull W s) (hyz : y ≠ z) :
    0 ≤ greenH (fwdMap W s y) (fwdMap W s z) ∧ greenH (fwdMap W s y) (fwdMap W s z) ≤ greenH y z := by
  have hfy := Ito.im_fwdMap_pos h.cont hs.1 hy ⟨hs.1, le_rfl⟩
  have hfz := Ito.im_fwdMap_pos h.cont hs.1 hz ⟨hs.1, le_rfl⟩
  have hne : fwdMap W s y ≠ fwdMap W s z := fun he =>
    hyz (QuantumZipper.FwdHolo.injOn_fwdMap h.cont hs.1 hy hz he)
  refine ⟨QuantumZipper.greenH_nonneg (le_of_lt hfy) (le_of_lt hfz) hne, ?_⟩
  rw [Ito.greenH_fwdMap_eq_sub_integral h.cont hs.1 hy hz hyz, sub_le_self_iff]
  refine intervalIntegral.integral_nonneg hs.1 fun u hu => ?_
  exact mul_nonneg_of_nonpos_of_nonpos (im_two_div_nonpos (Ito.im_fwdMap_pos h.cont hs.1 hy hu).le)
    (im_two_div_nonpos (Ito.im_fwdMap_pos h.cont hs.1 hz hu).le)

/-! ### The Loewner Green energy as a product integral -/

open Classical in
/-- `f_s` on the source set, `0` elsewhere (a measurable version). -/
def fwdSrc (r : ℝ) (W : ℝ → ℝ) (s : ℝ) : ℂ → ℂ := (srcSet r).piecewise (fwdMap W s) fun _ => 0

theorem measurable_fwdSrc (h : IsLocalRegime W r T) {s : ℝ} (hs : s ∈ Icc 0 T) : Measurable (fwdSrc r W s) := by
  classical
  exact ((QuantumZipper.FwdHolo.differentiableOn_fwdMap h.cont hs.1).continuousOn.mono
    (srcSet_subset h hs)).measurable_piecewise continuousOn_const (isOpen_srcSet r).measurableSet

/-- The energy integrand `φ(y) G(f_s y, f_s z) φ(z)` on `ℂ × ℂ` (with the measurable version of `f_s`). -/
def energyKer (r : ℝ) (W : ℝ → ℝ) (s : ℝ) (φ : ℂ → ℝ) (p : ℂ × ℂ) : ℝ :=
  φ p.1 * greenH (fwdSrc r W s p.1) (fwdSrc r W s p.2) * φ p.2

theorem energyKer_eq {s : ℝ} {φ : ℂ → ℝ} (hφ : ∀ z, φ z ≠ 0 → z ∈ srcSet r) (y z : ℂ) :
    φ y * greenH (fwdMap W s y) (fwdMap W s z) * φ z = energyKer r W s φ (y, z) := by
  classical
  by_cases hy : φ y = 0
  · simp [energyKer, hy]
  by_cases hz : φ z = 0
  · simp [energyKer, hz]
  simp only [energyKer, fwdSrc, Set.piecewise_eq_of_mem _ _ _ (hφ y hy), Set.piecewise_eq_of_mem _ _ _ (hφ z hz)]

theorem measurable_energyKer (h : IsLocalRegime W r T) {s : ℝ} (hs : s ∈ Icc 0 T) {φ : ℂ → ℝ}
    (hφm : Measurable φ) : Measurable (energyKer r W s φ) :=
  ((hφm.comp measurable_fst).mul (QuantumZipper.measurable_greenH.comp
    (((measurable_fwdSrc h hs).comp measurable_fst).prodMk ((measurable_fwdSrc h hs).comp measurable_snd)))).mul
    (hφm.comp measurable_snd)

/-- The diagonal of `ℂ × ℂ` is null. -/
theorem ae_ne_prod : ∀ᵐ p ∂((volume : Measure ℂ).prod volume), p.1 ≠ p.2 := by
  have hm : MeasurableSet {x : ℂ × ℂ | x.1 ≠ x.2} := (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [Measure.ae_prod_iff_ae_ae hm]
  exact ae_of_all _ fun y => measure_eq_zero_iff_ae_notMem.1 (measure_singleton y) |>.mono fun z hz h => hz h.symm

theorem srcSet_of_abs_le {φ : ℂ → ℝ} (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) {z : ℂ} (hz : φ z ≠ 0) : z ∈ srcSet r ∧ 6 * r ≤ ‖z‖ := by
  have hv : vSrc κ xL xR ρL ρR r z ≠ 0 := fun h0 => by
    have := hφ z; rw [h0, abs_zero] at this; exact hz (abs_nonpos_iff.1 this)
  exact ⟨(mem_srcSet_of_vSrc_ne_zero hF hr hv).1, (mem_srcSet_of_vSrc_ne_zero hF hr hv).2.1⟩

theorem abs_energyKer_le (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    {s : ℝ} (hs : s ∈ Icc 0 T) {φ : ℂ → ℝ} (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) {p : ℂ × ℂ}
    (hp : p.1 ≠ p.2) :
    |energyKer r W s φ p| ≤ |vSrc κ xL xR ρL ρR r p.1| * |vSrc κ xL xR ρL ρR r p.2| * greenH p.1 p.2 := by
  have hφ' : ∀ z, φ z ≠ 0 → z ∈ srcSet r := fun z hz => (srcSet_of_abs_le hF hr hφ hz).1
  have hRHS : 0 ≤ |vSrc κ xL xR ρL ρR r p.1| * |vSrc κ xL xR ρL ρR r p.2| * greenH p.1 p.2 := by
    by_cases h1 : vSrc κ xL xR ρL ρR r p.1 = 0
    · simp [h1]
    by_cases h2 : vSrc κ xL xR ρL ρR r p.2 = 0
    · simp [h2]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (QuantumZipper.greenH_nonneg
      (le_of_lt (mem_srcSet_of_vSrc_ne_zero hF hr h1).1.1) (le_of_lt (mem_srcSet_of_vSrc_ne_zero hF hr h2).1.1) hp)
  by_cases hy : φ p.1 = 0
  · simpa [energyKer, hy] using hRHS
  by_cases hz : φ p.2 = 0
  · simpa [energyKer, hz] using hRHS
  rw [← energyKer_eq (W := W) (s := s) hφ' p.1 p.2]
  have hy' := srcSet_subset h hs (hφ' _ hy)
  have hz' := srcSet_subset h hs (hφ' _ hz)
  obtain ⟨g0, g1⟩ := greenH_fwdMap_mem_Icc_src h hs hy' hz' hp
  rw [abs_mul, abs_mul, abs_of_nonneg g0]
  calc |φ p.1| * greenH (fwdMap W s p.1) (fwdMap W s p.2) * |φ p.2|
      ≤ |vSrc κ xL xR ρL ρR r p.1| * greenH p.1 p.2 * |vSrc κ xL xR ρL ρR r p.2| := by
        exact mul_le_mul (mul_le_mul (hφ _) g1 g0 (abs_nonneg _)) (hφ _) (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) (g0.trans g1))
    _ = _ := by ring

theorem integrable_energyKer (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) :
    Integrable (energyKer r W s φ) ((volume : Measure ℂ).prod volume) :=
  (integrable_abs_mul_greenH (κ := κ) (ρL := ρL) (ρR := ρR) hF hr).mono'
    (measurable_energyKer h hs hφm).aestronglyMeasurable
    (ae_ne_prod.mono fun p hp => by rw [Real.norm_eq_abs]; exact abs_energyKer_le h hF hr hs hφ hp)

/-- **The Loewner Green energy as a product integral** (for `|φ| ≤ |v|`). -/
theorem loewnerGreenEnergy_eq_integral_energyKer (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) :
    loewnerGreenEnergy W s φ = ∫ p, energyKer r W s φ p ∂((volume : Measure ℂ).prod volume) := by
  have hφ' : ∀ z, φ z ≠ 0 → z ∈ srcSet r := fun z hz => (srcSet_of_abs_le hF hr hφ hz).1
  rw [integral_prod _ (integrable_energyKer h hF hr hs hφm hφ), loewnerGreenEnergy]
  congr 1; funext y; congr 1; funext z
  exact energyKer_eq hφ' y z

theorem abs_vSrc_le_self (z : ℂ) : |vSrc κ xL xR ρL ρR r z| ≤ |vSrc κ xL xR ρL ρR r z| := le_rfl

/-- **The energies of the approximations converge**: `E_s(v_{n_k}) → E_s(v)`. -/
theorem tendsto_loewnerGreenEnergy_vApprox (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => loewnerGreenEnergy W s (vApprox κ xL xR ρL ρR r (n k))) atTop
      (𝓝 (loewnerGreenEnergy W s (vSrc κ xL xR ρL ρR r))) := by
  simp_rw [loewnerGreenEnergy_eq_integral_energyKer h hF hr hs (measurable_vApprox hF hr _)
    (abs_vApprox_le _), loewnerGreenEnergy_eq_integral_energyKer h hF hr hs (measurable_vSrc hF hr)
    abs_vSrc_le_self]
  refine tendsto_integral_of_dominated_convergence
    (fun p => |vSrc κ xL xR ρL ρR r p.1| * |vSrc κ xL xR ρL ρR r p.2| * greenH p.1 p.2)
    (fun k => (measurable_energyKer h hs (measurable_vApprox hF hr _)).aestronglyMeasurable)
    (integrable_abs_mul_greenH hF hr) (fun k => ae_ne_prod.mono fun p hp => by
      rw [Real.norm_eq_abs]; exact abs_energyKer_le h hF hr hs (abs_vApprox_le _) hp)
    (ae_of_all _ fun p => ?_)
  exact (((tendsto_vApprox p.1).comp hn).mul_const _).mul ((tendsto_vApprox p.2).comp hn)

/-! ### The Loewner Green identity for the source -/

variable (κ xL xR ρL ρR r) in
/-- **`‖f‖²_∇ = ∫ v f`**: the Dirichlet energy of the cutoff `f`, through Green inversion `G_ℍ v = f`
(`integral_greenH_mul_vSrc`); it is the time-zero energy `E_0(v)` (`loewnerGreenEnergy_vSrc_eq` at `s = 0`). -/
def srcNorm : ℝ := ∫ z, vSrc κ xL xR ρL ρR r z * fCut κ xL xR ρL ρR r z

theorem integrable_vSrc_mul_fCut (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    Integrable fun z => vSrc κ xL xR ρL ρR r z * fCut κ xL xR ρL ρR r z := by
  obtain ⟨C, hC⟩ := (contDiff_fCut (κ := κ) (ρL := ρL) (ρR := ρR) hF hr (n := 0)).continuous.bounded_above_of_compact_support
    (hasCompactSupport_fCut hr.1)
  exact (integrable_vSrc hF hr).mul_bdd (contDiff_fCut hF hr (n := 0)).continuous.aestronglyMeasurable
    (ae_of_all _ hC)

/-- **The Loewner Green identity for the source** ((HL4), p. 248: "`∫₀^{t∧S} a_s² ds = ‖f‖²_∇ −
G_{ℍ∖K_{t∧S}}(v, v)`"): in the local regime, `E_s(v) = ‖f‖²_∇ − ∫₀ˢ A(u)² du`. -/
theorem loewnerGreenEnergy_vSrc_eq (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) :
    loewnerGreenEnergy W s (vSrc κ xL xR ρL ρR r) =
      srcNorm κ xL xR ρL ρR r - ∫ u in (0 : ℝ)..s, srcDrift κ xL xR ρL ρR r W u ^ 2 := by
  classical
  have hs0 := hs.1
  have hr0 : 0 < r := hr.1
  obtain ⟨Cv, hCv0, hCv⟩ := exists_abs_vSrc_le (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
  set v := vSrc κ xL xR ρL ρR r with hv
  set A := srcDrift κ xL xR ρL ρR r W with hA
  set MA := 8 / (11 * r) * ∫ z, |v z| with hMA
  -- the integrand on `ℝ × ℂ`
  set F : ℝ → ℂ → ℝ := fun u y => A (clampS s u) * (srcKer r W (clampS s u) y * v y) with hF_def
  have hcl : ∀ u, clampS s u ∈ Icc 0 T := fun u =>
    ⟨(clampS_mem hs0 u).1, (clampS_mem hs0 u).2.trans hs.2⟩
  have hAc : Continuous fun u => A (clampS s u) :=
    (continuousOn_srcDrift h hF hr).comp_continuous (continuous_clampS s) hcl
  have hFm : Measurable fun p : ℝ × ℂ => F p.1 p.2 := by
    refine Coupling.measurable_uncurry_of_continuousOn isClosed_univ (0 : ℝ) (fun y => ?_) (fun u _ => ?_)
      (fun u hu => absurd (mem_univ u) hu)
    · refine Continuous.continuousOn ?_
      by_cases hy : y ∈ srcSet r
      · have hys : y ∈ H \ fwdHull W s := srcSet_subset h hs hy
        have hc := (Ito.continuousOn_fwdMap_time' h.cont hs0 hys).comp_continuous (continuous_clampS s)
          (clampS_mem hs0)
        have hk : Continuous fun u => srcKer r W (clampS s u) y := by
          simp only [srcKer, Set.piecewise_eq_of_mem _ _ _ hy]
          exact Complex.continuous_im.comp (continuous_const.div hc fun u =>
            Ito.fwdMap_ne_zero h.cont hs0 hys (clampS_mem hs0 u))
        exact hAc.mul (hk.mul continuous_const)
      · simp only [hF_def, srcKer, Set.piecewise_eq_of_notMem _ _ _ hy, zero_mul, mul_zero]
        exact continuous_const
    · exact measurable_const.mul ((measurable_srcKer h (hcl u)).mul (measurable_vSrc hF hr))
  set K := MA * (8 / (11 * r)) * Cv with hK
  have hFb : ∀ u y, |F u y| ≤ K * (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) y := by
    intro u y
    have hK0 : 0 ≤ K := by
      rw [hK, hMA]; exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (integral_nonneg fun _ => abs_nonneg _)) (by positivity)) hCv0
    by_cases hy : v y = 0
    · simp only [hF_def, hy, mul_zero, abs_zero]
      exact mul_nonneg hK0 (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · obtain ⟨hyS, -, hy7⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hy
      rw [Set.indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact hy7), mul_one]
      simp only [hF_def, srcKer, Set.piecewise_eq_of_mem _ _ _ hyS, abs_mul]
      have h1 := abs_srcDrift_le h hF hr (hcl u) (κ := κ) (ρL := ρL) (ρR := ρR)
      have h2 := abs_im_two_div_src_le h hF hr (hcl u) hy
      have h3 := hCv y
      calc |A (clampS s u)| * (|(2 / fwdMap W (clampS s u) y).im| * |v y|)
          ≤ MA * (8 / (11 * r) * Cv) := by gcongr
        _ = K := by rw [hK]; ring
  have hint : Integrable (Function.uncurry F) ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => (fun _ : ℝ => (1 : ℝ)) p.1 *
        (fun y => K * (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) y) p.2)
        ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
      have hball : Integrable fun y : ℂ => (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) y :=
        (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
      have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) s)) := by
        rw [uIoc_of_le hs0]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact Integrable.mul_prod (L := ℝ) (integrable_const _) (hball.const_mul K)
    refine hg.mono' hFm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, one_mul, Real.norm_eq_abs]
    exact hFb p.1 p.2
  have hswap := intervalIntegral_integral_swap hint
  have hleft : ∫ u in (0 : ℝ)..s, ∫ y, F u y = ∫ u in (0 : ℝ)..s, A u ^ 2 := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs0] at hu
    simp only [hF_def, clampS_of_mem hu, integral_const_mul, sq]
    congr 1
    rw [hA, srcDrift]
    exact integral_congr_ae (ae_of_all _ fun y => srcKer_mul_vSrc hF hr W u y)
  have hright : ∀ y, ∫ u in (0 : ℝ)..s, F u y =
      v y * ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * A u := by
    intro y
    by_cases hy : v y = 0
    · simp [hF_def, hy]
    · have hyS := (mem_srcSet_of_vSrc_ne_zero hF hr hy).1
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hs0] at hu
      simp only [hF_def, clampS_of_mem hu, srcKer, Set.piecewise_eq_of_mem _ _ _ hyS]
      ring
  have hFi : Integrable fun y => v y * ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * A u := by
    have := hint.integral_prod_right
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [Function.uncurry]
    rw [← hright y, intervalIntegral.integral_of_le hs0, uIoc_of_le hs0]
  have hpot : ∀ y, v y * greenPot κ xL xR ρL ρR r W s y =
      v y * fCut κ xL xR ρL ρR r y - v y * ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * A u := by
    intro y
    by_cases hy : v y = 0
    · simp [hy]
    · have hyS := (mem_srcSet_of_vSrc_ne_zero hF hr hy).1
      rw [greenPot_eq h hF hr hs (srcSet_subset h hs hyS), mul_sub]
  have hE : loewnerGreenEnergy W s v = ∫ y, v y * greenPot κ xL xR ρL ρR r W s y := by
    unfold loewnerGreenEnergy greenPot
    congr 1; funext y
    rw [← integral_const_mul]
    congr 1; funext z
    ring
  rw [hE]
  simp_rw [hpot]
  rw [integral_sub (integrable_vSrc_mul_fCut hF hr) hFi, srcNorm]
  congr 1
  rw [← hleft, hswap]
  exact integral_congr_ae (ae_of_all _ fun y => (hright y).symm)

end Energy

end LocalExt

end InteractingSLE
