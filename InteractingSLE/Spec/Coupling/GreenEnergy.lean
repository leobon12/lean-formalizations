import InteractingSLE.Spec.Coupling.Separation
import InteractingSLE.Spec.Coupling.Fubini
import InteractingSLE.Spec.Ito.Coordinates
import InteractingSLE.Frozen.Spec.loewnerGreenEnergy
import QuantumZipper.Proofs.Thm11.FieldMartingales

/-!
# The Loewner evolution of the Green energy `E_t(φ)` (pathwise (3.16)–(3.19))

Packet PROVE-T11-L311 (Specification §3.3, L519–L548; graph nodes `SPEC.eq-3.16`, `SPEC.eq-3.19`). For the frozen
`E_t(φ) = loewnerGreenEnergy w t φ = ∬ φ(y) G(f_t y, f_t z) φ(z) dy dz` and a test function `φ` whose support `K`
stays unswallowed up to time `T` with `Im f_T ≥ δ > 0` on `K`:

* `integrable_greenEnergy_integrand`: the integrand is integrable on `ℂ × ℂ` (the logarithmic diagonal
  singularity: `0 ≤ G(f_r y, f_r z) ≤ G(y, z)`, and QuantumZipper's `integrable_rho_rho_greenH`);
* `loewnerGreenEnergy_sub_eq_integral` (**(3.16) integrated against `φ ⊗ φ`**): for `0 ≤ p ≤ q ≤ T`,
  `E_p(φ) − E_q(φ) = ∫_p^q (∫ φ(z) Im(2/f_s(z)) dz)² ds`;
* `abs_integral_mul_im_two_div_le`: `|∫ φ Im(2/f_s)| ≤ (2/δ) ∫ |φ|` for `s ≤ T`.

Hence `E_t(φ)` is nonincreasing and Lipschitz in `t`, with derivative `−(∫ φ Im(2/f_t))²`: the bracket of the tested
mean (3.19) (the martingale statement is in `TestMean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology QuantumZipper
open scoped ComplexConjugate

namespace InteractingSLE

namespace Coupling

variable {W : ℝ → ℝ} {T : ℝ} {φ : ℂ → ℝ} {δ : ℝ}

/-- `Im(2/f_s(z))`, the coefficient `k_s(z)` of `dB` in `d𝔥_s(z)`. -/
def kCoef (W : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℝ := (2 / fwdMap W s z).im

/-- The protection of a set `K` up to time `T`: unswallowed, with `Im f_T ≥ δ` on `K`. -/
def IsProtected (W : ℝ → ℝ) (T δ : ℝ) (K : Set ℂ) : Prop :=
  ∀ z ∈ K, z ∈ H \ fwdHull W T ∧ δ ≤ (fwdMap W T z).im

section Protected

variable {K : Set ℂ}

theorem IsProtected.mem_of_le (hK : IsProtected W T δ K) {r : ℝ} (hr : r ∈ Icc 0 T) {z : ℂ}
    (hz : z ∈ K) : z ∈ H \ fwdHull W r :=
  Ito.mem_diff_fwdHull_of_le (hK z hz).1 hr.2

theorem IsProtected.le_im (hK : IsProtected W T δ K) (hW : Continuous W) (hT : 0 ≤ T) {r : ℝ}
    (hr : r ∈ Icc 0 T) {z : ℂ} (hz : z ∈ K) : δ ≤ (fwdMap W r z).im := by
  have hanti := Ito.antitoneOn_im_fwdMap_of_continuousOn hT hW.continuousOn (hK z hz).1.1
    (Ito.exists_isForwardSol_of_mem hT (hK z hz).1)
  exact (hK z hz).2.trans (hanti hr ⟨hT, le_rfl⟩ hr.2)

theorem IsProtected.le_im_self (hK : IsProtected W T δ K) (hW : Continuous W) (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ K) : δ ≤ z.im := by
  have h := hK.le_im hW hT ⟨le_rfl, hT⟩ hz
  rwa [fwdMap_zero_of_mem hW hT (hK z hz).1, Complex.sub_im, Complex.ofReal_im, sub_zero] at h

theorem IsProtected.continuousOn_fwdMap (hK : IsProtected W T δ K) (hW : Continuous W) {r : ℝ}
    (hr : r ∈ Icc 0 T) : ContinuousOn (fwdMap W r) K := fun _ hz =>
  (FwdHolo.hasDerivAt_fwdMap hW hr.1 (hK.mem_of_le hr hz)).continuousAt.continuousWithinAt

/-- The forward map on `K`, extended by the constant `i` off `K`: a measurable function. -/
def fwdMapOn (W : ℝ → ℝ) (r : ℝ) (K : Set ℂ) : ℂ → ℂ := by
  classical exact K.piecewise (fwdMap W r) fun _ => Complex.I

theorem measurable_fwdMapOn (hK : IsProtected W T δ K) (hKc : IsClosed K) (hW : Continuous W)
    {r : ℝ} (hr : r ∈ Icc 0 T) : Measurable (fwdMapOn W r K) := by
  classical
  exact (hK.continuousOn_fwdMap hW hr).measurable_piecewise continuousOn_const hKc.measurableSet

theorem fwdMapOn_of_mem {r : ℝ} {z : ℂ} (hz : z ∈ K) : fwdMapOn W r K z = fwdMap W r z := by
  classical simp [fwdMapOn, hz]

theorem measurable_greenH : Measurable fun p : ℂ × ℂ => greenH p.1 p.2 := by
  unfold greenH
  fun_prop

theorem kCoef_neg {s : ℝ} {z : ℂ} (hz : 0 < (fwdMap W s z).im) : kCoef W s z < 0 := by
  have hne : fwdMap W s z ≠ 0 := fun h => by rw [h, Complex.zero_im] at hz; exact lt_irrefl 0 hz
  rw [kCoef, im_two_div]
  have : 0 < ‖fwdMap W s z‖ ^ 2 := by have := norm_pos_iff.2 hne; positivity
  exact div_neg_of_neg_of_pos (by linarith) this

theorem abs_kCoef_le (hδ : 0 < δ) {s : ℝ} {z : ℂ} (hz : δ ≤ (fwdMap W s z).im) :
    |kCoef W s z| ≤ 2 / δ :=
  (Complex.abs_im_le_norm _).trans (Ito.norm_two_div_le hδ hz)

/-- (3.16) between two times: `G(f_p y, f_p z) − G(f_q y, f_q z) = ∫_p^q k_s(y) k_s(z) ds`. -/
theorem greenH_fwdMap_sub_eq (hK : IsProtected W T δ K) (hW : Continuous W) (hT : 0 ≤ T)
    {y z : ℂ} (hy : y ∈ K) (hz : z ∈ K) (hyz : y ≠ z) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hqT : q ≤ T) :
    greenH (fwdMap W p y) (fwdMap W p z) - greenH (fwdMap W q y) (fwdMap W q z) =
      ∫ s in p..q, kCoef W s y * kCoef W s z := by
  have hpT : p ∈ Icc 0 T := ⟨hp, hpq.trans hqT⟩
  have hqT' : q ∈ Icc 0 T := ⟨hp.trans hpq, hqT⟩
  rw [Ito.greenH_fwdMap_eq_sub_integral hW hp (hK.mem_of_le hpT hy) (hK.mem_of_le hpT hz) hyz,
    Ito.greenH_fwdMap_eq_sub_integral hW hqT'.1 (hK.mem_of_le hqT' hy) (hK.mem_of_le hqT' hz) hyz]
  have hc := Ito.continuousOn_im_two_div_mul hW hT (hK y hy).1 (hK z hz).1
  have hi : ∀ r ∈ Icc 0 T, IntervalIntegrable (fun s => kCoef W s y * kCoef W s z) volume 0 r :=
    fun r hr => (hc.mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1
  have := intervalIntegral.integral_interval_sub_left (hi q hqT') (hi p hpT)
  simp only [kCoef] at this ⊢
  linarith

/-- `0 ≤ G(f_r y, f_r z) ≤ G(y, z)` on a protected set, off the diagonal. -/
theorem greenH_fwdMap_mem_Icc (hK : IsProtected W T δ K) (hW : Continuous W) (hT : 0 ≤ T)
    (hδ : 0 < δ) {y z : ℂ} (hy : y ∈ K) (hz : z ∈ K) (hyz : y ≠ z) {r : ℝ} (hr : r ∈ Icc 0 T) :
    0 ≤ greenH (fwdMap W r y) (fwdMap W r z) ∧
      greenH (fwdMap W r y) (fwdMap W r z) ≤ greenH y z := by
  have hiy := hK.le_im hW hT hr hy
  have hiz := hK.le_im hW hT hr hz
  constructor
  · have hsep := norm_sub_sq_mul_le hW hT (hK y hy).1 (hK z hz).1 hr
    have hne : fwdMap W r y ≠ fwdMap W r z := by
      intro h
      rw [h, sub_self, norm_zero] at hsep
      have h1 : 0 < ‖y - z‖ ^ 2 := by have := norm_pos_iff.2 (sub_ne_zero.2 hyz); positivity
      have h2 : 0 < (fwdMap W r y).im * (fwdMap W r z).im :=
        mul_pos (hδ.trans_le hiy) (hδ.trans_le hiz)
      nlinarith [mul_pos h1 h2]
    exact greenH_nonneg (le_of_lt (hδ.trans_le hiy)) (le_of_lt (hδ.trans_le hiz)) hne
  · have h := greenH_fwdMap_sub_eq hK hW hT hy hz hyz le_rfl hr.1 hr.2
    have h0 : ∀ s ∈ Icc (0 : ℝ) T, (fwdMap W s y) ∈ H ∧ (fwdMap W s z) ∈ H := fun s hs =>
      ⟨hδ.trans_le (hK.le_im hW hT hs hy), hδ.trans_le (hK.le_im hW hT hs hz)⟩
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..r, kCoef W s y * kCoef W s z := by
      refine intervalIntegral.integral_nonneg hr.1 fun s hs => ?_
      have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hr.2⟩
      exact (mul_pos_of_neg_of_neg (kCoef_neg (h0 s hs').1) (kCoef_neg (h0 s hs').2)).le
    have e0 : fwdMap W 0 y = y - W 0 := fwdMap_zero_of_mem hW hT (hK y hy).1
    have e0' : fwdMap W 0 z = z - W 0 := fwdMap_zero_of_mem hW hT (hK z hz).1
    rw [e0, e0', FwdClock.greenH_sub_ofReal] at h
    linarith

/-- The integrand `φ(y) G(f_r y, f_r z) φ(z)` of `E_r(φ)` on `ℂ × ℂ`. -/
def energyIntegrand (W : ℝ → ℝ) (r : ℝ) (φ : ℂ → ℝ) (p : ℂ × ℂ) : ℝ :=
  φ p.1 * greenH (fwdMap W r p.1) (fwdMap W r p.2) * φ p.2

theorem eq_zero_of_notMem_tsupport' {z : ℂ} (hz : z ∉ tsupport φ) : φ z = 0 :=
  image_eq_zero_of_notMem_tsupport hz

theorem energyIntegrand_eq_fwdMapOn (r : ℝ) (p : ℂ × ℂ) :
    energyIntegrand W r φ p =
      φ p.1 * greenH (fwdMapOn W r (tsupport φ) p.1) (fwdMapOn W r (tsupport φ) p.2) * φ p.2 := by
  by_cases h1 : p.1 ∈ tsupport φ
  · by_cases h2 : p.2 ∈ tsupport φ
    · simp only [energyIntegrand, fwdMapOn_of_mem h1, fwdMapOn_of_mem h2]
    · simp [energyIntegrand, eq_zero_of_notMem_tsupport' h2]
  · simp [energyIntegrand, eq_zero_of_notMem_tsupport' h1]

theorem integrable_energyIntegrand (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hK : IsProtected W T δ (tsupport φ)) (hW : Continuous W) (hT : 0 ≤ T) (hδ : 0 < δ) {r : ℝ}
    (hr : r ∈ Icc 0 T) :
    Integrable (energyIntegrand W r φ) ((volume : Measure ℂ).prod volume) := by
  have hρδ : ∀ a : ℂ, a.im < δ → φ a = 0 := fun a ha => eq_zero_of_notMem_tsupport' fun h =>
    absurd (hK.le_im_self hW hT h) (not_le.2 ha)
  have hmeas : Measurable (energyIntegrand W r φ) := by
    have hf := measurable_fwdMapOn hK (isClosed_tsupport φ) hW hr
    have e : energyIntegrand W r φ = fun p => φ p.1 *
        greenH (fwdMapOn W r (tsupport φ) p.1) (fwdMapOn W r (tsupport φ) p.2) * φ p.2 :=
      funext (energyIntegrand_eq_fwdMapOn r)
    rw [e]
    exact ((hφc.measurable.comp measurable_fst).mul (measurable_greenH.comp
      ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd)))).mul
      (hφc.measurable.comp measurable_snd)
  refine Integrable.mono' (FieldMart.integrable_rho_rho_greenH hφc hφs hδ hρδ)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [FieldMart.ae_ne_diag] with p hp
  rw [Real.norm_eq_abs, energyIntegrand]
  by_cases h1 : p.1 ∈ tsupport φ
  · by_cases h2 : p.2 ∈ tsupport φ
    · obtain ⟨g0, g1⟩ := greenH_fwdMap_mem_Icc hK hW hT hδ h1 h2 hp hr
      rw [abs_mul, abs_mul, abs_of_nonneg g0]
      have := mul_nonneg (abs_nonneg (φ p.1)) (abs_nonneg (φ p.2))
      calc |φ p.1| * greenH (fwdMap W r p.1) (fwdMap W r p.2) * |φ p.2|
          = |φ p.1| * |φ p.2| * greenH (fwdMap W r p.1) (fwdMap W r p.2) := by ring
        _ ≤ |φ p.1| * |φ p.2| * greenH p.1 p.2 := mul_le_mul_of_nonneg_left g1 this
    · simp [eq_zero_of_notMem_tsupport' h2]
  · simp [eq_zero_of_notMem_tsupport' h1]

theorem loewnerGreenEnergy_eq_integral_prod (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hK : IsProtected W T δ (tsupport φ)) (hW : Continuous W) (hT : 0 ≤ T) (hδ : 0 < δ) {r : ℝ}
    (hr : r ∈ Icc 0 T) :
    loewnerGreenEnergy W r φ = ∫ p, energyIntegrand W r φ p ∂((volume : Measure ℂ).prod volume) :=
  (integral_prod _ (integrable_energyIntegrand hφc hφs hK hW hT hδ hr)).symm

/-- The time `s` clamped to `[p, q]`. -/
def clampTime (p q s : ℝ) : ℝ := max p (min s q)

theorem clampTime_mem {p q : ℝ} (hpq : p ≤ q) (s : ℝ) : clampTime p q s ∈ Icc p q :=
  ⟨le_max_left _ _, max_le hpq (min_le_right _ _)⟩

theorem clampTime_of_mem {p q s : ℝ} (hs : s ∈ Icc p q) : clampTime p q s = s := by
  rw [clampTime, min_eq_left hs.2, max_eq_right hs.1]

theorem continuous_clampTime (p q : ℝ) : Continuous (clampTime p q) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem continuousOn_kCoef (hK : IsProtected W T δ K) (hW : Continuous W) (hT : 0 ≤ T) (hδ : 0 < δ)
    {r : ℝ} (hr : r ∈ Icc 0 T) : ContinuousOn (kCoef W r) K :=
  Complex.continuous_im.comp_continuousOn (continuousOn_const.div (hK.continuousOn_fwdMap hW hr)
    fun z hz h => by
      have := hδ.trans_le (hK.le_im hW hT hr hz)
      rw [h, Complex.zero_im] at this; exact lt_irrefl 0 this)

theorem continuous_kCoef_clampTime (hK : IsProtected W T δ K) (hW : Continuous W) (hT : 0 ≤ T)
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hqT : q ≤ T) {z : ℂ} (hz : z ∈ K) :
    Continuous fun s => kCoef W (clampTime p q s) z := by
  have hmem : ∀ s, clampTime p q s ∈ Icc 0 T := fun s =>
    ⟨hp.trans (clampTime_mem hpq s).1, (clampTime_mem hpq s).2.trans hqT⟩
  have h := (Ito.continuousOn_fwdMap_time' hW hT (hK z hz).1).comp_continuous
    (continuous_clampTime p q) hmem
  exact Complex.continuous_im.comp (continuous_const.div h fun s =>
    Ito.fwdMap_ne_zero hW hT (hK z hz).1 (hmem s))

theorem measurable_phi_kCoef_clampTime (hφc : Continuous φ) (hK : IsProtected W T δ (tsupport φ))
    (hW : Continuous W) (hT : 0 ≤ T) (hδ : 0 < δ) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hqT : q ≤ T) :
    Measurable fun x : ℂ × ℝ => φ x.1 * kCoef W (clampTime p q x.2) x.1 := by
  refine measurable_uncurry_of_continuousOn (isClosed_tsupport φ)
    (g := fun z s => φ z * kCoef W (clampTime p q s) z) 0 (fun s => ?_) (fun z hz => ?_)
    (fun z hz s => by simp [eq_zero_of_notMem_tsupport' hz])
  · have hr : clampTime p q s ∈ Icc 0 T :=
      ⟨hp.trans (clampTime_mem hpq s).1, (clampTime_mem hpq s).2.trans hqT⟩
    exact hφc.continuousOn.mul (continuousOn_kCoef hK hW hT hδ hr)
  · exact (continuous_const.mul (continuous_kCoef_clampTime hK hW hT hp hpq hqT hz)).measurable

/-- **(3.16) integrated against `φ ⊗ φ`**: `E_p(φ) − E_q(φ) = ∫_p^q (∫ φ(z) Im(2/f_s(z)) dz)² ds`. -/
theorem loewnerGreenEnergy_sub_eq_integral (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hK : IsProtected W T δ (tsupport φ)) (hW : Continuous W) (hT : 0 ≤ T) (hδ : 0 < δ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) (hqT : q ≤ T) :
    loewnerGreenEnergy W p φ - loewnerGreenEnergy W q φ =
      ∫ s in p..q, (∫ z, φ z * kCoef W s z) ^ 2 := by
  have hpT : p ∈ Icc 0 T := ⟨hp, hpq.trans hqT⟩
  have hqT' : q ∈ Icc 0 T := ⟨hp.trans hpq, hqT⟩
  rw [loewnerGreenEnergy_eq_integral_prod hφc hφs hK hW hT hδ hpT,
    loewnerGreenEnergy_eq_integral_prod hφc hφs hK hW hT hδ hqT',
    ← integral_sub (integrable_energyIntegrand hφc hφs hK hW hT hδ hpT)
      (integrable_energyIntegrand hφc hφs hK hW hT hδ hqT')]
  set Ψ : ℝ → ℂ → ℝ := fun s z => φ z * kCoef W (clampTime p q s) z with hΨ
  have hΨs : ∀ s ∈ Ioc p q, ∀ z, Ψ s z = φ z * kCoef W s z := fun s hs z => by
    rw [hΨ]; simp only; rw [clampTime_of_mem (Ioc_subset_Icc_self hs)]
  have hD : ∀ᵐ x ∂((volume : Measure ℂ).prod volume),
      energyIntegrand W p φ x - energyIntegrand W q φ x =
        ∫ s in Ioc p q, Ψ s x.1 * Ψ s x.2 := by
    filter_upwards [FieldMart.ae_ne_diag] with x hx
    by_cases h1 : x.1 ∈ tsupport φ
    · by_cases h2 : x.2 ∈ tsupport φ
      · have h := greenH_fwdMap_sub_eq hK hW hT h1 h2 hx hp hpq hqT
        simp only [energyIntegrand]
        rw [show φ x.1 * greenH (fwdMap W p x.1) (fwdMap W p x.2) * φ x.2 -
            φ x.1 * greenH (fwdMap W q x.1) (fwdMap W q x.2) * φ x.2 =
            φ x.1 * φ x.2 * (greenH (fwdMap W p x.1) (fwdMap W p x.2) -
              greenH (fwdMap W q x.1) (fwdMap W q x.2)) by ring, h,
          intervalIntegral.integral_of_le hpq, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
        simp only [hΨs s hs]
        ring
      · simp [energyIntegrand, hΨ, eq_zero_of_notMem_tsupport' h2]
    · simp [energyIntegrand, hΨ, eq_zero_of_notMem_tsupport' h1]
  rw [integral_congr_ae hD]
  have : IsFiniteMeasure (volume.restrict (Ioc p q)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  have hΨm := measurable_phi_kCoef_clampTime hφc hK hW hT hδ hp hpq hqT
  have hΨb : ∀ s z, |Ψ s z| ≤ |φ z| * (2 / δ) := fun s z => by
    by_cases hz : z ∈ tsupport φ
    · have hr : clampTime p q s ∈ Icc 0 T :=
        ⟨hp.trans (clampTime_mem hpq s).1, (clampTime_mem hpq s).2.trans hqT⟩
      rw [hΨ, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_kCoef_le hδ (hK.le_im hW hT hr hz)) (abs_nonneg _)
    · simp [hΨ, eq_zero_of_notMem_tsupport' hz]
  have hint3 : Integrable (Function.uncurry fun (x : ℂ × ℂ) (s : ℝ) => Ψ s x.1 * Ψ s x.2)
      (((volume : Measure ℂ).prod volume).prod (volume.restrict (Ioc p q))) := by
    refine Integrable.mono' ((((hφi.abs.mul_prod hφi.abs).mul_prod
      (integrable_const (1 : ℝ))).mul_const ((2 / δ) ^ 2)))
      (((hΨm.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (hΨm.comp (measurable_fst.snd.prodMk measurable_snd))).aestronglyMeasurable)
      (ae_of_all _ fun r => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    calc |Ψ r.2 r.1.1| * |Ψ r.2 r.1.2| ≤ (|φ r.1.1| * (2 / δ)) * (|φ r.1.2| * (2 / δ)) :=
          mul_le_mul (hΨb _ _) (hΨb _ _) (abs_nonneg _) (by positivity)
      _ = |φ r.1.1| * |φ r.1.2| * 1 * (2 / δ) ^ 2 := by ring
  rw [integral_integral_swap hint3, intervalIntegral.integral_of_le hpq]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [integral_prod_mul (fun z => Ψ s z) (fun z => Ψ s z), sq]
  simp only [hΨs s hs]

/-- `|∫ φ(z) Im(2/f_s(z)) dz| ≤ (2/δ) ∫ |φ|` for `s ∈ [0, T]`. -/
theorem abs_integral_mul_kCoef_le (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (hK : IsProtected W T δ (tsupport φ)) (hW : Continuous W)
    (hT : 0 ≤ T) (hδ : 0 < δ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    |∫ z, φ z * kCoef W s z| ≤ 2 / δ * ∫ z, |φ z| := by
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le
    (((hφc.integrable_of_hasCompactSupport hφs).abs.const_mul _)) (ae_of_all _ fun z => ?_)
  · by_cases hz : z ∈ tsupport φ
    · rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_kCoef_le hδ (hK.le_im hW hT hs hz)) (abs_nonneg _)
    · simp [eq_zero_of_notMem_tsupport' hz]

end Protected

end Coupling

end InteractingSLE
