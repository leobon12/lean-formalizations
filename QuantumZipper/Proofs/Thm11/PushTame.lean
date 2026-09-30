import QuantumZipper.Proofs.GFF.ZeroRegBoundary
import QuantumZipper.Proofs.GFF.Admissible
import QuantumZipper.Proofs.Analysis.Pushforward
import QuantumZipper.Proofs.Thm11.ForwardClock
import QuantumZipper.Proofs.Thm11.ForwardTamed
import QuantumZipper.Proofs.Loewner.Algebra
import QuantumZipper.Statements.CouplingFields
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# RG-3a: the pushforward test measures `ν_T^±` are tame (deterministic part)

Blueprint `THM11_BLUEPRINT.md` §7, node RG-3 (deterministic part). For a driver `W`, a time
`T > 0` and a density `φ` (bounded, vanishing off a compact `K ⊆ ℍ`), let

  `ν_T := ((φ Leb).restrict D_T).map f_T`,  `D_T = ℍ \ K_T`,  `f_T = fwdMap W T`

(`pushTest W T φ`). With `φ = ρ^±` this is the measure at which `coordChangeOn X f_T D_T`
evaluates `X` (see `coordChangeOn_eq_evalReg_pushTest`). We prove:

* **FD-6** `surjOn_fwdMap`: `f_T : D_T → ℍ` is onto (from `ForwardReverseRelation`).
* `pushTest_greenH_pot`: bounded zero-boundary Green potential, using FD-6 and the kernel
  monotonicity FD-3 `G(f_T a, f_T b) ≤ G(a,b)`.
* `pushTest_ball_le`: the Frostman bound `ν_T(B(x,s)) ≤ M h^{-2} s²` for `Im x ≥ h`, `s ≤ h/2`,
  from `|f_T'(a)| ≥ Im f_T(a) / Im a` (FD-1), injectivity and the holomorphic change of
  variables.
* `isAdmissibleH_pushTest`: admissibility, given bounded images (FD-5, real barriers) and the
  extra hypothesis `∫ log⁻(Im x) dν_T < ∞` (see the note below);
  `lintegral_logIm_pushTest_lt_top_of_clock` derives that hypothesis from `∫_{D_T} φ S_T < ∞`
  (`S_T` = `fwdClock`).
* `evalReg_pushTest_ae_eq`, `coordChangeOn_pushTest_ae_eq`: RG-2 applies, given the
  strip-decay hypothesis.

**Note (admissibility).** `IsAdmissibleH` asks for a bounded singular log potential
`sup_y ∫ log⁻|x-y| dν(x)`. For real `y` this is not controlled by the Green potential (which
vanishes at `ℝ`), the Frostman bound or the log-log strip decay. We use the bound
`log⁻|x-y| ≤ G(x, ỹ) + log⁻ Im x` (`ỹ` the reflection of `y` into `Hbar`), so the extra
hypothesis `∫ log⁻(Im x) dν_T < ∞` suffices.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace PushTame

variable {W : ℝ → ℝ}

/-! ## FD-6: surjectivity -/

/-- **FD-6.** `fwdMap W T` maps `ℍ \ K_T` onto `ℍ`. -/
theorem surjOn_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) :
    SurjOn (fwdMap W T) (H \ fwdHull W T) H := by
  intro z hz
  have hz' : 0 < z.im := hz
  set V : ℝ → ℝ := fun s => W (T - s) - W T with hVdef
  have hV : Continuous V :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hVdef]
  have e : (fun s => V (T - s) - V T) = W := by
    funext s
    simp only [hVdef, sub_sub_cancel, sub_self, hW0]
    ring
  have h := LoewnerAlgebra.fwdMap_revMap_timeRev V hV hV0 hT hz
  rw [e] at h
  refine ⟨revMap V T z, ⟨?_, h.1⟩, h.2⟩
  show 0 < (revMap V T z).im
  exact lt_of_lt_of_le hz' (im_le_im_revMap V hV z hz' hT.le)

/-! ## The pushforward test measure -/

/-- `ν_T = ((φ Leb).restrict (ℍ \ K_T)).map f_T`. -/
def pushTest (W : ℝ → ℝ) (T : ℝ) (φ : ℂ → ℝ≥0∞) : Measure ℂ :=
  ((volume.withDensity φ).restrict (H \ fwdHull W T)).map (fwdMap W T)

section Basic

variable {T : ℝ} {φ : ℂ → ℝ≥0∞}

theorem measurableSet_H_pt : MeasurableSet H :=
  measurableSet_lt measurable_const Complex.measurable_im

theorem measurableSet_dom (hW : Continuous W) (hT : 0 ≤ T) :
    MeasurableSet (H \ fwdHull W T) :=
  (FwdHolo.isOpen_compl_fwdHull hW hT).measurableSet

theorem continuousOn_fwdMap_dom (hW : Continuous W) (hT : 0 ≤ T) :
    ContinuousOn (fwdMap W T) (H \ fwdHull W T) :=
  (FwdHolo.differentiableOn_fwdMap hW hT).continuousOn

theorem aemeasurable_fwdMap_dom (hW : Continuous W) (hT : 0 ≤ T) (μ : Measure ℂ) :
    AEMeasurable (fwdMap W T) (μ.restrict (H \ fwdHull W T)) :=
  (continuousOn_fwdMap_dom hW hT).aemeasurable (measurableSet_dom hW hT)

/-- Integrals against `ν_T`. -/
theorem lintegral_pushTest (hW : Continuous W) (hT : 0 ≤ T) (hφ : Measurable φ)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂pushTest W T φ = ∫⁻ a in H \ fwdHull W T, φ a * g (fwdMap W T a) := by
  unfold pushTest
  rw [lintegral_map' hg.aemeasurable (aemeasurable_fwdMap_dom hW hT _),
    restrict_withDensity (measurableSet_dom hW hT),
    lintegral_withDensity_eq_lintegral_mul₀ hφ.aemeasurable (g := fun a => g (fwdMap W T a))
      (hg.comp_aemeasurable (aemeasurable_fwdMap_dom hW hT volume))]
  rfl

/-- Measures of sets under `ν_T`. -/
theorem pushTest_apply (hW : Continuous W) (hT : 0 ≤ T) {B : Set ℂ} (hB : MeasurableSet B) :
    pushTest W T φ B = ∫⁻ a in fwdMap W T ⁻¹' B ∩ (H \ fwdHull W T), φ a := by
  unfold pushTest
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_fwdMap_dom hW hT _) hB,
    Measure.restrict_apply' (measurableSet_dom hW hT), withDensity_apply']

theorem pushTest_compl_H (hW : Continuous W) (hT : 0 ≤ T) : pushTest W T φ Hᶜ = 0 := by
  rw [pushTest_apply hW hT measurableSet_H_pt.compl]
  have : fwdMap W T ⁻¹' Hᶜ ∩ (H \ fwdHull W T) = ∅ := by
    ext a
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    intro h1 h2
    exact h1 (FwdHolo.mapsTo_fwdMap hW hT h2)
  rw [this, Measure.restrict_empty, lintegral_zero_measure]

theorem ae_mem_H_pushTest (hW : Continuous W) (hT : 0 ≤ T) :
    ∀ᵐ x ∂pushTest W T φ, x ∈ H := by
  rw [ae_iff]
  exact pushTest_compl_H hW hT

theorem isFiniteMeasure_pushTest (hφ : Measurable φ) {c : ℝ≥0∞} (hc : c < ⊤)
    (hφc : ∀ z, φ z ≤ c) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (hφK : ∀ z ∉ K, φ z = 0) : IsFiniteMeasure (pushTest W T φ) := by
  have h := (isAdmissibleH_withDensity hφ hc hφc hK
    (hKH.trans fun z (hz : 0 < z.im) => (hz.le : 0 ≤ z.im)) hφK).1
  unfold pushTest
  infer_instance

/-- **Support.** If `f_T(K ∩ D_T)` is bounded, `ν_T` has compact support in `Hbar`. -/
theorem pushTest_support (hW : Continuous W) (hT : 0 ≤ T) {K : Set ℂ} (hKc : IsClosed K)
    (hφK : ∀ z ∉ K, φ z = 0)
    (hbdd : Bornology.IsBounded (fwdMap W T '' (K ∩ (H \ fwdHull W T)))) :
    ∃ K', IsCompact K' ∧ K' ⊆ Hbar ∧ pushTest W T φ K'ᶜ = 0 := by
  refine ⟨closure (fwdMap W T '' (K ∩ (H \ fwdHull W T))), hbdd.isCompact_closure, ?_, ?_⟩
  · have hcl : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
    refine closure_minimal ?_ hcl
    rintro _ ⟨a, ⟨-, ha⟩, rfl⟩
    have : 0 < (fwdMap W T a).im := FwdHolo.mapsTo_fwdMap hW hT ha
    exact this.le
  · rw [pushTest_apply hW hT isClosed_closure.measurableSet.compl]
    have hsub : fwdMap W T ⁻¹' (closure (fwdMap W T '' (K ∩ (H \ fwdHull W T))))ᶜ ∩
        (H \ fwdHull W T) ⊆ Kᶜ := by
      intro a ha haK
      exact ha.1 (subset_closure (mem_image_of_mem _ ⟨haK, ha.2⟩))
    apply le_antisymm _ (zero_le)
    calc _ ≤ ∫⁻ a in Kᶜ, φ a := lintegral_mono_set hsub
      _ = ∫⁻ a in Kᶜ, 0 := setLIntegral_congr_fun hKc.measurableSet.compl
          (fun a ha => hφK a ha)
      _ = 0 := by simp

end Basic

/-! ## Elementary kernel inequalities -/

lemma norm_sq_eq_re_im_pt (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- `G(a,b) ≤ log(1+2R) + log⁻|a-b|` for `0 ≤ Im b ≤ R`. -/
lemma greenH_le_log_add_pt {a b : ℂ} (ha : 0 < a.im) (hb0 : 0 ≤ b.im) {R : ℝ}
    (hbR : b.im ≤ R) (hab : a ≠ b) :
    greenH a b ≤ Real.log (1 + 2 * R) + max 0 (-Real.log ‖b - a‖) := by
  have ht : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have hR : 0 ≤ R := hb0.trans hbR
  have hbc : ‖b - conj b‖ ≤ 2 * R := by
    have h := norm_sq_eq_re_im_pt (b - conj b)
    simp only [Complex.sub_re, Complex.conj_re, sub_self, Complex.sub_im, Complex.conj_im,
      sub_neg_eq_add] at h
    nlinarith [norm_nonneg (b - conj b)]
  have h1 : ‖a - conj b‖ ≤ ‖a - b‖ + 2 * R := by
    have : a - conj b = (a - b) + (b - conj b) := by ring
    rw [this]
    exact (norm_add_le _ _).trans (by linarith)
  have h2 : 0 < ‖a - conj b‖ := by
    have : 0 < (a - conj b).im := by
      simp only [Complex.sub_im, Complex.conj_im]; linarith
    exact this.trans_le ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  unfold greenH
  rw [norm_sub_rev b a]
  set t := ‖a - b‖ with ht_def
  have h3 : Real.log ‖a - conj b‖ ≤ Real.log (t + 2 * R) := Real.log_le_log h2 h1
  rcases le_or_gt 1 t with h | h
  · have h4 : Real.log (t + 2 * R) ≤ Real.log (1 + 2 * R) + Real.log t := by
      rw [← Real.log_mul (by linarith) ht.ne']
      exact Real.log_le_log (by linarith) (by nlinarith)
    have := le_max_left 0 (-Real.log t)
    linarith
  · have h4 : Real.log (t + 2 * R) ≤ Real.log (1 + 2 * R) :=
      Real.log_le_log (by linarith) (by linarith)
    have := le_max_right 0 (-Real.log t)
    linarith

/-- `log⁻|x-y| ≤ G(ỹ, x) + log⁻(Im x)` with `ỹ = Re y + i|Im y|`, for `x ∈ ℍ`. -/
lemma logNeg_le_greenH_add_pt {x : ℂ} (y : ℂ) (hx : 0 < x.im) :
    ENNReal.ofReal (-Real.log ‖x - y‖) ≤
      ENNReal.ofReal (greenH ⟨y.re, |y.im|⟩ x) + ENNReal.ofReal (-Real.log x.im) := by
  set y' : ℂ := ⟨y.re, |y.im|⟩ with hy'
  set d := ‖x - y‖ with hd_def
  set d' := ‖x - y'‖ with hd'_def
  have hd2 : d ^ 2 = (x.re - y.re) ^ 2 + (x.im - y.im) ^ 2 := by
    rw [hd_def, norm_sq_eq_re_im_pt]; simp
  have hd'2 : d' ^ 2 = (x.re - y.re) ^ 2 + (x.im - |y.im|) ^ 2 := by
    rw [hd'_def, norm_sq_eq_re_im_pt, hy']; simp
  have hdd' : d' ≤ d := by
    have : (x.im - |y.im|) ^ 2 ≤ (x.im - y.im) ^ 2 := by
      rcases le_or_gt 0 y.im with hy | hy
      · rw [abs_of_nonneg hy]
      · rw [abs_of_neg hy]; nlinarith
    nlinarith [norm_nonneg (x - y), norm_nonneg (x - y')]
  have hE : x.im ≤ ‖y' - conj x‖ := by
    have : (y' - conj x).im = |y.im| + x.im := by
      simp [hy']
    have h := (le_abs_self (y' - conj x).im).trans (Complex.abs_im_le_norm (y' - conj x))
    rw [this] at h
    linarith [abs_nonneg y.im]
  have hlogE : -Real.log ‖y' - conj x‖ ≤ -Real.log x.im := by
    have := Real.log_le_log hx hE; linarith
  rcases (norm_nonneg (x - y)).eq_or_lt with h0 | hpos
  · rw [← hd_def] at h0
    rw [← h0, Real.log_zero, neg_zero, ENNReal.ofReal_zero]
    exact zero_le
  rcases (norm_nonneg (x - y')).eq_or_lt with h0' | hpos'
  · -- `x = y'`: then `y = conj x` and `d = 2 Im x ≥ Im x`
    have hxy : x = y' := sub_eq_zero.mp (norm_eq_zero.mp h0'.symm)
    have hre : x.re = y.re := by rw [hxy]
    have him : x.im = |y.im| := by rw [hxy]
    have hdx : x.im ≤ d := by
      rcases le_or_gt 0 y.im with hy | hy
      · exfalso
        rw [abs_of_nonneg hy] at him
        have : d ^ 2 = 0 := by rw [hd2, hre, him]; ring
        rw [← hd_def] at hpos
        nlinarith
      · rw [abs_of_neg hy] at him
        have : d ^ 2 = (2 * x.im) ^ 2 := by rw [hd2, hre]; nlinarith
        nlinarith [norm_nonneg (x - y)]
    have : -Real.log d ≤ -Real.log x.im := by
      have := Real.log_le_log hx hdx; linarith
    exact (ENNReal.ofReal_le_ofReal this).trans le_add_self
  · have hle : -Real.log d ≤ greenH y' x + -Real.log x.im := by
      have h1 : Real.log d' ≤ Real.log d := Real.log_le_log hpos' hdd'
      unfold greenH
      rw [norm_sub_rev y' x, ← hd'_def]
      linarith
    exact (ENNReal.ofReal_le_ofReal hle).trans ENNReal.ofReal_add_le

/-! ## Potential bound (FD-3 + FD-6) -/

section Potential

variable {T : ℝ} {φ : ℂ → ℝ≥0∞}

/-- **Bounded Green potential of `ν_T`.** -/
theorem pushTest_greenH_pot (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 < T)
    (hφ : Measurable φ) {c : ℝ≥0∞} (hc : c < ⊤) (hφc : ∀ z, φ z ≤ c) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) (hφK : ∀ z ∉ K, φ z = 0) :
    ∃ U : ℝ≥0, ∀ x ∈ H, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂pushTest W T φ ≤ U := by
  obtain ⟨Rk, hRk⟩ := hK.isBounded.exists_norm_le
  set R := max Rk 0 with hR_def
  set L0 := ∫⁻ x : ℂ, ENNReal.ofReal (-Real.log ‖x‖) with hL0_def
  have hL0 : L0 < ⊤ := admissible_lintegral_logNeg_lt_top
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set Ctot := c * (ENNReal.ofReal (Real.log (1 + 2 * R)) * volume K + L0) with hCtot
  have hfin : Ctot ≠ ⊤ :=
    ENNReal.mul_ne_top hc.ne (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_lt_top.ne, hL0.ne⟩)
  refine ⟨Ctot.toNNReal, fun x hx => ?_⟩
  obtain ⟨a, ha, rfl⟩ := surjOn_fwdMap hW hW0 hT hx
  have hmeas : ∀ p : ℂ, Measurable fun y => ENNReal.ofReal (greenH p y) := fun p =>
    (measurable_greenH.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hne : ∀ᵐ b ∂(volume : Measure ℂ), b ≠ a := by
    rw [ae_iff]; simp
  have hsa := exists_isForwardSol_of_not_mem_fwdHull hT.le ha.1 ha.2
  rw [lintegral_pushTest hW hT.le hφ (hmeas _), ENNReal.coe_toNNReal hfin]
  calc ∫⁻ b in H \ fwdHull W T, φ b * ENNReal.ofReal (greenH (fwdMap W T a) (fwdMap W T b))
      ≤ ∫⁻ b in H \ fwdHull W T, φ b * ENNReal.ofReal (greenH a b) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem (measurableSet_dom hW hT.le), ae_restrict_of_ae hne]
          with b hb hba
        have hsb := exists_isForwardSol_of_not_mem_fwdHull hT.le hb.1 hb.2
        have := (FwdClock.greenH_fwdMap_mem_Icc hW ha.1 hb.1 (Ne.symm hba) hsa hsb
          ⟨hT.le, le_rfl⟩).2
        gcongr
    _ ≤ ∫⁻ b, φ b * ENNReal.ofReal (greenH a b) := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ b, c * (ENNReal.ofReal (Real.log (1 + 2 * R)) * K.indicator 1 b +
          ENNReal.ofReal (-Real.log ‖b - a‖)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hne] with b hba
        by_cases hb : b ∈ K
        · rw [indicator_of_mem hb, Pi.one_apply, mul_one]
          refine mul_le_mul' (hφc b) ?_
          have hbH : 0 < b.im := hKH hb
          have hbR : b.im ≤ R :=
            (Complex.im_le_norm b).trans ((hRk b hb).trans (le_max_left _ _))
          have hg := greenH_le_log_add_pt ha.1 hbH.le hbR (Ne.symm hba)
          refine (ENNReal.ofReal_le_ofReal hg).trans (ENNReal.ofReal_add_le.trans ?_)
          rw [admissible_ofReal_max_zero]
        · rw [hφK b hb, zero_mul]
          exact zero_le
    _ = Ctot := by
        rw [lintegral_const_mul' _ _ hc.ne,
          lintegral_add_left ((measurable_one.indicator hKm).const_mul _),
          lintegral_const_mul _ (measurable_one.indicator hKm), lintegral_indicator_one hKm,
          admissible_lintegral_logNeg_sub]

end Potential

/-! ## Frostman bound (FD-1 + change of variables) -/

section Frostman

variable {T : ℝ} {φ : ℂ → ℝ≥0∞}

/-- **Frostman bound for `ν_T`** with exponents `p = α = 2`. -/
theorem pushTest_ball_le (hW : Continuous W) (hT : 0 ≤ T) {c : ℝ≥0∞} (hc : c < ⊤)
    (hφc : ∀ z, φ z ≤ c) {K : Set ℂ} (hK : IsCompact K)
    (hφK : ∀ z ∉ K, φ z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ h' : ℝ, 0 < h' → ∀ x : ℂ, h' ≤ x.im → ∀ s : ℝ, 0 < s → s ≤ h' / 2 →
      pushTest W T φ (Metric.ball x s) ≤ ENNReal.ofReal (M * h' ^ (-(2 : ℝ)) * s ^ (2 : ℝ)) := by
  obtain ⟨Rk, hRk⟩ := hK.isBounded.exists_norm_le
  set R := max Rk 1 with hR_def
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine ⟨c.toReal * (4 * Real.pi * R ^ 2), by positivity, fun h hh x hx s hs hsh => ?_⟩
  set D := H \ fwdHull W T with hD
  set f := fwdMap W T with hf
  have hDo : IsOpen D := FwdHolo.isOpen_compl_fwdHull hW hT
  set E := K ∩ (D ∩ f ⁻¹' Metric.ball x s) with hE
  have hEm : MeasurableSet E :=
    hKm.inter ((continuousOn_fwdMap_dom hW hT).isOpen_inter_preimage hDo
      Metric.isOpen_ball).measurableSet
  set k : ℝ := (h / (2 * R)) ^ 2 with hk
  have hk0 : 0 < k := by positivity
  -- change of variables: `k · |E| ≤ |f(E)| ≤ |B(x,s)|`
  have hcv := lintegral_comp_holo hDo (FwdHolo.differentiableOn_fwdMap hW hT)
    (FwdHolo.injOn_fwdMap hW hT) (fun z hz => FwdHolo.deriv_fwdMap_ne_zero hW hT hz) hEm
    (fun z hz => hz.2.1) (fun _ => (1 : ℝ≥0∞))
  simp only [mul_one, lintegral_one, Measure.restrict_apply_univ] at hcv
  have hkey : ENNReal.ofReal k * volume E ≤ ENNReal.ofReal (s ^ 2 * Real.pi) := by
    calc ENNReal.ofReal k * volume E = ∫⁻ _ in E, ENNReal.ofReal k := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ z in E, ENNReal.ofReal (‖deriv f z‖ ^ 2) := by
          refine setLIntegral_mono' hEm fun z hz => ENNReal.ofReal_le_ofReal ?_
          have hzK := hz.1
          have hzD : z ∈ D := hz.2.1
          have hzB : f z ∈ Metric.ball x s := hz.2.2
          have hz0 : 0 < z.im := hzD.1
          have hzR : z.im ≤ R :=
            (Complex.im_le_norm z).trans ((hRk z hzK).trans (le_max_left _ _))
          have hfz : h / 2 ≤ (f z).im := by
            have h1 := (le_abs_self _).trans (Complex.abs_im_le_norm (x - f z))
            rw [Metric.mem_ball, dist_comm, Complex.dist_eq] at hzB
            simp only [Complex.sub_im] at h1
            linarith
          have hsol := exists_isForwardSol_of_not_mem_fwdHull hT hzD.1 hzD.2
          have hder := FwdClock.im_fwdMap_div_le_exp_re_logDerivFwd hW hz0 hsol
            (⟨hT, le_rfl⟩ : T ∈ Icc (0 : ℝ) T)
          rw [← FwdClock.norm_deriv_fwdMap hW hT hzD] at hder
          have hq : h / (2 * R) ≤ (f z).im / z.im := by
            rw [div_le_div_iff₀ (by positivity) hz0]
            nlinarith
          rw [hk]
          exact pow_le_pow_left₀ (by positivity) (hq.trans hder) 2
      _ = volume (f '' E) := hcv.symm
      _ ≤ volume (Metric.ball x s) := by
          apply measure_mono
          rintro _ ⟨z, hz, rfl⟩
          exact hz.2.2
      _ = ENNReal.ofReal (s ^ 2 * Real.pi) := by
          rw [Complex.volume_ball, ← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_coe_nnreal,
            NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
  have hvol : volume E ≤ ENNReal.ofReal (s ^ 2 * Real.pi / k) := by
    rw [ENNReal.ofReal_div_of_pos hk0, ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr hk0).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hkey
  rw [pushTest_apply hW hT Metric.isOpen_ball.measurableSet]
  have hmeasD : MeasurableSet (f ⁻¹' Metric.ball x s ∩ D) := by
    rw [inter_comm]
    exact ((continuousOn_fwdMap_dom hW hT).isOpen_inter_preimage hDo
      Metric.isOpen_ball).measurableSet
  calc ∫⁻ a in f ⁻¹' Metric.ball x s ∩ D, φ a
      ≤ ∫⁻ a in f ⁻¹' Metric.ball x s ∩ D, K.indicator (fun _ => c) a := by
        refine lintegral_mono fun a => ?_
        by_cases ha : a ∈ K
        · rw [indicator_of_mem ha]; exact hφc a
        · rw [hφK a ha]; exact zero_le
    _ = c * volume E := by
        rw [lintegral_indicator_const hKm, Measure.restrict_apply hKm, hE, inter_comm D]
    _ ≤ c * ENNReal.ofReal (s ^ 2 * Real.pi / k) := by gcongr
    _ = ENNReal.ofReal (c.toReal * (4 * Real.pi * R ^ 2) * h ^ (-(2 : ℝ)) * s ^ (2 : ℝ)) := by
        rw [← ENNReal.ofReal_toReal hc.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        congr 1
        rw [Real.rpow_neg hh.le, Real.rpow_two, Real.rpow_two, hk]
        field_simp
        ring

end Frostman

/-! ## Admissibility and the application of RG-2 -/

section Tame

variable {T : ℝ} {φ : ℂ → ℝ≥0∞}

/-- **Admissibility of `ν_T`**, given bounded images and `∫ log⁻(Im x) dν_T < ∞`. -/
theorem isAdmissibleH_pushTest (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 < T)
    (hφ : Measurable φ) {c : ℝ≥0∞} (hc : c < ⊤) (hφc : ∀ z, φ z ≤ c) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) (hφK : ∀ z ∉ K, φ z = 0)
    (hbdd : Bornology.IsBounded (fwdMap W T '' (K ∩ (H \ fwdHull W T))))
    (hlog : ∫⁻ x, ENNReal.ofReal (-Real.log x.im) ∂pushTest W T φ < ⊤) :
    IsAdmissibleH (pushTest W T φ) := by
  obtain ⟨U, hU⟩ := pushTest_greenH_pot hW hW0 hT hφ hc hφc hK hKH hφK
  refine ⟨isFiniteMeasure_pushTest hφ hc hφc hK hKH hφK,
    pushTest_support hW hT.le hK.isClosed hφK hbdd, ?_⟩
  refine ⟨(U : ℝ≥0∞) + ∫⁻ x, ENNReal.ofReal (-Real.log x.im) ∂pushTest W T φ,
    ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, hlog⟩, fun y => ?_⟩
  set y' : ℂ := ⟨y.re, |y.im|⟩ with hy'
  have hmeas : Measurable fun x => ENNReal.ofReal (greenH y' x) :=
    (measurable_greenH.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂pushTest W T φ
      ≤ ∫⁻ x, (ENNReal.ofReal (greenH y' x) + ENNReal.ofReal (-Real.log x.im))
          ∂pushTest W T φ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem_H_pushTest hW hT.le] with x hx
        exact logNeg_le_greenH_add_pt y hx
    _ = ∫⁻ x, ENNReal.ofReal (greenH y' x) ∂pushTest W T φ +
          ∫⁻ x, ENNReal.ofReal (-Real.log x.im) ∂pushTest W T φ := lintegral_add_left hmeas _
    _ ≤ _ := by
        gcongr
        rcases (abs_nonneg y.im).eq_or_lt with h0 | hpos
        · -- `ỹ` is real: `G(ỹ, ·) = 0`
          have hz : ∀ x, greenH y' x = 0 := by
            intro x
            have hc' : conj y' = y' := Complex.ext (by simp [hy']) (by simp [hy', ← h0])
            unfold greenH
            rw [show ‖y' - conj x‖ = ‖y' - x‖ by
              rw [← Complex.norm_conj (y' - conj x), map_sub, Complex.conj_conj, hc']]
            ring
          simp [hz]
        · have hyH : y' ∈ H := by show 0 < y'.im; simpa [hy'] using hpos
          exact hU y' hyH

/-- **RG-3a, deterministic tameness.** Under the barrier hypotheses (FD-5) and the log
hypothesis, `ν_T` satisfies every hypothesis of `evalReg_ae_eq_zeroGFF_bdry` except the strip
decay. -/
theorem pushTest_tame (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 < T)
    (hφ : Measurable φ) {c : ℝ≥0∞} (hc : c < ⊤) (hφc : ∀ z, φ z ≤ c) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) (hφK : ∀ z ∉ K, φ z = 0) {R : ℝ} (hR : 0 < R)
    (hKR : ∀ a ∈ K, |a.re| < R) (hp : ∃ v, IsForwardSol W (R : ℂ) T v)
    (hm : ∃ v, IsForwardSol W ((-R : ℝ) : ℂ) T v)
    (hlog : ∫⁻ x, ENNReal.ofReal (-Real.log x.im) ∂pushTest W T φ < ⊤) :
    IsAdmissibleH (pushTest W T φ) ∧
      (∃ U : ℝ≥0, ∀ x ∈ H, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂pushTest W T φ ≤ U) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ h' : ℝ, 0 < h' → ∀ x : ℂ, h' ≤ x.im → ∀ s : ℝ, 0 < s →
        s ≤ h' / 2 → pushTest W T φ (Metric.ball x s) ≤
          ENNReal.ofReal (M * h' ^ (-(2 : ℝ)) * s ^ (2 : ℝ)) := by
  obtain ⟨Rk, hRk⟩ := hK.isBounded.exists_norm_le
  have hbdd : Bornology.IsBounded (fwdMap W T '' (K ∩ (H \ fwdHull W T))) :=
    isBounded_fwdMap_image_of_barriers hW hT.le (by rw [hW0, abs_zero]; exact hR) hp hm
      (M := Rk) fun a ha => ⟨hKR a ha, (Complex.im_le_norm a).trans (hRk a ha)⟩
  exact ⟨isAdmissibleH_pushTest hW hW0 hT hφ hc hφc hK hKH hφK hbdd hlog,
    pushTest_greenH_pot hW hW0 hT hφ hc hφc hK hKH hφK,
    pushTest_ball_le hW hT.le hc hφc hK hφK⟩

end Tame

end PushTame
end QuantumZipper
