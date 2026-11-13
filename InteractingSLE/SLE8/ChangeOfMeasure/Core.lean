import InteractingSLE.SLE8.ChangeOfMeasure.TestFunction
import InteractingSLE.SLE8.ChangeOfMeasure.Clock
import QuantumZipper.Proofs.RS.MartingaleBound
import QuantumZipper.Proofs.Probability.Girsanov.DynkinStop
import QuantumZipper.Proofs.ItoLite.OptionalStopping
import QuantumZipper.Proofs.Probability.Williams.MarkovHit
import MathFin.Probability.Martingales.UnifIntegrableL2

/-!
# Optional sampling at the height clock (SLE₈ note, proof of Lemma 3.1)

SLE₈ note `source/sle8-continuity.pdf`, §3.1, pp. 4–5 (transcription `source/sle8/sle8-continuity.md`,
anchor `lem-3.1-proof`).

Let `B` be a Brownian motion with continuous paths, measurable coordinates and `B 0 = 0`, and let
`U_s = (Z_s, log Φ_s) = RS.rsProc 8 B (iy)` be the state of the reverse flow from `iy` driven by `√8 B`
(`stProc`). It solves an additive-noise equation with the bounded Lipschitz drift `RS.rsDrift y`.

* `setIntegral_stoppedValue_eq`: for a function `F` that is `C³` on `{Im > 0}`, has zero Dynkin
  generator there, and whose square is dominated by a Rohde–Schramm test function on the region the
  flow visits before its height reaches `√5`, and for stopping times `ρ ≤ σ` before the hitting time of
  height `√5` (`topTime`), `∫_A F(U_σ) = ∫_A F(U_ρ)` for every `A ∈ 𝓕_ρ`. The proof localizes with the
  exit times of `{|X| < n, Y < √5}` capped at `n` (QuantumZipper's local Dynkin formula between stopping
  times, `Girsanov.integral_mul_localDynkin_stopped_eq`), and passes to the limit with the `L²` bound
  given by the domination (`MathFin`'s `L²`-Vitali lemma). This replaces Itô's formula and Novikov's
  criterion in the note: for `F = expTest 0 = 𝓜` it is the martingale property of `𝓜` up to the
  height `√5` used to define `ℚ`.
* `measure_not_reach_eq_zero`: almost surely the height reaches `√5`.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal

namespace InteractingSLE.SLE8.ChangeOfMeasure

open QuantumZipper QuantumZipper.RS FwdHolo FrozenMart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {y : ℝ}

/-! ### The state process -/

/-- The state `(Z_s, log Φ_s)` of the reverse flow from `iy` driven by `√8 B`. -/
abbrev stProc (B : ℝ≥0 → Ω → ℝ) (y : ℝ) : ℝ≥0 → Ω → ℂ × ℝ := rsProc 8 B ((y : ℂ) * I)

omit mΩ in
theorem stProc_fst (t : ℝ≥0) (ω : Ω) : (stProc B y t ω).1 = htZ (drive 8 B ω) y t := rfl

theorem stProc_integralEq (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (ω : Ω) (t : ℝ≥0) :
    stProc B y t ω = (((y : ℂ) * I), 0) + (∫ r in (0 : ℝ)..t, rsDrift y (stProc B y r.toNNReal ω))
      + B t ω • rsNoise 8 := by
  have h := rsProc_integralEq hBc 8 (z := (y : ℂ) * I) (by simpa using hy) ω t
  rwa [im_mul_I] at h

theorem continuous_drive8 (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) : Continuous (drive 8 B ω) :=
  NonSwallow.continuous_drive_ns hBc 8 ω

theorem continuous_stProc (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (ω : Ω) :
    Continuous (stProc B y · ω) :=
  Dynkin.continuous_of_integralEq hBc (lipschitz_rsDrift hy).continuous (norm_rsDrift_le hy)
    (stProc_integralEq hBc hy) ω

theorem measurable_stProc (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    (hy : 0 < y) (t : ℝ≥0) : Measurable[NonSwallow.bmFilt hBm t] (stProc B y t) :=
  Dynkin.measurable_of_integralEq (NonSwallow.bmFilt hBm) (NonSwallow.bmFilt_adapted hBm) hBc
    (lipschitz_rsDrift hy) (norm_rsDrift_le hy) (stProc_integralEq hBc hy)
    (continuous_stProc hBc hy) t

theorem stProc_zero (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (hy : 0 < y)
    (ω : Ω) : stProc B y 0 ω = (((y : ℂ) * I), 0) := by
  rw [stProc_integralEq hBc hy ω 0, hB0 ω]
  simp

theorem le_im_stProc (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (t : ℝ≥0) (ω : Ω) :
    y ≤ (stProc B y t ω).1.im :=
  le_im_htZ (continuous_drive8 hBc ω) hy t.coe_nonneg

/-- `log Φ_s = (U_s).2`. -/
theorem snd_stProc_eq (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (t : ℝ≥0) (ω : Ω) :
    (stProc B y t ω).2 = Real.log ‖deriv (revMap (drive 8 B ω) t) ((y : ℂ) * I)‖ :=
  (log_phi_htZ (continuous_drive8 hBc ω) hy t.coe_nonneg).symm

/-- `Φ_s = e^{(U_s).2} ≤ Y_s / y`. -/
theorem exp_snd_stProc_le (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (t : ℝ≥0) (ω : Ω) :
    Real.exp (stProc B y t ω).2 ≤ (stProc B y t ω).1.im / y := by
  have hW := continuous_drive8 hBc ω
  rw [snd_stProc_eq hBc hy, Real.exp_log (norm_pos_iff.2
    (deriv_revMap_ne_zero _ hW t.coe_nonneg (mem_H_mul_I hy)))]
  exact phi_le_im_div hW hy t.coe_nonneg

/-- `|log Φ_s| ≤ 2 s / y²`. -/
theorem abs_snd_stProc_le (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (t : ℝ≥0) (ω : Ω) :
    |(stProc B y t ω).2| ≤ 2 * t / y ^ 2 := by
  have hW := continuous_drive8 hBc ω
  show |(∫ s in (0 : ℝ)..t, 2 / (revMap (drive 8 B ω) s ((y : ℂ) * I)) ^ 2).re| ≤ _
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 / y ^ 2)
    fun s hs => ?_).trans ?_
  · rw [uIoc_of_le t.coe_nonneg] at hs
    have h1 : y ≤ ‖revMap (drive 8 B ω) s ((y : ℂ) * I)‖ :=
      (le_im_htZ hW hy hs.1.le).trans (Complex.im_le_norm _)
    rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr)
  · rw [sub_zero, abs_of_nonneg t.coe_nonneg]
    apply le_of_eq
    ring

/-! ### The hitting time of height `√5` -/

/-- Every path of the height reaches `√5`. -/
def ReachesTop (B : ℝ≥0 → Ω → ℝ) (y : ℝ) : Prop :=
  ∀ ω, ∃ s : ℝ≥0, √5 ≤ (htZ (drive 8 B ω) y s).im

/-- The hitting time of height `√5`, i.e. of the height parameter `U = log √5`. -/
def topTime (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (ω : Ω) : ℝ≥0 := hitTime (drive 8 B ω) y √5

/-- The hitting time of a level `c ≤ √5` is a stopping time of the natural filtration. -/
theorem isStoppingTime_hitTime (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    (hy : 0 < y) (hreach : ReachesTop B y) {c : ℝ} (hc : c ≤ √5) :
    IsStoppingTime (NonSwallow.bmFilt hBm)
      (fun ω => ((hitTime (drive 8 B ω) y c : ℝ≥0) : WithTop ℝ≥0)) := by
  intro t
  have hreach' : ∀ ω, ∃ s : ℝ≥0, c ≤ (htZ (drive 8 B ω) y s).im := fun ω =>
    let ⟨s, hs⟩ := hreach ω; ⟨s, hc.trans hs⟩
  have : {ω | ((hitTime (drive 8 B ω) y c : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
      {ω | c ≤ (stProc B y t ω).1.im} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    exact hitTime_le_iff (continuous_drive8 hBc ω) hy (hreach' ω) t
  rw [this]
  exact measurableSet_le measurable_const
    (Complex.measurable_im.comp (measurable_fst.comp (measurable_stProc hBc hBm hy t)))

/-! ### Localization -/

/-- The exit set: `|X| ≥ n` or `Y ≥ √5`. -/
def locCl (n : ℕ) : Set (ℂ × ℝ) := {x | (n : ℝ) ≤ |x.1.re|} ∪ {x | √5 ≤ x.1.im}

/-- The localizing region. -/
def locK (y : ℝ) (n : ℕ) : Set (ℂ × ℝ) :=
  {x | y ≤ x.1.im ∧ x.1.im ≤ √5 ∧ |x.1.re| ≤ n ∧ |x.2| ≤ 2 * n / y ^ 2}

/-- The localizing times: exit from `{|X| < n, Y < √5}`, capped at `n`. -/
def locTime (B : ℝ≥0 → Ω → ℝ) (y : ℝ) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  hittingBtwn (stProc B y) (locCl n) 0 n ω

theorem isClosed_locCl (n : ℕ) : IsClosed (locCl n) :=
  (isClosed_le continuous_const (continuous_abs.comp
    (Complex.continuous_re.comp continuous_fst))).union
    (isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst))

theorem isClosed_locK (y : ℝ) (n : ℕ) : IsClosed (locK y n) := by
  have him : Continuous fun x : ℂ × ℝ => x.1.im := Complex.continuous_im.comp continuous_fst
  have hre : Continuous fun x : ℂ × ℝ => |x.1.re| :=
    continuous_abs.comp (Complex.continuous_re.comp continuous_fst)
  exact (isClosed_le continuous_const him).inter ((isClosed_le him continuous_const).inter
    ((isClosed_le hre continuous_const).inter
      (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)))

theorem isCompact_locK (y : ℝ) (n : ℕ) : IsCompact (locK y n) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_locK y n) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ × ℝ))
    (r := (n : ℝ) + √5 + |y| + 2 * n / y ^ 2)).subset fun x hx => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  refine max_le ?_ ?_
  · refine (Complex.norm_le_abs_re_add_abs_im x.1).trans ?_
    have : |x.1.im| ≤ √5 + |y| := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le y, Real.sqrt_nonneg 5], by linarith [abs_nonneg y]⟩
    have : 0 ≤ 2 * (n : ℝ) / y ^ 2 := by positivity
    linarith
  · rw [Real.norm_eq_abs]
    have : 0 ≤ (n : ℝ) := n.cast_nonneg
    linarith [Real.sqrt_nonneg 5, abs_nonneg y]

theorem locK_subset (hy : 0 < y) (n : ℕ) : locK y n ⊆ rsDom := fun _ hx => hy.trans_le hx.1

theorem isStoppingTime_locTime (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    (hy : 0 < y) (n : ℕ) :
    IsStoppingTime (NonSwallow.bmFilt hBm) (fun ω => ((locTime B y n ω : ℝ≥0) : WithTop ℝ≥0)) :=
  ItoLite.isStoppingTime_hittingBtwn_of_isClosed (measurable_stProc hBc hBm hy)
    (continuous_stProc hBc hy) (isClosed_locCl n) n

/-- The flow stays in the localizing region until it exits. -/
theorem stProc_mem_locK (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (hy : 0 < y)
    (hy5 : y ≤ √5) (n : ℕ) (ω : Ω) (t : ℝ≥0) (ht : t ≤ n)
    (hs : ∀ s < t, stProc B y s ω ∉ locCl n) : stProc B y t ω ∈ locK y n := by
  have hUc := continuous_stProc hBc hy ω
  refine ⟨le_im_stProc hBc hy t ω, ?_, ?_, ?_⟩
  rotate_right
  · refine (abs_snd_stProc_le hBc hy t ω).trans ?_
    have : (t : ℝ) ≤ n := by exact_mod_cast ht
    gcongr
  all_goals rcases eq_or_ne t 0 with h0 | hpos'
  · rw [h0, stProc_zero hBc hB0 hy ω]; simpa using hy5
  · have hcl : IsClosed {s : ℝ≥0 | (stProc B y s ω).1.im ≤ √5} :=
      isClosed_le (Complex.continuous_im.comp (continuous_fst.comp hUc)) continuous_const
    have hsub : Iio t ⊆ {s : ℝ≥0 | (stProc B y s ω).1.im ≤ √5} := fun s hst => by
      have := hs s hst
      simp only [locCl, mem_union, mem_ofPred_eq, not_or, not_le] at this
      exact this.2.le
    have := hcl.closure_subset_iff.2 hsub
    rw [closure_Iio' (a := t) ⟨0, pos_iff_ne_zero.2 hpos'⟩] at this
    exact this (le_refl t)
  · rw [h0, stProc_zero hBc hB0 hy ω]; simp
  · have hcl : IsClosed {s : ℝ≥0 | |(stProc B y s ω).1.re| ≤ n} :=
      isClosed_le (continuous_abs.comp (Complex.continuous_re.comp (continuous_fst.comp hUc)))
        continuous_const
    have hsub : Iio t ⊆ {s : ℝ≥0 | |(stProc B y s ω).1.re| ≤ n} := fun s hst => by
      have := hs s hst
      simp only [locCl, mem_union, mem_ofPred_eq, not_or, not_le] at this
      exact this.1.le
    have := hcl.closure_subset_iff.2 hsub
    rw [closure_Iio' (a := t) ⟨0, pos_iff_ne_zero.2 hpos'⟩] at this
    exact this (le_refl t)

/-- For each path, the localizing times eventually exceed the hitting time of height `√5`. -/
theorem eventually_topTime_le_locTime (hBc : ∀ ω, Continuous (B · ω)) (hy : 0 < y) (ω : Ω) :
    ∀ᶠ n in atTop, topTime B y ω ≤ locTime B y n ω := by
  have hW := continuous_drive8 hBc ω
  set S := topTime B y ω with hS
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := S)).exists_bound_of_continuousOn
    (continuous_stProc hBc hy ω).continuousOn
  filter_upwards [eventually_ge_atTop (⌈C⌉₊ + ⌈(S : ℝ)⌉₊ + 1)] with n hn
  have hCn : C < n := by
    have := Nat.le_ceil C
    have : ((⌈C⌉₊ + ⌈(S : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this
    linarith [(Nat.cast_nonneg ⌈(S : ℝ)⌉₊ : (0 : ℝ) ≤ _)]
  have hSn : S ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    have := Nat.le_ceil (S : ℝ)
    have : ((⌈C⌉₊ + ⌈(S : ℝ)⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at this ⊢
    linarith [(Nat.cast_nonneg ⌈C⌉₊ : (0 : ℝ) ≤ _)]
  have hnot : ∀ s < S, stProc B y s ω ∉ locCl n := by
    intro s hs hmem
    rcases hmem with h | h
    · have h1 := hC s ⟨bot_le, hs.le⟩
      have h2 : |(stProc B y s ω).1.re| ≤ ‖stProc B y s ω‖ :=
        (Complex.abs_re_le_norm _).trans (norm_fst_le _)
      simp only [mem_ofPred_eq] at h
      linarith
    · simp only [mem_ofPred_eq] at h
      exact absurd (hitTime_le s h) (not_le.2 hs)
  unfold locTime
  rw [hittingBtwn]
  split_ifs with hex
  · refine le_csInf ?_ fun j hj => ?_
    · obtain ⟨j, hj, hjs⟩ := hex; exact ⟨j, hj, hjs⟩
    · by_contra hlt
      exact hnot j (not_le.1 hlt) hj.2
  · exact hSn

/-! ### Optional sampling at the height clock -/

section Sampling

variable (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
  (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) (hy : 0 < y) (hy5 : y ≤ √5)
include hB hBc hBm hB0 hy hy5

omit hB hBm in
/-- The stopped flow lies in the localizing region before the localizing time. -/
theorem stoppedValue_mem_locK {τ : Ω → WithTop ℝ≥0} (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ ((locTime B y n ω : ℝ≥0) : WithTop ℝ≥0)) (ω : Ω) :
    stoppedValue (stProc B y) τ ω ∈ locK y n := by
  have hfin : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hτ ω)
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hfin
  have htl : t ≤ locTime B y n ω := by rw [← WithTop.coe_le_coe, ht]; exact hτ ω
  have hval : stoppedValue (stProc B y) τ ω = stProc B y t ω := by
    rw [stoppedValue, ← ht]; rfl
  rw [hval]
  refine stProc_mem_locK hBc hB0 hy hy5 n ω t (htl.trans (hittingBtwn_le ω)) fun s hs => ?_
  exact notMem_of_lt_hittingBtwn (hs.trans_le htl) bot_le

omit hB hB0 hy5 in
theorem measurable_stoppedValue_stProc {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (NonSwallow.bmFilt hBm) τ) : Measurable (stoppedValue (stProc B y) τ) := by
  have hprog : IsStronglyProgressive (NonSwallow.bmFilt hBm) (stProc B y) :=
    StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (measurable_stProc hBc hBm hy t).stronglyMeasurable) (continuous_stProc hBc hy)
  exact (measurable_stoppedValue hprog hτ).mono hτ.measurableSpace_le le_rfl

variable {F : ℂ × ℝ → ℝ} (hF : ContDiffOn ℝ 3 F rsDom) (hFm : Measurable F)
  (hLF : ∀ x : ℂ × ℝ, 0 < x.1.im → y ≤ x.1.im → dynkinGen (rsDrift y) (rsNoise 8) F x = 0)
  {C r : ℝ} (hC : 0 ≤ C)
  (hdom : ∀ x : ℂ × ℝ, y ≤ x.1.im → x.1.im ≤ √5 → Real.exp x.2 ≤ x.1.im / y →
    F x ^ 2 ≤ C * rsTest 8 r x)
include hF hFm hLF hC hdom

omit hLF in
/-- The localized integrals converge (the `L²` bound comes from the domination). -/
theorem tendsto_integral_loc {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (NonSwallow.bmFilt hBm) σ)
    (hσtop : ∀ ω, σ ω ≤ (topTime B y ω : WithTop ℝ≥0)) {A : Set Ω}
    {An : ℕ → Set Ω} (hAnm : ∀ n, MeasurableSet (An n))
    (hAn : ∀ ω, ∀ᶠ n in atTop, (ω ∈ An n ↔ ω ∈ A)) :
    MemLp (fun ω => A.indicator 1 ω * F (stoppedValue (stProc B y) σ ω)) 2 P ∧
    Tendsto (fun n : ℕ => ∫ ω, (An n).indicator 1 ω *
        F (stoppedValue (stProc B y) (fun ω => min (σ ω) (locTime B y n ω : WithTop ℝ≥0)) ω) ∂P)
      atTop (𝓝 (∫ ω, A.indicator 1 ω * F (stoppedValue (stProc B y) σ ω) ∂P)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set Fl := NonSwallow.bmFilt hBm
  set U := stProc B y
  set G := rsTest 8 r
  have hτn := isStoppingTime_locTime hBc hBm hy (B := B)
  set σn : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (σ ω) (locTime B y n ω : WithTop ℝ≥0)
  have hσn : ∀ n, IsStoppingTime Fl (σn n) := fun n => hσ.min (hτn n)
  have hσnle : ∀ n ω, σn n ω ≤ (locTime B y n ω : WithTop ℝ≥0) := fun n ω => min_le_right _ _
  -- bounds on the compact regions
  have hFb : ∀ n : ℕ, ∃ M, ∀ x ∈ locK y n, ‖F x‖ ≤ M := fun n =>
    (isCompact_locK y n).exists_bound_of_continuousOn (hF.continuousOn.mono (locK_subset hy n))
  have hGb : ∀ n : ℕ, ∃ M, ∀ x ∈ locK y n, |G x| ≤ M := fun n => by
    obtain ⟨M, hM⟩ := (isCompact_locK y n).exists_bound_of_continuousOn
      ((contDiffOn_rsTest 8 r).continuousOn.mono (locK_subset hy n))
    exact ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩
  have hGm : Measurable G := by simp only [G]; unfold rsTest; fun_prop
  -- the supermartingale bound for the dominating function
  have hGint : ∀ n, ∫ ω, G (stoppedValue U (σn n) ω) ∂P ≤ G (((y : ℂ) * I), 0) := by
    intro n
    obtain ⟨M, hM⟩ := hGb n
    have h := Girsanov.integral_mul_localDynkin_stopped_le hB hBc Fl
      (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) (lipschitz_rsDrift hy)
      (norm_rsDrift_le hy) (stProc_integralEq hBc hy) isOpen_rsDom (isClosed_locCl n)
      (isClosed_locK y n) (locK_subset hy n) (contDiffOn_rsTest 8 r)
      (fun x hx _ => (dynkinGen_rsTest (by norm_num) r (hy.trans_le hx.1) hx.1).le) n
      (fun ω t ht hs => stProc_mem_locK hBc hB0 hy hy5 n ω t ht hs) hM
      (isStoppingTime_const Fl 0) (hσn n) (fun ω => bot_le) (hσnle n)
      (Y := fun _ => (1 : ℝ)) measurable_const (fun _ => zero_le_one) (fun _ => le_rfl)
    simp only [one_mul, stoppedValue_const] at h
    refine h.trans (le_of_eq ?_)
    simp only [stProc_zero hBc hB0 hy, integral_const, probReal_univ, one_smul, G]
  set f : ℕ → Ω → ℝ := fun n ω => (An n).indicator 1 ω * F (stoppedValue U (σn n) ω) with hf
  set g : Ω → ℝ := fun ω => A.indicator 1 ω * F (stoppedValue U σ ω) with hg
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (measurable_const.indicator (hAnm n)).mul
      (hFm.comp (measurable_stoppedValue_stProc hBc hBm hy (hσn n)))
  have hind : ∀ (S : Set Ω) ω, |S.indicator (1 : Ω → ℝ) ω| ≤ 1 := fun S ω => by
    by_cases h : ω ∈ S <;> simp [h]
  have hfL2 : ∀ n, MemLp (f n) 2 P := by
    intro n
    obtain ⟨M, hM⟩ := hFb n
    refine MemLp.of_bound (hfm n).aestronglyMeasurable M (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hM _ (stoppedValue_mem_locK hBc hB0 hy hy5 n (hσnle n) ω)
    rw [Real.norm_eq_abs] at h1
    calc |(An n).indicator 1 ω| * |F (stoppedValue U (σn n) ω)| ≤ 1 * M :=
          mul_le_mul (hind _ ω) h1 (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have hsq : ∀ n ω, f n ω ^ 2 ≤ C * G (stoppedValue U (σn n) ω) := by
    intro n ω
    have hK := stoppedValue_mem_locK hBc hB0 hy hy5 n (hσnle n) ω
    have hfin : σn n ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (hσnle n ω)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hfin
    have hval : stoppedValue U (σn n) ω = stProc B y t ω := by
      rw [stoppedValue, ← ht]; rfl
    have h2 := hdom (stoppedValue U (σn n) ω) hK.1 hK.2.1
      (by rw [hval]; exact exp_snd_stProc_le hBc hy t ω)
    calc f n ω ^ 2 = (An n).indicator 1 ω ^ 2 * F (stoppedValue U (σn n) ω) ^ 2 := by
          simp only [hf]; ring
      _ ≤ 1 * F (stoppedValue U (σn n) ω) ^ 2 := by
          gcongr
          have := hind (An n) ω
          rw [← sq_abs]
          nlinarith [abs_nonneg ((An n).indicator (1 : Ω → ℝ) ω)]
      _ ≤ C * G (stoppedValue U (σn n) ω) := by rw [one_mul]; exact h2
  have hbound : ∀ n, ∫ ω, f n ω ^ 2 ∂P ≤ C * G (((y : ℂ) * I), 0) := by
    intro n
    obtain ⟨M, hM⟩ := hGb n
    have hGi : Integrable (fun ω => G (stoppedValue U (σn n) ω)) P := by
      refine Integrable.of_bound (C := M)
        (hGm.comp (measurable_stoppedValue_stProc hBc hBm hy (hσn n))).aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      exact hM _ (stoppedValue_mem_locK hBc hB0 hy hy5 n (hσnle n) ω)
    calc ∫ ω, f n ω ^ 2 ∂P ≤ ∫ ω, C * G (stoppedValue U (σn n) ω) ∂P :=
          integral_mono ((hfL2 n).integrable_sq) (hGi.const_mul C) (hsq n)
      _ = C * ∫ ω, G (stoppedValue U (σn n) ω) ∂P := integral_const_mul C _
      _ ≤ C * G (((y : ℂ) * I), 0) := mul_le_mul_of_nonneg_left (hGint n) hC
  -- pointwise convergence (eventually equal)
  have hev : ∀ ω, ∀ᶠ n in atTop, f n ω = g ω := by
    intro ω
    filter_upwards [eventually_topTime_le_locTime hBc hy ω, hAn ω] with n hn hA'
    have hle : σ ω ≤ (locTime B y n ω : WithTop ℝ≥0) :=
      (hσtop ω).trans (WithTop.coe_le_coe.2 hn)
    have hmin : σn n ω = σ ω := min_eq_left hle
    have hI : (An n).indicator (1 : Ω → ℝ) ω = A.indicator 1 ω := by
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hA'.2 h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hA'.1 h'))]
    simp only [hf, hg, hI]
    congr 2
    simp only [stoppedValue, hmin]
  have htend : ∀ ω, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := fun ω =>
    tendsto_nhds_of_eventually_eq (hev ω)
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, ∀ᵐ ω ∂P, Tendsto (fun k => f (ns (ms k)) ω) atTop (𝓝 (g ω)) :=
    fun ns hns => ⟨id, ae_of_all _ fun ω => (htend ω).comp (hns.comp tendsto_id)⟩
  have hgL2 : MemLp g 2 P := MathFin.memLp_two_of_subseq_ae_of_sq_bound hfL2 hfm hbound
    ⟨id, ae_of_all _ fun ω => htend ω⟩
  have h := MathFin.tendsto_setIntegral_of_subseq_ae_of_sq_bound hfL2 hbound
    (hgL2.mono_exponent (by norm_num)) hsub univ
  exact ⟨hgL2, by simpa only [setIntegral_univ] using h⟩

/-- **Optional sampling at the height clock.** For stopping times `ρ ≤ σ` before the hitting time of
height `√5`, and every `A ∈ 𝓕_ρ`, `∫_A F(U_σ) = ∫_A F(U_ρ)`. -/
theorem setIntegral_stoppedValue_eq {ρ σ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime (NonSwallow.bmFilt hBm) ρ) (hσ : IsStoppingTime (NonSwallow.bmFilt hBm) σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω) (hσtop : ∀ ω, σ ω ≤ (topTime B y ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hρ.measurableSpace] A) :
    ∫ ω in A, F (stoppedValue (stProc B y) σ ω) ∂P =
      ∫ ω in A, F (stoppedValue (stProc B y) ρ ω) ∂P := by
  set Fl := NonSwallow.bmFilt hBm
  set U := stProc B y
  have hτn := isStoppingTime_locTime hBc hBm hy (B := B)
  have hAm : MeasurableSet A := hρ.measurableSpace_le A hA
  set An : ℕ → Set Ω := fun n => A ∩ {ω | ρ ω ≤ (locTime B y n ω : WithTop ℝ≥0)} with hAn_def
  have hAnρ : ∀ n, MeasurableSet[(hρ.min (hτn n)).measurableSpace] (An n) := fun n =>
    hρ.measurableSet_inter_le (hτn n) A hA
  have hAnm : ∀ n, MeasurableSet (An n) := fun n =>
    (hρ.min (hτn n)).measurableSpace_le _ (hAnρ n)
  have hAn : ∀ ω, ∀ᶠ n in atTop, (ω ∈ An n ↔ ω ∈ A) := by
    intro ω
    filter_upwards [eventually_topTime_le_locTime hBc hy ω] with n hn
    have : ρ ω ≤ (locTime B y n ω : WithTop ℝ≥0) :=
      ((hρσ ω).trans (hσtop ω)).trans (WithTop.coe_le_coe.2 hn)
    simp only [hAn_def, mem_inter_iff, mem_ofPred_eq, this, and_true]
  -- the localized identities
  have key : ∀ n : ℕ, ∫ ω, (An n).indicator 1 ω *
        F (stoppedValue U (fun ω => min (σ ω) (locTime B y n ω : WithTop ℝ≥0)) ω) ∂P =
      ∫ ω, (An n).indicator 1 ω *
        F (stoppedValue U (fun ω => min (ρ ω) (locTime B y n ω : WithTop ℝ≥0)) ω) ∂P := by
    intro n
    obtain ⟨M, hM⟩ := (isCompact_locK y n).exists_bound_of_continuousOn
      (hF.continuousOn.mono (locK_subset hy n))
    exact Girsanov.integral_mul_localDynkin_stopped_eq hB hBc Fl
      (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) (lipschitz_rsDrift hy)
      (norm_rsDrift_le hy) (stProc_integralEq hBc hy) isOpen_rsDom (isClosed_locCl n)
      (isClosed_locK y n) (locK_subset hy n) hF (fun x hx _ => hLF x (hy.trans_le hx.1) hx.1) n
      (fun ω t ht hs => stProc_mem_locK hBc hB0 hy hy5 n ω t ht hs)
      (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx)
      (hρ.min (hτn n)) (hσ.min (hτn n)) (fun ω => min_le_min (hρσ ω) le_rfl)
      (fun ω => min_le_right _ _) (measurable_const.indicator (hAnρ n)) (CY := 1)
      (fun ω => by by_cases h : ω ∈ An n <;> simp [h])
      (fun ω => by by_cases h : ω ∈ An n <;> simp [h])
  have h1 := tendsto_integral_loc hB hBc hBm hB0 hy hy5 hF hFm hC hdom hσ hσtop hAnm hAn
  have h2 := tendsto_integral_loc hB hBc hBm hB0 hy hy5 hF hFm hC hdom hρ
    (fun ω => (hρσ ω).trans (hσtop ω)) hAnm hAn
  have heq := tendsto_nhds_unique (h1.2.congr key) h2.2
  have hconv : ∀ τ : Ω → WithTop ℝ≥0, ∫ ω, A.indicator 1 ω * F (stoppedValue U τ ω) ∂P =
      ∫ ω in A, F (stoppedValue U τ ω) ∂P := by
    intro τ
    rw [← integral_indicator hAm]
    congr 1
    funext ω
    by_cases h : ω ∈ A <;> simp [h]
  rw [← hconv, ← hconv, heq]

omit hLF in
/-- The stopped test function is square integrable. -/
theorem memLp_stoppedValue {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (NonSwallow.bmFilt hBm) σ)
    (hσtop : ∀ ω, σ ω ≤ (topTime B y ω : WithTop ℝ≥0)) :
    MemLp (fun ω => F (stoppedValue (stProc B y) σ ω)) 2 P := by
  have h := (tendsto_integral_loc hB hBc hBm hB0 hy hy5 hF hFm hC hdom hσ hσtop (A := univ)
    (An := fun _ => univ) (fun _ => MeasurableSet.univ) (fun ω => Eventually.of_forall
      fun _ => Iff.rfl)).1
  simpa only [Set.indicator_univ, Pi.one_apply, one_mul] using h

/-- **Optional sampling at the height clock, `lintegral` form** (for a nonnegative test function). -/
theorem setLIntegral_stoppedValue_eq (hF0 : ∀ x : ℂ × ℝ, 0 < x.1.im → 0 ≤ F x)
    {ρ σ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime (NonSwallow.bmFilt hBm) ρ) (hσ : IsStoppingTime (NonSwallow.bmFilt hBm) σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω) (hσtop : ∀ ω, σ ω ≤ (topTime B y ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[hρ.measurableSpace] A) :
    ∫⁻ ω in A, ENNReal.ofReal (F (stoppedValue (stProc B y) σ ω)) ∂P =
      ∫⁻ ω in A, ENNReal.ofReal (F (stoppedValue (stProc B y) ρ ω)) ∂P := by
  have hnn : ∀ τ : Ω → WithTop ℝ≥0, ∀ ω, 0 ≤ F (stoppedValue (stProc B y) τ ω) := fun τ ω =>
    hF0 _ (hy.trans_le (le_im_stProc hBc hy _ ω))
  have hi : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (NonSwallow.bmFilt hBm) τ →
      (∀ ω, τ ω ≤ (topTime B y ω : WithTop ℝ≥0)) →
      Integrable (fun ω => F (stoppedValue (stProc B y) τ ω)) P := by
    intro τ hτ hτtop
    have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
    exact (memLp_stoppedValue hB hBc hBm hB0 hy hy5 hF hFm hC hdom hτ hτtop).integrable
      (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal (hi σ hσ hσtop).integrableOn
      (ae_of_all _ (hnn σ)),
    ← ofReal_integral_eq_lintegral_ofReal (hi ρ hρ (fun ω => (hρσ ω).trans (hσtop ω))).integrableOn
      (ae_of_all _ (hnn ρ)),
    setIntegral_stoppedValue_eq hB hBc hBm hB0 hy hy5 hF hFm hLF hC hdom hρ hσ hρσ hσtop hA]

/-- **Optional sampling with an unbounded weight.** For `ξ ≥ 0` measurable with respect to `𝓕_ρ`,
`∫ ξ F(U_σ) = ∫ ξ F(U_ρ)` (as `lintegral`s). -/
theorem lintegral_mul_stoppedValue_eq (hF0 : ∀ x : ℂ × ℝ, 0 < x.1.im → 0 ≤ F x)
    {ρ σ : Ω → WithTop ℝ≥0}
    (hρ : IsStoppingTime (NonSwallow.bmFilt hBm) ρ) (hσ : IsStoppingTime (NonSwallow.bmFilt hBm) σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω) (hσtop : ∀ ω, σ ω ≤ (topTime B y ω : WithTop ℝ≥0)) {ξ : Ω → ℝ≥0∞}
    (hξ : Measurable[hρ.measurableSpace] ξ) :
    ∫⁻ ω, ξ ω * ENNReal.ofReal (F (stoppedValue (stProc B y) σ ω)) ∂P =
      ∫⁻ ω, ξ ω * ENNReal.ofReal (F (stoppedValue (stProc B y) ρ ω)) ∂P := by
  have hm : hρ.measurableSpace ≤ mΩ := hρ.measurableSpace_le
  have hd : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (NonSwallow.bmFilt hBm) τ →
      Measurable fun ω => ENNReal.ofReal (F (stoppedValue (stProc B y) τ ω)) := fun τ hτ =>
    ENNReal.measurable_ofReal.comp (hFm.comp (measurable_stoppedValue_stProc hBc hBm hy hτ))
  have hμ : (P.withDensity fun ω => ENNReal.ofReal (F (stoppedValue (stProc B y) σ ω))).trim hm =
      (P.withDensity fun ω => ENNReal.ofReal (F (stoppedValue (stProc B y) ρ ω))).trim hm := by
    refine @Measure.ext _ hρ.measurableSpace _ _ fun S hS => ?_
    rw [trim_measurableSet_eq hm hS, trim_measurableSet_eq hm hS,
      withDensity_apply _ (hm S hS), withDensity_apply _ (hm S hS)]
    exact setLIntegral_stoppedValue_eq hB hBc hBm hB0 hy hy5 hF hFm hLF hC hdom hF0 hρ hσ hρσ
      hσtop hS
  have e : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime (NonSwallow.bmFilt hBm) τ →
      ∫⁻ ω, ξ ω * ENNReal.ofReal (F (stoppedValue (stProc B y) τ ω)) ∂P =
        ∫⁻ ω, ξ ω ∂((P.withDensity fun ω =>
          ENNReal.ofReal (F (stoppedValue (stProc B y) τ ω))).trim hm) := by
    intro τ hτ
    rw [lintegral_trim hm hξ, lintegral_withDensity_eq_lintegral_mul _ (hd τ hτ)
      (hξ.mono hm le_rfl)]
    congr 1
    funext ω
    simp only [Pi.mul_apply]
    ring
  rw [e σ hσ, e ρ hρ, hμ]

end Sampling

/-! ### The height reaches `√5` almost surely -/

theorem measurable_rsTest_aux {r : ℝ} : Measurable (rsTest 8 r) := by
  unfold rsTest
  fun_prop


/-- `cosh³ J / Y⁶ ≥ (1 + k²)^{3/2} / 125` in the cone `|X| ≥ k Y`, below height `√5`. -/
theorem rsTest_three_halves_ge {k : ℝ} (hk : 0 ≤ k) {x : ℂ × ℝ} (hY : 0 < x.1.im)
    (hY5 : x.1.im ≤ √5) (hcone : k * x.1.im ≤ |x.1.re|) :
    Real.exp (Real.log (1 + k ^ 2) * (3 / 2) - 3 * Real.log 5) ≤ rsTest 8 (3 / 2) x := by
  obtain ⟨⟨X, Y⟩, L⟩ := x
  simp only at hY hY5 hcone
  have hN : (1 + k ^ 2) * Y ^ 2 ≤ X ^ 2 + Y ^ 2 := by
    have h := sq_le_sq' (by linarith [abs_nonneg X, mul_nonneg hk hY.le]) hcone
    rw [sq_abs] at h
    nlinarith
  have hN0 : 0 < X ^ 2 + Y ^ 2 := by positivity
  have e : rsTest 8 (3 / 2) (⟨X, Y⟩, L) = Real.exp (Real.log Y * (-9) +
      Real.log (X ^ 2 + Y ^ 2) * (3 / 2)) := by
    simp only [rsTest, rsLam, rsZeta]
    rw [Real.rpow_def_of_pos hY, Real.rpow_def_of_pos hN0, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e]
  refine Real.exp_le_exp.2 ?_
  have h1 : Real.log (1 + k ^ 2) + 2 * Real.log Y ≤ Real.log (X ^ 2 + Y ^ 2) := by
    have hl : Real.log (Y ^ 2) = 2 * Real.log Y := by rw [Real.log_pow]; push_cast; ring
    rw [← hl, ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by simpa using hN)
  have h2 : Real.log Y ≤ Real.log 5 / 2 := by
    have := Real.log_le_log hY hY5
    rwa [Real.log_sqrt (by norm_num)] at this
  nlinarith

/-- **Almost surely the height reaches `√5`.** -/
theorem measure_not_reachesTop (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) (hy : 0 < y) (hy5 : y ≤ √5) :
    P {ω | ∀ s : ℝ≥0, (htZ (drive 8 B ω) y s).im < √5} = 0 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set Fl := NonSwallow.bmFilt hBm
  set U := stProc B y with hU_def
  set G := rsTest 8 (3 / 2) with hG_def
  set N₀ := {ω | ∀ s : ℝ≥0, (htZ (drive 8 B ω) y s).im < √5} with hN₀
  set c₀ := G (((y : ℂ) * I), 0)
  have hUc := continuous_stProc hBc hy (B := B)
  have hU0 : ∀ ω, U 0 ω = (((y : ℂ) * I), 0) := stProc_zero hBc hB0 hy
  -- for each natural `k`, a bound `P(N₀) ≤ c₀ · 125 / (1 + k²)`
  have hbound : ∀ k : ℕ, (P N₀).toReal ≤ c₀ / Real.exp (Real.log (1 + (k : ℝ) ^ 2) * (3 / 2) -
      3 * Real.log 5) := by
    intro k
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    set n : ℕ := ⌈5 * (1 + (k : ℝ) ^ 2) / 2 * Real.log (√5 / y)⌉₊ + 1 with hn
    set Cl : Set (ℂ × ℝ) := {x | (k : ℝ) * x.1.im ≤ |x.1.re|} ∪ {x | √5 ≤ x.1.im} with hCl
    set K : Set (ℂ × ℝ) := {x | y ≤ x.1.im ∧ x.1.im ≤ √5 ∧ |x.1.re| ≤ (k : ℝ) * x.1.im ∧
      |x.2| ≤ 2 * n / y ^ 2} with hK
    have him : Continuous fun x : ℂ × ℝ => x.1.im := Complex.continuous_im.comp continuous_fst
    have hre : Continuous fun x : ℂ × ℝ => |x.1.re| :=
      continuous_abs.comp (Complex.continuous_re.comp continuous_fst)
    have hClc : IsClosed Cl :=
      (isClosed_le (continuous_const.mul him) hre).union (isClosed_le continuous_const him)
    have hKc : IsClosed K :=
      (isClosed_le continuous_const him).inter ((isClosed_le him continuous_const).inter
        ((isClosed_le hre (continuous_const.mul him)).inter
          (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)))
    have hKsub : K ⊆ locK y (⌈(k : ℝ) * √5⌉₊ + n) := by
      intro x hx
      refine ⟨hx.1, hx.2.1, ?_, ?_⟩
      · have : |x.1.re| ≤ (k : ℝ) * √5 := hx.2.2.1.trans (mul_le_mul_of_nonneg_left hx.2.1 hk)
        push_cast
        linarith [Nat.le_ceil ((k : ℝ) * √5), (n.cast_nonneg : (0 : ℝ) ≤ n)]
      · refine hx.2.2.2.trans ?_
        push_cast
        have : (n : ℝ) ≤ ⌈(k : ℝ) * √5⌉₊ + n := by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ⌈(k : ℝ) * √5⌉₊)]
        gcongr
    have hKcpt : IsCompact K := (isCompact_locK y _).of_isClosed_subset hKc hKsub
    have hKO : K ⊆ rsDom := fun x hx => hy.trans_le hx.1
    obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn
      ((contDiffOn_rsTest 8 (3 / 2)).continuousOn.mono hKO)
    have hUK : ∀ ω (t : ℝ≥0), t ≤ n → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K := by
      intro ω t ht hs
      refine ⟨le_im_stProc hBc hy t ω, ?_, ?_, ?_⟩
      rotate_right
      · refine (abs_snd_stProc_le hBc hy t ω).trans ?_
        have : (t : ℝ) ≤ n := by exact_mod_cast ht
        gcongr
      all_goals rcases eq_or_ne t 0 with h0 | hpos'
      · rw [h0, hU0 ω]; simpa using hy5
      · have hcl : IsClosed {s : ℝ≥0 | (U s ω).1.im ≤ √5} :=
          isClosed_le (Complex.continuous_im.comp (continuous_fst.comp (hUc ω))) continuous_const
        have hsub : Iio t ⊆ {s : ℝ≥0 | (U s ω).1.im ≤ √5} := fun s hst => by
          have := hs s hst
          simp only [hCl, mem_union, mem_ofPred_eq, not_or, not_le] at this
          exact this.2.le
        have := hcl.closure_subset_iff.2 hsub
        rw [closure_Iio' (a := t) ⟨0, pos_iff_ne_zero.2 hpos'⟩] at this
        exact this (le_refl t)
      · rw [h0, hU0 ω]; simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, abs_zero, mul_im, add_zero]; exact mul_nonneg hk hy.le
      · have hcl : IsClosed {s : ℝ≥0 | |(U s ω).1.re| ≤ (k : ℝ) * (U s ω).1.im} :=
          isClosed_le (continuous_abs.comp (Complex.continuous_re.comp (continuous_fst.comp (hUc ω))))
            (continuous_const.mul (Complex.continuous_im.comp (continuous_fst.comp (hUc ω))))
        have hsub : Iio t ⊆ {s : ℝ≥0 | |(U s ω).1.re| ≤ (k : ℝ) * (U s ω).1.im} := fun s hst => by
          have := hs s hst
          simp only [hCl, mem_union, mem_ofPred_eq, not_or, not_le] at this
          exact this.1.le
        have := hcl.closure_subset_iff.2 hsub
        rw [closure_Iio' (a := t) ⟨0, pos_iff_ne_zero.2 hpos'⟩] at this
        exact this (le_refl t)
    set τ : Ω → ℝ≥0 := fun ω => hittingBtwn U Cl 0 n ω with hτ_def
    have hτ : IsStoppingTime Fl (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) :=
      ItoLite.isStoppingTime_hittingBtwn_of_isClosed (measurable_stProc hBc hBm hy) hUc hClc n
    have heq := Girsanov.integral_mul_localDynkin_stopped_eq hB hBc Fl
      (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) (lipschitz_rsDrift hy)
      (norm_rsDrift_le hy) (stProc_integralEq hBc hy) isOpen_rsDom hClc hKc hKO
      (contDiffOn_rsTest 8 (3 / 2))
      (fun x hx _ => dynkinGen_rsTest (by norm_num) (3 / 2) (hy.trans_le hx.1) hx.1) n hUK
      (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx)
      (isStoppingTime_const Fl 0) hτ (fun ω => bot_le) (fun ω => le_rfl)
      (Y := fun _ => (1 : ℝ)) measurable_const (fun _ => zero_le_one) (CY := 1) (fun _ => le_rfl)
    rw [← hU_def, ← hG_def] at heq
    simp only [one_mul, stoppedValue_const] at heq
    have hval : ∀ ω, stoppedValue U (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) ω = U (τ ω) ω :=
      fun ω => rfl
    simp only [hval, hU0, integral_const, probReal_univ, one_smul] at heq
    -- on `N₀`, the flow leaves the cone before time `n`
    set c := Real.exp (Real.log (1 + (k : ℝ) ^ 2) * (3 / 2) - 3 * Real.log 5) with hc
    have hsubset : N₀ ⊆ {ω | c ≤ G (U (τ ω) ω)} := by
      intro ω hω
      have hW := continuous_drive8 hBc ω
      have hex : ∃ j ∈ Icc (0 : ℝ≥0) n, U j ω ∈ Cl := by
        by_contra hne
        push Not at hne
        have hcone : ∀ r ∈ Icc (0 : ℝ) n, |(htZ (drive 8 B ω) y r).re| ≤
            (k : ℝ) * (htZ (drive 8 B ω) y r).im ∧ (htZ (drive 8 B ω) y r).im ≤ √5 := by
          intro r hr
          have h := hne r.toNNReal ⟨bot_le, by
            rw [← NNReal.coe_le_coe, Real.coe_toNNReal r hr.1]; exact_mod_cast hr.2⟩
          simp only [hCl, mem_union, mem_ofPred_eq, not_or, not_le] at h
          rw [stProc_fst, Real.coe_toNNReal r hr.1] at h
          exact ⟨h.1.le, h.2.le⟩
        have hgrow := im_ge_of_cone hW hy (by positivity : (0 : ℝ) ≤ n) hcone
        have hlt := hω (n : ℝ≥0)
        have h5 : √5 ≤ y * Real.exp (2 * (n : ℝ) / (5 * (1 + (k : ℝ) ^ 2))) := by
          have hpos : 0 < 5 * (1 + (k : ℝ) ^ 2) := by positivity
          have hn' : 5 * (1 + (k : ℝ) ^ 2) / 2 * Real.log (√5 / y) ≤ n := by
            have := Nat.le_ceil (5 * (1 + (k : ℝ) ^ 2) / 2 * Real.log (√5 / y))
            simp only [hn]; push_cast; linarith
          have hlog : Real.log (√5 / y) ≤ 2 * (n : ℝ) / (5 * (1 + (k : ℝ) ^ 2)) := by
            rw [le_div_iff₀ hpos]; nlinarith
          calc √5 = y * (√5 / y) := by field_simp
            _ = y * Real.exp (Real.log (√5 / y)) := by
                rw [Real.exp_log (div_pos (by positivity) hy)]
            _ ≤ _ := by gcongr
        have : ((n : ℝ≥0) : ℝ) = (n : ℝ) := by push_cast; rfl
        rw [this] at hlt
        linarith
      have hmem := Williams.mem_hittingBtwn_of_isClosed hUc hClc hex
      have hYlt : (U (τ ω) ω).1.im < √5 := hω (τ ω)
      rcases hmem with h | h
      · exact rsTest_three_halves_ge hk (hy.trans_le (le_im_stProc hBc hy _ ω)) hYlt.le h
      · exact absurd h (not_le.2 hYlt)
    have hGi : Integrable (fun ω => G (U (τ ω) ω)) P := by
      refine Integrable.of_bound (C := M) ?_ (ae_of_all _ fun ω => ?_)
      · have := measurable_stoppedValue_stProc hBc hBm hy hτ
        exact (measurable_rsTest_aux.comp this).aestronglyMeasurable
      · have hfin : τ ω ≤ n := hittingBtwn_le ω
        exact hM _ (hUK ω (τ ω) hfin fun s hs => notMem_of_lt_hittingBtwn hs bot_le)
    have hGnn : 0 ≤ᵐ[P] fun ω => G (U (τ ω) ω) := ae_of_all _ fun ω => by
      have := hy.trans_le (le_im_stProc hBc hy (τ ω) ω)
      simp only [G, rsTest]
      have h1 := Real.rpow_nonneg (show (0 : ℝ) ≤ (U (τ ω) ω).1.re ^ 2 + (U (τ ω) ω).1.im ^ 2 by
        positivity) (3 / 2)
      have h2 := Real.rpow_nonneg this.le (rsZeta 8 (3 / 2) - 2 * (3 / 2))
      positivity
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hGnn hGi c
    have hcpos : 0 < c := Real.exp_pos _
    rw [heq] at hmarkov
    rw [le_div_iff₀ hcpos]
    calc (P N₀).toReal * c ≤ (P {ω | c ≤ G (U (τ ω) ω)}).toReal * c := by
          gcongr
          exact measure_ne_top _ _
      _ = c * (P {ω | c ≤ G (U (τ ω) ω)}).toReal := mul_comm _ _
      _ ≤ c₀ := hmarkov
  -- let `k → ∞`
  have hlim : Tendsto (fun k : ℕ => c₀ / Real.exp (Real.log (1 + (k : ℝ) ^ 2) * (3 / 2) -
      3 * Real.log 5)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => Real.exp (Real.log (1 + (k : ℝ) ^ 2) * (3 / 2) -
        3 * Real.log 5)) atTop atTop := by
      refine Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _ ?_)
      refine Tendsto.atTop_mul_const (by norm_num) ?_
      refine Real.tendsto_log_atTop.comp ?_
      refine tendsto_atTop_add_const_left _ _ ?_
      exact (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact h1.const_div_atTop c₀
  have h0 : (P N₀).toReal ≤ 0 := ge_of_tendsto' hlim hbound
  have := (ENNReal.toReal_eq_zero_iff _).1 (le_antisymm h0 ENNReal.toReal_nonneg)
  rcases this with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

end InteractingSLE.SLE8.ChangeOfMeasure
