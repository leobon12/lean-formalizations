import QuantumZipper.Proofs.Thm11.FieldMartingales
import QuantumZipper.Proofs.Thm11.CharFunRhs
import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# Theorem 1.1, MF-6 (MAIN-MART)

Blueprint `blueprint/THM11_BLUEPRINT.md`, §6, node MF-6.  For `κ ∈ (0,4]`, `T > 0`, a Brownian
motion `B` and `ρ ∈ C_c^∞(ℍ)`:

`E exp(i (𝔥_T, ρ) − E_T(ρ)/2) = exp(i (𝔥₀, ρ) − E₀(ρ)/2)`,

with `(𝔥_T, ρ) = ∫ ρ hTfwd`, `E_T(ρ) = CharFunRhs.Efwd`, `(𝔥₀, ρ) = ∫ ρ h0fwd` and
`E₀(ρ) = ∬ ρρ G` (`main_mart`).

Proof: MF-5 (`FieldMart.integral_exp_fieldX_fieldV`) along `δ_m = δ₀/(m+2) ↓ 0`, `c = δ/2`.
For `a ∈ ℍ \ K_T` the frozen field and kernel eventually equal `hTfwd` and `G(f_T a, f_T b)`
(`eventually_frozen_true`); `K_T` is Lebesgue-null (DF-2); domination by
`|ρ|(2π/√κ + 2|χ| S_T)` (`abs_frozenField_le_clock`) and by `|ρ||ρ| G`; dominated convergence in
`a`, then on `Ω` (bound `exp(½∬|ρ||ρ|G)`).

The clock integrability `∫_{D_T} |ρ| S_T < ∞` (needed only if `χ ≠ 0`, i.e. `κ < 4`) is taken as
the hypothesis `hclock`; it is the content of `ClockIntegrable.ae_lintegral_clock_lt_top`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace MainMart

open FwdHolo FwdClock FrozenMart FieldMart NonSwallow

/-! ## A. Deterministic facts for a fixed path -/

section Det

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- A test function on `ℍ` vanishes on `{Im < δ₀}` for some `δ₀ > 0`. -/
theorem exists_im_pos_of_testFun (ρ : TestFun H) : ∃ δ₀ > 0, ∀ a : ℂ, a.im < δ₀ → ρ.1 a = 0 := by
  obtain ⟨-, hρc, hρH⟩ := ρ.2
  rcases (tsupport ρ.1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun a _ => ?_⟩
    by_contra h
    have := subset_tsupport _ h
    rw [he] at this
    exact this
  · obtain ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hρc hne Complex.continuous_im.continuousOn
    refine ⟨z.im, hρH hz, fun a ha => ?_⟩
    by_contra h
    have := isMinOn_iff.1 hmin a (subset_tsupport _ h)
    linarith

/-- For `a ∈ ℍ \ K_T` and all small `δ` (and `c ≤ δ`): the freezing time is `T` and the tamed
flow and argument process are the true ones on `[0,T]`. -/
theorem eventually_frozen_true (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ} (Tn : ℝ≥0) (ω : Ω)
    {a : ℂ} (ha : a ∈ H \ fwdHull (drive κ B ω) Tn) :
    ∃ δs > 0, ∀ δ c : ℝ, 0 < c → c ≤ δ → δ ≤ δs →
      frozenTime κ c δ Tn B a ω = Tn ∧ ∀ t ∈ Icc (0 : ℝ) Tn,
        tamedZ (drive κ B ω) c a t = fwdMap (drive κ B ω) t a ∧
        tamedA (drive κ B ω) c a t = (logDerivFwd (drive κ B ω) t a).im := by
  set W := drive κ B ω with hWdef
  have hW : Continuous W := continuous_drive_path hBc ω
  have hT := Tn.coe_nonneg
  have ha0 : 0 < a.im := ha.1
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT ha.1 ha.2
  have hfu : ∀ t ∈ Icc (0 : ℝ) Tn, fwdMap W t a = u t := fun t ht => fwdMap_eq hW ha0 hu ht
  obtain ⟨hanti, hpos⟩ := im_isForwardSol_le hW ha0 hu
  have hTm : (Tn : ℝ) ∈ Icc (0 : ℝ) Tn := ⟨hT, le_rfl⟩
  set m := (u Tn).im with hm
  have hm0 : 0 < m := hpos _ hTm
  have hge : ∀ t ∈ Icc (0 : ℝ) Tn, m ≤ (u t).im := fun t ht => hanti ht hTm ht.2
  refine ⟨m / 2, by positivity, fun δ c hc hcδ hδ => ?_⟩
  have hcm : ∀ t ∈ Icc (0 : ℝ) Tn, c ≤ (u t).im := fun t ht => by linarith [hge t ht]
  have htz := tamedZ_eq_of_isForwardSol hW hc hT hu hcm
  have him : ∀ t ∈ Icc (0 : ℝ) Tn, c ≤ (tamedZ W c a t).im := fun t ht => by
    rw [htz t ht]; exact hcm t ht
  have htA := im_logDerivFwd_eq_tamedA hW hc hT ha0 him
  refine ⟨?_, fun t ht => ⟨by rw [htz t ht, hfu t ht], (htA t ht).symm⟩⟩
  unfold frozenTime hittingBtwn
  rw [if_neg]
  rintro ⟨j, hj, hjs⟩
  have hj' : (j : ℝ) ∈ Icc (0 : ℝ) Tn := ⟨j.coe_nonneg, by exact_mod_cast hj.2⟩
  have h1 : (tamedZ W c a j).im ≤ δ := hjs
  rw [htz _ hj'] at h1
  linarith [hge _ hj']

theorem frozenField_eq_hTfwd {κ c δ : ℝ} (Tn : ℝ≥0) (ω : Ω) {a : ℂ}
    (ha : a ∈ H \ fwdHull (drive κ B ω) Tn) (hσ : frozenTime κ c δ Tn B a ω = Tn)
    (hZ : tamedZ (drive κ B ω) c a Tn = fwdMap (drive κ B ω) Tn a)
    (hA : tamedA (drive κ B ω) c a Tn = (logDerivFwd (drive κ B ω) Tn a).im) :
    frozenField κ c δ Tn B a Tn ω = hTfwd κ (drive κ B ω) Tn a := by
  simp only [frozenField, fzPhi, fzU, fzZ, fzA, hσ, min_self]
  rw [hZ, hA, hTfwd, if_pos ha]

theorem frozenKernel_eq_greenH {κ c δ : ℝ} (Tn : ℝ≥0) (ω : Ω) {a b : ℂ}
    (hσa : frozenTime κ c δ Tn B a ω = Tn) (hσb : frozenTime κ c δ Tn B b ω = Tn)
    (hZa : tamedZ (drive κ B ω) c a Tn = fwdMap (drive κ B ω) Tn a)
    (hZb : tamedZ (drive κ B ω) c b Tn = fwdMap (drive κ B ω) Tn b) :
    frozenKernel κ c δ Tn B a b Tn ω =
      greenH (fwdMap (drive κ B ω) Tn a) (fwdMap (drive κ B ω) Tn b) := by
  simp only [frozenKernel, fzZ, hσa, hσb, min_self]
  rw [hZa, hZb]

/-- `Im f_T(a) > 0` and the clock formula `S_T(a) = ½ log(Im a / Im f_T(a))` on `ℍ \ K_T`. -/
theorem im_fwdMap_pos_and_clock {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ}
    (ha : a ∈ H \ fwdHull W T) :
    0 < (fwdMap W T a).im ∧ fwdClock W T a = 1 / 2 * Real.log (a.im / (fwdMap W T a).im) := by
  have ha0 : 0 < a.im := ha.1
  have hsol := exists_isForwardSol_of_not_mem_fwdHull hT ha.1 ha.2
  have e := im_fwdMap_eq_clock hW ha0 hsol ⟨hT, le_rfl⟩
  refine ⟨by rw [e]; exact mul_pos ha0 (Real.exp_pos _), ?_⟩
  rw [e, div_mul_cancel_left₀ ha0.ne', Real.log_inv, Real.log_exp]
  ring

theorem intervalIntegrable_clock {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {a : ℂ}
    (ha : a ∈ H \ fwdHull W T) :
    IntervalIntegrable (fun s => 1 / ‖fwdMap W s a‖ ^ 2) volume 0 T := by
  have ha0 : 0 < a.im := ha.1
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT ha.1 ha.2
  obtain ⟨-, hpos⟩ := im_isForwardSol_le hW ha0 hu
  have hne : ∀ s ∈ Icc (0 : ℝ) T, fwdMap W s a ≠ 0 := fun s hs h => by
    have := hpos s hs
    rw [← fwdMap_eq hW ha0 hu hs, h, Complex.zero_im] at this
    exact lt_irrefl _ this
  refine ContinuousOn.intervalIntegrable_of_Icc hT ?_
  exact continuousOn_const.div ((continuousOn_fwdMap_time hW hT ha).norm.pow 2)
    fun s hs => pow_ne_zero _ (norm_ne_zero_iff.2 (hne s hs))

/-- **Domination (FD-1).** On `ℍ \ K_T`, `|𝔥^δ_T(a)| ≤ 2π/√κ + 2|χ| S_T(a)`. -/
theorem abs_frozenField_le_clock (hBc : ∀ ω, Continuous (B · ω)) {κ c δ : ℝ} (hκ : 0 < κ)
    (hc : 0 < c) (hcδ : c ≤ δ) (Tn : ℝ≥0) (ω : Ω) {a : ℂ}
    (ha : a ∈ H \ fwdHull (drive κ B ω) Tn) (hδa : δ ≤ a.im) :
    |frozenField κ c δ Tn B a Tn ω| ≤
      2 * Real.pi / Real.sqrt κ + 2 * |chiC κ| * fwdClock (drive κ B ω) Tn a := by
  set W := drive κ B ω with hWdef
  have hW : Continuous W := continuous_drive_path hBc ω
  have hT := Tn.coe_nonneg
  have ha0 : 0 < a.im := ha.1
  set σ := frozenTime κ c δ Tn B a ω with hσ
  set u : ℝ≥0 := min Tn σ with hu
  have huσ : u ≤ σ := min_le_right _ _
  have huT : (u : ℝ) ≤ Tn := by exact_mod_cast min_le_left Tn σ
  have him : ∀ s ∈ Icc (0 : ℝ) u, c ≤ (tamedZ W c a s).im := by
    intro s hs
    have hs' : s.toNNReal ≤ σ :=
      (show s.toNNReal ≤ u by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2).trans
        huσ
    have h := im_fzZ_ge_of_le_frozenTime (κ := κ) hBc hc hδa ω hs'
    unfold fzZ at h
    rw [Real.coe_toNNReal _ hs.1] at h
    exact hcδ.trans h
  have hA := im_logDerivFwd_eq_tamedA hW hc u.coe_nonneg ha0 him u ⟨u.coe_nonneg, le_rfl⟩
  have hsol : ∃ v, IsForwardSol W a u v := ⟨_, isForwardSol_tamedZ hW hc u.coe_nonneg him⟩
  have hAb := abs_im_logDerivFwd_le hW ha0 hsol ⟨u.coe_nonneg, le_rfl⟩
  have hmono : fwdClock W u a ≤ fwdClock W Tn a := by
    unfold fwdClock
    exact intervalIntegral.integral_mono_interval le_rfl u.coe_nonneg huT
      (Eventually.of_forall fun s => by simp only [Pi.zero_apply]; positivity)
      (intervalIntegrable_clock hW hT ha)
  have hs : 0 ≤ 2 / Real.sqrt κ := by positivity
  show |h0fwd κ (tamedZ W c a u) - chiC κ * tamedA W c a u| ≤ _
  rw [← hA]
  calc |h0fwd κ (tamedZ W c a u) - chiC κ * (logDerivFwd W u a).im|
      ≤ |h0fwd κ (tamedZ W c a u)| + |chiC κ * (logDerivFwd W u a).im| := abs_sub _ _
    _ = 2 / Real.sqrt κ * |Complex.arg (tamedZ W c a u)| + |chiC κ| * |(logDerivFwd W u a).im| := by
        rw [h0fwd, abs_mul, abs_mul, abs_neg, abs_of_nonneg hs]
    _ ≤ 2 / Real.sqrt κ * Real.pi + |chiC κ| * (2 * fwdClock W Tn a) :=
        add_le_add (mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) hs)
          (mul_le_mul_of_nonneg_left (hAb.trans (by linarith)) (abs_nonneg _))
    _ = _ := by ring

end Det

/-! ## B. Pathwise limits `δ ↓ 0` -/

section Limits

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- `X^{δ_n}_T(ω) → ∫ ρ hTfwd` for a path with Lebesgue-null hull and integrable clock. -/
theorem tendsto_fieldX (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ}
    (hκ : 0 < κ) {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (hρδ₀ : ∀ a : ℂ, a.im < δ₀ → ρ a = 0) {δn : ℕ → ℝ} (hδpos : ∀ n, 0 < δn n)
    (hδle : ∀ n, δn n ≤ δ₀) (hδlim : Tendsto δn atTop (𝓝 0)) (Tn : ℝ≥0) (ω : Ω)
    (hnull : volume (fwdHull (drive κ B ω) Tn) = 0)
    (hclock : chiC κ = 0 ∨ ∫⁻ a in H \ fwdHull (drive κ B ω) Tn,
      ENNReal.ofReal |ρ a| * ENNReal.ofReal (fwdClock (drive κ B ω) Tn a) < ⊤) :
    Tendsto (fun n => fieldX κ (δn n / 2) (δn n) Tn B ρ Tn ω) atTop
      (𝓝 (∫ z, ρ z * hTfwd κ (drive κ B ω) Tn z)) := by
  set W := drive κ B ω with hWdef
  have hW : Continuous W := continuous_drive_path hBc ω
  have hT := Tn.coe_nonneg
  set D := H \ fwdHull W Tn with hD
  have hDo : IsOpen D := isOpen_compl_fwdHull hW hT
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  set C1 : ℝ := 2 * Real.pi / Real.sqrt κ with hC1
  have hC10 : 0 ≤ C1 := by positivity
  have hS0 : ∀ a, 0 ≤ fwdClock W Tn a := fun a =>
    intervalIntegral.integral_nonneg hT fun _ _ => by positivity
  set g : ℂ → ℝ := D.indicator (fun a => |ρ a| * (C1 + 2 * |chiC κ| * fwdClock W Tn a)) with hg
  have hg0 : ∀ a, 0 ≤ g a := fun a => indicator_nonneg (fun a _ => by
    have := hS0 a; positivity) a
  have hgi : Integrable g := by
    have hsplit : g = D.indicator (fun a => |ρ a| * C1) +
        D.indicator (fun a => 2 * |chiC κ| * (|ρ a| * fwdClock W Tn a)) := by
      funext a
      by_cases h : a ∈ D <;> simp [hg, h]
      ring
    rw [hsplit]
    refine ((hρi.abs.mul_const C1).indicator hDo.measurableSet).add ?_
    rcases hclock with h0 | hfin
    · simp [h0]
    · refine (integrable_indicator_iff hDo.measurableSet).2 (Integrable.const_mul ?_ _)
      refine ⟨?_, ?_⟩
      · have hfc : ContinuousOn (fwdMap W Tn) D := (differentiableOn_fwdMap hW hT).continuousOn
        have hpos : ∀ a ∈ D, 0 < (fwdMap W Tn a).im := fun a ha =>
          (im_fwdMap_pos_and_clock hW hT ha).1
        have hc : ContinuousOn
            (fun a => |ρ a| * (1 / 2 * Real.log (a.im / (fwdMap W Tn a).im))) D :=
          (continuous_abs.comp hρc).continuousOn.mul (continuousOn_const.mul
            ((Complex.continuous_im.continuousOn.div
              (Complex.continuous_im.comp_continuousOn hfc) (fun a ha => (hpos a ha).ne')).log
              (fun a ha => (div_pos ha.1 (hpos a ha)).ne')))
        exact (hc.congr (fun a ha => by rw [(im_fwdMap_pos_and_clock hW hT ha).2])).aestronglyMeasurable
          hDo.measurableSet
      · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun a => mul_nonneg (abs_nonneg _) (hS0 a))]
        refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun a => ?_)) hfin
        exact ENNReal.ofReal_mul (abs_nonneg _)
  have hmeasF : ∀ n, AEStronglyMeasurable
      (fun a => ρ a * frozenField κ (δn n / 2) (δn n) Tn B a Tn ω) volume := fun n =>
    (hρc.measurable.mul ((measurable_frozenField_amb (κ := κ) (δ := δn n) hBc (bmFilt hBm)
      (bmFilt_adapted hBm) (by linarith [hδpos n] : 0 < δn n / 2) Tn Tn).comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hKae : ∀ᵐ a ∂(volume : Measure ℂ), a ∉ fwdHull W Tn := by
    rw [ae_iff]; simpa using hnull
  refine tendsto_integral_of_dominated_convergence g hmeasF hgi (fun n => ?_) ?_
  · filter_upwards [hKae] with a haK
    by_cases hρa : ρ a = 0
    · simp [hρa, hg0 a]
    have hIm : δ₀ ≤ a.im := not_lt.1 fun h => hρa (hρδ₀ a h)
    have haD : a ∈ D := ⟨hδ₀.trans_le hIm, haK⟩
    rw [Real.norm_eq_abs, abs_mul, hg, indicator_of_mem haD]
    exact mul_le_mul_of_nonneg_left (abs_frozenField_le_clock hBc hκ
      (by linarith [hδpos n]) (by linarith [hδpos n]) Tn ω haD ((hδle n).trans hIm))
      (abs_nonneg _)
  · filter_upwards [hKae] with a haK
    by_cases hρa : ρ a = 0
    · simp [hρa]
    have hIm : δ₀ ≤ a.im := not_lt.1 fun h => hρa (hρδ₀ a h)
    have haD : a ∈ D := ⟨hδ₀.trans_le hIm, haK⟩
    obtain ⟨δs, hδs, hev⟩ := eventually_frozen_true (κ := κ) hBc Tn ω haD
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hδlim.eventually (eventually_le_nhds hδs)] with n hn
    obtain ⟨hσ, hZA⟩ := hev (δn n) (δn n / 2) (by linarith [hδpos n]) (by linarith [hδpos n]) hn
    have hTm : (Tn : ℝ) ∈ Icc (0 : ℝ) Tn := ⟨hT, le_rfl⟩
    rw [frozenField_eq_hTfwd Tn ω haD hσ (hZA _ hTm).1 (hZA _ hTm).2]

/-- `V^{δ_n}_T(ω) → E_T(ρ)` (`CharFunRhs.Efwd`) for a path with Lebesgue-null hull. -/
theorem tendsto_fieldV (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω)) {κ : ℝ}
    {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) (hρδ₀ : ∀ a : ℂ, a.im < δ₀ → ρ a = 0) {δn : ℕ → ℝ} (hδpos : ∀ n, 0 < δn n)
    (hδle : ∀ n, δn n ≤ δ₀) (hδlim : Tendsto δn atTop (𝓝 0)) (Tn : ℝ≥0) (ω : Ω)
    (hnull : volume (fwdHull (drive κ B ω) Tn) = 0) :
    Tendsto (fun n => fieldV κ (δn n / 2) (δn n) Tn B ρ Tn ω) atTop
      (𝓝 (CharFunRhs.Efwd (drive κ B ω) Tn ρ)) := by
  set W := drive κ B ω with hWdef
  have hT := Tn.coe_nonneg
  set D := H \ fwdHull W Tn with hD
  set K := fwdHull W Tn with hK
  set Lf : ℂ × ℂ → ℝ := fun p => ρ p.1 * ρ p.2 * D.indicator (1 : ℂ → ℝ) p.1 *
    D.indicator (1 : ℂ → ℝ) p.2 * greenH (fwdMap W Tn p.1) (fwdMap W Tn p.2) with hLf
  set bnd : ℂ × ℂ → ℝ := fun p => |ρ p.1| * |ρ p.2| * greenH p.1 p.2 with hbnd
  have hbi : Integrable bnd ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
    integrable_rho_rho_greenH hρc hρs hδ₀ hρδ₀
  have hmeasF : ∀ n, AEStronglyMeasurable (fun p : ℂ × ℂ =>
      ρ p.1 * ρ p.2 * frozenKernel κ (δn n / 2) (δn n) Tn B p.1 p.2 Tn ω)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := fun n =>
    (((hρc.measurable.comp measurable_fst).mul (hρc.measurable.comp measurable_snd)).mul
      ((measurable_frozenKernel_amb (κ := κ) (δ := δn n) hBc (bmFilt hBm) (bmFilt_adapted hBm)
        (by linarith [hδpos n] : 0 < δn n / 2) Tn Tn).comp
          (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)),
      ‖ρ p.1 * ρ p.2 * frozenKernel κ (δn n / 2) (δn n) Tn B p.1 p.2 Tn ω‖ ≤ bnd p := by
    intro n
    filter_upwards [ae_ne_diag] with p hp
    by_cases h1 : ρ p.1 = 0
    · simp [hbnd, h1]
    by_cases h2 : ρ p.2 = 0
    · simp [hbnd, h2]
    have i1 : δn n ≤ p.1.im := (hδle n).trans (not_lt.1 fun h => h1 (hρδ₀ _ h))
    have i2 : δn n ≤ p.2.im := (hδle n).trans (not_lt.1 fun h => h2 (hρδ₀ _ h))
    have hc : 0 < δn n / 2 := by linarith [hδpos n]
    have hcδ : δn n / 2 ≤ δn n := by linarith [hδpos n]
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (frozenKernel_nonneg (κ := κ) hBc hc hcδ i1 i2 hp Tn Tn ω)]
    exact mul_le_mul_of_nonneg_left (frozenKernel_le_greenH (κ := κ) hBc hc hcδ i1 i2 hp Tn Tn ω)
      (by positivity)
  have hgood : ∀ᵐ p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)), p.1 ≠ p.2 ∧ p.1 ∉ K ∧ p.2 ∉ K := by
    have h1 : ∀ᵐ p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)), p.1 ∉ K := by
      rw [ae_iff]
      have e : {p : ℂ × ℂ | ¬ p.1 ∉ K} = K ×ˢ univ := by ext p; simp
      rw [e, Measure.prod_prod, hnull, zero_mul]
    have h2 : ∀ᵐ p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)), p.2 ∉ K := by
      rw [ae_iff]
      have e : {p : ℂ × ℂ | ¬ p.2 ∉ K} = univ ×ˢ K := by ext p; simp
      rw [e, Measure.prod_prod, hnull, mul_zero]
    filter_upwards [ae_ne_diag, h1, h2] with p a b c using ⟨a, b, c⟩
  have hlim : ∀ᵐ p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)), Tendsto
      (fun n => ρ p.1 * ρ p.2 * frozenKernel κ (δn n / 2) (δn n) Tn B p.1 p.2 Tn ω) atTop
      (𝓝 (Lf p)) := by
    filter_upwards [hgood] with p hp
    obtain ⟨hne, h1K, h2K⟩ := hp
    by_cases h1 : ρ p.1 = 0
    · simp [hLf, h1]
    by_cases h2 : ρ p.2 = 0
    · simp [hLf, h2]
    have hD1 : p.1 ∈ D := ⟨hδ₀.trans_le (not_lt.1 fun h => h1 (hρδ₀ _ h)), h1K⟩
    have hD2 : p.2 ∈ D := ⟨hδ₀.trans_le (not_lt.1 fun h => h2 (hρδ₀ _ h)), h2K⟩
    obtain ⟨δ1, hδ1, hev1⟩ := eventually_frozen_true (κ := κ) hBc Tn ω hD1
    obtain ⟨δ2, hδ2, hev2⟩ := eventually_frozen_true (κ := κ) hBc Tn ω hD2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hδlim.eventually (eventually_le_nhds hδ1),
      hδlim.eventually (eventually_le_nhds hδ2)] with n hn1 hn2
    obtain ⟨hσ1, hZ1⟩ :=
      hev1 (δn n) (δn n / 2) (by linarith [hδpos n]) (by linarith [hδpos n]) hn1
    obtain ⟨hσ2, hZ2⟩ :=
      hev2 (δn n) (δn n / 2) (by linarith [hδpos n]) (by linarith [hδpos n]) hn2
    have hTm : (Tn : ℝ) ∈ Icc (0 : ℝ) Tn := ⟨hT, le_rfl⟩
    simp only [hLf, indicator_of_mem hD1, indicator_of_mem hD2, Pi.one_apply, mul_one]
    rw [frozenKernel_eq_greenH Tn ω hσ1 hσ2 (hZ1 _ hTm).1 (hZ2 _ hTm).1]
  have hLi : Integrable Lf ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    refine Integrable.mono' hbi (aestronglyMeasurable_of_tendsto_ae atTop hmeasF hlim) ?_
    filter_upwards [hlim, ae_all_iff.2 hbound] with p hp hb
    exact le_of_tendsto' hp.norm hb
  have hEq : ∫ p, Lf p ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) = CharFunRhs.Efwd W Tn ρ := by
    rw [integral_prod Lf hLi]
    rfl
  rw [← hEq]
  exact tendsto_integral_of_dominated_convergence bnd hmeasF hbi hbound hlim

end Limits

/-! ## C. MF-6 -/

theorem re_I_mul_sub_div_two (x v : ℝ) : (I * (x : ℂ) - (v : ℂ) / 2).re = -(v / 2) := by
  simp

/-- **MF-6 (MAIN-MART).** For `κ ∈ (0,4]`, `T > 0`, a Brownian motion `B` and `ρ ∈ C_c^∞(ℍ)`,
`E exp(i ∫ ρ 𝔥_T − E_T(ρ)/2) = exp(i ∫ ρ 𝔥₀ − ∬ ρρ G / 2)`.  The hypothesis `hclock`
(integrability of the clock against `|ρ|` on `ℍ \ K_T`, only needed when `χ ≠ 0`) is
`ClockIntegrable.ae_lintegral_clock_lt_top`. -/
theorem main_mart {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {T : ℝ} (hT : 0 < T)
    (ρ : TestFun H)
    (hclock : ∀ᵐ ω ∂P, chiC κ = 0 ∨ ∫⁻ a in H \ fwdHull (drive κ B ω) T,
      ENNReal.ofReal |ρ.1 a| * ENNReal.ofReal (fwdClock (drive κ B ω) T a) < ⊤) :
    ∫ ω, cexp (I * ((∫ z, ρ.1 z * hTfwd κ (drive κ B ω) T z : ℝ) : ℂ) -
        (CharFunRhs.Efwd (drive κ B ω) T ρ.1 : ℂ) / 2) ∂P =
      cexp (I * ((∫ z, ρ.1 z * h0fwd κ z : ℝ) : ℂ) -
        ((∫ x, ∫ y, ρ.1 x * ρ.1 y * greenH x y : ℝ) : ℂ) / 2) := by
  have hBpre := hB.toIsPreBrownianReal
  have hP : IsProbabilityMeasure P := hBpre.isGaussianProcess.isProbabilityMeasure
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB' : IsPreBrownianReal B' P :=
    hBpre.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  obtain ⟨hρsm, hρs, -⟩ := ρ.2
  have hρc : Continuous ρ.1 := hρsm.continuous
  obtain ⟨δ₀, hδ₀, hρδ₀⟩ := exists_im_pos_of_testFun ρ
  set Tn : ℝ≥0 := T.toNNReal with hTn
  have hTT : (Tn : ℝ) = T := Real.coe_toNNReal _ hT.le
  set δn : ℕ → ℝ := fun n => δ₀ / ((n : ℝ) + 2) with hδn
  have hδpos : ∀ n, 0 < δn n := fun n => by positivity
  have hδle : ∀ n, δn n ≤ δ₀ := fun n =>
    div_le_self hδ₀.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hδlim : Tendsto δn atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hρδ : ∀ n, ∀ a : ℂ, a.im < δn n → ρ.1 a = 0 := fun n a h =>
    hρδ₀ a (h.trans_le (hδle n))
  have hc : ∀ n, 0 < δn n / 2 := fun n => by linarith [hδpos n]
  have hcδ : ∀ n, δn n / 2 ≤ δn n := fun n => by linarith [hδpos n]
  set 𝓕 := bmFilt hB'm with h𝓕
  set G0 : ℝ := ∫ p, ρ.1 p.1 * ρ.1 p.2 * greenH p.1 p.2 ∂((volume : Measure ℂ).prod (volume : Measure ℂ))
    with hG0
  set F : ℕ → Ω → ℂ := fun n ω =>
    cexp (I * (fieldX κ (δn n / 2) (δn n) Tn B' ρ.1 Tn ω : ℂ) -
      (fieldV κ (δn n / 2) (δn n) Tn B' ρ.1 Tn ω : ℂ) / 2) with hF
  have hF5 : ∀ n, ∫ ω, F n ω ∂P =
      cexp (I * ((∫ z, ρ.1 z * h0fwd κ z : ℝ) : ℂ) - (G0 : ℂ) / 2) := fun n =>
    integral_exp_fieldX_fieldV hB' hB'c 𝓕 (bmFilt_adapted hB'm) (bmFilt_le_past hB'm) hκ
      (hc n) (hcδ n) hρc hρs (hρδ n) Tn
  have hnull := ae_measure_fwdHull_eq_zero hB' hB'm hB'c hκ hκ4 (volume : Measure ℂ) Tn
  have hclock' : ∀ᵐ ω ∂P, chiC κ = 0 ∨ ∫⁻ a in H \ fwdHull (drive κ B' ω) Tn,
      ENNReal.ofReal |ρ.1 a| * ENNReal.ofReal (fwdClock (drive κ B' ω) Tn a) < ⊤ := by
    filter_upwards [hclock, hdrive] with ω h hd
    rw [hd, hTT]; exact h
  set Lim : Ω → ℂ := fun ω =>
    cexp (I * ((∫ z, ρ.1 z * hTfwd κ (drive κ B' ω) Tn z : ℝ) : ℂ) -
      (CharFunRhs.Efwd (drive κ B' ω) Tn ρ.1 : ℂ) / 2) with hLim
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (Lim ω)) := by
    filter_upwards [hnull, hclock'] with ω h1 h2
    have hX := tendsto_fieldX hB'm hB'c hκ hρc hρs hδ₀ hρδ₀ hδpos hδle hδlim Tn ω h1 h2
    have hV := tendsto_fieldV hB'm hB'c hρc hρs hδ₀ hρδ₀ hδpos hδle hδlim Tn ω h1
    exact (Complex.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hX)).sub
        (((Complex.continuous_ofReal.tendsto _).comp hV).div_const 2))
  set E : ℝ := ∫ p, |ρ.1 p.1| * |ρ.1 p.2| * greenH p.1 p.2 ∂((volume : Measure ℂ).prod (volume : Measure ℂ))
    with hE
  have hFm : ∀ n, AEStronglyMeasurable (F n) P := fun n => by
    have hXm : Measurable (fieldX κ (δn n / 2) (δn n) Tn B' ρ.1 Tn) :=
      measurable_integral_mul_joint hρc.measurable
        (measurable_frozenField_amb (κ := κ) (δ := δn n) hB'c 𝓕 (bmFilt_adapted hB'm) (hc n)
          Tn Tn)
    have hVm : Measurable (fieldV κ (δn n / 2) (δn n) Tn B' ρ.1 Tn) :=
      measurable_integral_mul_joint (μ := (volume : Measure ℂ).prod (volume : Measure ℂ))
        (ρ := fun p : ℂ × ℂ => ρ.1 p.1 * ρ.1 p.2)
        ((hρc.measurable.comp measurable_fst).mul (hρc.measurable.comp measurable_snd))
        (measurable_frozenKernel_amb (κ := κ) (δ := δn n) hB'c 𝓕 (bmFilt_adapted hB'm) (hc n)
          Tn Tn)
    exact (Complex.measurable_exp.comp ((measurable_const.mul
      (Complex.measurable_ofReal.comp hXm)).sub
        ((Complex.measurable_ofReal.comp hVm).div_const 2))).aestronglyMeasurable
  have hFb : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ Real.exp (E / 2) := fun n => ae_of_all _ fun ω => by
    have hv := abs_fieldV_le (κ := κ) hB'c (hc n) (hcδ n) hρc hρs (hρδ n) Tn Tn ω
    simp only [hF, Complex.norm_exp, re_I_mul_sub_div_two]
    rw [Real.exp_le_exp]
    linarith [(abs_le.1 hv).1]
  have hDCT := tendsto_integral_of_dominated_convergence (fun _ => Real.exp (E / 2)) hFm
    (integrable_const _) hFb hlim
  have hconst : ∫ ω, Lim ω ∂P =
      cexp (I * ((∫ z, ρ.1 z * h0fwd κ z : ℝ) : ℂ) - (G0 : ℂ) / 2) :=
    tendsto_nhds_unique hDCT (by simp only [hF5]; exact tendsto_const_nhds)
  have hint : Integrable (fun p : ℂ × ℂ => ρ.1 p.1 * ρ.1 p.2 * greenH p.1 p.2)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
    integrable_rho_rho_mul hρc hρs hδ₀ hρδ₀ (C := 0) measurable_greenH.aestronglyMeasurable
      (fun p hne ha hb => by
        rw [zero_add, abs_of_nonneg (greenH_nonneg (show 0 ≤ p.1.im by linarith)
          (show 0 ≤ p.2.im by linarith) hne)])
  have hE0 : G0 = ∫ x, ∫ y, ρ.1 x * ρ.1 y * greenH x y :=
    integral_prod (fun p : ℂ × ℂ => ρ.1 p.1 * ρ.1 p.2 * greenH p.1 p.2) hint
  rw [← hE0, ← hconst, ← hTT]
  refine integral_congr_ae ?_
  filter_upwards [hdrive] with ω hω
  simp only [hLim, hω]

end MainMart
end QuantumZipper
