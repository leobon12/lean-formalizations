import QuantumZipper.Proofs.Section5.TVLocal
import SmallGammaGeodesics.CC.ExtensionPull
import LQGMetric.Field.Measurable

/-!
# GM Lemma 2.4, display (2.6): the total-variation reduction

Source: Gwynne–Miller 1905.00384v2, `coord-change-final.tex` l. 547–562. On an open disk `B` (containing
`K` and the support of the normalizing test function `f_r`, `∫ f_r = 1`) we work with the normalized
field `nrm f_r u = u − (u, f_r) · 1` (`u ∈ 𝒟'(B)`). This file proves the deterministic algebra and the
TV bookkeeping of GM's argument:

* `nrm_add_const`: adding a constant does not change the normalized field (`∫ f_r = 1`);
* `nrm_add_smoothDist_cutoff`: GM's cutoff step: replacing the harmonic part `Y` by any `S` with
  `S = Y − (Y, f_r)` on `B` (e.g. `χ · (Y − (Y, f_r))`, `χ = 1` on `B`) does not change `nrm`;
* `tendsto_lintegral_cmBound`: if the Cameron–Martin energies `E_n → 0` in probability, then
  `∫ min(1, √(exp E_n − 1)) → 0`;
* `tendsto_tvDist_of_inputs`: (2.6) from (i) the decomposition, (ii) the Cameron–Martin mixture bound,
  (iii) the energy decay, (iv) IG4 Prop 2.10(i) (with the conformal invariance of the zero-boundary
  GFF), (v) the law identification of the limit. Inputs (i)–(v) are explicit hypotheses here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.GM24

open LQGMetric QuantumZipper
open SmallGammaGeodesics.CC (intDist intDist_apply)

variable {B : Opens ℂ}

/-! ## The normalized field -/

/-- `u − (u, f_r) · 1`: the field minus its smooth average (GM l. 549–553). -/
def nrm (fr : TestOn B) (u : DistOn B) : DistOn B := u - u fr • intDist B

theorem nrm_apply (fr : TestOn B) (u : DistOn B) (g : TestOn B) :
    nrm fr u g = u g - u fr * ∫ x, g x := by
  rw [nrm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, intDist_apply,
    smul_eq_mul]

theorem measurable_nrm (fr : TestOn B) : Measurable (nrm fr) := by
  apply measurable_distOn_iff.mpr
  intro g
  simp only [nrm_apply]
  exact (measurable_distOn_apply g).sub ((measurable_distOn_apply fr).mul_const _)

/-- Constants are invisible to the normalized field. -/
theorem nrm_add_const {fr : TestOn B} (hfr : ∫ x, fr x = 1) (u : DistOn B) (c : ℝ) :
    nrm fr (u + c • intDist B) = nrm fr u := by
  ext g
  simp only [nrm_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    intDist_apply, smul_eq_mul, hfr]
  ring

/-- A function on `B` (continuous on `B`) as a distribution on `B`: `g ↦ ∫ g Y`. -/
def smoothDist (B : Opens ℂ) (Y : ℂ → ℝ) : DistOn B := Distribution.ofFun B Y MeasureTheory.volume ⊤

theorem smoothDist_apply {Y : ℂ → ℝ} (hY : ContinuousOn Y B) (g : TestOn B) :
    smoothDist B Y g = ∫ x, g x * Y x := by
  rw [smoothDist, Distribution.ofFun_apply (hY.locallyIntegrableOn B.isOpen.measurableSet)]
  simp only [smul_eq_mul]

theorem integrable_test_mul {Y : ℂ → ℝ} (hY : ContinuousOn Y B) (g : TestOn B) :
    Integrable (fun x => g x * Y x) := by
  have hK : IsCompact (tsupport (g : ℂ → ℝ)) := g.hasCompactSupport.isCompact
  have hc : ContinuousOn (fun x => g x * Y x) (tsupport (g : ℂ → ℝ)) :=
    g.continuous.continuousOn.mul (hY.mono g.tsupport_subset)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 (hc.integrableOn_compact hK)
  intro x hx
  exact subset_tsupport _ (left_ne_zero_of_mul hx)

/-- **GM's cutoff step** (l. 557–561): if `S = Y − (Y, f_r)` on `B`, then
`nrm (u + Y) = nrm (u + S)`. -/
theorem nrm_add_smoothDist_cutoff {fr : TestOn B} (hfr : ∫ x, fr x = 1) (u : DistOn B)
    {Y S : ℂ → ℝ} (hY : ContinuousOn Y B)
    (hS : EqOn S (fun x => Y x - smoothDist B Y fr) B) :
    nrm fr (u + smoothDist B Y) = nrm fr (u + smoothDist B S) := by
  have hSc : ContinuousOn S B := (hY.sub continuousOn_const).congr hS
  have key : ∀ g : TestOn B,
      smoothDist B S g = smoothDist B Y g - smoothDist B Y fr * ∫ x, g x := by
    intro g
    rw [smoothDist_apply hSc, smoothDist_apply hY, ← integral_const_mul,
      ← integral_sub (integrable_test_mul hY g) ((g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).const_mul _)]
    congr 1
    funext x
    by_cases hx : x ∈ (B : Set ℂ)
    · rw [hS hx]; ring
    · have : g x = 0 := g.zero_on_compl hx
      rw [this]; ring
  have hfr0 : smoothDist B S fr = 0 := by rw [key fr, hfr]; ring
  ext g
  simp only [nrm_apply, add_apply, key g, hfr0]
  ring

/-! ## The Cameron–Martin bound tends to zero -/

/-- The Cameron–Martin TV bound `min(1, √(exp E − 1))` (`tvDist_zb_countable_shift_le_min`). -/
def cmBound (E : ℝ) : ℝ≥0∞ := min 1 (ENNReal.ofReal (Real.sqrt (Real.exp E - 1)))

theorem cmBound_le_one (E : ℝ) : cmBound E ≤ 1 := min_le_left _ _

theorem cmBound_mono {E E' : ℝ} (h : E ≤ E') : cmBound E ≤ cmBound E' :=
  min_le_min_left _ (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (by linarith [Real.exp_le_exp.2 h])))

theorem measurable_cmBound : Measurable cmBound :=
  measurable_const.min (ENNReal.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp (Real.measurable_exp.sub measurable_const)))

/-- **Energies → 0 in probability ⇒ the Cameron–Martin bounds → 0 in mean.** -/
theorem tendsto_lintegral_cmBound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : ℕ → Ω → ℝ}
    (hE : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ < E n ω}) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, cmBound (E n ω) ∂P) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hcont : Continuous fun x : ℝ => ENNReal.ofReal (Real.sqrt (Real.exp x - 1)) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_sqrt.comp (Real.continuous_exp.sub
      continuous_const))
  have h0 : ENNReal.ofReal (Real.sqrt (Real.exp 0 - 1)) = 0 := by simp
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), ENNReal.ofReal (Real.sqrt (Real.exp x - 1)) < ε / 2 := by
    have := hcont.tendsto 0
    rw [h0] at this
    exact this (Iio_mem_nhds hε2)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set δ : ℝ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hδε : ENNReal.ofReal (Real.sqrt (Real.exp δ - 1)) < ε / 2 :=
    hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; exact half_lt_self hr)
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (hE δ hδ)) (ε / 2) hε2] with n hn
  have hpt : ∀ ω, cmBound (E n ω) ≤ ENNReal.ofReal (Real.sqrt (Real.exp δ - 1)) +
      {ω | δ < E n ω}.indicator 1 ω := by
    intro ω
    by_cases h : δ < E n ω
    · rw [indicator_of_mem (show ω ∈ {ω | δ < E n ω} from h)]
      exact (cmBound_le_one _).trans le_add_self
    · rw [indicator_of_notMem (show ω ∉ {ω | δ < E n ω} from h), add_zero]
      exact (cmBound_mono (not_lt.1 h)).trans (min_le_right _ _)
  calc ∫⁻ ω, cmBound (E n ω) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (Real.sqrt (Real.exp δ - 1)) + {ω | δ < E n ω}.indicator 1 ω) ∂P :=
        lintegral_mono hpt
    _ ≤ ENNReal.ofReal (Real.sqrt (Real.exp δ - 1)) + P {ω | δ < E n ω} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        exact add_le_add le_rfl (lintegral_indicator_one_le _)
    _ ≤ ε / 2 + ε / 2 := add_le_add hδε.le hn
    _ = ε := ENNReal.add_halves ε

/-! ## The total-variation reduction -/

/-- **GM (2.6) from its inputs.** On a probability space, let `N n` be the normalized observed fields
(`nrm f_r` of `(h ∘ φ_n⁻¹)|_B`), `Ninf` the limit field (`h(α ·)|_B`). Suppose
* (decomposition: Markov property of `h` on a disk, transported by `φ_n⁻¹`) eventually, a.s.,
  `N n = nrm f_r (X n + Y n + C n)` with `X n` the transported zero-boundary part, `Y n` the
  transported harmonic part (continuous on `B`) and `C n` a constant;
* (cutoff) `S n = Y n − (Y n, f_r)` on `B`;
* (Cameron–Martin mixture) `TV(X n + S n, X n) ≤ E min(1, √(exp E_n − 1))`;
* (energy) `E_n → 0` in probability;
* (IG4 Prop 2.10(i) with conformal invariance) `TV(nrm X n, nrm H) → 0`;
* (limit law) `nrm H` has the law of `Ninf`.
Then `TV(law N n, law Ninf) → 0`. -/
theorem tendsto_tvDist_of_inputs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {fr : TestOn B} (hfr : ∫ x, fr x = 1)
    {N : ℕ → Ω → DistOn B} {Ninf H : Ω → DistOn B} {X : ℕ → Ω → DistOn B} {Y S : ℕ → Ω → ℂ → ℝ}
    {C E : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hXS : ∀ n, Measurable fun ω => X n ω + smoothDist B (S n ω))
    (hdec : ∀ᶠ n in atTop, ∀ᵐ ω ∂P,
      N n ω = nrm fr (X n ω + smoothDist B (Y n ω) + C n ω • intDist B))
    (hcut : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ContinuousOn (Y n ω) B ∧
      EqOn (S n ω) (fun x => Y n ω x - smoothDist B (Y n ω) fr) B)
    (hCM : ∀ᶠ n in atTop, TV.tvDist (P.map fun ω => X n ω + smoothDist B (S n ω)) (P.map (X n)) ≤
      ∫⁻ ω, cmBound (E n ω) ∂P)
    (hE : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => P {ω | δ < E n ω}) atTop (𝓝 0))
    (hIG4 : Tendsto (fun n => TV.tvDist (P.map (nrm fr ∘ X n)) (P.map (nrm fr ∘ H))) atTop (𝓝 0))
    (hlaw : P.map (nrm fr ∘ H) = P.map Ninf) :
    Tendsto (fun n => TV.tvDist (P.map (N n)) (P.map Ninf)) atTop (𝓝 0) := by
  have hnrm := measurable_nrm fr
  have hlim := (tendsto_lintegral_cmBound hE).add hIG4
  rw [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hdec, hcut, hCM] with n hdn hcn hCMn
  have hNeq : P.map (N n) = P.map (nrm fr ∘ fun ω => X n ω + smoothDist B (S n ω)) := by
    refine Measure.map_congr ?_
    filter_upwards [hdn, hcn] with ω hω hcω
    rw [hω, nrm_add_const hfr, Function.comp_apply,
      nrm_add_smoothDist_cutoff hfr _ hcω.1 hcω.2]
  rw [hNeq, ← hlaw]
  refine (TV.tvDist_triangle (ν := P.map (nrm fr ∘ X n))).trans (add_le_add ?_ le_rfl)
  rw [← Measure.map_map hnrm (hXS n), ← Measure.map_map hnrm (hX n)]
  exact (TV.tvDist_map_le hnrm).trans hCMn

/-! ## The decomposition, from a Markov decomposition on a larger domain -/

/-- Restriction `𝒟'(V) → 𝒟'(B)` for `B ≤ V`. -/
def restrictDist {B V : Opens ℂ} (hBV : B ≤ V) (u : DistOn V) : DistOn B :=
  u.comp (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V))

theorem restrictDist_apply {B V : Opens ℂ} (hBV : B ≤ V) (u : DistOn V) (g : TestOn B) :
    restrictDist hBV u g = u (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) g) :=
  rfl

theorem coe_monoCLM_le {B V : Opens ℂ} (hBV : B ≤ V) (g : TestOn B) :
    ⇑(TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) g) = ⇑g := by
  rw [TestFunction.monoCLM_apply, ite_cond_eq_true _ _ (eq_true ⟨le_rfl, hBV⟩)]

/-- **From a Markov decomposition to the decomposition hypothesis of `tendsto_tvDist_of_inputs`.**
If `u = z + H` on `V ⊇ B` in the sense of distributions (`(u − z, ψ) = ∫ H ψ`, the form of the conformal invariance of the zero-boundary GFF's
`exists_pullback_markov_*_joint`), and `u = u' + c` (a circle recentering), then
`nrm (u'|_B) = nrm (z|_B + H|_B + (−c) · 1)`. -/
theorem nrm_restrict_eq_of_decomp {B V : Opens ℂ} (hBV : B ≤ V) {fr : TestOn B}
    {u u' z : DistOn V} {H : ℂ → ℝ} {c : ℝ} (hH : ContinuousOn H B)
    (hpair : ∀ ψ : TestOn V, (u - z) ψ = ∫ x, H x * ψ x)
    (hc : u = u' + c • intDist V) :
    nrm fr (restrictDist hBV u') =
      nrm fr (restrictDist hBV z + smoothDist B H + (-c) • intDist B) := by
  congr 1
  ext g
  have h1 := hpair (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) g)
  rw [hc] at h1
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, intDist_apply, smul_eq_mul, coe_monoCLM_le hBV] at h1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, restrictDist_apply,
    intDist_apply, smul_eq_mul, smoothDist_apply hH]
  have e : ∫ x, H x * g x = ∫ x, g x * H x := by congr 1; funext x; ring
  linarith

end SupercriticalConformalCovariance.GM24
