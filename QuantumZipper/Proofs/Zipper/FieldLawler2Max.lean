import QuantumZipper.Proofs.Thm18.LWExcMaxPrin
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Lindelöf's maximum principle with finitely many exceptional boundary points (task FL2-MAXEXC)

`fl2_harm_le_zero_off_finite`: a harmonic function `f` on an open set `U ⊆ ℂ`, bounded above,
with `limsup f ≤ 0` at every frontier point of `U` outside a finite set `E` and at `∞`,
satisfies `f ≤ 0` on `U`.

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge 2005, Ch. I, Lemma 1.1
(Lindelöf's maximum principle), p. 2. We follow its proof: subtract the barrier
`ε ∑_{ζ ∈ F} log (diam / |z - ζ|)`, apply the ordinary maximum principle, and let `ε → 0`.
Instead of the Möbius map `1/(z - z₀)` used there to reduce to a bounded region, we use the
hypothesis at `∞` directly and work on `U ∩ B(0, ρ) \ E`, with `ρ` beyond the radius where
`f ≤ ε'`; the ordinary maximum principle is `lwExc_harm_le_zero`
(`QuantumZipper/Proofs/Thm18/LWExcMaxPrin.lean`). The barrier is written as
`log ‖∏_{e ∈ E} (z - e)/r‖`, harmonic off `E` by mathlib's `AnalyticAt.harmonicAt_log_norm`.
-/

namespace QuantumZipper.FieldLawler

open Metric Set Filter Topology

/-- The barrier product `∏_{e ∈ E} (z - e) / r`. -/
noncomputable def fl2MaxBar (E : Finset ℂ) (r : ℝ) (z : ℂ) : ℂ := ∏ e ∈ E, (z - e) / (r : ℂ)

lemma fl2MaxBar_analyticAt (E : Finset ℂ) (r : ℝ) (z : ℂ) : AnalyticAt ℂ (fl2MaxBar E r) z := by
  have h : fl2MaxBar E r = ∏ e ∈ E, fun z : ℂ => (z - e) / (r : ℂ) := by
    funext w; simp [fl2MaxBar, Finset.prod_apply]
  rw [h]
  exact Finset.analyticAt_prod _ (fun e _ => (analyticAt_id.sub analyticAt_const).div_const)

lemma fl2MaxBar_ne_zero (E : Finset ℂ) {r : ℝ} (hr : r ≠ 0) {z : ℂ} (hz : z ∉ (E : Set ℂ)) :
    fl2MaxBar E r z ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 (fun e he => div_ne_zero (sub_ne_zero.2 ?_)
    (Complex.ofReal_ne_zero.2 hr))
  rintro rfl
  exact hz he

lemma fl2MaxBar_norm (E : Finset ℂ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖fl2MaxBar E r z‖ = ∏ e ∈ E, (‖z - e‖ / r) := by
  simp [fl2MaxBar, norm_prod, Complex.norm_real, abs_of_pos hr]

lemma fl2MaxBar_norm_le_one (E : Finset ℂ) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (h : ∀ e ∈ E, ‖z - e‖ ≤ r) : ‖fl2MaxBar E r z‖ ≤ 1 := by
  rw [fl2MaxBar_norm E hr]
  exact Finset.prod_le_one₀ (fun e _ => by positivity) (fun e he => (div_le_one hr).2 (h e he))

lemma fl2MaxBar_norm_le_single (E : Finset ℂ) {r : ℝ} (hr : 0 < r) {z e₀ : ℂ}
    (h : ∀ e ∈ E, ‖z - e‖ ≤ r) (he₀ : e₀ ∈ E) : ‖fl2MaxBar E r z‖ ≤ ‖z - e₀‖ / r := by
  classical
  rw [fl2MaxBar_norm E hr, ← Finset.mul_prod_erase E _ he₀]
  exact mul_le_of_le_one_right (by positivity) (Finset.prod_le_one₀ (fun _ _ => by positivity)
    (fun e he => (div_le_one hr).2 (h e (Finset.mem_of_mem_erase he))))

/-- Core step (Garnett–Marshall, Lemma I.1.1): at a point `y₀ ∈ U \ E`, `f y₀ ≤ ε'` whenever
`f ≤ ε'` on `U` outside the ball of radius `R`. -/
lemma fl2_harm_le_eps_off_finite {U : Set ℂ} {f : ℂ → ℝ} (E : Finset ℂ) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) {M : ℝ} (hMU : ∀ y ∈ U, f y ≤ M)
    {ε' : ℝ} (hε' : 0 < ε')
    (hfr : ∀ x₀ ∈ frontier U, x₀ ∉ E → ∃ δ > 0, ∀ y ∈ U, dist y x₀ < δ → f y ≤ ε')
    {R : ℝ} (hR : ∀ y ∈ U, R ≤ ‖y‖ → f y ≤ ε') {y₀ : ℂ} (hy₀ : y₀ ∈ U)
    (hy₀E : y₀ ∉ (E : Set ℂ)) : f y₀ ≤ ε' := by
  set ρ : ℝ := max R ‖y₀‖ + 1 with hρ
  set r : ℝ := ρ + ∑ e ∈ E, ‖e‖ + 1 with hr
  have hρ0 : 0 < ρ := by
    have := le_max_right R ‖y₀‖; have := norm_nonneg y₀; linarith
  have hsum0 : 0 ≤ ∑ e ∈ E, ‖e‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hr0 : 0 < r := by linarith
  have hrb : ∀ z ∈ ball (0 : ℂ) ρ, ∀ e ∈ E, ‖z - e‖ ≤ r := by
    intro z hz e he
    have h1 : ‖z‖ < ρ := by simpa using hz
    have h2 : ‖e‖ ≤ ∑ e ∈ E, ‖e‖ :=
      Finset.single_le_sum (f := fun e : ℂ => ‖e‖) (fun _ _ => norm_nonneg _) he
    have := norm_sub_le z e
    linarith
  set V : Set ℂ := U ∩ ball (0 : ℂ) ρ ∩ (E : Set ℂ)ᶜ with hV
  have hVo : IsOpen V :=
    (hU.inter isOpen_ball).inter E.finite_toSet.isClosed.isOpen_compl
  have hy₀V : y₀ ∈ V := by
    refine ⟨⟨hy₀, ?_⟩, hy₀E⟩
    have := le_max_right R ‖y₀‖
    simp only [mem_ball, dist_zero_right]; linarith
  set B : ℂ → ℂ := fl2MaxBar E r with hB
  set L : ℝ := Real.log ‖B y₀‖ with hL
  -- for every `η > 0`, the function `f - ε' + η log ‖B‖` is `≤ 0` on `V`
  have hmain : ∀ η : ℝ, 0 < η → f y₀ - ε' + η * L ≤ 0 := by
    intro η hη
    set g : ℂ → ℝ := fun z => f z - ε' + η * Real.log ‖B z‖ with hg
    have hgle : ∀ y ∈ V, f y ≤ ε' → g y ≤ 0 := by
      intro y hy hfy
      have hlog : Real.log ‖B y‖ ≤ 0 :=
        Real.log_nonpos (norm_nonneg _) (fl2MaxBar_norm_le_one E hr0 (hrb y hy.1.2))
      have := mul_nonpos_of_nonneg_of_nonpos hη.le hlog
      simp only [hg]; linarith
    have hgh : InnerProductSpace.HarmonicOnNhd g V := by
      intro y hy
      have h1 : InnerProductSpace.HarmonicAt (fun z => Real.log ‖B z‖) y :=
        AnalyticAt.harmonicAt_log_norm (fl2MaxBar_analyticAt E r y) (fl2MaxBar_ne_zero E hr0.ne' hy.2)
      have h2 := ((hf y hy.1.1).sub (InnerProductSpace.harmonicAt_const ε')).add
        (h1.const_smul (c := η))
      have h3 : g = (f - fun _ => ε') + η • (fun z => Real.log ‖B z‖) := by
        funext z; simp [hg, smul_eq_mul]
      rw [h3]; exact h2
    have hgbd : ∀ x₀ ∈ frontier V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∈ V, dist y x₀ < δ → g y ≤ ε := by
      intro x₀ hx₀ ε hε
      rw [hVo.frontier_eq] at hx₀
      obtain ⟨hx₀c, hx₀V⟩ := hx₀
      by_cases hx₀E : x₀ ∈ E
      · refine ⟨r * Real.exp (-|M| / η), by positivity, fun y hy hdy => ?_⟩
        have hBpos : 0 < ‖B y‖ := norm_pos_iff.2 (fl2MaxBar_ne_zero E hr0.ne' hy.2)
        have hBle : ‖B y‖ ≤ ‖y - x₀‖ / r := fl2MaxBar_norm_le_single E hr0 (hrb y hy.1.2) hx₀E
        have hlt : ‖y - x₀‖ / r < Real.exp (-|M| / η) := by
          rw [div_lt_iff₀ hr0, mul_comm, ← dist_eq_norm]; exact hdy
        have hlog : Real.log ‖B y‖ < -|M| / η := by
          have := Real.log_lt_log hBpos (hBle.trans_lt hlt)
          rwa [Real.log_exp] at this
        have hηl : η * Real.log ‖B y‖ < -|M| := by
          have := mul_lt_mul_of_pos_left hlog hη
          rwa [mul_div_cancel₀ _ hη.ne'] at this
        have := hMU y hy.1.1
        have := le_abs_self M
        simp only [hg]; linarith
      by_cases hx₀U : x₀ ∈ U
      · have hfar : ρ ≤ ‖x₀‖ := by
          by_contra hlt; push Not at hlt
          exact hx₀V ⟨⟨hx₀U, by simpa using hlt⟩, hx₀E⟩
        refine ⟨1, one_pos, fun y hy hdy => (hgle y hy (hR y hy.1.1 ?_)).trans hε.le⟩
        have := norm_sub_norm_le x₀ y
        rw [← dist_eq_norm, dist_comm] at this
        have := le_max_left R ‖y₀‖
        linarith
      · have hx₀fr : x₀ ∈ frontier U := by
          rw [hU.frontier_eq]
          exact ⟨closure_mono (fun z hz => hz.1.1) hx₀c, hx₀U⟩
        obtain ⟨δ, hδ, hδf⟩ := hfr x₀ hx₀fr hx₀E
        exact ⟨δ, hδ, fun y hy hdy => (hgle y hy (hδf y hy.1.1 hdy)).trans hε.le⟩
    have hginf : ∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, ∀ y ∈ V, R' ≤ ‖y‖ → g y ≤ ε := by
      intro ε _
      refine ⟨ρ, fun y hy hy' => ?_⟩
      have : ‖y‖ < ρ := by simpa using hy.1.2
      exact absurd hy' (not_le.2 this)
    exact Thm18Asm.LWFar.lwExc_harm_le_zero hVo hgh hgbd hginf y₀ hy₀V
  -- let `η → 0`
  have : f y₀ - ε' ≤ 0 := by
    refine le_of_forall_pos_le_add (fun t ht => ?_)
    have hη : 0 < t / (|L| + 1) := by positivity
    have h1 := hmain _ hη
    have h2 : -(t / (|L| + 1) * L) ≤ t := by
      have h3 : -(t / (|L| + 1) * L) ≤ t / (|L| + 1) * |L| := by
        rw [← neg_mul]; nlinarith [neg_abs_le L, hη]
      have h4 : t / (|L| + 1) * |L| ≤ t := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg L]
      linarith
    linarith
  linarith

/-- **Lindelöf's maximum principle** (Garnett–Marshall, *Harmonic Measure*, Ch. I, Lemma 1.1,
p. 2), for an open set `U ⊆ ℂ` with the boundary condition at `∞` included: a harmonic function
bounded above on `U`, with `limsup ≤ 0` at every frontier point outside the finite set `E` and
at `∞`, is `≤ 0` on `U`. -/
theorem fl2_harm_le_zero_off_finite {U : Set ℂ} {f : ℂ → ℝ} (E : Finset ℂ) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) (hbd : BddAbove (f '' U))
    (hfr : ∀ x₀ ∈ frontier U, x₀ ∉ E → ∀ ε > 0, ∃ δ > 0, ∀ y ∈ U, dist y x₀ < δ → f y ≤ ε)
    (hinf : ∀ ε > 0, ∃ R, ∀ y ∈ U, R ≤ ‖y‖ → f y ≤ ε) : ∀ y ∈ U, f y ≤ 0 := by
  obtain ⟨M, hM⟩ := hbd
  have hMU : ∀ y ∈ U, f y ≤ M := fun y hy => hM ⟨y, hy, rfl⟩
  have hoff : ∀ y₀ ∈ U, y₀ ∉ (E : Set ℂ) → f y₀ ≤ 0 := by
    intro y₀ hy₀ hy₀E
    refine le_of_forall_pos_le_add (fun ε' hε' => ?_)
    obtain ⟨R, hR⟩ := hinf ε' hε'
    rw [zero_add]
    exact fl2_harm_le_eps_off_finite E hU hf hMU hε'
      (fun x₀ hx₀ hx₀E => hfr x₀ hx₀ hx₀E ε' hε') hR hy₀ hy₀E
  intro y₀ hy₀
  by_cases hy₀E : y₀ ∈ (E : Set ℂ)
  · have hc : ContinuousAt f y₀ := (hf y₀ hy₀).1.continuousAt
    have h1 : ∀ᶠ y in 𝓝[≠] y₀, y ∈ U := nhdsWithin_le_nhds (hU.mem_nhds hy₀)
    have h2 : ∀ᶠ y in 𝓝[≠] y₀, y ∉ ((E.erase y₀ : Finset ℂ) : Set ℂ) :=
      nhdsWithin_le_nhds ((E.erase y₀).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp))
    have h3 : ∀ᶠ y in 𝓝[≠] y₀, y ≠ y₀ := self_mem_nhdsWithin
    have hev : ∀ᶠ y in 𝓝[≠] y₀, f y ≤ 0 := by
      filter_upwards [h1, h2, h3] with y hyU hyE hy
      refine hoff y hyU (fun hmem => hyE ?_)
      simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨hmem, hy⟩
    exact le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds) hev
  · exact hoff y₀ hy₀ hy₀E

end QuantumZipper.FieldLawler
