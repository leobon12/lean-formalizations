import InteractingSLE.Spec.Sec2.MartingaleLevy

/-!
# Local martingales before a random time, and martingales as uniform limits

Packet PROVE-SEC2-MART. Specification, Theorem 2.4 (`source/spec/p001-048.md`, anchor `thm-2.4`,
L819–L823): the hypothesis is that `𝔥_t(z)` "evolves as a continuous local martingale in `t` for each
fixed `z ∈ ℍ` until the time `z` is absorbed by `K_t`". This file fixes the meaning of that phrase
(`IsLocalMartingaleBefore`) and proves the two limit arguments that turn it into martingale
statements about the Laurent coefficients:

* `setIntegral_stoppedProcess_eq_of_isLocalMartingaleBefore`: if `X` is a local martingale before
  `ζ`, right-continuous before `ζ`, and bounded up to a bounded stopping time `τ < ζ`, then `X^τ` has
  constant set integrals over `𝓕ₛ`-sets (optional stopping of each `X^{σₙ}` at `τ`, then dominated
  convergence as `n → ∞`);
* `martingale_of_forall_abs_sub_le`: an adapted integrable process that is uniformly approximated,
  within `εₖ → 0`, by processes with constant set integrals is a martingale.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- `X` is a local martingale before the random time `ζ` ("a local martingale in `t` until the time
`z` is absorbed", Specification Theorem 2.4): there are stopping times `σₙ ≤ ζ` such that every
`X^{σₙ}` is a martingale, and almost surely every level below `ζ` is eventually exceeded by the
`σₙ` (in particular `σₙ ↑ ζ` suffices). -/
def IsLocalMartingaleBefore (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (ζ : Ω → WithTop ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓕 (σ n)) ∧ (∀ n ω, σ n ω ≤ ζ ω) ∧
    (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < ζ ω → ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) ∧
    ∀ n, Martingale (stoppedProcess X (σ n)) 𝓕 P

/-- A process that is right-continuous before `ζ` and stopped at some `σ ≤ ζ` is right-continuous. -/
lemma continuousWithinAt_stoppedProcess {X : ℝ≥0 → Ω → ℝ} {ζ σ : Ω → WithTop ℝ≥0}
    (hσζ : ∀ ω, σ ω ≤ ζ ω)
    (hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < ζ ω → ContinuousWithinAt (X · ω) (Ici s) s)
    (ω : Ω) (s : ℝ≥0) : ContinuousWithinAt (stoppedProcess X σ · ω) (Ici s) s := by
  rcases lt_or_ge (s : WithTop ℝ≥0) (σ ω) with hs | hs
  · -- before `σ`: the stopped path agrees with `X` near `s` on the right
    have hX := hrc ω s (hs.trans_le (hσζ ω))
    rcases eq_or_ne (σ ω) ⊤ with htop | hne
    · have : (stoppedProcess X σ · ω) = (X · ω) := by
        funext u; simp only [stoppedProcess, htop, min_top_right]; rfl
      rw [this]; exact hX
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
      have hsr : s < r := by rw [← hr] at hs; exact_mod_cast hs
      have heq : ∀ᶠ u in 𝓝[Ici s] s, stoppedProcess X σ u ω = X u ω := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hsr)] with u hu
        simp only [stoppedProcess, ← hr]
        rw [← WithTop.coe_min, min_eq_left (le_of_lt hu)]
        rfl
      have hs0 : stoppedProcess X σ s ω = X s ω := by
        simp only [stoppedProcess, ← hr]
        rw [← WithTop.coe_min, min_eq_left hsr.le]
        rfl
      exact hX.congr_of_eventuallyEq heq hs0
  · -- after `σ`: the stopped path is constant on `[s, ∞)`
    have hconst : ∀ u ∈ Ici s, stoppedProcess X σ u ω = stoppedProcess X σ s ω := by
      intro u hu
      simp only [stoppedProcess]
      rw [min_eq_right hs, min_eq_right (hs.trans (WithTop.coe_le_coe.2 hu))]
    exact (continuousWithinAt_const.congr (fun u hu => hconst u hu) (hconst s (le_refl s)))

/-- **A local martingale before `ζ`, stopped at a bounded stopping time `τ < ζ` up to which it is
bounded, has constant set integrals** (and is almost everywhere measurable). Optional stopping of
each `X^{σₙ}` at `τ`, then dominated convergence as `n → ∞`. -/
theorem setIntegral_stoppedProcess_eq_of_isLocalMartingaleBefore [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} {ζ τ : Ω → WithTop ℝ≥0} (hX : IsLocalMartingaleBefore 𝓕 P ζ X)
    (hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < ζ ω → ContinuousWithinAt (X · ω) (Ici s) s)
    (hτ : IsStoppingTime 𝓕 τ) {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hτζ : ∀ᵐ ω ∂P, τ ω < ζ ω)
    {C : ℝ} (hC : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → |X t ω| ≤ C) :
    (∀ t, Integrable (stoppedProcess X τ t) P) ∧
      ∀ s t : ℝ≥0, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
        ∫ ω in A, stoppedProcess X τ t ω ∂P = ∫ ω in A, stoppedProcess X τ s ω ∂P := by
  obtain ⟨σ, hσ, hσζ, hσlim, hσmart⟩ := hX
  -- the doubly stopped martingales
  set Z : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess (stoppedProcess X (σ n)) τ with hZ
  have hZmart : ∀ n, Martingale (Z n) 𝓕 P := fun n =>
    Martingale.stoppedProcess_of_rightContinuous (hσmart n)
      (continuousWithinAt_stoppedProcess (hσζ n) hrc) hτ
  -- the stopped time is finite
  have hτne : ∀ ω, τ ω ≠ ⊤ := fun ω => ne_top_of_le_ne_top WithTop.coe_ne_top (hτT ω)
  -- every evaluation time is at most `τ`
  have hZbd : ∀ n t ω, |Z n t ω| ≤ C := fun n t ω => by
    simp only [hZ, stoppedProcess]
    refine hC ω _ ?_
    have h1 : min ((((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ≥0)) : WithTop ℝ≥0) (σ n ω)
        ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    rw [coe_untopA_of_ne_top h1]
    have h2 : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    refine (min_le_left _ _).trans ?_
    rw [coe_untopA_of_ne_top h2]
    exact min_le_right _ _
  -- convergence to `X^τ`
  have hlim : ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => Z n t ω) atTop (𝓝 (stoppedProcess X τ t ω)) := by
    filter_upwards [hσlim, hτζ] with ω hω hτω
    intro t
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 (hτne ω)
    have hev := hω r (hr ▸ hτω)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    simp only [hZ, stoppedProcess]
    have h2 : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    rw [coe_untopA_of_ne_top h2, min_eq_left ((min_le_right _ _).trans (hr ▸ hn.le))]
  have hZm : ∀ n t, StronglyMeasurable (Z n t) := fun n t => ((hZmart n).1 t).mono (𝓕.le t)
  have hmeas : ∀ t, AEStronglyMeasurable (stoppedProcess X τ t) P := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hZm n t).aestronglyMeasurable)
      (hlim.mono fun ω h => h t)
  have hXbd : ∀ t ω, |stoppedProcess X τ t ω| ≤ C := fun t ω => by
    simp only [stoppedProcess]
    refine hC ω _ ?_
    rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  refine ⟨fun t => Integrable.of_bound (hmeas t) C
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hXbd t ω),
    fun s t hst A hA => ?_⟩
  have hdct : ∀ u, Tendsto (fun n => ∫ ω in A, Z n u ω ∂P) atTop
      (𝓝 (∫ ω in A, stoppedProcess X τ u ω ∂P)) := fun u =>
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (hZm n u).aestronglyMeasurable.restrict) (integrable_const C)
      (fun n => Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZbd n u ω)
      (ae_restrict_of_ae (hlim.mono fun ω h => h u))
  have heq : ∀ n, ∫ ω in A, Z n t ω ∂P = ∫ ω in A, Z n s ω ∂P := fun n =>
    ((hZmart n).setIntegral_eq hst hA).symm
  exact tendsto_nhds_unique ((hdct t).congr heq) (hdct s)

/-- **Uniform approximation by processes with constant set integrals.** An adapted integrable process
`X` is a martingale if for every `k` some process `G k` with constant set integrals over `𝓕ₛ`-sets is
within `ε k` of `X` everywhere, with `ε k → 0`. -/
theorem martingale_of_forall_abs_sub_le [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hXa : StronglyAdapted 𝓕 X) (hXi : ∀ t, Integrable (X t) P) {G : ℕ → ℝ≥0 → Ω → ℝ}
    (hGm : ∀ k t, AEStronglyMeasurable (G k t) P) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hGX : ∀ k t ω, |G k t ω - X t ω| ≤ ε k)
    (hG : ∀ k (s t : ℝ≥0), s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
      ∫ ω in A, G k t ω ∂P = ∫ ω in A, G k s ω ∂P) :
    Martingale X 𝓕 P := by
  refine ⟨hXa, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hXi t)
    (fun A _ _ => (hXi s).integrableOn) (fun A hA _ => ?_)
    (hXa s).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝓕.le s A hA
  have hGi : ∀ k u, Integrable (G k u) P := fun k u => by
    have hd : Integrable (fun ω => G k u ω - X u ω) P :=
      Integrable.of_bound ((hGm k u).sub (hXi u).aestronglyMeasurable) (ε k)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGX k u ω)
    have := hd.add (hXi u)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  have hbound : ∀ k, |∫ ω in A, X s ω ∂P - ∫ ω in A, X t ω ∂P| ≤ 2 * ε k := fun k => by
    have h1 : ∫ ω in A, X s ω ∂P - ∫ ω in A, X t ω ∂P
        = ∫ ω in A, (X s ω - G k s ω) ∂P - ∫ ω in A, (X t ω - G k t ω) ∂P := by
      rw [integral_sub (hXi s).integrableOn (hGi k s).integrableOn,
        integral_sub (hXi t).integrableOn (hGi k t).integrableOn, hG k s t hst A hA]
      ring
    have hbd : ∀ u, |∫ ω in A, (X u ω - G k u ω) ∂P| ≤ ε k := fun u => by
      have hrestr : (P.restrict A) Set.univ ≤ 1 := by
        rw [Measure.restrict_apply_univ]; exact prob_le_one
      calc |∫ ω in A, (X u ω - G k u ω) ∂P| = ‖∫ ω in A, (X u ω - G k u ω) ∂P‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ε k * ((P.restrict A) Set.univ).toReal := by
            refine norm_integral_le_of_norm_le_const ?_
            exact Eventually.of_forall fun ω => by
              rw [Real.norm_eq_abs, abs_sub_comm]; exact hGX k u ω
        _ ≤ ε k * 1 := by
            have hne : Nonempty Ω := by
              by_contra h
              rw [not_nonempty_iff] at h
              have := measure_univ (μ := P)
              rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
              exact zero_ne_one this
            have hε0 : 0 ≤ ε k := (abs_nonneg _).trans (hGX k 0 (Classical.choice hne))
            refine mul_le_mul_of_nonneg_left ?_ hε0
            exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hrestr)
        _ = ε k := mul_one _
    rw [h1]
    calc _ ≤ |∫ ω in A, (X s ω - G k s ω) ∂P| + |∫ ω in A, (X t ω - G k t ω) ∂P| := abs_sub _ _
      _ ≤ 2 * ε k := by linarith [hbd s, hbd t]
  have hlim : Tendsto (fun k => 2 * ε k) atTop (𝓝 0) := by simpa using hε.const_mul 2
  have h0 : |∫ ω in A, X s ω ∂P - ∫ ω in A, X t ω ∂P| ≤ 0 :=
    ge_of_tendsto hlim (Eventually.of_forall hbound)
  have := abs_nonpos_iff.1 h0
  linarith

end MartChar

end InteractingSLE
