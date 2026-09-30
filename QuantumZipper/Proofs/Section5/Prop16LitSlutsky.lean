import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A Slutsky step for Proposition 1.6, literal form

`LitSlutsky.tendsto_integral_sub`: if `X_C` is tight and `Y_C − X_C → 0` in probability, then
`E F(Y_C) − E F(X_C) → 0` for every bounded continuous `F` on `ℝ^m`. This is the elementary
half of Slutsky's theorem (e.g. Billingsley, *Convergence of Probability Measures*, 2nd ed.,
Thm. 3.1), proved directly (uniform continuity of `F` on a compact ball) because the limit
object of `theorem1_6` is given through `E F(·)` only. Own elementary proof (AGENT_GUIDE cost
rule).
-/

noncomputable section

open Filter Set Metric MeasureTheory
open scoped Topology ENNReal

namespace QuantumZipper

namespace LitSlutsky

/-- **Slutsky step.** -/
theorem tendsto_integral_sub {α : Type*} [MeasurableSpace α] (Q : Measure α)
    [IsProbabilityMeasure Q] {m : ℕ} (Xv Yv : ℝ → α → (Fin m → ℝ))
    (hX : ∀ C, AEMeasurable (Xv C) Q) (hY : ∀ C, AEMeasurable (Yv C) Q)
    {F : (Fin m → ℝ) → ℝ} (hF : Continuous F) {B : ℝ} (hB : ∀ v, |F v| ≤ B)
    (htight : ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, Q {p | M < ‖Xv C p‖} ≤ ENNReal.ofReal θ)
    (hclose : ∀ η > 0, Tendsto (fun C => Q {p | η ≤ ‖Yv C p - Xv C p‖}) atTop (𝓝 0)) :
    Tendsto (fun C => ∫ p, F (Yv C p) ∂Q - ∫ p, F (Xv C p) ∂Q) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B' := max B 1 with hB'
  have hB'0 : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB'' : ∀ v, |F v| ≤ B' := fun v => (hB v).trans (le_max_left _ _)
  set θ := ε / (8 * B') with hθ
  have hθ0 : 0 < θ := by positivity
  obtain ⟨M, hM⟩ := htight θ hθ0
  have hK : IsCompact (closedBall (0 : Fin m → ℝ) (M + 1)) := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hF.continuousOn) (ε / 4) (by positivity)
  set η := min δ 1 with hη
  have hη0 : 0 < η := lt_min hδ one_pos
  have hcl := hclose η hη0
  have hcl' : ∀ᶠ C in atTop, Q {p | η ≤ ‖Yv C p - Xv C p‖} ≤ ENNReal.ofReal θ :=
    hcl.eventually (Iic_mem_nhds (by simpa using hθ0))
  filter_upwards [hM, hcl'] with C hC1 hC2
  -- the bad set
  set bad := {p | M < ‖Xv C p‖} ∪ {p | η ≤ ‖Yv C p - Xv C p‖} with hbad
  have hbadm : NullMeasurableSet bad Q :=
    (nullMeasurableSet_lt aemeasurable_const (hX C).norm).union
      (nullMeasurableSet_le aemeasurable_const ((hY C).sub (hX C)).norm)
  have hbadQ : Q bad ≤ ENNReal.ofReal (2 * θ) := by
    calc Q bad ≤ Q {p | M < ‖Xv C p‖} + Q {p | η ≤ ‖Yv C p - Xv C p‖} := measure_union_le _ _
      _ ≤ ENNReal.ofReal θ + ENNReal.ofReal θ := add_le_add hC1 hC2
      _ = ENNReal.ofReal (2 * θ) := by
          rw [← ENNReal.ofReal_add hθ0.le hθ0.le]; ring_nf
  have hbadR : Q.real bad ≤ 2 * θ := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbadQ
  -- integrability
  have hIX : Integrable (fun p => F (Xv C p)) Q :=
    Integrable.of_bound (hF.measurable.comp_aemeasurable (hX C)).aestronglyMeasurable B'
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hB'' _)
  have hIY : Integrable (fun p => F (Yv C p)) Q :=
    Integrable.of_bound (hF.measurable.comp_aemeasurable (hY C)).aestronglyMeasurable B'
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hB'' _)
  have hIg : Integrable (fun p => ε / 4 + bad.indicator (fun _ => 2 * B') p) Q :=
    (integrable_const _).add ((integrable_const _).indicator₀ hbadm)
  -- pointwise bound
  have hpt : ∀ p, ‖F (Yv C p) - F (Xv C p)‖ ≤ ε / 4 + bad.indicator (fun _ => 2 * B') p := by
    intro p
    rw [Real.norm_eq_abs]
    by_cases hp : p ∈ bad
    · rw [indicator_of_mem hp]
      have h1 := hB'' (Yv C p); have h2 := hB'' (Xv C p)
      have := abs_sub (F (Yv C p)) (F (Xv C p))
      have : 0 < ε / 4 := by positivity
      linarith
    · rw [indicator_of_notMem hp, add_zero]
      simp only [hbad, mem_union, mem_ofPred_eq, not_or, not_lt, not_le] at hp
      have hXK : Xv C p ∈ closedBall (0 : Fin m → ℝ) (M + 1) := by
        rw [mem_closedBall, dist_zero_right]; linarith
      have hYK : Yv C p ∈ closedBall (0 : Fin m → ℝ) (M + 1) := by
        rw [mem_closedBall, dist_zero_right]
        have := norm_le_norm_add_norm_sub' (Yv C p) (Xv C p)
        have : η ≤ 1 := min_le_right _ _
        rw [show Yv C p - Xv C p = Yv C p - Xv C p from rfl] at *
        linarith [norm_sub_rev (Yv C p) (Xv C p)]
      have hd : dist (Yv C p) (Xv C p) < δ := by
        rw [dist_eq_norm]; exact hp.2.trans_le (min_le_left _ _)
      have := hδF _ hYK _ hXK hd
      rw [Real.dist_eq] at this
      exact this.le
  have hint := norm_integral_le_of_norm_le hIg (ae_of_all _ hpt)
  rw [integral_sub hIY hIX] at hint
  rw [integral_add (integrable_const _) ((integrable_const _).indicator₀ hbadm),
    integral_indicator₀ hbadm, setIntegral_const, integral_const, smul_eq_mul, smul_eq_mul,
    probReal_univ, one_mul] at hint
  rw [Real.dist_eq, sub_zero]
  rw [Real.norm_eq_abs] at hint
  have h8 : Q.real bad * (2 * B') ≤ 2 * θ * (2 * B') :=
    mul_le_mul_of_nonneg_right hbadR (by positivity)
  have h9 : 2 * θ * (2 * B') = ε / 2 := by rw [hθ]; field_simp; ring
  linarith

/-- The clipped norm `min 1 (max 0 (‖v‖ − M))`. -/
def clipN {m : ℕ} (M : ℝ) (v : Fin m → ℝ) : ℝ := min 1 (max 0 (‖v‖ - M))

theorem continuous_clipN {m : ℕ} (M : ℝ) : Continuous (clipN (m := m) M) :=
  continuous_const.min (continuous_const.max (continuous_norm.sub continuous_const))

theorem clipN_nonneg {m : ℕ} (M : ℝ) (v : Fin m → ℝ) : 0 ≤ clipN M v :=
  le_min zero_le_one (le_max_left _ _)

theorem clipN_le_one {m : ℕ} (M : ℝ) (v : Fin m → ℝ) : clipN M v ≤ 1 := min_le_left _ _

/-- **Tightness from convergence in law** (for `E F(·)`-convergence to an a.e.-measurable
limit). -/
theorem tight_of_tendsto {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (Q : Measure α)
    [IsProbabilityMeasure Q] (P' : Measure β) [IsProbabilityMeasure P'] {m : ℕ}
    (Xv : ℝ → α → (Fin m → ℝ)) (Zv : β → (Fin m → ℝ)) (hX : ∀ C, AEMeasurable (Xv C) Q)
    (hZ : AEMeasurable Zv P')
    (hconv : ∀ F : (Fin m → ℝ) → ℝ, Continuous F → (∃ B, ∀ v, |F v| ≤ B) →
      Tendsto (fun C => ∫ p, F (Xv C p) ∂Q) atTop (𝓝 (∫ ω, F (Zv ω) ∂P'))) :
    ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, Q {p | M < ‖Xv C p‖} ≤ ENNReal.ofReal θ := by
  intro θ hθ
  -- the limit side
  have hlim : Tendsto (fun n : ℕ => ∫ ω, clipN (n : ℝ) (Zv ω) ∂P') atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P')
      (F := fun (n : ℕ) ω => clipN (n : ℝ) (Zv ω)) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun n => ((continuous_clipN (n : ℝ)).measurable.comp_aemeasurable hZ).aestronglyMeasurable)
      (integrable_const _)
      (fun n => ae_of_all _ fun ω => by
        show ‖clipN (n : ℝ) (Zv ω)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (clipN_nonneg _ _)]; exact clipN_le_one _ _)
      (ae_of_all _ fun ω => by
        show Tendsto (fun n : ℕ => clipN (n : ℝ) (Zv ω)) atTop (𝓝 0)
        refine tendsto_const_nhds.congr' ?_
        obtain ⟨N, hN⟩ := exists_nat_ge ‖Zv ω‖
        filter_upwards [eventually_ge_atTop N] with n hn
        have : ‖Zv ω‖ - n ≤ 0 := by
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        simp [clipN, max_eq_left this])
    simpa using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (half_pos hθ))).exists
  have hc := hconv (clipN (n : ℝ)) (continuous_clipN _) ⟨1, fun v => by
    rw [abs_of_nonneg (clipN_nonneg _ _)]; exact clipN_le_one _ _⟩
  refine ⟨n + 1, ?_⟩
  filter_upwards [hc.eventually (gt_mem_nhds (show ∫ ω, clipN (n : ℝ) (Zv ω) ∂P' < θ by
    linarith))] with C hC
  set S := {p | (n : ℝ) + 1 < ‖Xv C p‖} with hS
  have hSm : NullMeasurableSet S Q := nullMeasurableSet_lt aemeasurable_const (hX C).norm
  have hI : Integrable (fun p => clipN (n : ℝ) (Xv C p)) Q :=
    Integrable.of_bound ((continuous_clipN _).measurable.comp_aemeasurable (hX C)).aestronglyMeasurable
      1 (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (clipN_nonneg _ _)]; exact clipN_le_one _ _)
  have hle : Q.real S ≤ ∫ p, clipN (n : ℝ) (Xv C p) ∂Q := by
    have h1 : ∫ p, S.indicator (fun _ => (1 : ℝ)) p ∂Q = Q.real S := by
      rw [integral_indicator₀ hSm, setIntegral_const, smul_eq_mul, mul_one]
    rw [← h1]
    refine integral_mono ((integrable_const _).indicator₀ hSm) hI fun p => ?_
    by_cases hp : p ∈ S
    · rw [indicator_of_mem hp]
      have hp' : (n : ℝ) + 1 < ‖Xv C p‖ := hp
      simp only [clipN]
      rw [min_eq_left]
      exact le_max_of_le_right (by linarith)
    · rw [indicator_of_notMem hp]; exact clipN_nonneg _ _
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hθ.le]
  rw [measureReal_def] at hle
  linarith

/-- **Closeness in probability from a pointwise bound at small scale.** If a scale `A C → 0`
in probability, `Φ C` is tight, and pointwise `‖Y C − X C‖ ≤ ε₀ Φ C` once `0 < A C < δ(p)`
(with `δ(p) > 0` independent of `C`), then `Y C − X C → 0` in probability. -/
theorem tendsto_close_of_pointwise {α : Type*} [MeasurableSpace α] (Q : Measure α)
    [IsProbabilityMeasure Q] {m : ℕ} (Xv Yv : ℝ → α → (Fin m → ℝ))
    (hX : ∀ C, AEMeasurable (Xv C) Q) (hY : ∀ C, AEMeasurable (Yv C) Q)
    (A Φ : ℝ → α → ℝ) (hΦm : ∀ C, AEMeasurable (Φ C) Q)
    (hA : ∀ δ > 0, Tendsto (fun C => Q {p | ¬ (0 < A C p ∧ A C p < δ)}) atTop (𝓝 0))
    (hΦ : ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, Q {p | M < Φ C p} ≤ ENNReal.ofReal θ)
    (hpt : ∀ ε₀ > 0, ∃ δ : α → ℝ, (∀ᵐ p ∂Q, 0 < δ p) ∧ ∀ C, ∀ᵐ p ∂Q,
      0 < A C p → A C p < δ p → ‖Yv C p - Xv C p‖ ≤ ε₀ * Φ C p) :
    ∀ η > 0, Tendsto (fun C => Q {p | η ≤ ‖Yv C p - Xv C p‖}) atTop (𝓝 0) := by
  intro η hη
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- a.e. convergence of the scale along a subsequence
  set g : ℕ → α → ℝ := fun n p => if 0 < A (ns n) p then A (ns n) p else 1 with hg
  have hgm : TendstoInMeasure Q g atTop (fun _ => (0 : ℝ)) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((hA _ (lt_min hε one_pos)).comp hns) (fun _ => bot_le) fun n => measure_mono fun p hp => ?_
    simp only [mem_ofPred_eq, Function.comp_apply] at hp ⊢
    rintro ⟨h1, h2⟩
    have hgv : g n p = A (ns n) p := by simp [hg, h1]
    rw [Real.dist_eq, sub_zero, hgv, abs_of_pos h1] at hp
    have := h2.trans_le (min_le_left _ _)
    linarith
  obtain ⟨ms, hms, hmsae⟩ := hgm.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hnsms : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  have hθ2 : 0 < θ / 2 := ENNReal.half_pos hθ.ne'
  rcases eq_or_ne θ ⊤ with hθt | hθt
  · exact Eventually.of_forall fun _ => by simp [hθt]
  have hθr : 0 < (θ / 2).toReal := ENNReal.toReal_pos hθ2.ne' (ENNReal.div_ne_top hθt two_ne_zero)
  obtain ⟨M, hM⟩ := hΦ _ hθr
  set ε₀ := η / (2 * (|M| + 1)) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  have hε₀M : ε₀ * M < η := by
    have h1 : ε₀ * M ≤ ε₀ * |M| := mul_le_mul_of_nonneg_left (le_abs_self M) hε₀0.le
    have h2 : ε₀ * |M| < ε₀ * (2 * (|M| + 1)) :=
      mul_lt_mul_of_pos_left (by linarith [abs_nonneg M]) hε₀0
    have h3 : ε₀ * (2 * (|M| + 1)) = η := by rw [hε₀]; field_simp
    linarith
  obtain ⟨δ, hδ0, hδ⟩ := hpt ε₀ hε₀0
  set T : ℕ → Set α := fun k =>
    {p | η ≤ ‖Yv (ns (ms k)) p - Xv (ns (ms k)) p‖} ∩ {p | Φ (ns (ms k)) p ≤ M} with hT
  have hTm : ∀ k, NullMeasurableSet (T k) Q := fun k =>
    (nullMeasurableSet_le aemeasurable_const ((hY _).sub (hX _)).norm).inter
      (nullMeasurableSet_le (hΦm _) aemeasurable_const)
  have hT0 : Tendsto (fun k => Q (T k)) atTop (𝓝 0) := by
    have hlim := tendsto_lintegral_filter_of_dominated_convergence' (μ := Q) (l := atTop)
      (F := fun k => (T k).indicator (1 : α → ℝ≥0∞)) (f := fun _ => 0) (fun _ => 1)
      (Eventually.of_forall fun k => aemeasurable_const.indicator₀ (hTm k))
      (Eventually.of_forall fun k => ae_of_all _ fun p =>
        Set.indicator_le (fun _ _ => le_rfl) p)
      (by simp) ?_
    · simpa [lintegral_indicator₀ (hTm _)] using hlim
    have hall : ∀ᵐ p ∂Q, ∀ k, 0 < A (ns (ms k)) p → A (ns (ms k)) p < δ p →
        ‖Yv (ns (ms k)) p - Xv (ns (ms k)) p‖ ≤ ε₀ * Φ (ns (ms k)) p :=
      ae_all_iff.2 fun k => hδ _
    filter_upwards [hmsae, hδ0, hall] with p hp hpδ hpall
    refine tendsto_const_nhds.congr' ?_
    have hev := hp.eventually (gt_mem_nhds (lt_min hpδ one_pos))
    filter_upwards [hev] with k hk
    have hk1 : g (ms k) p < 1 := hk.trans_le (min_le_right _ _)
    have hpos : 0 < A (ns (ms k)) p := by
      by_contra hneg
      simp [hg, hneg] at hk1
    have hgv : g (ms k) p = A (ns (ms k)) p := by simp [hg, hpos]
    have hsm : A (ns (ms k)) p < δ p := by
      rw [← hgv]; exact hk.trans_le (min_le_left _ _)
    have hb := hpall k hpos hsm
    have hnot : p ∉ T k := by
      rintro ⟨h1, h2⟩
      have h2' : Φ (ns (ms k)) p ≤ M := h2
      have h1' : η ≤ ‖Yv (ns (ms k)) p - Xv (ns (ms k)) p‖ := h1
      have := mul_le_mul_of_nonneg_left h2' hε₀0.le
      linarith
    simp [indicator_of_notMem hnot]
  filter_upwards [hnsms.eventually hM, hT0.eventually (Iic_mem_nhds hθ2)] with k hk1 hk2
  calc Q {p | η ≤ ‖Yv (ns (ms k)) p - Xv (ns (ms k)) p‖}
      ≤ Q {p | M < Φ (ns (ms k)) p} + Q (T k) := by
        refine (measure_mono fun p hp => ?_).trans (measure_union_le _ _)
        by_cases h : M < Φ (ns (ms k)) p
        · exact Or.inl h
        · exact Or.inr ⟨hp, not_lt.1 h⟩
    _ ≤ θ / 2 + θ / 2 := by
        refine add_le_add (hk1.trans ?_) hk2
        rw [ENNReal.ofReal_toReal (ENNReal.div_ne_top hθt two_ne_zero)]
        
    _ = θ := ENNReal.add_halves θ

end LitSlutsky

end QuantumZipper
