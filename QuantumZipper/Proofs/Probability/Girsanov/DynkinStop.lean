import QuantumZipper.Proofs.Thm11.FrozenLocalDynkin

/-!
# GIR-D: local Dynkin formula between two stopping times

Blueprint `blueprint/GIRSANOV_BLUEPRINT.md`, §2, node GIR-D.

Context of `FrozenMart.martingale_localDynkin_stopped` / `RS.integral_localDynkin_stopped_le`:
`U` solves `U_t = u + ∫₀ᵗ b(U) + B_t e` (`b` bounded Lipschitz), `F` is `C³` on the open set `O`,
`|F| ≤ M` on the closed set `K ⊆ O`, and `U` stays in `K` up to its hitting time
`τ = hittingBtwn U Cl 0 T` of the closed set `Cl` (capped at `T`).

* `Girsanov.integral_mul_localDynkin_stopped_le`: if `dynkinGen b e F ≤ 0` on `K \ Cl`, then for
  stopping times `ρ ≤ σ ≤ τ` and a bounded nonnegative `𝓕_ρ`-measurable `Y`,
  `E[Y F(U_σ)] ≤ E[Y F(U_ρ)]`.
* `Girsanov.integral_mul_localDynkin_stopped_eq`: the equality version when
  `dynkinGen b e F = 0` on `K \ Cl`.

Proof (the argument of EXT-RS P1, `RS.integral_localDynkin_stopped_le`, with optional sampling at
two stopping times in place of the deterministic times `0, T`): smooth cutoffs `F_R`, IL-3
`Dynkin.dynkin_additive` gives the martingale `N^R_t = F_R(U_t) − F_R(u) − ∫₀ᵗ L F_R(U)`;
frozen at `T` and stopped at the exit time `θ_R` of `Cl ∪ {‖x‖ ≥ R}` it is a bounded continuous
martingale `S^R` (IL-4). Optional sampling at `σ` and at `ρ` (`ItoLite.integral_mul_stoppedValue_eq_of_le`,
the continuous-time optional stopping theorem, Le Gall, *Brownian Motion, Martingales, and
Stochastic Calculus*, GTM 274, Springer 2016, Theorem 3.22, pp. 59–60) gives
`E[Y S^R_σ] = E[Y S^R_T] = E[Y S^R_ρ]`, and `F_R(U_{σ∧θ_R}) − F_R(U_{ρ∧θ_R})
= S^R_σ − S^R_ρ + ∫_{ρ∧θ_R}^{σ∧θ_R} L F_R(U) ≤ S^R_σ − S^R_ρ`. Let `R → ∞` by dominated
convergence (`θ_R = τ` for large `R`). This replaces Itô's formula (Le Gall, Thm 5.10, p. 113)
applied between two stopping times. The equality version follows by applying the inequality to
`F` and `-F`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Girsanov

open FrozenMart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Local Dynkin formula between two stopping times, supermartingale version (GIR-D).** Let `U`
solve `U_t = u + ∫₀ᵗ b(U) + B_t e` (`b` bounded Lipschitz), let `F` be `C³` on the open set `O`,
with `dynkinGen b e F ≤ 0` on `K \ Cl`, where `K ⊆ O` is closed, `Cl` is closed, and `|F| ≤ M`
on `K`. Assume `U` stays in `K` up to (and including) each time before which it has not met
`Cl` (up to `T`), and let `τ = hittingBtwn U Cl 0 T`. Then for stopping times `ρ ≤ σ ≤ τ` and
every `𝓕_ρ`-measurable `Y` with `0 ≤ Y ≤ CY`, `E[Y F(U_σ)] ≤ E[Y F(U_ρ)]`. -/
theorem integral_mul_localDynkin_stopped_le (hB : IsPreBrownianReal B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {b : E → E} {Lb : ℝ≥0} {Mb : ℝ} (hb : LipschitzWith Lb b) (hbM : ∀ x, ‖b x‖ ≤ Mb)
    {u e : E} {U : ℝ≥0 → Ω → E}
    (hU : ∀ ω (t : ℝ≥0), U t ω = u + (∫ r in (0 : ℝ)..t, b (U r.toNNReal ω)) + B t ω • e)
    {O Cl K : Set E} (hO : IsOpen O) (hCl : IsClosed Cl) (hK : IsClosed K) (hKO : K ⊆ O)
    {F : E → ℝ} (hF : ContDiffOn ℝ 3 F O) (hLF : ∀ x ∈ K, x ∉ Cl → dynkinGen b e F x ≤ 0)
    (T : ℝ≥0) (hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K)
    {M : ℝ} (hFM : ∀ x ∈ K, |F x| ≤ M)
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ) (hσ : IsStoppingTime 𝓕 σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω)
    (hστ : ∀ ω, σ ω ≤ ((hittingBtwn U Cl 0 T ω : ℝ≥0) : WithTop ℝ≥0)) {Y : Ω → ℝ}
    (hY : Measurable[hρ.measurableSpace] Y) (hY0 : ∀ ω, 0 ≤ Y ω) {CY : ℝ}
    (hYb : ∀ ω, Y ω ≤ CY) :
    ∫ ω, Y ω * F (stoppedValue U σ ω) ∂P ≤ ∫ ω, Y ω * F (stoppedValue U ρ ω) ∂P := by
  have hστ' := hστ
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hbc : Continuous b := hb.continuous
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc hbc hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 hBad hBc hb hbM hU hUc
  have hUad : Adapted 𝓕 U := hUm
  -- cutoffs
  have hcut : ∀ R : ℕ, ∃ f : E → ℝ, ContDiff ℝ 3 f ∧ (∀ x, f x ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport f ∧ tsupport f ⊆ O ∧ ∀ x ∈ K ∩ closedBall 0 (R : ℝ), f =ᶠ[𝓝 x] 1 :=
    fun R => exists_cutoff_of_isCompact ((isCompact_closedBall (0 : E) (R : ℝ)).inter_left hK) hO
      (inter_subset_left.trans hKO)
  choose f hfd hfr hfc hfO hf1 using hcut
  set FR : ℕ → E → ℝ := fun R x => f R x * F x with hFR_def
  have hFRd : ∀ R, ContDiff ℝ 3 (FR R) := by
    intro R
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact (hfd R).contDiffAt.mul (hF.contDiffAt (hO.mem_nhds hx))
    · have hx' : x ∉ tsupport (f R) := fun h => hx (hfO R h)
      rw [notMem_tsupport_iff_eventuallyEq] at hx'
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hx'] with y hy
      show f R y * F y = 0
      rw [hy, Pi.zero_apply, zero_mul]
  have hFRc : ∀ R, HasCompactSupport (FR R) := fun R => (hfc R).mul_right
  have hbound : ∀ R, ∃ C, ∀ x, ‖fderiv ℝ (FR R) x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 (FR R) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 3 (FR R) x‖ ≤ C := by
    intro R
    obtain ⟨C1, h1⟩ := ((hFRd R).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
      ((hFRc R).fderiv (𝕜 := ℝ))
    obtain ⟨C2, h2⟩ := ((hFRd R).continuous_iteratedFDeriv (m := 2)
      (by norm_num)).bounded_above_of_compact_support ((hFRc R).iteratedFDeriv 2)
    obtain ⟨C3, h3⟩ := ((hFRd R).continuous_iteratedFDeriv (m := 3)
      (by norm_num)).bounded_above_of_compact_support ((hFRc R).iteratedFDeriv 3)
    exact ⟨max C1 (max C2 C3), fun x => ⟨(h1 x).trans (le_max_left _ _),
      (h2 x).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (h3 x).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩
  choose C hC using hbound
  have hC0 : ∀ R, 0 ≤ C R := fun R => (norm_nonneg _).trans (hC R 0).1
  have hF0 : ∀ R, ∃ C0, ∀ x, ‖FR R x‖ ≤ C0 := fun R =>
    (hFRd R).continuous.bounded_above_of_compact_support (hFRc R)
  choose C0 hC0' using hF0
  set LR : ℕ → E → ℝ := fun R => dynkinGen b e (FR R) with hLR_def
  have hLRc : ∀ R, Continuous (LR R) := fun R => Dynkin.continuous_dynkinGen (hFRd R) hbc e
  have hLRb : ∀ R x, |LR R x| ≤ C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2) := by
    intro R x
    simp only [LR, dynkinGen]
    have h1 : |fderiv ℝ (FR R) x (b x)| ≤ C R * Mb := by
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ (FR R) x).le_opNorm (b x)).trans
        (mul_le_mul (hC R x).1 (hbM x) (norm_nonneg _) (hC0 R))
    have h2 : |iteratedFDeriv ℝ 2 (FR R) x ![e, e]| ≤ C R * ‖e‖ ^ 2 :=
      (Dynkin.abs_iteratedFDeriv_two_vec_le _ x e).trans
        (mul_le_mul_of_nonneg_right (hC R x).2.1 (by positivity))
    calc _ ≤ |fderiv ℝ (FR R) x (b x)| + |1 / 2 * iteratedFDeriv ℝ 2 (FR R) x ![e, e]| :=
          abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          gcongr
  -- generator of the cutoff equals the generator of `F` near `K ∩ closedBall 0 R`
  have hLReq : ∀ (R : ℕ) x, x ∈ K ∩ closedBall 0 (R : ℝ) → LR R x = dynkinGen b e F x := by
    intro R x hx
    have hev : FR R =ᶠ[𝓝 x] F := (hf1 R x hx).mono fun y hy => by
      show f R y * F y = F y
      rw [hy, Pi.one_apply, one_mul]
    simp only [LR, dynkinGen, hev.fderiv_eq, (hev.iteratedFDeriv ℝ 2).eq_of_nhds]
  -- Dynkin martingales, frozen at `T`
  set MR : ℕ → ℝ≥0 → Ω → ℝ := fun R t ω =>
    FR R (U t ω) - FR R u - ∫ r in (0 : ℝ)..t, LR R (U r.toNNReal ω) with hMR_def
  have hMR : ∀ R, Martingale (MR R) 𝓕 P := fun R =>
    Dynkin.dynkin_additive hB hBc 𝓕 hBad hpast hb hbM hU (hFRd R) (hC R)
  have hNR : ∀ R, Martingale (fun t => MR R (min t T)) 𝓕 P := fun R =>
    martingale_min_const (hMR R) T
  have hMRc : ∀ R ω, Continuous fun t => MR R t ω := by
    intro R ω
    have hg : Continuous fun r : ℝ => LR R (U r.toNNReal ω) :=
      (hLRc R).comp ((hUc ω).comp continuous_real_toNNReal)
    have hprim := intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hg.intervalIntegrable a b) 0
    exact (((hFRd R).continuous.comp (hUc ω)).sub continuous_const).sub
      (hprim.comp NNReal.continuous_coe)
  have hNRc : ∀ R ω, Continuous fun t => MR R (min t T) ω := fun R ω =>
    (hMRc R ω).comp (continuous_id.min continuous_const)
  have hNRb : ∀ R t ω, |MR R (min t T) ω| ≤
      C0 R + C0 R + (C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2)) * T := by
    intro R t ω
    simp only [MR]
    have h1 := hC0' R (U (min t T) ω)
    have h2 := hC0' R u
    have h3 : ‖∫ r in (0 : ℝ)..((min t T : ℝ≥0) : ℝ), LR R (U r.toNNReal ω)‖ ≤
        (C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2)) * T := by
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun r _ => by rw [Real.norm_eq_abs]; exact hLRb R _)).trans ?_
      rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      have hK0 : 0 ≤ C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2) :=
        (abs_nonneg _).trans (hLRb R 0)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right t T) hK0
    rw [Real.norm_eq_abs] at h1 h2 h3
    calc _ ≤ |FR R (U (min t T) ω) - FR R u| + |∫ r in (0 : ℝ)..((min t T : ℝ≥0) : ℝ),
          LR R (U r.toNNReal ω)| := abs_sub _ _
      _ ≤ |FR R (U (min t T) ω)| + |FR R u| + _ := by gcongr; exact abs_sub _ _
      _ ≤ _ := by gcongr
  -- stopping times
  set ClR : ℕ → Set E := fun R => Cl ∪ {x | (R : ℝ) ≤ ‖x‖} with hClR_def
  have hClR : ∀ R, IsClosed (ClR R) := fun R =>
    hCl.union (isClosed_le continuous_const continuous_norm)
  set θ : ℕ → Ω → ℝ≥0 := fun R ω => hittingBtwn U (ClR R) 0 T ω with hθ_def
  have hθst : ∀ R, IsStoppingTime 𝓕 (fun ω => ((θ R ω : ℝ≥0) : WithTop ℝ≥0)) := fun R =>
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUad hUc (hClR R) T
  have hθT : ∀ R ω, θ R ω ≤ T := fun R ω => hittingBtwn_le ω
  -- before `θ R`, the path is in `K`, off `Cl`, and inside the ball
  have hbefore : ∀ R ω (q : ℝ≥0), q < θ R ω → U q ω ∉ ClR R := fun R ω q hq =>
    notMem_of_lt_hittingBtwn hq zero_le
  have hK_of : ∀ R ω (s : ℝ≥0), s ≤ θ R ω → U s ω ∈ K := fun R ω s hs =>
    hUK ω s (hs.trans (hθT R ω)) fun q hq h => hbefore R ω q (hq.trans_le hs) (Or.inl h)
  have hLR0 : ∀ R ω (q : ℝ≥0), q < θ R ω → LR R (U q ω) ≤ 0 := by
    intro R ω q hq
    have hnot := hbefore R ω q hq
    have hball : U q ω ∈ closedBall (0 : E) (R : ℝ) := by
      rw [mem_closedBall_zero_iff]
      exact le_of_lt (not_le.mp fun h => hnot (Or.inr h))
    rw [hLReq R _ ⟨hK_of R ω q hq.le, hball⟩]
    exact hLF _ (hK_of R ω q hq.le) fun h => hnot (Or.inl h)
  -- the stopped cutoff processes
  set G : ℕ → ℝ≥0 → Ω → ℝ := fun R t ω => FR R (U (min t (θ R ω)) ω) with hG_def
  have hGb : ∀ R t ω, |G R t ω| ≤ M := by
    intro R t ω
    simp only [G, FR]
    rw [abs_mul]
    have hf := hfr R (U (min t (θ R ω)) ω)
    have hfa : |f R (U (min t (θ R ω)) ω)| ≤ 1 := by rw [abs_of_nonneg hf.1]; exact hf.2
    calc _ ≤ 1 * |F (U (min t (θ R ω)) ω)| := by gcongr
      _ ≤ M := by rw [one_mul]; exact hFM _ (hK_of R ω _ (min_le_right _ _))
  -- identification for large `R`
  set τ : Ω → ℝ≥0 := fun ω => hittingBtwn U Cl 0 T ω with hτ_def
  have hlarge : ∀ ω, ∃ R0 : ℕ, ∀ R ≥ R0, ∀ t, G R t ω = F (U (min t (τ ω)) ω) := by
    intro ω
    obtain ⟨Rb, hRb⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hUc ω).continuousOn
    refine ⟨⌈Rb⌉₊ + 1, fun R hR t => ?_⟩
    have hRlt : Rb < R := by
      have h1 : (⌈Rb⌉₊ : ℝ) + 1 ≤ R := by exact_mod_cast hR
      linarith [Nat.le_ceil Rb]
    have hθτ : θ R ω = τ ω := by
      have hiff : ∀ j ∈ Icc (0 : ℝ≥0) T, (U j ω ∈ ClR R ↔ U j ω ∈ Cl) := by
        intro j hj
        refine ⟨fun h => h.resolve_right fun h' => ?_, Or.inl⟩
        have := hRb j hj
        simp only [mem_setOf_eq] at h'
        linarith
      have hex : (∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ ClR R) ↔ ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl :=
        ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, (hiff j hj).1 h⟩, fun ⟨j, hj, h⟩ => ⟨j, hj, (hiff j hj).2 h⟩⟩
      have hset : Icc (0 : ℝ≥0) T ∩ {i | U i ω ∈ ClR R} = Icc (0 : ℝ≥0) T ∩ {i | U i ω ∈ Cl} := by
        ext j
        exact ⟨fun ⟨hj, h⟩ => ⟨hj, (hiff j hj).1 h⟩, fun ⟨hj, h⟩ => ⟨hj, (hiff j hj).2 h⟩⟩
      simp only [θ, τ, hittingBtwn, hset]
      by_cases h : ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl
      · rw [if_pos h, if_pos (hex.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (hex.1 h'))]
    simp only [G, FR]
    rw [hθτ]
    have hmemK : U (min t (τ ω)) ω ∈ K := by
      have := hK_of R ω (min t (τ ω)) (by rw [hθτ]; exact min_le_right _ _)
      exact this
    have hball : U (min t (τ ω)) ω ∈ closedBall (0 : E) (R : ℝ) := by
      rw [mem_closedBall_zero_iff]
      have hτT : τ ω ≤ T := hittingBtwn_le ω
      exact (hRb _ ⟨zero_le, (min_le_right _ _).trans hτT⟩).trans hRlt.le
    rw [(hf1 R _ ⟨hmemK, hball⟩).self_of_nhds, Pi.one_apply, one_mul]
  -- the two stopping times are finite and bounded by `τ ≤ T`
  have hστ2 : ∀ ω, σ ω ≤ (τ ω : WithTop ℝ≥0) := hστ'
  have hρτ2 : ∀ ω, ρ ω ≤ (τ ω : WithTop ℝ≥0) := fun ω => (hρσ ω).trans (hστ2 ω)
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hYabs : ∀ ω, |Y ω| ≤ CY := fun ω => by rw [abs_of_nonneg (hY0 ω)]; exact hYb ω
  have hYm : Measurable Y := hY.mono hρ.measurableSpace_le le_rfl
  -- a stopping time `κ ≤ τ`: its real value is `≤ τ`, and it is the coercion of it
  have hkτ : ∀ κ : Ω → WithTop ℝ≥0, (∀ ω, κ ω ≤ (τ ω : WithTop ℝ≥0)) →
      ∀ ω, (κ ω).untopA ≤ τ ω ∧ κ ω = ((κ ω).untopA : WithTop ℝ≥0) := by
    intro κ hκ ω
    have hκT : ∀ ω, κ ω ≤ (T : WithTop ℝ≥0) := fun ω =>
      (hκ ω).trans (WithTop.coe_le_coe.2 (hτT ω))
    have heq := ItoLite.eq_coe_untopA_of_le hκT ω
    refine ⟨?_, heq⟩
    have := hκ ω
    rwa [heq, WithTop.coe_le_coe] at this
  -- increments of the drift integral are `≤ 0` before `θ R`
  have hLRi : ∀ R ω (x y : ℝ), IntervalIntegrable (fun r : ℝ => LR R (U r.toNNReal ω)) volume x y :=
    fun R ω x y => ((hLRc R).comp ((hUc ω).comp continuous_real_toNNReal)).intervalIntegrable x y
  have hint01 : ∀ R ω (x y : ℝ≥0), x ≤ y → y ≤ θ R ω →
      (∫ r in (0 : ℝ)..(y : ℝ), LR R (U r.toNNReal ω))
        - ∫ r in (0 : ℝ)..(x : ℝ), LR R (U r.toNNReal ω) ≤ 0 := by
    intro R ω x y hxy hy
    rw [intervalIntegral.integral_interval_sub_left (hLRi R ω 0 y) (hLRi R ω 0 x),
      intervalIntegral.integral_of_le (NNReal.coe_le_coe.2 hxy), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_nonpos measurableSet_Ioo fun r hr => ?_
    have hlt : r.toNNReal < θ R ω := by
      refine lt_of_lt_of_le ?_ hy
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (x.coe_nonneg.trans hr.1.le)]
      exact hr.2
    exact hLR0 R ω _ hlt
  -- measurability of the stopped cutoff values at a stopping time
  have hprog : IsStronglyProgressive 𝓕 U :=
    (hUad.stronglyAdapted).isStronglyProgressive_of_continuous hUc
  have hGκm : ∀ R (κ : Ω → WithTop ℝ≥0), IsStoppingTime 𝓕 κ →
      (∀ ω, κ ω ≤ (τ ω : WithTop ℝ≥0)) →
      StronglyMeasurable fun ω => Y ω * G R (κ ω).untopA ω := by
    intro R κ hκ hκτ
    have hmin := hκ.min (hθst R)
    have h := (measurable_stoppedValue hprog hmin).mono hmin.measurableSpace_le le_rfl
    have heq : stoppedValue U (fun ω => min (κ ω) ((θ R ω : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => U (min (κ ω).untopA (θ R ω)) ω := by
      funext ω
      simp only [stoppedValue]
      rw [(hkτ κ hκτ ω).2, ← WithTop.coe_min, ItoLite.untopA_coe_nnreal,
        ItoLite.untopA_coe_nnreal]
    rw [heq] at h
    exact hYm.stronglyMeasurable.mul ((hFRd R).continuous.comp_stronglyMeasurable
      h.stronglyMeasurable)
  -- the supermartingale inequality for each cutoff
  have hstep : ∀ R, ∫ ω, Y ω * G R (σ ω).untopA ω ∂P ≤ ∫ ω, Y ω * G R (ρ ω).untopA ω ∂P := by
    intro R
    set SR : ℝ≥0 → Ω → ℝ := fun t ω => MR R (min (min t (θ R ω)) T) ω with hSR_def
    have hSR : Martingale SR 𝓕 P :=
      ItoLite.martingale_stopped_of_continuous (hNR R) (hNRc R) (hNRb R) (hθst R)
    have hSRc : ∀ ω, Continuous (SR · ω) := fun ω =>
      (hNRc R ω).comp (continuous_id.min continuous_const)
    have hSRb : ∀ t ω, |SR t ω| ≤ C0 R + C0 R + (C R * Mb + 1 / 2 * (C R * ‖e‖ ^ 2)) * T :=
      fun t ω => hNRb R _ ω
    have hSRprog : IsStronglyProgressive 𝓕 SR :=
      hSR.stronglyAdapted.isStronglyProgressive_of_continuous hSRc
    have hσT : ∀ ω, σ ω ≤ (T : WithTop ℝ≥0) := fun ω =>
      (hστ2 ω).trans (WithTop.coe_le_coe.2 (hτT ω))
    have hρT' : ∀ ω, ρ ω ≤ (T : WithTop ℝ≥0) := fun ω =>
      (hρτ2 ω).trans (WithTop.coe_le_coe.2 (hτT ω))
    have hYσ : Measurable[hσ.measurableSpace] Y :=
      hY.mono (hρ.measurableSpace_mono hσ hρσ) le_rfl
    have h1 := ItoLite.integral_mul_stoppedValue_eq_of_le hSR hSRc hSRb hσ hσT hYσ hYabs
    have h2 := ItoLite.integral_mul_stoppedValue_eq_of_le hSR hSRc hSRb hρ hρT' hY hYabs
    have hSκ : ∀ (κ : Ω → WithTop ℝ≥0), IsStoppingTime 𝓕 κ →
        Integrable (fun ω => Y ω * stoppedValue SR κ ω) P := by
      intro κ hκ
      exact ItoLite.integrable_of_bound_abs (hYm.stronglyMeasurable.mul
        ((measurable_stoppedValue hSRprog hκ).mono hκ.measurableSpace_le le_rfl).stronglyMeasurable)
        (fun ω => ItoLite.abs_mul_le_of_le (hYabs ω) (hSRb _ ω))
    have hGκi : ∀ (κ : Ω → WithTop ℝ≥0), IsStoppingTime 𝓕 κ →
        (∀ ω, κ ω ≤ (τ ω : WithTop ℝ≥0)) →
        Integrable (fun ω => Y ω * G R (κ ω).untopA ω) P := fun κ hκ hκτ =>
      ItoLite.integrable_of_bound_abs (hGκm R κ hκ hκτ)
        (fun ω => ItoLite.abs_mul_le_of_le (hYabs ω) (hGb R _ ω))
    -- pointwise comparison
    have hpt : ∀ ω, Y ω * G R (σ ω).untopA ω - Y ω * G R (ρ ω).untopA ω ≤
        Y ω * stoppedValue SR σ ω - Y ω * stoppedValue SR ρ ω := by
      intro ω
      set a := (ρ ω).untopA
      set c := (σ ω).untopA
      have hac : a ≤ c := by
        have h := hρσ ω
        rwa [(hkτ ρ hρτ2 ω).2, (hkτ σ hστ2 ω).2, WithTop.coe_le_coe] at h
      have haT : min a (θ R ω) ≤ T := (min_le_right _ _).trans (hθT R ω)
      have hcT : min c (θ R ω) ≤ T := (min_le_right _ _).trans (hθT R ω)
      have hi := hint01 R ω (min a (θ R ω)) (min c (θ R ω)) (min_le_min_right _ hac)
        (min_le_right _ _)
      simp only [stoppedValue, hSR_def, MR, G]
      rw [← mul_sub, ← mul_sub, min_eq_left haT, min_eq_left hcT]
      refine mul_le_mul_of_nonneg_left ?_ (hY0 ω)
      linarith
    have hint : ∫ ω, (Y ω * G R (σ ω).untopA ω - Y ω * G R (ρ ω).untopA ω) ∂P ≤
        ∫ ω, (Y ω * stoppedValue SR σ ω - Y ω * stoppedValue SR ρ ω) ∂P :=
      integral_mono ((hGκi σ hσ hστ2).sub (hGκi ρ hρ hρτ2))
      ((hSκ σ hσ).sub (hSκ ρ hρ)) hpt
    rw [integral_sub (hGκi σ hσ hστ2) (hGκi ρ hρ hρτ2), integral_sub (hSκ σ hσ) (hSκ ρ hρ),
      h1, h2, sub_self] at hint
    linarith
  -- limit `R → ∞`
  have hDCT : ∀ (κ : Ω → WithTop ℝ≥0), IsStoppingTime 𝓕 κ → (∀ ω, κ ω ≤ (τ ω : WithTop ℝ≥0)) →
      Tendsto (fun R => ∫ ω, Y ω * G R (κ ω).untopA ω ∂P) atTop
        (𝓝 (∫ ω, Y ω * F (stoppedValue U κ ω) ∂P)) := by
    intro κ hκ hκτ
    refine tendsto_integral_of_dominated_convergence (fun _ => CY * M)
      (fun R => (hGκm R κ hκ hκτ).aestronglyMeasurable)
      (integrable_const _) (fun R => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · rw [Real.norm_eq_abs]
      exact ItoLite.abs_mul_le_of_le (hYabs ω) (hGb R _ ω)
    · obtain ⟨R0, hR0⟩ := hlarge ω
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R0, fun R hR => ?_⟩)
      show _ = Y ω * G R (κ ω).untopA ω
      rw [hR0 R hR, min_eq_left (hkτ κ hκτ ω).1]
      rfl
  exact le_of_tendsto_of_tendsto' (hDCT σ hσ hστ2) (hDCT ρ hρ hρτ2) hstep

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `dynkinGen` is odd in the test function. -/
theorem dynkinGen_neg (b : E → E) (e : E) (F : E → ℝ) (x : E) :
    dynkinGen b e (-F) x = -dynkinGen b e F x := by
  simp only [dynkinGen, fderiv_neg, iteratedFDeriv_neg_apply, neg_apply]
  ring

/-- **Local Dynkin formula between two stopping times, martingale version (GIR-D).** Same
context as `integral_mul_localDynkin_stopped_le`, with `dynkinGen b e F = 0` on `K \ Cl`; then
for stopping times `ρ ≤ σ ≤ τ` and every `𝓕_ρ`-measurable `Y` with `0 ≤ Y ≤ CY`,
`E[Y F(U_σ)] = E[Y F(U_ρ)]`. -/
theorem integral_mul_localDynkin_stopped_eq (hB : IsPreBrownianReal B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {b : E → E} {Lb : ℝ≥0} {Mb : ℝ} (hb : LipschitzWith Lb b) (hbM : ∀ x, ‖b x‖ ≤ Mb)
    {u e : E} {U : ℝ≥0 → Ω → E}
    (hU : ∀ ω (t : ℝ≥0), U t ω = u + (∫ r in (0 : ℝ)..t, b (U r.toNNReal ω)) + B t ω • e)
    {O Cl K : Set E} (hO : IsOpen O) (hCl : IsClosed Cl) (hK : IsClosed K) (hKO : K ⊆ O)
    {F : E → ℝ} (hF : ContDiffOn ℝ 3 F O) (hLF : ∀ x ∈ K, x ∉ Cl → dynkinGen b e F x = 0)
    (T : ℝ≥0) (hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K)
    {M : ℝ} (hFM : ∀ x ∈ K, |F x| ≤ M)
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ) (hσ : IsStoppingTime 𝓕 σ)
    (hρσ : ∀ ω, ρ ω ≤ σ ω)
    (hστ : ∀ ω, σ ω ≤ ((hittingBtwn U Cl 0 T ω : ℝ≥0) : WithTop ℝ≥0)) {Y : Ω → ℝ}
    (hY : Measurable[hρ.measurableSpace] Y) (hY0 : ∀ ω, 0 ≤ Y ω) {CY : ℝ}
    (hYb : ∀ ω, Y ω ≤ CY) :
    ∫ ω, Y ω * F (stoppedValue U σ ω) ∂P = ∫ ω, Y ω * F (stoppedValue U ρ ω) ∂P := by
  have h1 := integral_mul_localDynkin_stopped_le hB hBc 𝓕 hBad hpast hb hbM hU hO hCl hK hKO hF
    (fun x hx hx' => (hLF x hx hx').le) T hUK hFM hρ hσ hρσ hστ hY hY0 hYb
  have h2 := integral_mul_localDynkin_stopped_le hB hBc 𝓕 hBad hpast hb hbM hU hO hCl hK hKO
    (F := -F) hF.neg (fun x hx hx' => by rw [dynkinGen_neg, hLF x hx hx', neg_zero])
    T hUK (M := M) (fun x hx => by rw [Pi.neg_apply, abs_neg]; exact hFM x hx)
    hρ hσ hρσ hστ hY hY0 hYb
  simp only [Pi.neg_apply, mul_neg, integral_neg, neg_le_neg_iff] at h2
  exact le_antisymm h1 h2

end Girsanov
end QuantumZipper
