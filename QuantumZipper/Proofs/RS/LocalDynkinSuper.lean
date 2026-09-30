import QuantumZipper.Proofs.Thm11.FrozenLocalDynkin

/-!
# RS P1: local Dynkin formula, supermartingale version

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §2, node P1.

`RS.integral_localDynkin_stopped_le`: same hypotheses as
`FrozenMart.martingale_localDynkin_stopped`, but with `dynkinGen b e F ≤ 0` on `K \ Cl`; then
`E F(U_{T ∧ τ}) ≤ F(u)`.

Proof: the argument of `FrozenMart.martingale_localDynkin_stopped` (smooth cutoffs, IL-3
`Dynkin.dynkin_additive`, stopping at the hitting time of `Cl ∪ {‖x‖ ≥ R}`, dominated
convergence as `R → ∞`), except that the drift integral `∫₀^{T∧ρ_R} LF(U)` is now `≤ 0` and is
dropped. This replaces the use of Itô's formula for supermartingales (Kemppainen, *SLE*,
Thm 2.7, p. 24; Rohde–Schramm, Ann. Math. 161 (2005), proof of Thm 3.2, p. 10).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

open FrozenMart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Local Dynkin formula, supermartingale version (RS P1).** Let `U` solve
`U_t = u + ∫₀ᵗ b(U) + B_t e` (`b` bounded Lipschitz), let `F` be `C³` on the open set `O`, with
`dynkinGen b e F ≤ 0` on `K \ Cl`, where `K ⊆ O` is closed, `Cl` is closed, and `|F| ≤ M` on
`K`. If `U` stays in `K` up to (and including) each time before which it has not met `Cl` (up to
`T`), then `E F(U_{T ∧ τ}) ≤ F(u)` with `τ = hittingBtwn U Cl 0 T`. -/
theorem integral_localDynkin_stopped_le (hB : IsPreBrownianReal B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (𝓕 : Filtration ℝ≥0 mΩ) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hpast : ∀ t, 𝓕 t ≤ MeasurableSpace.comap (fun ω (r : Set.Iic t) => B r ω) MeasurableSpace.pi)
    {b : E → E} {Lb : ℝ≥0} {Mb : ℝ} (hb : LipschitzWith Lb b) (hbM : ∀ x, ‖b x‖ ≤ Mb)
    {u e : E} {U : ℝ≥0 → Ω → E}
    (hU : ∀ ω (t : ℝ≥0), U t ω = u + (∫ r in (0 : ℝ)..t, b (U r.toNNReal ω)) + B t ω • e)
    {O Cl K : Set E} (hO : IsOpen O) (hCl : IsClosed Cl) (hK : IsClosed K) (hKO : K ⊆ O)
    {F : E → ℝ} (hF : ContDiffOn ℝ 3 F O) (hLF : ∀ x ∈ K, x ∉ Cl → dynkinGen b e F x ≤ 0)
    (T : ℝ≥0) (hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl) → U t ω ∈ K)
    {M : ℝ} (hFM : ∀ x ∈ K, |F x| ≤ M) :
    ∫ ω, F (U (min T (hittingBtwn U Cl 0 T ω)) ω) ∂P ≤ F u := by
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
  set ρ : ℕ → Ω → ℝ≥0 := fun R ω => hittingBtwn U (ClR R) 0 T ω with hρ_def
  have hρst : ∀ R, IsStoppingTime 𝓕 (fun ω => ((ρ R ω : ℝ≥0) : WithTop ℝ≥0)) := fun R =>
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUad hUc (hClR R) T
  have hρT : ∀ R ω, ρ R ω ≤ T := fun R ω => hittingBtwn_le ω
  -- before `ρ R`, the path is in `K`, off `Cl`, and inside the ball
  have hbefore : ∀ R ω (q : ℝ≥0), q < ρ R ω → U q ω ∉ ClR R := fun R ω q hq =>
    notMem_of_lt_hittingBtwn hq zero_le
  have hK_of : ∀ R ω (s : ℝ≥0), s ≤ ρ R ω → U s ω ∈ K := fun R ω s hs =>
    hUK ω s (hs.trans (hρT R ω)) fun q hq h => hbefore R ω q (hq.trans_le hs) (Or.inl h)
  have hLR0 : ∀ R ω (q : ℝ≥0), q < ρ R ω → LR R (U q ω) ≤ 0 := by
    intro R ω q hq
    have hnot := hbefore R ω q hq
    have hball : U q ω ∈ closedBall (0 : E) (R : ℝ) := by
      rw [mem_closedBall_zero_iff]
      exact le_of_lt (not_le.mp fun h => hnot (Or.inr h))
    rw [hLReq R _ ⟨hK_of R ω q hq.le, hball⟩]
    exact hLF _ (hK_of R ω q hq.le) fun h => hnot (Or.inl h)
  have hint0 : ∀ R ω (s : ℝ≥0), s ≤ ρ R ω →
      ∫ r in (0 : ℝ)..(s : ℝ), LR R (U r.toNNReal ω) ≤ 0 := by
    intro R ω s hs
    rw [intervalIntegral.integral_of_le s.coe_nonneg, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_nonpos measurableSet_Ioo fun r hr => ?_
    have hlt : r.toNNReal < ρ R ω := by
      refine lt_of_lt_of_le ?_ hs
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1.le]
      exact hr.2
    exact hLR0 R ω _ hlt
  -- the stopped cutoff processes
  set G : ℕ → ℝ≥0 → Ω → ℝ := fun R t ω => FR R (U (min t (ρ R ω)) ω) with hG_def
  have hGb : ∀ R t ω, |G R t ω| ≤ M := by
    intro R t ω
    simp only [G, FR]
    rw [abs_mul]
    have hf := hfr R (U (min t (ρ R ω)) ω)
    have hfa : |f R (U (min t (ρ R ω)) ω)| ≤ 1 := by rw [abs_of_nonneg hf.1]; exact hf.2
    calc _ ≤ 1 * |F (U (min t (ρ R ω)) ω)| := by gcongr
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
    have hρτ : ρ R ω = τ ω := by
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
      simp only [ρ, τ, hittingBtwn, hset]
      by_cases h : ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl
      · rw [if_pos h, if_pos (hex.2 h)]
      · rw [if_neg h, if_neg (fun h' => h (hex.1 h'))]
    simp only [G, FR]
    rw [hρτ]
    have hmemK : U (min t (τ ω)) ω ∈ K := by
      have := hK_of R ω (min t (τ ω)) (by rw [hρτ]; exact min_le_right _ _)
      exact this
    have hball : U (min t (τ ω)) ω ∈ closedBall (0 : E) (R : ℝ) := by
      rw [mem_closedBall_zero_iff]
      have hτT : τ ω ≤ T := hittingBtwn_le ω
      exact (hRb _ ⟨zero_le, (min_le_right _ _).trans hτT⟩).trans hRlt.le
    rw [(hf1 R _ ⟨hmemK, hball⟩).self_of_nhds, Pi.one_apply, one_mul]
  have htend : ∀ t ω, Tendsto (fun R => G R t ω) atTop (𝓝 (F (U (min t (τ ω)) ω))) := by
    intro t ω
    obtain ⟨R0, hR0⟩ := hlarge ω
    exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨R0, fun R hR => (hR0 R hR t).symm⟩)
  -- measurability of the stopped cutoff values
  have hprog : IsStronglyProgressive 𝓕 U :=
    (hUad.stronglyAdapted).isStronglyProgressive_of_continuous hUc
  have hGsm : ∀ R t, StronglyMeasurable (G R t) := by
    intro R t
    have h := hprog.stronglyMeasurable_stoppedProcess (hρst R) t
    have heq : stoppedProcess U (fun ω => ((ρ R ω : ℝ≥0) : WithTop ℝ≥0)) t =
        fun ω => U (min t (ρ R ω)) ω := by
      funext ω
      simp only [stoppedProcess, ← WithTop.coe_min]
      rfl
    rw [heq] at h
    exact (hFRd R).continuous.comp_stronglyMeasurable h
  have hGi : ∀ R t, Integrable (G R t) P := fun R t =>
    ItoLite.integrable_of_bound_abs (hGsm R t) (hGb R t)
  -- the supermartingale inequality for each cutoff
  have hstep : ∀ R, ∫ ω, G R T ω ∂P ≤ ∫ ω, G R 0 ω ∂P := by
    intro R
    have hst := ItoLite.martingale_stopped_of_continuous (hNR R) (hNRc R) (hNRb R) (hρst R)
    have hE : ∫ ω, MR R (min (min T (ρ R ω)) T) ω ∂P = ∫ ω, MR R (min (min 0 (ρ R ω)) T) ω ∂P := by
      have := hst.setIntegral_eq (show (0 : ℝ≥0) ≤ T from zero_le) MeasurableSet.univ
      simpa only [setIntegral_univ] using this.symm
    have hpt : ∀ ω, G R T ω ≤ MR R (min (min T (ρ R ω)) T) ω + FR R u := by
      intro ω
      have h1 : min T (ρ R ω) = ρ R ω := min_eq_right (hρT R ω)
      have h2 : min (ρ R ω) T = ρ R ω := min_eq_left (hρT R ω)
      simp only [G, MR, h1, h2]
      linarith [hint0 R ω (ρ R ω) le_rfl]
    have h0 : ∀ ω, MR R (min (min 0 (ρ R ω)) T) ω + FR R u = G R 0 ω := by
      intro ω
      simp [G, MR]
    have hMi := hst.integrable T
    calc ∫ ω, G R T ω ∂P ≤ ∫ ω, (MR R (min (min T (ρ R ω)) T) ω + FR R u) ∂P :=
          integral_mono (hGi R T) (hMi.add (integrable_const _)) hpt
      _ = ∫ ω, (MR R (min (min 0 (ρ R ω)) T) ω + FR R u) ∂P := by
          rw [integral_add hMi (integrable_const _), hE,
            integral_add ((hst.integrable 0)) (integrable_const _)]
      _ = ∫ ω, G R 0 ω ∂P := integral_congr_ae (ae_of_all _ h0)
  have hDCT : ∀ t', Tendsto (fun R => ∫ ω, G R t' ω ∂P) atTop
      (𝓝 (∫ ω, F (U (min t' (τ ω)) ω) ∂P)) := by
    intro t'
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun R => (hGsm R t').aestronglyMeasurable)
      (integrable_const M) (fun R => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => htend t' ω)
    rw [Real.norm_eq_abs]; exact hGb R t' ω
  have hlim := le_of_tendsto_of_tendsto' (hDCT T) (hDCT 0) hstep
  have hU0 : (fun ω => F (U (min 0 (τ ω)) ω)) =ᵐ[P] fun _ => F u := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h0
    simp [hU ω 0, h0]
  rw [integral_congr_ae hU0] at hlim
  simpa using hlim

end RS
end QuantumZipper
