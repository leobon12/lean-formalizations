import InteractingSLE.Spec.Ito.Gm2Local

/-!
# The mixed Itô formula before a lifetime: the assembly

Packet PROVE-ITO-GEN2. **`isCLMBefore_residual_and_bracket`** (see `Gm2Local`'s module docstring):
the localizing times are `τₙ = σₙ^X ∧ σₙ^{X²−A} ∧ hₙ`, where `hₙ` is the first time the state leaves
the compact `Kₙ = {p : ‖p‖ ≤ n, dist(p, Oᶜ) ≥ 1/(n+1)}` or one of `|X|`, `|A|`, `‖Y‖` and the
total variation of `Y` exceeds `n`, read along the processes stopped at `σₙ^X ∧ σₙ^{X²−A}` (so that
only values before the lifetime enter).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gm2

section MeasHelp

variable {Ω' : Type*} {m' : MeasurableSpace Ω'} {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']

omit [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] in
lemma measurable_norm_comp {f : Ω' → E'} (hf : Measurable f) : Measurable fun ω => ‖f ω‖ :=
  hf.norm

omit [NormedSpace ℝ E'] in
lemma measurable_danger (O : Set (E' × ℝ)) {y : Ω' → E'} {x a v : Ω' → ℝ} (hy : Measurable y)
    (hx : Measurable x) (ha : Measurable a) (hv : Measurable v) (n : ℕ) :
    Measurable fun ω => max (max (max ‖y ω‖ |x ω|) (max |a ω| (v ω)) - n)
      (1 / ((n : ℝ) + 1) - distCompl O (y ω, x ω)) :=
  (((hy.norm.max hx.abs).max (ha.abs.max hv)).sub measurable_const).max
    (measurable_const.sub ((continuous_distCompl O).measurable.comp (hy.prodMk hx)))

end MeasHelp

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {m : ℕ}
  {F : E × ℝ → ℝ} {O : Set (E × ℝ)} {ζ : Ω → WithTop ℝ≥0} {X A : ℝ≥0 → Ω → ℝ}
  {Y : ℝ≥0 → Ω → E} {U : Fin m → Ω → StieltjesFunction ℝ≥0}
  {c : Fin m → ℝ≥0 → Ω → E} {a : Fin m → ℝ≥0 → Ω → ℝ}

/-- The compact `Kₙ` of states at distance at least `1/(n+1)` from the complement of `O` and of norm
at most `n`. -/
def compactIn (O : Set (E × ℝ)) (n : ℕ) : Set (E × ℝ) :=
  Metric.closedBall 0 n ∩ {p | 1 / ((n : ℝ) + 1) ≤ distCompl O p}

omit [MeasurableSpace E] [BorelSpace E] in
lemma isCompact_compactIn (O : Set (E × ℝ)) (n : ℕ) : IsCompact (compactIn O n) :=
  (isCompact_closedBall 0 (n : ℝ)).of_isClosed_subset
    (Metric.isClosed_closedBall.inter (isClosed_le continuous_const (continuous_distCompl O)))
    inter_subset_left

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compactIn_subset (O : Set (E × ℝ)) (n : ℕ) : compactIn O n ⊆ O := fun p hp =>
  mem_of_pos_distCompl (lt_of_lt_of_le (by positivity) hp.2)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- **Stopping strictly before the lifetime keeps adaptedness** (indicator form). -/
lemma measurable_stoppedProcess_indicator_before {G : Type*} [TopologicalSpace G]
    [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G] [Zero G]
    {Z : ℝ≥0 → Ω → G} (hZ : ∀ t, Measurable[𝓕 t] (Z t))
    (hZc : ∀ ω, ContinuousOn (Z · ω) {t | (t : WithTop ℝ≥0) < ζ ω}) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) (hτζ : ∀ ω, τ ω = 0 ∨ τ ω < ζ ω) (t : ℝ≥0) :
    Measurable[𝓕 t] (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator (Z t)) τ t) := by
  have h := measurable_stoppedProcess_of_rightContinuousBefore hZ hτ
    (fun ω hω s hs => continuousWithinAt_of_continuousOn_lt (hZc ω)
      (hs.trans_lt ((hτζ ω).resolve_left hω.ne'))) t
  have he : stoppedProcess (fun t => {ω | 0 < τ ω}.indicator (Z t)) τ t =
      {ω | 0 < τ ω}.indicator (stoppedProcess Z τ t) := by
    funext ω; simp only [stoppedProcess_indicator_comm]
  rw [he]; exact h.indicator (𝓕.mono bot_le _ (hτ.measurableSet_gt 0))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
lemma measurable_stopStieltjes_apply {k : Fin m} (hUa : ∀ t, Measurable[𝓕 t] fun ω => U k ω t)
    (hUc : ∀ ω, Continuous (U k ω)) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ)
    (hτζ : ∀ ω, τ ω = 0 ∨ τ ω < ζ ω) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => stopStieltjes (U k ω) (τ ω).untopA t := by
  have h := measurable_stoppedProcess_of_rightContinuousBefore (Z := fun t ω => U k ω t)
    hUa hτ (fun ω _ s _ => (hUc ω).continuousWithinAt) t
  have he : (fun ω => stopStieltjes (U k ω) (τ ω).untopA t) =
      stoppedProcess (fun t ω => U k ω t) τ t := by
    funext ω
    simp only [stopStieltjes_apply, stoppedProcess_of_eq_coe _ (eq_coe_untopA_of_pos hτζ ω)]
  rw [he]; exact h

/-- **The mixed Itô formula before a lifetime** (the form Theorem 2.6's proof applies; see the module
docstring of `Gm2Local`). -/
theorem isCLMBefore_residual_and_bracket [IsProbabilityMeasure P]
    (hO : IsOpen O) (hF : ContDiffOn ℝ 3 F O)
    (hX : IsCLMBefore 𝓕 P ζ X) (hXA : IsCLMBefore 𝓕 P ζ (fun t ω => X t ω ^ 2 - A t ω))
    (hXc : ∀ ω, ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hYc : ∀ ω, ContinuousOn (Y · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hcc : ∀ k ω, ContinuousOn (c k · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hac : ∀ k ω, ContinuousOn (a k · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (ha0 : ∀ k ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ζ ω → 0 ≤ a k u ω)
    (hUc : ∀ k ω, Continuous (U k ω))
    (hY : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω →
      Y t ω = Y 0 ω + ∑ k, ∫ u in Ioc 0 t, c k u ω ∂(U k ω).measure)
    (hA : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω →
      A t ω = ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure)
    (hO_path : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → (Y t ω, X t ω) ∈ O)
    (hYa : ∀ t, Measurable[𝓕 t] (Y t)) (hca : ∀ k t, Measurable[𝓕 t] (c k t))
    (haa : ∀ k t, Measurable[𝓕 t] (a k t)) (hUa : ∀ k t, Measurable[𝓕 t] fun ω => U k ω t) :
    IsCLMBefore 𝓕 P ζ (residual F Y X U c a) ∧
      IsCLMBefore 𝓕 P ζ (fun t ω => residual F Y X U c a t ω ^ 2 - bracket F Y X U a t ω) := by
  obtain ⟨-, σX, hσX, hσXζ, hσXev, hσXm⟩ := hX
  obtain ⟨-, σA, hσA, hσAζ, hσAev, hσAm⟩ := hXA
  -- continuity before the lifetime
  have hAz (ω : Ω) : ContinuousOn (A · ω) {t | (t : WithTop ℝ≥0) < ζ ω} := by
    have hsum : ContinuousOn (fun t => ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure)
        {t | (t : WithTop ℝ≥0) < ζ ω} :=
      continuousOn_finsetSum (f := fun k t => ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure) _
        fun k _ => continuousOn_integral_Ioc_zero (U k ω) (hUc k ω) (hac k ω)
    exact hsum.congr fun t ht => hA ω t ht
  have hXAz (ω : Ω) : ContinuousOn (fun t => X t ω ^ 2 - A t ω) {t | (t : WithTop ℝ≥0) < ζ ω} :=
    ((hXc ω).pow 2).sub (hAz ω)
  set TV : ℝ≥0 → Ω → ℝ := fun s ω => ∑ k, ∫ u in Ioc 0 s, ‖c k u ω‖ ∂(U k ω).measure with hTVdef
  have hTVz (ω : Ω) : ContinuousOn (TV · ω) {t | (t : WithTop ℝ≥0) < ζ ω} :=
    continuousOn_finsetSum (f := fun k t => ∫ u in Ioc 0 t, ‖c k u ω‖ ∂(U k ω).measure) _
      fun k _ => continuousOn_integral_Ioc_zero (U k ω) (hUc k ω) (hcc k ω).norm
  -- the common localizing times
  set ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (σX n ω) (σA n ω) with hρdef
  have hρ (n : ℕ) : IsStoppingTime 𝓕 (ρ n) := (hσX n).min (hσA n)
  have hρζ (n : ℕ) (ω : Ω) : ρ n ω = 0 ∨ ρ n ω < ζ ω := by
    rcases hσXζ n ω with h | h
    · left; simp only [hρdef, h]; exact min_eq_left bot_le
    · right; exact (min_le_left _ _).trans_lt h
  have hloc (n : ℕ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) (hτρ : ∀ ω, τ ω ≤ ρ n ω) :
      Martingale (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator (X t)) τ) 𝓕 P ∧
      Martingale (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator
        (fun ω => X t ω ^ 2 - A t ω)) τ) 𝓕 P :=
    ⟨martingale_stoppedProcess_indicator_of_le hτ (fun ω => (hτρ ω).trans (min_le_left _ _))
        (hσXm n) fun ω => continuous_stoppedProcess_indicator_of_continuousOn (hXc ω)
          (hσXζ n ω) _,
      martingale_stoppedProcess_indicator_of_le (X := fun t ω => X t ω ^ 2 - A t ω) hτ
        (fun ω => (hτρ ω).trans (min_le_right _ _)) (hσAm n) fun ω =>
          continuous_stoppedProcess_indicator_of_continuousOn (hXAz ω) (hσAζ n ω) _⟩
  -- the processes stopped at `ρ n`, and the danger process
  set r : ℕ → Ω → ℝ≥0 := fun n ω => (ρ n ω).untopA with hrdef
  set Xs : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess (fun t => {ω | 0 < ρ n ω}.indicator (X t))
    (ρ n) with hXsdef
  set As : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess (fun t => {ω | 0 < ρ n ω}.indicator (A t))
    (ρ n) with hAsdef
  set XAs : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess (fun t => {ω | 0 < ρ n ω}.indicator
    (fun ω => X t ω ^ 2 - A t ω)) (ρ n) with hXAsdef
  set Ys : ℕ → ℝ≥0 → Ω → E := fun n => stoppedProcess (fun t => {ω | 0 < ρ n ω}.indicator (Y t))
    (ρ n) with hYsdef
  set cs : ℕ → Fin m → ℝ≥0 → Ω → E := fun n k =>
    stoppedProcess (fun t => {ω | 0 < ρ n ω}.indicator (c k t)) (ρ n) with hcsdef
  set TVs : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω =>
    ∑ k, ∫ u in Ioc 0 t, ‖cs n k u ω‖ ∂(stopStieltjes (U k ω) (r n ω)).measure with hTVsdef
  set D : ℕ → ℝ≥0 → Ω → ℝ := fun n t ω =>
    max (max (max ‖Ys n t ω‖ |Xs n t ω|) (max |As n t ω| (TVs n t ω)) - n)
      (1 / ((n : ℝ) + 1) - distCompl O (Ys n t ω, Xs n t ω)) with hDdef
  have hXsc (n : ℕ) (ω : Ω) : Continuous (Xs n · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hXc ω) (hρζ n ω) _
  have hAsc (n : ℕ) (ω : Ω) : Continuous (As n · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hAz ω) (hρζ n ω) _
  have hYsc (n : ℕ) (ω : Ω) : Continuous (Ys n · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hYc ω) (hρζ n ω) _
  have hcsc (n : ℕ) (k : Fin m) (ω : Ω) : Continuous (cs n k · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hcc k ω) (hρζ n ω) _
  have hTVsc (n : ℕ) (ω : Ω) : Continuous (TVs n · ω) :=
    continuous_finsetSum _ fun k _ => continuous_integral_Ioc_zero _
      (continuous_stopStieltjes (hUc k ω) _) (hcsc n k ω).norm
  have hDc (n : ℕ) (ω : Ω) : Continuous (D n · ω) :=
    (((((hYsc n ω).norm.max (hXsc n ω).abs).max ((hAsc n ω).abs.max (hTVsc n ω))).sub
      continuous_const).max (continuous_const.sub
        ((continuous_distCompl O).comp ((hYsc n ω).prodMk (hXsc n ω)))))
  have hXsm (n : ℕ) (t : ℝ≥0) : Measurable[𝓕 t] (Xs n t) :=
    ((hloc n (hρ n) fun _ => le_rfl).1.stronglyAdapted t).measurable
  have hXAsm (n : ℕ) (t : ℝ≥0) : Measurable[𝓕 t] (XAs n t) :=
    ((hloc n (hρ n) fun _ => le_rfl).2.stronglyAdapted t).measurable
  have hAsm (n : ℕ) (t : ℝ≥0) : Measurable[𝓕 t] (As n t) := by
    have he : As n t = fun ω => Xs n t ω ^ 2 - XAs n t ω := by
      funext ω
      simp only [hAsdef, hXsdef, hXAsdef]
      rw [stoppedProcess_indicator_apply A (hρζ n) t ω, stoppedProcess_indicator_apply X (hρζ n) t ω,
        stoppedProcess_indicator_apply (fun t ω => X t ω ^ 2 - A t ω) (hρζ n) t ω]
      split_ifs <;> simp
    rw [he]; exact ((hXsm n t).pow_const 2).sub (hXAsm n t)
  have hYsm (n : ℕ) (t : ℝ≥0) : Measurable[𝓕 t] (Ys n t) :=
    measurable_stoppedProcess_indicator_before hYa hYc (hρ n) (hρζ n) t
  have hTVsm (n : ℕ) (t : ℝ≥0) : Measurable[𝓕 t] (TVs n t) :=
    Finset.measurable_sum _ fun k _ => measurable_stieltjesIntegral
      (g := fun u ω => ‖cs n k u ω‖) (fun ω => (hcsc n k ω).norm)
      (fun ω => stopStieltjes (U k ω) (r n ω))
      (fun u hu => measurable_norm_comp (m' := 𝓕 t)
        ((measurable_stoppedProcess_indicator_before (hca k) (hcc k) (hρ n) (hρζ n)
          u).mono (𝓕.mono hu) le_rfl))
      (fun u hu => (measurable_stopStieltjes_apply (hUa k) (hUc k) (hρ n) (hρζ n) u).mono
        (𝓕.mono hu) le_rfl)
  have hDm (n : ℕ) (t : ℝ≥0) : Measurable[𝓕 t] (D n t) :=
    measurable_danger (m' := 𝓕 t) O (hYsm n t) (hXsm n t) (hAsm n t) (hTVsm n t) n
  -- values of the stopped processes up to `ρ n`
  have hval (n : ℕ) (ω : Ω) (hω : 0 < ρ n ω) (s : ℝ≥0) (hs : (s : WithTop ℝ≥0) ≤ ρ n ω) :
      Xs n s ω = X s ω ∧ As n s ω = A s ω ∧ Ys n s ω = Y s ω ∧ TVs n s ω = TV s ω := by
    have hρr : ρ n ω = (r n ω : WithTop ℝ≥0) := eq_coe_untopA_of_pos (hρζ n) ω
    have hsr : min s (r n ω) = s := min_eq_left (WithTop.coe_le_coe.1 (hρr ▸ hs))
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [hXsdef]; rw [stoppedProcess_indicator_apply X (hρζ n) s ω, ite_eq_left hω, hsr]
    · simp only [hAsdef]; rw [stoppedProcess_indicator_apply A (hρζ n) s ω, ite_eq_left hω, hsr]
    · simp only [hYsdef]; rw [stoppedProcess_indicator_apply Y (hρζ n) s ω, ite_eq_left hω, hsr]
    · simp only [hTVsdef, hTVdef]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hcs (u : ℝ≥0) : ‖cs n k u ω‖ = ‖c k (min u (r n ω)) ω‖ := by
        simp only [hcsdef]; rw [stoppedProcess_indicator_apply (c k) (hρζ n) u ω, ite_eq_left hω]
      simp only [hcs]
      rw [integral_stopStieltjes_comp_min (U k ω) (r n ω) s (fun u => ‖c k u ω‖), hsr]
  have hDval (n : ℕ) (ω : Ω) (hω : 0 < ρ n ω) (s : ℝ≥0) (hs : (s : WithTop ℝ≥0) ≤ ρ n ω) :
      D n s ω = max (max (max ‖Y s ω‖ |X s ω|) (max |A s ω| (TV s ω)) - n)
        (1 / ((n : ℝ) + 1) - distCompl O (Y s ω, X s ω)) := by
    obtain ⟨h1, h2, h3, h4⟩ := hval n ω hω s hs
    simp only [hDdef, h1, h2, h3, h4]
  -- the first exits and the localizing times
  set h : ℕ → Ω → WithTop ℝ≥0 := fun n => firstNonneg (D n) with hhdef
  have hh (n : ℕ) : IsStoppingTime 𝓕 (h n) := isStoppingTime_firstNonneg (hDm n) (hDc n)
  set τ : ℕ → Ω → WithTop ℝ≥0 := fun n ω => min (ρ n ω) (h n ω) with hτdef
  have hτ (n : ℕ) : IsStoppingTime 𝓕 (τ n) := (hρ n).min (hh n)
  have hτρ (n : ℕ) (ω : Ω) : τ n ω ≤ ρ n ω := min_le_left _ _
  have hτζ (n : ℕ) (ω : Ω) : τ n ω = 0 ∨ τ n ω < ζ ω := by
    rcases hρζ n ω with h0 | hlt
    · left; exact le_antisymm ((hτρ n ω).trans h0.le) bot_le
    · right; exact (hτρ n ω).trans_lt hlt
  -- bounds up to `τ n`
  have hbd (n : ℕ) (ω : Ω) (hω : 0 < τ n ω) (s : ℝ≥0) (hs : (s : WithTop ℝ≥0) ≤ τ n ω) :
      (Y s ω, X s ω) ∈ compactIn O n ∧ |X s ω| ≤ n ∧ |A s ω| ≤ n ∧ ‖Y s ω‖ ≤ n ∧
        TV s ω ≤ n := by
    have hρpos : 0 < ρ n ω := hω.trans_le (hτρ n ω)
    have hhpos : 0 < h n ω := hω.trans_le (min_le_right _ _)
    have hD := le_zero_of_le_firstNonneg (hDc n) hhpos (hs.trans (min_le_right _ _))
    rw [hDval n ω hρpos s (hs.trans (hτρ n ω))] at hD
    obtain ⟨h1, h2⟩ := max_le_iff.1 hD
    have hbn : max (max ‖Y s ω‖ |X s ω|) (max |A s ω| (TV s ω)) ≤ n := by linarith
    simp only [max_le_iff] at hbn
    obtain ⟨⟨hy, hx⟩, ha, hv⟩ := hbn
    refine ⟨⟨?_, ?_⟩, hx, ha, hy, hv⟩
    · rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
      exact ⟨hy, hx⟩
    · show 1 / ((n : ℝ) + 1) ≤ distCompl O (Y s ω, X s ω)
      linarith
  -- the localizing times exhaust the lifetime
  have hev : ∀ᵐ ω ∂P, ∀ r0 : ℝ≥0, (r0 : WithTop ℝ≥0) < ζ ω →
      ∀ᶠ n in atTop, (r0 : WithTop ℝ≥0) < τ n ω := by
    filter_upwards [hσXev, hσAev] with ω hωX hωA
    intro r0 hr0
    have hIcc : Icc (0 : ℝ≥0) r0 ⊆ {t | (t : WithTop ℝ≥0) < ζ ω} := fun s hs =>
      lt_of_le_of_lt (WithTop.coe_le_coe.2 hs.2) hr0
    have hbc : ContinuousOn (fun s => max (max ‖Y s ω‖ |X s ω|) (max |A s ω| (TV s ω)))
        (Icc 0 r0) :=
      have hΦ : Continuous fun q : E × ℝ × ℝ × ℝ =>
          max (max ‖q.1‖ |q.2.1|) (max |q.2.2.1| q.2.2.2) :=
        (continuous_fst.norm.max continuous_snd.fst.abs).max
          (continuous_snd.snd.fst.abs.max continuous_snd.snd.snd)
      (hΦ.comp_continuousOn ((hYc ω).prodMk ((hXc ω).prodMk ((hAz ω).prodMk (hTVz ω))))).mono hIcc
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hbc
    have hdc : ContinuousOn (fun s => distCompl O (Y s ω, X s ω)) (Icc 0 r0) :=
      ((continuous_distCompl O).comp_continuousOn ((hYc ω).prodMk (hXc ω))).mono hIcc
    obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 bot_le) hdc
    have hδ : 0 < distCompl O (Y s0 ω, X s0 ω) := pos_distCompl hO (hO_path ω s0 (hIcc hs0))
    have hn1 : ∀ᶠ n : ℕ in atTop, B < n := tendsto_natCast_atTop_atTop.eventually_gt_atTop B
    have hn2 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < distCompl O (Y s0 ω, X s0 ω) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)
    filter_upwards [hωX r0 hr0, hωA r0 hr0, hn1, hn2] with n h1 h2 h3 h4
    have hρn : (r0 : WithTop ℝ≥0) < ρ n ω := lt_min h1 h2
    have hρpos : 0 < ρ n ω := lt_of_le_of_lt bot_le hρn
    refine lt_min hρn (lt_firstNonneg (hDc n) fun s hs => ?_)
    rw [hDval n ω hρpos s (le_trans (WithTop.coe_le_coe.2 hs) hρn.le)]
    have hsI : s ∈ Icc 0 r0 := ⟨bot_le, hs⟩
    have hb := hB s hsI
    rw [Real.norm_eq_abs] at hb
    have hdist := isMinOn_iff.1 hmin s hsI
    have hle := le_abs_self (max (max ‖Y s ω‖ |X s ω|) (max |A s ω| (TV s ω)))
    exact max_lt (by linarith) (by linarith)
  -- the martingales at each localizing time, and continuity before the lifetime
  have hmain (n : ℕ) := martingale_stopped_residual_of_bounds (P := P) hO hF
    (isCompact_compactIn O n) (compactIn_subset O n) (Nat.cast_nonneg n) hXc hYc hcc hac ha0 hUc
    hY hA hYa hca haa hUa (hτ n) (hτζ n) (hloc n (hτ n) (hτρ n)).1 (hloc n (hτ n) (hτρ n)).2
    (hbd n)
  have hcont (ω : Ω) := continuousOn_residual_bracket hO hF (hXc ω) (hYc ω) (fun k => hcc k ω)
    (fun k => hac k ω) (fun k => hUc k ω) (hO_path ω)
  exact ⟨⟨.of_forall fun ω => (hcont ω).1, τ, hτ, hτζ, hev, fun n => (hmain n).1⟩,
    ⟨.of_forall fun ω => ((hcont ω).1.pow 2).sub (hcont ω).2, τ, hτ, hτζ, hev,
      fun n => (hmain n).2⟩⟩

end Main

end InteractingSLE.Ito.Gm2
