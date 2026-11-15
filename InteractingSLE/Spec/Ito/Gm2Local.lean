import InteractingSLE.Spec.Ito.Gm2Stop
import MathFin.Probability.Brownian.ExitTime

/-!
# The mixed Itô formula before a lifetime: localization

Packet PROVE-ITO-GEN2. This is the form in which Theorem 2.6's proof applies Itô's formula
(`source/spec/p001-048.md` L977–L986, the semimartingale argument of Theorem 2.4 at one point:
`W_t = Re g_t(z) − Im g_t(z) cot(arg f_t(z))`, "localization inside `(0, π)` and Itô's formula"):

**`isCLMBefore_residual_and_bracket`** (assembled in `Gm2Lifetime`). Let `X` be a continuous local martingale before a random time
`ζ` with bracket `A` (`X² − A` a continuous local martingale before `ζ`), in the sense of the
statement candidate's `IsContLocalMartingaleBefore` (local copy `IsCLMBefore`). Let `A` and the
finite-variation coordinate `Y` be Stieltjes integrals `A = Σₖ ∫ aₖ dUₖ`, `Y = Y_0 + Σₖ ∫ cₖ dUₖ`
before `ζ` against continuous random integrators `Uₖ` (time, the monotone force-point images, …),
with densities continuous before `ζ`. Let `F` be `C³` on an open set `O` containing `(Y_t, X_t)` for
`t < ζ`. Then the mixed residual
`N_t = F(Y_t, X_t) − F(Y_0, X_0) − Σₖ ∫_{(0,t]} (∂_y F cₖ + ½ ∂²_x F aₖ) dUₖ`
and `N² − Σₖ ∫ (∂_x F)² aₖ dUₖ` are continuous local martingales before `ζ`.

No density with respect to Lebesgue measure, no absolute continuity of the force-point motions, no
Brownian motion and no stochastic integral are used: the proof localizes (exit times from compacts of
`O`, bounds on `X`, `A`, the total variation) to the bounded core
(`martingale_residual`, `martingale_residual_sq_sub_bracket`). This file contains the local predicate,
the exit-time and distance tools, the reduction at one localizing time
(`martingale_stopped_residual_of_bounds`) and the continuity of the residual before the lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gm2

/-- **A continuous local martingale before `ζ`**: verbatim the body of the statement candidate's
`IsContLocalMartingaleBefore` (`…/isle/candidates/T2426-v2.lean`), kept under a distinct name until
that definition is frozen (the bridge is `Iff.rfl`). Almost surely the path is continuous on `[0, ζ)`,
and there are stopping times `σₙ`, each `0` or strictly below `ζ`, eventually above every time before
`ζ` almost surely, with every `1_{σₙ > 0} X_{t ∧ σₙ}` a martingale. -/
def IsCLMBefore {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (ζ : Ω → WithTop ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) {t | (t : WithTop ℝ≥0) < ζ ω}) ∧
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓕 (σ n)) ∧ (∀ n ω, σ n ω = 0 ∨ σ n ω < ζ ω) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < ζ ω → ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) ∧
      ∀ n, Martingale (stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (X t)) (σ n)) 𝓕 P

/-! ### Times before a lifetime -/

lemma exists_between_of_lt_withTop {t₀ : ℝ≥0} {z : WithTop ℝ≥0} (h : (t₀ : WithTop ℝ≥0) < z) :
    ∃ T : ℝ≥0, t₀ < T ∧ (T : WithTop ℝ≥0) < z := by
  rcases eq_or_ne z ⊤ with rfl | hz
  · exact ⟨t₀ + 1, lt_add_one t₀, WithTop.coe_lt_top _⟩
  · obtain ⟨z', rfl⟩ := WithTop.ne_top_iff_exists.1 hz |>.imp fun _ h => h.symm
    have h' : t₀ < z' := WithTop.coe_lt_coe.1 h
    obtain ⟨T, h1, h2⟩ := exists_between h'
    exact ⟨T, h1, WithTop.coe_lt_coe.2 h2⟩

/-- **A Stieltjes primitive is continuous before a lifetime** if the integrand is. -/
theorem continuousOn_integral_Ioc_zero (U : StieltjesFunction ℝ≥0) (hU : Continuous U)
    {g : ℝ≥0 → ℝ} {z : WithTop ℝ≥0} (hg : ContinuousOn g {t | (t : WithTop ℝ≥0) < z}) :
    ContinuousOn (fun t => ∫ u in Ioc 0 t, g u ∂U.measure) {t | (t : WithTop ℝ≥0) < z} := by
  intro t₀ ht₀
  obtain ⟨T, hT, hTz⟩ := exists_between_of_lt_withTop ht₀
  have hgT : Continuous fun u => g (min u T) :=
    hg.comp_continuous (continuous_id.min continuous_const) fun u =>
      lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right u T)) hTz
  have heq : ∀ t ∈ Iic T, (∫ u in Ioc 0 t, g u ∂U.measure) = ∫ u in Ioc 0 t, g (min u T) ∂U.measure :=
    fun t ht => setIntegral_congr_fun measurableSet_Ioc fun u hu => by
      rw [min_eq_left (hu.2.trans ht)]
  refine ContinuousAt.continuousWithinAt ?_
  exact ((continuous_integral_Ioc_zero U hU hgT).continuousAt).congr
    (Filter.mem_of_superset (Iic_mem_nhds hT) fun t ht => (heq t ht).symm)

/-! ### Distance to the boundary of the domain -/

section Dist

variable {G : Type*} [MetricSpace G]

/-- A continuous function positive exactly on the open set `O`: the distance to its complement (or
`1` when `O` is everything). -/
def distCompl (O : Set G) (p : G) : ℝ := if Oᶜ = ∅ then 1 else Metric.infDist p Oᶜ

lemma continuous_distCompl (O : Set G) : Continuous (distCompl O) := by
  unfold distCompl
  split_ifs
  · exact continuous_const
  · exact Metric.continuous_infDist_pt _

lemma pos_distCompl {O : Set G} (hO : IsOpen O) {p : G} (hp : p ∈ O) : 0 < distCompl O p := by
  unfold distCompl
  split_ifs with h
  · exact one_pos
  · exact (hO.isClosed_compl.notMem_iff_infDist_pos (Set.nonempty_iff_ne_empty.2 h)).1
      (fun h' => h' hp)

lemma mem_of_pos_distCompl {O : Set G} {p : G} (hp : 0 < distCompl O p) : p ∈ O := by
  unfold distCompl at hp
  split_ifs at hp with h
  · rw [Set.compl_empty_iff] at h; rw [h]; trivial
  · by_contra hpO
    have := Metric.infDist_zero_of_mem (show p ∈ Oᶜ from hpO)
    linarith

end Dist

/-! ### First passage of a continuous adapted real process above `0` -/

section Passage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The first time a real process reaches `[0, ∞)` (MathFin's exit time of `max (B + 1) 0` at
level `1`). -/
def firstNonneg (B : ℝ≥0 → Ω → ℝ) : Ω → WithTop ℝ≥0 :=
  MathFin.exitTime (fun t ω => max (B t ω + 1) 0) 1

lemma abs_max_add_one_ge_one_iff (x : ℝ) : ((1 : ℕ) : ℝ) ≤ |max (x + 1) 0| ↔ 0 ≤ x := by
  rw [abs_of_nonneg (le_max_right _ _), Nat.cast_one]
  constructor
  · intro h
    rcases le_total (x + 1) 0 with h' | h'
    · rw [max_eq_right h'] at h; linarith
    · rw [max_eq_left h'] at h; linarith
  · intro h; exact le_max_of_le_left (by linarith)

theorem isStoppingTime_firstNonneg {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) : IsStoppingTime 𝓕 (firstNonneg B) :=
  MathFin.isStoppingTime_exitTime_of_measurable
    (fun t => ((hBm t).add_const 1).max measurable_const)
    (fun ω => ((hBc ω).add continuous_const).max continuous_const) 1

/-- Up to a positive first passage, the process is nonpositive. -/
theorem le_zero_of_le_firstNonneg {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) {ω : Ω}
    (hpos : 0 < firstNonneg B ω) {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) ≤ firstNonneg B ω) :
    B s ω ≤ 0 := by
  have h := MathFin.abs_le_of_le_exitTime (B := fun t ω => max (B t ω + 1) 0)
    (fun ω => ((hBc ω).add continuous_const).max continuous_const) (N := 1) hpos hs
  rw [abs_of_nonneg (le_max_right _ _), Nat.cast_one] at h
  linarith [le_max_left (B s ω + 1) 0]

/-- If the process is negative on `[0, r]`, the first passage comes after `r`. -/
theorem lt_firstNonneg {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) {ω : Ω} {r : ℝ≥0}
    (hneg : ∀ s ≤ r, B s ω < 0) : (r : WithTop ℝ≥0) < firstNonneg B ω := by
  by_contra h
  rw [not_lt] at h
  obtain ⟨s, hs, hge⟩ := (MathFin.exitTime_le_iff (B := fun t ω => max (B t ω + 1) 0)
    (fun ω => ((hBc ω).add continuous_const).max continuous_const) 1 r ω).1 h
  rw [abs_max_add_one_ge_one_iff] at hge
  exact (hneg s hs.2).not_ge hge

end Passage

/-! ### One localizing time -/

lemma partialSnd_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F G : E × ℝ → ℝ}
    {p : E × ℝ} (h : F =ᶠ[𝓝 p] G) : partialSnd F p = partialSnd G p := by
  unfold partialSnd; rw [h.fderiv_eq]

section OneStop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {m : ℕ}
  {F : E × ℝ → ℝ} {O : Set (E × ℝ)} {ζ : Ω → WithTop ℝ≥0} {X A : ℝ≥0 → Ω → ℝ}
  {Y : ℝ≥0 → Ω → E} {U : Fin m → Ω → StieltjesFunction ℝ≥0}
  {c : Fin m → ℝ≥0 → Ω → E} {a : Fin m → ℝ≥0 → Ω → ℝ}

lemma isOpen_lt_withTop (z : WithTop ℝ≥0) : IsOpen {t : ℝ≥0 | (t : WithTop ℝ≥0) < z} :=
  isOpen_Iio.preimage WithTop.continuous_coe

/-- On `{τ > 0}` with `τ = 0 ∨ τ < ζ`, `τ` is the finite time `τ.untopA`. -/
lemma eq_coe_untopA_of_pos {τ : Ω → WithTop ℝ≥0} (hτζ : ∀ ω, τ ω = 0 ∨ τ ω < ζ ω) (ω : Ω) :
    τ ω = ((τ ω).untopA : WithTop ℝ≥0) := by
  have hne : τ ω ≠ ⊤ := by
    rcases hτζ ω with h | h
    · rw [h]; exact WithTop.zero_ne_top
    · exact ne_top_of_lt h
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]

/-- The value of an indicator-stopped process at a time `0` or strictly before the lifetime. -/
lemma stoppedProcess_indicator_apply {G : Type*} [Zero G] (Z : ℝ≥0 → Ω → G)
    {τ : Ω → WithTop ℝ≥0} (hτζ : ∀ ω, τ ω = 0 ∨ τ ω < ζ ω) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (fun t => {ω | 0 < τ ω}.indicator (Z t)) τ t ω =
      if 0 < τ ω then Z (min t (τ ω).untopA) ω else 0 := by
  rw [stoppedProcess_indicator_comm]
  by_cases h : 0 < τ ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | 0 < τ ω} from h), ite_eq_left h,
      stoppedProcess_of_eq_coe Z (eq_coe_untopA_of_pos hτζ ω)]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < τ ω} from h), ite_eq_right h]

lemma continuousWithinAt_of_continuousOn_lt {G : Type*} [TopologicalSpace G]
    {Z : ℝ≥0 → G} {z : WithTop ℝ≥0} (hZ : ContinuousOn Z {t | (t : WithTop ℝ≥0) < z})
    {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) < z) : ContinuousWithinAt Z (Ici s) s :=
  (hZ.continuousAt ((isOpen_lt_withTop z).mem_nhds hs)).continuousWithinAt

/-- **The mixed formula at one localizing time.** If `τ` (`0` or strictly before `ζ`) localizes `X`
and `X² − A`, and up to `τ` the state stays in a compact `K ⊆ O` with `X`, `A`, `Y` and the total
variation bounded by `n`, then the residual and its squared-minus-bracket process, stopped at `τ`
(and zeroed on `{τ = 0}`), are martingales. -/
theorem martingale_stopped_residual_of_bounds [IsProbabilityMeasure P]
    (hO : IsOpen O) (hF : ContDiffOn ℝ 3 F O) {K : Set (E × ℝ)} (hK : IsCompact K) (hKO : K ⊆ O)
    {n : ℝ} (hn : 0 ≤ n)
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
    (hYa : ∀ t, Measurable[𝓕 t] (Y t)) (hca : ∀ k t, Measurable[𝓕 t] (c k t))
    (haa : ∀ k t, Measurable[𝓕 t] (a k t)) (hUa : ∀ k t, Measurable[𝓕 t] fun ω => U k ω t)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) (hτζ : ∀ ω, τ ω = 0 ∨ τ ω < ζ ω)
    (hMτ : Martingale (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator (X t)) τ) 𝓕 P)
    (hM2τ : Martingale (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator
      (fun ω => X t ω ^ 2 - A t ω)) τ) 𝓕 P)
    (hbd : ∀ ω, 0 < τ ω → ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ τ ω →
      (Y s ω, X s ω) ∈ K ∧ |X s ω| ≤ n ∧ |A s ω| ≤ n ∧ ‖Y s ω‖ ≤ n ∧
        ∑ k, ∫ u in Ioc 0 s, ‖c k u ω‖ ∂(U k ω).measure ≤ n) :
    Martingale (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator
        (residual F Y X U c a t)) τ) 𝓕 P ∧
      Martingale (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator
        (fun ω => residual F Y X U c a t ω ^ 2 - bracket F Y X U a t ω)) τ) 𝓕 P := by
  set Sτ := {ω | 0 < τ ω} with hSτ
  have hSm (t : ℝ≥0) : MeasurableSet[𝓕 t] Sτ := 𝓕.mono bot_le _ (hτ.measurableSet_gt 0)
  set r : Ω → ℝ≥0 := fun ω => (τ ω).untopA with hrdef
  have hτr (ω : Ω) : τ ω = (r ω : WithTop ℝ≥0) := eq_coe_untopA_of_pos hτζ ω
  have hrζ (ω : Ω) (hω : 0 < τ ω) (u : ℝ≥0) : ((min u (r ω) : ℝ≥0) : WithTop ℝ≥0) < ζ ω := by
    have h := (hτζ ω).resolve_left hω.ne'
    rw [hτr ω] at h
    exact lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right _ _)) h
  have hrle (ω : Ω) (u : ℝ≥0) : ((min u (r ω) : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := by
    rw [hτr ω]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
  have hr0 (ω : Ω) (hω : ¬ 0 < τ ω) : r ω = 0 := by
    have : τ ω = 0 := le_antisymm (not_lt.1 hω) bot_le
    simp only [hrdef, this]
    rw [WithTop.untopA_eq_untop WithTop.zero_ne_top, WithTop.untop_zero]
  have hvR (Z : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
      stoppedProcess (fun t => Sτ.indicator (Z t)) τ t ω =
        if 0 < τ ω then Z (min t (r ω)) ω else 0 := stoppedProcess_indicator_apply Z hτζ t ω
  have hvE (Z : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) :
      stoppedProcess (fun t => Sτ.indicator (Z t)) τ t ω =
        if 0 < τ ω then Z (min t (r ω)) ω else 0 := stoppedProcess_indicator_apply Z hτζ t ω
  -- the stopped data
  set M' : ℝ≥0 → Ω → ℝ := stoppedProcess (fun t => Sτ.indicator (X t)) τ with hM'
  set A' : ℝ≥0 → Ω → ℝ := stoppedProcess (fun t => Sτ.indicator (A t)) τ with hA'
  set Y' : ℝ≥0 → Ω → E := stoppedProcess (fun t => Sτ.indicator (Y t)) τ with hY'
  set c' : Fin m → ℝ≥0 → Ω → E := fun k => stoppedProcess (fun t => Sτ.indicator (c k t)) τ
    with hc'
  set a' : Fin m → ℝ≥0 → Ω → ℝ := fun k => stoppedProcess (fun t => Sτ.indicator (a k t)) τ
    with ha'
  set U' : Fin m → Ω → StieltjesFunction ℝ≥0 := fun k ω => stopStieltjes (U k ω) (r ω) with hU'
  have hM'v (t : ℝ≥0) (ω : Ω) : M' t ω = if 0 < τ ω then X (min t (r ω)) ω else 0 := hvR X t ω
  have hA'v (t : ℝ≥0) (ω : Ω) : A' t ω = if 0 < τ ω then A (min t (r ω)) ω else 0 := hvR A t ω
  have hY'v (t : ℝ≥0) (ω : Ω) : Y' t ω = if 0 < τ ω then Y (min t (r ω)) ω else 0 := hvE Y t ω
  have hc'v (k : Fin m) (t : ℝ≥0) (ω : Ω) :
      c' k t ω = if 0 < τ ω then c k (min t (r ω)) ω else 0 := hvE (c k) t ω
  have ha'v (k : Fin m) (t : ℝ≥0) (ω : Ω) :
      a' k t ω = if 0 < τ ω then a k (min t (r ω)) ω else 0 := hvR (a k) t ω
  -- continuity
  have hAz (ω : Ω) : ContinuousOn (A · ω) {t | (t : WithTop ℝ≥0) < ζ ω} := by
    have hsum : ContinuousOn (fun t => ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure)
        {t | (t : WithTop ℝ≥0) < ζ ω} :=
      continuousOn_finsetSum (f := fun k t => ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure) _
        fun k _ => continuousOn_integral_Ioc_zero (U k ω) (hUc k ω) (hac k ω)
    exact hsum.congr fun t ht => hA ω t ht
  have hMc' (ω : Ω) : Continuous (M' · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hXc ω) (hτζ ω) Sτ
  have hAc' (ω : Ω) : Continuous (A' · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hAz ω) (hτζ ω) Sτ
  have hYc' (ω : Ω) : Continuous (Y' · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hYc ω) (hτζ ω) Sτ
  have hcc' (k : Fin m) (ω : Ω) : Continuous (c' k · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hcc k ω) (hτζ ω) Sτ
  have hac' (k : Fin m) (ω : Ω) : Continuous (a' k · ω) :=
    continuous_stoppedProcess_indicator_of_continuousOn (hac k ω) (hτζ ω) Sτ
  have hUc' (k : Fin m) (ω : Ω) : Continuous (U' k ω) := continuous_stopStieltjes (hUc k ω) (r ω)
  have ha0' (k : Fin m) (u : ℝ≥0) (ω : Ω) : 0 ≤ a' k u ω := by
    rw [ha'v]; split_ifs with h
    · exact ha0 k ω _ (hrζ ω h u)
    · exact le_rfl
  -- the representations
  have hint0R (k : Fin m) (t : ℝ≥0) (ω : Ω) (h : ¬ 0 < τ ω) (g : ℝ≥0 → ℝ) :
      ∫ u in Ioc 0 t, g u ∂(U' k ω).measure = 0 := by
    simp only [hU', integral_stopStieltjes, hr0 ω h, min_eq_right (show (0 : ℝ≥0) ≤ t from bot_le),
      Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
  have hint0E (k : Fin m) (t : ℝ≥0) (ω : Ω) (h : ¬ 0 < τ ω) (g : ℝ≥0 → E) :
      ∫ u in Ioc 0 t, g u ∂(U' k ω).measure = 0 := by
    simp only [hU', integral_stopStieltjes, hr0 ω h, min_eq_right (show (0 : ℝ≥0) ≤ t from bot_le),
      Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]
  have hY'rep (t : ℝ≥0) (ω : Ω) :
      Y' t ω = Y' 0 ω + ∑ k, ∫ u in Ioc 0 t, c' k u ω ∂(U' k ω).measure := by
    by_cases h : 0 < τ ω
    · simp only [hY'v, hc'v, h, ite_true]
      have hk (k : Fin m) : ∫ u in Ioc 0 t, c k (min u (r ω)) ω ∂(U' k ω).measure =
          ∫ u in Ioc 0 (min t (r ω)), c k u ω ∂(U k ω).measure :=
        integral_stopStieltjes_comp_min (U k ω) (r ω) t (fun u => c k u ω)
      simp only [hk, min_eq_left (show (0 : ℝ≥0) ≤ r ω from bot_le)]
      exact hY ω _ (hrζ ω h t)
    · simp only [hY'v, h, ite_false, zero_add]
      exact (Finset.sum_eq_zero fun k _ => hint0E k t ω h _).symm
  have hA'rep (t : ℝ≥0) (ω : Ω) :
      A' t ω = A' 0 ω + ∑ k, ∫ u in Ioc 0 t, a' k u ω ∂(U' k ω).measure := by
    by_cases h : 0 < τ ω
    · simp only [hA'v, ha'v, h, ite_true]
      have hk (k : Fin m) : ∫ u in Ioc 0 t, a k (min u (r ω)) ω ∂(U' k ω).measure =
          ∫ u in Ioc 0 (min t (r ω)), a k u ω ∂(U k ω).measure :=
        integral_stopStieltjes_comp_min (U k ω) (r ω) t (fun u => a k u ω)
      have h00 : ((0 : ℝ≥0) : WithTop ℝ≥0) < ζ ω := by
        have h1 := hrζ ω h 0
        rwa [min_eq_left (show (0 : ℝ≥0) ≤ r ω from bot_le)] at h1
      have h0 : A 0 ω = 0 := by
        rw [hA ω 0 h00]
        simp only [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure,
          Finset.sum_const_zero]
      simp only [hk, min_eq_left (show (0 : ℝ≥0) ≤ r ω from bot_le), h0, zero_add]
      exact hA ω _ (hrζ ω h t)
    · simp only [hA'v, h, ite_false, zero_add]
      exact (Finset.sum_eq_zero fun k _ => hint0R k t ω h _).symm
  -- bounds
  have hK' (t : ℝ≥0) (ω : Ω) : |M' t ω| ≤ n := by
    rw [hM'v]; split_ifs with h
    · exact (hbd ω h _ (hrle ω t)).2.1
    · simpa using hn
  have hL' (t : ℝ≥0) (ω : Ω) : |A' t ω| ≤ n := by
    rw [hA'v]; split_ifs with h
    · exact (hbd ω h _ (hrle ω t)).2.2.1
    · simpa using hn
  have hR' (t : ℝ≥0) (ω : Ω) : ‖Y' t ω‖ ≤ n := by
    rw [hY'v]; split_ifs with h
    · exact (hbd ω h _ (hrle ω t)).2.2.2.1
    · simpa using hn
  have hV' (t : ℝ≥0) (ω : Ω) : ∑ k, ∫ u in Ioc 0 t, ‖c' k u ω‖ ∂(U' k ω).measure ≤ n := by
    by_cases h : 0 < τ ω
    · simp only [hc'v, h, ite_true]
      have hk (k : Fin m) : ∫ u in Ioc 0 t, ‖c k (min u (r ω)) ω‖ ∂(U' k ω).measure =
          ∫ u in Ioc 0 (min t (r ω)), ‖c k u ω‖ ∂(U k ω).measure :=
        integral_stopStieltjes_comp_min (U k ω) (r ω) t (fun u => ‖c k u ω‖)
      simp only [hk]
      exact (hbd ω h _ (hrle ω t)).2.2.2.2
    · rw [Finset.sum_eq_zero fun k _ => hint0R k t ω h _]; exact hn
  -- adaptedness
  have hlt (ω : Ω) (hω : 0 < τ ω) (s : ℝ≥0) (hs : (s : WithTop ℝ≥0) ≤ τ ω) :
      (s : WithTop ℝ≥0) < ζ ω := hs.trans_lt ((hτζ ω).resolve_left hω.ne')
  have hYa' (t : ℝ≥0) : Measurable[𝓕 t] (Y' t) := by
    have h := measurable_stoppedProcess_of_rightContinuousBefore hYa hτ
      (fun ω hω s hs => continuousWithinAt_of_continuousOn_lt (hYc ω) (hlt ω hω s hs)) t
    have he : Y' t = Sτ.indicator (stoppedProcess Y τ t) := by
      funext ω; simp only [hY', stoppedProcess_indicator_comm]
    rw [he]; exact h.indicator (hSm t)
  have hca' (k : Fin m) (t : ℝ≥0) : Measurable[𝓕 t] (c' k t) := by
    have h := measurable_stoppedProcess_of_rightContinuousBefore (hca k) hτ
      (fun ω hω s hs => continuousWithinAt_of_continuousOn_lt (hcc k ω) (hlt ω hω s hs)) t
    have he : c' k t = Sτ.indicator (stoppedProcess (c k) τ t) := by
      funext ω; simp only [hc', stoppedProcess_indicator_comm]
    rw [he]; exact h.indicator (hSm t)
  have haa' (k : Fin m) (t : ℝ≥0) : Measurable[𝓕 t] (a' k t) := by
    have h := measurable_stoppedProcess_of_rightContinuousBefore (haa k) hτ
      (fun ω hω s hs => continuousWithinAt_of_continuousOn_lt (hac k ω) (hlt ω hω s hs)) t
    have he : a' k t = Sτ.indicator (stoppedProcess (a k) τ t) := by
      funext ω; simp only [ha', stoppedProcess_indicator_comm]
    rw [he]; exact h.indicator (hSm t)
  have hUa' (k : Fin m) (t : ℝ≥0) : Measurable[𝓕 t] fun ω => U' k ω t := by
    have h := measurable_stoppedProcess_of_rightContinuousBefore (Z := fun t ω => U k ω t)
      (hUa k) hτ (fun ω _ s _ => (hUc k ω).continuousWithinAt) t
    have he : (fun ω => U' k ω t) = stoppedProcess (fun t ω => U k ω t) τ t := by
      funext ω; simp only [hU', stopStieltjes_apply, stoppedProcess_of_eq_coe _ (hτr ω)]
    rw [he]; exact h
  -- the martingale inputs
  have hM2' : Martingale (fun t ω => M' t ω ^ 2 - A' t ω) 𝓕 P := by
    convert hM2τ using 1
    funext t ω
    rw [hM'v, hA'v, stoppedProcess_indicator_apply (fun t ω => X t ω ^ 2 - A t ω) hτζ t ω]
    split_ifs <;> first | rfl | simp
  -- the cut-off and the bounded core
  obtain ⟨χ, hχ, hχc, hχO, hχ1⟩ := exists_cutoff hK hO hKO
  set Fc : E × ℝ → ℝ := fun p => χ p * F p with hFc
  have hFc3 : ContDiff ℝ 3 Fc := contDiff_mul_of_tsupport_subset hO hF hχ hχO
  have hFcc : HasCompactSupport Fc := hχc.mul_right
  have hFceq (p : E × ℝ) (hp : p ∈ K) : Fc =ᶠ[𝓝 p] F := by
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hp)] with q hq
    simp [hFc, hq]
  have hcore1 := martingale_residual (P := P) (𝓕 := 𝓕) (F := Fc) (Y := Y') (M := M') (A := A')
    (U := U') (c := c') (a := a') hFc3 hFcc hMτ hM2' hK' hL' hR' hV' hMc' hAc' hYc' hcc' hac'
    ha0' hY'rep hA'rep hYa' hca' haa' hUa'
  have hcore2 := martingale_residual_sq_sub_bracket (P := P) (𝓕 := 𝓕) (F := Fc) (Y := Y')
    (M := M') (A := A') (U := U') (c := c') (a := a') hFc3 hFcc hMτ hM2' hK' hL' hR' hV' hMc' hAc'
    hYc' hcc' hac' ha0' hUc' hY'rep hA'rep hYa' hca' haa' hUa'
  -- identification of the core processes with the stopped residual and bracket
  have hd (ω : Ω) (h : 0 < τ ω) (k : Fin m) (u : ℝ≥0) :
      driftDensity Fc Y' M' c' a' k u ω = driftDensity F Y X c a k (min u (r ω)) ω := by
    have h1 : driftDensity Fc Y' M' c' a' k u ω = driftDensity Fc Y X c a k (min u (r ω)) ω := by
      simp only [driftDensity, hY'v, hM'v, hc'v, ha'v, h, ite_true]
    rw [h1]
    exact driftDensity_congr (hFceq _ (hbd ω h _ (hrle ω u)).1)
  have hq (ω : Ω) (h : 0 < τ ω) (k : Fin m) (u : ℝ≥0) :
      partialSnd Fc (Y' u ω, M' u ω) ^ 2 * a' k u ω =
        partialSnd F (Y (min u (r ω)) ω, X (min u (r ω)) ω) ^ 2 * a k (min u (r ω)) ω := by
    simp only [hY'v, hM'v, ha'v, h, ite_true]
    rw [partialSnd_congr (hFceq _ (hbd ω h _ (hrle ω u)).1)]
  have hI1 : residual Fc Y' M' U' c' a' =
      stoppedProcess (fun t => Sτ.indicator (residual F Y X U c a t)) τ := by
    funext t ω
    rw [hvR (residual F Y X U c a) t ω]
    by_cases h : 0 < τ ω
    · rw [ite_eq_left h]
      have hk (k : Fin m) : ∫ u in Ioc 0 t, driftDensity Fc Y' M' c' a' k u ω ∂(U' k ω).measure =
          ∫ u in Ioc 0 (min t (r ω)), driftDensity F Y X c a k u ω ∂(U k ω).measure := by
        rw [setIntegral_congr_fun measurableSet_Ioc fun u _ => hd ω h k u]
        exact integral_stopStieltjes_comp_min (U k ω) (r ω) t
          (fun u => driftDensity F Y X c a k u ω)
      have h0 : min (0 : ℝ≥0) (r ω) = 0 := min_eq_left bot_le
      have hFt := (hFceq _ (hbd ω h _ (hrle ω t)).1).eq_of_nhds
      have hF0 := (hFceq _ (hbd ω h _ (hrle ω 0)).1).eq_of_nhds
      simp only [residual, hk]
      rw [hY'v, hM'v, hY'v, hM'v]
      simp only [h, ite_true]
      rw [hFt, hF0, h0]
    · rw [ite_eq_right h]
      simp only [residual, hY'v, hM'v, h, ite_false, sub_self,
        Finset.sum_eq_zero fun k _ => hint0R k t ω h _]
  have hI2 : bracket Fc Y' M' U' a' =
      stoppedProcess (fun t => Sτ.indicator (bracket F Y X U a t)) τ := by
    funext t ω
    rw [hvR (bracket F Y X U a) t ω]
    by_cases h : 0 < τ ω
    · rw [ite_eq_left h]
      simp only [bracket]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [setIntegral_congr_fun measurableSet_Ioc fun u _ => hq ω h k u]
      exact integral_stopStieltjes_comp_min (U k ω) (r ω) t
        (fun u => partialSnd F (Y u ω, X u ω) ^ 2 * a k u ω)
    · rw [ite_eq_right h]
      exact Finset.sum_eq_zero fun k _ => hint0R k t ω h _
  refine ⟨?_, ?_⟩
  · rw [← hI1]; exact hcore1
  · convert hcore2 using 1
    rw [hI1, hI2]
    funext t ω
    rw [stoppedProcess_indicator_apply
      (fun t ω => residual F Y X U c a t ω ^ 2 - bracket F Y X U a t ω) hτζ t ω,
      hvR (residual F Y X U c a) t ω, hvR (bracket F Y X U a) t ω]
    split_ifs <;> first | rfl | simp

end OneStop

/-! ### Continuity before the lifetime -/

section Cont

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
  {F : E × ℝ → ℝ} {O : Set (E × ℝ)} {ζ : Ω → WithTop ℝ≥0} {X : ℝ≥0 → Ω → ℝ}
  {Y : ℝ≥0 → Ω → E} {U : Fin m → Ω → StieltjesFunction ℝ≥0}
  {c : Fin m → ℝ≥0 → Ω → E} {a : Fin m → ℝ≥0 → Ω → ℝ}

omit [NormedSpace ℝ E] in
lemma continuousOn_state_comp {G : Type*} [TopologicalSpace G] {Φ : E × ℝ → G}
    (hΦ : ContinuousOn Φ O) {ω : Ω}
    (hXc : ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hYc : ContinuousOn (Y · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hO_path : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → (Y t ω, X t ω) ∈ O) :
    ContinuousOn (fun t => Φ (Y t ω, X t ω)) {t | (t : WithTop ℝ≥0) < ζ ω} :=
  hΦ.comp (hYc.prodMk hXc) fun t ht => hO_path t ht

/-- **The residual and the bracket are continuous before the lifetime.** -/
theorem continuousOn_residual_bracket (hO : IsOpen O) (hF : ContDiffOn ℝ 3 F O) {ω : Ω}
    (hXc : ContinuousOn (X · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hYc : ContinuousOn (Y · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hcc : ∀ k, ContinuousOn (c k · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hac : ∀ k, ContinuousOn (a k · ω) {t | (t : WithTop ℝ≥0) < ζ ω})
    (hUc : ∀ k, Continuous (U k ω))
    (hO_path : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → (Y t ω, X t ω) ∈ O) :
    ContinuousOn (fun t => residual F Y X U c a t ω) {t | (t : WithTop ℝ≥0) < ζ ω} ∧
      ContinuousOn (fun t => bracket F Y X U a t ω) {t | (t : WithTop ℝ≥0) < ζ ω} := by
  have hD1 : ContinuousOn (fderiv ℝ F) O := hF.continuousOn_fderiv_of_isOpen hO (by norm_num)
  have hF2 : ContDiffOn ℝ 2 (fderiv ℝ F) O := hF.fderiv_of_isOpen hO (by norm_num)
  have hD2 : ContinuousOn (fderiv ℝ (fderiv ℝ F)) O :=
    hF2.continuousOn_fderiv_of_isOpen hO (by norm_num)
  have hPF : ContinuousOn (partialFst F) O := hD1.clm_comp continuousOn_const
  have hPS : ContinuousOn (partialSnd F) O := hD1.clm_apply continuousOn_const
  have hPSS : ContinuousOn (partialSndSnd F) O :=
    (hD2.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hdc (k : Fin m) : ContinuousOn (fun u => driftDensity F Y X c a k u ω)
      {t | (t : WithTop ℝ≥0) < ζ ω} :=
    ((continuousOn_state_comp hPF hXc hYc hO_path).clm_apply (hcc k)).add
      ((continuousOn_const.mul (continuousOn_state_comp hPSS hXc hYc hO_path)).mul (hac k))
  have hqc (k : Fin m) : ContinuousOn (fun u => partialSnd F (Y u ω, X u ω) ^ 2 * a k u ω)
      {t | (t : WithTop ℝ≥0) < ζ ω} :=
    ((continuousOn_state_comp hPS hXc hYc hO_path).pow 2).mul (hac k)
  refine ⟨?_, ?_⟩
  · refine ((continuousOn_state_comp hF.continuousOn hXc hYc hO_path).sub continuousOn_const).sub ?_
    exact continuousOn_finsetSum (f := fun k t => ∫ u in Ioc 0 t,
      driftDensity F Y X c a k u ω ∂(U k ω).measure) _ fun k _ =>
        continuousOn_integral_Ioc_zero (U k ω) (hUc k) (hdc k)
  · exact continuousOn_finsetSum (f := fun k t => ∫ u in Ioc 0 t,
      partialSnd F (Y u ω, X u ω) ^ 2 * a k u ω ∂(U k ω).measure) _ fun k _ =>
        continuousOn_integral_Ioc_zero (U k ω) (hUc k) (hqc k)

end Cont

end InteractingSLE.Ito.Gm2
