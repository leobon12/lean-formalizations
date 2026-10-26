import SupercriticalLFPPAS.Identification.Deterministic
import SupercriticalLFPPAS.Inputs.EscapeTendsto
import SupercriticalLFPPAS.Inputs.RationalCirclePositive
import SupercriticalLFPPAS.Field.HeatVersion
import SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.CompactSetDist
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong

/-!
# (5.6) and its q′ analogue: no comparison constant below one (packet UND)

Paper §5, l. 543–568 ((5.6), "the same argument shows that fewer than N bands have q′ ≤ k"); SB2 §2.6 bullets "(5.6)"
and "q′ direction", D9 steps 3–4, M9. The target `noContract_of` proves the interface `Core.NoContractStmt` (the
contradiction input of Proposition 5.1) from `ConfinementStmt` (Lemma 2.2), `LocCircleStmt` ((2.9)) and
`LFPPGeodesicStmt`.

Fix `c < 1`, deterministic radii `ρ(ε) → 0`, put `c₀ = max(c, 1/2)` and choose `κ = e^{θ'} > 1` with `c₀κ² < 1`. With
`O = ∂B₁(0)`, `O′ = ∂B₂(0)` and the displaced rational circles `O_n = ∂B_{a_n}(0)`, `O′_n = ∂B_{b_n}(0)` of
`Identification.Deterministic`, choose deterministically (each bad event has probability at most `1/10`):
* `n₀`: `D(O,O′) ≤ κ D(O_{n₀}, O′_{n₀})` (measurable events, a.s. eventually true by lsc and compactness,
  `und_tendsto_measure_zero`);
* `R₁ = k₁ ≥ 2`: `D(O,O′) < D(O, ∂B_{R₁}(0))` ((1.4), `ae_d2EscapeSetDist_tendsto`, with `D(O,O′) < ∞` a.s.);
* `M = k₂`: `D(O,O′) ≤ M`;
* `R₀` from `ConfinementStmt` (`K = O`, level `κM + 1`), and `R = max(R₁, R₀, 2)`.
Then for small `ε`: `ρ(ε) < 1/(n₀+3)`, and the outer probabilities of failure of (2.9) for `(O_{n₀}, O′_{n₀})` and for
`(O, O′)` and of the confinement are at most `1/10`. Off the union of five bad sets (one of them null) the deterministic
contradictions `und_not_compIn_dsource` / `und_not_compIn_xsource` exclude `CompIn` in each direction, so both outer
probabilities of `¬ CompIn` are at least `1/2` (`und_half_le_of_cover`; outer measures are subadditive, so no
measurability of the `X̂`-events is needed). `θ = 1/2`.

Deviation from the paper's route (allowed: the target is the interface statement): the ordinary-LFPP half of (5.6)
(subsequence form of `S.hlim`, (2.1)) is replaced by the crossing estimate of `Identification.Deterministic` together
with (2.9) on the displaced circles; the hypothesis `LocApproxStmt` of the target is therefore not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Identification

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric IsNormalizedWholePlaneGFF)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)

/-! ### Probability tools -/

/-- Measurable events that almost surely eventually fail have probabilities tending to `0` (continuity from above
applied to the tails `⋃_{m ≥ n} B_m`). -/
theorem und_tendsto_measure_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {B : ℕ → Set Ω} (hB : ∀ n, MeasurableSet (B n)) (hae : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ B n) :
    Tendsto (fun n => P (B n)) atTop (𝓝 0) := by
  set C : ℕ → Set Ω := fun n => ⋃ m ≥ n, B m with hC
  have hCm : ∀ n, NullMeasurableSet (C n) P := fun n =>
    (MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hB m).nullMeasurableSet
  have hanti : Antitone C := fun n n' hnn' ω hω => by
    obtain ⟨m, hm, hmB⟩ := mem_iUnion₂.1 hω
    exact mem_iUnion₂.2 ⟨m, le_trans hnn' hm, hmB⟩
  have hlim := tendsto_measure_iInter_atTop hCm hanti ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n, C n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hae)
    simp only [mem_iInter] at hω
    simp only [mem_ofPred_eq, not_eventually, not_not]
    exact frequently_atTop.2 fun n => by
      obtain ⟨m, hm, hmB⟩ := mem_iUnion₂.1 (hω n)
      exact ⟨m, hm, hmB⟩
  rw [hnull] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    (fun n => measure_mono fun ω hω => mem_iUnion₂.2 ⟨n, le_rfl, hω⟩)

/-- Five bad sets of outer probability at most `1/10` each: the complement of their union, which lies in `A`, gives
`P(A) ≥ 1/2` (subadditivity of the outer measure; no measurability needed). -/
theorem und_half_le_of_cover {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A B₁ B₂ B₃ B₄ B₅ : Set Ω} (hcov : ∀ ω, ω ∉ B₁ → ω ∉ B₂ → ω ∉ B₃ → ω ∉ B₄ → ω ∉ B₅ → ω ∈ A)
    (h₁ : P B₁ ≤ ENNReal.ofReal (1 / 10)) (h₂ : P B₂ ≤ ENNReal.ofReal (1 / 10))
    (h₃ : P B₃ ≤ ENNReal.ofReal (1 / 10)) (h₄ : P B₄ ≤ ENNReal.ofReal (1 / 10))
    (h₅ : P B₅ ≤ ENNReal.ofReal (1 / 10)) :
    ENNReal.ofReal (1 / 2) ≤ P A := by
  classical
  have hsub : (univ : Set Ω) ⊆ A ∪ (B₁ ∪ (B₂ ∪ (B₃ ∪ (B₄ ∪ B₅)))) := by
    intro ω _
    by_cases g₁ : ω ∈ B₁
    · exact Or.inr (Or.inl g₁)
    by_cases g₂ : ω ∈ B₂
    · exact Or.inr (Or.inr (Or.inl g₂))
    by_cases g₃ : ω ∈ B₃
    · exact Or.inr (Or.inr (Or.inr (Or.inl g₃)))
    by_cases g₄ : ω ∈ B₄
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl g₄))))
    by_cases g₅ : ω ∈ B₅
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr g₅))))
    exact Or.inl (hcov ω g₁ g₂ g₃ g₄ g₅)
  have h10 : (0 : ℝ) ≤ 1 / 10 := by norm_num
  have hsum : ENNReal.ofReal (1 / 10) + (ENNReal.ofReal (1 / 10) + (ENNReal.ofReal (1 / 10) +
      (ENNReal.ofReal (1 / 10) + ENNReal.ofReal (1 / 10)))) = ENNReal.ofReal (1 / 2) := by
    rw [← ENNReal.ofReal_add h10 h10, ← ENNReal.ofReal_add h10 (by norm_num),
      ← ENNReal.ofReal_add h10 (by norm_num), ← ENNReal.ofReal_add h10 (by norm_num)]
    norm_num
  have h1 : (1 : ℝ≥0∞) ≤ P A + ENNReal.ofReal (1 / 2) := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ ≤ P (A ∪ (B₁ ∪ (B₂ ∪ (B₃ ∪ (B₄ ∪ B₅))))) := measure_mono hsub
      _ ≤ P A + (P B₁ + (P B₂ + (P B₃ + (P B₄ + P B₅)))) := by
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
          exact measure_union_le _ _
      _ ≤ P A + (ENNReal.ofReal (1 / 10) + (ENNReal.ofReal (1 / 10) + (ENNReal.ofReal (1 / 10) +
            (ENNReal.ofReal (1 / 10) + ENNReal.ofReal (1 / 10))))) := by gcongr
      _ = P A + ENNReal.ofReal (1 / 2) := by rw [hsum]
  have h2 : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  rw [← h2] at h1
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h1

/-- The good event of (2.9) at one cutoff, read off its failure set. -/
theorem und_of_not_mem_fail {Ω : Type*} {ε : ℝ} {Q : ε ∈ Ioo (0 : ℝ) 1 → Ω → Prop} {ω : Ω}
    (hω : ω ∉ {ω | ∃ hε : ε ∈ Ioo (0 : ℝ) 1, ¬ Q hε ω}) (hε : ε ∈ Ioo (0 : ℝ) 1) : Q hε ω := by
  by_contra hcon
  exact hω ⟨hε, hcon⟩

/-! ### The target -/

/-- **(5.6) and its `q′` analogue, core form** (paper §5, l. 543–568; SB2 §2.6, D9 steps 3–4, M9): from Lemma 2.2,
(2.9) and LFPP geodesics alone. For `c < 1` and deterministic radii `ρ(ε) → 0` there are `R ≥ 1` and `θ > 0` (here
`θ = 1/2`) such that, for small `ε`, the comparison `CompIn` with constant `c` and radius `ρ(ε)` fails with outer
probability at least `θ`, in both directions. -/
theorem noContract_of_core (S : Core.Setup) (hConf : Core.ConfinementStmt S) (hCirc : Core.LocCircleStmt S)
    (hG : Core.LFPPGeodesicStmt) : Core.NoContractStmt S := by
  intro Ω _ P _ h hh c hc ρ hρ hρ0
  -- the constants `c₀ = max c (1/2) < 1` and `κ = e^{θ'} > 1` with `c₀ κ² < 1`
  set c₀ : ℝ := max c (1 / 2) with hc₀def
  have hcc₀ : c ≤ c₀ := le_max_left _ _
  have hc₀0 : 0 ≤ c₀ := le_trans (by norm_num) (le_max_right c (1 / 2))
  have hc₀1 : c₀ < 1 := max_lt hc (by norm_num)
  obtain ⟨θ', hθ', hck⟩ : ∃ θ' : ℝ, 0 < θ' ∧ c₀ * Real.exp θ' * Real.exp θ' < 1 := by
    have he : Tendsto Real.exp (𝓝 0) (𝓝 1) := by
      simpa only [Real.exp_zero] using Real.continuous_exp.tendsto 0
    have hcont : Tendsto (fun θ : ℝ => c₀ * Real.exp θ * Real.exp θ) (𝓝 0) (𝓝 c₀) := by
      simpa only [mul_one] using (tendsto_const_nhds.mul he).mul he
    have hev : ∀ᶠ θ in 𝓝[>] (0 : ℝ), c₀ * Real.exp θ * Real.exp θ < 1 ∧ θ ∈ Ioi (0 : ℝ) :=
      ((hcont.eventually (gt_mem_nhds hc₀1)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨θ', h1, h2⟩ := hev.exists
    exact ⟨θ', h2, h1⟩
  set κ : ℝ := Real.exp θ' with hκdef
  have hκ1 : 1 < κ := Real.one_lt_exp_iff.2 hθ'
  have hκ0 : 0 ≤ κ := (Real.exp_pos θ').le
  have h10 : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 10) := ENNReal.ofReal_pos.2 (by norm_num)
  -- measurability of the `D`-observables
  have hDm : Measurable fun ω => S.D (h ω) := S.hD.1.comp hh.1.measurable
  have hsdm : ∀ K₁ K₂ : Set ℂ, IsCompact K₁ → IsCompact K₂ →
      Measurable fun ω => setDist (S.D (h ω)) K₁ K₂ := fun K₁ K₂ h₁ h₂ =>
    (SupercriticalLQGUniqueness.Uniqueness.Measurability.ClauseEvents.measurable_setDist_compact K₁ K₂ h₁ h₂).comp
      hDm
  set t : Ω → ℝ≥0∞ := fun ω => setDist (S.D (h ω)) (sphere 0 1) (sphere 0 2) with htdef
  have htm : Measurable t := hsdm _ _ (isCompact_sphere 0 1) (isCompact_sphere 0 2)
  -- almost sure inputs: `0 < D(O,O′) < ∞` ((iii)), the barrier and length space, escape (1.4)
  have hposfin : ∀ᵐ ω ∂P, 0 < t ω ∧ t ω < ⊤ := by
    have h12 := Inputs.ae_setDist_rationalCircle_pos_lt_top S.hD P h hh (0, 0) (0, 0) 1 2 one_pos two_pos
      (by simpa using und_disjoint_sphere (show (1 : ℝ) ≠ 2 by norm_num))
    simpa using h12
  have hweak := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric S.hD
  have hreg := SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ae_regularAt_self hweak P h hh
  have hesc := ae_d2EscapeSetDist_tendsto hweak P h hh
  -- `n₀`: the lsc event `D(O,O′) ≤ κ D(O_{n₀}, O′_{n₀})`
  set Blsc : ℕ → Set Ω := fun n =>
    {ω | ENNReal.ofReal κ * setDist (S.D (h ω)) (sphere 0 (undA n)) (sphere 0 (undB n)) < t ω} with hBlscdef
  have hBlsc : Tendsto (fun n => P (Blsc n)) atTop (𝓝 0) := by
    refine und_tendsto_measure_zero P (fun n => measurableSet_lt
      ((hsdm _ _ (isCompact_sphere _ _) (isCompact_sphere _ _)).const_mul _) htm) ?_
    filter_upwards [hposfin] with ω hω
    exact (und_eventually_le_mul (S.D (h ω)) hω.1.ne' hω.2.ne hκ1).mono fun n hn => not_lt.2 hn
  obtain ⟨n₀, hn₀⟩ := ((tendsto_order.1 hBlsc).2 _ h10).exists
  -- `R₁ = k₁`: the escape event `D(O,O′) < D(O, ∂B_{k₁}(0))`
  set Besc : ℕ → Set Ω := fun k => {ω | setDist (S.D (h ω)) (sphere 0 1) (sphere 0 (k : ℝ)) ≤ t ω}
    with hBescdef
  have hBesc : Tendsto (fun k => P (Besc k)) atTop (𝓝 0) := by
    refine und_tendsto_measure_zero P (fun k => measurableSet_le
      (hsdm _ _ (isCompact_sphere _ _) (isCompact_sphere _ _)) htm) ?_
    filter_upwards [hposfin, hesc] with ω hω hescω
    have hlim := (hescω 1).comp tendsto_natCast_atTop_atTop
    have hsub : sphere (0 : ℂ) 1 ⊆ closedBall 0 ((1 : ℕ) : ℝ) := by
      rw [Nat.cast_one]
      exact sphere_subset_closedBall
    filter_upwards [(tendsto_order.1 hlim).1 (t ω) hω.2] with k hk
    rw [mem_ofPred_eq, not_le]
    exact hk.trans_le (und_setDist_mono _ hsub subset_rfl)
  obtain ⟨k₁, hk₁, hk₁2⟩ := (((tendsto_order.1 hBesc).2 _ h10).and (eventually_ge_atTop 2)).exists
  -- `M = k₂`: the event `D(O,O′) ≤ M`
  set BM : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal (k : ℝ) < t ω} with hBMdef
  have hBM : Tendsto (fun k => P (BM k)) atTop (𝓝 0) := by
    refine und_tendsto_measure_zero P (fun k => measurableSet_lt measurable_const htm) ?_
    filter_upwards [hposfin] with ω hω
    filter_upwards [eventually_ge_atTop ⌈(t ω).toReal⌉₊] with k hk
    rw [mem_ofPred_eq, not_lt]
    calc t ω = ENNReal.ofReal (t ω).toReal := (ENNReal.ofReal_toReal hω.2.ne).symm
      _ ≤ ENNReal.ofReal (k : ℝ) :=
          ENNReal.ofReal_le_ofReal ((Nat.le_ceil _).trans (by exact_mod_cast hk))
  obtain ⟨k₂, hk₂⟩ := ((tendsto_order.1 hBM).2 _ h10).exists
  -- confinement (Lemma 2.2) of the localized escape distance from `O`, through the canonical heat version
  obtain ⟨X, hX, -⟩ := Field.exists_jointHeatVersion_core P h hh
  obtain ⟨R₀, hR₀⟩ := hConf P h hh X hX (sphere 0 1) (isCompact_sphere 0 1) (κ * (k₂ : ℝ) + 1) (1 / 10)
    (by norm_num)
  set R : ℝ := max (max (k₁ : ℝ) R₀) 2 with hRdef
  have hRk₁ : (k₁ : ℝ) ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRR₀ : R₀ ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR2 : (2 : ℝ) ≤ R := le_max_right _ _
  have hk₁1 : (1 : ℝ) < k₁ := by exact_mod_cast (show 1 < k₁ by omega)
  refine ⟨R, 1 / 2, by linarith, by norm_num, ?_⟩
  -- the circle comparison (2.9) for `(O_{n₀}, O′_{n₀})` and for `(O, O′)`
  have hLC₁ := hCirc P h hh (0, 0) (0, 0) (1 + 1 / ((n₀ : ℚ) + 3)) (2 - 1 / ((n₀ : ℚ) + 3)) (und_ratA_pos n₀)
    (und_ratB_pos n₀)
    (by rw [und_rationalCircle_undA, und_rationalCircle_undB]; exact und_disjoint_sphere (undA_lt_undB n₀).ne) θ' hθ'
  rw [und_rationalCircle_undA, und_rationalCircle_undB] at hLC₁
  have hO1 : rationalCircle (0, 0) 1 = sphere (0 : ℂ) 1 := by simp [rationalCircle]
  have hO2 : rationalCircle (0, 0) 2 = sphere (0 : ℂ) 2 := by simp [rationalCircle]
  have hLC₂ := hCirc P h hh (0, 0) (0, 0) 1 2 one_pos two_pos
    (by rw [hO1, hO2]; exact und_disjoint_sphere (by norm_num)) θ' hθ'
  rw [hO1, hO2] at hLC₂
  -- the null set of the almost sure inputs
  set N : Set Ω := {ω | ¬ ((0 < t ω ∧ t ω < ⊤) ∧
    SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.RegularAt S.D (S.ξ : ℝ) (h ω))} with hNdef
  have hN : P N ≤ ENNReal.ofReal (1 / 10) := by
    rw [show P N = 0 from ae_iff.1 (hposfin.and hreg)]
    exact zero_le
  have hempty : P (∅ : Set Ω) ≤ ENNReal.ofReal (1 / 10) := by
    rw [measure_empty]
    exact zero_le
  -- small cutoffs
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ρ ε < 1 / ((n₀ : ℝ) + 3) := hρ0.eventually (gt_mem_nhds (und_gap_pos n₀))
  have e2 := (tendsto_order.1 hLC₁).2 _ h10
  have e3 := (tendsto_order.1 hLC₂).2 _ h10
  have e4 := hR₀ R hRR₀
  filter_upwards [e1, e2, e3, e4] with ε h1 h2 h3 h4
  intro hε
  have hρa : 1 + ρ ε ≤ undA n₀ := by unfold undA; linarith
  have hρb : undB n₀ ≤ 2 - ρ ε := by unfold undB; linarith
  constructor
  · -- the `D`-source: (5.6) through (2.9) on the displaced circles and the crossing estimate
    refine und_half_le_of_cover P ?_ hn₀.le hk₁.le hN h2.le hempty
    intro ω g₁ g₂ g₃ g₄ _
    simp only [hBlscdef, hBescdef, hNdef, mem_ofPred_eq, not_lt, not_le, not_not] at g₁ g₂ g₃
    obtain ⟨⟨hpos, hfin⟩, hregω⟩ := g₃
    have hloc := (und_of_not_mem_fail g₄ hε).2
    exact und_not_compIn_dsource (S.D (h ω)) (Core.locMetric S ε hε (h ω)) hregω.barrier hregω.length
      (R₁ := (k₁ : ℝ)) hk₁1 hRk₁ hcc₀ hc₀0 hκ0 hck (undA_lt_undB n₀).le hρa hρb hpos.ne' hfin g₂ g₁ hloc
  · -- the `X̂`-source (the `q′` claim): an `X̂`-geodesic realizing `X̂(O,O′)`, confined by Lemma 2.2
    refine und_half_le_of_cover P ?_ hn₀.le hk₂.le hN h3.le (h4 hε).1
    intro ω g₁ g₂ g₃ g₄ g₅
    simp only [hBlscdef, hBMdef, hNdef, mem_ofPred_eq, not_lt, not_le, not_not] at g₁ g₂ g₃ g₅
    obtain ⟨⟨hpos, hfin⟩, -⟩ := g₃
    have hloc := (und_of_not_mem_fail g₄ hε).1
    exact und_not_compIn_xsource hG (S.D (h ω)) (S.ξ : ℝ) (S.m ⟨ε, hε.1⟩)
      (SupercriticalLQGUniqueness.B2.Polylog.plMollifyC 1 ε hε (h ω)) (M := (k₂ : ℝ)) (by linarith) hcc₀ hc₀0 hκ0
      (Nat.cast_nonneg _) hck (undA_lt_undB n₀).le hρa hρb hpos.ne' hfin g₂ hloc g₅ g₁

-- The target keeps the packet's signature verbatim; its (2.1) hypothesis `hA` is not needed by this route (the crossing
-- estimate replaces the ordinary-LFPP half of (5.6)), hence the local linter option.
set_option linter.unusedVariables false in
/-- **(5.6) and its `q′` analogue** (packet UND target; paper §5, l. 543–568; SB2 §2.6, D9 steps 3–4, M9), in the form
consumed by Proposition 5.1. The hypothesis `hA` ((2.1)) is not used: see `noContract_of_core`. -/
theorem noContract_of (S : Core.Setup) (hConf : Core.ConfinementStmt S) (hCirc : Core.LocCircleStmt S)
    (hA : Core.LocApproxStmt) (hG : Core.LFPPGeodesicStmt) : Core.NoContractStmt S :=
  noContract_of_core S hConf hCirc hG

end SupercriticalLFPPAS.Identification
