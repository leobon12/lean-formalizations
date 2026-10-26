import SupercriticalConformalCovariance.Cover.Display10

/-!
# Good covers, part 3: the Borel–Cantelli subsequence

Source: the paper, l. 448–451 ("Choose a deterministic subsequence ε_j ↓ 0 with summable failure
probabilities, simultaneously for a countable compact exhaustion. Then almost surely the good covers occur
along this subsequence on every compact set."), and Lemma 2.1, l. 145–147.

* `goodCovers_seq`: for a countable family of compact sets `K n` (each with its own neighbourhood
  `cl B_ρₙ(K n) × (0, r₀ₙ]` of locality and probability `≥ p`) and any positive `ε_j → 0` with
  `∑ ε_j^q < ∞`, almost surely, for every `n`, the good cover of `K n` at scale `ε_j` occurs for all large `j`.
  The rate of `display10_uniform` is polynomial, so one deterministic sequence serves every `n`.
* `summable_two_pow` and `goodCovers_seq_two_pow`: the sequence `ε_j = 2^{-(j+1)}`.
* `goodCovers_everyCompact`: the paper's form. If, as in Lemma 5.1, for every compact `L ⊆ U` there is
  `r₀ > 0` with locality and `inf_{z ∈ L} P[F z r] ≥ p` for `r ≤ r₀`, then almost surely, for EVERY compact
  `L ⊆ U`, the good cover of `L` at scale `ε_j` occurs for all large `j`. The exhaustion is
  `CompactExhaustion.choice` of the open subspace `U`; the neighbourhood `cl B_ρ(K)` of each exhausting set is
  supplied by applying the hypothesis to the compact set `cl B_ρ(K) ⊆ U` (uniformity in `z` on a
  neighbourhood of `K`, not just on `K`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Cover

open LQGMetric LQGMetric.Blueprint

/-- **the Borel–Cantelli subsequence for a countable family of compact sets** -/
theorem goodCovers_seq (q : ℝ) (hq : 0 < q) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (F : ℂ → ℝ → Set Ω) (K : ℕ → Set ℂ),
        (∀ n, Bornology.IsBounded (K n)) →
        (∀ n, ∃ ρ r₀ : ℝ, 0 < ρ ∧ 0 < r₀ ∧ IsAnnulusLocalOn P h F (K n) ρ r₀ ∧
          IsProbLowerOn P F (K n) ρ r₀ p) →
        ∀ ε : ℕ → ℝ, (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) → Summable (fun j => ε j ^ q) →
        ∀ᵐ ω ∂P, ∀ n, ∀ᶠ j in atTop, ω ∈ coverEvent F (K n) (ε j) := by
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := display10_uniform q hq
  refine ⟨p, hp0, hp1, ?_⟩
  intro Ω _ P _ h hh F K hK hhyp ε hε0 hε hsum
  rw [ae_all_iff]
  intro n
  obtain ⟨ρ, r₀, hρ, hr₀, hloc, hprob⟩ := hhyp n
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hK n)
  set R₀ : ℝ := max R 0
  have hKR : K n ⊆ closedBall 0 R₀ := fun x hx =>
    mem_closedBall_zero_iff.2 ((hR x hx).trans (le_max_left _ _))
  set ε₁ : ℝ := min (min ρ r₀) (1 / 8)
  have hε₁ : 0 < ε₁ := lt_min (lt_min hρ hr₀) (by norm_num)
  set C : ℝ := c * (200 * R₀ + 5) ^ 2
  have hC : 0 ≤ C := by positivity
  classical
  -- the failure events, set to `∅` while `ε_j` is not yet small
  set s : ℕ → Set Ω := fun j => if ε j < ε₁ then (coverEvent F (K n) (ε j))ᶜ else ∅ with hs
  have hsj : ∀ j, P (s j) ≤ ENNReal.ofReal (C * ε j ^ q) := by
    intro j
    simp only [hs]
    split_ifs with hj
    · have h1 : ε j < min ρ r₀ := hj.trans_le (min_le_left _ _)
      exact H P h hh F (K n) R₀ (le_max_right _ _) hKR ρ r₀ hloc hprob (ε j) (hε0 j)
        (hj.trans_le (min_le_right _ _)) (h1.le.trans (min_le_left _ _))
        (h1.le.trans (min_le_right _ _))
    · simp
  have hfin : ∑' j, P (s j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hsj)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hC (Real.rpow_nonneg (hε0 j).le _))
      (hsum.mul_left C)]
    exact ENNReal.ofReal_ne_top
  have hsmall : ∀ᶠ j in atTop, ε j < ε₁ := hε.eventually (gt_mem_nhds hε₁)
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω, hsmall] with j hj hjs
  simp only [hs, ite_eq_left hjs, mem_compl_iff, not_not] at hj
  exact hj

/-- `∑ (2^{-(j+1)})^q < ∞` -/
theorem summable_two_pow {q : ℝ} (hq : 0 < q) :
    Summable (fun j : ℕ => ((2 : ℝ)⁻¹ ^ (j + 1)) ^ q) := by
  have hr0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ q := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ)⁻¹ ^ q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hq
  refine ((summable_geometric_of_lt_one hr0 hr1).mul_left ((2 : ℝ)⁻¹ ^ q)).congr fun j => ?_
  have e : ((2 : ℝ)⁻¹ ^ (j + 1)) ^ q = ((2 : ℝ)⁻¹ ^ q) ^ (j + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  rw [e, pow_succ']

theorem tendsto_two_pow : Tendsto (fun j : ℕ => (2 : ℝ)⁻¹ ^ (j + 1)) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 1)

/-- **the deterministic sequence `ε_j = 2^{-(j+1)}`** serves every member of the countable family -/
theorem goodCovers_seq_two_pow (q : ℝ) (hq : 0 < q) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (F : ℂ → ℝ → Set Ω) (K : ℕ → Set ℂ),
        (∀ n, Bornology.IsBounded (K n)) →
        (∀ n, ∃ ρ r₀ : ℝ, 0 < ρ ∧ 0 < r₀ ∧ IsAnnulusLocalOn P h F (K n) ρ r₀ ∧
          IsProbLowerOn P F (K n) ρ r₀ p) →
        ∀ᵐ ω ∂P, ∀ n, ∀ᶠ j in atTop, ω ∈ coverEvent F (K n) ((2 : ℝ)⁻¹ ^ (j + 1)) := by
  obtain ⟨p, hp0, hp1, H⟩ := goodCovers_seq q hq
  exact ⟨p, hp0, hp1, fun P _ h hh F K hK hhyp =>
    H P h hh F K hK hhyp _ (fun j => pow_pos (by norm_num) _) tendsto_two_pow
      (summable_two_pow hq)⟩

/-- **the good covers occur along the subsequence on every compact set** (l. 448–451), in the paper's
form: the hypothesis is Lemma 5.1's, for every compact `L ⊆ U` (with `z ∈ L`, no neighbourhood). -/
theorem goodCovers_everyCompact (q : ℝ) (hq : 0 < q) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (U : Set ℂ), IsOpen U → ∀ F : ℂ → ℝ → Set Ω,
        (∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
          AEEventIn P (localSigma h z r) (F z r) ∧
          ENNReal.ofReal p ≤ P (F z r)) →
        ∀ ε : ℕ → ℝ, (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) → Summable (fun j => ε j ^ q) →
        ∀ᵐ ω ∂P, ∀ L : Set ℂ, IsCompact L → L ⊆ U →
          ∀ᶠ j in atTop, ω ∈ coverEvent F L (ε j) := by
  obtain ⟨p, hp0, hp1, H⟩ := goodCovers_seq q hq
  refine ⟨p, hp0, hp1, ?_⟩
  intro Ω _ P _ h hh U hU F hhyp ε hε0 hε hsum
  -- a compact exhaustion of the open subspace `U`
  let V : TopologicalSpace.Opens ℂ := ⟨U, hU⟩
  let E : CompactExhaustion V := CompactExhaustion.choice V
  let K : ℕ → Set ℂ := fun n => Subtype.val '' E n
  have hKc : ∀ n, IsCompact (K n) := fun n => Subtype.isCompact_iff.1 (E.isCompact n)
  have hKU : ∀ n, K n ⊆ U := fun n => by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hKex : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∃ n, L ⊆ K n := by
    intro L hL hLU
    have hL' : IsCompact (Subtype.val ⁻¹' L : Set V) := by
      rw [Subtype.isCompact_iff, image_preimage_eq_of_subset fun x hx => ⟨⟨x, hLU hx⟩, rfl⟩]
      exact hL
    obtain ⟨n, hn⟩ := E.exists_superset_of_isCompact hL'
    refine ⟨n, fun x hx => ⟨⟨x, hLU hx⟩, hn hx, rfl⟩⟩
  -- the neighbourhood hypothesis from the paper's hypothesis on `cl B_ρ(K n)`
  have hnbhd : ∀ n, ∃ ρ r₀ : ℝ, 0 < ρ ∧ 0 < r₀ ∧ IsAnnulusLocalOn P h F (K n) ρ r₀ ∧
      IsProbLowerOn P F (K n) ρ r₀ p := by
    intro n
    obtain ⟨ρ, hρ, hρU⟩ := (hKc n).exists_cthickening_subset_open hU (hKU n)
    obtain ⟨r₀, hr₀, hz⟩ := hhyp _ (hKc n).cthickening hρU
    exact ⟨ρ, r₀, hρ, hr₀, fun z hz' r hr => (hz z hz' r hr).1, fun z hz' r hr => (hz z hz' r hr).2⟩
  filter_upwards [H P h hh F K (fun n => (hKc n).isBounded) hnbhd ε hε0 hε hsum] with ω hω
  intro L hL hLU
  obtain ⟨n, hn⟩ := hKex L hL hLU
  filter_upwards [hω n] with j hj
  exact coverEvent_mono F hn (hε0 j).le hj

end SupercriticalConformalCovariance.Cover
