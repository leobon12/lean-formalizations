import SupercriticalLFPPAS.Proposition51.Chain
import SupercriticalLFPPAS.Iteration.Quantiles
import NV1Evidence

/-!
# Proposition 5.1: the low-quantile claim (packet P51)

Paper l. 543–566, SB2 §2.6 "Fewer than N bands have q_{ε,j} ≤ k", Details D9 step 3 (with M9: the radius `R` is the
one produced by (5.6) for the given constant and radii, and the iteration is run with that `R`).

A band is *low* for direction `b` (`IsLow`) when at least `⌈n/3⌉` of its `n` radii have `kapDir ≤ k`, i.e. its
`⌈n/3⌉`-th smallest ratio is `≤ k` (D8: "m-th smallest κ ≤ k ⟺ #{κ ≤ k} ≥ m"). `low_count`: for `ε` small, fewer than `N`
of the `3N` bands are low, in each direction. Proof by contradiction: on a reference space, `NoContractStmt` with
`c := (1 + 3d₀/λ)k + (1−λ)^N C_init < 1` and `ρ(ε) := 513 ε^{s_{3N}}` gives `R, θ` and a failure probability `≥ θ` for
all small `ε`; if `≥ N` bands were low at arbitrarily small `ε`, the chain (`chain_rate`, with `K := k`, contracting in
the low bands, `S_ε := {κ ≤ k}`) and the initial comparison would make that failure probability `O(ε^{min(p₀,β)}) < θ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Proposition51

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric IsNormalizedWholePlaneGFF)

/-- Band `i + 1` is low for direction `b` at level `k`: at least `⌈n/3⌉` of its `n` radii have `kapDir ≤ k`. -/
def IsLow (S : Core.Setup) (b : Bool) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (k : ℝ) (i : ℕ) : Prop :=
  Iteration.thirdQuantileIndex (bandExps ε i).card ≤
    ((bandExps ε i).filter fun j => kapDir S b ε hε j ≤ k).card

instance (S : Core.Setup) (b : Bool) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (k : ℝ) :
    DecidablePred (IsLow S b ε hε k) := fun _ => Nat.decLe _ _

theorem card_le_three_mul_thirdQuantileIndex (n : ℕ) : n ≤ 3 * Iteration.thirdQuantileIndex n := by
  unfold Iteration.thirdQuantileIndex
  omega

/-- In a low band the radii with `kapDir ≤ k` are admissible for the contraction step with `K := k`. -/
theorem admBand_of_isLow {S : Core.Setup} {b : Bool} {ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1} {k : ℝ} {i : ℕ}
    (hlow : IsLow S b ε hε k i) :
    AdmBand S b ε hε k i ((bandExps ε i).filter fun j => kapDir S b ε hε j ≤ k) :=
  ⟨Finset.filter_subset _ _,
    (card_le_three_mul_thirdQuantileIndex _).trans (Nat.mul_le_mul_left 3 hlow),
    fun _ hj => (Finset.mem_filter.mp hj).2⟩

theorem tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ε : ℝ => ε ^ p) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **Low-quantile claim** (D9 step 3): for `ε` small, fewer than `N` of the bands `1, …, 3N` are low, in direction
`b`, whenever `(1 + 3d₀/λ)k + (1−λ)^N C_init < 1`. -/
theorem low_count (S : Core.Setup) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hstep : DirStep S lam)
    (hN : Core.NoContractStmt S) {Cinit : ℝ} (hCinit : 0 ≤ Cinit) (hinit : InitProp S Cinit)
    {d₀ k : ℝ} (hd₀ : 0 < d₀) (hk : 0 ≤ k) {N : ℕ}
    (hc : (1 + 3 * d₀ / lam) * k + (1 - lam) ^ N * Cinit < 1) (b : Bool) :
    ∃ ε₃ : ℝ, 0 < ε₃ ∧ ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₃ →
      ((Finset.range (3 * N)).filter (IsLow S b ε hε k)).card < N := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, h₀, hh₀⟩ := SupercriticalLQGUniqueness.exists_normalizedGFF
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (1 + 3 * d₀ / lam) * k + (1 - lam) ^ N * Cinit := ⟨_, rfl⟩
  rw [← hc_def] at hc
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ → ℝ, ρ = fun ε => if 0 < ε then 513 * ε ^ Iteration.bandLower (3 * N) else 1 :=
    ⟨_, rfl⟩
  have hs : 0 < Iteration.bandLower (3 * N) := by
    unfold Iteration.bandLower Iteration.bandUpper
    positivity
  have hρpos : ∀ ε, 0 < ρ ε := by
    intro ε
    rw [hρ_def]
    dsimp only
    split_ifs with hε
    · exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hε _)
    · exact one_pos
  have hρlim : Tendsto ρ (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => 513 * ε ^ Iteration.bandLower (3 * N)) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_rpow_nhdsGT_zero hs).const_mul 513
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp [hρ_def, show (0 : ℝ) < ε from hε]
  obtain ⟨R, θ, hR, hθ, hev⟩ := hN P₀ h₀ hh₀ c hc ρ hρpos hρlim
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, Hinit⟩ := hinit R hR
  obtain ⟨β, c₁, ε₁, hβ, hc₁, hε₁, Hchain⟩ :=
    chain_rate S hlam hlam1 hstep hd₀ hR (K := k) hk hCinit (3 * N)
  have hrate : Tendsto (fun ε : ℝ => c₀ * ε ^ p₀ + c₁ * ε ^ β) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_rpow_nhdsGT_zero hp₀).const_mul c₀).add
      ((tendsto_rpow_nhdsGT_zero hβ).const_mul c₁)
  have hev2 := hev.and ((hrate.eventually (gt_mem_nhds hθ)).and
    (mem_of_superset (Ioo_mem_nhdsGT (lt_min hε₀ hε₁)) fun x hx => hx.2))
  obtain ⟨δ, hδ, hδsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev2
  obtain ⟨ε, hε, hεδ, hNcard⟩ := hcon δ hδ
  obtain ⟨hθle, hlt, hεε⟩ := hδsub ⟨hε.1, hεδ⟩
  have hεε : ε < min ε₀ ε₁ := hεε
  obtain ⟨G, hG⟩ : ∃ G : Finset ℕ, G = (Finset.range (3 * N)).filter (IsLow S b ε hε k) := ⟨_, rfl⟩
  rw [← hG] at hNcard
  have hchain := Hchain P₀ h₀ hh₀ ε hε (lt_of_lt_of_le hεε (min_le_right _ _)) b G
    (fun i => (bandExps ε i).filter fun j => kapDir S b ε hε j ≤ k)
    (by rw [hG]; exact Finset.filter_subset _ _)
    (fun i hi => by rw [hG] at hi; exact admBand_of_isLow (Finset.mem_filter.mp hi).2)
  have hinit' := Hinit P₀ h₀ hh₀ ε hε (lt_of_lt_of_le hεε (min_le_left _ _))
  have hiter : iterF k lam d₀ G.card Cinit ≤ c := by
    rw [hc_def]
    exact iterF_le hlam hlam1 hd₀.le hk hCinit hNcard
  have hρε : ρ ε = 513 * ε ^ Iteration.bandLower (3 * N) := by
    simp [hρ_def, hε.1]
  have hsub : {ω | ¬ compDir S b R ε hε (h₀ ω) c (ρ ε)} ⊆
      {ω | ¬ (compDir S true R ε hε (h₀ ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          compDir S false R ε hε (h₀ ω) Cinit (513 * ε ^ Iteration.bandLower 0))} ∪
        {ω | compDir S b R ε hε (h₀ ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          ¬ compDir S b R ε hε (h₀ ω) (iterF k lam d₀ G.card Cinit)
            (513 * ε ^ Iteration.bandLower (3 * N))} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    by_cases hA : compDir S b R ε hε (h₀ ω) Cinit (513 * ε ^ Iteration.bandLower 0)
    · refine Or.inr ⟨hA, fun hfin => hω ?_⟩
      rw [hρε]
      exact compDir_mono hiter le_rfl hfin
    · refine Or.inl fun hboth => hA ?_
      cases b
      · exact hboth.2
      · exact hboth.1
  have hpos₀ : 0 ≤ c₀ * ε ^ p₀ := mul_nonneg hc₀.le (Real.rpow_pos_of_pos hε.1 _).le
  have hpos₁ : 0 ≤ c₁ * ε ^ β := mul_nonneg hc₁.le (Real.rpow_pos_of_pos hε.1 _).le
  have hbound : P₀ {ω | ¬ compDir S b R ε hε (h₀ ω) c (ρ ε)} ≤
      ENNReal.ofReal (c₀ * ε ^ p₀ + c₁ * ε ^ β) := by
    calc P₀ {ω | ¬ compDir S b R ε hε (h₀ ω) c (ρ ε)}
        ≤ P₀ ({ω | ¬ (compDir S true R ε hε (h₀ ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
              compDir S false R ε hε (h₀ ω) Cinit (513 * ε ^ Iteration.bandLower 0))} ∪
            {ω | compDir S b R ε hε (h₀ ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
              ¬ compDir S b R ε hε (h₀ ω) (iterF k lam d₀ G.card Cinit)
                (513 * ε ^ Iteration.bandLower (3 * N))}) := measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (c₀ * ε ^ p₀) + ENNReal.ofReal (c₁ * ε ^ β) := add_le_add hinit' hchain
      _ = ENNReal.ofReal (c₀ * ε ^ p₀ + c₁ * ε ^ β) := (ENNReal.ofReal_add hpos₀ hpos₁).symm
  have hθ' : ENNReal.ofReal θ ≤ P₀ {ω | ¬ compDir S b R ε hε (h₀ ω) c (ρ ε)} := by
    cases b
    · exact (hθle hε).2
    · exact (hθle hε).1
  have hfin := hθ'.trans hbound
  rw [ENNReal.ofReal_le_ofReal_iff (add_nonneg hpos₀ hpos₁)] at hfin
  have hlt' : c₀ * ε ^ p₀ + c₁ * ε ^ β < θ := hlt
  linarith

end SupercriticalLFPPAS.Proposition51
