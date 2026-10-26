import SupercriticalLFPPAS.Proposition51.LowQuantile

/-!
# Proposition 5.1 (packet P51)

`prop51_of : ContractionStmt S → LocCompareStmt S → NoContractStmt S → Prop51Stmt S` (paper Proposition 5.1, §5,
l. 505–581; SB2 §2.6, Details D8–D9 with M9; SB3 §2).

Constants (D9 step 1): `λ` from `ContractionStmt`; `C_init` the `C₀` of (2.7)–(2.8) at `ζ = 1/2` (independent of `U`);
`v := min(1, u/8)`, `k := 1/(1+v)`, `d₀ := λv/6` and `N₀` from `Iteration.exists_iteration_constants`, `N := N₀ + 1`;
bands `t_j = 8^{-j}`, `s_j = t_j/4`, `j = 1, …, 3N`.

Final iteration (D9 steps 5–6): for `ε` below the thresholds of `low_count` (both directions), at least `N + 2` of the
`3N` bands have both quantiles `> k`; in each of them at least `⌈n/3⌉` radii satisfy `k < κ_ε < k⁻¹` (D8,
`Iteration.middle_card_of_two_inverse_quantiles`), so the chain (`chain_rate`, `K := k⁻¹ = 1 + v`) contracts in these bands in
both directions; the constant is `≤ (1 + 3d₀/λ)(1+v) + (1−λ)^N C_init < 1 + u` and the radius `513 ε^{s_{3N}}`. The
failure probability is at most `c₀ε^{p₀} + 2c₁ε^β ≤ (c₀ + 2c₁) ε^{min(p₀,β)}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Proposition51

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric IsNormalizedWholePlaneGFF)

theorem bandLower_pos (i : ℕ) : 0 < Iteration.bandLower i := by
  unfold Iteration.bandLower Iteration.bandUpper
  positivity

/-- At least `N` of the `3N` bands are low in neither direction when fewer than `N` are low in each. -/
theorem card_good_bands {N : ℕ} (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q]
    (hp : ((Finset.range (3 * N)).filter p).card < N) (hq : ((Finset.range (3 * N)).filter q).card < N) :
    N ≤ ((Finset.range (3 * N)).filter fun i => ¬ p i ∧ ¬ q i).card := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.range (3 * N)) (fun i => ¬ p i ∧ ¬ q i)
  have hsub : ((Finset.range (3 * N)).filter fun i => ¬ (¬ p i ∧ ¬ q i)) ⊆
      (Finset.range (3 * N)).filter p ∪ (Finset.range (3 * N)).filter q := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hpi : p i
    · exact Or.inl ⟨hi.1, hpi⟩
    · exact Or.inr ⟨hi.1, by_contra fun hqi => hi.2 ⟨hpi, hqi⟩⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_range] at hsum
  omega

/-- In a band low in neither direction, the radii with `k < κ_ε < k⁻¹` are admissible for the contraction step with
`K := k⁻¹`, in both directions. -/
theorem admBand_middle {S : Core.Setup} {ε : ℝ} {hε : ε ∈ Ioo (0 : ℝ) 1} {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    {i : ℕ} (hlow : ¬ IsLow S true ε hε k i) (hlow' : ¬ IsLow S false ε hε k i) (b : Bool) :
    AdmBand S b ε hε k⁻¹ i
      ((bandExps ε i).filter fun j => k < kapDir S true ε hε j ∧ kapDir S true ε hε j < k⁻¹) := by
  have hκpos : ∀ j ∈ bandExps ε i, 0 < kapDir S true ε hε j := fun j _ => kappaS_pos S _ _
  have hlo : ((bandExps ε i).filter fun j => kapDir S true ε hε j ≤ k).card <
      Iteration.thirdQuantileIndex (bandExps ε i).card := lt_of_not_ge hlow
  have hhi' : ((bandExps ε i).filter fun j => kapDir S false ε hε j ≤ k).card <
      Iteration.thirdQuantileIndex (bandExps ε i).card := lt_of_not_ge hlow'
  have e : ((bandExps ε i).filter fun j => kapDir S false ε hε j ≤ k) =
      (bandExps ε i).filter fun j => (kapDir S true ε hε j)⁻¹ ≤ k :=
    Finset.filter_congr fun _ _ => Iff.rfl
  rw [e] at hhi'
  have hmid := Iteration.middle_card_of_two_inverse_quantiles (bandExps ε i) (kapDir S true ε hε) hk hk1 hκpos
    hlo hhi'
  refine ⟨Finset.filter_subset _ _, (card_le_three_mul_thirdQuantileIndex _).trans
    (Nat.mul_le_mul_left 3 hmid), fun j hj => ?_⟩
  obtain ⟨-, hkj, hjk⟩ := Finset.mem_filter.mp hj
  cases b
  · have h1 : (kapDir S true ε hε j)⁻¹ < k⁻¹ := inv_strictAnti₀ hk hkj
    exact h1.le
  · exact hjk.le

/-- **Proposition 5.1** (internal form, `Core.Prop51Stmt`) from the contraction step (§4.2), the localized comparison
(2.7)–(2.8) and the no-contraction statement (5.6). -/
theorem prop51_of (S : Core.Setup) (hC : Core.ContractionStmt S) (hL : Core.LocCompareStmt S)
    (hN : Core.NoContractStmt S) : Core.Prop51Stmt S := by
  classical
  intro u R hu hR
  obtain ⟨lam, hlam, hlam1, hstep⟩ := dirStep_of S hC
  obtain ⟨Cinit, hCinit, hinit⟩ := init_of S hL
  obtain ⟨v, d₀, N₀, hv, -, hd₀eq, hTk, hhalf, hupper⟩ :=
    Iteration.exists_iteration_constants hu hlam hlam1 hCinit.le
  have hd₀ : 0 < d₀ := by rw [hd₀eq]; positivity
  obtain ⟨k, hk_def⟩ : ∃ k : ℝ, k = 1 / (1 + v) := ⟨_, rfl⟩
  rw [← hk_def] at hTk hhalf
  have hk : 0 < k := by rw [hk_def]; positivity
  have hk1 : k < 1 := by
    rw [hk_def, div_lt_one (by linarith)]
    linarith
  have hkinv : k⁻¹ = 1 + v := by rw [hk_def, one_div, inv_inv]
  have hpowN : (1 - lam) ^ (N₀ + 1) * Cinit ≤ (1 - lam) ^ N₀ * Cinit :=
    mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by linarith) (by linarith) (Nat.le_succ N₀)) hCinit.le
  have hc : (1 + 3 * d₀ / lam) * k + (1 - lam) ^ (N₀ + 1) * Cinit < 1 := by
    unfold Iteration.contractionFixedPoint at hTk hhalf
    linarith
  obtain ⟨ε₃, hε₃, Hlow⟩ := low_count S hlam hlam1 hstep hN hCinit.le hinit hd₀ hk.le hc true
  obtain ⟨ε₃', hε₃', Hlow'⟩ := low_count S hlam hlam1 hstep hN hCinit.le hinit hd₀ hk.le hc false
  obtain ⟨p₀, c₀, ε₀, hp₀, hc₀, hε₀, Hinit⟩ := hinit R hR
  obtain ⟨β, c₁, ε₁, hβ, hc₁, hε₁, Hchain⟩ :=
    chain_rate S hlam hlam1 hstep hd₀ hR (K := k⁻¹) (inv_pos.mpr hk).le hCinit.le (3 * (N₀ + 1))
  refine ⟨Iteration.bandLower (3 * (N₀ + 1)), min p₀ β, c₀ + 2 * c₁, min (min ε₃ ε₃') (min ε₀ ε₁),
    bandLower_pos _, lt_min hp₀ hβ, by positivity, lt_min (lt_min hε₃ hε₃') (lt_min hε₀ hε₁), ?_⟩
  intro Ω _ P _ h hh ε hε hεε
  have hεa : ε < ε₃ := lt_of_lt_of_le hεε ((min_le_left _ _).trans (min_le_left _ _))
  have hεb : ε < ε₃' := lt_of_lt_of_le hεε ((min_le_left _ _).trans (min_le_right _ _))
  have hε0 : ε < ε₀ := lt_of_lt_of_le hεε ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < ε₁ := lt_of_lt_of_le hεε ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨G, hG⟩ : ∃ G : Finset ℕ, G = (Finset.range (3 * (N₀ + 1))).filter
      (fun i => ¬ IsLow S true ε hε k i ∧ ¬ IsLow S false ε hε k i) := ⟨_, rfl⟩
  have hGcard : N₀ + 1 ≤ G.card := by
    rw [hG]
    exact card_good_bands _ _ (Hlow ε hε hεa) (Hlow' ε hε hεb)
  have hch : ∀ b : Bool, P {ω | compDir S b R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
      ¬ compDir S b R ε hε (h ω) (iterF k⁻¹ lam d₀ G.card Cinit)
        (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1)))} ≤ ENNReal.ofReal (c₁ * ε ^ β) := fun b =>
    Hchain P h hh ε hε hε1 b G
      (fun i => (bandExps ε i).filter fun j => k < kapDir S true ε hε j ∧ kapDir S true ε hε j < k⁻¹)
      (by rw [hG]; exact Finset.filter_subset _ _)
      (fun i hi => by
        rw [hG, Finset.mem_filter] at hi
        exact admBand_middle hk hk1 hi.2.1 hi.2.2 b)
  have hfinal : iterF k⁻¹ lam d₀ G.card Cinit ≤ 1 + u := by
    have h1 := iterF_le hlam hlam1 hd₀.le (inv_pos.mpr hk).le hCinit.le hGcard
    rw [hkinv] at h1 ⊢
    linarith
  have hsub : {ω | ¬ (Core.CompIn (S.D (h ω)) (Core.locMetric S ε hε (h ω)) (ball 0 (R + 2)) R (1 + u)
        (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1))) ∧
      Core.CompIn (Core.locMetric S ε hε (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R (1 + u)
        (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1))))} ⊆
      {ω | ¬ (compDir S true R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          compDir S false R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0))} ∪
        {ω | compDir S true R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          ¬ compDir S true R ε hε (h ω) (iterF k⁻¹ lam d₀ G.card Cinit)
            (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1)))} ∪
        {ω | compDir S false R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          ¬ compDir S false R ε hε (h ω) (iterF k⁻¹ lam d₀ G.card Cinit)
            (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1)))} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    by_cases h1 : compDir S true R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0)
    · by_cases h2 : compDir S false R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0)
      · by_cases hf : compDir S true R ε hε (h ω) (iterF k⁻¹ lam d₀ G.card Cinit)
            (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1)))
        · refine Or.inr ⟨h2, fun hb => hω ?_⟩
          have hF : compDir S true R ε hε (h ω) (1 + u) (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1))) :=
            compDir_mono hfinal le_rfl hf
          have hB : compDir S false R ε hε (h ω) (1 + u) (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1))) :=
            compDir_mono hfinal le_rfl hb
          exact ⟨hF, hB⟩
        · exact Or.inl (Or.inr ⟨h1, hf⟩)
      · exact Or.inl (Or.inl fun hboth => h2 hboth.2)
    · exact Or.inl (Or.inl fun hboth => h1 hboth.1)
  have hpos₀ : 0 ≤ c₀ * ε ^ p₀ := mul_nonneg hc₀.le (Real.rpow_pos_of_pos hε.1 _).le
  have hpos₁ : 0 ≤ c₁ * ε ^ β := mul_nonneg hc₁.le (Real.rpow_pos_of_pos hε.1 _).le
  have hrate : c₀ * ε ^ p₀ + c₁ * ε ^ β + c₁ * ε ^ β ≤ (c₀ + 2 * c₁) * ε ^ min p₀ β := by
    have e1 : ε ^ p₀ ≤ ε ^ min p₀ β := Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_left _ _)
    have e2 : ε ^ β ≤ ε ^ min p₀ β := Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (min_le_right _ _)
    have f1 := mul_le_mul_of_nonneg_left e1 hc₀.le
    have f2 := mul_le_mul_of_nonneg_left e2 hc₁.le
    have e3 : (c₀ + 2 * c₁) * ε ^ min p₀ β = c₀ * ε ^ min p₀ β + 2 * (c₁ * ε ^ min p₀ β) := by ring
    rw [e3]
    linarith
  calc P {ω | ¬ (Core.CompIn (S.D (h ω)) (Core.locMetric S ε hε (h ω)) (ball 0 (R + 2)) R (1 + u)
        (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1))) ∧
      Core.CompIn (Core.locMetric S ε hε (h ω)) (S.D (h ω)) (ball 0 (R + 2)) R (1 + u)
        (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1))))}
      ≤ P ({ω | ¬ (compDir S true R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          compDir S false R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0))} ∪
        {ω | compDir S true R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          ¬ compDir S true R ε hε (h ω) (iterF k⁻¹ lam d₀ G.card Cinit)
            (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1)))} ∪
        {ω | compDir S false R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
          ¬ compDir S false R ε hε (h ω) (iterF k⁻¹ lam d₀ G.card Cinit)
            (513 * ε ^ Iteration.bandLower (3 * (N₀ + 1)))}) := measure_mono hsub
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (c₀ * ε ^ p₀) + ENNReal.ofReal (c₁ * ε ^ β) + ENNReal.ofReal (c₁ * ε ^ β) :=
        add_le_add (add_le_add (Hinit P h hh ε hε hε0) (hch true)) (hch false)
    _ = ENNReal.ofReal (c₀ * ε ^ p₀ + c₁ * ε ^ β + c₁ * ε ^ β) := by
        rw [ENNReal.ofReal_add (add_nonneg hpos₀ hpos₁) hpos₁, ENNReal.ofReal_add hpos₀ hpos₁]
    _ ≤ ENNReal.ofReal ((c₀ + 2 * c₁) * ε ^ min p₀ β) := ENNReal.ofReal_le_ofReal hrate

end SupercriticalLFPPAS.Proposition51
