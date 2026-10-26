import SupercriticalLFPPAS.Proposition51.Basic

/-!
# Proposition 5.1: the iteration through the bands (packet P51)

The iteration of the contraction step (§4.2) through the bands `t_j = 8^{-j}`, `s_j = t_j/4` of Proposition 5.1 (paper
l. 528–581; SB2 §2.6 "Bands", "Uniformity", Details D8–D9).

Lean route (equivalent to choosing `N` bands, but uniform without a pigeonhole over band sets): the chain runs through
*all* bands `j = 1, …, n` in increasing order; the state after band `j` is the comparison with radius `513 ε^{s_j}`
(`s₀ = bandLower 0 = 1/4`). At a band `j ∈ G` (an admissible set of radii is given) one contraction step is made with
the prior radius `513 ε^{s_{j-1}}` (`t_j < s_{j-1}`); at a band `j ∉ G` the radius is simply enlarged to `513 ε^{s_j}`
(no probability cost). After band `i` the constant is `F_K^{g}(C_init)`, `g = #(G ∩ [1, i])`; the step constants of
`Core.ContractionStmt` depend only on `(g, i)` in a finite set, so one exponent, constant and threshold serve every `G`
(`uniform_rate`). The final constant `F_K^{#G}(C_init) ≤ (1 + 3d₀/λ)K + (1−λ)^N C_init` for `#G ≥ N` (D8, `iterF_le`).

Main result: `chain_rate`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Proposition51

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric IsNormalizedWholePlaneGFF)

/-! ### Iterated contraction factor -/

/-- `F_K^{g}(C)`: `g` contraction steps with the same ratio bound `K`. -/
def iterF (K lam d₀ : ℝ) (g : ℕ) (C : ℝ) : ℝ :=
  (fun C => Iteration.contractionFactor C K lam d₀)^[g] C

theorem iterF_zero (K lam d₀ C : ℝ) : iterF K lam d₀ 0 C = C := rfl

theorem iterF_succ (K lam d₀ : ℝ) (g : ℕ) (C : ℝ) :
    iterF K lam d₀ (g + 1) C = Iteration.contractionFactor (iterF K lam d₀ g C) K lam d₀ :=
  Function.iterate_succ_apply' _ _ _

theorem contractionFactor_nonneg {C K lam d₀ : ℝ} (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hd₀ : 0 ≤ d₀) (hC : 0 ≤ C) : 0 ≤ Iteration.contractionFactor C K lam d₀ := by
  unfold Iteration.contractionFactor
  have h1 : 0 ≤ 1 - lam := by linarith
  have h2 : 0 ≤ max C K := le_max_of_le_left hC
  have h3 : 0 ≤ lam + 3 * d₀ := by positivity
  exact add_nonneg (mul_nonneg h1 h2) (mul_nonneg h3 hK)

theorem iterF_nonneg {K lam d₀ C : ℝ} (hK : 0 ≤ K) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hd₀ : 0 ≤ d₀)
    (hC : 0 ≤ C) (g : ℕ) : 0 ≤ iterF K lam d₀ g C := by
  induction g with
  | zero => exact hC
  | succ g ih =>
      rw [iterF_succ]
      exact contractionFactor_nonneg hK hlam hlam1 hd₀ ih

/-- (5.5) for `g ≥ N` steps (D8): `F_K^{g}(C) ≤ (1 + 3d₀/λ)K + (1−λ)^N C`. -/
theorem iterF_le {K lam d₀ C : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hd₀ : 0 ≤ d₀) (hK : 0 ≤ K)
    (hC : 0 ≤ C) {N g : ℕ} (hNg : N ≤ g) :
    iterF K lam d₀ g C ≤ (1 + 3 * d₀ / lam) * K + (1 - lam) ^ N * C := by
  have h := Iteration.contraction_recursion_bound (N := g) hlam hlam1 hd₀ hK hC
    (C := fun j => iterF K lam d₀ j C) (K := fun _ => K) rfl (fun j _ => iterF_succ K lam d₀ j C)
    (fun _ _ => hK) (fun _ _ => le_rfl)
  have hp : (1 - lam) ^ g ≤ (1 - lam) ^ N := pow_le_pow_of_le_one (by linarith) (by linarith) hNg
  have := mul_le_mul_of_nonneg_right hp hC
  linarith

/-! ### Bands -/

/-- The band facts used by one step at band `i + 1` with prior band `i`: `0 < s_{i+1}`, `4 s_{i+1} ≤ t_{i+1}`,
`t_{i+1} < s_i < 1`, `s_{i+1} ≤ s_i`. -/
theorem band_step (i : ℕ) :
    0 < Iteration.bandLower (i + 1) ∧ 4 * Iteration.bandLower (i + 1) ≤ Iteration.bandUpper (i + 1) ∧
      Iteration.bandUpper (i + 1) < Iteration.bandLower i ∧ Iteration.bandLower i < 1 ∧
      Iteration.bandLower (i + 1) ≤ Iteration.bandLower i := by
  have hp : 0 < (1 / 8 : ℝ) ^ i := pow_pos (by norm_num) i
  have hp1 : (1 / 8 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have e1 : Iteration.bandUpper (i + 1) = (1 / 8 : ℝ) ^ i / 8 := by
    simp only [Iteration.bandUpper, pow_succ]
    ring
  have e2 : Iteration.bandLower (i + 1) = (1 / 8 : ℝ) ^ i / 32 := by
    simp only [Iteration.bandLower, e1]
    ring
  have e3 : Iteration.bandLower i = (1 / 8 : ℝ) ^ i / 4 := rfl
  rw [e1, e2, e3]
  refine ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

/-- The exponents of band `i + 1`: `R_ε(s_{i+1}, t_{i+1})`. -/
def bandExps (ε : ℝ) (i : ℕ) : Finset ℤ :=
  Iteration.radiusExponents ε (Iteration.bandLower (i + 1)) (Iteration.bandUpper (i + 1))

/-- An admissible radius set `T` for band `i + 1`, direction `b` and ratio bound `K` (the hypotheses on `S_ε` in
`Core.ContractionStmt`). -/
def AdmBand (S : Core.Setup) (b : Bool) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (K : ℝ) (i : ℕ) (T : Finset ℤ) : Prop :=
  T ⊆ bandExps ε i ∧ (bandExps ε i).card ≤ 3 * T.card ∧ ∀ j ∈ T, kapDir S b ε hε j ≤ K

/-! ### The chain -/

/-- **Iteration through the bands.** For fixed `λ, d₀, R, K, C_init` and `n` bands there are `β, c₁, ε₁` such that,
uniformly over normalized fields, `ε < ε₁`, directions `b`, sets `G ⊆ {0, …, n−1}` of (0-based) bands and admissible
radius sets in the bands of `G`: the probability that the comparison `(C_init, 513 ε^{s₀})` holds but
`(F_K^{#G}(C_init), 513 ε^{s_n})` fails is at most `c₁ ε^β`. -/
theorem chain_rate (S : Core.Setup) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hstep : DirStep S lam)
    {d₀ : ℝ} (hd₀ : 0 < d₀) {R : ℝ} (hR : 1 ≤ R) {K Cinit : ℝ} (hK : 0 ≤ K) (hCinit : 0 ≤ Cinit) (n : ℕ) :
    ∃ β c₁ ε₁ : ℝ, 0 < β ∧ 0 < c₁ ∧ 0 < ε₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P → ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₁ →
        ∀ (b : Bool) (G : Finset ℕ) (T : ℕ → Finset ℤ), G ⊆ Finset.range n →
          (∀ i ∈ G, AdmBand S b ε hε K i (T i)) →
          P {ω | compDir S b R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
            ¬ compDir S b R ε hε (h ω) (iterF K lam d₀ G.card Cinit) (513 * ε ^ Iteration.bandLower n)} ≤
            ENNReal.ofReal (c₁ * ε ^ β) := by
  classical
  obtain ⟨β, c, e, hβ, hc, he, H⟩ := uniform_rate (Finset.range (n + 1) ×ˢ Finset.range n)
    (fun gi ε x => ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (hε : ε ∈ Ioo (0 : ℝ) 1) (b : Bool)
        (T : Finset ℤ), AdmBand S b ε hε K gi.2 T →
          P {ω | compDir S b R ε hε (h ω) (iterF K lam d₀ gi.1 Cinit) (513 * ε ^ Iteration.bandLower gi.2) ∧
            ¬ compDir S b R ε hε (h ω) (iterF K lam d₀ (gi.1 + 1) Cinit)
              (513 * ε ^ Iteration.bandLower (gi.2 + 1))} ≤ x)
    (fun gi ε x y hxy hx Ω _ P _ h hh hε b T hT => (hx P h hh hε b T hT).trans hxy)
    (fun gi _ => by
      obtain ⟨hs, h4, htt, hto, -⟩ := band_step gi.2
      obtain ⟨β, c₁, ε₁, hβ, hc₁, hε₁, H⟩ := hstep d₀ hd₀ R hR _ _ _ (iterF K lam d₀ gi.1 Cinit) hs h4 htt
        hto (iterF_nonneg hK hlam.le hlam1 hd₀.le hCinit gi.1)
      refine ⟨β, c₁, ε₁, hβ, hc₁, hε₁, fun ε _ _ hεe Ω _ P _ h hh hε b T hT => ?_⟩
      rw [iterF_succ]
      exact H P h hh ε hε hεe T hT.1 hT.2.1 K hK b hT.2.2)
  refine ⟨β, (n + 1) * c, e, hβ, by positivity, he, ?_⟩
  intro Ω _ P _ h hh ε hε hεe b G T hG hT
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ i, g i = ((Finset.range i).filter (· ∈ G)).card := ⟨_, fun _ => rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set Ω, ∀ i, A i =
      {ω | compDir S b R ε hε (h ω) (iterF K lam d₀ (g i) Cinit) (513 * ε ^ Iteration.bandLower i)} :=
    ⟨_, fun _ => rfl⟩
  have hg0 : g 0 = 0 := by simp [hg]
  have hgn : g n = G.card := by
    rw [hg]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun hi => hi.2, fun hi => ⟨Finset.mem_range.mp (hG hi), hi⟩⟩
  have hgsucc : ∀ i, g (i + 1) = if i ∈ G then g i + 1 else g i := by
    intro i
    rw [hg, hg, Finset.range_add_one, Finset.filter_insert]
    split_ifs with hi
    · rw [Finset.card_insert_of_notMem]
      simp
    · rfl
  have hgle : ∀ i, g i ≤ i := fun i => by
    rw [hg]
    exact (Finset.card_filter_le _ _).trans (Finset.card_range i).le
  have hset : {ω | compDir S b R ε hε (h ω) Cinit (513 * ε ^ Iteration.bandLower 0) ∧
      ¬ compDir S b R ε hε (h ω) (iterF K lam d₀ G.card Cinit) (513 * ε ^ Iteration.bandLower n)} =
      A 0 \ A n := by
    rw [hA, hA, hg0, hgn, iterF_zero]
    rfl
  rw [hset]
  refine (measure_sdiff_le_sum P A n).trans ?_
  have hterm : ∀ i ∈ Finset.range n, P (A i \ A (i + 1)) ≤ ENNReal.ofReal (c * ε ^ β) := by
    intro i hi
    by_cases hiG : i ∈ G
    · have e1 : g (i + 1) = g i + 1 := by simp [hgsucc i, hiG]
      have hmem : (g i, i) ∈ Finset.range (n + 1) ×ˢ Finset.range n :=
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_of_le ((hgle i).trans (Finset.mem_range.mp hi).le)), hi⟩
      have h1 := H (g i, i) hmem ε hε.1 hε.2 hεe P h hh hε b (T i) (hT i hiG)
      rw [hA, hA, e1]
      exact h1
    · have e1 : g (i + 1) = g i := by simp [hgsucc i, hiG]
      have hsub : A i ⊆ A (i + 1) := by
        rw [hA, hA, e1]
        intro ω hω
        have hrad : 513 * ε ^ Iteration.bandLower i ≤ 513 * ε ^ Iteration.bandLower (i + 1) := by
          have := Real.rpow_le_rpow_of_exponent_ge hε.1 hε.2.le (band_step i).2.2.2.2
          linarith
        exact compDir_mono le_rfl hrad hω
      rw [Set.sdiff_eq_empty.mpr hsub, measure_empty]
      exact zero_le
  have hcε : 0 ≤ c * ε ^ β := mul_nonneg hc.le (Real.rpow_pos_of_pos hε.1 β).le
  calc ∑ i ∈ Finset.range n, P (A i \ A (i + 1))
      ≤ ∑ _i ∈ Finset.range n, ENNReal.ofReal (c * ε ^ β) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((n : ℝ) * (c * ε ^ β)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((n + 1) * c * ε ^ β) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith

end SupercriticalLFPPAS.Proposition51
