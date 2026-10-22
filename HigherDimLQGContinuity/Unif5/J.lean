import HigherDimLQGContinuity.Unif5.Recursion
import HigherDimLQGMetric.DGZ.BadBoxJ

/-!
# Uniform DGZ Lemma 5.9: the events `𝒥₁` and `𝒥₂′` are likely (packet U2)

Blueprint Part D, `d:lem-u57`(c); NA3 §2.5, §2.15 row 13; [8]-bp `r2:lem:59`. Port of
`HigherDimLQGMetric.DGZ.prob_J1_compl_le` and `DGZ.prob_J_compl_le` (`DGZ/BadBoxJ.lean`, MA7 D-5.5–5.9, G9).

The top level is `m = dgzLevel λ K n` for the uniform `λ`.

* `prob_J2'_compl_le_unif` (`𝒥₂′`, `ξ`-free): `P[(𝒥₂′)ᶜ] ≤ C 2^{-n}`. The fixed-`Q` lemma `DGZ.prob_J2'_compl_le`
  involves `Q` only through `λ = dgzLambda d Q`; at `Q = √(2(d + 2α))` this is `α/(4(α + d))`
  (`u2_dgzLambda_sqrt_eq`), so it is reused verbatim.
* `prob_J1_compl_le_unif_gen` / `prob_J1_compl_le_unif` (`𝒥₁`): `P[𝒥₁ᶜ] ≤ C 2^{-αn/2}`, from the uniform Lemma 5.8
  (`q_le_unif_gen`) and the count of `a_m`-boxes in `B₂(0)` (`DGZ.BadBox.mem_cube_of_obox_subset_two`), with
  `(d + α)(1 - 2λ) = d + α/2` (`u2_add_mul_one_sub_two_mul_lambda`) and `(1 - 2λ)n ≤ a_m`
  (`DGZ.BadBox.dgzLevel_facts`).
* `prob_J_compl_le_unif_gen` / `prob_J_compl_le_unif` (**target**, Lemma 5.9): `P[(𝒥₁ ∩ 𝒥₂′)ᶜ] ≤ C 2^{-n/C}`.

As in `Recursion.lean`, the general forms take `α, λ = α/(4(α+d)), β ≥ d + 3α/2, Q̄ > √(2β), ν > 0` over the `ξ` with
`UHyp d κ b μ ξ` and `ξQ(ξ) - ξQ̄ ≥ ν`; the targets use the constants of (A.7). All constants are independent of `ξ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-! ## `𝒥₂′` -/

/-- **`𝒥₂′` is likely for the sequence `dgzSeq λ K`, `λ = α/(4(α + d))`** (`d:lem-u57`(c); `𝒥₂′` is `ξ`-free): for
`α > 0` there is `K₀` such that for every `K ≥ K₀` there is `C > 0` with `P[(𝒥₂′)ᶜ] ≤ C 2^{-n}` for every dyadic
realization and all parameters with `p.K = K`, `a = dgzSeq λ K` (`m = dgzLevel λ K n`). This is
`DGZ.prob_J2'_compl_le` at the exponent `√(2(d + 2α))`. -/
theorem prob_J2'_compl_le_unif {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {α lam : ℝ} (hα : 0 < α)
    (hlam : lam = α / (4 * (α + d))) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
        ∀ p : NiceParams, p.K = K → p.a = dgzSeq lam K →
          P {ω | ¬ EventJ2' p (fun q z => H q z ω) (dgzLevel lam K p.n)} ≤
            ENNReal.ofReal (C * (2 : ℝ) ^ (-(p.n : ℝ))) := by
  subst hlam
  rw [← u2_dgzLambda_sqrt_eq (d := d) hα.le]
  exact prob_J2'_compl_le hκ (u2_sqrt_lt_sqrt hα)

/-! ## `𝒥₁` -/

/-- **`𝒥₁` is likely, general constants** (port of `DGZ.prob_J1_compl_le`). Let `d ≥ 2`, `κ` admissible with support
radius `ρ`, `b, μ > 0`, `R ≥ 2ρ + 10`, `α > 0`, `λ = α/(4(α + d))`, `β ≥ d + 3α/2`, `Q̄ > √(2β)` and `ν > 0`. For
every `θ > 0` with `θ(3 + λ) ≤ νλ/8` there is `K₀` such that for every `K ≥ K₀` there is `C > 0` such that for every
`ε > 0` there is `L₀` with `P[𝒥₁ᶜ] ≤ C 2^{-αn/2}` for every `ξ` with `UHyp d κ b μ ξ` and `ξQ(ξ) - ξQ̄ ≥ ν`, every
dyadic realization, the parameters with these `θ, ε, R, K`, `L ≥ L₀`, `a = dgzSeq λ K`, and all `n, k`
(`m = dgzLevel λ K n`). -/
theorem prob_J1_compl_le_unif_gen (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ}
    (hR : 2 * ρ + 10 ≤ (R : ℝ)) {α lam β Qb ν : ℝ} (hα : 0 < α) (hlam : lam = α / (4 * (α + d)))
    (hβ : d + 3 * α / 2 ≤ β) (hβQ : √(2 * β) < Qb) (hν : 0 < ν) :
    ∀ θ : ℝ, 0 < θ → θ * (3 + lam) ≤ ν * lam / 8 → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0,
      ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ν ≤ ξ * distExp d ξ - ξ * Qb →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
          ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.ε = ε → p.R = R →
            p.K = K → L₀ ≤ p.L → p.a = dgzSeq lam K →
              P {ω | ¬ EventJ1 p (fun q z => H q z ω) (dgzLevel lam K p.n)} ≤
                ENNReal.ofReal (C * (2 : ℝ) ^ (-(α * p.n / 2))) := by
  intro θ hθ hθν
  have hlam0 : 0 < lam := by rw [hlam]; exact u0_lambda_pos hα
  have hlam4 : lam ≤ 1 / 4 := by rw [hlam]; exact u2_lambda_le_quarter hα
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- `(d + α)(1 - 2λ) = d + α/2`
  have hkey : ((d : ℝ) + α) * (1 - 2 * lam) = d + α / 2 := by
    rw [hlam]
    exact u2_add_mul_one_sub_two_mul_lambda hα
  obtain ⟨K₀, hK₀⟩ := q_le_unif_gen hd hκ hb hμ hρ hR hα hlam hβ hβQ hν θ hθ hθν
  refine ⟨max K₀ 1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := (le_max_right _ _).trans hK
  obtain ⟨n₀, hn₀⟩ := BadBox.dgzLevel_facts hlam0 hlam4 hK1
  refine ⟨4 ^ d + (2 : ℝ) ^ (α * n₀ / 2), by positivity, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hK₀ K ((le_max_left _ _).trans hK) ε hε
  refine ⟨L₀, fun ξ hξh hνξ Ω _ P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha => ?_⟩
  have := hH.whiteNoise.isProbabilityMeasure
  rcases lt_or_ge p.n n₀ with hn | hn
  · -- small `n`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (α * n₀ / 2) * (2 : ℝ) ^ (-(α * p.n / 2)) := by
      rw [← Real.rpow_add two_pos]
      apply Real.one_le_rpow one_le_two
      have : (p.n : ℝ) ≤ n₀ := by exact_mod_cast hn.le
      nlinarith
    have h2 : 0 ≤ (4 : ℝ) ^ d * (2 : ℝ) ^ (-(α * p.n / 2)) := by positivity
    nlinarith
  · obtain ⟨hm1, hmn, hlow⟩ := hn₀ p.n hn
    set m := dgzLevel lam K p.n with hm
    have hamn : p.a m ≤ p.n := by rw [ha]; exact hmn
    have hlow' : (1 - 2 * lam) * p.n ≤ p.a m := by rw [ha]; exact hlow
    -- the union bound
    have hset : {ω | ¬ EventJ1 p (fun q z => H q z ω) m} =
        {ω | ∃ u : Zd d, obox (latPt (p.s m) u) (p.s m) ⊆ obox (0 : Rd d) 2 ∧
          ¬ NiceBox p (fun q z => H q z ω) m u} := by
      ext ω
      simp only [mem_ofPred_eq, EventJ1, not_forall, exists_prop]
    rw [hset]
    refine (BadBox.measure_exists_le_card_mul P (BadBox.cube 0 (2 ^ (p.n - p.a m + 1) - 1)) _ _
      (fun u hu => BadBox.mem_cube_of_obox_subset_two p m u hu)
      (b := ENNReal.ofReal ((2 : ℝ) ^ (-(α * p.a m)))) fun u _ =>
        hL₀ ξ hξh hνξ Ω P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha m hm1 hamn u).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [BadBox.card_cube]
    -- `(2N - 1)^d 2^{-α a_m} ≤ 4^d 2^{-αn/2}`
    set e : ℕ := p.n - p.a m with he
    have hcard : (((2 * (2 ^ (e + 1) - 1) + 1) ^ d : ℕ) : ℝ) ≤ ((2 : ℝ) ^ ((e : ℝ) + 2)) ^ d := by
      have h1 : 2 * (2 ^ (e + 1) - 1) + 1 ≤ 2 ^ (e + 2) := by
        have : 1 ≤ 2 ^ (e + 1) := Nat.one_le_two_pow
        rw [pow_succ 2 (e + 1)]
        omega
      have h2 : ((2 * (2 ^ (e + 1) - 1) + 1) ^ d : ℕ) ≤ (2 ^ (e + 2)) ^ d :=
        Nat.pow_le_pow_left h1 d
      have h3 : (((2 ^ (e + 2)) ^ d : ℕ) : ℝ) = ((2 : ℝ) ^ ((e : ℝ) + 2)) ^ d := by
        push_cast
        rw [← Real.rpow_natCast 2 (e + 2)]
        push_cast
        rfl
      rw [← h3]
      exact_mod_cast h2
    have he' : (e : ℝ) = p.n - p.a m := by rw [he, Nat.cast_sub hamn]
    calc (((2 * (2 ^ (e + 1) - 1) + 1) ^ d : ℕ) : ℝ) * (2 : ℝ) ^ (-(α * p.a m))
        ≤ ((2 : ℝ) ^ ((e : ℝ) + 2)) ^ d * (2 : ℝ) ^ (-(α * p.a m)) := by gcongr
      _ = (2 : ℝ) ^ ((d : ℝ) * ((e : ℝ) + 2) + -(α * p.a m)) := by
          rw [BadBox.two_rpow_pow, ← Real.rpow_add two_pos]
      _ ≤ (2 : ℝ) ^ (2 * (d : ℝ) + -(α * p.n / 2)) := by
          apply Real.rpow_le_rpow_of_exponent_le one_le_two
          rw [he']
          have h1 : ((d : ℝ) + α) * ((1 - 2 * lam) * p.n) ≤ ((d : ℝ) + α) * p.a m :=
            mul_le_mul_of_nonneg_left hlow' (by positivity)
          rw [← mul_assoc, hkey] at h1
          nlinarith
      _ = 4 ^ d * (2 : ℝ) ^ (-(α * p.n / 2)) := by
          rw [Real.rpow_add two_pos]
          congr 1
          rw [show (2 : ℝ) * d = ((2 * d : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
            pow_mul]
          norm_num
      _ ≤ (4 ^ d + (2 : ℝ) ^ (α * n₀ / 2)) * (2 : ℝ) ^ (-(α * p.n / 2)) := by
          gcongr
          have : (0 : ℝ) ≤ (2 : ℝ) ^ (α * n₀ / 2) := by positivity
          linarith

/-- **`𝒥₁` is likely, uniformly** (port of `DGZ.prob_J1_compl_le`; blueprint `d:lem-u57`(c)). Let `d ≥ 2`, `κ`
admissible with support radius `ρ`, `b, μ > 0` and `R ≥ 2ρ + 10`; `α = uAlpha`, `λ = uLambda`. For every
`θ ∈ (0, uTheta]` there is `K₀` such that for every `K ≥ K₀` there is `C > 0` such that for every `ε > 0` there is
`L₀` with `P[𝒥₁ᶜ] ≤ C 2^{-αn/2}` for every `ξ ∈ S(b, μ)`, every dyadic realization, the uniform parameters with these
`θ, ε, R, K` and `L ≥ L₀`, and all `n, k` (`m = dgzLevel λ K n`). -/
theorem prob_J1_compl_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ}
    (hR : 2 * ρ + 10 ≤ (R : ℝ)) :
    ∀ θ : ℝ, 0 < θ → θ ≤ uTheta d b μ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0,
      ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
          ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.ε = ε → p.R = R →
            p.K = K → L₀ ≤ p.L → p.a = dgzSeq (uLambda d b μ) K →
              P {ω | ¬ EventJ1 p (fun q z => H q z ω) (dgzLevel (uLambda d b μ) K p.n)} ≤
                ENNReal.ofReal (C * (2 : ℝ) ^ (-(uAlpha d b μ * p.n / 2))) := by
  intro θ hθ hθθ
  have hα := uAlpha_pos (d := d) hb hμ
  have hβ : (d : ℝ) + 3 * uAlpha d b μ / 2 ≤ uBeta d b μ := by
    rw [uBeta_eq]
    linarith
  obtain ⟨K₀, hK₀⟩ := prob_J1_compl_le_unif_gen hd hκ hb hμ hρ hR hα rfl hβ
    (sqrt_two_uBeta_lt_uQbar hb hμ) (uNu_pos hb hμ) θ hθ (u2_theta_mul_le hb hμ hθθ)
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨C, hC, hCε⟩ := hK₀ K hK
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hCε ε hε
  exact ⟨L₀, fun ξ hξh => hL₀ ξ hξh (hξh.uNu_le hμ)⟩

/-! ## Lemma 5.9 -/

/-- **DGZ Lemma 5.9, general constants** (port of `DGZ.prob_J_compl_le`). Under the hypotheses of
`prob_J1_compl_le_unif_gen`: for every `θ > 0` with `θ(3 + λ) ≤ νλ/8` there is `K₀` such that for every `K ≥ K₀`
there is `C > 0` such that for every `ε > 0` there is `L₀` with `P[(𝒥₁ ∩ 𝒥₂′)ᶜ] ≤ C 2^{-n/C}`. -/
theorem prob_J_compl_le_unif_gen (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ}
    (hR : 2 * ρ + 10 ≤ (R : ℝ)) {α lam β Qb ν : ℝ} (hα : 0 < α) (hlam : lam = α / (4 * (α + d)))
    (hβ : d + 3 * α / 2 ≤ β) (hβQ : √(2 * β) < Qb) (hν : 0 < ν) :
    ∀ θ : ℝ, 0 < θ → θ * (3 + lam) ≤ ν * lam / 8 → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0,
      ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ν ≤ ξ * distExp d ξ - ξ * Qb →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
          ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.ε = ε → p.R = R →
            p.K = K → L₀ ≤ p.L → p.a = dgzSeq lam K →
              P {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel lam K p.n) ∧
                EventJ2' p (fun q z => H q z ω) (dgzLevel lam K p.n))} ≤
                ENNReal.ofReal (C * (2 : ℝ) ^ (-(p.n : ℝ) / C)) := by
  intro θ hθ hθν
  obtain ⟨K₁, hJ1⟩ := prob_J1_compl_le_unif_gen hd hκ hb hμ hρ hR hα hlam hβ hβQ hν θ hθ hθν
  obtain ⟨K₂, hJ2⟩ := prob_J2'_compl_le_unif (d := d) hκ hα hlam
  refine ⟨max K₁ K₂, fun K hK => ?_⟩
  obtain ⟨C₁, hC₁, hJ1K⟩ := hJ1 K ((le_max_left _ _).trans hK)
  obtain ⟨C₂, hC₂, hJ2K⟩ := hJ2 K ((le_max_right _ _).trans hK)
  set C : ℝ := max (C₁ + C₂) (max (2 / α) 1) with hC
  have hC1 : 1 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC0 : 0 < C := by linarith
  have hCα : 2 / α ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCC : C₁ + C₂ ≤ C := le_max_left _ _
  refine ⟨C, hC0, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hJ1K ε hε
  refine ⟨L₀, fun ξ hξh hνξ Ω _ P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha => ?_⟩
  have h1 := hL₀ ξ hξh hνξ Ω P W H hH p hpξ hpQ hpθ hpε hpR hpK hL ha
  have h2 := hJ2K Ω P W H hH p hpK ha
  have hsub : {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel lam K p.n) ∧
      EventJ2' p (fun q z => H q z ω) (dgzLevel lam K p.n))} ⊆
      {ω | ¬ EventJ1 p (fun q z => H q z ω) (dgzLevel lam K p.n)} ∪
        {ω | ¬ EventJ2' p (fun q z => H q z ω) (dgzLevel lam K p.n)} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, not_and_or] at hω ⊢
    exact hω
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hr1 : (2 : ℝ) ^ (-(α * p.n / 2)) ≤ (2 : ℝ) ^ (-(p.n : ℝ) / C) := by
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    have h3 : (p.n : ℝ) / C ≤ α * p.n / 2 := by
      rw [div_le_iff₀ hC0]
      have h4 : 2 ≤ α * C := by
        rw [div_le_iff₀ hα] at hCα
        linarith
      nlinarith
    rw [neg_div]
    linarith
  have hr2 : (2 : ℝ) ^ (-(p.n : ℝ)) ≤ (2 : ℝ) ^ (-(p.n : ℝ) / C) := by
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hC0]
    nlinarith
  calc _ ≤ _ := measure_mono hsub
    _ ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(α * p.n / 2))) +
        ENNReal.ofReal (C₂ * (2 : ℝ) ^ (-(p.n : ℝ))) :=
        (measure_union_le _ _).trans (add_le_add h1 h2)
    _ = ENNReal.ofReal (C₁ * (2 : ℝ) ^ (-(α * p.n / 2)) + C₂ * (2 : ℝ) ^ (-(p.n : ℝ))) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(p.n : ℝ) / C)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hy : (0 : ℝ) ≤ (2 : ℝ) ^ (-(p.n : ℝ) / C) := by positivity
        calc C₁ * (2 : ℝ) ^ (-(α * p.n / 2)) + C₂ * (2 : ℝ) ^ (-(p.n : ℝ))
            ≤ C₁ * (2 : ℝ) ^ (-(p.n : ℝ) / C) + C₂ * (2 : ℝ) ^ (-(p.n : ℝ) / C) := by
              gcongr
          _ = (C₁ + C₂) * (2 : ℝ) ^ (-(p.n : ℝ) / C) := by ring
          _ ≤ C * (2 : ℝ) ^ (-(p.n : ℝ) / C) := mul_le_mul_of_nonneg_right hCC hy

/-- **Uniform DGZ Lemma 5.9** (target `prob_J_compl_le_unif`; blueprint `d:lem-u57`(c); port of
`DGZ.prob_J_compl_le`). Let `d ≥ 2`, `κ` admissible with support radius `ρ`, `b, μ > 0` and `R ≥ 2ρ + 10`;
`λ = uLambda`. For every `θ ∈ (0, uTheta]` there is `K₀` such that for every `K ≥ K₀` there is `C > 0` such that for
every `ε > 0` there is `L₀` (all depending only on `d, κ, b, μ, R` and the displayed parameters) with
`P[(𝒥₁ ∩ 𝒥₂′)ᶜ] ≤ C 2^{-n/C}` for every `ξ ∈ S(b, μ)`, every dyadic realization, the uniform parameters (`p.ξ = ξ`,
`p.Q = Q(ξ)`, `p.θ = θ`, `p.ε = ε`, `p.R = R`, `p.K = K`, `L ≥ L₀`, `a = dgzSeq λ K`) and all `n, k`, with
`m = dgzLevel λ K n`. -/
theorem prob_J_compl_le_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {R : ℕ}
    (hR : 2 * ρ + 10 ≤ (R : ℝ)) :
    ∀ θ : ℝ, 0 < θ → θ ≤ uTheta d b μ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∃ C > 0,
      ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
          (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H →
          ∀ p : NiceParams, p.ξ = ξ → p.Q = distExp d ξ → p.θ = θ → p.ε = ε → p.R = R →
            p.K = K → L₀ ≤ p.L → p.a = dgzSeq (uLambda d b μ) K →
              P {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel (uLambda d b μ) K p.n) ∧
                EventJ2' p (fun q z => H q z ω) (dgzLevel (uLambda d b μ) K p.n))} ≤
                ENNReal.ofReal (C * (2 : ℝ) ^ (-(p.n : ℝ) / C)) := by
  intro θ hθ hθθ
  have hα := uAlpha_pos (d := d) hb hμ
  have hβ : (d : ℝ) + 3 * uAlpha d b μ / 2 ≤ uBeta d b μ := by
    rw [uBeta_eq]
    linarith
  obtain ⟨K₀, hK₀⟩ := prob_J_compl_le_unif_gen hd hκ hb hμ hρ hR hα rfl hβ
    (sqrt_two_uBeta_lt_uQbar hb hμ) (uNu_pos hb hμ) θ hθ (u2_theta_mul_le hb hμ hθθ)
  refine ⟨K₀, fun K hK => ?_⟩
  obtain ⟨C, hC, hCε⟩ := hK₀ K hK
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hCε ε hε
  exact ⟨L₀, fun ξ hξh => hL₀ ξ hξh (hξh.uNu_le hμ)⟩

end HigherDimLQGContinuity
