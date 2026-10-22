import HigherDimLQGContinuity.UnifCompare.Prop513
import HigherDimLQGContinuity.UnifCompare.Lemma514
import HigherDimLQGContinuity.Unif5.J

/-!
# Uniform DGZ Proposition 5.1, left inequality, for the pair `(0, e₁)` (packet U3)

Blueprint Part D, `d:prop-u52`(a) (NA3 §2.2, §2.5, ROUTE-1; [8]-bp `r2:prop:51`). Port of
`HigherDimLQGMetric.DGZ.prop51Shape` (`DGZ/CompareProp51.lean`, MA7 D-5.1; it keeps [1]'s restriction `k ≤ c n`, which
the proof does not use).

**Statement** (`prop51_unif`). Let `d ≥ 2`, `κ` admissible, `b, μ > 0`, `ε > 0`. There are `c > 0` and `N`
(depending only on `d, κ, b, μ, ε`) such that for every `ξ ∈ S(b, μ)`, every dyadic realization, `n ≥ N` and
`1 ≤ k ≤ c n`: `P[D_{n+k}(0, e₁; B₂(0)) ≤ c 2^{-(1-ϕ(ξ)+ε)k} D_n(0, e₁; B₂(0))] ≤ 2^{-cn}`, `ϕ(ξ) = ξQ(ξ)`.

**Proof** (the sealed proof, with every constant chosen before `ξ`):
* `λ = uLambda d b μ`, `θ₀ = uTheta d b μ` (U0's constant package (A.7)), `R = dgzR ρ`;
* `K₀` and, for the chosen `K`, `C_J` and `L₀(ε)` from U2's `prob_J_compl_le_unif` (Lemma 5.9, uniform);
* the deterministic threshold `N₀ = N₀(d, θ₀, R)` from `cmp_lfppDistance_le_unif` (uniform Prop. 5.13 + Lemma 5.14's
  good event; `d:lem-u510`);
* `K` from `DGZ.cmp_exists_K` **at `b`**: `6bK + K ≤ K^{3/2}`, hence `6ξK + K ≤ K^{3/2}` for `ξ ≤ b`;
* `u, C₁₄` from `prob_not_lemma514Good_le_unif` (`λ' = λ/2`);
* `C₁₃ = prop513Const d b L ≥ prop513Const d ξ L` (`prop513Const_le_of_le`; in place of the blueprint's `4 C_L(b)`);
* `c = min(1/(3C₁₃ + 1), 1/(2(C_J + C₁₄)))` and `N = max(N_t, ⌈max(K⁴/(1-λ), 8/λ, 4R/λ)⌉)`.
On `𝒥₁ ∩ 𝒥₂′` and Lemma 5.14's good event, `D_n ≤ (3/2) C₁₃ 2^{(1-ϕ+ε)k} D_{n+k}`, which contradicts the event of the
statement since `(3/2) C₁₃ c ≤ 1/2` and `D_n > 0`; the two exceptional events have probability
`≤ C_J 2^{-n/C_J} + C₁₄ e^{-n/C₁₄} ≤ 2^{-cn}` for `n ≥ N`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox obox)

variable {d : ℕ}

/-- **Uniform DGZ Proposition 5.1, the direction used, for the pair `(0, e₁)`** (port of `DGZ.prop51Shape`;
`d:prop-u52`(a)): for `d ≥ 2`, `κ` admissible, `b, μ > 0` and `ε > 0` there are `c > 0` and `N` (depending only on
`d, κ, b, μ, ε`) such that for every `ξ ∈ S(b, μ)`, every dyadic realization, `n ≥ N` and `1 ≤ k ≤ c n`:
`P[D_{n+k}(0, e₁; B₂(0)) ≤ c 2^{-(1-ξQ(ξ)+ε)k} D_n(0, e₁; B₂(0))] ≤ 2^{-cn}`. -/
theorem prop51_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {b μ : ℝ} (hb : 0 < b)
    (hμ : 0 < μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∃ N : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n k : ℕ, N ≤ n → 1 ≤ k →
          (k : ℝ) ≤ c * n →
          P {ω | lfppDistance d ξ (fun z => H (n + k) z ω) ≤
              c * (2 : ℝ) ^ (-(1 - ξ * distExp d ξ + ε) * k) *
                lfppDistance d ξ (fun z => H n z ω)} ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-(c * n))) := by
  set lam : ℝ := uLambda d b μ with hlamdef
  have hlam0 : 0 < lam := uLambda_pos hb hμ
  have hlam4 : lam ≤ 1 / 4 := uLambda_le_quarter hb hμ
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  have hR10 : 2 * ρ + 10 ≤ (dgzR ρ : ℝ) := le_dgzR ρ
  have hR100 : 100 ≤ dgzR ρ := by
    unfold dgzR
    omega
  set θ₀ : ℝ := uTheta d b μ with hθ₀def
  have hθ₀ : 0 < θ₀ := uTheta_pos hb hμ
  obtain ⟨K₀, hJK⟩ := prob_J_compl_le_unif hd hκ hb hμ hρ hR10 θ₀ hθ₀ le_rfl
  obtain ⟨N₀, hdet⟩ := cmp_lfppDistance_le_unif hd hθ₀ hR100
  obtain ⟨K, hKK₀, hK2, hKN₀, hK3, hK40, hK6, hKlog, hK8⟩ :=
    cmp_exists_K b hlam0 (dgzR ρ) N₀ K₀ d
  obtain ⟨CJ, hCJ, hJε⟩ := hJK K hKK₀
  obtain ⟨L₀, hJL⟩ := hJε ε hε
  set L : ℝ := max L₀ 1 with hLdef
  have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨u, -, C14, hC14, h514⟩ := prob_not_lemma514Good_le_unif hd hκ hb hμ
    (lam' := lam / 2) (by positivity) (by linarith)
  set C13 : ℝ := prop513Const d b L with hC13def
  have hC13 : 0 ≤ C13 := prop513Const_nonneg d b hL.le
  set CT : ℝ := CJ + C14 with hCTdef
  have hCT : 0 < CT := add_pos hCJ hC14
  obtain ⟨Nt, hNt⟩ := cmp_two_rpow_tail hCT
  set c : ℝ := min (1 / (3 * C13 + 1)) (1 / (2 * CT)) with hcdef
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hc1 : c * (3 * C13 + 1) ≤ 1 := by
    have := min_le_left (1 / (3 * C13 + 1)) (1 / (2 * CT))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  have hc2 : c * (2 * CT) ≤ 1 := by
    have := min_le_right (1 / (3 * C13 + 1)) (1 / (2 * CT))
    rw [le_div_iff₀ (by positivity)] at this
    exact this
  set M : ℝ := max (((K ^ 4 : ℕ) : ℝ) / (1 - lam))
    (max (8 / lam) (4 * (dgzR ρ : ℝ) / lam)) with hMdef
  refine ⟨c, hc, max Nt ⌈M⌉₊, fun ξ hU Ω _ P W H hH n k hn hk _ => ?_⟩
  have hξ : 0 < ξ := hU.base.xi_pos
  have hξb : ξ ≤ b := hU.le_b
  set Q : ℝ := distExp d ξ with hQdef
  have hPprob := hH.whiteNoise.isProbabilityMeasure
  have hnNt : Nt ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  simp only [hMdef, max_le_iff] at hnM
  obtain ⟨hnK, hn8, hnR⟩ := hnM
  have h1lam : 0 < 1 - lam := by linarith
  rw [div_le_iff₀ h1lam] at hnK
  have hnK' : ((K ^ 4 : ℕ) : ℝ) ≤ (1 - lam) * n := by linarith
  -- the `K`-condition of the cover at `ξ ≤ b`
  have hK6ξ : 6 * ξ * K + K ≤ (K : ℝ) ^ ((3 : ℝ) / 2) := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have : 6 * ξ * K ≤ 6 * b * K :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξb (by norm_num)) hK0
    linarith
  have hC13ξ : prop513Const d ξ L ≤ C13 := prop513Const_le_of_le hξb hL.le
  set p : NiceParams := uNiceParams d b μ ξ θ₀ ε L K (dgzR ρ) n k with hpdef
  have hJn := hJL ξ hU Ω P W H hH p rfl rfl rfl rfl rfl rfl (le_max_left _ _) rfl
  have h514n := h514 ξ hU Ω P W H hH n
  -- the event of the statement forces `(𝒥₁ ∩ 𝒥₂′)ᶜ` or the failure of Lemma 5.14
  have hsub : {ω | lfppDistance d ξ (fun z => H (n + k) z ω) ≤
      c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * lfppDistance d ξ (fun z => H n z ω)} ⊆
      {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel lam K p.n) ∧
        EventJ2' p (fun q z => H q z ω) (dgzLevel lam K p.n))} ∪
      {ω | ¬ Lemma514Good ξ Q u (lam / 2) (fun z => H n z ω) n} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon hω
    obtain ⟨⟨hJ1, hJ2⟩, hG⟩ := hcon
    have hcmp := hdet ξ Q hξ lam hlam0 hlam4 p rfl rfl rfl rfl rfl u (fun q z => H q z ω)
      (fun q => (hH.band q).continuous ω) hK2 hKN₀ hK3 hK40 hK6ξ hKlog hK8 hL hnK' hn8 hnR hJ1
      hJ2 hG
    have hpos : 0 < lfppDistance d ξ (fun z => H n z ω) :=
      lfppDistance_pos (by omega) ((hH.band n).continuous ω)
    have hposk : 0 < lfppDistance d ξ (fun z => H (n + k) z ω) :=
      lfppDistance_pos (by omega) ((hH.band (n + k)).continuous ω)
    set Dn : ℝ := lfppDistance d ξ (fun z => H n z ω) with hDn
    set Dnk : ℝ := lfppDistance d ξ (fun z => H (n + k) z ω) with hDnk
    set X : ℝ := (2 : ℝ) ^ ((1 - ξ * Q + ε) * k) with hXdef
    set Y : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) with hYdef
    have hXY : X * Y = 1 := by
      rw [hXdef, hYdef, ← Real.rpow_add two_pos,
        show (1 - ξ * Q + ε) * (k : ℝ) + -(1 - ξ * Q + ε) * k = 0 by ring, Real.rpow_zero]
    have hX : 0 ≤ X := (Real.rpow_pos_of_pos two_pos _).le
    have hcmp' : Dn ≤ 3 / 2 * C13 * X * Dnk := by
      have h1 : 3 / 2 * prop513Const d ξ L * X * Dnk ≤ 3 / 2 * C13 * X * Dnk := by
        have h2 : 3 / 2 * prop513Const d ξ L ≤ 3 / 2 * C13 :=
          mul_le_mul_of_nonneg_left hC13ξ (by norm_num)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hX) hposk.le
      exact hcmp.trans h1
    have hc3 : 3 / 2 * C13 * c ≤ 1 / 2 := by nlinarith
    have hmain : Dn ≤ 3 / 2 * C13 * c * Dn := by
      calc Dn ≤ 3 / 2 * C13 * X * Dnk := hcmp'
        _ ≤ 3 / 2 * C13 * X * (c * Y * Dn) :=
            mul_le_mul_of_nonneg_left hω (by positivity)
        _ = 3 / 2 * C13 * c * (X * Y) * Dn := by ring
        _ = 3 / 2 * C13 * c * Dn := by rw [hXY, mul_one]
    have := mul_le_mul_of_nonneg_right hc3 hpos.le
    linarith
  have hexp : Real.exp (-(n : ℝ) / C14) ≤ (2 : ℝ) ^ (-(n : ℝ) / C14) := by
    rw [neg_div]
    exact cmp_exp_neg_le_two_rpow (by positivity)
  have hreal : CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * Real.exp (-(n : ℝ) / C14) ≤
      (2 : ℝ) ^ (-(c * n)) := by
    calc CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * Real.exp (-(n : ℝ) / C14)
        ≤ CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * (2 : ℝ) ^ (-(n : ℝ) / C14) := by
          have := mul_le_mul_of_nonneg_left hexp hC14.le
          linarith
      _ ≤ CT * (2 : ℝ) ^ (-(n : ℝ) / CT) := cmp_add_two_rpow_le hCJ hC14 n
      _ ≤ (2 : ℝ) ^ (-(n : ℝ) / (2 * CT)) := hNt n hnNt
      _ ≤ (2 : ℝ) ^ (-(c * n)) := by
          refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
          rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith
  calc P {ω | lfppDistance d ξ (fun z => H (n + k) z ω) ≤
        c * (2 : ℝ) ^ (-(1 - ξ * Q + ε) * k) * lfppDistance d ξ (fun z => H n z ω)}
      ≤ P ({ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel lam K p.n) ∧
          EventJ2' p (fun q z => H q z ω) (dgzLevel lam K p.n))} ∪
          {ω | ¬ Lemma514Good ξ Q u (lam / 2) (fun z => H n z ω) n}) :=
        measure_mono hsub
    _ ≤ P {ω | ¬ (EventJ1 p (fun q z => H q z ω) (dgzLevel lam K p.n) ∧
          EventJ2' p (fun q z => H q z ω) (dgzLevel lam K p.n))} +
        P {ω | ¬ Lemma514Good ξ Q u (lam / 2) (fun z => H n z ω) n} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ)) +
        ENNReal.ofReal (C14 * Real.exp (-(n : ℝ) / C14)) := add_le_add hJn h514n
    _ = ENNReal.ofReal (CJ * (2 : ℝ) ^ (-(n : ℝ) / CJ) + C14 * Real.exp (-(n : ℝ) / C14)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (-(c * n))) := ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGContinuity
