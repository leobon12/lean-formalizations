/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Heights
import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition

/-!
# Force weights in §7.3: Lemmas 7.16–7.17, the threshold criterion, and (TI13.1) for `κ ≤ 4`

Packet PROVE-SEC7-C (specification §7.3, `source/spec/p289-336.md` L628–L690, pp. 330–334; supplement §3.6,
`p433-480.md` L721–L742, p. 462; Aux. lemma 113, `p337-384.md` L686–L692). Throughout `λ = sleLambda κ = π/√κ`
and `χ = chiC κ = 2/√κ − √κ/2`, both positive for `0 < κ < 4` (`Sec4.sleLambda_pos`, `Sec4.chiC_pos`); a height `h`
left of the seed has cumulative weight `−h/λ − 1` and a height right of it `h/λ − 1` (`Sec4.cumWeightLeft`,
`Sec4.cumWeightRight`).

* **The threshold criterion** used throughout §7.3 ("all side partial sums remain strictly greater than `−2`, so no
  continuation threshold can occur"): for an ordered state, if every partial sum of the weights on each side, taken
  from the seed outward, exceeds `−2`, the frozen `ForceWord.ThresholdCondition` fails
  (`not_thresholdCondition_of_partialSums`). The marks at the driver on one side always form an initial segment
  (`isLowerSet_filter_eq_of_antitone`).
* **Lemma 7.17**, (AV1)–(AV3): the first piece of the two-angle flow line has seed weights
  `r_L = (a − θ₁χ)/λ − 1`, `r_R = (b + θ₁χ)/λ − 1`, which exceed `−2` exactly under the lemma's boundary inequalities
  (`lem717_rL_gt_iff`, `lem717_rR_gt_iff`); the second piece has seed weights `q_L = (θ₁ − θ₂)χ/λ`,
  `q_R = (θ₂ − θ₁)χ/λ` read off from the tip heights `∓λ + (θ₂ − θ₁)χ` (`lem717_qL_eq`, `lem717_qR_eq`), both `> −2`
  iff `|θ₁ − θ₂| < 2λ/χ` (`lem717_q_gt_iff`); and `q_L + r_L = (a − θ₂χ)/λ − 1`, `q_R + r_R = (b + θ₂χ)/λ − 1`
  (`lem717_qL_add_rL`, `lem717_qR_add_rR`). Hence the conditional word of the second piece never meets its
  continuation threshold (`lem717_not_thresholdCondition`).
* **Lemma 7.16**, first part: with equal angle steps `Δ = λ(ρ^R + 2)/χ` every conditional right weight is `ρ^R`, the
  marginal right weight of `η_{θ_n}` is `ρ^R + (n − 1)(ρ^R + 2)` (`lem716_marginal_right_weight`), which reaches
  `κ/2 − 2` for some `n` (`lem716_exists_marginal_right_weight_ge`), and the left weights `(a − θ_kχ)/λ − 1` are all
  nonnegative once `a` is large (`lem716_exists_left_weights_nonneg`).
* **Lemma 7.16**, supplement §3.6: the auxiliary angles `θ(r) = λ(r + 2)/χ` of the zero-angle flow with weights
  `(ρ̃_L; ρ_R)` give the auxiliary flows the seed weights `ρ̃_L − r − 2` and `ρ_R + r + 2`
  (`lem716_aux_left_weight`, `lem716_aux_right_weight`), conditional left weight `r` for `η` to their right
  (`lem716_aux_cond_weight`), and the admissibility claims of §3.6 (`lem716_aux_weights`); the final step
  `0 ≥ p(r) P[x ∉ α₁]`, `P[x ∉ α₁] > 0` ⟹ `p(r) = 0` is `lem716_eq_zero_of_mul_le_zero`.
* **Aux. lemma 113**: for `0 < κ ≤ 4` the alternatives (TI13.1) cover every pair of side totals
  (`ti13_1_of_le_four`).
-/

set_option autoImplicit false

noncomputable section

open Real Finset
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Sec7

open Sec4

/-! ### The threshold criterion from side partial sums -/

/-- In an ordered state the left marks at the driver form an initial segment of `Fin n` (a lower set). -/
theorem isLowerSet_filter_eq_of_antitone {n : ℕ} {v : Fin n → ℝ} {w : ℝ} (hv : Antitone v)
    (hle : ∀ i, v i ≤ w) : IsLowerSet {i | v i = w} := by
  intro i j hji hi
  have h1 : v i ≤ v j := hv hji
  have h2 := hle j
  simp only [Set.mem_ofPred_eq] at hi ⊢
  linarith

/-- The marks at the driver on one side have weight sum equal to a partial sum from the seed outward (or `0`). -/
theorem sum_filter_eq_partialSum {n : ℕ} {v : Fin n → ℝ} {w : ℝ} (ρ : Fin n → ℝ)
    (hlow : IsLowerSet {i | v i = w}) :
    (∑ i ∈ univ.filter (fun i => v i = w), ρ i) = 0 ∨
      ∃ m : Fin n, (∑ i ∈ univ.filter (fun i => v i = w), ρ i) =
        ∑ i ∈ univ.filter (fun i => i ≤ m), ρ i := by
  by_cases hne : (univ.filter (fun i => v i = w)).Nonempty
  · right
    set m := (univ.filter (fun i => v i = w)).max' hne
    refine ⟨m, ?_⟩
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    have hm : v m = w := by
      have := (univ.filter (fun i => v i = w)).max'_mem hne
      simpa using this
    constructor
    · intro hi
      exact (univ.filter (fun i => v i = w)).le_max' i (by simpa using hi)
    · intro hi
      exact hlow hi hm
  · left
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, sum_empty]

/-- The threshold criterion: in an ordered state (`vL` antitone and `≤ w`, `vR` monotone and `≥ w`), if every
partial sum of the weights from the seed outward exceeds `−2` on each side, then the continuation-threshold
condition fails. -/
theorem not_thresholdCondition_of_partialSums {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ}
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hL : Antitone vL) (hLw : ∀ i, vL i ≤ w) (hR : Monotone vR)
    (hRw : ∀ i, w ≤ vR i) (hsL : ∀ m : Fin nL, -2 < ∑ i ∈ univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin nR, -2 < ∑ i ∈ univ.filter (fun i => i ≤ m), ρR i) :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  have hlowL := isLowerSet_filter_eq_of_antitone hL hLw
  have hlowR : IsLowerSet {i | vR i = w} := by
    have : Antitone fun i => -vR i := fun i j h => neg_le_neg (hR h)
    have h := isLowerSet_filter_eq_of_antitone (w := -w) this (fun i => neg_le_neg (hRw i))
    simpa only [neg_inj] using h
  rintro (h | h)
  · rcases sum_filter_eq_partialSum ρL hlowL with h0 | ⟨m, hm⟩
    · rw [h0] at h; linarith
    · rw [hm] at h; linarith [hsL m]
  · rcases sum_filter_eq_partialSum ρR hlowR with h0 | ⟨m, hm⟩
    · rw [h0] at h; linarith
    · rw [hm] at h; linarith [hsR m]

/-! ### Lemma 7.17: the two-angle flow line (AV1)–(AV3) -/

variable {κ : ℝ}

/-- (AV1), left: the first piece (angle `θ`) sees the height `−a + θχ` left of the seed; its weight is
`r_L = (a − θχ)/λ − 1`. -/
theorem lem717_rL_eq (a θ : ℝ) :
    cumWeightLeft κ (-a + θ * chiC κ) = (a - θ * chiC κ) / sleLambda κ - 1 := by
  simp only [cumWeightLeft]; congr 1; ring

/-- (AV1), right: the height `b + θχ` right of the seed gives `r_R = (b + θχ)/λ − 1`. -/
theorem lem717_rR_eq (b θ : ℝ) :
    cumWeightRight κ (b + θ * chiC κ) = (b + θ * chiC κ) / sleLambda κ - 1 := rfl

/-- (AV1): `r_L > −2` iff `−a + θχ < λ` (the lemma's hypothesis `−a + θ_iχ < λ`). -/
theorem lem717_rL_gt_iff (hκ : 0 < κ) (a θ : ℝ) :
    -2 < (a - θ * chiC κ) / sleLambda κ - 1 ↔ -a + θ * chiC κ < sleLambda κ := by
  have hl := sleLambda_pos hκ
  rw [show -2 < (a - θ * chiC κ) / sleLambda κ - 1 ↔ -1 < (a - θ * chiC κ) / sleLambda κ by
    constructor <;> intro h <;> linarith, lt_div_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- (AV1): `r_R > −2` iff `b + θχ > −λ` (the lemma's hypothesis `b + θ_iχ > −λ`). -/
theorem lem717_rR_gt_iff (hκ : 0 < κ) (b θ : ℝ) :
    -2 < (b + θ * chiC κ) / sleLambda κ - 1 ↔ -sleLambda κ < b + θ * chiC κ := by
  have hl := sleLambda_pos hκ
  rw [show -2 < (b + θ * chiC κ) / sleLambda κ - 1 ↔ -1 < (b + θ * chiC κ) / sleLambda κ by
    constructor <;> intro h <;> linarith, lt_div_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- (AV2), left: the tip height `−λ + (θ₂ − θ₁)χ` left of the new seed has weight `q_L = (θ₁ − θ₂)χ/λ`. -/
theorem lem717_qL_eq (hκ : 0 < κ) (θ₁ θ₂ : ℝ) :
    cumWeightLeft κ (-sleLambda κ + (θ₂ - θ₁) * chiC κ) = (θ₁ - θ₂) * chiC κ / sleLambda κ := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightLeft]; field_simp; ring

/-- (AV2), right: the tip height `λ + (θ₂ − θ₁)χ` gives `q_R = (θ₂ − θ₁)χ/λ`. -/
theorem lem717_qR_eq (hκ : 0 < κ) (θ₁ θ₂ : ℝ) :
    cumWeightRight κ (sleLambda κ + (θ₂ - θ₁) * chiC κ) = (θ₂ - θ₁) * chiC κ / sleLambda κ := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightRight]; field_simp; ring

/-- (AV2): `q_L > −2` and `q_R > −2` exactly when `|θ₁ − θ₂| < 2λ/χ` (`0 < κ < 4`). -/
theorem lem717_q_gt_iff (hκ : 0 < κ) (hκ4 : κ < 4) (θ₁ θ₂ : ℝ) :
    (-2 < (θ₁ - θ₂) * chiC κ / sleLambda κ ∧ -2 < (θ₂ - θ₁) * chiC κ / sleLambda κ) ↔
      |θ₁ - θ₂| < 2 * sleLambda κ / chiC κ := by
  have hl := sleLambda_pos hκ
  have hc := chiC_pos hκ hκ4
  have e1 : θ₁ - θ₂ < 2 * sleLambda κ / chiC κ ↔ (θ₁ - θ₂) * chiC κ < 2 * sleLambda κ := lt_div_iff₀ hc
  have e2 : -(2 * sleLambda κ / chiC κ) < θ₁ - θ₂ ↔ (θ₂ - θ₁) * chiC κ < 2 * sleLambda κ := by
    rw [neg_lt, neg_sub]; exact lt_div_iff₀ hc
  rw [lt_div_iff₀ hl, lt_div_iff₀ hl, abs_lt, e1, e2]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- (AV3), left: `q_L + r_L = (a − θ₂χ)/λ − 1`. -/
theorem lem717_qL_add_rL (hκ : 0 < κ) (a θ₁ θ₂ : ℝ) :
    (θ₁ - θ₂) * chiC κ / sleLambda κ + ((a - θ₁ * chiC κ) / sleLambda κ - 1) =
      (a - θ₂ * chiC κ) / sleLambda κ - 1 := by
  have := sleLambda_ne_zero hκ
  field_simp; ring

/-- (AV3), right: `q_R + r_R = (b + θ₂χ)/λ − 1`. -/
theorem lem717_qR_add_rR (hκ : 0 < κ) (b θ₁ θ₂ : ℝ) :
    (θ₂ - θ₁) * chiC κ / sleLambda κ + ((b + θ₁ * chiC κ) / sleLambda κ - 1) =
      (b + θ₂ * chiC κ) / sleLambda κ - 1 := by
  have := sleLambda_ne_zero hκ
  field_simp; ring

/-- Lemma 7.17's hypotheses make the four values `q_L, q_L + r_L, q_R, q_R + r_R` of (AV3) exceed `−2`
(and also `r_L, r_R`, the first piece's seed weights). -/
theorem lem717_weights_gt (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ}
    (hθ : |θ₁ - θ₂| < 2 * sleLambda κ / chiC κ)
    (hb : ∀ θ ∈ ({θ₁, θ₂} : Set ℝ), -sleLambda κ < b + θ * chiC κ)
    (ha : ∀ θ ∈ ({θ₁, θ₂} : Set ℝ), -a + θ * chiC κ < sleLambda κ) :
    -2 < (θ₁ - θ₂) * chiC κ / sleLambda κ ∧
      -2 < (θ₁ - θ₂) * chiC κ / sleLambda κ + ((a - θ₁ * chiC κ) / sleLambda κ - 1) ∧
      -2 < (θ₂ - θ₁) * chiC κ / sleLambda κ ∧
      -2 < (θ₂ - θ₁) * chiC κ / sleLambda κ + ((b + θ₁ * chiC κ) / sleLambda κ - 1) ∧
      -2 < (a - θ₁ * chiC κ) / sleLambda κ - 1 ∧ -2 < (b + θ₁ * chiC κ) / sleLambda κ - 1 := by
  obtain ⟨hqL, hqR⟩ := (lem717_q_gt_iff hκ hκ4 θ₁ θ₂).2 hθ
  refine ⟨hqL, ?_, hqR, ?_, ?_, ?_⟩
  · rw [lem717_qL_add_rL hκ]; exact (lem717_rL_gt_iff hκ a θ₂).2 (ha θ₂ (by simp))
  · rw [lem717_qR_add_rR hκ]; exact (lem717_rR_gt_iff hκ b θ₂).2 (hb θ₂ (by simp))
  · exact (lem717_rL_gt_iff hκ a θ₁).2 (ha θ₁ (by simp))
  · exact (lem717_rR_gt_iff hκ b θ₁).2 (hb θ₁ (by simp))

/-- Partial sums of a two-entry weight vector. -/
theorem partialSum_fin_two (ρ : Fin 2 → ℝ) (m : Fin 2) :
    ∑ i ∈ univ.filter (fun i => i ≤ m), ρ i = if m = 0 then ρ 0 else ρ 0 + ρ 1 := by
  fin_cases m
  · simp only [Fin.zero_eta, Fin.isValue, ite_true]
    rw [show univ.filter (fun i : Fin 2 => i ≤ 0) = {0} by decide, sum_singleton]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false]
    rw [show univ.filter (fun i : Fin 2 => i ≤ 1) = univ by decide, Fin.sum_univ_two]

/-- Lemma 7.17: the conditional word of the second piece, with left weights `(q_L, r_L)` and right weights
`(q_R, r_R)` (the new seed group, then the surviving image of the old seed-side mark), meets no continuation
threshold in any ordered state. The cases with fewer marks are the sub-words. -/
theorem lem717_not_thresholdCondition (hκ : 0 < κ) (hκ4 : κ < 4) {a b θ₁ θ₂ : ℝ}
    (hθ : |θ₁ - θ₂| < 2 * sleLambda κ / chiC κ)
    (hb : ∀ θ ∈ ({θ₁, θ₂} : Set ℝ), -sleLambda κ < b + θ * chiC κ)
    (ha : ∀ θ ∈ ({θ₁, θ₂} : Set ℝ), -a + θ * chiC κ < sleLambda κ) {w : ℝ} {vL vR : Fin 2 → ℝ}
    (hL : Antitone vL) (hLw : ∀ i, vL i ≤ w) (hR : Monotone vR) (hRw : ∀ i, w ≤ vR i) :
    ¬ ForceWord.ThresholdCondition
      ![(θ₁ - θ₂) * chiC κ / sleLambda κ, (a - θ₁ * chiC κ) / sleLambda κ - 1]
      ![(θ₂ - θ₁) * chiC κ / sleLambda κ, (b + θ₁ * chiC κ) / sleLambda κ - 1] w vL vR := by
  obtain ⟨h1, h2, h3, h4, -, -⟩ := lem717_weights_gt hκ hκ4 hθ hb ha
  refine not_thresholdCondition_of_partialSums hL hLw hR hRw (fun m => ?_) (fun m => ?_)
  · rw [partialSum_fin_two]; split_ifs <;> simpa using by assumption
  · rw [partialSum_fin_two]; split_ifs <;> simpa using by assumption


/-! ### Lemma 7.16, first part: the iterated flow lines of Figure 7.8

A flow line of angle `θ` of the field with boundary data `−a` left and `b` right of `0` has weights
`((a − θχ)/λ − 1; (b + θχ)/λ − 1)`, and (Proposition 7.4) the conditional law of `η_{θ_k}` given `η_{θ_{k−1}}`
has right weight `(θ_k − θ_{k−1})χ/λ − 2`. With the angles `θ_k = θ₁ + (k − 1)Δ`, `Δ = λ(ρ^R + 2)/χ`, and
`b = λ(1 + ρ^R) − θ₁χ`, every conditional right weight and the right weight of `η_{θ₁}` are `ρ^R`. -/

/-- The angle step `Δ = λ(ρ^R + 2)/χ`. -/
def lem716Step (κ ρR : ℝ) : ℝ := sleLambda κ * (ρR + 2) / chiC κ

theorem lem716Step_pos (hκ : 0 < κ) (hκ4 : κ < 4) {ρR : ℝ} (hρ : -2 < ρR) : 0 < lem716Step κ ρR :=
  div_pos (mul_pos (sleLambda_pos hκ) (by linarith)) (chiC_pos hκ hκ4)

/-- Each conditional right weight `(θ_k − θ_{k−1})χ/λ − 2 = Δχ/λ − 2` equals `ρ^R`. -/
theorem lem716_step_weight (hκ : 0 < κ) (hκ4 : κ < 4) (ρR : ℝ) :
    lem716Step κ ρR * chiC κ / sleLambda κ - 2 = ρR := by
  have hl := sleLambda_ne_zero hκ
  have hc := (chiC_pos hκ hκ4).ne'
  simp only [lem716Step]
  field_simp
  ring

/-- With `b = λ(1 + ρ^R) − θ₁χ`, the marginal right weight of `η_{θ_n}`, `θ_n = θ₁ + (n − 1)Δ`, is
`ρ^R + (n − 1)(ρ^R + 2)`. -/
theorem lem716_marginal_right_weight (hκ : 0 < κ) (hκ4 : κ < 4) (ρR θ₁ : ℝ) (n : ℕ) :
    ((sleLambda κ * (1 + ρR) - θ₁ * chiC κ) + (θ₁ + n * lem716Step κ ρR) * chiC κ) / sleLambda κ - 1 =
      ρR + n * (ρR + 2) := by
  have hl := sleLambda_ne_zero hκ
  have hc := (chiC_pos hκ hκ4).ne'
  simp only [lem716Step]
  field_simp
  ring

/-- "By choosing `n` large enough, we can arrange that `ρ^R_n ≥ κ/2 − 2`." -/
theorem lem716_exists_marginal_right_weight_ge {ρR : ℝ} (hρ : -2 < ρR) (c : ℝ) :
    ∃ n : ℕ, c ≤ ρR + n * (ρR + 2) := by
  obtain ⟨n, hn⟩ := exists_nat_ge ((c - ρR) / (ρR + 2))
  refine ⟨n, ?_⟩
  have hpos : 0 < ρR + 2 := by linarith
  rw [div_le_iff₀ hpos] at hn
  linarith

/-- "By choosing `a` very large", every left weight `(a − θ_kχ)/λ − 1`, `k ≤ n`, is nonnegative. -/
theorem lem716_exists_left_weights_nonneg (hκ : 0 < κ) (θ : ℕ → ℝ) (n : ℕ) :
    ∃ a : ℝ, ∀ k ≤ n, 0 ≤ (a - θ k * chiC κ) / sleLambda κ - 1 := by
  have hl := sleLambda_pos hκ
  set M := ∑ k ∈ range (n + 1), |θ k * chiC κ|
  refine ⟨sleLambda κ + M, fun k hk => ?_⟩
  have hkM : |θ k * chiC κ| ≤ M :=
    single_le_sum (f := fun k => |θ k * chiC κ|) (fun _ _ => abs_nonneg _) (mem_range.2 (by omega))
  have h1 : θ k * chiC κ ≤ M := (le_abs_self _).trans hkM
  rw [sub_nonneg, le_div_iff₀ hl]
  linarith

/-- The first part's conclusion: a product of hit probabilities vanishes only if a factor vanishes
(`P[x ∈ η_{θ_n}] = p(ρ^L_1)⋯p(ρ^L_n) = 0` gives `k₀` with `p(ρ^L_{k₀}) = 0`). -/
theorem lem716_exists_factor_eq_zero {n : ℕ} (p : Fin n → ℝ) (h : ∏ k, p k = 0) : ∃ k, p k = 0 := by
  obtain ⟨k, -, hk⟩ := prod_eq_zero_iff.1 h
  exact ⟨k, hk⟩

/-! ### Lemma 7.16, supplement §3.6: the auxiliary flows `α_i = η_{θ_i}` -/

/-- The auxiliary angle `θ(r) = λ(r + 2)/χ` of supplement §3.6. -/
def lem716AuxAngle (κ r : ℝ) : ℝ := sleLambda κ * (r + 2) / chiC κ

theorem lem716AuxAngle_mul_chiC_div (hκ : 0 < κ) (hκ4 : κ < 4) (r : ℝ) :
    lem716AuxAngle κ r * chiC κ / sleLambda κ = r + 2 := by
  have hl := sleLambda_ne_zero hκ
  have hc := (chiC_pos hκ hκ4).ne'
  simp only [lem716AuxAngle]
  field_simp

/-- The zero-angle flow with weights `(ρ̃_L; ρ_R)` sees the heights `−λ(1 + ρ̃_L)` and `λ(1 + ρ_R)`; its auxiliary
flow of angle `θ(r)` has left seed weight `ρ̃_L − r − 2`. -/
theorem lem716_aux_left_weight (hκ : 0 < κ) (hκ4 : κ < 4) (ρtL r : ℝ) :
    cumWeightLeft κ (-(sleLambda κ * (1 + ρtL)) + lem716AuxAngle κ r * chiC κ) = ρtL - r - 2 := by
  have h := lem716AuxAngle_mul_chiC_div hκ hκ4 r
  have hl := sleLambda_ne_zero hκ
  simp only [cumWeightLeft]
  have e : sleLambda κ * (1 + ρtL) / sleLambda κ = 1 + ρtL := by field_simp
  rw [neg_div, add_div, neg_div, e, h]
  ring

/-- … and right seed weight `ρ_R + r + 2`. -/
theorem lem716_aux_right_weight (hκ : 0 < κ) (hκ4 : κ < 4) (ρR r : ℝ) :
    cumWeightRight κ (sleLambda κ * (1 + ρR) + lem716AuxAngle κ r * chiC κ) = ρR + r + 2 := by
  have h := lem716AuxAngle_mul_chiC_div hκ hκ4 r
  have hl := sleLambda_ne_zero hκ
  simp only [cumWeightRight]
  rw [add_div, h, mul_comm, mul_div_assoc, div_self hl]
  ring

/-- Proposition 7.4's middle weight: conditional on `α = η_{θ(r)}`, the zero-angle flow `η` (to its right) has left
seed weight `(θ(r) − 0)χ/λ − 2 = r`. -/
theorem lem716_aux_cond_weight (hκ : 0 < κ) (hκ4 : κ < 4) (r : ℝ) :
    (lem716AuxAngle κ r - 0) * chiC κ / sleLambda κ - 2 = r := by
  rw [sub_zero, lem716AuxAngle_mul_chiC_div hκ hκ4]; ring

/-- Supplement §3.6, the admissibility claims: for `r > −2`, `r₀ ≥ 0`, `ρ_R > −2` and `ρ̃_L > max(r, r₀) + 2`, both
auxiliary left seed weights are positive, both right seed weights exceed `−2`, and the right weight of `α₂` is
positive, hence at least `κ/2 − 2` (so `α₂` avoids `ℝ₊`). -/
theorem lem716_aux_weights (hκ4 : κ < 4) {r r₀ ρR ρtL : ℝ} (hr : -2 < r) (hr₀ : 0 ≤ r₀) (hρR : -2 < ρR)
    (hρtL : max r r₀ + 2 < ρtL) :
    0 < ρtL - r - 2 ∧ 0 < ρtL - r₀ - 2 ∧ -2 < ρR + r + 2 ∧ -2 < ρR + r₀ + 2 ∧ 0 < ρR + r₀ + 2 ∧
      κ / 2 - 2 ≤ ρR + r₀ + 2 := by
  have h1 := le_max_left r r₀
  have h2 := le_max_right r r₀
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Supplement §3.6, the last step: `0 = P[x ∈ η] ≥ p(r) P[x ∉ α₁]` with `P[x ∉ α₁] > 0` gives `p(r) = 0`. -/
theorem lem716_eq_zero_of_mul_le_zero {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (h : p * q ≤ 0) : p = 0 := by
  rcases hp.lt_or_eq with hp' | hp'
  · exact absurd h (not_le.2 (mul_pos hp' hq))
  · exact hp'.symm

/-! ### Aux. lemma 113: (TI13.1) covers all side totals for `κ ≤ 4` -/

/-- For `0 < κ ≤ 4` the alternatives (TI13.1) `s_L ≤ −2`, `s_R ≤ −2`, or `s_L, s_R > d = κ/2 − 4` cover every pair
of side totals (as `d ≤ −2`), so Aux. lemma 113 applies to every two-sided configuration in the revised induction. -/
theorem ti13_1_of_le_four (hκ4 : κ ≤ 4) (sL sR : ℝ) :
    sL ≤ -2 ∨ sR ≤ -2 ∨ (κ / 2 - 4 < sL ∧ κ / 2 - 4 < sR) := by
  by_cases hL : sL ≤ -2
  · exact Or.inl hL
  by_cases hR : sR ≤ -2
  · exact Or.inr (Or.inl hR)
  push Not at hL hR
  exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

end Sec7

end InteractingSLE
