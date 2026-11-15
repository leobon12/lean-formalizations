import InteractingSLE.Spec.Sec4.PartialSums
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

/-!
# Section 4.2: boundary heights and the weight condition (4.4)

Packet PROVE-SEC4-B. The arithmetic of §4.2 of the specification (`source/spec/p097-144.md`,
pp. 116–127), with `λ = sleLambda κ`, `λ' = sleLambda (16/κ)`, `χ = chiC κ` and the identities
(4.1)–(4.3) of PROVE-SEC4-A (`InteractingSLE.Spec.Sec4.Heights`).

* Figure 4.6, Lemma 4.7 proof, Proposition 4.9 proof, Remark 4.10: the heights
  `−λ − (π/2)χ ≤ −λ'`, `λ − (π/2)χ = λ'`, `−λ' + (π/2)χ = λ − 2λ' = −λ + πχ ∈ (−λ, λ)`,
  `λ' + (π/2)χ = λ`.
* (4.4): `Cond44 κ ρL ρR` — every left partial sum is at least `κ/2 − 2`, every right partial sum
  is nonnegative.
* Proposition 4.12 proof: for `0 < κ < 4` and an ordered word, (4.4) gives the noncollision
  partial-sum hypothesis of Aux. lemma 7 (`hasAdmissiblePartialSums_of_cond44`, SEC4-A's
  `HasAdmissiblePartialSums`, amalgamated groups).
* Proof of Theorem 1.2 assuming (4.4): the boundary data of the force word is at most `−λ + πχ`
  left of `0` and at least `λ` right of `0` (`forceBoundaryData_bounds_of_cond44`), the
  lower-boundary hypotheses of Proposition 4.11 ("by adjusting the boundary data of `h`, we can
  arrange so that `η ∼ SLE_κ(ρ)` with any choice of weights `ρ` satisfying (4.4)").
* `prop412_of_aux7` (conditional helper, distinct name): Proposition 4.12 from the statement of
  Aux. lemma 7 for the given evolution (Aux. lemma 7 is not yet in Lean: it rests on [Zha10]).
* (SP2) and the bounded drift of the Aux. lemma 24 localization.
-/

set_option autoImplicit false

noncomputable section

open Real Finset MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec4

open QuantumZipper (chiC)

/-! ### Heights of Figure 4.6, Lemma 4.7, Proposition 4.9 and Remark 4.10 -/

/-- Figure 4.6 and Lemma 4.7 proof (lower boundary, left of `0`): `−λ − (π/2)χ ≤ −λ'` for
`0 < κ ≤ 4`. -/
theorem fig46_lower_left_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    -sleLambda κ - π / 2 * chiC κ ≤ -sleLambda (16 / κ) := by
  have h := sleLambda_sixteen_div_eq_sub hκ
  have hl : sleLambda (16 / κ) ≤ sleLambda κ := by
    rw [sleLambda_sixteen_div hκ]
    have := sleLambda_pos hκ
    nlinarith
  linarith

/-- Figure 4.6 and Lemma 4.7 proof (lower boundary, right of `0`; (4.2)): `λ − (π/2)χ = λ'`. -/
theorem fig46_lower_right_eq {κ : ℝ} (hκ : 0 < κ) :
    sleLambda κ - π / 2 * chiC κ = sleLambda (16 / κ) :=
  (sleLambda_sixteen_div_eq_sub hκ).symm

/-- Lemma 4.7 proof (vertical upward slit, derivative argument `−π/2`): `−λ + πχ/2 = −λ'`. -/
theorem slit_left_height_eq {κ : ℝ} (hκ : 0 < κ) :
    -sleLambda κ + π * chiC κ / 2 = -sleLambda (16 / κ) := by
  have h := sleLambda_sixteen_div_eq_sub hκ
  linarith

/-- Figure 4.6, Lemma 4.7 and Proposition 4.9 proofs (the upper-left height of the flow line):
`−λ' + (π/2)χ = λ − 2λ'`. -/
theorem fig46_upper_left_eq {κ : ℝ} (hκ : 0 < κ) :
    -sleLambda (16 / κ) + π / 2 * chiC κ = sleLambda κ - 2 * sleLambda (16 / κ) := by
  have h := sleLambda_sixteen_div_eq_sub hκ
  linarith

/-- Remark 4.10: `−λ' + πχ/2 = −λ + πχ`. -/
theorem rem410_upper_left_eq {κ : ℝ} (hκ : 0 < κ) :
    -sleLambda (16 / κ) + π * chiC κ / 2 = -sleLambda κ + π * chiC κ := by
  have h := sleLambda_sixteen_div_eq_sub hκ
  linarith

/-- Figure 4.6, Lemma 4.7, Proposition 4.9 and Remark 4.10: the upper-left height
`−λ' + (π/2)χ` lies in the strictly critical interval `(−λ, λ)` for `0 < κ < 4`. -/
theorem fig46_upper_left_mem_Ioo {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    -sleLambda (16 / κ) + π / 2 * chiC κ ∈ Set.Ioo (-sleLambda κ) (sleLambda κ) := by
  rw [fig46_upper_left_eq hκ]
  have h1 := sleLambda_sixteen_div_lt hκ hκ4
  have h2 := sleLambda_sixteen_div_pos hκ
  constructor <;> linarith

/-- Figure 4.6, Lemma 4.7 and Remark 4.10 (the upper-right height of the flow line):
`λ' + (π/2)χ = λ`. -/
theorem fig46_upper_right_eq {κ : ℝ} (hκ : 0 < κ) :
    sleLambda (16 / κ) + π / 2 * chiC κ = sleLambda κ := by
  have h := sleLambda_sixteen_div_eq_sub hκ
  linarith

/-! ### The weight condition (4.4) -/

/-- **(4.4)**: every left partial sum `∑_{i ≤ j} ρ^{i,L}` (`1 ≤ j ≤ k`) is at least `κ/2 − 2`, and
every right partial sum `∑_{i ≤ j} ρ^{i,R}` (`1 ≤ j ≤ ℓ`) is nonnegative (the Lean index
`i : Fin n` is the source index `i + 1`). -/
def Cond44 (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  (∀ j : ℕ, 1 ≤ j → j ≤ nL → κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nL => i.val < j), ρL i) ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ nR → 0 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i.val < j), ρR i

/-- A downward closed set of indices of `Fin n` is an initial segment `{i | i < m}`. -/
theorem filter_eq_filter_val_lt_card {n : ℕ} {p : Fin n → Prop} [DecidablePred p]
    (hp : ∀ i i' : Fin n, i' ≤ i → p i → p i') :
    univ.filter p = univ.filter (fun i : Fin n => i.val < (univ.filter p).card) := by
  apply Finset.filter_congr
  intro i _
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ univ.filter p := fun i' hi' =>
      mem_filter.2 ⟨mem_univ _, hp i i' (Finset.mem_Iic.1 hi') hi⟩
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hi
    by_contra hni
    have hsub : univ.filter p ⊆ Finset.Iio i := by
      intro i' hi'
      rw [Finset.mem_Iio]
      by_contra hle
      exact hni (hp i' i (not_lt.1 hle) (mem_filter.1 hi').2)
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- A left prefix of an ordered word is an index prefix. -/
theorem sum_filter_lt_xL_ge_of_cond44 {κ : ℝ} {nL : ℕ} {xL ρL : Fin nL → ℝ} (hxL : Antitone xL)
    (h44 : ∀ j : ℕ, 1 ≤ j → j ≤ nL →
      κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nL => i.val < j), ρL i)
    {x : ℝ} (hne : ∃ i, x < xL i) : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => x < xL i), ρL i := by
  have hdown : ∀ i i' : Fin nL, i' ≤ i → x < xL i → x < xL i' := fun i i' hii' hi =>
    hi.trans_le (hxL hii')
  rw [filter_eq_filter_val_lt_card hdown]
  obtain ⟨i₀, hi₀⟩ := hne
  refine h44 _ ?_ ?_
  · exact card_pos.2 ⟨i₀, mem_filter.2 ⟨mem_univ _, hi₀⟩⟩
  · exact (card_filter_le _ _).trans (by simp)

/-- A right prefix of an ordered word is an index prefix. -/
theorem sum_filter_xR_le_nonneg_of_cond44 {nR : ℕ} {xR ρR : Fin nR → ℝ} (hxR : Monotone xR)
    (h44 : ∀ j : ℕ, 1 ≤ j → j ≤ nR →
      0 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i.val < j), ρR i)
    (x : ℝ) : 0 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ x), ρR i := by
  have hdown : ∀ i i' : Fin nR, i' ≤ i → xR i ≤ x → xR i' ≤ x := fun i i' hii' hi =>
    (hxR hii').trans hi
  rw [filter_eq_filter_val_lt_card hdown]
  rcases Nat.eq_zero_or_pos (univ.filter fun i => xR i ≤ x).card with h0 | hpos
  · rw [h0]
    simp
  · exact h44 _ hpos ((card_filter_le _ _).trans (by simp))

/-- **Proposition 4.12 proof**: "For `0 < κ < 4` one has `κ/2 − 2 < 0`. The left partial sums in
(4.4) are at least `κ/2 − 2`, and its right partial sums are nonnegative, hence also at least
`κ/2 − 2`." For an ordered word, (4.4) gives the noncollision partial-sum hypothesis of Aux.
lemma 7 on amalgamated groups. -/
theorem hasAdmissiblePartialSums_of_cond44 {κ : ℝ} (hκ4 : κ < 4) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h44 : Cond44 κ ρL ρR) : HasAdmissiblePartialSums κ ρL ρR xL xR :=
  ⟨fun _ _ hne => sum_filter_lt_xL_ge_of_cond44 hF.1 h44.1 hne, fun x _ _ =>
    le_trans (by linarith) (sum_filter_xR_le_nonneg_of_cond44 hF.2.2.1 h44.2 x)⟩

/-- **Proof of Theorem 1.2 assuming (4.4)** (pp. 121–122): for `0 < κ < 4` and an ordered word
with weights satisfying (4.4), the boundary data of the force word is at most `−λ + πχ` on
`(−∞, 0)` and at least `λ` on `[0, ∞)` — the lower-boundary hypotheses of Proposition 4.11
(Remarks 4.8 and 4.10). -/
theorem forceBoundaryData_bounds_of_cond44 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h44 : Cond44 κ ρL ρR) :
    (∀ x : ℝ, x < 0 → forceBoundaryData κ ρL ρR xL xR x ≤ -sleLambda κ + π * chiC κ) ∧
      ∀ x : ℝ, 0 ≤ x → sleLambda κ ≤ forceBoundaryData κ ρL ρR xL xR x := by
  have hl := sleLambda_pos hκ
  have hπχ := pi_mul_chiC hκ
  constructor
  · intro x hx
    rw [forceBoundaryData_of_neg ρL ρR xL xR hx, hπχ]
    have hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => x < xL i), ρL i := by
      by_cases hne : ∃ i, x < xL i
      · exact sum_filter_lt_xL_ge_of_cond44 hF.1 h44.1 hne
      · push Not at hne
        rw [Finset.filter_false_of_mem fun i _ => not_lt.2 (hne i), sum_empty]
        linarith
    nlinarith
  · intro x hx
    rw [forceBoundaryData_of_nonneg ρL ρR xL xR hx]
    have hS := sum_filter_xR_le_nonneg_of_cond44 hF.2.2.1 h44.2 x
    nlinarith

/-- **Proposition 4.12 from Aux. lemma 7** (conditional helper; the source proof, p. 124, is
exactly this reduction). For `0 < κ < 4`, an ordered word with weights satisfying (4.4), and an
integrated `SLE_κ(ρ)` evolution, the conclusion of Aux. lemma 7 — infinite lifetime, a continuous
generating trace, and `|η(t)| → ∞` — holds provided Aux. lemma 7 holds for this evolution. The
hypothesis `haux7` is the statement of Aux. lemma 7 (`source/spec/p001-048.md#aux-7`), which rests
on [Zha10, Theorems 4.2 and 7.7] and is not yet formalized; it is not a premise of
Proposition 4.12. -/
theorem prop412_of_aux7 {κ : ℝ} (hκ4 : κ < 4) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) (h44 : Cond44 κ ρL ρR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (haux7 : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      HasAdmissiblePartialSums κ ρL ρR xL xR →
      ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
          Tendsto (fun t => ‖η t‖) atTop atTop) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
        Tendsto (fun t => ‖η t‖) atTop atTop :=
  haux7 hev (hasAdmissiblePartialSums_of_cond44 hκ4 hF h44)

/-! ### (SP2) and the localized drift of Aux. lemma 24 -/

/-- (SP2): `ρ_* > −2` implies `ρ_* > κ/2 − 4` for `κ < 4`. -/
theorem sp2 {κ ρ : ℝ} (hκ4 : κ < 4) (hρ : -2 < ρ) : κ / 2 - 4 < ρ := by linarith

/-- Aux. lemma 24 proof (p. 124): "On this localization the added drift is bounded by
`n ∑_j |ρ_j|`": if every force gap is at least `1/n` (`n > 0`), then
`|∑_j ρ_j / (W − V_j)| ≤ n ∑_j |ρ_j|`. -/
theorem abs_sum_div_le_of_gap {ι : Type*} (s : Finset ι) (ρ V : ι → ℝ) {W n : ℝ} (hn : 0 < n)
    (hgap : ∀ j ∈ s, 1 / n ≤ |W - V j|) : |∑ j ∈ s, ρ j / (W - V j)| ≤ n * ∑ j ∈ s, |ρ j| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hg := hgap j hj
  have hpos : 0 < |W - V j| := lt_of_lt_of_le (by positivity) hg
  rw [abs_div, div_le_iff₀ hpos]
  have : 1 ≤ n * |W - V j| := by
    rw [div_le_iff₀ hn] at hg
    linarith
  nlinarith [abs_nonneg (ρ j)]

end Sec4

end InteractingSLE
