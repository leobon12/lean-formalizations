import QuantumZipper.Proofs.Thm18.G1Side3Red

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (3): a scale-invariant law on `[0,∞]` is carried by `{0, ∞}`

If a random variable `X ∈ [0,∞]` has the same law as `c^m X` for a fixed `c > 1` and every
`m ∈ ℕ`, then `X ∈ {0, ∞}` almost surely (`ae_zero_or_top_of_scaleInv`): the events
`{c^n ≤ X < c^{n+1}}`, `n ∈ ℤ`, are disjoint, all have the probability of `{1 ≤ X < c}`, and
exhaust `{0 < X < ∞}`. This is the scaling argument for the infinite quantum area of a side
domain (the area `X = μ_h(D)` satisfies `law(X) = law(e^{γC} X)` by adding a constant to the
wedge field and recanonicalizing; Sheffield, arXiv:1012.4797, §1.6; Duplantier–Miller–Sheffield,
*Mating of trees*, Def. 4.4 and Prop. 4.7). Own elementary proof.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuantumZipper
namespace G1Side

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Dichotomy for a scale-invariant law.** -/
theorem ae_zero_or_top_of_scaleInv [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞} (hX : Measurable X)
    {c : ℝ≥0∞} (hc1 : 1 < c) (hct : c ≠ ⊤)
    (hinv : ∀ m : ℕ, P.map (fun ω => c ^ m * X ω) = P.map X) :
    ∀ᵐ ω ∂P, X ω = 0 ∨ X ω = ⊤ := by
  have hc0 : c ≠ 0 := (zero_lt_one.trans hc1).ne'
  have hcm : ∀ m : ℕ, Measurable fun ω => c ^ m * X ω := fun m => hX.const_mul _
  -- the law identity on intervals
  have hI : ∀ (m : ℕ) (B : Set ℝ≥0∞), MeasurableSet B →
      P ((fun ω => c ^ m * X ω) ⁻¹' B) = P (X ⁻¹' B) := fun m B hB => by
    rw [← Measure.map_apply (hcm m) hB, ← Measure.map_apply hX hB, hinv m]
  set A0 : Set ℝ≥0∞ := Ico 1 c with hA0
  -- `P(c^n ≤ X < c^{n+1}) = P(A0)` for `n ≥ 0`
  have hpos : ∀ n : ℕ, P (X ⁻¹' Ico (c ^ n) (c ^ (n + 1))) = P (X ⁻¹' A0) := by
    intro n
    have hcn0 : c ^ n ≠ 0 := pow_ne_zero _ hc0
    have hcnt : c ^ n ≠ ⊤ := ENNReal.pow_ne_top hct
    rw [← hI n (Ico (c ^ n) (c ^ (n + 1))) measurableSet_Ico]
    congr 1
    ext ω
    simp only [mem_preimage, mem_Ico, hA0, pow_succ]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := (ENNReal.mul_le_mul_iff_right hcn0 hcnt (b := 1) (c := X ω)).1
        exact this (by rwa [mul_one])
      · exact (ENNReal.mul_right_strictMono hcn0 hcnt).lt_iff_lt.1 h2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc c ^ n = c ^ n * 1 := (mul_one _).symm
          _ ≤ c ^ n * X ω := by gcongr
      · exact ENNReal.mul_lt_mul_right hcn0 hcnt h2
  have hbig : ∀ y : ℝ≥0∞, y ≠ ⊤ → ∃ n : ℕ, y < c ^ n := by
    intro y hy
    have hcr : 1 < c.toReal := by
      have := ENNReal.toReal_strict_mono hct hc1
      simpa using this
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt y.toReal hcr
    refine ⟨n, ?_⟩
    rw [← ENNReal.ofReal_toReal hy, ← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hct),
      ENNReal.toReal_pow]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hn
  -- summing the disjoint events for `n ≥ 0`
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => X ⁻¹' Ico (c ^ n) (c ^ (n + 1))) := by
    intro i j hij
    refine Disjoint.preimage _ ?_
    rcases lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hx hx' => by
        have : c ^ (i + 1) ≤ c ^ j := pow_le_pow_right₀ hc1.le h
        exact absurd (hx.2.trans_le (this.trans hx'.1)) (lt_irrefl _)
    · exact Set.disjoint_left.2 fun x hx hx' => by
        have : c ^ (j + 1) ≤ c ^ i := pow_le_pow_right₀ hc1.le h
        exact absurd (hx'.2.trans_le (this.trans hx.1)) (lt_irrefl _)
  have hsum : ∑' n : ℕ, P (X ⁻¹' Ico (c ^ n) (c ^ (n + 1))) ≤ 1 := by
    rw [← measure_iUnion hdisj fun n => hX measurableSet_Ico]
    exact prob_le_one
  have hA00 : P (X ⁻¹' A0) = 0 := by
    by_contra hne
    simp_rw [hpos] at hsum
    rw [ENNReal.tsum_const_eq_top_of_ne_zero hne] at hsum
    exact absurd hsum (by simp)
  -- negative indices: `P(c^{-m} ≤ X < c^{1-m}) = P(1 ≤ c^m X < c) = P(A0)`
  have hneg : ∀ m : ℕ, P ((fun ω => c ^ m * X ω) ⁻¹' A0) = 0 := fun m => by
    rw [hI m A0 measurableSet_Ico, hA00]
  -- every `0 < X < ∞` lies in one of the events
  have hcover : {ω | X ω ≠ 0 ∧ X ω ≠ ⊤} ⊆
      (⋃ n : ℕ, X ⁻¹' Ico (c ^ n) (c ^ (n + 1))) ∪ ⋃ m : ℕ, (fun ω => c ^ m * X ω) ⁻¹' A0 := by
    rintro ω ⟨h0, ht⟩
    rcases le_or_gt 1 (X ω) with h1 | h1
    · -- `X ≥ 1`: the largest `n` with `c^n ≤ X`
      left
      have hex : ∃ n : ℕ, X ω < c ^ n := hbig _ ht
      classical
      let n := Nat.find hex
      have hn : X ω < c ^ n := Nat.find_spec hex
      have hn0 : n ≠ 0 := by
        intro h
        have : X ω < c ^ 0 := h ▸ hn
        rw [pow_zero] at this
        exact absurd h1 (not_le.2 this)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hk' : c ^ k ≤ X ω := not_lt.1 (Nat.find_min hex (by omega : k < n))
      exact mem_iUnion.2 ⟨k, hk', by rw [show k + 1 = n from hk.symm]; exact hn⟩
    · -- `X < 1`: the least `m` with `1 ≤ c^m X`
      right
      have hex : ∃ m : ℕ, 1 ≤ c ^ m * X ω := by
        obtain ⟨m, hm⟩ := hbig _ (ENNReal.inv_ne_top.2 h0)
        refine ⟨m, ?_⟩
        calc (1 : ℝ≥0∞) = (X ω)⁻¹ * X ω := (ENNReal.inv_mul_cancel h0 ht).symm
          _ ≤ c ^ m * X ω := by gcongr
      classical
      let m := Nat.find hex
      have hm : 1 ≤ c ^ m * X ω := Nat.find_spec hex
      have hm0 : m ≠ 0 := by
        intro h
        have : 1 ≤ c ^ 0 * X ω := h ▸ hm
        rw [pow_zero, one_mul] at this
        exact absurd this (not_le.2 h1)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have hk' : c ^ k * X ω < 1 := not_le.1 (Nat.find_min hex (by omega : k < m))
      refine mem_iUnion.2 ⟨m, hm, ?_⟩
      show c ^ m * X ω < c
      calc c ^ m * X ω = c * (c ^ k * X ω) := by rw [show m = k + 1 from hk, pow_succ]; ring
        _ < c * 1 := ENNReal.mul_lt_mul_right hc0 hct hk'
        _ = c := mul_one c
  have hnull : P {ω | X ω ≠ 0 ∧ X ω ≠ ⊤} = 0 := by
    refine measure_mono_null hcover (measure_union_null ?_ ?_)
    · exact measure_iUnion_null fun n => by rw [hpos n, hA00]
    · exact measure_iUnion_null hneg
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) hnull
  simp only [mem_setOf_eq, not_or] at hω ⊢
  exact hω

end G1Side
end QuantumZipper
