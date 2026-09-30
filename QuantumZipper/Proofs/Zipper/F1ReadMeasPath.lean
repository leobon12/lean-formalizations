import QuantumZipper.Proofs.Zipper.F1Read

/-!
# READLEN, path part (1): a measurable continuity certificate for the dyadic read-off

Theorem 1.3, node F1d input (d) (`F1.ReadLenAEMeasStmt`). The driver of the `configLawFull` data
is read through its dyadic values, `readDrv p = B4d.pathExt (p ∘ toNNReal)`. Continuity of a path
is not an event of the product σ-algebra on `ℝ≥0 → ℝ`, but continuity of its dyadic read-off
follows from a *countable* certificate:

* `DyUC p`: on each window `[0, N]` the values of `p` at the non-negative dyadic points are
  uniformly continuous (quantifiers over `ℕ` only); `measurableSet_dyUC`.
* `continuous_readDrv_of_dyUC`: `DyUC p → Continuous (readDrv p)` (the dyadic roundings
  `⌊2ⁿt⌋/2ⁿ` form Cauchy sequences, and the uniform modulus passes to the limit).
* `dyUC_of_continuous`: every continuous `p` satisfies `DyUC p` (uniform continuity on compacts).
* `readDrv_zero`: `readDrv p 0 = p 0`.

Own elementary arguments (standard extension of a uniformly continuous function from a dense set).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

/-- The dyadic point `k / 2ⁿ`. -/
def dy (n k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ n

/-- The value of a path at the dyadic point `k / 2ⁿ`. -/
def dyv (p : ℝ≥0 → ℝ) (n k : ℕ) : ℝ := p (dy n k).toNNReal

/-- **The countable continuity certificate**: uniform continuity on the dyadics of each window. -/
def DyUC (p : ℝ≥0 → ℝ) : Prop :=
  ∀ N m : ℕ, ∃ j : ℕ, ∀ n k n' k' : ℕ, dy n k ≤ N → dy n' k' ≤ N →
    |dy n k - dy n' k'| ≤ 1 / ((j : ℝ) + 1) → |dyv p n k - dyv p n' k'| ≤ 1 / ((m : ℝ) + 1)

theorem measurableSet_dyUC : MeasurableSet {p : ℝ≥0 → ℝ | DyUC p} := by
  refine measurableSet_setOfPred.2 ?_
  refine Measurable.forall fun N => Measurable.forall fun m => Measurable.exists fun j =>
    Measurable.forall fun n => Measurable.forall fun k => Measurable.forall fun n' =>
      Measurable.forall fun k' => measurable_const.imp (measurable_const.imp
        (measurable_const.imp ?_))
  refine measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)
  exact continuous_abs.measurable.comp (Measurable.sub (f := fun a : ℝ≥0 → ℝ => dyv a n k)
    (g := fun a => dyv a n' k') (measurable_pi_apply _) (measurable_pi_apply _))

theorem dy_nonneg (n k : ℕ) : 0 ≤ dy n k := by unfold dy; positivity

/-- The rounding index `⌊2ⁿ t⌋₊`. -/
def rdx (n : ℕ) (t : ℝ) : ℕ := (⌊(2 : ℝ) ^ n * t⌋).toNat

theorem readDrv_seq (p : ℝ≥0 → ℝ) (n : ℕ) (t : ℝ) :
    (fun r : ℝ => p r.toNNReal) (dyadicRound n t) = dyv p n (rdx n t) := by
  unfold dyv rdx dy
  simp only
  congr 1
  rcases le_or_gt 0 ⌊(2 : ℝ) ^ n * t⌋ with h | h
  · have e : ((⌊(2 : ℝ) ^ n * t⌋.toNat : ℕ) : ℝ) = ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [e, dyadicRound]
  · rw [Int.toNat_eq_zero.2 h.le, Nat.cast_zero, zero_div, Real.toNNReal_zero]
    apply Real.toNNReal_of_nonpos
    unfold dyadicRound
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h.le) (by positivity)

theorem abs_dy_rdx_sub_le (n : ℕ) (t : ℝ) :
    |dy n (rdx n t) - max t 0| ≤ 1 / (2 : ℝ) ^ n := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  unfold dy rdx
  rcases le_or_gt 0 ⌊(2 : ℝ) ^ n * t⌋ with h | h
  · have e : ((⌊(2 : ℝ) ^ n * t⌋.toNat : ℕ) : ℝ) = ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    have ht : 0 ≤ t := by
      have h1 := Int.floor_le ((2 : ℝ) ^ n * t)
      have h2 : (0 : ℝ) ≤ ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) := by exact_mod_cast h
      nlinarith
    rw [e, max_eq_left ht]
    have h1 := Int.floor_le ((2 : ℝ) ^ n * t)
    have h2 := Int.lt_floor_add_one ((2 : ℝ) ^ n * t)
    have key : ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) / (2 : ℝ) ^ n - t =
        (((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) - (2 : ℝ) ^ n * t) / (2 : ℝ) ^ n := by
      field_simp
    rw [key, abs_div, abs_of_pos hq, div_le_div_iff_of_pos_right hq, abs_le]
    constructor <;> linarith
  · have ht : t < 0 := by
      by_contra hc
      push Not at hc
      exact absurd (Int.floor_nonneg.2 (by positivity)) (not_le.2 h)
    rw [Int.toNat_eq_zero.2 h.le, Nat.cast_zero, zero_div, max_eq_right ht.le, sub_zero,
      abs_zero]
    positivity

theorem dy_rdx_le (n : ℕ) (t : ℝ) : dy n (rdx n t) ≤ max t 0 := by
  have hq : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  unfold dy rdx
  rcases le_or_gt 0 ⌊(2 : ℝ) ^ n * t⌋ with h | h
  · have e : ((⌊(2 : ℝ) ^ n * t⌋.toNat : ℕ) : ℝ) = ((⌊(2 : ℝ) ^ n * t⌋ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [e, div_le_iff₀ hq]
    have h1 := Int.floor_le ((2 : ℝ) ^ n * t)
    nlinarith [le_max_left t 0, le_max_right t 0]
  · rw [Int.toNat_eq_zero.2 h.le, Nat.cast_zero, zero_div]
    exact le_max_right _ _

theorem eventually_inv_pow_le {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, 1 / (2 : ℝ) ^ n ≤ ε := by
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N₀, fun n hn => ?_⟩
  rw [← one_div_pow]
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans hN₀.le

/-- The key estimate from the certificate. -/
theorem dyUC_est {p : ℝ≥0 → ℝ} (h : DyUC p) (N m : ℕ) :
    ∃ δ > 0, ∀ s t : ℝ, s ≤ N → t ≤ N → ∀ n n' : ℕ,
      1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ n' + |max s 0 - max t 0| ≤ δ →
      |dyv p n (rdx n s) - dyv p n' (rdx n' t)| ≤ 1 / ((m : ℝ) + 1) := by
  obtain ⟨j, hj⟩ := h N m
  refine ⟨1 / ((j : ℝ) + 1), by positivity, fun s t hs ht n n' hδ => hj n _ n' _ ?_ ?_ ?_⟩
  · exact (dy_rdx_le n s).trans (max_le hs (Nat.cast_nonneg N))
  · exact (dy_rdx_le n' t).trans (max_le ht (Nat.cast_nonneg N))
  · have h1 := abs_dy_rdx_sub_le n s
    have h2 := abs_dy_rdx_sub_le n' t
    have e : dy n (rdx n s) - dy n' (rdx n' t) =
        (dy n (rdx n s) - max s 0) + (max s 0 - max t 0) - (dy n' (rdx n' t) - max t 0) := by
      ring
    have h3 := abs_sub ((dy n (rdx n s) - max s 0) + (max s 0 - max t 0))
      (dy n' (rdx n' t) - max t 0)
    have h4 := abs_add_le (dy n (rdx n s) - max s 0) (max s 0 - max t 0)
    rw [e]
    linarith

theorem readDrv_eq_limUnder (p : ℝ≥0 → ℝ) (t : ℝ) :
    readDrv p t = limUnder atTop fun n => dyv p n (rdx n t) := by
  unfold readDrv B4d.pathExt
  simp only [readDrv_seq]

theorem tendsto_readDrv_of_dyUC {p : ℝ≥0 → ℝ} (h : DyUC p) (t : ℝ) :
    Tendsto (fun n => dyv p n (rdx n t)) atTop (𝓝 (readDrv p t)) := by
  have hc : CauchySeq fun n => dyv p n (rdx n t) := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨δ, hδ, hest⟩ := dyUC_est h ⌈t⌉₊ m
    obtain ⟨N₀, hN₀⟩ := eventually_inv_pow_le (half_pos hδ)
    refine ⟨N₀, fun n hn n' hn' => ?_⟩
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hest t t (Nat.le_ceil t) (Nat.le_ceil t) n n' ?_) hm
    rw [sub_self, abs_zero, add_zero]
    linarith [hN₀ n hn, hN₀ n' hn']
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  rwa [readDrv_eq_limUnder, hL.limUnder_eq]

/-- **The certificate gives a continuous read-off.** -/
theorem continuous_readDrv_of_dyUC {p : ℝ≥0 → ℝ} (h : DyUC p) : Continuous (readDrv p) := by
  refine Metric.continuous_iff.2 fun t ε hε => ?_
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨δ, hδ, hest⟩ := dyUC_est h (⌈t⌉₊ + 1) m
  refine ⟨min 1 (δ / 2), lt_min one_pos (half_pos hδ), fun s hs => ?_⟩
  have hs1 : |s - t| < 1 := (Real.dist_eq s t ▸ hs).trans_le (min_le_left _ _)
  have hs2 : |s - t| < δ / 2 := (Real.dist_eq s t ▸ hs).trans_le (min_le_right _ _)
  have hsN : s ≤ ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast; linarith [Nat.le_ceil t, (abs_lt.1 hs1).2]
  have htN : t ≤ ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil t]
  have hmax : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
  obtain ⟨N₀, hN₀⟩ := eventually_inv_pow_le (show 0 < (δ / 2 - |s - t|) / 2 by linarith)
  have hev : ∀ᶠ n in atTop, |dyv p n (rdx n s) - dyv p n (rdx n t)| ≤ 1 / ((m : ℝ) + 1) :=
    eventually_atTop.2 ⟨N₀, fun n hn => hest s t hsN htN n n (by linarith [hN₀ n hn])⟩
  have hlim : Tendsto (fun n => |dyv p n (rdx n s) - dyv p n (rdx n t)|) atTop
      (𝓝 |readDrv p s - readDrv p t|) :=
    ((tendsto_readDrv_of_dyUC h s).sub (tendsto_readDrv_of_dyUC h t)).abs
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (le_of_tendsto hlim hev) hm

/-- **Continuous paths carry the certificate.** -/
theorem dyUC_of_continuous {p : ℝ≥0 → ℝ} (hp : Continuous p) : DyUC p := by
  intro N m
  set g : ℝ → ℝ := fun r => p r.toNNReal with hg
  have hgc : Continuous g := hp.comp continuous_real_toNNReal
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := N)).uniformContinuousOn_of_continuous
    hgc.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc (1 / ((m : ℝ) + 1)) (by positivity)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
  refine ⟨j, fun n k n' k' h1 h2 h3 => ?_⟩
  have := hδ' (dy n k) ⟨dy_nonneg n k, h1⟩ (dy n' k') ⟨dy_nonneg n' k', h2⟩
    (by rw [Real.dist_eq]; exact h3.trans_lt hj)
  rw [Real.dist_eq] at this
  exact this.le

theorem readDrv_zero (p : ℝ≥0 → ℝ) : readDrv p 0 = p 0 := by
  have h : ∀ n, dyv p n (rdx n 0) = p 0 := by
    intro n
    simp [dyv, rdx, dy]
  rw [readDrv_eq_limUnder]
  simp only [h]
  exact tendsto_const_nhds.limUnder_eq

/-- The path part of the good data: the continuity certificate (hence a continuous read-off,
`continuous_readDrv_of_dyUC`), start at `0`, every real `x ≠ 0` alive up to time `1`. -/
def PathGood (p : ℝ≥0 → ℝ) : Prop :=
  DyUC p ∧ readDrv p 0 = 0 ∧
    ∀ x : ℝ, x ≠ 0 → ∃ u, IsForwardSol (readDrv p) (x : ℂ) 1 u

end F1
end QuantumZipper
