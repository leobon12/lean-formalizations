/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripMain

/-!
# Aux. lemma 22, chart `E`, step 1: the span form of the chordal hitting theorem

Packet PROVE-SEC5-M (specification §4.1, Aux. lemma 22, pp. 113–115). PROVE-SEC5-L's chordal theorem
`Aux22Strip.ae_exists_hit_of_retarget` is stated for a right list of length `j + 1 + 1 + m` (the span between the
marks of Lean indices `j` and `j + 1`) with Zhan's hypotheses on LP9's transformed word. This file restates it for a
right list of any length, with two consecutive right marks `x_a < x_c` bounding the span, and with the hypotheses
read on the original word as cumulative weights at marks (`Σ_{x_i ≤ x} ρ^R_i`, `Σ_{x ≤ x_i} ρ^L_i`):

* every left cumulative weight, and every right cumulative weight before `x_a`, is at least `κ/2 − 2`;
* the right cumulative weight through `x_a` lies in `(κ/2 − 4, κ/2 − 2)` (Zhan's `|q₊ − q₋| < 2`);
* every right cumulative weight from `x_c` on is at most `κ/2 − 4` (the new lower prefix sums after the old target).

**`ae_exists_hit_of_span`**: almost surely every generating trace reaches a point of `(x_a, x_c)` at a finite time
`t ≤ ζ`, never visiting `ℝ \ {0}` before `t`. The proof reindexes (`n = j + 1 + 1 + m`) and computes LP9's prefix sums
(`sum_Iic_natAdd_retargetρL`: after the old target, `κ − 6 − Σ_{i ≤ l} ρ^R_i`).

`SeedSpanHitStatement κ` (named input, **not proved**) is the same statement for words whose first marks may sit at the
seed `0`; it is the only missing input of the seeded chart-`E` results in `Aux22ChartE.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5

namespace Aux22ChartE

open Strip

/-- A sum over `Iic r` as a sum over all indices. -/
theorem sum_Iic_eq_sum_ite {N : ℕ} (f : Fin N → ℝ) (r : Fin N) :
    ∑ i ∈ Iic r, f i = ∑ i, if i ≤ r then f i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i; simp

/-- **LP9's left prefix sums after the old target**: through the `l`-th new left mark after the original left
marks, the transformed left weights sum to `κ − 6 − Σ_{i ≤ j + 1 + (m − l)} ρ^R_i`. -/
theorem sum_Iic_natAdd_retargetρL (κ : ℝ) {nL j m : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + 1 + m) → ℝ)
    (l : Fin (m + 1)) :
    ∑ i ∈ Iic (Fin.natAdd nL l), LP.retargetρL κ ρL ρR i =
      κ - 6 - ∑ i ∈ Iic (⟨j + 1 + (m - l.val), by omega⟩ : Fin (j + 1 + 1 + m)), ρR i := by
  set T := κ - 6 - ((∑ i, ρL i) + ∑ i, ρR i) with hTdef
  have hL : ∑ i ∈ Iic (Fin.natAdd nL l), LP.retargetρL κ ρL ρR i = (∑ i, ρL i) + (T +
      ∑ q : Fin m, if q.succ ≤ l then ρR (Fin.natAdd (j + 1 + 1) q.rev) else 0) := by
    rw [sum_Iic_eq_sum_ite, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [Fin.le_def]; simp; omega))]
      simp [LP.retargetρL]
    · rw [Fin.sum_univ_succ]
      congr 1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [Fin.le_def]; simp))]
        simp [LP.retargetρL, hTdef]
      · refine Finset.sum_congr rfl fun q _ => ?_
        have e : (Fin.natAdd nL q.succ ≤ Fin.natAdd nL l) = (q.succ ≤ l) := by
          apply propext; simp [Fin.le_def]
        simp only [e]
        simp [LP.retargetρL]
  have hR : ∑ i ∈ Iic (⟨j + 1 + (m - l.val), by omega⟩ : Fin (j + 1 + 1 + m)), ρR i =
      (∑ i : Fin (j + 1 + 1), ρR (Fin.castAdd m i)) +
        ∑ q : Fin m, if q.val + 1 + l.val ≤ m then ρR (Fin.natAdd (j + 1 + 1) q) else 0 := by
    rw [sum_Iic_eq_sum_ite, Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by rw [Fin.le_def]; simp; omega))]
    · refine Finset.sum_congr rfl fun q _ => ?_
      have e : ((Fin.natAdd (j + 1 + 1) q : Fin (j + 1 + 1 + m)) ≤ ⟨j + 1 + (m - l.val), by omega⟩) =
          (q.val + 1 + l.val ≤ m) := by
        apply propext; simp [Fin.le_def]; omega
      simp only [e]
  have hT : ∑ i, ρR i = (∑ i : Fin (j + 1 + 1), ρR (Fin.castAdd m i)) +
      ∑ q : Fin m, ρR (Fin.natAdd (j + 1 + 1) q) := Fin.sum_univ_add _
  have hrev : (∑ q : Fin m, if q.succ ≤ l then ρR (Fin.natAdd (j + 1 + 1) q.rev) else 0) =
      ∑ q : Fin m, if q.val + 1 + l.val ≤ m then 0 else ρR (Fin.natAdd (j + 1 + 1) q) := by
    rw [← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]
    have e : (q.rev.succ ≤ l) = ¬ (q.val + 1 + l.val ≤ m) := by
      apply propext; simp [Fin.le_def]; omega
    simp only [e]
    split_ifs <;> rfl
  have hsplit : ∑ q : Fin m, ρR (Fin.natAdd (j + 1 + 1) q) =
      (∑ q : Fin m, if q.val + 1 + l.val ≤ m then ρR (Fin.natAdd (j + 1 + 1) q) else 0) +
        ∑ q : Fin m, if q.val + 1 + l.val ≤ m then 0 else ρR (Fin.natAdd (j + 1 + 1) q) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> simp
  rw [hL, hR, hrev, hTdef, hT, hsplit]
  ring


/-- For a strictly increasing list, the marks at or left of `x_r` are the indices `≤ r`. -/
theorem filter_le_eq_Iic {N : ℕ} {x : Fin N → ℝ} (hx : StrictMono x) (r : Fin N) :
    univ.filter (fun i => x i ≤ x r) = Finset.Iic r := by
  ext i; simp [hx.le_iff_le]

/-- For a strictly decreasing list, the marks at or right of `x_r` are the indices `≤ r`. -/
theorem filter_ge_eq_Iic {N : ℕ} {x : Fin N → ℝ} (hx : StrictAnti x) (r : Fin N) :
    univ.filter (fun i => x r ≤ x i) = Finset.Iic r := by
  ext i; simp [hx.le_iff_ge]

/-- A prefix sum along `Fin.castLE`. -/
theorem sum_Iic_castLE {N M : ℕ} (h : N ≤ M) (f : Fin M → ℝ) (r : Fin N) :
    ∑ i ∈ Iic (Fin.castLE h r), f i = ∑ i ∈ Iic r, f (Fin.castLE h i) := by
  rw [← Fin.map_castLEEmb_Iic (a := r) h, Finset.sum_map]
  rfl

variable {κ : ℝ} {nL n : ℕ} {xL : Fin nL → ℝ} {xR : Fin n → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin n → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The first contact with the span `(x_a, x_c)` between two consecutive right marks** (chordal form of Aux. lemma
22, `0 < κ ≤ 4`, any number of marks; hypotheses on the original word's cumulative weights). -/
theorem ae_exists_hit_of_span (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hD : LP.IsDistinctForceWord xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ i, 0 < xR i) {ia ic : Fin n} (hac : xR ia < xR ic)
    (hgap : ∀ i, xR i ∉ Ioo (xR ia) (xR ic))
    (hL : ∀ i, κ / 2 - 2 ≤ ∑ i' ∈ univ.filter (fun i' => xL i ≤ xL i'), ρL i')
    (hR1 : ∀ i, xR i < xR ia → κ / 2 - 2 ≤ ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR i), ρR i')
    (hR2 : κ / 2 - 4 < ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR ia), ρR i')
    (hR2' : ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR ia), ρR i' < κ / 2 - 2)
    (hR3 : ∀ i, xR ic ≤ xR i → ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR i), ρR i' ≤ κ / 2 - 4) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η s ≠ z) ∧
        ∃ x : ℝ, xR ia < x ∧ x < xR ic ∧ η t = x := by
  have hsR := hD.2.2
  have hsL := hD.2.1
  have hlt : ia < ic := hsR.lt_iff_lt.1 hac
  have hsucc : ic.val = ia.val + 1 := by
    by_contra hne
    have hlt' : ia.val + 1 < ic.val := by have := Fin.lt_def.1 hlt; omega
    have h1 : ia.val + 1 < n := by omega
    exact hgap ⟨ia.val + 1, h1⟩ ⟨hsR (by rw [Fin.lt_def]; simp), hsR (by rw [Fin.lt_def]; simp; omega)⟩
  simp only [filter_ge_eq_Iic hsL] at hL
  rw [filter_le_eq_Iic hsR] at hR2 hR2'
  obtain ⟨j, m, hn, hja⟩ : ∃ j m, n = j + 1 + 1 + m ∧ ia.val = j := ⟨ia.val, n - ia.val - 2, by omega, rfl⟩
  subst hn
  have hia : ia = Fin.castAdd m (Fin.castSucc (Fin.last j)) := Fin.ext (by simp [hja])
  have hic : ic = LP.retargetIdx (j + 1) m := Fin.ext (by simp [LP.retargetIdx]; omega)
  subst hia hic
  have hpre : HasStripPrefixSums κ (Fin.init (LP.retargetρR ρR)) (LP.retargetρL κ ρL ρR) := by
    refine ⟨fun r => ?_, fun r => ?_⟩
    · have h' : j ≤ j + 1 + 1 + m := by omega
      have e : ∑ i ∈ Iic r, Fin.init (LP.retargetρR ρR) i = ∑ i ∈ Iic (Fin.castLE h' r), ρR i := by
        rw [sum_Iic_castLE]; rfl
      rw [e, ← filter_le_eq_Iic hsR]
      exact hR1 _ (hsR (by rw [Fin.lt_def]; simp))
    · refine Fin.addCases (fun r₀ => ?_) (fun l => ?_) r
      · have h' : nL ≤ nL + (m + 1) := by omega
        have e : ∑ i ∈ Iic (Fin.castAdd (m + 1) r₀), LP.retargetρL κ ρL ρR i = ∑ i ∈ Iic r₀, ρL i := by
          rw [show Fin.castAdd (m + 1) r₀ = Fin.castLE h' r₀ from rfl, sum_Iic_castLE]
          refine Finset.sum_congr rfl fun i _ => ?_
          show LP.retargetρL κ ρL ρR (Fin.castAdd (m + 1) i) = ρL i
          simp [LP.retargetρL]
        rw [e]
        exact hL r₀
      · rw [sum_Iic_natAdd_retargetρL]
        have := hR3 ⟨j + 1 + (m - l.val), by omega⟩ (hsR.monotone (by
          rw [Fin.le_def]; simp [LP.retargetIdx]))
        rw [filter_le_eq_Iic hsR] at this
        linarith
  have hS : chargeMinus (Fin.init (LP.retargetρR ρR)) (LP.retargetρR ρR (Fin.last j)) =
      ∑ i ∈ Iic (Fin.castAdd m (Fin.castSucc (Fin.last j))), ρR i := by
    have h' : j + 1 ≤ j + 1 + 1 + m := by omega
    rw [chargeMinus, show Fin.castAdd m (Fin.castSucc (Fin.last j)) = Fin.castLE h' (Fin.last j) from rfl,
      sum_Iic_castLE, show Finset.Iic (Fin.last j) = Finset.univ by ext; simp [Fin.le_last],
      Fin.sum_univ_castSucc]
    rfl
  have hq : |chargePlus κ (Fin.init (LP.retargetρR ρR)) (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR (Fin.last j)) -
      chargeMinus (Fin.init (LP.retargetρR ρR)) (LP.retargetρR ρR (Fin.last j))| < 2 := by
    have hsum := chargePlus_add_chargeMinus κ (Fin.init (LP.retargetρR ρR)) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR (Fin.last j))
    rw [abs_lt]
    constructor <;> linarith
  exact Aux22Strip.ae_exists_hit_of_retarget hκ hκ4 hE hD hxL hxR hpre hq

/-! ### Seed marks: the named input -/

/-- **Named input: the span form with seed marks** (Aux. lemma 22's chordal core when the first left and right marks
may sit at the seed `0`; PROVE-SEC5-L, "What remains" 2). The hypotheses of `ae_exists_hit_of_span`, except that the
word need not be separated from the seed (`LP.IsDistinctForceWord` allows `x^L_0 = 0 = x^R_0`; the cumulative-weight
conditions then make each seed weight at least `κ/2 − 2`) and the left end of the span is positive. Its proof needs
Zhan's strip endpoint theorem with seed groups (`Sec4.Aux21Statement` at `m = 0`, with lower noncollision on the strip
life), or a restart of the evolution at a positive stopping time with a Borel coding of the hitting event.
**Not proved**; `ae_exists_hit_of_span` is its case without marks at the seed. -/
def SeedSpanHitStatement (κ : ℝ) : Prop :=
  ∀ {nL n : ℕ} (xL : Fin nL → ℝ) (xR : Fin n → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin n → ℝ) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin n → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ia ic : Fin n),
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → LP.IsDistinctForceWord xL xR → 0 < xR ia →
    xR ia < xR ic → (∀ i, xR i ∉ Ioo (xR ia) (xR ic)) →
    (∀ i, κ / 2 - 2 ≤ ∑ i' ∈ univ.filter (fun i' => xL i ≤ xL i'), ρL i') →
    (∀ i, xR i < xR ia → κ / 2 - 2 ≤ ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR i), ρR i') →
    κ / 2 - 4 < ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR ia), ρR i' →
    ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR ia), ρR i' < κ / 2 - 2 →
    (∀ i, xR ic ≤ xR i → ∑ i' ∈ univ.filter (fun i' => xR i' ≤ xR i), ρR i' ≤ κ / 2 - 4) →
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η s ≠ z) ∧
        ∃ x : ℝ, xR ia < x ∧ x < xR ic ∧ η t = x

end Aux22ChartE

end Sec5

end InteractingSLE
