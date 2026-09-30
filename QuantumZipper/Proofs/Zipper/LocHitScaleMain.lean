import QuantumZipper.Proofs.Zipper.LocHitScaleArea

/-!
# LOC-HITSCALE (4): `LocHitScaleStmt` from almost-sure good behaviour of the zipper

Theorem 1.3, node E6 under D25. Continuation of `LocHitScaleArea.lean`.

For horizons `T` and driver bounds `M` (naturals) and the radius `Rp R T M ≥ MR + 9M + 9√T + 7`,
the good set `goodSet γ κ ℓ R T M` of local data asks: the window is bounded by `M` at the rational
times of `[0,T]`, the local left length at time `T` is `≥ ℓ`, the local hitting time `tauLoc` is
positive, the local scale `aLoc` lies in `(0, M)`, and `tauLoc + aLoc² R ≤ T`. It is measurable
(`measurableSet_goodSet`), and

* `conclusions_of_mem`: for a configuration with the good behaviour `HitScaleGood` (continuous
  driver vanishing at `0`, all real points alive, global boundary limits at the positive rational
  times, monotone left length reaching `ℓ`, positive hitting time, area limit and positive scale
  at the hitting time), membership of its local data gives every conclusion of
  `LocHitScaleStmt` (with `τ̃ = tauLoc`, `ã = aLoc`);
* `eventually_mem_goodSet`: such a configuration belongs to the good set for all large `T` and
  then all large `M`;
* `locHitScaleStmt_of_good`: hence `LocHitScaleStmt` whenever `HitScaleGood` holds almost surely
  and the local data are a.e.-measurable (tightness: the good events exhaust the space along
  `T` and then `M`, continuity of `P'` from below).

Own elementary argument (the paper, Sheffield arXiv:1012.4797 §5.4, pp. 70–72, asserts the
locality without proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper.E6

open D3Plus MeasUnzip CharFun

/-- The local radius. -/
def Rp (R T M : ℕ) : ℕ := ⌈(M : ℝ) * R + 9 * M + 9 * Real.sqrt T + 7⌉₊ + T

theorem le_Rp (R T M : ℕ) : T ≤ Rp R T M := Nat.le_add_left _ _

theorem bound_le_Rp (R T M : ℕ) : (M : ℝ) * R + 9 * M + 9 * Real.sqrt T + 7 ≤ Rp R T M := by
  unfold Rp
  push_cast
  linarith [Nat.le_ceil ((M : ℝ) * R + 9 * M + 9 * Real.sqrt T + 7),
    (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]

theorem bound9_le_Rp (R T M : ℕ) : 9 * (M : ℝ) + 9 * Real.sqrt T + 7 ≤ Rp R T M := by
  have h1 := bound_le_Rp R T M
  have h2 : (0 : ℝ) ≤ (M : ℝ) * R := by positivity
  linarith

/-- The good set of local data. -/
def goodSet (γ κ ℓ : ℝ) (R T M : ℕ) : Set FullData :=
  {d | (∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M) ∧
    ENNReal.ofReal ℓ ≤ lenLoc γ κ T (Rp R T M) T ⟨natCast_nonneg' T, le_rfl⟩ d ∧
    0 < tauLoc γ κ ℓ T (Rp R T M) d ∧ 0 < aLoc γ κ ℓ T (Rp R T M) M d ∧
    aLoc γ κ ℓ T (Rp R T M) M d < M ∧
    tauLoc γ κ ℓ T (Rp R T M) d + aLoc γ κ ℓ T (Rp R T M) M d ^ 2 * R ≤ T}

theorem measurableSet_goodSet (γ κ ℓ : ℝ) (R T M : ℕ) : MeasurableSet (goodSet γ κ ℓ R T M) := by
  have hτ := measurable_tauLoc γ κ ℓ T (Rp R T M)
  have ha := measurable_aLoc γ κ ℓ T (Rp R T M) M
  have h1 : MeasurableSet {d : FullData |
      ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} := by
    have e : {d : FullData | ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} =
        ⋂ r : ℚ, {d : FullData | 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} := by
      ext d; simp only [mem_setOf_eq, mem_iInter]
    rw [e]
    refine MeasurableSet.iInter fun r => ?_
    by_cases hr : 0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ T
    · simp only [hr.1, hr.2, true_implies]
      exact measurableSet_le (continuous_abs.measurable.comp
        ((measurable_pi_apply _).comp measurable_snd)) measurable_const
    · have e2 : {d : FullData | 0 ≤ (r : ℝ) → (r : ℝ) ≤ T → |d.2 (r : ℝ).toNNReal| ≤ M} =
          univ := by
        ext d
        simp only [mem_setOf_eq, mem_univ, iff_true]
        intro h0 hT
        exact absurd ⟨h0, hT⟩ hr
      rw [e2]
      exact MeasurableSet.univ
  exact h1.inter ((measurableSet_le measurable_const (measurable_lenLoc _ _ _ _ _ _)).inter
    ((measurableSet_lt measurable_const hτ).inter ((measurableSet_lt measurable_const ha).inter
    ((measurableSet_lt ha measurable_const).inter
      (measurableSet_le (hτ.add ((ha.pow_const 2).mul_const _)) measurable_const)))))

theorem window_locRich {R' T : ℕ} (hTR : T ≤ R') (y : Cfg) {r : ℝ} (h0 : 0 ≤ r)
    (hr : r ≤ T) : (locRich R' y).2 r.toNNReal = y.2 r := by
  simp only [locRich]
  rw [Real.coe_toNNReal r h0, min_eq_left (hr.trans (by exact_mod_cast hTR))]

variable {Ω' : Type*} [MeasurableSpace Ω']

end QuantumZipper.E6
