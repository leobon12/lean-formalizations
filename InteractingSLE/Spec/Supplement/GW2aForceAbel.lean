/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# The drift of the nearest force gap near a collision: Abel summation over the colliding group

Packet PROVE-GW2A-FORCE (input of `FlowFixedTimeInteriorStatement`). Deterministic.

For gaps `0 < u₀ ≤ u₁ ≤ … ≤ u_{m−1}` and weights `ρ`, Abel summation gives
`∑_{j<m} ρ_j / u_j = ∑_{k<m−1} (1/u_k − 1/u_{k+1}) S_k + S_{m−1}/u_{m−1}` with partial sums `S_k = ∑_{i≤k} ρ_i`. The
coefficients are nonnegative and vanish where `u_k = u_{k+1}` (merged marks). Hence if `c ≤ S_k` at every *break*
`k` (the last index, or `u_k < u_{k+1}`), then `∑_{j<m} ρ_j/u_j ≥ c / u₀` (`le_sum_div_of_breaks`). With `c = c₀ − 2`
this is the lower bound `c₀ / u₀` for the drift `2/u₀ + ∑ ρ_j/u_j` of the nearest gap `u₀` coming from the colliding
group; the separated marks contribute a bounded drift.

* `le_sum_div_of_breaks` (over `ℕ`), `le_sum_div_of_breaks_fin` (the first `m` marks of a `Fin n`-indexed word);
* `Sec2.IsForcePath.vR_sub_vR_le_of_le`: same-side spreads are nonincreasing in time; merged marks stay merged
  (`vR_eq_vR_of_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2aForce

/-! ### Abel summation over a prefix -/

/-- The partial-sum form of the Abel bound, before the last break. -/
theorem le_sum_div_aux (ρ u : ℕ → ℝ) (c : ℝ) (m : ℕ) (hpos : ∀ i < m, 0 < u i)
    (hmono : ∀ i, i + 1 < m → u i ≤ u (i + 1))
    (hcond : ∀ k, k + 1 < m → u k < u (k + 1) → c ≤ ∑ i ∈ range (k + 1), ρ i) :
    ∀ n, 1 ≤ n → n ≤ m →
      c * (1 / u 0 - 1 / u (n - 1)) + (∑ i ∈ range n, ρ i) / u (n - 1) ≤ ∑ i ∈ range n, ρ i / u i := by
  intro n hn1 hnm
  induction n, hn1 using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have ih' := ih (by omega)
    have hn0 : n - 1 + 1 = n := by omega
    have hu1 : 0 < u (n - 1) := hpos _ (by omega)
    have hu2 : 0 < u n := hpos _ (by omega)
    have hle : u (n - 1) ≤ u n := by
      have := hmono (n - 1) (by omega); rwa [hn0] at this
    rw [sum_range_succ, sum_range_succ, Nat.add_sub_cancel]
    have key : 0 ≤ (1 / u (n - 1) - 1 / u n) * ((∑ i ∈ range n, ρ i) - c) := by
      rcases hle.lt_or_eq with hlt | heq
      · refine mul_nonneg ?_ ?_
        · rw [sub_nonneg]; exact one_div_le_one_div_of_le hu1 hlt.le
        · have := hcond (n - 1) (by omega) (by rwa [hn0])
          rw [hn0] at this; linarith
      · rw [heq, sub_self, zero_mul]
    have e1 : (∑ i ∈ range n, ρ i + ρ n) / u n = (∑ i ∈ range n, ρ i) / u n + ρ n / u n := add_div _ _ _
    rw [e1]
    have e2 : (∑ i ∈ range n, ρ i) / u (n - 1) = (∑ i ∈ range n, ρ i) * (1 / u (n - 1)) := by ring
    have e3 : (∑ i ∈ range n, ρ i) / u n = (∑ i ∈ range n, ρ i) * (1 / u n) := by ring
    rw [e2] at ih'
    rw [e3]
    nlinarith [key, ih']

/-- **The Abel bound** (`ℕ`-indexed): for positive nondecreasing gaps `u₀ ≤ … ≤ u_{m−1}`, if `c ≤ S_k` at every break
`k < m` (the last index or `u_k < u_{k+1}`), then `c / u₀ ≤ ∑_{j<m} ρ_j / u_j`. -/
theorem le_sum_div_of_breaks (ρ u : ℕ → ℝ) (c : ℝ) (m : ℕ) (hm : 0 < m) (hpos : ∀ i < m, 0 < u i)
    (hmono : ∀ i, i + 1 < m → u i ≤ u (i + 1))
    (hcond : ∀ k < m, (k + 1 = m ∨ u k < u (k + 1)) → c ≤ ∑ i ∈ range (k + 1), ρ i) :
    c / u 0 ≤ ∑ i ∈ range m, ρ i / u i := by
  have h := le_sum_div_aux ρ u c m hpos hmono (fun k hk hlt => hcond k (by omega) (Or.inr hlt)) m hm le_rfl
  have hlast := hcond (m - 1) (by omega) (Or.inl (by omega))
  rw [Nat.sub_add_cancel hm] at hlast
  have hu : 0 < u (m - 1) := hpos _ (by omega)
  have : c * (1 / u 0 - 1 / u (m - 1)) + c / u (m - 1) ≤
      c * (1 / u 0 - 1 / u (m - 1)) + (∑ i ∈ range m, ρ i) / u (m - 1) := by
    gcongr
  have e : c * (1 / u 0 - 1 / u (m - 1)) + c / u (m - 1) = c / u 0 := by ring
  linarith

/-! ### From `Fin n` to `ℕ` -/

/-- Extension of a `Fin n`-indexed family by `0`. -/
def extNat {n : ℕ} (f : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then f ⟨i, h⟩ else 0

theorem extNat_fin {n : ℕ} (f : Fin n → ℝ) (j : Fin n) : extNat f j = f j := by
  simp [extNat, j.isLt]

/-- A sum over the first `m ≤ n` indices of `Fin n` is a sum over `range m`. -/
theorem sum_filter_lt_eq_sum_range {n : ℕ} (g : Fin n → ℝ) {m : ℕ} (hm : m ≤ n) :
    ∑ j ∈ univ.filter (fun j : Fin n => j.val < m), g j = ∑ i ∈ range m, extNat g i := by
  rw [sum_filter]
  have h1 : ∑ j : Fin n, (if j.val < m then g j else 0) =
      ∑ j : Fin n, (fun i : ℕ => if i < m then extNat g i else 0) j.val := by
    refine sum_congr rfl fun j _ => ?_
    simp only [extNat_fin]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < m then extNat g i else 0) n, ← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, Finset.mem_range]
  constructor
  · intro hh; exact hh.2
  · intro hh; exact ⟨by omega, hh⟩

/-- **The Abel bound for the first `m` marks of a `Fin n`-indexed word.** -/
theorem le_sum_div_of_breaks_fin {n : ℕ} (ρ u : Fin n → ℝ) (c : ℝ) {m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (hpos : ∀ j : Fin n, j.val < m → 0 < u j) (hmono : ∀ i j : Fin n, i ≤ j → j.val < m → u i ≤ u j)
    (hcond : ∀ k : Fin n, k.val < m → (k.val + 1 = m ∨ ∀ k' : Fin n, k'.val = k.val + 1 → u k < u k') →
      c ≤ ∑ i ∈ univ.filter (fun i : Fin n => i ≤ k), ρ i) :
    c / u ⟨0, by omega⟩ ≤ ∑ j ∈ univ.filter (fun j : Fin n => j.val < m), ρ j / u j := by
  have hsum : ∑ j ∈ univ.filter (fun j : Fin n => j.val < m), ρ j / u j =
      ∑ i ∈ range m, extNat ρ i / extNat u i := by
    rw [sum_filter_lt_eq_sum_range (fun j => ρ j / u j) hmn]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i < n := lt_of_lt_of_le (mem_range.1 hi) hmn
    simp [extNat, hi']
  rw [hsum]
  have h0 : u ⟨0, by omega⟩ = extNat u 0 := by simp [extNat, show 0 < n by omega]
  rw [h0]
  refine le_sum_div_of_breaks (extNat ρ) (extNat u) c m hm (fun i hi => ?_) (fun i hi => ?_) (fun k hk hbr => ?_)
  · have hi' : i < n := by omega
    simpa [extNat, hi'] using hpos ⟨i, hi'⟩ hi
  · have hi' : i + 1 < n := by omega
    have := hmono ⟨i, by omega⟩ ⟨i + 1, hi'⟩ (by simp [Fin.le_def]) hi
    simpa [extNat, hi', show i < n by omega] using this
  · have hk' : k < n := by omega
    have hbr' : k + 1 = m ∨ ∀ k' : Fin n, k'.val = k + 1 → u ⟨k, hk'⟩ < u k' := by
      rcases hbr with h | h
      · exact Or.inl h
      · refine Or.inr fun k' hk'v => ?_
        have hk1 : k + 1 < n := by omega
        have e : k' = ⟨k + 1, hk1⟩ := Fin.ext hk'v
        subst e
        simpa [extNat, hk1, hk'] using h
    have := hcond ⟨k, hk'⟩ hk hbr'
    have hps : ∑ i ∈ univ.filter (fun i : Fin n => i ≤ ⟨k, hk'⟩), ρ i = ∑ i ∈ range (k + 1), extNat ρ i := by
      have := sum_filter_lt_eq_sum_range ρ (m := k + 1) (by omega)
      rw [← this]
      congr 1
      ext i
      simp only [mem_filter, Finset.mem_univ, true_and]
      rw [Fin.le_def]
      show i.val ≤ k ↔ i.val < k + 1
      omega
    rwa [hps] at this

end GW2aForce

end Theorem14

/-! ### Same-side spreads between two times -/

namespace Sec2

namespace IsForcePath

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Same-side spreads are nonincreasing in time** (right side): for `i ≤ j` and `a ≤ t < ζ`,
`v^{j,R}_t − v^{i,R}_t ≤ v^{j,R}_a − v^{i,R}_a`. -/
theorem vR_sub_vR_le_of_le (h : IsForcePath xL xR ρL ρR w vL vR ζ) {a t : ℝ≥0} (hat : a ≤ t)
    (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nR} (hij : i ≤ j) :
    vR j t - vR i t ≤ vR j a - vR i a := by
  have hat' : (a : ℝ) ≤ t := by exact_mod_cast hat
  have hsub : uIcc (a : ℝ) t ⊆ uIcc 0 (t : ℝ) := by
    rw [uIcc_of_le hat', uIcc_of_le (NNReal.coe_nonneg t)]
    exact Icc_subset_Icc (NNReal.coe_nonneg a) le_rfl
  have hint := ((h.intervalIntegrable_forceR ht j).sub (h.intervalIntegrable_forceR ht i)).mono_set hsub
  have key : vR j t - vR i t - (vR j a - vR i a) = ∫ s in (a : ℝ)..t,
      (2 / (vR j s.toNNReal - w s.toNNReal) - 2 / (vR i s.toNNReal - w s.toNNReal)) := by
    rw [intervalIntegral.integral_sub ((h.intervalIntegrable_forceR ht j).mono_set hsub)
      ((h.intervalIntegrable_forceR ht i).mono_set hsub), ← h.vR_sub hat ht j, ← h.vR_sub hat ht i]
    ring
  have hae : (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal) - 2 / (vR i s.toNNReal - w s.toNNReal))
      ≤ᵐ[volume.restrict (Icc (a : ℝ) t)] fun _ => 0 := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionR i)] with s hs hsI
    have hsI' : s ∈ Icc (0 : ℝ) t := ⟨(NNReal.coe_nonneg a).trans hsI.1, hsI.2⟩
    have hlt := toNNReal_lt_of_mem_Icc ht hsI'
    have hne : w s.toNNReal ≠ vR i s.toNNReal := fun he => hs ⟨hsI'.1, hlt, he⟩
    have hp : 0 < vR i s.toNNReal - w s.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hlt i) hne)
    have hpq : vR i s.toNNReal - w s.toNNReal ≤ vR j s.toNNReal - w s.toNNReal :=
      sub_le_sub_right (h.monotone_vR hlt hij) _
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hp hpq
    linarith
  have hle : ∫ s in (a : ℝ)..t,
      (2 / (vR j s.toNNReal - w s.toNNReal) - 2 / (vR i s.toNNReal - w s.toNNReal)) ≤ 0 := by
    have := intervalIntegral.integral_mono_ae_restrict hat' hint intervalIntegrable_const hae
    simpa using this
  linarith

/-- **Merged marks stay merged**: if `v^{i,R}_a = v^{j,R}_a` then `v^{i,R}_t = v^{j,R}_t` for `a ≤ t < ζ`. -/
theorem vR_eq_vR_of_eq (h : IsForcePath xL xR ρL ρR w vL vR ζ) {a t : ℝ≥0} (hat : a ≤ t)
    (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nR} (hij : i ≤ j) (heq : vR i a = vR j a) : vR i t = vR j t := by
  have h1 := h.vR_sub_vR_le_of_le hat ht hij
  have h2 := h.monotone_vR ht hij
  linarith

end IsForcePath

end Sec2

end InteractingSLE
