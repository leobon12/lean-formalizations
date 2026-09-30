import QuantumZipper.Proofs.Thm11.ExtMeas
import QuantumZipper.Proofs.Thm11.ExtMeasCont
import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# THM11-AD8: the dyadic floor of the swallowing time (task EXT-MEAS), part 2

Deterministic lemmas about the objects of `ExtMeas.lean`: on the hull at time `T`, the swallowing
time `τ(p) = (swallowTime (drive κ B p.2) p.1).toReal` is a positive real (`tauAt`), membership
in the hull at time `t ≥ 0` is `τ ≤ t`, and the level-`j` dyadic floor `cellK` of `τ` is the
unique grid index whose cell `[k/2^j, (k+1)/2^j)` contains `τ`.  Consequently the finite sums
`dfloor`/`dval` (which are measurable by construction) are the floor itself and the field value
there, and the floor converges to `τ` from below.

Own elementary proof (no source needed): dyadic-grid bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Classical
open scoped NNReal ENNReal Topology
open QuantumZipper.NonSwallow

namespace QuantumZipper
namespace Thm11Asm

section Floor

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {κ T : ℝ}

/-- The swallowing time of `p.1` under the driver `drive κ B p.2`, as a real number. -/
noncomputable def tauAt (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (p : ℂ × Ω) : ℝ :=
  (swallowTime (drive κ B p.2) p.1).toReal

/-- On the hull at time `T ≥ 0`, `swallowTime` is `ENNReal.ofReal (tauAt κ B p)`, and `tauAt` is
positive and at most `T`. -/
theorem tauAt_spec {p : ℂ × Ω} (hW : Continuous (drive κ B p.2)) (hT : 0 ≤ T)
    (hp : p.1 ∈ fwdHull (drive κ B p.2) T) :
    swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p) ∧
      0 < tauAt κ B p ∧ tauAt κ B p ≤ T := by
  obtain ⟨σ, hσT, hσ⟩ := FwdClock.swallowTime_eq_of_mem_fwdHull hW hp
  have hpos : 0 < σ := ENNReal.ofReal_pos.mp (hσ ▸ swallowTime_pos hW hp.1)
  have hto : tauAt κ B p = σ := by rw [tauAt, hσ, ENNReal.toReal_ofReal hpos.le]
  exact ⟨by rw [hto, hσ], by rw [hto]; exact hpos, by rw [hto]; exact hσT⟩

/-- Membership in the forward hull at a nonnegative time, in terms of `tauAt`. -/
theorem mem_hull_iff_tauAt {p : ℂ × Ω} {t : ℝ}
    (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p)) (hz : 0 < p.1.im)
    (ht0 : 0 ≤ t) : p.1 ∈ fwdHull (drive κ B p.2) t ↔ tauAt κ B p ≤ t :=
  MeasCont.mem_fwdHull_ofReal_iff hz hσ ht0

/-- At nonnegative times below `tauAt`, the point is not swallowed. -/
theorem not_mem_hull_of_lt_tauAt {p : ℂ × Ω} {t : ℝ}
    (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p)) (hz : 0 < p.1.im)
    (ht0 : 0 ≤ t) (ht : t < tauAt κ B p) : p.1 ∉ fwdHull (drive κ B p.2) t :=
  MeasCont.not_mem_fwdHull_of_lt_tau hz hσ ht0 ht

/-- The level-`j` grid index whose cell contains `tauAt κ B p`. -/
noncomputable def cellK (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (j : ℕ) (p : ℂ × Ω) : ℕ :=
  Nat.ceil (2 ^ j * tauAt κ B p) - 1

/-- The grid index of the floor lies strictly below `tauAt` (as a real number, before dividing). -/
theorem cellK_lt_mul {p : ℂ × Ω} (hτ0 : 0 < tauAt κ B p) (j : ℕ) :
    ((cellK κ B j p : ℕ) : ℝ) < 2 ^ j * tauAt κ B p := by
  have h1 : (1 : ℕ) ≤ Nat.ceil (2 ^ j * tauAt κ B p) :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 ^ j * tauAt κ B p by positivity)
  rw [cellK, Nat.cast_sub h1, Nat.cast_one]
  linarith

/-- The next grid point is at least `tauAt` (as a real number, before dividing). -/
theorem cellK_le_mul {p : ℂ × Ω} (hτ0 : 0 < tauAt κ B p) (j : ℕ) :
    2 ^ j * tauAt κ B p ≤ ((cellK κ B j p + 1 : ℕ) : ℝ) := by
  have h1 : (1 : ℕ) ≤ Nat.ceil (2 ^ j * tauAt κ B p) :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  rw [cellK, Nat.sub_add_cancel h1]
  exact Nat.le_ceil _

/-- **The cell of the dyadic floor**: `dpt j (cellK) ≤ tauAt < dpt j (cellK + 1)`. -/
theorem cellK_spec {p : ℂ × Ω} (hτ0 : 0 < tauAt κ B p) (j : ℕ) :
    dpt j (cellK κ B j p) < tauAt κ B p ∧ tauAt κ B p ≤ dpt j (cellK κ B j p + 1) := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  constructor
  · rw [dpt, div_lt_iff₀ h2, mul_comm]
    exact cellK_lt_mul hτ0 j
  · rw [dpt, le_div_iff₀ h2, mul_comm]
    exact cellK_le_mul hτ0 j

/-- **Uniqueness of the cell index**. -/
theorem cellK_unique {p : ℂ × Ω} (hτ0 : 0 < tauAt κ B p) {j k : ℕ}
    (hk : dpt j k < tauAt κ B p) (hk' : tauAt κ B p ≤ dpt j (k + 1)) : k = cellK κ B j p := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have h1 : (k : ℝ) < 2 ^ j * tauAt κ B p := by
    have := (div_lt_iff₀ h2).mp (by simpa only [dpt] using hk)
    rwa [mul_comm] at this
  have h2' : 2 ^ j * tauAt κ B p ≤ ((k : ℕ) : ℝ) + 1 := by
    have h := (le_div_iff₀ h2).mp (by simpa only [dpt] using hk')
    rw [mul_comm] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have h3 := cellK_lt_mul hτ0 j
  have h4 := cellK_le_mul hτ0 j
  have hcast : (((cellK κ B j p + 1 : ℕ)) : ℝ) = ((cellK κ B j p : ℕ) : ℝ) + 1 := by
    push_cast; ring
  rw [hcast] at h4
  have h5 : k ≤ cellK κ B j p := by
    have : (k : ℝ) < ((cellK κ B j p : ℕ) : ℝ) + 1 := by linarith
    exact Nat.le_of_lt_succ (by exact_mod_cast this)
  have h6 : cellK κ B j p ≤ k := by
    have : ((cellK κ B j p : ℕ) : ℝ) < (k : ℝ) + 1 := by linarith
    exact Nat.le_of_lt_succ (by exact_mod_cast this)
  omega

/-- The cell condition of `dfloor`/`dval`, in terms of `tauAt` (`⇒`). -/
theorem cell_iff_mp {p : ℂ × Ω} (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p))
    {j k : ℕ} (hcon : p.1 ∉ fwdHull (drive κ B p.2) (dpt j k) ∧
      p.1 ∈ fwdHull (drive κ B p.2) (dpt j (k + 1))) :
    dpt j k < tauAt κ B p ∧ tauAt κ B p ≤ dpt j (k + 1) := by
  have hz : 0 < p.1.im := hcon.2.1
  refine ⟨?_, (mem_hull_iff_tauAt hσ hz (dpt_nonneg j (k + 1))).mp hcon.2⟩
  by_contra hle
  exact hcon.1 ((mem_hull_iff_tauAt hσ hz (dpt_nonneg j k)).mpr (not_lt.mp hle))

/-- The cell condition of `dfloor`/`dval`, in terms of `tauAt` (`⇐`). -/
theorem cell_iff_mpr {p : ℂ × Ω} (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p))
    (hz : 0 < p.1.im) {j k : ℕ} (h : dpt j k < tauAt κ B p ∧ tauAt κ B p ≤ dpt j (k + 1)) :
    p.1 ∉ fwdHull (drive κ B p.2) (dpt j k) ∧
      p.1 ∈ fwdHull (drive κ B p.2) (dpt j (k + 1)) :=
  ⟨not_mem_hull_of_lt_tauAt hσ hz (dpt_nonneg j k) h.1,
    (mem_hull_iff_tauAt hσ hz (dpt_nonneg j (k + 1))).mpr h.2⟩

/-- The floor index lies in the summation range. -/
theorem cellK_lt_gridN {p : ℂ × Ω} (hτ0 : 0 < tauAt κ B p) (hτT : tauAt κ B p ≤ T) (j : ℕ) :
    cellK κ B j p < gridN T j := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hle : Nat.ceil (2 ^ j * tauAt κ B p) ≤ Nat.ceil (2 ^ j * T) :=
    Nat.ceil_mono (by nlinarith)
  have h1 : 1 ≤ Nat.ceil (2 ^ j * tauAt κ B p) :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  unfold cellK gridN
  omega

/-- **The value attached to the floor is the field value at the floor.** -/
theorem dval_eq {p : ℂ × Ω} (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p))
    (hz : 0 < p.1.im) (hτ0 : 0 < tauAt κ B p) (hτT : tauAt κ B p ≤ T) (j : ℕ) :
    dval κ B T j p = extFieldAt κ B (dpt j (cellK κ B j p)) p := by
  have hmem : cellK κ B j p ∈ Finset.range (gridN T j) :=
    Finset.mem_range.mpr (cellK_lt_gridN hτ0 hτT j)
  show (Finset.range (gridN T j)).sum (fun k => if p.1 ∉ fwdHull (drive κ B p.2) (dpt j k) ∧
      p.1 ∈ fwdHull (drive κ B p.2) (dpt j (k + 1)) then extFieldAt κ B (dpt j k) p else 0) = _
  rw [Finset.sum_eq_single_of_mem (cellK κ B j p) hmem (fun k _ hk => by
    rw [if_neg]
    intro hcon
    obtain ⟨h1, h2⟩ := cell_iff_mp hσ hcon
    exact hk (cellK_unique hτ0 h1 h2))]
  exact if_pos (cell_iff_mpr hσ hz (cellK_spec hτ0 j))

/-- The floor is within `2^{-j}` of `tauAt` from below. -/
theorem cellK_sandwich {p : ℂ × Ω} (hτ0 : 0 < tauAt κ B p) (j : ℕ) :
    tauAt κ B p - (1 / 2 : ℝ) ^ j ≤ dpt j (cellK κ B j p) ∧
      dpt j (cellK κ B j p) ≤ tauAt κ B p := by
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hle := cellK_le_mul hτ0 j
  have hdiv : ((2 : ℝ) ^ j)⁻¹ = (1 / 2 : ℝ) ^ j := by rw [one_div, inv_pow]
  have hcast : (((cellK κ B j p + 1 : ℕ)) : ℝ) = ((cellK κ B j p : ℕ) : ℝ) + 1 := by
    push_cast; ring
  have h4 : tauAt κ B p ≤ (((cellK κ B j p : ℕ) : ℝ) + 1) / 2 ^ j := by
    rw [le_div_iff₀ h2, mul_comm (tauAt κ B p) ((2 : ℝ) ^ j)]
    rw [hcast] at hle
    linarith [hle]
  have h5 : (((cellK κ B j p : ℕ) : ℝ) + 1) / 2 ^ j =
      dpt j (cellK κ B j p) + (1 / 2 : ℝ) ^ j := by
    rw [add_div, one_div, dpt, hdiv]
  constructor
  · rw [h5] at h4
    linarith
  · exact le_of_lt (cellK_spec hτ0 j).1

/-- **The dyadic floor converges to `tauAt` from below.** -/
theorem tendsto_dpt_cellK {p : ℂ × Ω} (hτ0 : 0 < tauAt κ B p) :
    Tendsto (fun j => dpt j (cellK κ B j p)) atTop (𝓝[<] (tauAt κ B p)) := by
  have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun j => (cellK_spec hτ0 j).1⟩
  have hconst : Tendsto (fun _ : ℕ => tauAt κ B p) atTop (𝓝 (tauAt κ B p)) :=
    tendsto_const_nhds
  have hlow : Tendsto (fun j : ℕ => tauAt κ B p - (1 / 2 : ℝ) ^ j) atTop
      (𝓝 (tauAt κ B p)) := by
    simpa using hconst.sub hpow
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hconst
    (fun j => (cellK_sandwich hτ0 j).1) (fun j => (cellK_sandwich hτ0 j).2)

/-- Below `tauAt`, `extFieldAt` is the raw field formula. -/
theorem extFieldAt_eq_raw {p : ℂ × Ω}
    (hσ : swallowTime (drive κ B p.2) p.1 = ENNReal.ofReal (tauAt κ B p)) (hz : 0 < p.1.im)
    {s : ℝ} (hs0 : 0 ≤ s) (hs : s < tauAt κ B p) : extFieldAt κ B s p = rawFieldAt κ B s p :=
  extFieldAt_of_mem ⟨hz, not_mem_hull_of_lt_tauAt hσ hz hs0 hs⟩

end Floor

end Thm11Asm
end QuantumZipper
