import HigherDimLQGContinuity.Caps.CoverFull
import HigherDimLQGContinuity.Caps.Lemma22
import HigherDimLQGContinuity.Sewing.Lemma31a

/-!
# Band families of good grid balls (packet P7)

For a band `V` (dyadic radii `2^{-k} ∈ [e^{-2V}, e^{-V}]`, `k ∈ p4_fullScales V`), centres in the lattice
`κ₀ 2^{-k} ℤ^d` (`κ₀ = 1/(20√d)`, the grid of `cover210` and `lemma22`) inside `B̄_{W+1}`, and a predicate `good` on
balls, `p7BandSet d V W good` is the set of good balls of the band, viewed as `SewBall d = ℝ^d × ℝ` (centre, radius),
the index type of Lemma 3.1 (`lemma31a`, `lemma31b`). It is finite (`p7BandSet_finite`): it lies in the swapped
finite superset `p4_gridPairsFinset` of the inspected grid `gridPairs d 2 κ₀ N (W + 1)` of Lemma 2.2 whenever
`2V ≤ N` (`p7BandSet_swap_mem_gridPairs`). The complement of the covering event of `cover210_full` gives a member
of the band around every point of `B̄_W` (`p7_band_cover`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)
open HigherDimLQGMetric

variable {d : ℕ}

/-- The good balls of the band `V` with centres in `B̄_{W+1}` (see the module docstring). -/
def p7BandSet (d : ℕ) (V W : ℝ) (good : SewBall d → Prop) : Set (SewBall d) :=
  {B | (∃ k ∈ p4_fullScales V, ∃ j : Fin d → ℤ,
      B.2 = p4_radius k ∧ B.1 = latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) ∧
    ‖B.1‖ ≤ W + 1 ∧ good B}

theorem p7_p4_radius_pos (k : ℕ) : 0 < p4_radius k :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Radii of a band ball. -/
theorem p7BandSet_radius {V W : ℝ} (hV : 0 ≤ V) {good : SewBall d → Prop} {B : SewBall d}
    (hB : B ∈ p7BandSet d V W good) : Real.exp (-2 * V) ≤ B.2 ∧ B.2 ≤ Real.exp (-V) := by
  obtain ⟨⟨k, hk, j, hr, -⟩, -, -⟩ := hB
  rw [hr]
  exact (p4_mem_fullScales_iff hV k).mp hk

/-- A band ball, swapped, is an inspected grid pair of Lemma 2.2 at any depth `N ≥ 2V`. -/
theorem p7BandSet_swap_mem_gridPairs {V W : ℝ} (hV : 0 ≤ V) {N : ℕ} (hNV : 2 * V ≤ N)
    {good : SewBall d → Prop} {B : SewBall d} (hB : B ∈ p7BandSet d V W good) :
    (B.2, B.1) ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) N (W + 1) := by
  have hrad := p7BandSet_radius hV hB
  obtain ⟨⟨k, -, j, hr, hz⟩, hW, -⟩ := hB
  refine ⟨k, hr, ?_, j, ?_, hW⟩
  · calc Real.exp (-(N : ℝ)) ≤ Real.exp (-2 * V) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ B.2 := hrad.1
  · simp only
    rw [hz, hr]

/-- Band sets are finite. -/
theorem p7BandSet_finite (hd : 1 ≤ d) {V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (good : SewBall d → Prop) : (p7BandSet d V W good).Finite := by
  have hκ : 0 < 1 / (20 * Real.sqrt d) := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    positivity
  set N : ℕ := ⌈2 * V⌉₊
  have hNV : 2 * V ≤ N := Nat.le_ceil _
  refine ((Finset.finite_toSet (p4_gridPairsFinset d 2 (1 / (20 * Real.sqrt d)) N (W + 1))).image
    Prod.swap).subset ?_
  intro B hB
  refine ⟨(B.2, B.1), ?_, rfl⟩
  exact gridPairs_subset_finset (by norm_num) hκ (by linarith) (p7BandSet_swap_mem_gridPairs hV hNV hB)

/-- The finset of a band set. -/
def p7BandFinset (hd : 1 ≤ d) {V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) (good : SewBall d → Prop) :
    Finset (SewBall d) :=
  (p7BandSet_finite hd hV hW good).toFinset

theorem p7_mem_bandFinset (hd : 1 ≤ d) {V W : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) {good : SewBall d → Prop}
    {B : SewBall d} : B ∈ p7BandFinset hd hV hW good ↔ B ∈ p7BandSet d V W good :=
  Set.Finite.mem_toFinset _

/-- Coverage of `B̄_W` by a band, from the complement of the covering event of `cover210_full`: if every point of
`B̄_W` is within a tenth of the radius of the centre of some good grid ball of the band, then every point of `B̄_W` is
in the central tenth of a member of the band set. -/
theorem p7_band_cover {V W : ℝ} (hV : 0 ≤ V) {good : SewBall d → Prop}
    (hcov : ∀ x ∈ closedBall (0 : Rd d) W, ∃ k ∈ p4_fullScales V, ∃ j : Fin d → ℤ,
      ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 ∧
        good (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j, p4_radius k)) :
    ∀ x ∈ closedBall (0 : Rd d) W, ∃ B ∈ p7BandSet d V W good, ‖x - B.1‖ < B.2 / 10 := by
  intro x hx
  obtain ⟨k, hk, j, hdist, hgood⟩ := hcov x hx
  refine ⟨(latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j, p4_radius k), ⟨⟨k, hk, j, rfl, rfl⟩, ?_, hgood⟩,
    hdist⟩
  have hr1 : p4_radius k ≤ 1 := by
    have := ((p4_mem_fullScales_iff hV k).mp hk).2
    exact this.trans (by rw [Real.exp_le_one_iff]; linarith)
  have hxn : ‖x‖ ≤ W := mem_closedBall_zero_iff.mp hx
  have htri : ‖latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ ≤
      ‖x‖ + ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ := by
    have := norm_sub_le x (x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j)
    simpa only [sub_sub_cancel] using this
  simp only
  linarith

/-- The complement of the covering event of `cover210_full`, unfolded. -/
theorem p7_not_cover_event {s : ℝ} {E : Set (DistRd d)} {V W : ℝ} {g : DistRd d}
    (hg : g ∉ {g : DistRd d | ∃ x ∈ closedBall (0 : Rd d) W, ∀ k ∈ p4_fullScales V, ∀ j : Fin d → ℤ,
      ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 →
        recentre s (p4_radius k) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∉ E}) :
    ∀ x ∈ closedBall (0 : Rd d) W, ∃ k ∈ p4_fullScales V, ∃ j : Fin d → ℤ,
      ‖x - latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j‖ < p4_radius k / 10 ∧
        recentre s (p4_radius k) (latPt ((1 / (20 * Real.sqrt d)) * p4_radius k) j) g ∈ E := by
  intro x hx
  by_contra hcon
  apply hg
  refine ⟨x, hx, fun k hk j hdist hmem => hcon ⟨k, hk, j, hdist, hmem⟩⟩

end HigherDimLQGContinuity
