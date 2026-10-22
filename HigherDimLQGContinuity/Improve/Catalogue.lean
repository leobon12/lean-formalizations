import HigherDimLQGContinuity.Improve.Color
import HigherDimLQGContinuity.Improve.GridCount
import HigherDimLQGContinuity.ForcingCount.Defs

/-!
# Deterministic catalogues for the union bound

The centre set contains every site of the selected radius and colour whose
full inspection lies in the source ball and avoids the endpoints. It is fixed
by the net pair and the finite class, independently of the random field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

open Classical in
def q11CentreSet (d : ℕ) (r : ℝ) (color : Fin d → ℤ)
    (x y : Rd d) : Finset (Rd d) :=
  let step := r / (20 * Real.sqrt d)
  (shellGridBox d (⌈4 / step⌉₊ + 1) step).filter fun z =>
    (∃ j : Fin d → ℤ, z = latPt step j ∧ sec8Color d j = color) ∧
    closedBall z (4 * r) ⊆ ball (0 : Rd d) 4 ∧
    x ∉ closedBall z (4 * r) ∧ y ∉ closedBall z (4 * r)

def q11Catalogue (d : ℕ) (r : ℝ) (color : Fin d → ℤ)
    (bin : ℤ) (x y : Rd d) : Catalogue d :=
  ⟨r, q11CentreSet d r color x y, (2 : ℝ) ^ bin⟩

/-- A supplied site of the chosen class belongs to its deterministic
catalogue. -/
theorem q11_centre_mem {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    {color : Fin d → ℤ} {x y z : Rd d} {j : Fin d → ℤ}
    (hz : z = latPt (r / (20 * Real.sqrt d)) j)
    (hcolor : sec8Color d j = color)
    (hgeom : closedBall z (4 * r) ⊆ ball (0 : Rd d) 4 ∧
      x ∉ closedBall z (4 * r) ∧ y ∉ closedBall z (4 * r)) :
    z ∈ q11CentreSet d r color x y := by
  classical
  have hroot : 0 < Real.sqrt (d : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hstep : 0 < r / (20 * Real.sqrt d) := by positivity
  have hgrid : z ∈ gridPts (r / (20 * Real.sqrt d)) := by
    rw [hz]
    exact ⟨j, rfl⟩
  have hself : z ∈ closedBall z (4 * r) := mem_closedBall_self (by positivity)
  have hball : z ∈ ball (0 : Rd d) 4 := hgeom.1 hself
  have hbox := grid_ball_subset_shellGridBox (d := d) hstep
    (by norm_num : (0 : ℝ) ≤ 4) ⟨hgrid, hball⟩
  change z ∈ (shellGridBox d (⌈4 / (r / (20 * Real.sqrt d))⌉₊ + 1)
    (r / (20 * Real.sqrt d))).filter _
  exact Finset.mem_filter.mpr ⟨hbox, ⟨⟨j, hz, hcolor⟩,
    hgeom.1, hgeom.2.1, hgeom.2.2⟩⟩

/-- Every deterministic catalogue is geometrically valid when its radius
is at most one. -/
theorem q11_catalogue_valid {d : ℕ} (hd : 1 ≤ d) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (color : Fin d → ℤ) (bin : ℤ) (x y : Rd d) :
    (q11Catalogue d r color bin x y).Valid x y := by
  classical
  have hQ : 0 < (2 : ℝ) ^ bin := by positivity
  refine ⟨hr, hr1, hQ, ?_, ?_⟩
  · intro z hz
    exact (Finset.mem_filter.mp hz).2.2
  · intro z hz z' hz' hzz'
    obtain ⟨j, hjz, hjc⟩ := (Finset.mem_filter.mp hz).2.1
    obtain ⟨j', hjz', hjc'⟩ := (Finset.mem_filter.mp hz').2.1
    have hjj' : j ≠ j' := by
      intro he
      apply hzz'
      rw [hjz, hjz', he]
    have hsep := q11_same_color_sep hd hr hjj' (hjc.trans hjc'.symm)
    have hstepEq : (1 / (20 * Real.sqrt d)) * r = r / (20 * Real.sqrt d) := by ring
    rw [hstepEq] at hsep
    rw [← hjz, ← hjz'] at hsep
    have hdist : 4 * r + 4 * r < dist z z' := by
      rw [dist_eq_norm]
      linarith only [hsep, hr]
    change Disjoint (closedBall z (4 * r)) (closedBall z' (4 * r))
    exact closedBall_disjoint_closedBall hdist

/-- The centre set has the grid cardinality bound required by the forcing
count. -/
theorem q11_catalogue_card {d : ℕ} (hd : 1 ≤ d)
    {Δ r : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hr : Δ ^ (2 : ℕ) ≤ r)
    (color : Fin d → ℤ) (bin : ℤ) (x y : Rd d) :
    (((q11Catalogue d r color bin x y).Z.card : ℝ) ≤
      ((160 * Real.sqrt d + 5) / Δ ^ (2 : ℕ)) ^ d) := by
  classical
  apply q11_site_grid_card hd hΔ hΔ1 hr
  intro z hz
  obtain ⟨⟨j, hjz, -⟩, hgeom⟩ := (Finset.mem_filter.mp hz).2
  have hgrid : z ∈ gridPts (r / (20 * Real.sqrt d)) := by
    rw [hjz]
    exact ⟨j, rfl⟩
  have hself : z ∈ closedBall z (4 * r) :=
    mem_closedBall_self (by have := lt_of_lt_of_le (pow_pos hΔ _) hr; positivity)
  exact ⟨hgrid, hgeom.1 hself⟩

/-- The same count in the `Ccat * Δ^(-D0)` shape expected by Proposition
4.5, with `D0 = 2d`. -/
theorem q11_catalogue_card_for_prop45 {d : ℕ} (hd : 1 ≤ d)
    {Δ r : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hr : Δ ^ (2 : ℕ) ≤ r)
    (color : Fin d → ℤ) (bin : ℤ) (x y : Rd d) :
    (((q11Catalogue d r color bin x y).Z.card : ℝ) ≤
      (160 * Real.sqrt d + 5) ^ d * Δ ^ (-(2 * (d : ℝ)))) := by
  have hpow : Δ ^ (-(2 * (d : ℝ))) = ((Δ ^ (2 * d : ℕ)))⁻¹ := by
    have heq : (2 * (d : ℝ)) = ((2 * d : ℕ) : ℝ) := by push_cast; ring
    rw [heq, Real.rpow_neg hΔ.le, Real.rpow_natCast]
  calc
    ((q11Catalogue d r color bin x y).Z.card : ℝ)
        ≤ ((160 * Real.sqrt d + 5) / Δ ^ (2 : ℕ)) ^ d :=
          q11_catalogue_card hd hΔ hΔ1 hr color bin x y
    _ = (160 * Real.sqrt d + 5) ^ d * Δ ^ (-(2 * (d : ℝ))) := by
          rw [div_pow, ← pow_mul, hpow]
          simp only [div_eq_mul_inv]

end HigherDimLQGContinuity
