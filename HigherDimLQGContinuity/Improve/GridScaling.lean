import HigherDimLQGContinuity.Improve.PrimaryGrid
import HigherDimLQGContinuity.Improve.ScalingFamily

/-!
# Simultaneous scaling on the finite inspected grid
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

open Classical in
def q11GridFinite (d n : ℕ) : Finset (ℝ × Rd d) :=
  (p4_gridPairsFinset d 2 (1 / (20 * Real.sqrt d)) n 4).filter
    (fun p => p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) n 4)

theorem q11_gridFinite_mem {d n : ℕ} (hd : 1 ≤ d)
    {p : ℝ × Rd d}
    (hp : p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) n 4) :
    p ∈ q11GridFinite d n := by
  classical
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hκ : 0 < 1 / (20 * Real.sqrt d) := by positivity
  exact Finset.mem_filter.mpr
    ⟨gridPairs_subset_finset (by norm_num) hκ (by norm_num) hp, hp⟩

theorem q11_gridFinite_radius_pos {d n : ℕ} {p : ℝ × Rd d}
    (hp : p ∈ q11GridFinite d n) : 0 < p.1 := by
  classical
  obtain ⟨k, hk, -, -, -, -⟩ := (Finset.mem_filter.mp hp).2
  rw [hk]
  positivity

/-- Every candidate primary site in the cap's grid has exact site and seed
normalization simultaneously, almost surely under the radius-ten pin. -/
theorem q11_grid_scaling_ae {d n Ntr : ℕ} (hd : 2 ≤ d)
    (K : CountData d) (hξ : 0 < K.ξ) (hη : 0 < K.η)
    (hD : IsStrongExpMetric d K.ξ (distExp d K.ξ) K.D)
    (hE : IsStrongExpMetric d K.η (distExp d K.η) K.E)
    {L : ℝ} (hL : 0 < L)
    {Edge : Type} [Fintype Edge] (centre : Edge → Rd d) :
    ∀ᵐ H ∂(pinLaw d 10),
      ∀ p ∈ gridPairs d 2 (1 / (20 * Real.sqrt d)) n 4,
        (countSiteD K p.1 p.2 H = rho K.D (recentre 1 p.1 p.2 H) ∧
         (∃ hratio : 0 < scaleS d K.η 1 p.1 p.2 H /
             scaleS d K.ξ 1 p.1 p.2 H,
           countSiteE K p.1 p.2 H =
             (rho K.E (recentre 1 p.1 p.2 H)).smul
               (scaleS d K.η 1 p.1 p.2 H / scaleS d K.ξ 1 p.1 p.2 H)
               hratio) ∧
         (countSiteD K p.1 p.2 H).IsLength ∧
         (countSiteE K p.1 p.2 H).IsLength) ∧
        ∀ e : Edge, ∀ j : Fin Ntr,
          siteNorm K.ξ K.D (centre e) (seedTrialRadius_pos hL j)
              (recentre 1 p.1 p.2 H) =
            rho K.D (recentre 1 (seedTrialRadius L j) (centre e)
              (recentre 1 p.1 p.2 H)) ∧
          siteNorm K.η K.E (centre e) (seedTrialRadius_pos hL j)
              (recentre 1 p.1 p.2 H) =
            rho K.E (recentre 1 (seedTrialRadius L j) (centre e)
              (recentre 1 p.1 p.2 H)) := by
  classical
  have hf := q11_scaling_family_ae hd K hξ hη hD hE
    (by norm_num : (0 : ℝ) < 10)
    (q11GridFinite d n) (fun p hp => q11_gridFinite_radius_pos hp)
    (Finset.univ : Finset Edge) centre hL Ntr
  filter_upwards [hf] with H hH
  intro p hp
  obtain ⟨hmain, hseed⟩ := hH p (q11_gridFinite_mem (by omega : 1 ≤ d) hp)
  refine ⟨hmain, ?_⟩
  intro e j
  exact hseed e (Finset.mem_univ e) j (Finset.mem_range.mpr j.isLt)

end HigherDimLQGContinuity
