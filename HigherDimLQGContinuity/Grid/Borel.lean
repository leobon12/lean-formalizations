import HigherDimLQGContinuity.Grid.Bad
import HigherDimLQGContinuity.Grid.Asymp

/-! Summable comparison failures on a fixed positive parameter window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

theorem eventually_posBad_le {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi)
    {R : ℝ} (hR : 1 ≤ R) :
    ∀ᶠ j : ℕ in atTop,
      normLGFLaw d (posBad d lo hi R j) ≤ ENNReal.ofReal (endA j) := by
  obtain ⟨B, M, C, c, _hB, _hM, hc, _hc1, hC, hbound⟩ :=
    exists_posBad_bound_constants hd hP hlo hlohi hhi hR
  filter_upwards [eventually_posGrid_G (B := B) (M := M) hlo hlohi (by linarith : 0 < C),
    eventually_posGrid_depth (B := B) hlohi hC hc, eventually_posGrid_fail hlohi hC hc]
      with j hG hdepth hfail
  have hb := hbound j hG hdepth
  have hA : 0 ≤ endA (j + 1) := (endA_pos _).le
  have htwo : endA (j + 1) + endA (j + 1) = endA j := by
    rw [endA_succ]
    ring
  calc
    normLGFLaw d (posBad d lo hi R j) ≤
        ENNReal.ofReal (((2 : ℝ) ^ posLevel (j + 1) + 1) *
          (C * posDelta j ^ (-M) * Real.exp (-(c * posDelta j ^ M *
            (c * posDelta j / posWidth lo hi j))))) +
        ENNReal.ofReal (((2 : ℝ) ^ posLevel (j + 1) + 1) *
          (C * posDelta j ^ (-M) * Real.exp (-(c * posDelta j ^ M *
            (c * posDelta j / posWidth lo hi j))))) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using hb
    _ ≤ ENNReal.ofReal (endA (j + 1)) + ENNReal.ofReal (endA (j + 1)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hfail) (ENNReal.ofReal_le_ofReal hfail)
    _ = ENNReal.ofReal (endA j) := by
      rw [← ENNReal.ofReal_add hA hA, htwo]

/-- The countable good event: at every integral spatial radius all sufficiently fine
comparison events are absent. -/
def posGood (d : ℕ) (lo hi : ℝ) : Set (DistRd d) :=
  ⋂ R : ℕ, ⋃ J : ℕ, ⋂ j ∈ Set.Ici J, (posBad d lo hi (R + 1) j)ᶜ

theorem measurable_posGood {d : ℕ} (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) :
    MeasurableSet (posGood d lo hi) := by
  unfold posGood
  exact MeasurableSet.iInter fun R => MeasurableSet.iUnion fun J =>
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurable_posBad hd hlo hlohi hhi (R + 1) j).compl

theorem ae_posGood {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) :
    ∀ᵐ g ∂(normLGFLaw d), g ∈ posGood d lo hi := by
  change ∀ᵐ g ∂(normLGFLaw d), g ∈ ⋂ R : ℕ, ⋃ J : ℕ,
    ⋂ j ∈ Set.Ici J, (posBad d lo hi (R + 1) j)ᶜ
  simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_Ici]
  rw [ae_all_iff]
  intro R
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (eventually_posBad_le hd hP hlo hlohi hhi
      (R := R + 1) (by exact_mod_cast (show 1 ≤ R + 1 by omega : 1 ≤ R + 1)))
  have hsummable : Summable fun j : ℕ => endA (j + J) := by
    unfold endA
    simp_rw [pow_add]
    exact (summable_geometric_two.mul_right _)
  have hsum : ∑' j : ℕ, normLGFLaw d (posBad d lo hi (R + 1) (j + J)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun j => hJ (j + J) (by omega))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (endA_pos _).le) hsummable]
    exact ENNReal.ofReal_ne_top
  have hBC := ae_eventually_notMem hsum
  filter_upwards [hBC] with g hg
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.1 hg
  refine ⟨J + j₀, fun j hj => ?_⟩
  have h := hj₀ (j - J) (by omega : j₀ ≤ j - J)
  rwa [Nat.sub_add_cancel (by omega : J ≤ j)] at h

theorem null_posGood_compl {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) :
    normLGFLaw d (posGood d lo hi)ᶜ = 0 :=
  (ae_iff.1 (ae_posGood hd hP hlo hlohi hhi))

end HigherDimLQGContinuity
