import Mathlib
import MatedCRTHarmonic.Frozen.VerticesMeeting
import MatedCRTHarmonic.CellScaling.ConeDefs

/-!
# Unit mass, null overlaps and counting cells by area (deterministic)

Paper : "Distinct cells overlap only on sets of zero quantum area, so `A^γ_h(U^H_A) = |A|` for
finite `A ⊂ ℤ`." The area-overlap argument proves the
overlap claim from the area parameterization alone: if `μ(η([s, t])) = t − s` for all `s ≤ t`, then for
`s ≤ t ≤ s' ≤ t'`, `μ(η([s,t]) ∩ η([s',t'])) = 0` (inclusion–exclusion on `η([s,t']) = a ∪ c ∪ d`).

The counting lemma `finite_card_le_of_area` is the deterministic core of the cell-counting argument: if every cell meeting `D`
lies in `E`, then every finite family of such cells has cardinality `μ(⋃) ≤ μ(E)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- The image of a compact interval under a continuous curve is measurable. -/
theorem measurableSet_image_Icc (η : C(ℝ, ℂ)) (s t : ℝ) : MeasurableSet (η '' Icc s t) :=
  (isCompact_Icc.image η.continuous).measurableSet

/-- **Null overlaps of the area-parameterized curve** (the area-overlap argument): if `μ(η([s,t])) = t − s` for all
`s ≤ t`, then the images of two consecutive-or-separated intervals overlap in a `μ`-null set. -/
theorem measure_image_inter_eq_zero {μ : Measure ℂ} {η : C(ℝ, ℂ)}
    (hpar : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) {s t s' t' : ℝ}
    (hst : s ≤ t) (hts' : t ≤ s') (hs't' : s' ≤ t') :
    μ (η '' Icc s t ∩ η '' Icc s' t') = 0 := by
  set a := η '' Icc s t
  set c := η '' Icc t s'
  set d := η '' Icc s' t'
  have hunion : η '' Icc s t' = a ∪ c ∪ d := by
    have hI : Icc s t' = Icc s t ∪ Icc t s' ∪ Icc s' t' := by
      rw [Icc_union_Icc_eq_Icc hst hts', Icc_union_Icc_eq_Icc (le_trans hst hts') hs't']
    rw [hI, image_union, image_union]
  have hall : μ (a ∪ c ∪ d) = ENNReal.ofReal (t - s) + ENNReal.ofReal (s' - t) +
      ENNReal.ofReal (t' - s') := by
    rw [← hunion, hpar s t' (le_trans (le_trans hst hts') hs't'),
      ← ENNReal.ofReal_add (by linarith) (by linarith),
      ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  have hle : μ (a ∪ c ∪ d) ≤ μ (a ∪ d) + μ c := by
    calc μ (a ∪ c ∪ d) = μ ((a ∪ d) ∪ c) := by
          congr 1
          ext z
          simp only [mem_union]
          tauto
      _ ≤ μ (a ∪ d) + μ c := measure_union_le _ _
  have hc : μ c = ENNReal.ofReal (s' - t) := hpar t s' hts'
  have had : μ (a ∪ d) + μ (a ∩ d) = ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') := by
    rw [measure_union_add_inter a (measurableSet_image_Icc η s' t'), hpar s t hst, hpar s' t' hs't']
  have hfin : μ (a ∪ d) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_union_le a d)
    rw [hpar s t hst, hpar s' t' hs't']
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have h1 : ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') ≤ μ (a ∪ d) := by
    have h2 : ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') + ENNReal.ofReal (s' - t) ≤
        μ (a ∪ d) + ENNReal.ofReal (s' - t) := by
      calc ENNReal.ofReal (t - s) + ENNReal.ofReal (t' - s') + ENNReal.ofReal (s' - t)
          = μ (a ∪ c ∪ d) := by rw [hall]; ring
        _ ≤ μ (a ∪ d) + μ c := hle
        _ = μ (a ∪ d) + ENNReal.ofReal (s' - t) := by rw [hc]
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h2
  have h3 : μ (a ∪ d) + μ (a ∩ d) ≤ μ (a ∪ d) + 0 := by
    rw [had, add_zero]
    exact h1
  exact le_antisymm ((ENNReal.add_le_add_iff_left hfin).1 h3) zero_le

/-- The unit cells `η([x − 1, x])` overlap in `μ`-null sets. -/
theorem measure_unitCell_inter_eq_zero {μ : Measure ℂ} {η : C(ℝ, ℂ)}
    (hpar : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) {x y : ℤ} (hxy : x ≠ y) :
    μ (η '' Icc ((x : ℝ) - 1) x ∩ η '' Icc ((y : ℝ) - 1) y) = 0 := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have hle : (x : ℝ) ≤ (y : ℝ) - 1 := by
      have : x ≤ y - 1 := by omega
      exact_mod_cast this
    exact measure_image_inter_eq_zero hpar (by linarith) hle (by linarith)
  · have hle : (y : ℝ) ≤ (x : ℝ) - 1 := by
      have : y ≤ x - 1 := by omega
      exact_mod_cast this
    rw [inter_comm]
    exact measure_image_inter_eq_zero hpar (by linarith) hle (by linarith)

/-- **`A^γ_h(U_A) = |A|`** : finite unions of unit cells of an area-parameterized curve have area equal
to the number of cells. -/
theorem measure_biUnion_unitCell {μ : Measure ℂ} {η : C(ℝ, ℂ)}
    (hpar : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s)) (F : Finset ℤ) :
    μ (⋃ x ∈ F, η '' Icc ((x : ℝ) - 1) x) = F.card := by
  rw [measure_biUnion_finset₀]
  · have hone : ∀ x ∈ F, μ (η '' Icc ((x : ℝ) - 1) x) = 1 := by
      intro x _
      rw [hpar _ _ (by linarith)]
      simp
    rw [Finset.sum_congr rfl hone]
    simp
  · intro x _ y _ hxy
    exact measure_unitCell_inter_eq_zero hpar hxy
  · intro x _
    exact (measurableSet_image_Icc η _ _).nullMeasurableSet

/-- **Counting cells by area** (the cell-counting argument, deterministic core): if the `μ`-area of finite unions of cells is
their number, and every cell meeting `D` lies in `E` with `μ(E) ≤ T`, then only finitely many cells meet `D`, at most
`T` of them. -/
theorem finite_card_le_of_area {μ : Measure ℂ} {J : ℤ → Set ℂ}
    (hmass : ∀ F : Finset ℤ, μ (⋃ x ∈ F, J x) = F.card) {D E : Set ℂ}
    (hsub : ∀ x, (J x ∩ D).Nonempty → J x ⊆ E) {T : ℝ} (hT : 0 ≤ T) (hE : μ E ≤ ENNReal.ofReal T) :
    (verticesMeeting J D).Finite ∧ ((verticesMeeting J D).encard.toNat : ℝ) ≤ T := by
  set V := verticesMeeting J D
  have hfin_le : ∀ F : Finset ℤ, (↑F : Set ℤ) ⊆ V → (F.card : ℝ) ≤ T := by
    intro F hF
    have hU : (⋃ x ∈ F, J x) ⊆ E := by
      intro z hz
      simp only [mem_iUnion] at hz
      obtain ⟨x, hx, hzx⟩ := hz
      exact hsub x (hF hx) hzx
    have h1 : ((F.card : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal T := by
      rw [← hmass F]
      exact le_trans (measure_mono hU) hE
    rw [← ENNReal.ofReal_natCast] at h1
    exact (ENNReal.ofReal_le_ofReal_iff hT).1 h1
  have hVfin : V.Finite := by
    by_contra hinf
    obtain ⟨F, hFV, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊T⌋₊ + 1)
    have := hfin_le F hFV
    rw [hcard] at this
    push_cast at this
    linarith [Nat.lt_floor_add_one T]
  refine ⟨hVfin, ?_⟩
  have h := hfin_le hVfin.toFinset (by simp)
  rw [hVfin.encard_eq_coe_toFinset_card]
  simpa using h

end MatedCRTHarmonic.CellScaling
