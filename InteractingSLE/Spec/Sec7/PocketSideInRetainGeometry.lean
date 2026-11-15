/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainRecord
import InteractingSLE.Spec.Sec7.PocketSideInGeometry
import InteractingSLE.Spec.Sec7.Aux124

/-!
# The actual fixed pair's walls and filled records

PROVE-POCKET-SIDEIN. The three actual walls are fixed by the two candidate
seeds. Their union lies outside the intersection of the initial pockets.
Ready supplies both frontier coverage and every pocket membership event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketStopWalls PocketWordPerQ

/-- Any two walls whose evaluations are measurable from a larger fixed
history record have their null-completed walls information in that record
joined with the original driving filtration. -/
theorem wallsSigma_le_original_record {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ)
    {R L : Ω → ℝ≥0 → ℂ}
    (hR : ∀ t, Measurable[ℋ] fun ω => R ω t)
    (hL : ∀ t, Measurable[ℋ] fun ω => L ω t) (q : ℝ≥0) :
    wallsSigma P R L ≤ ℋ ⊔ drivingFiltration P hX q := by
  have hPair : Measurable[ℋ] (fullHist ![R, L]) := by
    apply measurable_fullHist (mΩ := ℋ)
    intro j t
    fin_cases j
    · exact hR t
    · exact hL t
  exact (wallsSigma_le_drivingFiltration hX R L).trans
    (sup_le_sup hPair.comap_le ((drivingFiltration P hX).mono bot_le))

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopField Sec7.PocketStopWallsFin
  Sec7.PocketStopWalls Sec7.PocketWordPerQ Sec7.PocketUnionPt LocalSets
open WangWu (negInv)

variable {Ω : Type} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- The fixed candidate pair's actual three incoming walls. -/
def pairWallFamily (outer inner : SideTest Ω) (d : WordObjects Ω) : Fin 3 → Ω → ℝ≥0 → ℂ :=
  ![d.rightWall, d.leftWall outer.seed, d.leftWall inner.seed]

/-- Ready supplies the two geometric inputs of the filled record criterion
for both bounded and seed-opening pockets. -/
theorem domain_wall_props {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    Disjoint (H ∩ negInv '' (range (d.rightWall ω) ∪ range (d.leftWall j.seed ω)))
      ((j.target i d).domain ω) ∧
    frontier ((j.target i d).domain ω) ∩ H ⊆
      negInv '' (range (d.rightWall ω) ∪ range (d.leftWall j.seed ω)) := by
  rcases hj with ⟨-, -, -, hG, -, -, -, -, hAG, -⟩
  rw [target_event] at hω
  have hωG : ω ∈ j.outerEvent := by
    cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
      exact (hAG hω).1
  rw [target_domain]
  exact cfPocket_walls_props (hG ω hωG).1

/-- Every actual wall is outside at least one of the two pockets. Nesting
is unnecessary for the joint marked union law. -/
theorem pairWallFamily_cover {outer inner : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hOuter : outer.Ready d) (hInner : inner.Ready d) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event) :
    H ∩ (negInv '' (⋃ j, range (pairWallFamily outer inner d j ω))) ⊆
      ((outer.target i d).domain ω)ᶜ ∪ ((inner.target i d).domain ω)ᶜ := by
  have hO := (domain_wall_props hOuter hωO).1
  have hI := (domain_wall_props hInner hωI).1
  rintro z ⟨hzH, w, hw, rfl⟩
  obtain ⟨j, s, rfl⟩ := mem_iUnion.1 hw
  fin_cases j
  · exact Or.inl fun hz => Set.disjoint_left.1 hO ⟨hzH, _, Or.inl ⟨s, rfl⟩, rfl⟩ hz
  · exact Or.inl fun hz => Set.disjoint_left.1 hO ⟨hzH, _, Or.inr ⟨s, rfl⟩, rfl⟩ hz
  · exact Or.inr fun hz => Set.disjoint_left.1 hI ⟨hzH, _, Or.inr ⟨s, rfl⟩, rfl⟩ hz

/-- The actual filled record at a fixed original time is measurable from
any retained record containing its walls and the common hull. No marked
Gaussian law or future-dependent chart selection enters this construction. -/
theorem measurable_eventFilled_of_ready {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (hMarks : (j.target i d).walls ≤ ℋ)
    {M : Set Ω} (hM : MeasurableSet[ℋ] M) (hME : M ⊆ (j.target i d).event)
    {F : Ω → Set ℂ} (hF : Measurable[ℋ, hittingSigma] F) :
    Measurable[ℋ, hittingSigma] (eventFilled M (j.target i d).domain F) := by
  have hRm : ∀ t, Measurable[ℋ] fun ω => d.rightWall ω t := fun t =>
    (measurable_right_wallsSigma (P := d.measure) hRc hLc t).mono
      (by rwa [target_walls] at hMarks) le_rfl
  have hLm : ∀ t, Measurable[ℋ] fun ω => d.leftWall j.seed ω t := fun t =>
    (measurable_left_wallsSigma (P := d.measure) hRc hLc t).mono
      (by rwa [target_walls] at hMarks) le_rfl
  have hΓ : Measurable[ℋ, hittingSigma]
      (fun ω => negInv '' (range (d.rightWall ω) ∪ range (d.leftWall j.seed ω))) := by
    have hc : ∀ k : Fin 2, ∀ ω, Continuous (![d.rightWall, d.leftWall j.seed] k ω) := by
      intro k ω
      fin_cases k
      · exact hRc ω
      · exact hLc ω
    have hm : ∀ k : Fin 2, ∀ t, Measurable[ℋ]
        (fun ω => ![d.rightWall, d.leftWall j.seed] k ω t) := by
      intro k t
      fin_cases k
      · exact hRm t
      · exact hLm t
    simpa only [iUnion_range_fin_two] using (@measurable_negInv_walls Ω ℋ 2 _ hc hm)
  have hΓF := @measurable_union_hitting Ω ℋ _ _ hΓ hF
  apply measurable_eventFilled hM (Γ := fun ω =>
    negInv '' (range (d.rightWall ω) ∪ range (d.leftWall j.seed ω)))
  · intro z
    have he : {ω | ω ∈ M ∧ z ∈ (j.target i d).domain ω} =
        M ∩ {ω | ω ∈ (j.target i d).event ∧ z ∈ (j.target i d).domain ω} := by
      ext ω
      exact ⟨fun h => ⟨h.1, hME h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [he]
    exact hM.inter (hMarks _ (measurableSet_domain hj hRc hLc z))
  · exact fun ω hω => isOpen_domain hj ω (hME hω)
  · exact fun ω hω => (domain_wall_props hj (hME hω)).1
  · exact fun ω hω => (domain_wall_props hj (hME hω)).2
  · apply Aux124.measurable_hitting_of_inter_H_eq hΓF
    intro ω
    ext z
    simp only [mem_inter_iff]
    tauto

end InteractingSLE.Wire.Current.SideTest
