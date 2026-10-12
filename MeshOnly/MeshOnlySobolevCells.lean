import BouRabeeGwynne.DualAdditivity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Support

/-! The actual finite cellwise-constant extension, including its exact
volume-weighted integrals. Cell intersections are discarded only after proving
that they are null in the ambient Euclidean volume. -/

open scoped BigOperators Classical ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

noncomputable def meshOnlyCellFunction (R : Set T.V) [Fintype R]
    (c : R → ℝ) (x : Euc d) : ℝ :=
  ∑ v : R, (T.cell v).carrier.indicator (fun _ => c v) x

lemma meshOnly_cellIndicator_integrable (v : T.V) (c : ℝ) :
    Integrable ((T.cell v).carrier.indicator (fun _ : Euc d => c)) volume := by
  exact (integrable_indicator_iff (T.cell v).compact.measurableSet).mpr
    (integrableOn_const (T.cell v).compact.measure_lt_top.ne)

lemma meshOnlyCellFunction_integrable (R : Set T.V) [Fintype R] (c : R → ℝ) :
    Integrable (T.meshOnlyCellFunction R c) volume := by
  exact integrable_finsetSum Finset.univ
    (fun v _ => T.meshOnly_cellIndicator_integrable v (c v))

lemma meshOnlyCellFunction_hasCompactSupport (R : Set T.V) [Fintype R] (c : R → ℝ) :
    HasCompactSupport (T.meshOnlyCellFunction R c) := by
  have h (v : R) : HasCompactSupport ((T.cell v).carrier.indicator (fun _ => c v)) :=
    HasCompactSupport.of_support_subset_isCompact (T.cell v).compact
      Set.support_indicator_subset
  have heq : T.meshOnlyCellFunction R c =
      ∑ v : R, (T.cell v).carrier.indicator (fun _ : Euc d => c v) := by
    ext x
    simp only [meshOnlyCellFunction, Finset.sum_apply]
  rw [heq]
  exact HasCompactSupport.finset_sum (s := Finset.univ) (fun v _ => h v)

lemma meshOnlyCellFunction_nonneg (R : Set T.V) [Fintype R] (c : R → ℝ)
    (hc : ∀ v, 0 ≤ c v) (x : Euc d) : 0 ≤ T.meshOnlyCellFunction R c x := by
  exact Finset.sum_nonneg fun v _ => Set.indicator_nonneg (fun _ _ => hc v) x

/-- Integrating against a continuous test function is exactly the finite
sum of the integrals over the actual cells. -/
theorem meshOnlyCellFunction_integral_mul
    (R : Set T.V) [Fintype R] (c : R → ℝ)
    (ψ : Euc d → ℝ) (hψ : Continuous ψ) :
    (∫ x, T.meshOnlyCellFunction R c x * ψ x ∂volume) =
      ∑ v : R, (∫ x in (T.cell v).carrier, ψ x ∂volume) * c v := by
  have heq (x : Euc d) : T.meshOnlyCellFunction R c x * ψ x =
      ∑ v : R, (T.cell v).carrier.indicator (fun x => ψ x * c v) x := by
    unfold meshOnlyCellFunction
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hx : x ∈ (T.cell v).carrier <;> simp [hx, mul_comm]
  simp_rw [heq]
  rw [integral_finsetSum Finset.univ
    (f := fun v : R => (T.cell v).carrier.indicator (fun x => ψ x * c v)) (fun (v : R) _ =>
    (integrable_indicator_iff (T.cell v).compact.measurableSet).mpr
      ((hψ.continuousOn.integrableOn_compact (T.cell v).compact).mul_const (c v)))]
  apply Finset.sum_congr rfl
  intro v _
  rw [integral_indicator (T.cell v).compact.measurableSet, integral_mul_const]

/-- At almost every point, a finite family of distinct actual cells has at
most one member. This includes contacts of all codimensions. -/
lemma meshOnly_ae_cells_disjoint (hd : 1 ≤ d) (R : Set T.V) [Fintype R] :
    ∀ᵐ x : Euc d ∂volume, ∀ v w : R, v ≠ w →
      ¬ (x ∈ (T.cell v).carrier ∧ x ∈ (T.cell w).carrier) := by
  apply ae_all_iff.mpr
  intro v
  apply ae_all_iff.mpr
  intro w
  by_cases hvw : v = w
  · exact Filter.Eventually.of_forall fun _ h => False.elim (h hvw)
  · have hnull : volume ((T.cell v).carrier ∩ (T.cell w).carrier) = 0 := by
      have h := T.toTilingData.facet_full_measure_zero hd
        (fun heq => hvw (Subtype.ext heq))
      rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    exact fun _ => hx

/-- Any scalar transform that vanishes at zero is represented by the same
finite cell indicators almost everywhere. No continuity of the transform is
needed: the extension takes only finitely many values. -/
lemma meshOnlyCellFunction_transform_ae (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (c : R → ℝ) (Ψ : ℝ → ℝ≥0∞) (hΨ : Ψ 0 = 0) :
    (fun x => Ψ (T.meshOnlyCellFunction R c x)) =ᵐ[volume]
      fun x => ∑ v : R, (T.cell v).carrier.indicator (fun _ => Ψ (c v)) x := by
  filter_upwards [T.meshOnly_ae_cells_disjoint hd R] with x hx
  by_cases hex : ∃ v : R, x ∈ (T.cell v).carrier
  · obtain ⟨v, hv⟩ := hex
    have hnot (w : R) (hw : w ≠ v) : x ∉ (T.cell w).carrier :=
      fun h => hx w v hw ⟨h, hv⟩
    have hc : T.meshOnlyCellFunction R c x = c v := by
      unfold meshOnlyCellFunction
      rw [Finset.sum_eq_single v]
      · exact Set.indicator_of_mem hv _
      · intro w _ hw
        exact Set.indicator_of_notMem (hnot w hw) _
      · simp
    rw [hc, Finset.sum_eq_single v]
    · exact (Set.indicator_of_mem hv (fun _ : Euc d => Ψ (c v))).symm
    · intro w _ hw
      exact Set.indicator_of_notMem (hnot w hw) _
    · simp
  · have hnot : ∀ v : R, x ∉ (T.cell v).carrier := by simpa using hex
    have hc : T.meshOnlyCellFunction R c x = 0 := by
      exact Finset.sum_eq_zero fun v _ => Set.indicator_of_notMem (hnot v) _
    rw [hc, hΨ]
    symm
    exact Finset.sum_eq_zero fun v _ => Set.indicator_of_notMem (hnot v) _

/-- Exact weighted integral of any nonnegative transform of the actual
finite extension. In particular this supplies all weighted Lᵖ identities. -/
theorem meshOnlyCellFunction_lintegral_transform (hd : 1 ≤ d)
    (R : Set T.V) [Fintype R] (c : R → ℝ) (Ψ : ℝ → ℝ≥0∞) (hΨ : Ψ 0 = 0) :
    (∫⁻ x, Ψ (T.meshOnlyCellFunction R c x) ∂volume) =
      ∑ v : R, (T.cell v).volume * Ψ (c v) := by
  rw [lintegral_congr_ae (T.meshOnlyCellFunction_transform_ae hd R c Ψ hΨ)]
  rw [lintegral_finsetSum Finset.univ
    (f := fun v : R => (T.cell v).carrier.indicator (fun _ => Ψ (c v)))
    (fun (v : R) _ => measurable_const.indicator (T.cell v).compact.measurableSet)]
  apply Finset.sum_congr rfl
  intro v _
  rw [lintegral_indicator (T.cell v).compact.measurableSet, lintegral_const]
  simp only [Measure.restrict_apply_univ, ConvexPolytope.volume,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact mul_comm _ _

end BouRabeeGwynne.OrthogonalTiling
