import MeshOnly.MeshOnlyEnergy

/-! The collar and energy constant are uniform over the continuum data. -/

open scoped Classical Topology ENNReal
open MeasureTheory

namespace BouRabeeGwynne.TilingSequence

variable {d : ℕ} (G : TilingSequence d)

/-- Lemma 5.1's energy bound, with a single eventual index and a single constant
for every harmonic function satisfying the same Hessian bound on W. -/
theorem eventually_uniform_energy_error_le (hd : 1 ≤ d) (hmesh : G.MeshConverges)
    {U W : Set (Euc d)} (hU : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (hW : IsOpen W) (hUW : closure U ⊆ W)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in Filter.atTop,
      ∃ hfin : ((G.tiling n).closedVertices U).Finite,
        letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
        ∀ (h : Euc d → ℝ) (hD : (G.tiling n).V → ℝ),
          IsHarmonicOn h W →
          (∀ x ∈ W, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) →
          (G.tiling n).SolvesDirichlet U (fun v => h ((G.tiling n).pos v)) hD →
          ((G.tiling n).finiteNetwork ((G.tiling n).closedVertices U)).energy
            (fun v => hD v - h ((G.tiling n).pos v)) ≤
              C * (G.tiling n).mesh.toReal ^ 2 := by
  obtain ⟨ρ, hρ, hρQ⟩ := hU.isCompact_closure.exists_cthickening_subset_open
    (hW.inter isOpen_interior) (fun x hx => ⟨hUW hx, hUD hx⟩)
  let Q := Metric.cthickening ρ (closure U)
  have hQc : IsCompact Q := hU.isCompact_closure.cthickening
  have hQW : Q ⊆ W := fun x hx => (hρQ hx).1
  have hQD : Q ⊆ interior G.domain := fun x hx => (hρQ hx).2
  have hQfinite : μHE[d] Q ≠ ∞ := by
    have hm : (μHE[d] : Measure (Euc d)) = volume := by
      simpa using InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Euc d)
    rw [hm]
    exact hQc.measure_lt_top.ne
  refine ⟨9 * (d : ℝ) * (μHE[d] Q).toReal * M ^ 2, by positivity, ?_⟩
  filter_upwards [G.eventually_closedVertices_finite hmesh hU hUD,
    G.eventually_closedRegion_in_compact_collar hmesh hρ (Q := Q) Set.Subset.rfl]
    with n hfin hn
  refine ⟨hfin, ?_⟩
  letI : Fintype ((G.tiling n).closedVertices U) := hfin.fintype
  intro h hD hh hH hsol
  apply (G.tiling n).harmonic_error_energy_le_collar hd U hD h hn.1 hM hsol
    hQfinite (by simpa only [G.common_domain n] using hQD) hQW hW hh
    (fun v => (hn.2 v v.property).1) (fun v => (hn.2 v v.property).2)
  intro x hx
  exact hH x (hQW hx)

end BouRabeeGwynne.TilingSequence
