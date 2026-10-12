import MeshOnly.MeshOnlyUniformEnergy
import MeshOnly.MeshOnlySobolevSupport
import MeshOnly.MeshOnlySobolevSupportVolume

/-! The weighted L² error estimate, uniform over the continuum data on one
fixed collar. The constant is chosen before the mesh index and the functions. -/

open MeasureTheory
open scoped Classical Topology ENNReal BigOperators

namespace BouRabeeGwynne.TilingSequence

variable {n : ℕ} (G : TilingSequence (n + 1))

theorem eventually_uniform_l2_error_le (hd : 2 ≤ n + 1) (hmesh : G.MeshConverges)
    {U W : Set (Euc (n + 1))} (hU : Bornology.IsBounded U)
    (hUD : HasAmbientCollar U G.domain) (hW : IsOpen W) (hUW : closure U ⊆ W)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in Filter.atTop,
      ∃ hfin : ((G.tiling k).closedVertices U).Finite,
        letI : Fintype ((G.tiling k).closedVertices U) := hfin.fintype
        ∀ (h : Euc (n + 1) → ℝ) (hD : (G.tiling k).V → ℝ),
          IsHarmonicOn h W →
          (∀ x ∈ W, ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M) →
          (G.tiling k).SolvesDirichlet U (fun v => h ((G.tiling k).pos v)) hD →
          (∑ v : (G.tiling k).closedVertices U,
            ((G.tiling k).cell v).volume.toReal *
              (hD v - h ((G.tiling k).pos v)) ^ 2) ≤
            C * (G.tiling k).mesh.toReal ^ 2 := by
  obtain ⟨CE, hCE, henergy⟩ := G.eventually_uniform_energy_error_le
    (by omega : 1 ≤ n + 1) hmesh hU hUD hW hUW hM
  obtain ⟨ρ, hρ, hρQ⟩ := hU.isCompact_closure.exists_cthickening_subset_open
    (hW.inter isOpen_interior) (fun x hx => ⟨hUW hx, hUD hx⟩)
  let Q := Metric.cthickening ρ (closure U)
  have hQc : IsCompact Q := hU.isCompact_closure.cthickening
  have hQD : Q ⊆ interior G.domain := fun x hx => (hρQ hx).2
  have hQfinite : volume Q ≠ ∞ := hQc.measure_lt_top.ne
  let V : ℝ := volume.real Q
  let C₀ := MeshOnlySobolev.nashConstant (n + 1)
  let B := C₀ * V ^ (2 / ((n + 1 : ℕ) : ℝ)) +
    Real.sqrt C₀ * V ^ (1 / ((n + 1 : ℕ) : ℝ))
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hC₀ : 0 ≤ C₀ := (MeshOnlySobolev.nashConstant_pos hd).le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B * CE, mul_nonneg hB hCE, ?_⟩
  filter_upwards [henergy,
    G.eventually_closedRegion_in_compact_collar hmesh hρ (Q := Q) Set.Subset.rfl,
    G.eventually_mesh_finite_le hmesh zero_lt_one] with k hk hc hsmall
  obtain ⟨hfin, he⟩ := hk
  refine ⟨hfin, ?_⟩
  letI : Fintype ((G.tiling k).closedVertices U) := hfin.fintype
  intro h hD hh hH hsol
  let T := G.tiling k
  let R := T.closedVertices U
  let u : R → ℝ := fun v => hD v - h (T.pos v)
  have hcell : ∀ v : R, (T.cell v).carrier ⊆ Q :=
    fun v => (hc.2 v v.property).1
  have hactive : ∀ v : R, u v ≠ 0 → T.pos v ∈ U := by
    intro v hv
    by_contra hout
    have heq := hsol.2 v (v.property.resolve_left hout)
    exact hv (by dsimp [u]; rw [heq, sub_self])
  have hcellD : ∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain := by
    intro v _
    simpa only [T, G.common_domain k] using (hcell v).trans hQD
  have hneighbors : ∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R :=
    fun v hv w hw => T.neighbor_mem_closedVertices (hactive v hv) hw
  have hsupport : (∑ v : R, if u v ≠ 0 then (T.cell v).volume.toReal else 0) ≤ V :=
    T.meshOnly_supportVolume_le (by omega) R u Q hQc.measurableSet hQfinite
      (fun v _ => hcell v)
  have hs := T.meshOnly_support_bound hd R u hc.1 hcellD hneighbors V hV hsupport
  have hcoeff : C₀ * V ^ (2 / ((n + 1 : ℕ) : ℝ)) +
      Real.sqrt C₀ * T.mesh.toReal * V ^ (1 / ((n + 1 : ℕ) : ℝ)) ≤ B := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall.2 (Real.sqrt_nonneg C₀))
      (Real.rpow_nonneg hV (1 / ((n + 1 : ℕ) : ℝ)))
    dsimp [B]
    linarith only [h]
  have hE : (T.finiteNetwork R).energy u ≤ CE * T.mesh.toReal ^ 2 :=
    he h hD hh hH hsol
  calc
    _ ≤ (C₀ * V ^ (2 / ((n + 1 : ℕ) : ℝ)) +
        Real.sqrt C₀ * T.mesh.toReal * V ^ (1 / ((n + 1 : ℕ) : ℝ))) *
          (T.finiteNetwork R).energy u := hs
    _ ≤ B * (T.finiteNetwork R).energy u :=
      mul_le_mul_of_nonneg_right hcoeff ((T.finiteNetwork R).energy_nonneg u)
    _ ≤ B * (CE * T.mesh.toReal ^ 2) := mul_le_mul_of_nonneg_left hE hB
    _ = _ := by ring

end BouRabeeGwynne.TilingSequence
