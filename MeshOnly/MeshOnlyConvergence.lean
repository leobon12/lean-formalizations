import MeshOnly.MeshOnlyUniformL2
import MeshOnly.MeshOnlyUniformCollar
import MeshOnly.MeshOnlyDirichletControl
import MeshOnly.MeshOnlyTilingSpike
import MeshOnly.MeshOnlyTargetAssembly

/-! Uniform convergence from the geometric Nash inequality and the local
volume-clock estimates. The mesh index is chosen before the harmonic data. -/

open MeasureTheory Filter
open scoped Classical Topology BigOperators ENNReal

namespace BouRabeeGwynne

namespace TilingSequence

theorem uniformMeshOnlyDirichlet {n : ℕ} (G : TilingSequence (n + 1))
    (hd : 2 ≤ n + 1) (hmesh : G.MeshConverges) {U : Set (Euc (n + 1))}
    (hU : Bornology.IsBounded U) (hUD : HasAmbientCollar U G.domain) :
    UniformMeshOnlyDirichletTarget G U := by
  obtain ⟨K, hK, hspikeBound⟩ := meshOnly_tiling_spike_bound hd
  intro W hW hUW M hM η hη
  obtain ⟨E, hE, hL2⟩ := G.eventually_uniform_l2_error_le hd hmesh hU hUD hW hUW hM
  obtain ⟨r, hr, hMr, hballs, hgeometry⟩ :=
    G.exists_meshOnly_uniform_radius hmesh hU hUD hW hUW hM hη
  let p := (η / 4) / (2 * M + 3 * η / 4)
  have hp : 0 < p := by dsimp [p]; positivity
  have hrealmesh : Tendsto (fun k => (G.tiling k).mesh.toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp hmesh
  have hvanish := mesh_only_spike_bound_tendsto_zero hd hrealmesh
    (K * Real.sqrt ((4 / η ^ 2) * E)) r
  have hsmall := hvanish.eventually_lt_const hp
  filter_upwards [hL2, G.eventually_finite_boundaryAccessible hmesh hU hUD,
    hgeometry, hsmall] with k hk haccess hgeo hbound
  obtain ⟨hfin, hL2k⟩ := hk
  letI : Fintype ((G.tiling k).closedVertices U) := hfin.fintype
  let T := G.tiling k
  let R := T.closedVertices U
  letI : MeasurableSpace R := ⊤
  let A := T.finiteInterior U
  let N := T.finiteNetwork R
  have ha : N.BoundaryAccessible A := haccess.choose_spec
  intro h hh hC2 hD hsol v hv
  let x : R := ⟨v, Or.inl hv⟩
  have hx : x ∈ A := hv
  have hε : 0 < T.mesh.toReal :=
    T.mesh_toReal_pos_of_accessible_vertex R A ha hgeo.1 hx
  have hposW : ∀ w : R, T.pos w ∈ W := fun w => (hgeo.2.2.2.2 w w.property).1
  have hcell : ∀ w ∈ A, (T.cell w).carrier ⊆ interior T.domain :=
    fun w _ => (hgeo.2.2.2.2 w w.property).2
  have hneighbors : ∀ w ∈ A, ∀ z : T.V, T.adj w z → z ∈ R :=
    fun w hw z hz => T.neighbor_mem_closedVertices hw hz
  let f₀ : R → ℝ := fun w => hD w
  let g₀ : R → ℝ := fun w => h (T.pos w)
  have hsolR : N.SolvesDirichlet A g₀ f₀ := T.solvesDirichlet_restrict hsol
  have hgval : ∀ w : R, |g₀ w| ≤ M := fun w => (hC2 (T.pos w) (hposW w)).1
  have hmax : ∀ w : R, |f₀ w| ≤ M :=
    N.abs_le_of_solvesDirichlet A ha hsolR (fun w _ => hgval w)
  have hL2f : (∑ w : R, (T.cell w).volume.toReal * (f₀ w - g₀ w) ^ 2) ≤
      E * T.mesh.toReal ^ 2 :=
    hL2k h hD hh (fun y hy => (hC2 y hy).2.2) hsol
  have hosc : ∀ w : R, dist (T.pos w) (T.pos x) < r →
      |g₀ w - g₀ x| ≤ η / 4 := by
    intro w hw
    have hxball : T.pos x ∈ Metric.ball (T.pos x) r := by
      simpa only [Metric.mem_ball, dist_self] using hr
    have hb := meshOnly_harmonic_oscillation hW hh
      (fun y hy => (hC2 y hy).2.1) (hballs (T.pos x) hv)
      hxball (Metric.mem_ball.mpr hw)
    exact hb.trans ((mul_le_mul_of_nonneg_left hw.le hM).trans hMr)
  have hno (f g : R → ℝ)
      (hbdy : ∀ w, w ∉ A → f w = g w)
      (hharm : ∀ w ∈ A, N.laplacian f w = 0)
      (hg : -M ≤ g x) (hf : ∀ w, f w ≤ M)
      (hlocal : ∀ w : R, dist (T.pos w) (T.pos x) < r → g w - g x ≤ η / 4)
      (henergy : (∑ w : R, (T.cell w).volume.toReal * (f w - g w) ^ 2) ≤
        E * T.mesh.toReal ^ 2) : ¬ g x + η ≤ f x := by
    intro hspike
    have hb := hspikeBound T R A f g x η M E r hη hM hE hr hgeo.1 hε
      hgeo.2.1 hgeo.2.2.1 (hgeo.2.2.2.1 (T.pos x) hv)
      hcell hneighbors hbdy hharm hg hf hspike hlocal henergy
    exact (not_le_of_gt hbound) hb
  have hpositive := hno f₀ g₀ hsolR.2 hsolR.1 (abs_le.mp (hgval x)).1
    (fun w => (abs_le.mp (hmax w)).2)
    (fun w hw => (le_abs_self _).trans (hosc w hw)) hL2f
  have hL2neg : (∑ w : R, (T.cell w).volume.toReal * ((-f₀) w - (-g₀) w) ^ 2) ≤
      E * T.mesh.toReal ^ 2 := by
    have hsq : ∀ w : R, ((-f₀) w - (-g₀) w) ^ 2 = (f₀ w - g₀ w) ^ 2 := by
      intro w
      simp only [Pi.neg_apply]
      ring
    simpa only [hsq] using hL2f
  have hnegative := hno (-f₀) (-g₀)
    (fun w hw => by simp only [Pi.neg_apply, hsolR.2 w hw])
    (fun w hw => by rw [N.laplacian_neg, hsolR.1 w hw, neg_zero])
    (by have hg := (abs_le.mp (hgval x)).2; change -M ≤ -g₀ x; linarith)
    (fun w => by have hf := (abs_le.mp (hmax w)).1; change -f₀ w ≤ M; linarith)
    (fun w hw => by
      have hg := (abs_le.mp (hosc w hw)).1
      change -g₀ w - -g₀ x ≤ η / 4
      linarith) hL2neg
  have hupper := lt_of_not_ge hpositive
  have hlower := lt_of_not_ge hnegative
  change hD v < h (T.pos v) + η at hupper
  change -hD v < -h (T.pos v) + η at hlower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TilingSequence

/-- Theorem 1.1 of `mesh_only_orthogonal_tilings_vol_notation.pdf`, including
uniformity over bounded C² families and actual eventual well-posedness. -/
theorem meshOnly_theorem11_proved : MeshOnlyTheorem11Statement := by
  intro d G U hd hD _hUopen hU hUD hmesh
  have hcollar : HasAmbientCollar U G.domain := by
    simpa only [HasAmbientCollar, hD.interior_eq] using hUD
  have huniform : UniformMeshOnlyDirichletTarget G U := by
    cases d with
    | zero => omega
    | succ n => exact G.uniformMeshOnlyDirichlet hd hmesh hU hcollar
  exact ⟨fun h hh => dirichletApproximation_of_uniformMeshOnly
    (by omega : 1 ≤ d) G U hU hcollar hmesh huniform h hh, huniform⟩

end BouRabeeGwynne
