import MeshOnly.MeshOnlyPowerWeights
import MeshOnly.MeshOnlyPowerClock
import MeshRates.Section3Heat

/-!
# MR §4: local power potential (Lemma 4.1) and exact clock identity (Lemma 4.2)

Built on the `MeshOnly` local power primitive `exists_meshOnly_local_power_primitive` and the
exact corrected-square identity `discreteLaplacian_correctedSquare`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal

namespace BouRabeeGwynne.MeshRates

/-- Cell formula for a primitive on a convex open set `S`, anchored at any point of
`interior P_v ∩ S` (a variant of `power_cell_formula_of_primitive`, whose anchor is `pos v ∈ S`). -/
theorem mr41_cell_formula_anchor {d : ℕ} (T : OrthogonalTiling d) {S : Set (Euc d)}
    (hS : IsOpen S) (hconv : Convex ℝ S) (ψ : Euc d → ℝ)
    (hψ : ContinuousOn ψ S) (v : T.V) {y₀ : Euc d}
    (hy₀ : y₀ ∈ interior (T.cell v).carrier ∩ S)
    (hderiv : ∀ x ∈ interior (T.cell v).carrier ∩ S,
      HasFDerivAt ψ (2 • innerSL ℝ (x - T.pos v)) x) :
    ∀ y ∈ (T.cell v).carrier ∩ S,
      ψ y = ‖y - T.pos v‖ ^ 2 - (‖y₀ - T.pos v‖ ^ 2 - ψ y₀) := by
  let g : Euc d → ℝ := fun y => ‖y - T.pos v‖ ^ 2 - (‖y₀ - T.pos v‖ ^ 2 - ψ y₀)
  have hg : ∀ x, HasFDerivAt g (2 • innerSL ℝ (x - T.pos v)) x :=
    fun x => (meshOnly_hasFDerivAt_sqDist (T.pos v) x).sub_const _
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have heq : Set.EqOn ψ g (interior (T.cell v).carrier ∩ S) := by
    refine (isOpen_interior.inter hS).eqOn_of_fderiv_eq
      ((T.cell v).convex.interior.inter hconv).isPreconnected
      (fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt)
      (fun x hx => (hderiv x hx).fderiv.trans (hg x).fderiv.symm) hy₀ ?_
    simp [g]
  have hclosure : closure (interior (T.cell v).carrier) = (T.cell v).carrier := by
    rw [(T.cell v).convex.closure_interior_eq_closure_of_nonempty_interior
      (T.cell v).interior_nonempty, (T.cell v).compact.isClosed.closure_eq]
  exact heq.of_subset_closure (hψ.mono Set.inter_subset_right) hgcont.continuousOn
    (Set.inter_subset_inter_left S interior_subset)
    (fun y hy => hS.closure_inter ⟨hclosure.symm ▸ hy.1, hy.2⟩)

/-- MR Lemma 4.1, (46)–(48), with the ε-collar `closedBall z (R + ε) ⊆ interior D` in place of
`B_R(z) ⋐ D`: a `2ε`-Lipschitz `ψ` with `∇ψ = Z = 2(y - v)` on each cell interior in `B_R(z)`, and
for every cell whose interior meets `B_R(z)` a weight `ω_v` with `ψ = ‖· - v‖² - ω_v` on
`P_v ∩ B_R(z)`. -/
theorem lemma41_localPowerPotential {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (hmesh : T.mesh ≠ ∞) (z : Euc d) {R : ℝ} (hR : 0 < R)
    (hcollar : Metric.closedBall z (R + T.mesh.toReal) ⊆ interior T.domain) :
    ∃ ψ : Euc d → ℝ,
      LipschitzWith ⟨2 * T.mesh.toReal, by positivity⟩ ψ ∧
      (∀ v : T.V, ∀ y ∈ interior (T.cell v).carrier ∩ Metric.ball z R,
        HasFDerivAt ψ ((2 : ℝ) • innerSL ℝ (y - T.pos v)) y) ∧
      ∀ v : T.V, (interior (T.cell v).carrier ∩ Metric.ball z R).Nonempty →
        ∃ ωv : ℝ, ∀ y ∈ (T.cell v).carrier ∩ Metric.ball z R, ψ y = ‖y - T.pos v‖ ^ 2 - ωv := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hm : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall z (R + T.mesh.toReal)).exists_cthickening_subset_open
    isOpen_interior hcollar
  rw [cthickening_closedBall hδ.le (by linarith)] at hδsub
  have hcol' : Metric.closedBall z ((R + δ) + T.mesh.toReal) ⊆ interior T.domain := by
    refine (Metric.closedBall_subset_closedBall ?_).trans hδsub; linarith
  obtain ⟨ψ, -, hlip, hderiv⟩ :=
    T.exists_meshOnly_local_power_primitive z (R + δ) R hR (by linarith) hmesh hcol'
  refine ⟨ψ, hlip, fun v y hy => by simpa only [two_smul] using hderiv v y hy, ?_⟩
  rintro v ⟨y₀, hy₀⟩
  exact ⟨_, mr41_cell_formula_anchor T Metric.isOpen_ball (convex_ball z R) ψ
    hlip.continuous.continuousOn v hy₀ (hderiv v)⟩

/-- MR Lemma 4.2, (50)–(52), under MR's hypothesis `B_{r+3ε}(z) ⋐ D`: weights `ω` coming from a
local power potential `ψ` of Lemma 4.1 on `B_{r+2ε}(z)` (the ball on which MR's proof uses (47))
satisfy `LΦ_z = 2d` on `V ∩ B_r(z)` for `Φ_z = ‖· - z‖² - ω`, and `|ω_v - ω_w| ≤ 2ε‖v - w‖` on
`V ∩ B_{r+2ε}(z)`. -/
theorem lemma42_exactClock {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (hmesh : T.mesh ≠ ∞) (z : Euc d) {r : ℝ} (hr : 0 < r)
    (hcollar : Metric.closedBall z (r + 3 * T.mesh.toReal) ⊆ interior T.domain) :
    ∃ (ψ : Euc d → ℝ) (ω : T.V → ℝ),
      LipschitzWith ⟨2 * T.mesh.toReal, by positivity⟩ ψ ∧
      (∀ v : T.V, (interior (T.cell v).carrier ∩ Metric.ball z (r + 2 * T.mesh.toReal)).Nonempty →
        ∀ y ∈ (T.cell v).carrier ∩ Metric.ball z (r + 2 * T.mesh.toReal),
          ψ y = ‖y - T.pos v‖ ^ 2 - ω v) ∧
      (∀ v : T.V, T.pos v ∈ Metric.ball z r → ∀ hv : (T.neighbors v).Finite,
        T.discreteLaplacian (fun u => ‖T.pos u - z‖ ^ 2 - ω u) v hv /
          (T.cell v).volume.toReal = 2 * (d : ℝ)) ∧
      (∀ v w : T.V, T.pos v ∈ Metric.ball z (r + 2 * T.mesh.toReal) →
        T.pos w ∈ Metric.ball z (r + 2 * T.mesh.toReal) →
          |ω v - ω w| ≤ 2 * T.mesh.toReal * ‖T.pos v - T.pos w‖) := by
  classical
  set ε := T.mesh.toReal with hεdef
  have hm : 0 ≤ ε := ENNReal.toReal_nonneg
  have hcol : Metric.closedBall z ((r + 2 * ε) + ε) ⊆ interior T.domain := by
    rw [show (r + 2 * ε) + ε = r + 3 * ε by ring]; exact hcollar
  obtain ⟨ψ, hlip, -, hcell⟩ :=
    lemma41_localPowerPotential hd T hmesh z (R := r + 2 * ε) (by linarith) hcol
  let ω : T.V → ℝ := fun v =>
    if h : (interior (T.cell v).carrier ∩ Metric.ball z (r + 2 * ε)).Nonempty then
      Classical.choose (hcell v h) else 0
  have hω : ∀ v, (interior (T.cell v).carrier ∩ Metric.ball z (r + 2 * ε)).Nonempty →
      ∀ y ∈ (T.cell v).carrier ∩ Metric.ball z (r + 2 * ε), ψ y = ‖y - T.pos v‖ ^ 2 - ω v := by
    intro v h
    simp only [ω, dif_pos h]
    exact Classical.choose_spec (hcell v h)
  -- at a marked point in the ball, `ω v = -ψ v`
  have hωpos : ∀ v, T.pos v ∈ Metric.ball z (r + 2 * ε) → ω v = -ψ (T.pos v) := by
    intro v hv
    have h := hω v ⟨T.pos v, T.pos_mem_interior v, hv⟩ (T.pos v)
      ⟨interior_subset (T.pos_mem_interior v), hv⟩
    simp only [sub_self, norm_zero] at h
    linarith
  refine ⟨ψ, ω, hlip, hω, ?_, ?_⟩
  · intro v hv hvfin
    have hv' := Metric.mem_ball.mp hv
    have hvD : (T.cell v).carrier ⊆ interior T.domain := by
      intro y hy
      apply hcollar
      have := T.toTilingData.dist_pos_le_mesh hy hmesh
      rw [Metric.mem_closedBall]
      linarith [dist_triangle y (T.pos v) z]
    have hL := T.discreteLaplacian_correctedSquare hd v hvD hvfin ω ?_ z
    · rw [hL, mul_div_assoc, div_self (cellVolume_toReal_pos T v).ne', mul_one]
    intro w hvw
    obtain ⟨y, hy⟩ := hvw.2.1
    have hyv := T.toTilingData.dist_pos_le_mesh hy.1 hmesh
    have hyz : y ∈ Metric.ball z (r + 2 * ε) := by
      rw [Metric.mem_ball]; linarith [dist_triangle y (T.pos v) z]
    have hwz : T.pos w ∈ Metric.ball z (r + 2 * ε) := by
      have := T.toTilingData.edge_dist_le_two_mesh hvw hmesh
      rw [Metric.mem_ball]; linarith [dist_triangle (T.pos w) (T.pos v) z, dist_comm (T.pos w) (T.pos v)]
    have hvz : T.pos v ∈ Metric.ball z (r + 2 * ε) := by
      rw [Metric.mem_ball]; linarith
    have hfv := hω v ⟨T.pos v, T.pos_mem_interior v, hvz⟩ y ⟨hy.1, hyz⟩
    have hfw := hω w ⟨T.pos w, T.pos_mem_interior w, hwz⟩ y ⟨hy.2, hyz⟩
    rw [T.powerEdgeGap_eq hvw hy, OrthogonalTiling.powerGapAt]
    linarith
  · intro v w hv hw
    rw [hωpos v hv, hωpos w hw]
    have h := hlip.dist_le_mul (T.pos v) (T.pos w)
    simp only [dist_eq_norm] at h
    rw [show -ψ (T.pos v) - -ψ (T.pos w) = -(ψ (T.pos v) - ψ (T.pos w)) by ring, abs_neg]
    exact h

end BouRabeeGwynne.MeshRates
