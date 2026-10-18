import MeshRates.Section6ExitLaw
import MeshRates.Section6Calculus
import MeshRates.Section3Heat
import MeshOnly.MeshOnlyPowerClock
import BouRabeeGwynne.Section3Accessibility
import BouRabeeGwynne.AffineDiscreteHarmonic

/-!
# MR (75)–(79): the one-sided estimate for one tiling

The law of the stopped position is BRG's discrete harmonic measure of `A = S ∩ B_r(z)` on the
closed region `V̄[U]`; `E_z σ` is the torsion function `G` of `A`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace BouRabeeGwynne.MeshRates

open MeasureTheory
open scoped ENNReal

open Classical in
/-- MR (79), one-sided, for one tiling: with `S = {v ∈ V[U] : f v > η/2}` (72), `A = S ∩ B_r(z)` and
`G` a torsion function of `A` (`ΔG = -m` on `A`, `G = 0` off `A`; this is `E_z σ`, (74)), the error
`f = h_D - h_C` satisfies `f(z) ≤ η/2 + (2/r² + M/2)(2d·G(z) + 2ε(r + 2ε))`. -/
theorem section6_oneSided_estimate {d : ℕ} (hd : 2 ≤ d) (T : OrthogonalTiling d)
    (hmesh : T.mesh ≠ ∞) (U : Set (Euc d)) [Fintype (T.closedVertices U)]
    (hcellU : ∀ v : T.V, T.pos v ∈ U → (T.cell v).carrier ⊆ interior T.domain)
    (h : Euc d → ℝ) (hD : T.V → ℝ) (hsol : T.SolvesDirichlet U (fun v => h (T.pos v)) hD)
    (hf2 : ∀ v : T.closedVertices U, hD v - h (T.pos v) ≤ 2)
    (z : T.closedVertices U) (hz : T.pos z ∈ U) {r η M : ℝ} (hr : 0 < r) (hη : 0 < η)
    (hM : 0 ≤ M) (hsmall : 4 * T.mesh.toReal ≤ r)
    (hball : Metric.closedBall (T.pos z) (2 * r) ⊆ interior T.domain)
    {W : Set (Euc d)} (hW : IsOpen W) (hballW : Metric.closedBall (T.pos z) (2 * r) ⊆ W)
    (hh : ContDiffOn ℝ 2 h W)
    (hH : ∀ x ∈ Metric.closedBall (T.pos z) (2 * r), ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M)
    (G : T.closedVertices U → ℝ)
    (hG : ∀ v : T.closedVertices U,
      (T.pos v ∈ U ∧ η / 2 < hD v - h (T.pos v) ∧ dist (T.pos v) (T.pos z) < r) →
        (T.finiteNetwork (T.closedVertices U)).laplacian G v = -(T.cell v).volume.toReal)
    (hG0 : ∀ v : T.closedVertices U,
      ¬ (T.pos v ∈ U ∧ η / 2 < hD v - h (T.pos v) ∧ dist (T.pos v) (T.pos z) < r) → G v = 0) :
    hD z - h (T.pos z) ≤
      η / 2 + (2 / r ^ 2 + M / 2) *
        (2 * (d : ℝ) * G z + 2 * T.mesh.toReal * (r + 2 * T.mesh.toReal)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  set ε := T.mesh.toReal with hε
  have hε0 : 0 < ε := mesh_toReal_pos_of_ne_top T hmesh z
  let N := T.finiteNetwork (T.closedVertices U)
  letI : MeasurableSpace (T.closedVertices U) := ⊤
  haveI : MeasurableSingletonClass (T.closedVertices U) := ⟨fun _ => trivial⟩
  set A : Set (T.closedVertices U) :=
    {v | T.pos v ∈ U ∧ η / 2 < hD v - h (T.pos v) ∧ dist (T.pos v) (T.pos z) < r} with hA
  set K := 2 / r ^ 2 + M / 2 with hK
  have hK0 : 0 ≤ K := by positivity
  by_cases hzA : z ∉ A
  · have hGz : G z = 0 := hG0 z hzA
    have hfz : hD z - h (T.pos z) ≤ η / 2 := by
      by_contra hc
      exact hzA ⟨hz, lt_of_not_ge hc, by simpa using hr⟩
    rw [hGz]
    have : 0 ≤ K * (2 * ((n + 1 : ℕ) : ℝ) * 0 + 2 * ε * (r + 2 * ε)) := by positivity
    linarith
  push Not at hzA
  have hAU : ∀ v ∈ A, T.pos v ∈ U := fun v hv => hv.1
  have hnb : ∀ v ∈ A, ∀ w, T.adj v w → w ∈ (T.closedVertices U) := fun v hv w hw =>
    T.neighbor_mem_closedVertices (hAU v hv) hw
  -- accessibility of `A`
  let e : Euc (n + 1) := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)
  have he : e ≠ 0 := by
    intro h0
    have := congrArg (fun x : Euc (n + 1) => x 0) h0
    simp [e] at this
  have haccess : N.BoundaryAccessible A :=
    T.finiteNetwork_boundaryAccessible_of_cell_interior (by omega) e he (T.closedVertices U) A hnb
      (fun v hv => hcellU v (hAU v hv))
  have hpos := N.totalConductance_pos_of_boundaryAccessible A haccess
  set H := N.discreteHarmonicMeasure A hpos z with hHdef
  have hint : ∀ g : (T.closedVertices U) → ℝ, Integrable g H := fun g => Integrable.of_finite
  -- exit support: outside `A`, within `r + 2ε` of `z`
  have hexit : ∀ᵐ (w : T.closedVertices U) ∂H, w ∉ A ∧ dist (T.pos w) (T.pos z) < r + 2 * ε := by
    filter_upwards [discreteHarmonicMeasure_ae_exit N A hpos haccess hzA] with w hw
    obtain ⟨hwA, u, huA, hu⟩ := hw
    refine ⟨hwA, ?_⟩
    have hadj : T.adj u w := T.conductanceReal_pos_iff.mp hu
    have h1 := T.toTilingData.edge_dist_le_two_mesh hadj hmesh
    have h2 := huA.2.2
    calc dist (T.pos w) (T.pos z) ≤ dist (T.pos u) (T.pos w) + dist (T.pos u) (T.pos z) :=
          dist_triangle_left _ _ _
      _ < r + 2 * ε := by linarith
  -- optional stopping: `h_D(z) = ∫ h_D dH`
  have hharm : N.SolvesDirichlet A (fun w : (T.closedVertices U) => hD w) (fun w : (T.closedVertices U) => hD w) := by
    refine ⟨fun v hv => ?_, fun _ _ => rfl⟩
    obtain ⟨hvf, hv0⟩ := hsol.1 v (hAU v hv)
    rw [T.closedNetwork_laplacian U hD v (hAU v hv) hvf]
    exact hv0
  have hstop := N.integral_discreteHarmonicMeasure_of_solvesDirichlet A hpos haccess hharm z
  -- (75): linear functions are harmonic
  set L := fderiv ℝ h (T.pos z) with hL
  have haff : N.SolvesDirichlet A (fun w : (T.closedVertices U) => L (T.pos w) + -L (T.pos z))
      (fun w : (T.closedVertices U) => L (T.pos w) + -L (T.pos z)) := by
    refine ⟨fun v hv => ?_, fun _ _ => rfl⟩
    obtain ⟨hvf, hv0⟩ := T.discreteHarmonicOn_affine (by omega) (T.interiorVertices U)
      (fun v hv => hcellU v hv) L (-L (T.pos z)) v (hAU v hv)
    rw [T.closedNetwork_laplacian U (fun w => L (T.pos w) + -L (T.pos z)) v (hAU v hv) hvf]
    exact hv0
  have h75 : ∫ (w : T.closedVertices U), L (T.pos w - T.pos z) ∂H = 0 := by
    have e1 := N.integral_discreteHarmonicMeasure_of_solvesDirichlet A hpos haccess haff z
    have e2 : (fun w : (T.closedVertices U) => L (T.pos w - T.pos z)) = fun w : T.closedVertices U => L (T.pos w) + -L (T.pos z) := by
      funext w; rw [map_sub, sub_eq_add_neg]
    rw [e2, e1]; ring
  -- (76): the clock potential and Dynkin's identity
  have hβ : r + 2 * ε < r + 5 / 2 * ε := by linarith
  have hcollar : Metric.closedBall (T.pos z) (r + 3 * ε + ε) ⊆ interior T.domain :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  obtain ⟨ω, hωlip, hωclock⟩ := T.exists_meshOnly_finiteNetwork_clock_potential (T.pos z)
    (r + 3 * ε) (r + 5 / 2 * ε) r (by linarith) (by linarith) hmesh hβ hcollar (T.closedVertices U)
  set c : ℝ := 2 * ((n + 1 : ℕ) : ℝ) with hc
  have hdyn := integral_discreteHarmonicMeasure_dynkin N A hpos haccess
    (fun w : (T.closedVertices U) => (T.cell w).volume.toReal) c (fun w : (T.closedVertices U) => ‖T.pos w - T.pos z‖ ^ 2 - ω w) G
    (fun v hv => by
      have h1 := hωclock v (by rw [Metric.mem_ball]; exact hv.2.2)
        (fun w hw => T.neighbor_mem_closedVertices (hAU v hv) hw)
      have hm := T.meshOnly_cellVolume_toReal_pos v
      unfold FiniteConductanceNetwork.massGenerator at h1
      rw [div_eq_iff hm.ne'] at h1
      exact h1)
    (fun v hv => hG v hv) (fun v hv => hG0 v hv) z
  have h76 : ∫ (w : T.closedVertices U), ‖T.pos w - T.pos z‖ ^ 2 ∂H ≤ c * G z + 2 * ε * (r + 2 * ε) := by
    have hle : ∀ᵐ (w : T.closedVertices U) ∂H, ‖T.pos w - T.pos z‖ ^ 2 ≤
        (‖T.pos w - T.pos z‖ ^ 2 - ω w) + (ω z + 2 * ε * (r + 2 * ε)) := by
      filter_upwards [hexit] with w hw
      have hl := hωlip z w (Metric.mem_ball_self (by linarith))
        (by rw [Metric.mem_ball]; linarith [hw.2])
      have hn : ‖T.pos w - T.pos z‖ ≤ r + 2 * ε := by rw [← dist_eq_norm]; exact hw.2.le
      have h3 := (abs_le.mp hl).2
      have h4 := mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ) ≤ 2 * ε)
      linarith
    calc _ ≤ ∫ (w : T.closedVertices U), ((‖T.pos w - T.pos z‖ ^ 2 - ω w) + (ω z + 2 * ε * (r + 2 * ε))) ∂H :=
          integral_mono_ae (hint _) (hint _) hle
      _ = c * G z + 2 * ε * (r + 2 * ε) := by
        rw [integral_add (hint _) (integrable_const _), hdyn, integral_const]
        simp; ring
  -- (77)–(79): pointwise bound on the exit support
  have hmain : ∀ᵐ (w : T.closedVertices U) ∂H, hD w - h (T.pos z) ≤
      η / 2 + L (T.pos w - T.pos z) + K * ‖T.pos w - T.pos z‖ ^ 2 := by
    filter_upwards [hexit] with w hw
    have hwB : T.pos w ∈ Metric.closedBall (T.pos z) (2 * r) := by
      rw [Metric.mem_closedBall]; linarith [hw.2]
    have htay := taylor_first_order_remainder_le hW hh (convex_closedBall _ _) hballW hH
      (Metric.mem_closedBall_self (by linarith)) hwB
    have htay' := (abs_le.mp htay).2
    have hfw : hD w - h (T.pos w) ≤ η / 2 + 2 / r ^ 2 * ‖T.pos w - T.pos z‖ ^ 2 := by
      by_cases hwU : T.pos w ∈ U
      · by_cases hwS : η / 2 < hD w - h (T.pos w)
        · have hrw : r ≤ ‖T.pos w - T.pos z‖ := by
            rw [← dist_eq_norm]; by_contra hc'; exact hw.1 ⟨hwU, hwS, lt_of_not_ge hc'⟩
          have h1 : 1 ≤ ‖T.pos w - T.pos z‖ ^ 2 / r ^ 2 := by
            rw [le_div_iff₀ (by positivity)]; nlinarith
          have h2 := hf2 w
          have h3 : 2 / r ^ 2 * ‖T.pos w - T.pos z‖ ^ 2 =
              2 * (‖T.pos w - T.pos z‖ ^ 2 / r ^ 2) := by ring
          linarith
        · have : 0 ≤ 2 / r ^ 2 * ‖T.pos w - T.pos z‖ ^ 2 := by positivity
          push Not at hwS; linarith
      · have hbd : (w : T.V) ∈ T.boundaryVertices U := w.property.resolve_left hwU
        rw [hsol.2 w hbd, sub_self]
        positivity
    have hKe : K * ‖T.pos w - T.pos z‖ ^ 2 =
        2 / r ^ 2 * ‖T.pos w - T.pos z‖ ^ 2 + M / 2 * ‖T.pos w - T.pos z‖ ^ 2 := by
      rw [hK]; ring
    linarith
  have hint1 : hD z - h (T.pos z) = ∫ (w : T.closedVertices U), (hD w - h (T.pos z)) ∂H := by
    rw [integral_sub (hint _) (integrable_const _), integral_const, hstop]
    simp
  rw [hint1]
  calc _ ≤ ∫ (w : T.closedVertices U), (η / 2 + L (T.pos w - T.pos z) + K * ‖T.pos w - T.pos z‖ ^ 2) ∂H :=
        integral_mono_ae (hint _) (hint _) hmain
    _ = η / 2 + 0 + K * ∫ (w : T.closedVertices U), ‖T.pos w - T.pos z‖ ^ 2 ∂H := by
        rw [integral_add (hint _) (hint _), integral_add (integrable_const _) (hint _),
          integral_const, h75, integral_const_mul]
        simp
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h76 hK0
        rw [hc] at this
        linarith

end BouRabeeGwynne.MeshRates
