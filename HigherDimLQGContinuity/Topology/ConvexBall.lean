import HigherDimLQGMetric.Topology.NonSepCone
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Convex sets minus a closed ball: contractible loops (NS-2′, `d ≥ 3`) and path-connectedness
(`d ≥ 2`)

Packet Q1 (ruling N9). Source: planning audit `planning/audits/NA2-section-4.md`, Details (c) **R1**
(NS-2′ and the leaves lemma of the bisection behind Lemma 4.1′).

Let `Ω ⊆ ℝ^d` be open and convex and `B̄(p, ρ) ⊆ Ω`. For `ρ ≥ 0` pick `ρ₁ > ρ` with `B̄(p, ρ₁) ⊆ Ω`
(compactness) and let `R(x) = p + (ρ₁ / |x - p|)(x - p)` be the radial retraction of `ℝ^d ∖ {p}` onto
the sphere `S(p, ρ₁)`. For `x ∈ W := Ω ∖ B̄(p, ρ)` the segment `[x, R x]` stays in `W`: its points
lie on the ray from `p` through `x` at distance between `|x - p| > ρ` and `ρ₁ > ρ` from `p`, and in
`Ω` by convexity.

* `loopsContractibleIn_convex_diff_closedBall` (**NS-2′**, `d ≥ 3`): every loop in `W` is freely
  null-homotopic in `W`. The loop `ℓ` is pushed to `R ∘ ℓ` by the straight-line homotopy; `R ∘ ℓ`
  lies in the punctured ball `B(p, 2ρ₁) ∖ {p}`, where it is null-homotopic by the library's NS-2
  (`HigherDimLQGMetric.Topology.loopsContractibleIn_ball_diff`), and the null-homotopy is
  retracted back to `S(p, ρ₁) ⊆ W` by `R` (which fixes `R ∘ ℓ`). This replaces the audit's
  polygonal "rotation away from a missed direction" step by a reuse of NS-2.
* `joinedIn_convex_diff_closedBall` (the leaves, `d ≥ 2`): `W` is path-connected: push both
  points radially to `S(p, ρ₁)` and join them on the sphere (`isPathConnected_sphere`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity.Topology

open Set Metric unitInterval
open HigherDimLFPP (Rd)
open HigherDimLQGMetric.Topology (LoopsContractibleIn loopsContractibleIn_ball_diff)

variable {d : ℕ}

/-! ### The radial retraction onto a sphere -/

/-- The radial retraction `x ↦ p + (ρ₁ / |x - p|)(x - p)` of `ℝ^d ∖ {p}` onto the sphere
`S(p, ρ₁)`. -/
def sphereRetract (p : Rd d) (ρ₁ : ℝ) (x : Rd d) : Rd d :=
  p + (ρ₁ / ‖x - p‖) • (x - p)

lemma sphereRetract_sub (p : Rd d) (ρ₁ : ℝ) (x : Rd d) :
    sphereRetract p ρ₁ x - p = (ρ₁ / ‖x - p‖) • (x - p) := by
  rw [sphereRetract, add_sub_cancel_left]

lemma norm_sphereRetract_sub {p x : Rd d} {ρ₁ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hx : x ≠ p) :
    ‖sphereRetract p ρ₁ x - p‖ = ρ₁ := by
  have hpos : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  rw [sphereRetract_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_mul_cancel₀ _ hpos.ne']

lemma sphereRetract_mem_sphere {p x : Rd d} {ρ₁ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hx : x ≠ p) :
    sphereRetract p ρ₁ x ∈ sphere p ρ₁ := by
  rw [mem_sphere, dist_eq_norm, norm_sphereRetract_sub hρ₁ hx]

lemma sphereRetract_ne {p x : Rd d} {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) (hx : x ≠ p) :
    sphereRetract p ρ₁ x ≠ p := by
  intro h
  have := norm_sphereRetract_sub hρ₁.le hx
  rw [h, sub_self, norm_zero] at this
  exact hρ₁.ne this

/-- `R` fixes the points of the sphere `S(p, ρ₁)`, so `R ∘ R = R` off `p`. -/
lemma sphereRetract_sphereRetract {p x : Rd d} {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) (hx : x ≠ p) :
    sphereRetract p ρ₁ (sphereRetract p ρ₁ x) = sphereRetract p ρ₁ x := by
  conv_lhs => rw [sphereRetract, norm_sphereRetract_sub hρ₁.le hx, div_self hρ₁.ne', one_smul,
    add_sub_cancel]

lemma continuousOn_sphereRetract (p : Rd d) (ρ₁ : ℝ) :
    ContinuousOn (sphereRetract p ρ₁) {p}ᶜ := by
  intro x hx
  have hx' : ‖x - p‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hx)
  apply ContinuousAt.continuousWithinAt
  unfold sphereRetract
  exact continuousAt_const.add
    ((continuousAt_const.div (continuous_id.sub continuous_const).norm.continuousAt hx').smul
      (continuous_id.sub continuous_const).continuousAt)

/-- The radial segment `[x, R x]` stays in `Ω ∖ B̄(p, ρ)`. -/
lemma segment_sphereRetract_subset {Ω : Set (Rd d)} (hΩc : Convex ℝ Ω) {p : Rd d} {ρ ρ₁ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρρ₁ : ρ < ρ₁) (hρ₁Ω : closedBall p ρ₁ ⊆ Ω) {x : Rd d}
    (hx : x ∈ Ω \ closedBall p ρ) :
    segment ℝ x (sphereRetract p ρ₁ x) ⊆ Ω \ closedBall p ρ := by
  have hxp : ρ < ‖x - p‖ := by
    have := hx.2
    rwa [mem_closedBall, dist_eq_norm, not_le] at this
  have hxp0 : x ≠ p := by
    rintro rfl
    exact hx.2 (mem_closedBall_self hρ0)
  have hpos : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hxp0)
  have hρ₁ : 0 ≤ ρ₁ := by linarith
  have hRΩ : sphereRetract p ρ₁ x ∈ Ω :=
    hρ₁Ω (sphere_subset_closedBall (sphereRetract_mem_sphere hρ₁ hxp0))
  intro w hw
  refine ⟨hΩc.segment_subset hx.1 hRΩ hw, ?_⟩
  rw [segment_eq_image] at hw
  obtain ⟨τ, ⟨hτ0, hτ1⟩, rfl⟩ := hw
  rw [mem_closedBall, dist_eq_norm, not_le]
  have hsub : (1 - τ) • x + τ • sphereRetract p ρ₁ x - p =
      ((1 - τ) + τ * (ρ₁ / ‖x - p‖)) • (x - p) := by
    rw [sphereRetract]
    module
  have hcoef : 0 ≤ (1 - τ) + τ * (ρ₁ / ‖x - p‖) := by
    have : 0 ≤ τ * (ρ₁ / ‖x - p‖) := mul_nonneg hτ0 (by positivity)
    linarith
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, add_mul, mul_assoc,
    div_mul_cancel₀ _ hpos.ne']
  have hm : 0 < min (‖x - p‖ - ρ) (ρ₁ - ρ) := lt_min (by linarith) (by linarith)
  have h1 : (1 - τ) * min (‖x - p‖ - ρ) (ρ₁ - ρ) ≤ (1 - τ) * (‖x - p‖ - ρ) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) (by linarith)
  have h2 : τ * min (‖x - p‖ - ρ) (ρ₁ - ρ) ≤ τ * (ρ₁ - ρ) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hτ0
  nlinarith

/-- For `0 ≤ ρ` and `B̄(p, ρ) ⊆ Ω` open, some `ρ₁ > ρ` still has `B̄(p, ρ₁) ⊆ Ω`. -/
lemma exists_closedBall_subset_of_closedBall {Ω : Set (Rd d)} (hΩ : IsOpen Ω) {p : Rd d}
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : closedBall p ρ ⊆ Ω) :
    ∃ ρ₁, ρ < ρ₁ ∧ closedBall p ρ₁ ⊆ Ω := by
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_closedBall p ρ).exists_cthickening_subset_open hΩ hρ
  rw [cthickening_closedBall hδ.le hρ0] at hδΩ
  exact ⟨δ + ρ, by linarith, hδΩ⟩

/-! ### NS-2′: loops in a convex set minus a closed ball (`d ≥ 3`) -/

/-- **NS-2′.** For `d ≥ 3`, `Ω ⊆ ℝ^d` open and convex and `B̄(p, ρ) ⊆ Ω`, every loop in
`Ω ∖ B̄(p, ρ)` is freely null-homotopic in `Ω ∖ B̄(p, ρ)` (cylinder form `LoopsContractibleIn`). -/
theorem loopsContractibleIn_convex_diff_closedBall (hd : 3 ≤ d) {Ω : Set (Rd d)} (hΩ : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {p : Rd d} {ρ : ℝ} (hρ : closedBall p ρ ⊆ Ω) :
    LoopsContractibleIn (Ω \ closedBall p ρ) := by
  intro ℓ hℓ hloop
  rcases lt_or_ge ρ 0 with hneg | hnn
  · -- `B̄(p, ρ) = ∅`: straight-line contraction in the convex set `Ω`
    have hW : Ω \ closedBall p ρ = Ω := by rw [closedBall_eq_empty.2 hneg, sdiff_empty]
    set K := ContinuousMap.Homotopy.affine ℓ (ContinuousMap.const I (ℓ 0)) with hK
    refine ⟨K.toContinuousMap.comp ContinuousMap.prodSwap, ?_, ?_, ?_, ℓ 0, ?_⟩
    · rintro ⟨s, t⟩
      show K (t, s) ∈ Ω \ closedBall p ρ
      rw [hW, hK, ContinuousMap.Homotopy.affine_apply]
      have hs : ℓ s ∈ Ω := by have := hℓ s; rwa [hW] at this
      have h0 : ℓ 0 ∈ Ω := by have := hℓ 0; rwa [hW] at this
      exact hΩc.lineMap_mem hs h0 ⟨t.2.1, t.2.2⟩
    · intro s
      show K (0, s) = ℓ s
      exact K.apply_zero s
    · intro t
      show K (t, 0) = K (t, 1)
      simp only [hK, ContinuousMap.Homotopy.affine_apply, hloop, ContinuousMap.const_apply]
    · intro s
      show K (1, s) = ℓ 0
      rw [K.apply_one]
      rfl
  · obtain ⟨ρ₁, hρρ₁, hρ₁Ω⟩ := exists_closedBall_subset_of_closedBall hΩ hnn hρ
    have hρ₁ : 0 < ρ₁ := lt_of_le_of_lt hnn hρρ₁
    set R := sphereRetract p ρ₁ with hR
    have hℓp : ∀ s, ℓ s ≠ p := by
      intro s h
      exact (hℓ s).2 (h ▸ mem_closedBall_self hnn)
    have hcompl : ∀ s, ℓ s ∈ ({p}ᶜ : Set (Rd d)) := fun s => hℓp s
    -- the pushed loop `R ∘ ℓ` on the sphere `S(p, ρ₁)`
    set Rℓ : C(I, Rd d) := ⟨fun s => R (ℓ s),
      (continuousOn_sphereRetract p ρ₁).comp_continuous ℓ.continuous hcompl⟩ with hRℓ
    have hRℓ_mem : ∀ s, Rℓ s ∈ ball p (2 * ρ₁) \ {p} := by
      intro s
      refine ⟨?_, sphereRetract_ne hρ₁ (hℓp s)⟩
      rw [mem_ball, dist_eq_norm]
      show ‖sphereRetract p ρ₁ (ℓ s) - p‖ < 2 * ρ₁
      rw [norm_sphereRetract_sub hρ₁.le (hℓp s)]
      linarith
    -- NS-2 in the punctured ball `B(p, 2ρ₁) ∖ {p}`
    obtain ⟨H', hH'W, hH'0, hH'side, c', hc'⟩ :=
      loopsContractibleIn_ball_diff hd p (2 * ρ₁) p Rℓ hRℓ_mem
        (by simp only [hRℓ, ContinuousMap.coe_mk, hloop])
    have hH'p : ∀ q, H' q ∈ ({p}ᶜ : Set (Rd d)) := fun q => (hH'W q).2
    have hc'p : c' ≠ p := by rw [← hc' 0]; exact (hH'W _).2
    -- the two homotopies `ℓ ≃ R ∘ ℓ ≃ const (R c')`
    set K₁ := ContinuousMap.Homotopy.affine ℓ Rℓ with hK₁
    let K₂ : Rℓ.Homotopy (ContinuousMap.const I (R c')) :=
      { toFun := fun q => R (H' (q.2, q.1))
        continuous_toFun := (continuousOn_sphereRetract p ρ₁).comp_continuous
          (H'.continuous.comp continuous_swap) fun q => hH'p _
        map_zero_left := fun s => by
          show R (H' (s, 0)) = R (ℓ s)
          rw [hH'0]
          exact sphereRetract_sphereRetract hρ₁ (hℓp s)
        map_one_left := fun s => by
          show R (H' (s, 1)) = R c'
          rw [hc' s] }
    have hK₂ : ∀ q, K₂ q = R (H' (q.2, q.1)) := fun q => rfl
    set K := K₁.trans K₂ with hK
    have hWsph : ∀ z, z ≠ p → R z ∈ Ω \ closedBall p ρ := by
      intro z hz
      have hzs := sphereRetract_mem_sphere hρ₁.le hz
      refine ⟨hρ₁Ω (sphere_subset_closedBall hzs), ?_⟩
      rw [mem_closedBall, not_le, mem_sphere.1 hzs]
      exact hρρ₁
    refine ⟨K.toContinuousMap.comp ContinuousMap.prodSwap, ?_, ?_, ?_, R c', ?_⟩
    · rintro ⟨s, t⟩
      show K (t, s) ∈ Ω \ closedBall p ρ
      rw [hK, ContinuousMap.Homotopy.trans_apply]
      split_ifs with h
      · rw [hK₁, ContinuousMap.Homotopy.affine_apply]
        apply segment_sphereRetract_subset hΩc hnn hρρ₁ hρ₁Ω (hℓ s)
        rw [segment_eq_image_lineMap]
        exact ⟨_, ⟨by simp only; linarith [t.2.1], by simp only; linarith⟩, rfl⟩
      · rw [hK₂]
        exact hWsph _ (hH'p _)
    · intro s
      show K (0, s) = ℓ s
      exact K.apply_zero s
    · intro t
      show K (t, 0) = K (t, 1)
      rw [hK, ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
      split_ifs with h
      · simp only [hK₁, ContinuousMap.Homotopy.affine_apply, hloop, hRℓ, ContinuousMap.coe_mk]
      · rw [hK₂, hK₂]
        simp only
        rw [hH'side]
    · intro s
      show K (1, s) = R c'
      rw [K.apply_one]
      rfl

/-! ### The leaves: convex set minus a closed ball is path-connected (`d ≥ 2`) -/

private lemma q1_rank_Rd_gt_one (hd : 2 ≤ d) : 1 < Module.rank ℝ (Rd d) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (show 1 < d by omega)

/-- **Leaves of the bisection.** For `d ≥ 2`, `Ω ⊆ ℝ^d` open and convex and `B̄(p, ρ) ⊆ Ω`, any two
points of `Ω ∖ B̄(p, ρ)` are joined by a path in `Ω ∖ B̄(p, ρ)`. -/
theorem joinedIn_convex_diff_closedBall (hd : 2 ≤ d) {Ω : Set (Rd d)} (hΩ : IsOpen Ω)
    (hΩc : Convex ℝ Ω) {p : Rd d} {ρ : ℝ} (hρ : closedBall p ρ ⊆ Ω) {x y : Rd d}
    (hx : x ∈ Ω \ closedBall p ρ) (hy : y ∈ Ω \ closedBall p ρ) :
    JoinedIn (Ω \ closedBall p ρ) x y := by
  rcases lt_or_ge ρ 0 with hneg | hnn
  · have hW : Ω \ closedBall p ρ = Ω := by rw [closedBall_eq_empty.2 hneg, sdiff_empty]
    rw [hW] at hx hy ⊢
    exact JoinedIn.of_segment_subset (hΩc.segment_subset hx hy)
  · obtain ⟨ρ₁, hρρ₁, hρ₁Ω⟩ := exists_closedBall_subset_of_closedBall hΩ hnn hρ
    have hρ₁ : 0 < ρ₁ := lt_of_le_of_lt hnn hρρ₁
    have hne : ∀ z ∈ Ω \ closedBall p ρ, z ≠ p := by
      rintro z hz rfl
      exact hz.2 (mem_closedBall_self hnn)
    have hsphW : sphere p ρ₁ ⊆ Ω \ closedBall p ρ := by
      intro z hz
      refine ⟨hρ₁Ω (sphere_subset_closedBall hz), ?_⟩
      rw [mem_closedBall, not_le, mem_sphere.1 hz]
      exact hρρ₁
    have hx' := JoinedIn.of_segment_subset (segment_sphereRetract_subset hΩc hnn hρρ₁ hρ₁Ω hx)
    have hy' := JoinedIn.of_segment_subset (segment_sphereRetract_subset hΩc hnn hρρ₁ hρ₁Ω hy)
    have hsph : JoinedIn (Ω \ closedBall p ρ) (sphereRetract p ρ₁ x) (sphereRetract p ρ₁ y) :=
      ((isPathConnected_sphere (q1_rank_Rd_gt_one hd) p hρ₁.le).joinedIn _
        (sphereRetract_mem_sphere hρ₁.le (hne x hx)) _
        (sphereRetract_mem_sphere hρ₁.le (hne y hy))).mono hsphW
    exact (hx'.trans hsph).trans hy'.symm

end HigherDimLQGContinuity.Topology

end
