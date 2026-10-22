import HigherDimLQGContinuity.ForcingCount.SiteNorm
import HigherDimLQGMetric.LogEnergy.Affine
import HigherDimLQGMetric.LogEnergy.QuantCM
import HigherDimLQGMetric.Field.SphereAvgBasic

/-!
# Placed bumps and selections

Packet Q9 (deterministic). Part B `b:def-catalogue`(b): for a valid catalogue and a selection `Z`, the supports of
different sites are disjoint, `f_Z = f_{z_i,s,ℓ}` on `B̄_{4s}(z_i)` for `(z_i, ℓ) ∈ Z`, `f_Z` vanishes off the placed
collectors (so on every site sphere `∂B_s(z)` and off `B₄`), `f_Z ≥ 0`, and `f_Z` is Cameron–Martin bounded with
constant `#Z · |M| · C` (`b:lem-bump`). Site units are unchanged by functions vanishing on the site sphere, wherever
the sphere averages converge (`b:lem-site-normal`(b)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

theorem q9Bump_apply (ψ : C(Rd d, ℝ)) (M : ℝ) (z : Rd d) (s : ℝ) (x : Rd d) :
    q9Bump ψ M z s x = M * ψ (s⁻¹ • (x - z)) := rfl

theorem q9_norm_siteCoord {z x : Rd d} {s : ℝ} (hs : 0 < s) : ‖s⁻¹ • (x - z)‖ = s⁻¹ * ‖x - z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]

/-- A placed bump vanishes off its placed collector `annCl z (3s/2) (5s/2)`. -/
theorem q9Bump_eq_zero_of_notMem {ψ : C(Rd d, ℝ)} {M : ℝ} {z : Rd d} {s : ℝ} (hs : 0 < s)
    (hψ : tsupport ψ ⊆ siteC d) {x : Rd d} (hx : x ∉ annCl z (3 * s / 2) (5 * s / 2)) :
    q9Bump ψ M z s x = 0 := by
  rw [q9Bump_apply]
  have hnot : s⁻¹ • (x - z) ∉ tsupport ψ := by
    intro h
    apply hx
    have hC := hψ h
    simp only [siteC, annCl, mem_ofPred_eq, sub_zero, q9_norm_siteCoord hs] at hC
    have h1 : 3 / 2 ≤ s⁻¹ * ‖x - z‖ := hC.1
    have h2 : s⁻¹ * ‖x - z‖ ≤ 5 / 2 := hC.2
    have h1' : 3 * s / 2 ≤ ‖x - z‖ := by
      have := mul_le_mul_of_nonneg_left h1 hs.le
      rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at this
      linarith
    have h2' : ‖x - z‖ ≤ 5 * s / 2 := by
      have := mul_le_mul_of_nonneg_left h2 hs.le
      rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at this
      linarith
    exact ⟨h1', h2'⟩
  rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]

theorem tsupport_q9Bump_subset {ψ : C(Rd d, ℝ)} {M : ℝ} {z : Rd d} {s : ℝ} (hs : 0 < s)
    (hψ : tsupport ψ ⊆ siteC d) : tsupport (q9Bump ψ M z s) ⊆ annCl z (3 * s / 2) (5 * s / 2) := by
  refine closure_minimal (fun x hx => ?_) (isClosed_annCl _ _ _)
  by_contra h
  exact hx (q9Bump_eq_zero_of_notMem hs hψ h)

theorem q9_annCl_subset_closedBall {z : Rd d} {s : ℝ} (hs : 0 < s) :
    annCl z (3 * s / 2) (5 * s / 2) ⊆ closedBall z (4 * s) := by
  intro x hx
  simp only [annCl, mem_ofPred_eq] at hx
  rw [mem_closedBall, dist_eq_norm]
  linarith [hx.2]

theorem q9_sphere_disjoint_annCl {z : Rd d} {s : ℝ} (hs : 0 < s) {x : Rd d} (hx : x ∈ sphere z s) :
    x ∉ annCl z (3 * s / 2) (5 * s / 2) := by
  intro h
  simp only [annCl, mem_ofPred_eq] at h
  rw [mem_sphere, dist_eq_norm] at hx
  linarith [h.1]

/-- Pulled back to site coordinates, a placed bump is the scaled profile. -/
theorem q9Bump_comp_aff (ψ : C(Rd d, ℝ)) (M : ℝ) (z : Rd d) {s : ℝ} (hs : 0 < s) :
    (q9Bump ψ M z s).comp (ContMetric.affineMap s z) = M • ψ := by
  ext u
  simp only [ContinuousMap.comp_apply, ContMetric.affineMap_apply, q9Bump_apply,
    ContinuousMap.smul_apply, smul_eq_mul, add_sub_cancel_right, smul_smul,
    inv_mul_cancel₀ hs.ne', one_smul]

theorem q9Bump_nonneg {ψ : C(Rd d, ℝ)} {M : ℝ} (hM : 0 ≤ M) (hψ : ∀ x, 0 ≤ ψ x) (z : Rd d) (s : ℝ)
    (x : Rd d) : 0 ≤ q9Bump ψ M z s x := by
  rw [q9Bump_apply]
  exact mul_nonneg hM (hψ _)

theorem q9Bump_le {ψ : C(Rd d, ℝ)} {M : ℝ} (hM : 0 ≤ M) (hψ : ∀ x, ψ x ≤ 1) (z : Rd d) (s : ℝ)
    (x : Rd d) : q9Bump ψ M z s x ≤ M := by
  rw [q9Bump_apply]
  calc M * ψ (s⁻¹ • (x - z)) ≤ M * 1 := mul_le_mul_of_nonneg_left (hψ _) hM
    _ = M := mul_one M

/-! ## Selections -/

section Selection

open Classical

variable (K : CountData d) (𝔆 : Catalogue d)

theorem selBump_apply (s : ℝ) (Z : Finset (Rd d × K.cat.Label)) (x : Rd d) :
    selBump K s Z x = ∑ p ∈ Z, q9Bump (K.cat.prof p.2) K.M p.1 s x := by
  simp only [selBump, ContinuousMap.sum_apply]

variable {K 𝔆}

theorem selBump_nonneg (hM : 0 ≤ K.M) (hprof : ∀ ℓ x, 0 ≤ K.cat.prof ℓ x) (s : ℝ)
    (Z : Finset (Rd d × K.cat.Label)) (x : Rd d) : 0 ≤ selBump K s Z x := by
  rw [selBump_apply]
  exact Finset.sum_nonneg fun p _ => q9Bump_nonneg hM (hprof p.2) _ _ _

theorem selBump_eq_zero_of_notMem {s : ℝ} (hs : 0 < s) (hprof : ∀ ℓ, tsupport (K.cat.prof ℓ) ⊆ siteC d)
    {Z : Finset (Rd d × K.cat.Label)} {x : Rd d}
    (hx : ∀ p ∈ Z, x ∉ annCl p.1 (3 * s / 2) (5 * s / 2)) : selBump K s Z x = 0 := by
  rw [selBump_apply]
  exact Finset.sum_eq_zero fun p hp => q9Bump_eq_zero_of_notMem hs (hprof p.2) (hx p hp)

theorem tsupport_selBump_subset {s : ℝ} (hs : 0 < s) (hprof : ∀ ℓ, tsupport (K.cat.prof ℓ) ⊆ siteC d)
    (Z : Finset (Rd d × K.cat.Label)) :
    tsupport (selBump K s Z) ⊆ ⋃ p ∈ Z, annCl p.1 (3 * s / 2) (5 * s / 2) := by
  refine closure_minimal (fun x hx => ?_) ?_
  · by_contra h
    simp only [mem_iUnion, not_exists] at h
    exact hx (selBump_eq_zero_of_notMem hs hprof fun p hp => h p hp)
  · exact isClosed_biUnion_finset fun p _ => isClosed_annCl _ _ _

/-- On the full inspection of one of its sites, `f_Z` is the bump of that site. -/
theorem selBump_eq_on_ball (hV : 𝔆.Valid K.x K.y) (hprof : ∀ ℓ, tsupport (K.cat.prof ℓ) ⊆ siteC d)
    {Z : Finset (Rd d × K.cat.Label)} (hZ : IsSelection 𝔆 Z) {p : Rd d × K.cat.Label} (hp : p ∈ Z)
    {x : Rd d} (hx : x ∈ closedBall p.1 (4 * 𝔆.s)) :
    selBump K 𝔆.s Z x = q9Bump (K.cat.prof p.2) K.M p.1 𝔆.s x := by
  have hs := hV.1
  rw [selBump_apply, ← Finset.add_sum_erase Z _ hp]
  have hzero : ∑ q ∈ Z.erase p, q9Bump (K.cat.prof q.2) K.M q.1 𝔆.s x = 0 := by
    refine Finset.sum_eq_zero fun q hq => q9Bump_eq_zero_of_notMem hs (hprof q.2) ?_
    intro hxq
    have hqZ := Finset.mem_of_mem_erase hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    have hne : q.1 ≠ p.1 := fun h => hqp (hZ.2 q hqZ p hp h)
    have hdisj := hV.2.2.2.2 q.1 (hZ.1 q hqZ) p.1 (hZ.1 p hp) hne
    exact Set.disjoint_left.1 hdisj (q9_annCl_subset_closedBall hs hxq) hx
  rw [hzero, add_zero]

/-- `f_Z` vanishes on every site sphere `∂B_s(z)`, `z ∈ 𝒵`. -/
theorem selBump_zero_on_sphere (hV : 𝔆.Valid K.x K.y) (hprof : ∀ ℓ, tsupport (K.cat.prof ℓ) ⊆ siteC d)
    {Z : Finset (Rd d × K.cat.Label)} (hZ : IsSelection 𝔆 Z) {z : Rd d} (hz : z ∈ 𝔆.Z) {x : Rd d}
    (hx : x ∈ sphere z 𝔆.s) : selBump K 𝔆.s Z x = 0 := by
  have hs := hV.1
  refine selBump_eq_zero_of_notMem hs hprof fun p hp hxp => ?_
  by_cases hpz : p.1 = z
  · rw [hpz] at hxp
    exact q9_sphere_disjoint_annCl hs hx hxp
  · have hdisj := hV.2.2.2.2 p.1 (hZ.1 p hp) z hz hpz
    have hxz : x ∈ closedBall z (4 * 𝔆.s) := by
      rw [mem_sphere] at hx
      rw [mem_closedBall]
      linarith
    exact Set.disjoint_left.1 hdisj (q9_annCl_subset_closedBall hs hxp) hxz

theorem tsupport_selBump_ball (hV : 𝔆.Valid K.x K.y) (hprof : ∀ ℓ, tsupport (K.cat.prof ℓ) ⊆ siteC d)
    {Z : Finset (Rd d × K.cat.Label)} (hZ : IsSelection 𝔆 Z) :
    tsupport (selBump K 𝔆.s Z) ⊆ ball (0 : Rd d) 4 := by
  refine (tsupport_selBump_subset hV.1 hprof Z).trans ?_
  simp only [iUnion_subset_iff]
  intro p hp
  exact (q9_annCl_subset_closedBall hV.1).trans ((hV.2.2.2.1 p.1 (hZ.1 p hp)).1)

/-- In the coordinates of one of its sites, `f_Z` is the scaled profile on `B`. -/
theorem selBump_comp_aff_eqOn (hV : 𝔆.Valid K.x K.y) (hprof : ∀ ℓ, tsupport (K.cat.prof ℓ) ⊆ siteC d)
    {Z : Finset (Rd d × K.cat.Label)} (hZ : IsSelection 𝔆 Z) {p : Rd d × K.cat.Label} (hp : p ∈ Z)
    {u : Rd d} (hu : u ∈ siteB d) :
    (selBump K 𝔆.s Z).comp (ContMetric.affineMap 𝔆.s p.1) u = (K.M • K.cat.prof p.2) u := by
  have hs := hV.1
  rw [← q9Bump_comp_aff (K.cat.prof p.2) K.M p.1 hs]
  simp only [ContinuousMap.comp_apply]
  apply selBump_eq_on_ball hV hprof hZ hp
  rw [ContMetric.affineMap_apply, mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos hs]
  have : ‖u‖ < 4 := by simpa [siteB] using hu
  nlinarith [norm_nonneg u]

/-- The Cameron–Martin bound of `f_Z` (`b:lem-bump`, placement and sums). -/
theorem isCMBounded_selBump {C : ℝ} (hC : ∀ ℓ, IsCMBounded (K.cat.prof ℓ) C) {s : ℝ} (hs : 0 < s)
    (Z : Finset (Rd d × K.cat.Label)) :
    IsCMBounded (selBump K s Z) (Z.card * (|K.M| * C)) := by
  have hcont : ∀ p ∈ Z, Continuous (fun x => q9Bump (K.cat.prof p.2) K.M p.1 s x) :=
    fun p _ => (q9Bump (K.cat.prof p.2) K.M p.1 s).continuous
  have hb : ∀ p ∈ Z, IsCMBounded (fun x => q9Bump (K.cat.prof p.2) K.M p.1 s x) (|K.M| * C) := by
    intro p _
    have h1 := (hC p.2).comp_affine (K.cat.prof p.2).continuous hs p.1
    exact h1.mul_const K.M
  have h := IsCMBounded.sum Z hcont hb
  have hfun : (fun x => ∑ p ∈ Z, q9Bump (K.cat.prof p.2) K.M p.1 s x) = ⇑(selBump K s Z) := by
    funext x
    rw [selBump_apply]
  rw [hfun, Finset.sum_const, nsmul_eq_mul] at h
  exact h

theorem selBump_erase_add {s : ℝ} {Z : Finset (Rd d × K.cat.Label)} {p : Rd d × K.cat.Label}
    (hp : p ∈ Z) : selBump K s Z = selBump K s (Z.erase p) + q9Bump (K.cat.prof p.2) K.M p.1 s := by
  simp only [selBump]
  rw [← Finset.sum_erase_add Z _ hp]

theorem selBump_singleton (s : ℝ) (p : Rd d × K.cat.Label) :
    selBump K s {p} = q9Bump (K.cat.prof p.2) K.M p.1 s := by
  simp [selBump]

theorem selBump_empty (s : ℝ) : selBump K s (∅ : Finset (Rd d × K.cat.Label)) = 0 := by
  simp [selBump]

end Selection

/-! ## Site units under modifications vanishing on the site sphere -/

/-- `S(H + f) = S(H)` when `f` vanishes on `∂B_s(z)` and the sphere averages of `H` at `(s, z)` converge. -/
theorem q9_scaleS_addFun_eq {ξ s : ℝ} (hs : 0 < s) {z : Rd d} {H : DistRd d} {a : ℝ}
    (ha : Tendsto (sphereAvgSeq H s z) atTop (𝓝 a)) {f : C(Rd d, ℝ)} (hf : ∀ x ∈ sphere z s, f x = 0) :
    scaleS d ξ 1 s z (addFun H f) = scaleS d ξ 1 s z H := by
  have ha' : Tendsto (sphereAvgSeq H (1 * s) z) atTop (𝓝 a) := by rwa [one_mul]
  have hzero : (∫ u, f (z + (1 * s) • u) ∂(unitSphereProb d)) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    apply hf
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, one_mul,
      Real.norm_eq_abs, abs_of_pos hs]
  unfold scaleS
  rw [sphereAvg_addFun_of_tendsto ha' f, hzero, add_zero]

end HigherDimLQGContinuity
