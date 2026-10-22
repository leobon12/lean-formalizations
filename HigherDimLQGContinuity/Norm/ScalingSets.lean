import HigherDimLQGContinuity.Norm.Scaling

/-!
# Exact scaling of set distances and internal diameters (packet P2; companion of `a:lem-scaling`)

Consumers of (2.6) (Part A `a:ssec-l21-proof` Steps 2–3, `a:lem-refs-212`; Part D `d:lem-scaling`) use it for set
distances and internal diameters of images under `Φ(w) = r w + z`:

* `p2_image_affine` and its instances `p2_image_affine_univ`, `…_sphere`, `…_ball`, `…_closedBall`, `…_ann`,
  `…_annCl` (`Φ(B_a(c)) = B_{ra}(rc + z)`, etc., `r > 0`);
* `p2_setDistIn_image_of_internal`, `p2_diamIn_image_of_internal`: deterministic transfer of an internal scaling identity;
* `rho_scaling_sets`: almost surely under `pinLaw d s₀`, simultaneously for all sets,
  `setDistIn ρ_g (ΦV) (ΦA) (ΦB) = S · setDistIn ρ_{g'} V A B` and `diamIn ρ_g (ΦV) (ΦA) = S · diamIn ρ_{g'} V A`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Images under `w ↦ r w + z` -/

theorem p2_image_affine {r : ℝ} (hr : r ≠ 0) (z : Rd d) (S : Set (Rd d)) :
    (fun w => r • w + z) '' S = (fun w => r⁻¹ • (w - z)) ⁻¹' S := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [smul_smul, hr] using hu
  · intro hw
    exact ⟨r⁻¹ • (w - z), hw, by simp [smul_smul, hr]⟩

theorem p2_norm_affine_inv {r : ℝ} (hr : 0 < r) (z c w : Rd d) :
    ‖r⁻¹ • (w - z) - c‖ = r⁻¹ * ‖w - (r • c + z)‖ := by
  have e : r⁻¹ • (w - z) - c = r⁻¹ • (w - (r • c + z)) := by
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]

theorem p2_image_affine_univ {r : ℝ} (hr : r ≠ 0) (z : Rd d) :
    (fun w => r • w + z) '' (univ : Set (Rd d)) = univ := by
  rw [p2_image_affine hr, preimage_univ]

theorem p2_image_affine_sphere {r : ℝ} (hr : 0 < r) (z c : Rd d) (a : ℝ) :
    (fun w => r • w + z) '' sphere c a = sphere (r • c + z) (r * a) := by
  rw [p2_image_affine hr.ne']
  ext w
  simp only [mem_preimage, mem_sphere, dist_eq_norm, p2_norm_affine_inv hr]
  rw [inv_mul_eq_iff_eq_mul₀ hr.ne']

theorem p2_image_affine_ball {r : ℝ} (hr : 0 < r) (z c : Rd d) (a : ℝ) :
    (fun w => r • w + z) '' ball c a = ball (r • c + z) (r * a) := by
  rw [p2_image_affine hr.ne']
  ext w
  simp only [mem_preimage, mem_ball, dist_eq_norm, p2_norm_affine_inv hr]
  rw [inv_mul_lt_iff₀ hr]

theorem p2_image_affine_closedBall {r : ℝ} (hr : 0 < r) (z c : Rd d) (a : ℝ) :
    (fun w => r • w + z) '' closedBall c a = closedBall (r • c + z) (r * a) := by
  rw [p2_image_affine hr.ne']
  ext w
  simp only [mem_preimage, mem_closedBall, dist_eq_norm, p2_norm_affine_inv hr]
  rw [inv_mul_le_iff₀ hr]

theorem p2_image_affine_ann {r : ℝ} (hr : 0 < r) (z c : Rd d) (a b : ℝ) :
    (fun w => r • w + z) '' ann c a b = ann (r • c + z) (r * a) (r * b) := by
  rw [p2_image_affine hr.ne']
  ext w
  simp only [mem_preimage, ann, mem_ofPred_eq, p2_norm_affine_inv hr]
  rw [lt_inv_mul_iff₀ hr, inv_mul_lt_iff₀ hr]

theorem p2_image_affine_annCl {r : ℝ} (hr : 0 < r) (z c : Rd d) (a b : ℝ) :
    (fun w => r • w + z) '' annCl c a b = annCl (r • c + z) (r * a) (r * b) := by
  rw [p2_image_affine hr.ne']
  ext w
  simp only [mem_preimage, annCl, mem_ofPred_eq, p2_norm_affine_inv hr]
  rw [le_inv_mul_iff₀ hr, inv_mul_le_iff₀ hr]

/-! ## Set distances and internal diameters -/

section Transfer

variable {G G' : ContMetric d} {Φ : Rd d → Rd d} {c : ℝ≥0∞}

theorem p2_setDistIn_image_of_internal (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (h : ∀ (U : Set (Rd d)) (x y : Rd d), G.internal (Φ '' U) (Φ x) (Φ y) = c * G'.internal U x y)
    (V A B : Set (Rd d)) :
    setDistIn G (Φ '' V) (Φ '' A) (Φ '' B) = c * setDistIn G' V A B := by
  unfold setDistIn
  simp only [iInf_image, h]
  simp only [ENNReal.mul_iInf_of_ne hc0 hctop]

theorem p2_diamIn_image_of_internal
    (h : ∀ (U : Set (Rd d)) (x y : Rd d), G.internal (Φ '' U) (Φ x) (Φ y) = c * G'.internal U x y)
    (V A : Set (Rd d)) :
    diamIn G (Φ '' V) (Φ '' A) = c * diamIn G' V A := by
  unfold diamIn
  simp only [iSup_image, h]
  simp only [ENNReal.mul_iSup]

end Transfer

/-- (2.6) for set distances and internal diameters: almost surely under `pinLaw d s₀`, simultaneously for all sets,
with `Φ(w) = r w + z`, `g' = recentre s r z g` and `S = scaleS d ξ s r z g`. -/
theorem rho_scaling_sets (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) {s s₀ r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (z : Rd d) :
    ∀ᵐ g ∂(pinLaw d s₀),
      (∀ V A B : Set (Rd d),
        setDistIn (rho D g) ((fun w => r • w + z) '' V) ((fun w => r • w + z) '' A) ((fun w => r • w + z) '' B) =
          ENNReal.ofReal (scaleS d ξ s r z g) * setDistIn (rho D (recentre s r z g)) V A B) ∧
      ∀ V A : Set (Rd d),
        diamIn (rho D g) ((fun w => r • w + z) '' V) ((fun w => r • w + z) '' A) =
          ENNReal.ofReal (scaleS d ξ s r z g) * diamIn (rho D (recentre s r z g)) V A := by
  filter_upwards [rho_scaling_of hd hξ hD (s := s) hs₀ hr z] with g hg
  have hc0 : ENNReal.ofReal (scaleS d ξ s r z g) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (scaleS_pos d ξ s hr z g)).ne'
  exact ⟨fun V A B => p2_setDistIn_image_of_internal hc0 ENNReal.ofReal_ne_top hg.2 V A B,
    fun V A => p2_diamIn_image_of_internal hg.2 V A⟩

end HigherDimLQGContinuity
