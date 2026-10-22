import HigherDimLQGMetric.Events.AnnulusDiameter
import HigherDimLQGMetric.Shell.Across

/-!
# Scale changes for regular events

The normalized length metric transports global crossing distances, internal
set distances, and internal diameters to the unit annulus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem setDistIn_smul {C : ℝ} (hC : 0 < C) (D : ContMetric d)
    (V A B : Set (Rd d)) :
    setDistIn (D.smul C hC) V A B = ENNReal.ofReal C * setDistIn D V A B := by
  unfold setDistIn
  simp_rw [ContMetric.internal_smul hC]
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top]

theorem setDistIn_affine {r : ℝ} (hr : r ≠ 0) (z : Rd d)
    (D : ContMetric d) (V A B : Set (Rd d)) :
    setDistIn (D.affine r hr z) V A B =
      setDistIn D ((fun u => r • u + z) '' V)
        ((fun u => r • u + z) '' A) ((fun u => r • u + z) '' B) := by
  unfold setDistIn
  simp_rw [ContMetric.internal_affine hr z D]
  simp only [iInf_image]

theorem sharpScaledCoeff (ξ Q : ℝ) (g : DistRd d) (r : ℝ) (z : Rd d) :
    (r ^ (ξ * Q))⁻¹ * Real.exp (-ξ * sphereAvg g r z) =
      (sNorm ξ Q g r z)⁻¹ := by
  have he : Real.exp (-ξ * sphereAvg g r z) =
      (Real.exp (ξ * sphereAvg g r z))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [sNorm, mul_inv_rev, he]
  ring

theorem sNorm_pos (ξ Q : ℝ) (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    0 < sNorm ξ Q g r z := by
  unfold sNorm
  positivity

private theorem ofReal_mul_inv (s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal s * ENNReal.ofReal s⁻¹ = 1 := by
  rw [← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one]

/-- Convert an upper bound for a normalized nonnegative quantity back to
the original scale. -/
theorem unscale_le {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞}
    (h : ENNReal.ofReal s⁻¹ * x ≤ ENNReal.ofReal t) :
    x ≤ ENNReal.ofReal (t * s) := by
  calc
    x = ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * x) := by
      rw [← mul_assoc, ofReal_mul_inv s hs, one_mul]
    _ ≤ ENNReal.ofReal s * ENNReal.ofReal t := by gcongr
    _ = ENNReal.ofReal (t * s) := by
      rw [← ENNReal.ofReal_mul hs.le]
      congr 1
      ring

/-- The strict upper-bound form of `unscale_le`. -/
theorem unscale_lt {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞}
    (h : ENNReal.ofReal s⁻¹ * x < ENNReal.ofReal t) :
    x < ENNReal.ofReal (t * s) := by
  have hpos : ENNReal.ofReal s ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hs).ne'
  have hfin : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    x = ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * x) := by
      rw [← mul_assoc, ofReal_mul_inv s hs, one_mul]
    _ < ENNReal.ofReal s * ENNReal.ofReal t := by
      simpa only [mul_comm] using ENNReal.mul_lt_mul_left hpos hfin h
    _ = ENNReal.ofReal (t * s) := by
      rw [← ENNReal.ofReal_mul hs.le]
      congr 1
      ring

/-- Lower bounds transport to the original scale as well. -/
theorem unscale_lower {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞}
    (h : ENNReal.ofReal t ≤ ENNReal.ofReal s⁻¹ * x) :
    ENNReal.ofReal (t * s) ≤ x := by
  calc
    ENNReal.ofReal (t * s) = ENNReal.ofReal s * ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul hs.le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * x) := by gcongr
    _ = x := by rw [← mul_assoc, ofReal_mul_inv s hs, one_mul]

theorem unscale_lower_strict {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞}
    (h : ENNReal.ofReal t < ENNReal.ofReal s⁻¹ * x) :
    ENNReal.ofReal (t * s) < x := by
  have hpos : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hfin : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal (t * s) = ENNReal.ofReal s * ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_mul hs.le]
      congr 1
      ring
    _ < ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * x) := by
      simpa only [mul_comm] using ENNReal.mul_lt_mul_left hpos hfin h
    _ = x := by rw [← mul_assoc, ofReal_mul_inv s hs, one_mul]

theorem sharpScaledMetric_internal (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (V : Set (Rd d)) (u v : Rd d) :
    (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) g hr z
      (Real.rpow_pos_of_pos hr _)).internal V u v =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
        (D g).internal ((fun w => r • w + z) '' V)
          (r • u + z) (r • v + z) := by
  unfold weakScaledMetric
  rw [ContMetric.internal_smul, ContMetric.internal_affine hr.ne' z (D g)]
  rw [sharpScaledCoeff]

theorem sharpScaledMetric_across (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (a b : ℝ) :
    acrossDist (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) g hr z
      (Real.rpow_pos_of_pos hr _)) 0 a b =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
        acrossDist (D g) z (r * a) (r * b) := by
  unfold weakScaledMetric
  rw [acrossDist_smul, acrossDist_affine hr, sharpScaledCoeff]

theorem sharpScaledMetric_setDistIn (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (V A B : Set (Rd d)) :
    setDistIn (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) g hr z
      (Real.rpow_pos_of_pos hr _)) V A B =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
        setDistIn (D g) ((fun w => r • w + z) '' V)
          ((fun w => r • w + z) '' A) ((fun w => r • w + z) '' B) := by
  unfold weakScaledMetric
  rw [setDistIn_smul, setDistIn_affine hr.ne' z, sharpScaledCoeff]

theorem sharpScaledMetric_diamIn (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (V A : Set (Rd d)) :
    diamIn (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) g hr z
      (Real.rpow_pos_of_pos hr _)) V A =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
        diamIn (D g) ((fun w => r • w + z) '' V)
          ((fun w => r • w + z) '' A) := by
  unfold weakScaledMetric
  rw [diamIn_smul, diamIn_affine hr.ne' z, sharpScaledCoeff]

/-- Crossing the two core spheres after normalization. -/
theorem sharpScaled_coreAcross (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    acrossDist (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) g hr z
      (Real.rpow_pos_of_pos hr _)) 0 1 2 =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
        setDistG (D g) (sphere z r) (sphere z (2 * r)) := by
  rw [sharpScaledMetric_across]
  rw [show r * 1 = r by ring, show r * 2 = 2 * r by ring]
  rfl

/-- The core internal diameter after normalization. -/
theorem sharpScaled_coreDiameter (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    diamIn (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) g hr z
      (Real.rpow_pos_of_pos hr _))
      (ann 0 (3 / 4) 3) (annCl 0 1 2) =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
        diamIn (D g) (ann z (3 * r / 4) (3 * r)) (annCl z r (2 * r)) := by
  rw [sharpScaledMetric_diamIn, image_ann_affine hr z,
    image_annCl_affine hr z]
  congr 2 <;> ring

/-- Internal distance between the core and one of the collar spheres. -/
theorem sharpScaled_collarDistance (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (z : Rd d) (ρ : ℝ) :
    setDistIn (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) g hr z
      (Real.rpow_pos_of_pos hr _))
      (ann 0 (1 / 2) 5) (annCl 0 1 2) (sphere 0 ρ) =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) *
        setDistIn (D g) (ann z (r / 2) (5 * r))
          (annCl z r (2 * r)) (sphere z (r * ρ)) := by
  rw [sharpScaledMetric_setDistIn, image_ann_affine hr z,
    image_annCl_affine hr z, image_sphere_affine hr z]
  congr 2 <;> ring

/-- The unit-scale metric conditions equivalent to regularity at `(z,r)`.
The two metrics have already been normalized by the same sharp factor. -/
def UnitReg (M N : ContMetric d) (U a A₀ ℓ β₀ : ℝ) : Prop :=
  ENNReal.ofReal a ≤ acrossDist M 0 1 2 ∧
  diamIn M (ann 0 (3 / 4) 3) (annCl 0 1 2) ≤ ENNReal.ofReal A₀ ∧
  (∀ ρ ∈ ({3 / 4, 3} : Set ℝ),
    ENNReal.ofReal (4 * max 1 U * ℓ) <
      setDistIn M (ann 0 (1 / 2) 5) (annCl 0 1 2) (sphere 0 ρ) ∧
    ENNReal.ofReal (4 * max 1 U * ℓ) <
      setDistIn N (ann 0 (1 / 2) 5) (annCl 0 1 2) (sphere 0 ρ)) ∧
  (∀ u ∈ annCl (0 : Rd d) 1 2, ∀ v ∈ annCl 0 1 2, ‖u - v‖ ≤ β₀ →
    M.internal (ann 0 (3 / 4) 3) u v < ENNReal.ofReal (ℓ / 4))

/-- Unit-scale regularity implies the source event at arbitrary center and
radius. -/
theorem regEvent_of_unitReg (ξ Q U a A₀ ℓ β₀ : ℝ)
    (A B : DistRd d → ContMetric d) (g : DistRd d)
    {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hunit : UnitReg
      (weakScaledMetric ξ A (fun t => t ^ (ξ * Q)) g hr z
        (Real.rpow_pos_of_pos hr _))
      (weakScaledMetric ξ B (fun t => t ^ (ξ * Q)) g hr z
        (Real.rpow_pos_of_pos hr _)) U a A₀ ℓ β₀) :
    g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z := by
  let s : ℝ := sNorm ξ Q g r z
  have hs : 0 < s := sNorm_pos ξ Q g hr z
  rcases hunit with ⟨hAcross, hDiam, hCollar, hMod⟩
  unfold RegEvent
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sharpScaled_coreAcross] at hAcross
    exact unscale_lower hs hAcross
  · rw [sharpScaled_coreDiameter] at hDiam
    exact unscale_le hs hDiam
  · intro ρ hρ
    have hcase : ρ = 3 * r / 4 ∨ ρ = 3 * r := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hρ
    rcases hcase with hρ | hρ
    · rw [hρ]
      obtain ⟨hA, hB⟩ := hCollar (3 / 4) (by simp)
      rw [sharpScaled_collarDistance] at hA hB
      have hA' := unscale_lower_strict hs hA
      have hB' := unscale_lower_strict hs hB
      constructor
      · simpa only [s, show r * (3 / 4) = 3 * r / 4 by ring] using hA'
      · simpa only [s, show r * (3 / 4) = 3 * r / 4 by ring] using hB'
    · rw [hρ]
      obtain ⟨hA, hB⟩ := hCollar 3 (by simp)
      rw [sharpScaled_collarDistance] at hA hB
      have hA' := unscale_lower_strict hs hA
      have hB' := unscale_lower_strict hs hB
      constructor
      · simpa only [s, show r * 3 = 3 * r by ring] using hA'
      · simpa only [s, show r * 3 = 3 * r by ring] using hB'
  · intro u hu v hv huv
    have hI : (fun x : Rd d => r • x + z) '' annCl 0 1 2 =
        annCl z r (2 * r) := by
      convert image_annCl_affine hr z 1 2 using 1; ring
    obtain ⟨u₀, hu₀, rfl⟩ := hI.symm ▸ hu
    obtain ⟨v₀, hv₀, rfl⟩ := hI.symm ▸ hv
    have hnorm : ‖u₀ - v₀‖ ≤ β₀ := by
      have he : ‖(r • u₀ + z) - (r • v₀ + z)‖ = r * ‖u₀ - v₀‖ := by
        rw [show (r • u₀ + z) - (r • v₀ + z) = r • (u₀ - v₀) by module,
          norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      rw [he] at huv
      exact le_of_mul_le_mul_left (by nlinarith [huv] : r * ‖u₀ - v₀‖ ≤ r * β₀) hr
    have hm := hMod u₀ hu₀ v₀ hv₀ hnorm
    rw [sharpScaledMetric_internal, image_ann_affine hr z] at hm
    convert unscale_lt hs hm using 1; ring

end HigherDimLQGMetric
