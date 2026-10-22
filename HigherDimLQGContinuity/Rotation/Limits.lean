import HigherDimLQGContinuity.Rotation.Convolution
import HigherDimLQGMetric.Frozen.Theorem12

/-!
# Local-uniform limits under isometries

This is the `Rd d` version of `GaussianLQG.ae_eq_comp_of_tendstoInProbLU`: if two sequences of
random functions agree after an isometry, their limits in probability agree almost surely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {l : Filter ι} {X X' : ι → Ω → Rd d × Rd d → ℝ}
  {Y Y' : Ω → Rd d × Rd d → ℝ} {T : Rd d × Rd d → Rd d × Rd d}

abbrev rotSqBall (d : ℕ) (R : ℝ) : Set (Rd d × Rd d) :=
  closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R

omit [MeasurableSpace Ω] in
private lemma rot_mem_union_of_two_mul_le
    {R δ : ℝ} {i : ι} {ω : Ω}
    (hT : ∀ p ∈ rotSqBall d R, T p ∈ rotSqBall d R)
    (hω : ∀ p, X' i ω p = X i ω (T p)) {p : Rd d × Rd d}
    (hp : p ∈ rotSqBall d R)
    (hd : 2 * δ ≤ dist (Y' ω p) (Y ω (T p))) :
    ENNReal.ofReal δ ≤ ⨆ q ∈ rotSqBall d R, edist (X' i ω q) (Y' ω q) ∨
      ENNReal.ofReal δ ≤ ⨆ q ∈ rotSqBall d R, edist (X i ω q) (Y ω q) := by
  have htri : dist (Y' ω p) (Y ω (T p)) ≤
      dist (X' i ω p) (Y' ω p) + dist (X i ω (T p)) (Y ω (T p)) := by
    calc dist (Y' ω p) (Y ω (T p)) ≤
          dist (Y' ω p) (X' i ω p) + dist (X' i ω p) (Y ω (T p)) :=
          dist_triangle _ _ _
      _ = dist (X' i ω p) (Y' ω p) + dist (X i ω (T p)) (Y ω (T p)) := by
          rw [dist_comm (Y' ω p), hω p]
  rcases le_or_gt δ (dist (X' i ω p) (Y' ω p)) with h1 | h1
  · left
    refine le_trans ?_ (le_iSup₂ (f := fun q _ => edist (X' i ω q) (Y' ω q)) p hp)
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal h1
  · right
    refine le_trans ?_ (le_iSup₂ (f := fun q _ => edist (X i ω q) (Y ω q)) (T p) (hT p hp))
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (by linarith)

private lemma rot_measure_discrepancy_eq_zero [l.NeBot]
    (hT : ∀ R, ∀ p ∈ rotSqBall d R, T p ∈ rotSqBall d R)
    (hX : TendstoInProbLU P X l Y) (hX' : TendstoInProbLU P X' l Y')
    (hXX' : ∀ᶠ i in l, ∀ᵐ ω ∂P, ∀ p, X' i ω p = X i ω (T p))
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    P {ω | ∃ p ∈ rotSqBall d R, 2 * δ ≤ dist (Y' ω p) (Y ω (T p))} = 0 := by
  set A := {ω | ∃ p ∈ rotSqBall d R, 2 * δ ≤ dist (Y' ω p) (Y ω (T p))}
  set B' : ι → Set Ω := fun i =>
    {ω | ENNReal.ofReal δ ≤ ⨆ q ∈ rotSqBall d R, edist (X' i ω q) (Y' ω q)}
  set B : ι → Set Ω := fun i =>
    {ω | ENNReal.ofReal δ ≤ ⨆ q ∈ rotSqBall d R, edist (X i ω q) (Y ω q)}
  have hle : ∀ᶠ i in l, P A ≤ P (B' i) + P (B i) := by
    filter_upwards [hXX'] with i hi
    set N := {ω | ¬ ∀ p, X' i ω p = X i ω (T p)}
    have hN : P N = 0 := ae_iff.1 hi
    have hsub : A ⊆ (B' i ∪ B i) ∪ N := by
      rintro ω ⟨p, hp, hd⟩
      by_cases hω : ∀ p, X' i ω p = X i ω (T p)
      · left
        exact rot_mem_union_of_two_mul_le (hT R) hω hp hd
      · right
        exact hω
    calc P A ≤ P ((B' i ∪ B i) ∪ N) := measure_mono hsub
      _ ≤ P (B' i ∪ B i) + P N := measure_union_le _ _
      _ = P (B' i ∪ B i) := by rw [hN, add_zero]
      _ ≤ P (B' i) + P (B i) := measure_union_le _ _
  have hlim : Tendsto (fun i => P (B' i) + P (B i)) l (𝓝 0) := by
    have h := (hX' R hR δ hδ).add (hX R hR δ hδ)
    rwa [add_zero] at h
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto hlim hle)

/-- Uniqueness of limits in probability in the local-uniform topology, after a coordinate map
that preserves every square closed ball. -/
theorem rot_ae_eq_comp_of_tendstoInProbLU [l.NeBot]
    (hT : ∀ R, ∀ p ∈ rotSqBall d R, T p ∈ rotSqBall d R)
    (hX : TendstoInProbLU P X l Y) (hX' : TendstoInProbLU P X' l Y')
    (hXX' : ∀ᶠ i in l, ∀ᵐ ω ∂P, ∀ p, X' i ω p = X i ω (T p)) :
    ∀ᵐ ω ∂P, ∀ p, Y' ω p = Y ω (T p) := by
  set A : ℕ → Set Ω := fun n => {ω | ∃ p ∈ rotSqBall d ((n : ℝ) + 1),
    2 * (2 * ((n : ℝ) + 1))⁻¹ ≤ dist (Y' ω p) (Y ω (T p))}
  have hA : ∀ n, P (A n) = 0 := fun n =>
    rot_measure_discrepancy_eq_zero hT hX hX' hXX' (by positivity) (by positivity)
  refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hA))
  simp only [mem_ofPred_eq, not_forall] at hω
  obtain ⟨p, hp⟩ := hω
  have hd : 0 < dist (Y' ω p) (Y ω (T p)) := dist_pos.2 hp
  obtain ⟨n, hn⟩ := exists_nat_ge
    (max (max ‖p.1‖ ‖p.2‖) (dist (Y' ω p) (Y ω (T p)))⁻¹)
  have h1 : max ‖p.1‖ ‖p.2‖ ≤ n := (le_max_left _ _).trans hn
  have h2 : (dist (Y' ω p) (Y ω (T p)))⁻¹ ≤ n := (le_max_right _ _).trans hn
  refine mem_iUnion.2 ⟨n, p, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff]
    linarith [le_max_left ‖p.1‖ ‖p.2‖]
  · rw [mem_closedBall_zero_iff]
    linarith [le_max_right ‖p.1‖ ‖p.2‖]
  · have e : 2 * (2 * ((n : ℝ) + 1))⁻¹ = ((n : ℝ) + 1)⁻¹ := by
      field_simp
    rw [e]
    have h3 : (dist (Y' ω p) (Y ω (T p)))⁻¹ ≤ (n : ℝ) + 1 := by linarith
    have h := inv_anti₀ (inv_pos.2 hd) h3
    rwa [inv_inv] at h

end HigherDimLQGContinuity
