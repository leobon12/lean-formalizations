/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstBounds

/-!
# D9 for clear accesses in a fixed image enclosure

Packet PROVE-ZHAN-GT4-A22. Unlike ordinary physical force points, the
accesses here may be integrated seed coordinates in a fixed first chart.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

/-- A finite family of distinct clear accesses supplies every force-point
part of D9, uniformly over image chains inside the fixed enclosure. The
own-map clearance and derivative lower bound are separate geometric data. -/
theorem exists_D9Const_of_image_enclosure {n : ℕ} {E : Set ℂ}
    (hE : IsHPHull E) (z : Option (Fin n) → ℝ) (hz : Function.Injective z)
    {ρ : ℝ} (hρ : 0 < ρ) (hclear : ∀ i, Disjoint (ball (z i : ℂ) ρ) E)
    (Tm : ℝ) :
    ∃ γ Γ lam : ℝ, 0 < γ ∧ ∀ (d : FrzData n) (A : Set ℂ) (T r a₀ : ℝ),
      OwnData d.W A d.φ T d.a d.W' → 0 < r → 0 < a₀ →
      d.ζ₀ = z none → (∀ m, d.ζ m = z (some m)) →
      (∀ t ∈ Icc (0 : ℝ) T,
        Disjoint (ball (d.W t : ℂ) r) ((fun w => fwdMap d.W t w + d.W t) '' A)) →
      (∀ t ∈ Icc (0 : ℝ) T, a₀ ≤ d.A 1 t) →
      (∀ t ∈ Icc (0 : ℝ) T, d.a t ≤ Tm) →
      fwdHull d.W' (d.a T) ⊆ E → d.D9Const A T r a₀ γ Γ lam := by
  obtain ⟨c, C, L, hc, hC, hL, hb⟩ := exists_access_bounds_of_enclosure hE z hρ hclear
  obtain ⟨ν, hν, hνle⟩ := exists_pos_le_of_fintype
    (fun ij : Option (Fin n) × Option (Fin n) =>
      if ij.1 = ij.2 then 1 else |z ij.1 - z ij.2|) fun ij => by
    by_cases he : ij.1 = ij.2
    · simp [he]
    · simp only [he, ↓reduceIte]
      exact abs_pos.2 (sub_ne_zero.2 fun hh => he (hz hh))
  let γ := min c (ν * Real.exp (-(2 / c ^ 2 * Tm)))
  have hγ : 0 < γ := lt_min hc (mul_pos hν (Real.exp_pos _))
  refine ⟨γ, 2 * C, L, hγ, ?_⟩
  intro d A T r a₀ h hr ha h0 hm hclr hA1 hclock hK
  have haT : 0 < d.a T := by
    have hh := h.mono ⟨le_rfl, h.pos.le⟩ ⟨h.pos.le, le_rfl⟩ h.pos
    rwa [h.a0] at hh
  have hsrc : ((d.W' 0 : ℝ) : ℂ) ∈ closure E :=
    closure_mono hK (start_mem_closure_fwdHull h.contW' haT)
  have hb' := hb d.W' (d.a T) h.contW' haT.le hsrc hK
  choose v hv using fun i => (hb' i).1
  have hgap : ∀ i, ∀ t ∈ Icc (0 : ℝ) T,
      c ≤ |(fwdMap d.W' (d.a t) (z i)).re| ∧
      |(fwdMap d.W' (d.a t) (z i)).re| ≤ C ∧
      InScale L (deriv (fwdMap d.W' (d.a t)) (z i)).re :=
    fun i t ht => (hb' i).2 _ (h.mapsTo_clock ht)
  have hpair : ∀ i j, i ≠ j → ∀ t ∈ Icc (0 : ℝ) T,
      γ ≤ |frzImg d.W' d.a (z i) t - frzImg d.W' d.a (z j) t| ∧
      |frzImg d.W' d.a (z i) t - frzImg d.W' d.a (z j) t| ≤ 2 * C := by
    intro i j hij t ht
    have hνij : ν ≤ |z i - z j| := by
      simpa only [hij, ↓reduceIte] using hνle (i, j)
    have hl := h.frzImg_sub_bounds_of_gap (hv j) (hv i) hc
      (fun u hu => (hgap j u hu).1) (fun u hu => (hgap i u hu).1) (hclock t ht) ht
    have hu : |frzImg d.W' d.a (z i) t - frzImg d.W' d.a (z j) t| ≤ 2 * C := by
      have he : frzImg d.W' d.a (z i) t - frzImg d.W' d.a (z j) t =
          (fwdMap d.W' (d.a t) (z i)).re - (fwdMap d.W' (d.a t) (z j)).re := by
        unfold frzImg; ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith [(hgap i t ht).2.1, (hgap j t ht).2.1])
    exact ⟨(min_le_right _ _).trans ((mul_le_mul_of_nonneg_right hνij
      (Real.exp_pos _).le).trans hl), hu⟩
  have he0 : ∀ t ∈ Icc (0 : ℝ) T,
      d.A20 t - d.A 0 t = (fwdMap d.W' (d.a t) (z none)).re := by
    intro t ht
    rw [FrzData.A20, FrzData.A, h.frzA_zero ht, frzImg, h0, add_sub_cancel_right]
  have hem : ∀ t ∈ Icc (0 : ℝ) T, ∀ m,
      d.B0 t m - d.A 0 t = (fwdMap d.W' (d.a t) (z (some m))).re := by
    intro t ht m
    rw [FrzData.B0, FrzData.A, h.frzA_zero ht, frzImg, hm m, add_sub_cancel_right]
  refine ⟨hr, ha, hγ, hclr, hA1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [he0 t ht]
    exact ⟨(min_le_left _ _).trans (hgap none t ht).1,
      (hgap none t ht).2.1.trans (by linarith)⟩
  · intro t ht m
    rw [hem t ht m]
    exact ⟨(min_le_left _ _).trans (hgap (some m) t ht).1,
      (hgap (some m) t ht).2.1.trans (by linarith)⟩
  · intro t ht m
    simpa only [FrzData.A20, FrzData.B0, h0, hm m] using
      hpair none (some m) (by simp) t ht
  · intro t ht m k hmk
    simpa only [FrzData.B0, hm m, hm k] using
      hpair (some m) (some k) (by simpa using hmk) t ht
  · intro t ht
    simpa only [FrzData.A21, frzImgD, h0] using (hgap none t ht).2.2
  · intro t ht m
    simpa only [FrzData.B1, frzImgD, hm m] using (hgap (some m) t ht).2.2

end InteractingSLE.ZhanGT4
