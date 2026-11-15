/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdData
import InteractingSLE.Spec.ZhanGT4.A1EightSeedRecord

/-!
# The actual seeded entrance and empty-height normalizations

Packet PROVE-ZHAN-GT4-A22. Identify the reflected entrance map with the
original frozen chart, then use the landed coincident-seed axis identity.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

/-- At own time zero the first reflected map has the value and derivative
of the actual frozen second chart at the original first source. -/
theorem OwnData.entrance_factors {W₁ W₂ a U : ℝ → ℝ} {S T t : ℝ}
    (h : OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S a U)
    (hW₂ : Continuous W₂) {q : ℝ → ℂ} (hq : IsForwardSol W₂ (0 : ℂ) T q)
    (ht : t ∈ Icc (0 : ℝ) T) :
    frzA W₁ U a (frzChart W₂ t) 0 0 = (frzChart W₂ t 0).re ∧
      frzA W₁ U a (frzChart W₂ t) 1 0 = (deriv (fwdMap W₂ t) 0).re := by
  obtain ⟨δ, hδ, hl, hv⟩ := exists_aliveDisc_self hq (ht.1.trans ht.2)
  have hd : DifferentiableOn ℂ (frzChart W₂ t) (ball (0 : ℂ) (aliveRad T δ)) :=
    (differentiableOn_fwdMap_aliveDisc hW₂ hq hδ hl ht).add_const (W₂ t : ℂ)
  have hR : IsMapOut ((fun z => fwdMap W₁ 0 z + W₁ 0) '' fwdHull W₂ t) (frzChart W₂ t) := by
    change IsMapOut (frzChart W₁ 0 '' fwdHull W₂ t) (frzChart W₂ t)
    rw [frzChart_zero_eq_id, Set.image_id]
    exact h.mapOut
  have he (k : ℕ) := h.iterate_deriv_ownExt_eq ⟨le_rfl, h.pos.le⟩ hR
    (aliveRad_pos hδ) (by simpa only [h.zero, Complex.ofReal_zero] using hd) k
  constructor
  · simpa only [frzA, Function.iterate_zero, id_eq, h.zero, Complex.ofReal_zero] using congrArg Complex.re (he 0)
  · have hh := congrArg Complex.re (he 1)
    change (deriv (ownExt W₁ U a (frzChart W₂ t) 0) (W₁ 0)).re =
      (deriv (fun z => fwdMap W₂ t z + (W₂ t : ℂ)) (W₁ 0)).re at hh
    rw [deriv_add_const] at hh
    simpa only [frzA, Function.iterate_one, h.zero, Complex.ofReal_zero] using hh

/-- The actual first-axis normalization equals the opposite original
one-source reference factor. Coincident entrance seeds are allowed. -/
theorem seedSView_normEll_zero {n : ℕ} {κ S T t : ℝ} (r : Fin n → ℝ)
    {W₁ W₂ : ℝ → ℝ} {as Ws : ℝ → ℝ → ℝ} (V : Fin n → ℝ → ℝ)
    (hκ : κ ≠ 0) (h : OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S (as t) (Ws t))
    (hW₂ : Continuous W₂) {q : ℝ → ℂ} (hq : IsForwardSol W₂ (0 : ℂ) T q)
    (ht : t ∈ Icc (0 : ℝ) T)
    {v : ℝ → ℂ} (hv : IsForwardSol (Ws t) ((W₂ t : ℝ) : ℂ) (as t S) v)
    (hV : ∀ m, V m 0 = 0) :
    (seedSView κ r W₁ W₂ as Ws V t).normEll 0 =
      dualGamma (16 / κ) (-1 / 2 + ∑ m, -(κ / 4) * r m) *
        Real.log (deriv (fwdMap W₂ t) 0).re +
      (-1 / 2 + ∑ m, -(κ / 4) * r m) *
        Real.log (((frzChart W₂ t 0).re - W₂ t) / (-W₂ 0)) := by
  have hd := (seedSView κ r W₁ W₂ as Ws V t).normEll_zero_eq_fused_axis h hκ hv
    (fun m => (hV m).trans h.zero.symm) (source_deriv_zero W₁ (W₂ 0))
  have he := h.entrance_factors hW₂ hq ht
  have h20 : (seedSView κ r W₁ W₂ as Ws V t).A20 0 = W₂ t := by
    change frzImg (Ws t) (as t) (W₂ t) 0 = _
    rw [frzImg, h.a0]
    exact source_value_zero (Ws t) (W₂ t)
  have hV₀ : (seedSView κ r W₁ W₂ as Ws V t).V₀ 0 = W₂ 0 :=
    source_value_zero W₁ (W₂ 0)
  rw [h20, hV₀] at hd
  simpa only [seedSView, SeedData.fromSource, SeedData.A, he.1, he.2, h.zero,
    zero_sub] using hd

/-- A source record against the actual empty frozen hull has zero log
density at every own time in the rectangle. -/
theorem seedSView_normEll_zero_height {n : ℕ} {κ S : ℝ} (r : Fin n → ℝ)
    {W₁ W₂ : ℝ → ℝ} {as Ws : ℝ → ℝ → ℝ} (V : Fin n → ℝ → ℝ)
    (hW₂ : Continuous W₂)
    (h : OwnData W₁ (fwdHull W₂ 0) (frzChart W₂ 0) S (as 0) (Ws 0))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) S) :
    (seedSView κ r W₁ W₂ as Ws V 0).normEll s = 0 := by
  have hK := QuantumZipper.RS.fwdHull_zero_eq_empty hW₂
  unfold seedSView
  rw [frzChart_zero_eq_id]
  rw [hK, frzChart_zero_eq_id] at h
  exact A1EightSeed.normEll_fromSource_empty_eq_zero h κ r (W₂ 0) V hs

end InteractingSLE.ZhanGT4
