/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedReciprocity
import InteractingSLE.Spec.ZhanGT4.DualSeedAccessAxis
import InteractingSLE.Spec.ZhanGT4.DualJointMeas

/-!
# The actual two seeded views and their separated source

Packet PROVE-ZHAN-GT4-A22. The first view uses integrated first-curve seeds.
The opposite view uses those same real accesses in the translated first chart.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)

/-- The seeded first view at a frozen second height. -/
def seedSView {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ)
    (as Ws : ℝ → ℝ → ℝ) (V : Fin n → ℝ → ℝ) (t : ℝ) : SeedData n :=
  SeedData.fromSource W₁ (Ws t) (as t) (frzChart W₂ t) κ r (W₂ t) (W₂ 0) V

/-- The opposite view at a fixed first prefix, in source-zero coordinates. -/
def seedTView {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ)
    (bt Wt : ℝ → ℝ → ℝ) (V : Fin n → ℝ → ℝ) (s : ℝ) : FrzData n :=
  ⟨(fun u => W₂ u - W₂ 0), Wt s, bt s, frzChart (fun u => W₁ u - W₂ 0) s,
    16 / κ, (fun m => -(κ / 4) * r m), W₁ s - W₂ 0, (fun m => V m s - W₂ 0)⟩

/-- The opposite original force coordinate is the image of the first source,
with precisely the source-zero translation. -/
theorem seedTView_source {n : ℕ} (κ : ℝ) (r : Fin n → ℝ) (W₁ W₂ : ℝ → ℝ)
    (bt Wt : ℝ → ℝ → ℝ) (V : Fin n → ℝ → ℝ) (s t : ℝ) :
    (seedTView κ r W₁ W₂ bt Wt V s).seedAccessSource (-W₂ 0) t =
      (frzChart W₂ t 0).re - W₂ 0 := by
  simp only [FrzData.seedAccessSource, seedTView, fwdMap_sub_const, ofReal_neg,
    neg_add_cancel, frzChart, add_re, ofReal_re]
  ring

/-- Translation preserves the ordinary derivative at the separated source. -/
theorem deriv_fwdMap_sub_const_source (W : ℝ → ℝ) (c t : ℝ) :
    deriv (fwdMap (fun u => W u - c) t) ((-c : ℝ) : ℂ) = deriv (fwdMap W t) 0 := by
  have hf : fwdMap (fun u => W u - c) t = fun z => fwdMap W t (z + c) :=
    funext (fwdMap_sub_const W c t)
  rw [hf, deriv_comp_add_const]
  simp only [ofReal_neg, neg_add_cancel]

/-- The original derivative in a source record is literally one at time zero. -/
theorem source_deriv_zero (W : ℝ → ℝ) (p : ℝ) :
    (deriv (fwdMap W 0) p).re = 1 := by
  have hf : fwdMap W 0 = fun z => z - (W 0 : ℂ) := funext (fwdMap_zero_eq_sub W)
  rw [hf, deriv_sub_const]
  change (deriv (id : ℂ → ℂ) (p : ℂ)).re = 1
  rw [deriv_id]
  rfl

/-- The original coordinate in a source record starts at its specified source. -/
theorem source_value_zero (W : ℝ → ℝ) (p : ℝ) :
    (fwdMap W 0 p).re + W 0 = p := by
  rw [fwdMap_zero_eq_sub]
  simp only [sub_re, ofReal_re]
  ring

end InteractingSLE.ZhanGT4
