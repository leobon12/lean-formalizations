/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualForceLaw
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# The stopped dual coupling on one rectangle: optional sampling in both coordinates

Packet PROVE-ZHAN-GT4-A17. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L341–L343, L401–L406, R38): "The positive density `M(S₁, S₂)` … has expectation one, by
optional sampling successively in the two coordinates" and "its restriction to each stopped rectangle has density
`M(S₁ᵐ, S₂ᵐ)`".

For one rectangle `i` and events `A` of curve `1` stopped at `S₁ i`, `B` of curve `2` stopped at `S₂ i`:

* **curve `1`** (`DualHyp.setIntegral_dualPatch_mul_E₁_eq`): for every curve-`2` path, optional sampling of A14's
  column martingale (curve `2` frozen) at `S₁ i` replaces `M*(T, T) · m₁` by `M*(S₁ i, T) · Ñ(S₁ i, 0)/Ñ(0, 0)`;
* **curve `2`** (`DualHyp.setIntegral_patchS_mul_E₂_eq`): for every curve-`1` path, optional sampling of A15's
  `t`-direction column martingale (curve `1` frozen, height cap `S₁ i`) at `S₂ i` replaces `M*(S₁ i, T) · m₂` by
  `M(S₁ i, S₂ i) · Ñ(0, S₂ i)/Ñ(0, 0)`;
* **the rectangle law** (`DualHyp.dualCoupling_rect`): `dualCoupling (A ×ˢ B)` is the integral over `A × B` of
  `M(S₁ i, S₂ i) · Ñ(S₁ i, 0)/Ñ(0, 0) · Ñ(0, S₂ i)/Ñ(0, 0)`.
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### The column product at an arbitrary time -/

section ColPatch

variable {Ω : Type*} {ι : Type*} [Fintype ι] {n : ℕ}

/-- **A14's column product at any time `s`** is the (D11) patch of the canonical normalised density at `(s, T)`
times the marginal factor `Ñ(max S₁ ∧ s, 0)/Ñ(0, 0)` (height cap `T` above every frozen height). -/
theorem colProd_frzDens_eq_patch {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W₂ : ℝ → ℝ} {S₁ : ι → Ω → ℝ≥0} {S₂ : ι → ℝ}
    {Tm : ℝ} (hS₂m : ∀ i, S₂ i ≤ Tm) (rr p : Fin n → ℝ) (s : ℝ≥0) (ω : Ω) :
    colProd (frzDens κ B W₂ S₁ S₂ Tm rr p) S₁ S₂ Tm s ω =
      patch (fun i => (S₁ i ω : ℝ)) S₂
        (fun x y => Real.exp (normLog (sEll κ rr (drive κ B ω) W₂
          (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
          (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p) x y)) s Tm *
      Real.exp (sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
          (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p
          (min (maxIn (stairCols fun i => (S₁ i ω : ℝ))) s) 0 -
        sEll κ rr (drive κ B ω) W₂ (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂)
          (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p 0 0) := by
  set N := frzDens κ B W₂ S₁ S₂ Tm rr p with hNdef
  have hN : ∀ ω x y, 0 < N ω x y := fun ω x y => Real.exp_pos _
  have hpm := patch_mul_marginal (S₁ := fun i => (S₁ i ω : ℝ)) (S₂ := S₂) (fun i => (S₁ i ω).coe_nonneg)
    (N := N ω) (hN ω) s.coe_nonneg Tm
  have hcolP : colProd N S₁ S₂ Tm s ω = ∏ c ∈ stairCols (fun i => (S₁ i ω : ℝ)),
      (N ω (min c s) (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) Tm) /
        N ω (min (prevIn (stairCols fun i => (S₁ i ω : ℝ)) c) s)
          (min (stairH (fun i => (S₁ i ω : ℝ)) S₂ c) Tm)) := rfl
  rw [hcolP, ← hpm]
  have hNe : ∀ x y, N ω x y = Real.exp (sEll κ rr (drive κ B ω) W₂
      (sSelA (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) (sSelW (drive κ B ω) W₂ (fun i => (S₁ i ω : ℝ)) S₂) p
      x y) := fun x y => frzDens_eq_exp_sEll hS₂m rr p ω x y
  simp only [hNe, normFactor_exp]
  rw [← Real.exp_sub]

/-- **A15's `t`-direction column product at any time `s`, height cap `tb`** (curve `1` frozen at `W₁`): the (D11)
patch of the canonical `t`-view normalised density at `(s, tb)` times the marginal factor
`Ñ_t(0, max S₂ ∧ s)/Ñ_t(0, 0)`. Only heights `≤ tb` are evaluated, where A14's selection is the canonical one. -/
theorem colProd_frzDens_tView_eq_patch {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} (hB0 : ∀ ω, B 0 ω = 0) {W₁ : ℝ → ℝ} {x₂ : ℝ}
    {S₂ : ι → Ω → ℝ≥0} {S₁ : ι → ℝ} {tb : ℝ} (rr p : Fin n → ℝ) (s : ℝ≥0) (ω : Ω) :
    colProd (frzDens (16 / κ) B (fun u => W₁ u - x₂) S₂ S₁ tb (fun m => -(κ / 4) * rr m) (fun m => p m - x₂))
        S₂ S₁ tb s ω =
      patch (fun i => (S₂ i ω : ℝ)) S₁
        (fun y x => Real.exp (normLog (tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
          (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
          (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p) x y)) s tb *
      Real.exp (tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
          (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
          (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p 0
          (min (maxIn (stairCols fun i => (S₂ i ω : ℝ))) s) -
        tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
          (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
          (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p 0 0) := by
  set N := frzDens (16 / κ) B (fun u => W₁ u - x₂) S₂ S₁ tb (fun m => -(κ / 4) * rr m) (fun m => p m - x₂)
    with hNdef
  set L : ℝ → ℝ → ℝ := fun y x => tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
    (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
    (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p x y with hL
  have hNe : ∀ y x, x ≤ tb → N ω y x = Real.exp (L y x) := fun y x hx => by
    rw [hNdef, frzDens_eq_exp_sEll_of_le hx, hL]
    simp only
    rw [tEll_eq_sEll κ rr p W₁ (drive (16 / κ) B ω) (QuantumZipper.drive_zero (hB0 ω)) x₂ S₁
      (fun i => (S₂ i ω : ℝ)) x y]
  have hcolP : colProd N S₂ S₁ tb s ω = ∏ c ∈ stairCols (fun i => (S₂ i ω : ℝ)),
      (N ω (min c s) (min (stairH (fun i => (S₂ i ω : ℝ)) S₁ c) tb) /
        N ω (min (prevIn (stairCols fun i => (S₂ i ω : ℝ)) c) s)
          (min (stairH (fun i => (S₂ i ω : ℝ)) S₁ c) tb)) := rfl
  have hprod : colProd N S₂ S₁ tb s ω = ∏ c ∈ stairCols (fun i => (S₂ i ω : ℝ)),
      (Real.exp (L (min c s) (min (stairH (fun i => (S₂ i ω : ℝ)) S₁ c) tb)) /
        Real.exp (L (min (prevIn (stairCols fun i => (S₂ i ω : ℝ)) c) s)
          (min (stairH (fun i => (S₂ i ω : ℝ)) S₁ c) tb))) := by
    rw [hcolP]
    exact Finset.prod_congr rfl fun c _ => by rw [hNe _ _ (min_le_right _ _), hNe _ _ (min_le_right _ _)]
  have hpm := patch_mul_marginal (S₁ := fun i => (S₂ i ω : ℝ)) (S₂ := S₁) (fun i => (S₂ i ω).coe_nonneg)
    (N := fun y x => Real.exp (L y x)) (fun _ _ => Real.exp_pos _) s.coe_nonneg tb
  rw [hprod, ← hpm]
  have hsym : ∀ y x, normLog L y x = normLog (tEll κ rr W₁ (fun u => drive (16 / κ) B ω u + x₂)
      (tSelA W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ)))
      (tSelW W₁ (fun u => drive (16 / κ) B ω u + x₂) S₁ (fun i => (S₂ i ω : ℝ))) p) x y := fun y x => by
    simp only [normLog, hL]; ring
  simp only [normFactor_exp L, hsym]
  rw [← Real.exp_sub]

end ColPatch

/-! ### The patch and the marginal factors at arbitrary points -/

section Rect

variable {Ω₁ Ω₂ : Type*} {ι : Type*} [Fintype ι] {n : ℕ}

/-- The (D11) patch at `(s, T)` of the canonical `s`-view normalised density of a pair of paths
(`dualPatch` is its value at `s = T`). -/
def dualPatchAt (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm s : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ :=
  patch (fun i => (S₁ i ω₁ : ℝ)) (fun i => (S₂ i ω₂ : ℝ))
    (fun x y => Real.exp (normLog (sEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (sSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ)))
      (sSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ))) p) x y)) s Tm

/-- The canonical `s`-view log-density `ℓ(x, y) = log Ñ(x, y)` of a pair of paths. -/
def pairS (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ → ℝ → ℝ :=
  sEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
    (sSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
      (fun i => (S₂ i ω₂ : ℝ)))
    (sSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
      (fun i => (S₂ i ω₂ : ℝ))) p

/-- The canonical `t`-view log-density `ℓ_t(x, y)` of a pair of paths. -/
def pairT (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ → ℝ → ℝ :=
  tEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
    (tSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
      (fun i => (S₂ i ω₂ : ℝ)))
    (tSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
      (fun i => (S₂ i ω₂ : ℝ))) p

theorem dualPatch_eq_at (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ = dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm Tm ω₁ ω₂ := rfl

theorem dualE₁_eq_pairS (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ = Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂
      (min (maxIn (stairCols fun i => (S₁ i ω₁ : ℝ))) Tm) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) := rfl

theorem dualE₂_eq_pairT (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ = Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0
      (min (maxIn (stairCols fun i => (S₂ i ω₂ : ℝ))) Tm) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) := rfl

/-- **The rectangle density** `M(S₁ i, S₂ i) · Ñ(S₁ i, 0)/Ñ(0, 0) · Ñ_t(0, S₂ i)/Ñ_t(0, 0)` of the stopped dual coupling
on rectangle `i` (§A.1.4, "its restriction to each stopped rectangle has density `M(S₁ᵐ, S₂ᵐ)`"). -/
def rectDens (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (i : ι) (ω : Ω₁ × Ω₂) : ℝ :=
  Real.exp (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2) (S₁ i ω.1) (S₂ i ω.2)) *
    Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0) *
    Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 (S₂ i ω.2) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0)

variable {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {κ : ℝ} {P₁ : Measure Ω₁}
  {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂}
  {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ} {Tm : ℝ}
  {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
include h

/-- **Optional sampling in the curve-`1` coordinate** (curve `2` frozen): on an event `A` of curve `1` stopped at
`S₁ i`, the patched density `M*(T, T) · Ñ(max S₁, 0)/Ñ(0, 0)` integrates like `M*(S₁ i, T) · Ñ(S₁ i, 0)/Ñ(0, 0)`
(A14's column martingale is a bounded right-continuous martingale; `setIntegral_stoppedValue_eq_of_rightContinuous`). -/
theorem setIntegral_dualPatch_mul_E₁_eq (rr : Fin n → ℝ) (i : ι) (ω₂ : Ω₂) {A : Set Ω₁}
    (hA : MeasurableSet[(h.stop₁ i).measurableSpace] A) :
    ∫ ω₁ in A, dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ ∂P₁ =
      ∫ ω₁ in A, dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) ∂P₁ ∧
      ∃ K : ℝ, ∀ ω₁, |dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂| ≤ K ∧
        |dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
          Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0)| ≤ K := by
  obtain ⟨ω₁₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  have hE := h.twoEncl ω₁₀ ω₂
  have hP := h.isProbabilityMeasure₁
  obtain ⟨K, hK⟩ := martingale_colProd_frozen (𝓕 := 𝓕₁) (P := P₁) h.κpos h.bm₁ h.cont₁ h.zero₁ h.hull₁ h.hull₂
    h.δpos h.sep h.dpos h.qpos h.qH h.pH h.pinj Tm rr
  obtain ⟨hM, hMrc, hbd⟩ := hK h.stop₁ h.pos₁ h.le₁ h.K₁ hE.cont₂ hE.start₂ hE.qW hE.S₂pos hE.S₂le hE.K₂ h.Tmpos
  set s₀ : ℝ≥0 := Tm.toNNReal with hs₀
  have hs₀R : (s₀ : ℝ) = Tm := Real.coe_toNNReal _ h.Tmpos.le
  have hle : (fun ω => (S₁ i ω : WithTop ℝ≥0)) ≤ fun _ => ((s₀ : ℝ≥0) : WithTop ℝ≥0) := fun ω =>
    WithTop.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, hs₀R]; exact h.le₁ i ω)
  have hos := setIntegral_stoppedValue_eq_of_rightContinuous hM hMrc (h.stop₁ i)
    (isStoppingTime_const 𝓕₁ s₀) hle (T := s₀) (fun _ => le_rfl) hA
  simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] at hos
  have e1 : ∀ ω₁, colProd (frzDens κ B₁ (fun u => drive (16 / κ) B₂ ω₂ u + x₂) S₁ (fun i => (S₂ i ω₂ : ℝ)) Tm rr p)
      S₁ (fun i => (S₂ i ω₂ : ℝ)) Tm s₀ ω₁ =
      dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ := fun ω₁ => by
    rw [colProd_frzDens_eq_patch hE.S₂le, hs₀R]; rfl
  have e2 : ∀ ω₁, colProd (frzDens κ B₁ (fun u => drive (16 / κ) B₂ ω₂ u + x₂) S₁ (fun i => (S₂ i ω₂ : ℝ)) Tm rr p)
      S₁ (fun i => (S₂ i ω₂ : ℝ)) Tm (S₁ i ω₁) ω₁ =
      dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) :=
      fun ω₁ => by
    have hmin : min (maxIn (stairCols fun i => (S₁ i ω₁ : ℝ))) (S₁ i ω₁ : ℝ) = S₁ i ω₁ :=
      min_eq_right (le_maxIn (Finset.mem_image_of_mem (fun i => (S₁ i ω₁ : ℝ)) (Finset.mem_univ i)))
    rw [colProd_frzDens_eq_patch hE.S₂le, hmin]
    rfl
  refine ⟨?_, K, fun ω => ⟨by rw [← e1]; exact hbd _ _, by rw [← e2]; exact hbd _ _⟩⟩
  simp only [e1, e2] at hos
  exact hos.symm

/-- **Optional sampling in the curve-`2` coordinate** (curve `1` frozen, height cap `S₁ i`): on an event `B` of curve
`2` stopped at `S₂ i`, `M*(S₁ i, T) · Ñ_t(0, max S₂)/Ñ_t(0, 0)` integrates like
`M(S₁ i, S₂ i) · Ñ_t(0, S₂ i)/Ñ_t(0, 0)` (A15's `t`-direction column martingale, the reflection `patch_twoView`, and
`M* = M` on the rectangle). -/
theorem setIntegral_patchAt_mul_E₂_eq (rr : Fin n → ℝ) (i : ι) (ω₁ : Ω₁) {B : Set Ω₂}
    (hB : MeasurableSet[(h.stop₂ i).measurableSpace] B) :
    ∫ ω₂ in B, dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ * dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ ∂P₂ =
      ∫ ω₂ in B, Real.exp (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂) (S₁ i ω₁) (S₂ i ω₂)) *
        Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 (S₂ i ω₂) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) ∂P₂ ∧
      ∃ K : ℝ, ∀ ω₂, |dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ * dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂| ≤ K ∧
        |Real.exp (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂) (S₁ i ω₁) (S₂ i ω₂)) *
          Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 (S₂ i ω₂) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0)| ≤ K := by
  obtain ⟨ω₂₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₂
  have hE := h.twoEncl ω₁ ω₂₀
  have hP := h.isProbabilityMeasure₂
  obtain ⟨K, hK⟩ := martingale_colProd_tView (𝓕 := 𝓕₂) (P := P₂) h.κpos h.bm₂ h.cont₂ h.zero₂ h.hull₁ h.hull₂
    h.δpos h.sep h.dpos h.qpos h.qH h.pH h.pinj Tm rr h.qx
  obtain ⟨hM, hMrc, hbd⟩ := hK h.stop₂ h.pos₂ h.le₂ h.K₂ hE.cont₁ hE.zero₁ hE.S₁pos hE.S₁le hE.K₁ (hE.S₁pos i)
  set s₀ : ℝ≥0 := Tm.toNNReal with hs₀
  have hs₀R : (s₀ : ℝ) = Tm := Real.coe_toNNReal _ h.Tmpos.le
  have hle : (fun ω => (S₂ i ω : WithTop ℝ≥0)) ≤ fun _ => ((s₀ : ℝ≥0) : WithTop ℝ≥0) := fun ω =>
    WithTop.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, hs₀R]; exact h.le₂ i ω)
  have hos := setIntegral_stoppedValue_eq_of_rightContinuous hM hMrc (h.stop₂ i)
    (isStoppingTime_const 𝓕₂ s₀) hle (T := s₀) (fun _ => le_rfl) hB
  simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe] at hos
  have htb : (0 : ℝ) ≤ S₁ i ω₁ := (S₁ i ω₁).coe_nonneg
  have e1 : ∀ ω₂, colProd (frzDens (16 / κ) B₂ (fun u => drive κ B₁ ω₁ u - x₂) S₂ (fun i => (S₁ i ω₁ : ℝ))
      (S₁ i ω₁) (fun m => -(κ / 4) * rr m) (fun m => p m - x₂)) S₂ (fun i => (S₁ i ω₁ : ℝ)) (S₁ i ω₁) s₀ ω₂ =
      dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ * dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ := fun ω₂ => by
    have hE' := h.twoEncl ω₁ ω₂
    rw [colProd_frzDens_tView_eq_patch (tb := (S₁ i ω₁ : ℝ)) h.zero₂, hs₀R, dualPatchAt,
      patch_twoView (fun j => (S₁ j ω₁).coe_nonneg) (fun j => (S₂ j ω₂).coe_nonneg) h.κpos.ne' hE'.cont₁ hE'.cont₂
        hE'.twoViewRect hE'.twoViewMarks htb h.Tmpos.le]
    rfl
  have e2 : ∀ ω₂, colProd (frzDens (16 / κ) B₂ (fun u => drive κ B₁ ω₁ u - x₂) S₂ (fun i => (S₁ i ω₁ : ℝ))
      (S₁ i ω₁) (fun m => -(κ / 4) * rr m) (fun m => p m - x₂)) S₂ (fun i => (S₁ i ω₁ : ℝ)) (S₁ i ω₁) (S₂ i ω₂) ω₂ =
      Real.exp (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂) (S₁ i ω₁) (S₂ i ω₂)) *
        Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 (S₂ i ω₂) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) :=
      fun ω₂ => by
    have hE' := h.twoEncl ω₁ ω₂
    have hmin : min (maxIn (stairCols fun i => (S₂ i ω₂ : ℝ))) (S₂ i ω₂ : ℝ) = S₂ i ω₂ :=
      min_eq_right (le_maxIn (Finset.mem_image_of_mem (fun i => (S₂ i ω₂ : ℝ)) (Finset.mem_univ i)))
    rw [colProd_frzDens_tView_eq_patch (tb := (S₁ i ω₁ : ℝ)) h.zero₂, hmin,
      ← patch_twoView (fun j => (S₁ j ω₁).coe_nonneg) (fun j => (S₂ j ω₂).coe_nonneg) h.κpos.ne' hE'.cont₁
        hE'.cont₂ hE'.twoViewRect hE'.twoViewMarks htb (S₂ i ω₂).coe_nonneg,
      patch_eq_of_inStair (fun j => (S₁ j ω₁).coe_nonneg) (fun y => by rw [normLog_zero_left, Real.exp_zero])
        htb le_rfl le_rfl (Real.exp_pos _)]
    rfl
  refine ⟨?_, K, fun ω => ⟨by rw [← e1]; exact hbd _ _, by rw [← e2]; exact hbd _ _⟩⟩
  simp only [e1, e2] at hos
  exact hos.symm

/-- **Joint measurability on `Ω₁ × Ω₂`** of the intermediate density `M*(S₁ i, T) · Ñ(S₁ i, 0)/Ñ(0, 0) · m₂` and of the
rectangle density `M(S₁ i, S₂ i) · Ñ(S₁ i, 0)/Ñ(0, 0) · Ñ_t(0, S₂ i)/Ñ_t(0, 0)` (A16's `measurable_pairNormLog`,
`measurable_pairEll_marg`, `measurable_tEll_marg` at random staircase points). -/
theorem measurable_condDens [Nonempty ι] (rr : Fin n → ℝ) (i : ι) :
    Measurable (fun ω : Ω₁ × Ω₂ => dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω.1) ω.1 ω.2 *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0) *
        dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω.1 ω.2) ∧
    Measurable (fun ω : Ω₁ × Ω₂ => Real.exp (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2) (S₁ i ω.1) (S₂ i ω.2)) *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0) *
        Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 (S₂ i ω.2) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0)) := by
  set V₂ : Ω₂ → ℝ → ℝ := fun ω u => drive (16 / κ) B₂ ω u + x₂ with hV₂
  have hB₁c : ∀ ω, Continuous fun r => B₁ r ω := h.cont₁
  have hB₂c : ∀ ω, Continuous fun r => B₂ r ω := h.cont₂
  have hB₂m := h.measurable_B₂
  have hV₂c : ∀ ω, Continuous (V₂ ω) := fun ω =>
    (QuantumZipper.drive_continuous (hB₂c ω)).add continuous_const
  have hVhit : ∀ t, 0 ≤ t → ∀ L : Set ℂ, IsCompact L → L ⊆ H →
      MeasurableSet {ω | (L ∩ fwdHull (V₂ ω) t).Nonempty} := fun t ht L hL hLH =>
    measurableSet_hit_drive_add hB₂c hB₂m ht x₂ hL hLH
  have hVfwd : ∀ t, 0 ≤ t → ∀ z ∈ H, Measurable fun ω => fwdMap (V₂ ω) t z := fun t ht z hz => by
    simp only [hV₂, ConformalImageFull.fwdMap_add_const]
    refine measurable_fwdMap_drive_at hB₂c hB₂m ht ?_
    have := hz
    simp only [QuantumZipper.H, Set.mem_ofPred_eq] at this ⊢
    simpa using this
  have hVt : ∀ t, Measurable fun ω => V₂ ω t := fun t => by
    show Measurable fun ω => Real.sqrt (16 / κ) * B₂ t.toNNReal ω + x₂
    exact (measurable_const.mul (hB₂m _)).add_const _
  have hS₁ : ∀ i, Measurable fun ω => (S₁ i ω : ℝ) := fun i => measurable_coe_of_isStoppingTime (h.stop₁ i)
  have hS₂ : ∀ i, Measurable fun ω => (S₂ i ω : ℝ) := fun i => measurable_coe_of_isStoppingTime (h.stop₂ i)
  have hE : ∀ ω : Ω₁ × Ω₂, TwoEncl (drive κ B₁ ω.1) (V₂ ω.2) (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ))
      H₁ H₂ δ q d p Tm := fun ω => h.twoEncl ω.1 ω.2
  have hS₁' : ∀ i, Measurable fun ω : Ω₁ × Ω₂ => (S₁ i ω.1 : ℝ) := fun i => (hS₁ i).comp measurable_fst
  have hS₂' : ∀ i, Measurable fun ω : Ω₁ × Ω₂ => (S₂ i ω.2 : ℝ) := fun i => (hS₂ i).comp measurable_snd
  have hNL := fun {X Y : Ω₁ × Ω₂ → ℝ} (hX : Measurable X) (hY : Measurable Y) (hX0 : ∀ ω, 0 ≤ X ω)
      (hY0 : ∀ ω, 0 ≤ Y ω) (hXY : ∀ ω, ∃ i, X ω ≤ S₁ i ω.1 ∧ Y ω ≤ S₂ i ω.2) =>
    measurable_pairNormLog (p := p) h.cont₁ h.measurable_B₁ hV₂c hVhit hVfwd hVt hS₁ hS₂ hE h.κpos.ne' rr hX hY hX0
      hY0 hXY
  have hm₁ := measurable_pairEll_marg (p := p) h.cont₁ h.measurable_B₁ hV₂c hVhit hVfwd hVt hS₁ hS₂ hE rr
    (X := fun ω => (S₁ i ω.1 : ℝ)) (hS₁' i) (fun ω => (S₁ i ω.1).coe_nonneg) (fun ω => ⟨i, le_rfl⟩)
  have hm₂' := measurable_tEll_marg h.measurable_B₁ h.cont₁ hB₂c hB₂m h.zero₂ hS₁ hS₂ hE rr
    (Y := fun ω => (S₂ i ω.2 : ℝ)) (hS₂' i) (fun ω => (S₂ i ω.2).coe_nonneg)
    (fun ω => by
      rw [stairH_zero_eq_maxIn fun j => ((hE ω).S₁pos j).le]
      exact le_maxIn (Finset.mem_image_of_mem (fun j => (S₂ j ω.2 : ℝ)) (Finset.mem_univ i)))
  have hm₂ := measurable_tEll_marg h.measurable_B₁ h.cont₁ hB₂c hB₂m h.zero₂ hS₁ hS₂ hE rr
    (Y := fun ω => min (maxIn (stairCols fun i => (S₂ i ω.2 : ℝ))) Tm)
    ((measurable_maxIn_stairCols hS₂').min measurable_const) (fun ω => le_min (maxIn_nonneg _) h.Tmpos.le)
    (fun ω => by rw [stairH_zero_eq_maxIn fun i => ((hE ω).S₁pos i).le]; exact min_le_left _ _)
  have hXY : ∀ j (ω : Ω₁ × Ω₂), ∃ k, (S₁ j ω.1 : ℝ) ≤ S₁ k ω.1 ∧
      stairH (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) (S₁ j ω.1) = S₂ k ω.2 :=
    fun j ω => exists_eq_stairH (fun k => ((hE ω).S₂pos k).le) le_rfl
  have hYm : ∀ j, Measurable fun ω : Ω₁ × Ω₂ =>
      min (stairH (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) (S₁ j ω.1)) Tm := fun j =>
    (measurable_stairH hS₁' hS₂' (hS₁' j)).min measurable_const
  have hpatch : Measurable fun ω : Ω₁ × Ω₂ => patchLog (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ))
      (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2)) (S₁ i ω.1) Tm := by
    have e : (fun ω : Ω₁ × Ω₂ => patchLog (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ))
        (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2)) (S₁ i ω.1) Tm) = fun ω => ∑ j,
        (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2) (min (S₁ j ω.1) (S₁ i ω.1))
            (min (stairH (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) (S₁ j ω.1)) Tm) -
          normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2)
            (min (prevIn (stairCols fun i => (S₁ i ω.1 : ℝ)) (S₁ j ω.1)) (S₁ i ω.1))
            (min (stairH (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) (S₁ j ω.1)) Tm)) /
        ((univ.filter fun k => (S₁ k ω.1 : ℝ) = S₁ j ω.1).card : ℝ) := by
      funext ω
      unfold patchLog
      exact sum_stairCols_eq (fun i => (S₁ i ω.1 : ℝ)) fun c =>
        normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2) (min c (S₁ i ω.1))
            (min (stairH (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) c) Tm) -
          normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2)
            (min (prevIn (stairCols fun i => (S₁ i ω.1 : ℝ)) c) (S₁ i ω.1))
            (min (stairH (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ)) c) Tm)
    rw [e]
    refine Finset.measurable_sum _ fun j _ => ((hNL ((hS₁' j).min (hS₁' i)) (hYm j) ?_ ?_ ?_).sub
      (hNL ((measurable_prevIn_stairCols hS₁' (hS₁' j)).min (hS₁' i)) (hYm j) ?_ ?_ ?_)).div
      (measurable_card_filter_eq hS₁' j)
    · exact fun ω => le_min (S₁ j ω.1).coe_nonneg (S₁ i ω.1).coe_nonneg
    · exact fun ω => le_min (stairH_nonneg _) h.Tmpos.le
    · intro ω
      obtain ⟨k, hk, hkeq⟩ := hXY j ω
      exact ⟨k, (min_le_left _ _).trans hk, (min_le_left _ _).trans hkeq.le⟩
    · exact fun ω => le_min (prevIn_nonneg _ _) (S₁ i ω.1).coe_nonneg
    · exact fun ω => le_min (stairH_nonneg _) h.Tmpos.le
    · intro ω
      obtain ⟨k, hk, hkeq⟩ := hXY j ω
      exact ⟨k, ((min_le_left _ _).trans (prevIn_le (S₁ j ω.1).coe_nonneg)).trans hk,
        (min_le_left _ _).trans hkeq.le⟩
  have hrect := hNL (hS₁' i) (hS₂' i) (fun ω => (S₁ i ω.1).coe_nonneg) (fun ω => (S₂ i ω.2).coe_nonneg)
    fun ω => ⟨i, le_rfl, le_rfl⟩
  refine ⟨?_, ((Real.measurable_exp.comp hrect).mul (Real.measurable_exp.comp hm₁)).mul
    (Real.measurable_exp.comp hm₂')⟩
  have e : (fun ω : Ω₁ × Ω₂ => dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω.1) ω.1 ω.2) = fun ω =>
      Real.exp (patchLog (fun i => (S₁ i ω.1 : ℝ)) (fun i => (S₂ i ω.2 : ℝ))
        (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2)) (S₁ i ω.1) Tm) := by
    funext ω
    simp only [dualPatchAt, patch, Real.log_exp]
    rfl
  rw [show (fun ω : Ω₁ × Ω₂ => dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω.1) ω.1 ω.2 *
      Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0) *
      dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω.1 ω.2) = fun ω =>
      (fun ω : Ω₁ × Ω₂ => dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω.1) ω.1 ω.2) ω *
      Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 (S₁ i ω.1) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω.1 ω.2 0 0) *
      dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω.1 ω.2 from rfl, e]
  exact ((Real.measurable_exp.comp hpatch).mul (Real.measurable_exp.comp hm₁)).mul (Real.measurable_exp.comp hm₂)

/-- The curve-`1` marginal exponent at height `0` does not depend on the curve-`2` path (`sEll_zero_congr`). -/
theorem pairS_zero_congr (rr : Fin n → ℝ) (ω₁ : Ω₁) (ω₂ ω₂' : Ω₂) (x : ℝ) :
    pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ x 0 = pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂' x 0 := by
  have hE := h.twoEncl ω₁ ω₂
  have hE' := h.twoEncl ω₁ ω₂'
  have h0 : drive (16 / κ) B₂ ω₂ 0 + x₂ = drive (16 / κ) B₂ ω₂' 0 + x₂ := by
    rw [QuantumZipper.drive_zero (h.zero₂ ω₂), QuantumZipper.drive_zero (h.zero₂ ω₂')]
  exact sEll_zero_congr κ rr p (drive κ B₁ ω₁) hE.cont₂ hE'.cont₂ h0 _ (fun j => (S₂ j ω₂).coe_nonneg)
    (fun j => (S₂ j ω₂').coe_nonneg) x

/-- **The stopped dual coupling on one rectangle** (§A.1.3–A.1.4, "optional sampling successively in the two
coordinates"; "its restriction to each stopped rectangle has density `M(S₁ᵐ, S₂ᵐ)`"): for an event `A` of curve `1`
stopped at `S₁ i` and an event `B` of curve `2` stopped at `S₂ i`, the mass of `A × B` under `dualCoupling` is the
integral over `A × B` (under `P₁ ⊗ P₂`) of the rectangle density
`M(S₁ i, S₂ i) · Ñ(S₁ i, 0)/Ñ(0, 0) · Ñ_t(0, S₂ i)/Ñ_t(0, 0)`. -/
theorem dualCoupling_rect [Nonempty ι] (rr : Fin n → ℝ) (i : ι) {A : Set Ω₁} {B : Set Ω₂}
    (hA : MeasurableSet[(h.stop₁ i).measurableSpace] A) (hB : MeasurableSet[(h.stop₂ i).measurableSpace] B) :
    dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm (A ×ˢ B) =
      ∫⁻ ω in A ×ˢ B, ENNReal.ofReal (rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i ω) ∂(P₁.prod P₂) := by
  have := h.isProbabilityMeasure₁
  have := h.isProbabilityMeasure₂
  have hAm : MeasurableSet A := (h.stop₁ i).measurableSpace_le _ hA
  have hBm : MeasurableSet B := (h.stop₂ i).measurableSpace_le _ hB
  obtain ⟨hI, hR⟩ := h.measurable_condDens rr i
  have hR' : Measurable (rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i) := hR
  obtain ⟨ω₂₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₂
  have hDm := h.measurable_dualDens rr
  -- notation
  set c : Ω₁ → ℝ := fun ω₁ => Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂₀ (S₁ i ω₁) 0 -
    pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂₀ 0 0) with hc
  have hcpos : ∀ ω₁, 0 < c ω₁ := fun _ => Real.exp_pos _
  have he₁ : ∀ ω₁ ω₂, Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 -
      pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) = c ω₁ := fun ω₁ ω₂ => by
    rw [hc, h.pairS_zero_congr rr ω₁ ω₂ ω₂₀, h.pairS_zero_congr rr ω₁ ω₂ ω₂₀ 0]
  have hpatchAt_pos : ∀ s ω₁ ω₂, 0 < dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm s ω₁ ω₂ := fun _ _ _ => Real.exp_pos _
  have hfpos : ∀ ω₁ ω₂, 0 < dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ :=
    fun _ _ => mul_pos (dualPatch_pos _ _ _ _ _ _ _ _ _ _ _) (Real.exp_pos _)
  -- the product density on the product space, and Fubini with curve `1` inside
  rw [dualCoupling, withDensity_apply _ (hAm.prod hBm), ← Measure.prod_restrict,
    lintegral_prod_symm _ hDm.ennreal_ofReal.aemeasurable, lintegral_prod _ hR'.ennreal_ofReal.aemeasurable]
  -- step 1: optional sampling in curve `1`, for every curve-`2` path
  have step1 : ∀ ω₂, ∫⁻ ω₁, ENNReal.ofReal (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ))
      (fun i ω => (S₂ i ω : ℝ)) Tm (ω₁, ω₂)) ∂P₁.restrict A =
      ∫⁻ ω₁, ENNReal.ofReal (dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) *
        dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₁.restrict A := by
    intro ω₂
    obtain ⟨hint, K, hK⟩ := h.setIntegral_dualPatch_mul_E₁_eq rr i ω₂ hA
    have hm2 : 0 < margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂ := margDens₂_pos _ _ _ _ _ _ _ _
    have hfm : Measurable fun ω₁ => dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
        dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ := by
      have := (hDm.comp (measurable_prodMk_right (y := ω₂))).div_const (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂)
      convert this using 1
      funext ω₁
      simp only [Function.comp, dualDens_eq, h.dualE₂_eq rr ω₁ ω₂, ]
      field_simp [hm2.ne']
    have hgm : Measurable fun ω₁ => dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) := by
      have := (hI.comp (measurable_prodMk_right (y := ω₂))).div_const (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂)
      convert this using 1
      funext ω₁
      simp only [Function.comp, h.dualE₂_eq rr ω₁ ω₂, ]
      field_simp [hm2.ne']
    have hfi : Integrable (fun ω₁ => dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
        dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) (P₁.restrict A) :=
      (Integrable.of_bound hfm.aestronglyMeasurable K (Eventually.of_forall fun ω₁ => (hK ω₁).1)).restrict
    have hgi : Integrable (fun ω₁ => dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0))
        (P₁.restrict A) :=
      (Integrable.of_bound hgm.aestronglyMeasurable K (Eventually.of_forall fun ω₁ => (hK ω₁).2)).restrict
    calc ∫⁻ ω₁, ENNReal.ofReal (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm
            (ω₁, ω₂)) ∂P₁.restrict A
        = ∫⁻ ω₁, ENNReal.ofReal (dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
            dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) * ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) ∂P₁.restrict A := by
          refine lintegral_congr fun ω₁ => ?_
          rw [dualDens_eq, h.dualE₂_eq rr ω₁ ω₂,
            ENNReal.ofReal_mul (hfpos ω₁ ω₂).le]
      _ = ENNReal.ofReal (∫ ω₁, dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
            dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ ∂P₁.restrict A) * ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ofReal_integral_eq_lintegral_ofReal hfi
            (Eventually.of_forall fun ω₁ => (hfpos ω₁ ω₂).le)]
      _ = ENNReal.ofReal (∫ ω₁, dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
            Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0)
              ∂P₁.restrict A) * ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) := by rw [hint]
      _ = _ := by
          rw [ofReal_integral_eq_lintegral_ofReal hgi
            (Eventually.of_forall fun ω₁ => (mul_pos (hpatchAt_pos _ _ _) (Real.exp_pos _)).le),
            ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun ω₁ => ?_
          rw [h.dualE₂_eq rr ω₁ ω₂, ← ENNReal.ofReal_mul (mul_pos (hpatchAt_pos _ _ _) (Real.exp_pos _)).le]
  -- step 2: optional sampling in curve `2`, for every curve-`1` path
  have step2 : ∀ ω₁, ∫⁻ ω₂, ENNReal.ofReal (dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
        Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) *
        dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₂.restrict B =
      ∫⁻ ω₂, ENNReal.ofReal (rectDens κ rr p B₁ B₂ x₂ S₁ S₂ i (ω₁, ω₂)) ∂P₂.restrict B := by
    intro ω₁
    obtain ⟨hint, K, hK⟩ := h.setIntegral_patchAt_mul_E₂_eq rr i ω₁ hB
    have hfm : Measurable fun ω₂ => dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
        dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ := by
      have := (hI.comp (measurable_prodMk_left (x := ω₁))).div_const (c ω₁)
      convert this using 1
      funext ω₂
      simp only [Function.comp, he₁]
      field_simp [(hcpos ω₁).ne']
    have hgm : Measurable fun ω₂ => Real.exp (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂) (S₁ i ω₁) (S₂ i ω₂)) *
        Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 (S₂ i ω₂) - pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) := by
      have := (hR'.comp (measurable_prodMk_left (x := ω₁))).div_const (c ω₁)
      convert this using 1
      funext ω₂
      simp only [Function.comp, rectDens, he₁]
      field_simp [(hcpos ω₁).ne']
    have hfi := (Integrable.of_bound (μ := P₂) hfm.aestronglyMeasurable K
      (Eventually.of_forall fun ω₂ => (hK ω₂).1)).restrict (s := B)
    have hgi := (Integrable.of_bound (μ := P₂) hgm.aestronglyMeasurable K
      (Eventually.of_forall fun ω₂ => (hK ω₂).2)).restrict (s := B)
    calc ∫⁻ ω₂, ENNReal.ofReal (dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
            Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) *
            dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₂.restrict B
        = ∫⁻ ω₂, ENNReal.ofReal (c ω₁) * ENNReal.ofReal (dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
            dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₂.restrict B := by
          refine lintegral_congr fun ω₂ => ?_
          rw [he₁, ← ENNReal.ofReal_mul (hcpos ω₁).le]
          congr 1; ring
      _ = ENNReal.ofReal (c ω₁) * ENNReal.ofReal (∫ ω₂, dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
            dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ ∂P₂.restrict B) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ofReal_integral_eq_lintegral_ofReal hfi
            (Eventually.of_forall fun ω₂ => (mul_pos (hpatchAt_pos _ _ _) (Real.exp_pos _)).le)]
      _ = ENNReal.ofReal (c ω₁) * ENNReal.ofReal (∫ ω₂, Real.exp (normLog (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂)
            (S₁ i ω₁) (S₂ i ω₂)) * Real.exp (pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 (S₂ i ω₂) -
              pairT κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) ∂P₂.restrict B) := by rw [hint]
      _ = _ := by
          rw [ofReal_integral_eq_lintegral_ofReal hgi
            (Eventually.of_forall fun ω₂ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le),
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun ω₂ => ?_
          rw [← ENNReal.ofReal_mul (hcpos ω₁).le, rectDens]
          simp only
          rw [he₁]
          congr 1; ring
  -- assemble: step 1 inside, swap, step 2 inside
  simp_rw [step1]
  rw [lintegral_lintegral_swap (f := fun ω₂ ω₁ => ENNReal.ofReal
    (dualPatchAt κ rr p B₁ B₂ x₂ S₁ S₂ Tm (S₁ i ω₁) ω₁ ω₂ *
      Real.exp (pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ (S₁ i ω₁) 0 - pairS κ rr p B₁ B₂ x₂ S₁ S₂ ω₁ ω₂ 0 0) *
      dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂)) ((hI.ennreal_ofReal.comp measurable_swap).aemeasurable)]
  simp_rw [step2]

end DualHyp

end Rect

end InteractingSLE.ZhanGT4
