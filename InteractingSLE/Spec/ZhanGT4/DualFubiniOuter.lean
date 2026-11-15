/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualJointMeas

/-!
# The outer Fubini integral: the stopped dual coupling has mass one and the force-point marginals

Packet PROVE-ZHAN-GT4-A16. Source: Astra, *Follow-up proofs*, §A.1.3 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L341–L343, R38): "The positive density `M(S₁, S₂)`, with respect to the product of the two
marginal laws, has expectation one, by optional sampling successively in the two coordinates. Its marginals are
unchanged." and §A.1.4 (L401–L406): "`M*(∞, ∞)` is a positive probability density with unchanged marginal laws".

Two independent ordinary chordal curves: curve `1` = `√κ B₁` on `(Ω₁, P₁)`, curve `2` = `√(16/κ) B₂ + x₂` on
`(Ω₂, P₂)`, with exit times `S₁ i`, `S₂ i` from finitely many protected enclosure pairs (`DualHyp`). The density
`D = M*_s(T, T) · m₁ · m₂` (`dualDens`, measurable by `DualJointMeas`) on `Ω₁ × Ω₂` has the height-`0` marginal factors
`m₁ = Ñ_s(max S₁, 0)/Ñ_s(0, 0)` (a function of curve `1` only: `margDens₁`) and `m₂ = Ñ_t(0, max S₂)/Ñ_t(0, 0)` (a
function of curve `2` only: `margDens₂`). Then:

* **`dualCoupling`** `= D · (P₁ ⊗ P₂)` is a probability measure (`isProbabilityMeasure_dualCoupling`);
* **its curve-`1` marginal is `m₁ · P₁`** (`map_fst_dualCoupling`: inner integral over curve `2` by A15's
  `integral_patch_mul_tMarg_eq_one`, outer one by `integral_exp_sMarg_eq_one`), and **its curve-`2` marginal is
  `m₂ · P₂`** (`map_snd_dualCoupling`: inner integral over curve `1` by `integral_patch_mul_sMarg_eq_one`).

The marginal densities `m₁`, `m₂` are the one-curve force-point (`SLE_κ(ρ)`) tilts of ordinary `SLE_κ` stopped at the
exit times; their identification with the force-point laws is not part of this file.
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-- An `ℝ≥0`-valued stopping time is a measurable real function. -/
theorem measurable_coe_of_isStoppingTime {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {S : Ω → ℝ≥0} (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) : Measurable fun ω => (S ω : ℝ) := by
  refine measurable_of_Iic fun x => ?_
  by_cases hx : x < 0
  · have e : (fun ω => (S ω : ℝ)) ⁻¹' Iic x = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
      exact hx.trans_le (S ω).coe_nonneg
    rw [e]; exact MeasurableSet.empty
  · have e : (fun ω => (S ω : ℝ)) ⁻¹' Iic x = {ω | (S ω : WithTop ℝ≥0) ≤ ((x.toNNReal : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq, WithTop.coe_le_coe]
      rw [Real.le_toNNReal_iff_coe_le (not_lt.1 hx)]
    rw [e]
    exact (𝓕.le _) _ (hS _)

section Setup

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι : Type*} {n : ℕ}

/-- **The hypotheses of the stopped dual coupling** (§A.1.3): two independent ordinary curves (curve `1` = `√κ B₁`
from `0`, curve `2` = `√(16/κ) B₂ + x₂`) and finitely many protected enclosure pairs `(H₁ i, H₂ i)` (A14's
enclosure data: separation `2δ i`, a protected point `0 < q i < x₂`, protected injective marks `p m`), with exit times
`S₁ i`, `S₂ i ∈ (0, T]` (stopping times) up to which the hulls stay in the enclosures. -/
structure DualHyp (κ : ℝ) (P₁ : Measure Ω₁) (𝓕₁ : Filtration ℝ≥0 mΩ₁) (B₁ : ℝ≥0 → Ω₁ → ℝ) (P₂ : Measure Ω₂)
    (𝓕₂ : Filtration ℝ≥0 mΩ₂) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (H₁ H₂ : ι → Set ℂ) (δ q d : ι → ℝ)
    (p : Fin n → ℝ) (Tm : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) : Prop where
  κpos : 0 < κ
  bm₁ : IsFilteredBrownianReal 𝓕₁ B₁ P₁
  cont₁ : ∀ ω, Continuous (B₁ · ω)
  zero₁ : ∀ ω, B₁ 0 ω = 0
  bm₂ : IsFilteredBrownianReal 𝓕₂ B₂ P₂
  cont₂ : ∀ ω, Continuous (B₂ · ω)
  zero₂ : ∀ ω, B₂ 0 ω = 0
  hull₁ : ∀ i, IsHPHull (H₁ i)
  hull₂ : ∀ i, IsHPHull (H₂ i)
  δpos : ∀ i, 0 < δ i
  sep : ∀ i, ∀ a ∈ H₂ i, ∀ z ∈ H₁ i, 2 * δ i ≤ ‖a - z‖
  dpos : ∀ i, 0 < d i
  qpos : ∀ i, 0 < q i
  qH : ∀ i, Disjoint (Metric.ball (q i : ℂ) (2 * d i)) (H₁ i ∪ H₂ i)
  pH : ∀ i m, Disjoint (Metric.ball (p m : ℂ) (2 * d i)) (H₁ i ∪ H₂ i)
  pinj : Function.Injective p
  x₂H : ∀ i, ((x₂ : ℝ) : ℂ) ∈ closure (H₂ i)
  qx : ∀ i, q i < x₂
  Tmpos : 0 < Tm
  stop₁ : ∀ i, IsStoppingTime 𝓕₁ fun ω => (S₁ i ω : WithTop ℝ≥0)
  pos₁ : ∀ i ω, 0 < S₁ i ω
  le₁ : ∀ i ω, (S₁ i ω : ℝ) ≤ Tm
  K₁ : ∀ i ω, fwdHull (drive κ B₁ ω) (S₁ i ω) ⊆ H₁ i
  stop₂ : ∀ i, IsStoppingTime 𝓕₂ fun ω => (S₂ i ω : WithTop ℝ≥0)
  pos₂ : ∀ i ω, 0 < S₂ i ω
  le₂ : ∀ i ω, (S₂ i ω : ℝ) ≤ Tm
  K₂ : ∀ i ω, fwdHull (fun u => drive (16 / κ) B₂ ω u + x₂) (S₂ i ω) ⊆ H₂ i

variable {κ : ℝ} {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂}
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ}
  {Tm : ℝ} {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
include h

/-- The enclosure data of every pair of paths. -/
theorem twoEncl (ω₁ : Ω₁) (ω₂ : Ω₂) :
    TwoEncl (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
      (fun i => (S₂ i ω₂ : ℝ)) H₁ H₂ δ q d p Tm where
  cont₁ := QuantumZipper.drive_continuous (h.cont₁ ω₁)
  cont₂ := (QuantumZipper.drive_continuous (h.cont₂ ω₂)).add continuous_const
  zero₁ := QuantumZipper.drive_zero (h.zero₁ ω₁)
  hull₁ := h.hull₁
  hull₂ := h.hull₂
  δpos := h.δpos
  sep := h.sep
  dpos := h.dpos
  qpos := h.qpos
  qH := h.qH
  pH := h.pH
  pinj := h.pinj
  start₂ := fun i => by simpa [QuantumZipper.drive_zero (h.zero₂ ω₂)] using h.x₂H i
  qW := fun i => by simpa [QuantumZipper.drive_zero (h.zero₂ ω₂)] using h.qx i
  S₁pos := fun i => NNReal.coe_pos.2 (h.pos₁ i ω₁)
  S₂pos := fun i => NNReal.coe_pos.2 (h.pos₂ i ω₂)
  S₁le := fun i => h.le₁ i ω₁
  S₂le := fun i => h.le₂ i ω₂
  K₁ := fun i => h.K₁ i ω₁
  K₂ := fun i => h.K₂ i ω₂

theorem isProbabilityMeasure₁ : IsProbabilityMeasure P₁ := h.bm₁.isProbabilityMeasure'

theorem isProbabilityMeasure₂ : IsProbabilityMeasure P₂ := h.bm₂.isProbabilityMeasure'

theorem measurable_B₁ (r : ℝ≥0) : Measurable (B₁ r) := (h.bm₁.2.1 r).mono (𝓕₁.le r) le_rfl

theorem measurable_B₂ (r : ℝ≥0) : Measurable (B₂ r) := (h.bm₂.2.1 r).mono (𝓕₂.le r) le_rfl

/-- **The patched dual density is jointly measurable.** -/
theorem measurable_dualDens [Fintype ι] [Nonempty ι] (rr : Fin n → ℝ) :
    Measurable (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm) :=
  ZhanGT4.measurable_dualDens h.κpos h.cont₁ h.measurable_B₁ h.cont₂ h.measurable_B₂ h.zero₂
    (fun i => measurable_coe_of_isStoppingTime (h.stop₁ i)) (fun i => measurable_coe_of_isStoppingTime (h.stop₂ i))
    h.Tmpos.le (fun ω => h.twoEncl ω.1 ω.2) rr

end DualHyp

end Setup

/-! ### The marginal densities and the factorizations of the product density -/

section Marg

variable {Ω₁ Ω₂ : Type*} {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The curve-`1` marginal density** `m₁ = Ñ_s(max S₁ ∧ T, 0)/Ñ_s(0, 0)`: the canonical `s`-view at frozen height
`0` (curve `2` enters only through its start `x₂`, `sEll_zero_congr`). -/
def margDens₁ (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (Tm : ℝ)
    (ω₁ : Ω₁) : ℝ :=
  Real.exp (sEll κ rr (drive κ B₁ ω₁) (fun _ => x₂)
      (sSelA (drive κ B₁ ω₁) (fun _ => x₂) (fun i => (S₁ i ω₁ : ℝ)) fun _ => 0)
      (sSelW (drive κ B₁ ω₁) (fun _ => x₂) (fun i => (S₁ i ω₁ : ℝ)) fun _ => 0) p
      (min (maxIn (stairCols fun i => (S₁ i ω₁ : ℝ))) Tm) 0 -
    sEll κ rr (drive κ B₁ ω₁) (fun _ => x₂)
      (sSelA (drive κ B₁ ω₁) (fun _ => x₂) (fun i => (S₁ i ω₁ : ℝ)) fun _ => 0)
      (sSelW (drive κ B₁ ω₁) (fun _ => x₂) (fun i => (S₁ i ω₁ : ℝ)) fun _ => 0) p 0 0)

/-- **The curve-`2` marginal density** `m₂ = Ñ_t(0, max S₂ ∧ T)/Ñ_t(0, 0)`: the canonical `t`-view at curve-`1` height
`0` (curve `1` enters only through its start `0`, `tEll_zero_congr`). -/
def margDens₂ (κ : ℝ) (rr p : Fin n → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ)
    (ω₂ : Ω₂) : ℝ :=
  Real.exp (tEll κ rr (fun _ => 0) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (tSelA (fun _ => 0) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun _ => 0) fun i => (S₂ i ω₂ : ℝ))
      (tSelW (fun _ => 0) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun _ => 0) fun i => (S₂ i ω₂ : ℝ)) p 0
      (min (maxIn (stairCols fun i => (S₂ i ω₂ : ℝ))) Tm) -
    tEll κ rr (fun _ => 0) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (tSelA (fun _ => 0) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun _ => 0) fun i => (S₂ i ω₂ : ℝ))
      (tSelW (fun _ => 0) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun _ => 0) fun i => (S₂ i ω₂ : ℝ)) p 0 0)

/-- The (D11) patch of the canonical `s`-view normalised density of a pair of paths. -/
def dualPatch (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ :=
  patch (fun i => (S₁ i ω₁ : ℝ)) (fun i => (S₂ i ω₂ : ℝ))
    (fun x y => Real.exp (normLog (sEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (sSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ)))
      (sSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ))) p) x y)) Tm Tm

/-- The curve-`1` marginal factor of the product density, as a function of both paths. -/
def dualE₁ (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ :=
  Real.exp (sEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (sSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ)))
      (sSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ))) p (min (maxIn (stairCols fun i => (S₁ i ω₁ : ℝ))) Tm) 0 -
    sEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (sSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ)))
      (sSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ))) p 0 0)

/-- The curve-`2` marginal factor of the product density, as a function of both paths. -/
def dualE₂ (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) : ℝ :=
  Real.exp (tEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (tSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ)))
      (tSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ))) p 0 (min (maxIn (stairCols fun i => (S₂ i ω₂ : ℝ))) Tm) -
    tEll κ rr (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂)
      (tSelA (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ)))
      (tSelW (drive κ B₁ ω₁) (fun u => drive (16 / κ) B₂ ω₂ u + x₂) (fun i => (S₁ i ω₁ : ℝ))
        (fun i => (S₂ i ω₂ : ℝ))) p 0 0)

theorem dualDens_eq (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm (ω₁, ω₂) =
      dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
        dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ := rfl

theorem margDens₁_pos (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (Tm : ℝ)
    (ω₁ : Ω₁) : 0 < margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁ := Real.exp_pos _

theorem margDens₂_pos (κ : ℝ) (rr p : Fin n → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ)
    (ω₂ : Ω₂) : 0 < margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂ := Real.exp_pos _

theorem dualPatch_pos (κ : ℝ) (rr p : Fin n → ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ)
    (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    0 < dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ := Real.exp_pos _

/-- The largest column end is below a common bound of the columns. -/
theorem maxIn_stairCols_le {a : ι → ℝ} {T : ℝ} (hT : 0 ≤ T) (ha : ∀ i, a i ≤ T) : maxIn (stairCols a) ≤ T := by
  refine max'_le _ _ _ fun x hx => ?_
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact hT
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact ha i

variable {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {κ : ℝ} {P₁ : Measure Ω₁}
  {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂}
  {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ} {Tm : ℝ}
  {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
include h

/-- **The curve-`1` factor depends only on curve `1`.** -/
theorem dualE₁_eq (rr : Fin n → ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ = margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁ := by
  have hE := h.twoEncl ω₁ ω₂
  have h0 : drive (16 / κ) B₂ ω₂ 0 + x₂ = x₂ := by rw [QuantumZipper.drive_zero (h.zero₂ ω₂), zero_add]
  unfold dualE₁ margDens₁
  rw [sEll_zero_congr κ rr p (drive κ B₁ ω₁) hE.cont₂ continuous_const h0 _ (fun i => (hE.S₂pos i).le)
      (fun _ => le_rfl), sEll_zero_congr κ rr p (drive κ B₁ ω₁) hE.cont₂ continuous_const h0 _
      (fun i => (hE.S₂pos i).le) (fun _ => le_rfl)]

/-- **The curve-`2` factor depends only on curve `2`.** -/
theorem dualE₂_eq (rr : Fin n → ℝ) (ω₁ : Ω₁) (ω₂ : Ω₂) :
    dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ = margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂ := by
  have hE := h.twoEncl ω₁ ω₂
  unfold dualE₂ margDens₂
  rw [tEll_zero_congr κ rr p hE.cont₁ continuous_const hE.zero₁ _ (fun i => (hE.S₁pos i).le) (fun _ => le_rfl),
    tEll_zero_congr κ rr p hE.cont₁ continuous_const hE.zero₁ _ (fun i => (hE.S₁pos i).le) (fun _ => le_rfl)]

/-- **Inner integral over curve `2`** (curve `1` frozen): A15's `integral_patch_mul_tMarg_eq_one`. -/
theorem integral_dualPatch_mul_E₂ (rr : Fin n → ℝ) (ω₁ : Ω₁) :
    ∫ ω₂, dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ ∂P₂ = 1 :=
  integral_patch_mul_tMarg_eq_one h.κpos h.bm₂ h.cont₂ h.zero₂ h.hull₁ h.hull₂ h.δpos h.sep h.dpos h.qpos h.qH h.pH
    h.pinj h.Tmpos rr h.x₂H h.qx h.stop₂ h.pos₂ h.le₂ h.K₂ (QuantumZipper.drive_continuous (h.cont₁ ω₁))
    (QuantumZipper.drive_zero (h.zero₁ ω₁)) (fun i => NNReal.coe_pos.2 (h.pos₁ i ω₁)) (fun i => h.le₁ i ω₁)
    fun i => h.K₁ i ω₁

/-- **Inner integral over curve `1`** (curve `2` frozen): `integral_patch_mul_sMarg_eq_one`. -/
theorem integral_dualPatch_mul_E₁ (rr : Fin n → ℝ) (ω₂ : Ω₂) :
    ∫ ω₁, dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ ∂P₁ = 1 := by
  obtain ⟨ω₁⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  have hE := h.twoEncl ω₁ ω₂
  exact integral_patch_mul_sMarg_eq_one h.κpos h.bm₁ h.cont₁ h.zero₁ h.hull₁ h.hull₂ h.δpos h.sep h.dpos h.qpos
    h.qH h.pH h.pinj h.Tmpos rr h.stop₁ h.pos₁ h.le₁ h.K₁ hE.cont₂ hE.start₂ hE.qW hE.S₂pos hE.S₂le hE.K₂

/-- **The curve-`1` marginal density has mean one** (`integral_exp_sMarg_eq_one` for any frozen curve-`2` path). -/
theorem integral_margDens₁ (rr : Fin n → ℝ) : ∫ ω₁, margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁ ∂P₁ = 1 := by
  obtain ⟨ω₂⟩ := nonempty_of_isFilteredBrownianReal h.bm₂
  obtain ⟨ω₁⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  have hE := h.twoEncl ω₁ ω₂
  have h1 := integral_exp_sMarg_eq_one h.κpos h.bm₁ h.cont₁ h.zero₁ h.hull₁ h.hull₂ h.δpos h.sep h.dpos h.qpos
    h.qH h.pH h.pinj rr h.stop₁ h.pos₁ h.le₁ h.K₁ hE.cont₂ hE.start₂ hE.qW hE.S₂pos hE.S₂le hE.K₂
  rw [← h1]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hmin : min (maxIn (stairCols fun i => (S₁ i ω : ℝ))) Tm = maxIn (stairCols fun i => (S₁ i ω : ℝ)) :=
    min_eq_left (maxIn_stairCols_le h.Tmpos.le fun i => h.le₁ i ω)
  have := h.dualE₁_eq rr ω ω₂
  unfold dualE₁ at this
  rw [hmin] at this
  rw [← this]

end DualHyp

end Marg

/-! ### The stopped dual coupling -/

section Coupling

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι : Type*} [Fintype ι] {n : ℕ}

/-- **The stopped dual coupling** `D · (P₁ ⊗ P₂)` (§A.1.3–A.1.4), `D` the patched dual density `dualDens`. -/
def dualCoupling (κ : ℝ) (rr p : Fin n → ℝ) (P₁ : Measure Ω₁) (B₁ : ℝ≥0 → Ω₁ → ℝ) (P₂ : Measure Ω₂)
    (B₂ : ℝ≥0 → Ω₂ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (S₂ : ι → Ω₂ → ℝ≥0) (Tm : ℝ) : Measure (Ω₁ × Ω₂) :=
  (P₁.prod P₂).withDensity fun ω =>
    ENNReal.ofReal (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm ω)

variable {κ : ℝ} {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂}
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ}
  {Tm : ℝ} {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
include h

/-- **Fubini, curve `2` inside**: the mass of `D · (P₁ ⊗ P₂)` over `A × Ω₂` is the `m₁ · P₁`-mass of `A`. -/
theorem setLIntegral_dualDens_fst [Nonempty ι] (rr : Fin n → ℝ) (A : Set Ω₁) :
    ∫⁻ ω in A ×ˢ univ, ENNReal.ofReal
        (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm ω) ∂(P₁.prod P₂) =
      ∫⁻ ω₁ in A, ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁) ∂P₁ := by
  have := h.isProbabilityMeasure₁
  have := h.isProbabilityMeasure₂
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod _ (h.measurable_dualDens rr).ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun ω₁ => ?_
  have hint := h.integral_dualPatch_mul_E₂ rr ω₁
  have hi : Integrable (fun ω₂ => dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
      dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) P₂ :=
    Integrable.of_integral_ne_zero (by rw [hint]; exact one_ne_zero)
  have hnn : 0 ≤ᵐ[P₂] fun ω₂ => dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
      dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ :=
    Eventually.of_forall fun ω₂ => (mul_pos (dualPatch_pos _ _ _ _ _ _ _ _ _ _ _) (Real.exp_pos _)).le
  calc ∫⁻ ω₂, ENNReal.ofReal (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm
          (ω₁, ω₂)) ∂P₂
      = ∫⁻ ω₂, ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁) * ENNReal.ofReal
          (dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₂ := by
        refine lintegral_congr fun ω₂ => ?_
        rw [dualDens_eq, h.dualE₁_eq rr ω₁ ω₂, ← ENNReal.ofReal_mul (margDens₁_pos _ _ _ _ _ _ _ _).le]
        congr 1; ring
    _ = ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁) * ∫⁻ ω₂, ENNReal.ofReal
          (dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₂ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₂ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi hnn, hint, ENNReal.ofReal_one, mul_one]

/-- **Fubini, curve `1` inside**: the mass of `D · (P₁ ⊗ P₂)` over `Ω₁ × A` is the `m₂ · P₂`-mass of `A`. -/
theorem setLIntegral_dualDens_snd [Nonempty ι] (rr : Fin n → ℝ) (A : Set Ω₂) :
    ∫⁻ ω in univ ×ˢ A, ENNReal.ofReal
        (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm ω) ∂(P₁.prod P₂) =
      ∫⁻ ω₂ in A, ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) ∂P₂ := by
  have := h.isProbabilityMeasure₁
  have := h.isProbabilityMeasure₂
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod_symm _ (h.measurable_dualDens rr).ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun ω₂ => ?_
  have hint := h.integral_dualPatch_mul_E₁ rr ω₂
  have hi : Integrable (fun ω₁ => dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
      dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) P₁ :=
    Integrable.of_integral_ne_zero (by rw [hint]; exact one_ne_zero)
  have hnn : 0 ≤ᵐ[P₁] fun ω₁ => dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ *
      dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ :=
    Eventually.of_forall fun ω₁ => (mul_pos (dualPatch_pos _ _ _ _ _ _ _ _ _ _ _) (Real.exp_pos _)).le
  calc ∫⁻ ω₁, ENNReal.ofReal (dualDens κ rr p B₁ B₂ x₂ (fun i ω => (S₁ i ω : ℝ)) (fun i ω => (S₂ i ω : ℝ)) Tm
          (ω₁, ω₂)) ∂P₁
      = ∫⁻ ω₁, ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) * ENNReal.ofReal
          (dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₁ := by
        refine lintegral_congr fun ω₁ => ?_
        rw [dualDens_eq, h.dualE₂_eq rr ω₁ ω₂, ← ENNReal.ofReal_mul (margDens₂_pos _ _ _ _ _ _ _ _).le]
        congr 1; ring
    _ = ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) * ∫⁻ ω₁, ENNReal.ofReal
          (dualPatch κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂ * dualE₁ κ rr p B₁ B₂ x₂ S₁ S₂ Tm ω₁ ω₂) ∂P₁ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi hnn, hint, ENNReal.ofReal_one, mul_one]

/-- **The curve-`1` marginal of the stopped dual coupling is `m₁ · P₁`** (§A.1.3, "its marginals are unchanged"). -/
theorem map_fst_dualCoupling [Nonempty ι] (rr : Fin n → ℝ) :
    (dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm).map Prod.fst =
      P₁.withDensity fun ω₁ => ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω₁) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, dualCoupling, withDensity_apply _ (measurable_fst hA),
    withDensity_apply _ hA]
  have e : Prod.fst ⁻¹' A = A ×ˢ (univ : Set Ω₂) := by ext ω; simp
  rw [e]
  exact h.setLIntegral_dualDens_fst rr A

/-- **The curve-`2` marginal of the stopped dual coupling is `m₂ · P₂`.** -/
theorem map_snd_dualCoupling [Nonempty ι] (rr : Fin n → ℝ) :
    (dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm).map Prod.snd =
      P₂.withDensity fun ω₂ => ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω₂) := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA, dualCoupling, withDensity_apply _ (measurable_snd hA),
    withDensity_apply _ hA]
  have e : Prod.snd ⁻¹' A = (univ : Set Ω₁) ×ˢ A := by ext ω; simp
  rw [e]
  exact h.setLIntegral_dualDens_snd rr A

/-- **The stopped dual coupling is a probability measure** (§A.1.4: "`M*(∞, ∞)` is a positive probability
density"): its curve-`1` marginal `m₁ · P₁` has mass `E[m₁] = 1` (`integral_margDens₁`). -/
theorem isProbabilityMeasure_dualCoupling [Nonempty ι] (rr : Fin n → ℝ) :
    IsProbabilityMeasure (dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm) := by
  constructor
  have := h.isProbabilityMeasure₁
  have h1 : dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm univ =
      ((dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm).map Prod.fst) univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  have hint := h.integral_margDens₁ rr
  rw [h1, h.map_fst_dualCoupling rr, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero (by rw [hint]; exact one_ne_zero))
      (Eventually.of_forall fun _ => (margDens₁_pos _ _ _ _ _ _ _ _).le), hint, ENNReal.ofReal_one]

end DualHyp

end Coupling

end InteractingSLE.ZhanGT4
