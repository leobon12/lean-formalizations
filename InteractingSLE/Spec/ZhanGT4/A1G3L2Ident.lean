/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1GoodTime
import InteractingSLE.Spec.ZhanGT4.A1MargClock
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomLocal
import InteractingSLE.Spec.ZhanGT4.A1ForcesFam
import InteractingSLE.Spec.ZhanGT4.A1LargeDensSeed
import InteractingSLE.Spec.ZhanGT4.DualSeedEndCanonical

/-!
# Zhan's A.1 under R83: the canonical image is the seeded image chain of a stopped driver

Packet PROVE-A1-G3LAW2 (the identification step, generic: G3 and Eight, both directions). A.1's seeded records use
the image curve's driver **stopped at the rectangle exit** `S` (A1-EIGHTSEED's `eightDrv`), while the canonical image
processes (`A1Ref.imgDrv`, A1-FORCES's `canonForce`, A1-LARGEDENS's `canonSeed`) read the unstopped driver. The two
agree on `[0, S]`, which is all the canonical image reads below the clock of a good horizon. This file proves, at one
sample (deterministic, any image start `xj`):

* **`imgClk_imgDrv_eqOn_of_ownData`**: for an image chain `(a, W')` (`OwnData`, frame of the image curve) of a driver
  `W` agreeing with the image curve's driver `wj` on `[0, S]`, `S` good: the canonical clock is `a` on `[0, S]` and the
  canonical image driver is `W' + xj` on `[0, a(S)]`; **`ofReal_lt_imgLife_of_ownData`**: `a(S)` is strictly before
  the canonical image lifetime;
* **`seedCapacityDriver_eq_sub`**: the seeded capacity driver is `W' − W'(0)` up to the capacity horizon;
* **`isForwardSol_of_geometry_right`/`_left`**: a non-seed force point of a seeded image geometry is a real forward
  solution of the image driver;
* **`canonForce_eq_of_geometry_right`/`_left`**, **`canonSeed_eq_of_geometry_right`/`_left`**: the canonical
  forces of frozen-chart marks and the canonical seed forces are the geometry's force coordinates up to its horizon.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Core

/-! ### The canonical image driver and clock under a stopped driver -/

section Det

variable {xj xk τ S : ℝ} {wj wk W W' a : ℝ → ℝ} {ζj : ℝ≥0∞}

/-- **The canonical clock and image driver of the image curve are the image chain of any driver agreeing with it up to
a good horizon**: for `OwnData W (physHull (xk − xj) wk τ) (physMap (xk − xj) wk τ) S a W'` (the image curve's frame)
with `W = wj` on `[0, S]` and `S` good, the canonical clock is `a` on `[0, S]` and the canonical image driver is
`W' + xj` on `[0, a(S)]`. -/
theorem imgClk_imgDrv_eqOn_of_ownData
    (hown : OwnData W (physHull (xk - xj) wk τ) (physMap (xk - xj) wk τ) S a W') (hWj : EqOn W wj (Icc 0 S))
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
    (hgood : A1Ref.IsGoodTime xj wj ζj xk wk τ S) :
    EqOn (A1Ref.imgClk xj wj xk wk τ) a (Icc 0 S) ∧
      EqOn (A1Ref.imgDrv xj wj ζj xk wk τ) (fun σ => W' σ + xj) (Icc 0 (a S)) := by
  obtain ⟨hIs, hEq⟩ := isImgDrvOn_of_ownData hown
  obtain ⟨T₁, hST₁, hc₁⟩ := A1SeedGeom.exists_continuousOn_beyond_of_isGoodTime hj hgood
  have hWc : ContinuousOn W (Icc 0 T₁) := hown.cont.continuousOn
  have hkE : EqOn wk wk (Icc 0 τ) := fun _ _ => rfl
  have hclkW : ∀ t ∈ Icc (0 : ℝ) S, A1Ref.imgClk xj W xk wk τ t = a t := fun t ht => by
    rw [A1Marg.imgClk_sub]
    exact (hEq ht).symm
  have hclk : ∀ t ∈ Icc (0 : ℝ) S, A1Ref.imgClk xj wj xk wk τ t = a t := fun t ht => by
    rw [A1SeedGeom.imgClk_congr hτ hkE hc₁ hWc (ht.2.trans_lt hST₁)
      (hWj.symm.mono (Icc_subset_Icc_right ht.2)), hclkW t ht]
  have hhull : ∀ t ∈ Icc (0 : ℝ) S, physHull xj wj t = physHull xj W t := fun t ht =>
    A1SeedGeom.physHull_congr_of_continuousOn hc₁ hWc ht.1 (ht.2.trans_lt hST₁)
      (hWj.symm.mono (Icc_subset_Icc_right ht.2))
  have hadd := A1Marg.isImgDrvOn_add hIs
  have hIs' : A1Ref.IsImgDrvOn xj wj xk wk τ S (fun σ => W' σ + xj) := by
    refine ⟨hadd.1, hadd.2.1, fun t ht => ?_⟩
    rw [hclk t ht, hhull t ht, ← hclkW t ht]
    exact hadd.2.2 t ht
  refine ⟨fun t ht => hclk t ht, ?_⟩
  have he := A1Ref.imgDrv_eqOn hj hj0 hk hk0 hτ hgood hIs'
  rwa [hclk S ⟨hown.pos.le, le_rfl⟩] at he

/-- **The clock at the horizon is strictly before the canonical image lifetime.** -/
theorem ofReal_lt_imgLife_of_ownData
    (hown : OwnData W (physHull (xk - xj) wk τ) (physMap (xk - xj) wk τ) S a W') (hWj : EqOn W wj (Icc 0 S))
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
    (hgood : A1Ref.IsGoodTime xj wj ζj xk wk τ S) :
    ENNReal.ofReal (a S) < A1Ref.imgLife xj wj ζj xk wk τ := by
  have h := A1Forces.ofReal_imgClk_lt_imgLife hj hj0 hk hk0 hτ hgood
  rwa [(imgClk_imgDrv_eqOn_of_ownData hown hWj hj hj0 hk hk0 hτ hgood).1 ⟨hown.pos.le, le_rfl⟩] at h

/-- **The centred canonical image driver is the centred image chain driver** up to the clock of the horizon. -/
theorem imgDrv_sub_eq_of_ownData
    (hown : OwnData W (physHull (xk - xj) wk τ) (physMap (xk - xj) wk τ) S a W') (hWj : EqOn W wj (Icc 0 S))
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ)
    (hgood : A1Ref.IsGoodTime xj wj ζj xk wk τ S) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ a S) :
    A1Ref.imgDrv xj wj ζj xk wk τ t - A1Ref.imgDrv xj wj ζj xk wk τ 0 = W' t - W' 0 := by
  have h := (imgClk_imgDrv_eqOn_of_ownData hown hWj hj hj0 hk hk0 hτ hgood).2
  rw [h ⟨ht0, ht⟩, h ⟨le_rfl, ht0.trans ht⟩]
  ring

end Det

/-! ### The seeded capacity driver -/

section Seeded

variable {Ω : Type*} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0} {A : Ω → Set ℂ} {c : ℝ}

/-- **The seeded capacity driver is the centred image chain driver** up to the capacity horizon. -/
theorem seedCapacityDriver_eq_sub (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω)) (hc : 0 < c)
    (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r) (ω : Ω) {u : ℝ≥0}
    (hu : u ≤ seedCapacityHorizon d S ω) :
    seedCapacityDriver d S u ω = (d ω).W' u - (d ω).W' 0 := by
  have hr : (seedCapacityTime d S u ω : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
    ⟨(seedCapacityTime d S u ω).coe_nonneg, by exact_mod_cast min_le_right _ _⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨le_rfl, (S ω).coe_nonneg⟩
  have ha0 : 0 ≤ (d ω).a (S ω) := by
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn h0 ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  have hu' : (u : ℝ) ≤ (d ω).a (S ω) := by
    have := NNReal.coe_le_coe.2 hu
    rwa [seedCapacityHorizon, Real.coe_toNNReal _ ha0] at this
  have hcl := seedCapacityTime_clock_clamped hown hCc hCs hc hlb ω u
  have heA : (d ω).A 0 (seedCapacityTime d S u ω) =
      (d ω).W' ((d ω).a (seedCapacityTime d S u ω)) := (hown ω).frzA_zero hr
  have he0 : (d ω).A 0 0 = (d ω).W' ((d ω).a 0) := (hown ω).frzA_zero h0
  rw [seedCapacityDriver, heA, he0, (hown ω).a0, hcl, min_eq_left hu']

/-- The capacity horizon is the clock at the own horizon. -/
theorem coe_seedCapacityHorizon (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W') (ω : Ω) :
    (seedCapacityHorizon d S ω : ℝ) = (d ω).a (S ω) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨le_rfl, (S ω).coe_nonneg⟩
  have ha0 : 0 ≤ (d ω).a (S ω) := by
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn h0 ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  rw [seedCapacityHorizon, Real.coe_toNNReal _ ha0]

end Seeded

/-! ### Force points of a seeded image geometry are forward solutions -/

section Forward

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}

/-- The complex integral of the real force rate. -/
theorem integral_two_div_ofReal (f : ℝ → ℝ) (s : ℝ) :
    (∫ r in (0 : ℝ)..s, (2 : ℂ) / ((f r : ℝ) : ℂ)) = ((∫ r in (0 : ℝ)..s, 2 / f r : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun r _ => ?_
  push_cast
  rfl

/-- **A non-seed right force point of a seeded image geometry is a real forward solution of the image driver**: if the
geometry's driver is `W' − W'(0)` up to its horizon, `vR j − w` solves the centred forward flow of `W'` from the real
point `xR j + W'(0)`. -/
theorem isForwardSol_of_geometry_right (hgeo : SeedImageGeometry xL xR ρL ρR w vL vR T) (j : Fin nR)
    (hxj : xR j ≠ 0) {W' : ℝ → ℝ} (hw : ∀ s : ℝ≥0, s ≤ T → w s = W' s - W' 0) :
    IsForwardSol W' ((xR j + W' 0 : ℝ) : ℂ) T (fun s => ((vR j s.toNNReal - w s.toNNReal : ℝ) : ℂ)) := by
  refine ⟨(continuous_ofReal.comp (((hgeo.continuous_right j).comp continuous_real_toNNReal).sub
    (hgeo.continuous_w.comp continuous_real_toNNReal))).continuousOn, fun s hs => ⟨?_, ?_⟩⟩
  · rw [Ne, ofReal_eq_zero, sub_eq_zero]
    rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, Real.toNNReal_zero, hgeo.right_zero, hgeo.w_zero]
      exact hxj
    · exact (hgeo.right_gt s.toNNReal (Real.toNNReal_pos.2 hpos)
        (Real.toNNReal_le_iff_le_coe.2 hs.2) j).ne'
  · have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
    show ((vR j s.toNNReal - w s.toNNReal : ℝ) : ℂ) = _
    rw [integral_two_div_ofReal (fun r => vR j r.toNNReal - w r.toNNReal) s]
    have hf := hgeo.force_right s.toNNReal hsT j
    rw [Real.coe_toNNReal _ hs.1] at hf
    rw [hf, hw _ hsT, Real.coe_toNNReal _ hs.1]
    push_cast
    ring

/-- **A non-seed left force point of a seeded image geometry is a real forward solution of the image driver.** -/
theorem isForwardSol_of_geometry_left (hgeo : SeedImageGeometry xL xR ρL ρR w vL vR T) (i : Fin nL)
    (hxi : xL i ≠ 0) {W' : ℝ → ℝ} (hw : ∀ s : ℝ≥0, s ≤ T → w s = W' s - W' 0) :
    IsForwardSol W' ((xL i + W' 0 : ℝ) : ℂ) T (fun s => ((vL i s.toNNReal - w s.toNNReal : ℝ) : ℂ)) := by
  refine ⟨(continuous_ofReal.comp (((hgeo.continuous_left i).comp continuous_real_toNNReal).sub
    (hgeo.continuous_w.comp continuous_real_toNNReal))).continuousOn, fun s hs => ⟨?_, ?_⟩⟩
  · rw [Ne, ofReal_eq_zero, sub_eq_zero]
    rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, Real.toNNReal_zero, hgeo.left_zero, hgeo.w_zero]
      exact hxi
    · exact (hgeo.left_lt s.toNNReal (Real.toNNReal_pos.2 hpos)
        (Real.toNNReal_le_iff_le_coe.2 hs.2) i).ne
  · have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
    show ((vL i s.toNNReal - w s.toNNReal : ℝ) : ℂ) = _
    rw [integral_two_div_ofReal (fun r => vL i r.toNNReal - w r.toNNReal) s]
    have hf := hgeo.force_left s.toNNReal hsT i
    rw [Real.coe_toNNReal _ hs.1] at hf
    rw [hf, hw _ hsT, Real.coe_toNNReal _ hs.1]
    push_cast
    ring

end Forward

end InteractingSLE.ZhanGT4.A1G3L2
