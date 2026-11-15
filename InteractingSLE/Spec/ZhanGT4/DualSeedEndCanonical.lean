/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseCoords
import InteractingSLE.Spec.ZhanGT4.A1RefBridge

/-!
# Seeded capacity coordinates are the canonical rectangle coordinates

Packet PROVE-ZHAN-GT4-A22. Identify the inverse-clock driver with the
canonical image driver on the whole closed capacity interval, and with
its constant continuation beyond that interval. This uses the actual
`OwnData` bridge required by R72.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {n : ℕ} {d : Ω → SeedData n} {S : Ω → ℝ≥0}
  {A : Ω → Set ℂ} {c : ℝ}

/-- The clamped inverse clock covers the closed capacity interval exactly
and is constant after its endpoint. -/
theorem seedCapacityTime_clock_clamped
    (hown : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
    (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)
    (ω : Ω) (u : ℝ≥0) :
    (d ω).a (seedCapacityTime d S u ω) = min (u : ℝ) ((d ω).a (S ω)) := by
  have h0 : 0 ≤ (d ω).a (S ω) := by
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn ⟨le_rfl, (hown ω).pos.le⟩
      ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  by_cases hu : u ≤ seedCapacityHorizon d S ω
  · have hh := seedCapacityTime_spec hown hCc hCs hc hlb ω hu
    have hu' : (u : ℝ) ≤ (d ω).a (S ω) := by
      have := NNReal.coe_le_coe.2 hu
      simpa only [seedCapacityHorizon, Real.coe_toNNReal _ h0] using this
    rw [hh.2, min_eq_left hu']
  · have hu' : (d ω).a (S ω) ≤ (u : ℝ) := by
      have := NNReal.coe_le_coe.2 (le_of_not_ge hu)
      simpa only [seedCapacityHorizon, Real.coe_toNNReal _ h0] using this
    have hval := (invClock_eq_coe hCc (seedQuadClock_zero _) hc hlb u ω).2.1
    have hs : S ω ≤ invClockT (seedQuadClock (seedCapacityCoeff d S)) u ω :=
      (hCs ω).le_iff_le.1
        ((seedCapacityCoeff_clock_eq hown ω le_rfl).trans_le (hu'.trans_eq hval.symm))
    rw [seedCapacityTime, min_eq_right hs, min_eq_right hu']

/-- The seeded capacity driver used in the image law is the centered
canonical image driver, stopped at the rectangle's capacity horizon. -/
theorem seedCapacityDriver_eq_canonical
    {wk : Ω → ℝ → ℝ} {ζ : Ω → ℝ≥0∞} {xk τ : Ω → ℝ}
    (hown : ∀ ω, OwnData (d ω).W (A2X.physHull (xk ω) (wk ω) (τ ω))
      (d ω).φ (S ω) (d ω).a (d ω).W')
    (hφ : ∀ ω, (d ω).φ = A2X.physMap (xk ω) (wk ω) (τ ω))
    (hj : ∀ ω T, ENNReal.ofReal T < ζ ω → ContinuousOn (d ω).W (Icc 0 T))
    (hk : ∀ ω, ∃ τ', τ ω < τ' ∧ ContinuousOn (wk ω) (Icc 0 τ'))
    (hk0 : ∀ ω, wk ω 0 = 0) (hτ : ∀ ω, 0 ≤ τ ω)
    (hgood : ∀ ω, A1Ref.IsGoodTime 0 (d ω).W (ζ ω) (xk ω) (wk ω) (τ ω) (S ω))
    (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff d S) ω))
    (hCs : ∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff d S) ω))
    (hc : 0 < c) (hlb : ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff d S) ω r)
    (ω : Ω) (u : ℝ≥0) :
    seedCapacityDriver d S u ω =
      A1Ref.imgDrv 0 (d ω).W (ζ ω) (xk ω) (wk ω) (τ ω)
        (min (u : ℝ) ((d ω).a (S ω))) -
      A1Ref.imgDrv 0 (d ω).W (ζ ω) (xk ω) (wk ω) (τ ω) 0 := by
  have hgeo : OwnData (d ω).W (A2X.physHull (xk ω) (wk ω) (τ ω))
      (A2X.physMap (xk ω) (wk ω) (τ ω)) (S ω) (d ω).a (d ω).W' := by
    simpa only [hφ ω] using hown ω
  have he := A1Ref.imgDrv_eqOn_of_ownData (hj ω) (hown ω).zero
    (hk ω) (hk0 ω) (hτ ω) (hgood ω) hgeo
  have hr : (seedCapacityTime d S u ω : ℝ) ∈ Icc (0 : ℝ) (S ω) :=
    ⟨(seedCapacityTime d S u ω).coe_nonneg, by exact_mod_cast min_le_right _ _⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (S ω) := ⟨le_rfl, (S ω).coe_nonneg⟩
  have ha0 : 0 ≤ (d ω).a (S ω) := by
    rw [← (hown ω).a0]
    exact (hown ω).mono.monotoneOn h0 ⟨(S ω).coe_nonneg, le_rfl⟩ (S ω).coe_nonneg
  have hcl := seedCapacityTime_clock_clamped hown hCc hCs hc hlb ω u
  have heA : (d ω).A 0 (seedCapacityTime d S u ω) =
      (d ω).W' ((d ω).a (seedCapacityTime d S u ω)) := (hown ω).frzA_zero hr
  have he0 : (d ω).A 0 0 = (d ω).W' ((d ω).a 0) := (hown ω).frzA_zero h0
  rw [seedCapacityDriver, heA, he0, (hown ω).a0, hcl,
    he ⟨le_min u.coe_nonneg ha0, min_le_right _ _⟩, he ⟨le_rfl, ha0⟩]

end InteractingSLE.ZhanGT4
