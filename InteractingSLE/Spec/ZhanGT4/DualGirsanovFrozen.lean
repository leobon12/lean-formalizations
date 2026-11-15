/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualGirsanovQ
import InteractingSLE.Spec.ZhanGT4.D9Const
import InteractingSLE.Spec.ZhanGT4.MTildeMartFrozen

/-!
# Girsanov with the other curve frozen, IV: the protected rectangle

Packet PROVE-ZHAN-GT4-A9. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L351, R38):
"(D9) … The positive density `M(S₁, S₂)` … By (D8) and Girsanov, with the other curve stopped, the new drift of `W_j`
is `κ_j q_j = ((6 − κ_j)/2) A_{j,2}/A_{j,1} − (κ_j/2) A_{j,1}/E_{j,0} + Σ ρ_{j,m} A_{j,1}/E_{j,m}`."

* `exists_frzMartHyp`: for separated enclosures, a protected point and protected marks, and a time bound, there are
  constants `r, a₀, γ, Γ, λ, L` such that every configuration — ordinary `SLE_κ` (`W = √κB`) growing in `H₁` up to
  `T ≤ Tm`, the other curve frozen with hull in `H₂` at a time `0 < t₂ ≤ Tm` — satisfies the hypotheses `FrzMartHyp`
  of PROVE-ZHAN-GT4-A8's stopped martingale (with `D9Const` from `exists_twoCurveD9`, `ScaleOK` from `exists_scaleOK`).
* **`FrzMartHyp.isFilteredBrownianReal_girs`**: under `Q = (M̃_S/M̃_0) · P` the process
  `X = B − ∫₀^{·∧S} √κ ∂_xℓ(u, W_u) du` is a Brownian motion of `𝓕` (`IsDriverLogField.isFilteredBrownianReal_girsProcess`
  for `ℓ = log M̃`, `isDriverLogField_frozen`); hence `W = √κ X + ∫ κ ∂_xℓ(u, W_u) du`.
* `FrzData.LSX_driver_eq_dualQ`: at the driver `∂_xℓ = q_j` of (D7), so the new drift is `κ q_j`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-- **At the driver, `∂_x log M̃` is the noise coefficient `q_j` of (D7)**: `α A_{j,2}/A_{j,1} − A_{j,1}/(2E_{j,0}) +
Σ r_{j,m} A_{j,1}/E_{j,m}`, `E_{j,0} = A_{j,0} − A_{k,0}`, `E_{j,m} = A_{j,0} − B_{m,0}`. -/
theorem FrzData.LSX_driver_eq_dualQ {n : ℕ} (d : FrzData n) (t : ℝ) :
    d.LSX t (d.W t) = dualQ d.κ (d.A 1 t) (d.A 2 t) (d.A 0 t - d.A20 t) d.r (fun m => d.A 0 t - d.B0 t m) := by
  have h2 : ∀ x y : ℝ, x / (2 * y) = 1 / 2 * (x / y) := fun x y => by rw [div_mul_eq_div_div]; ring
  unfold FrzData.LSX dualLogSpaceX dualQ
  rw [h2]
  rfl

/-- **(D10) at the driver** (§A.1.3, "Apply (D3) to the mapped driver `A_{j,0}`. Its `A_{j,2}`-drift cancels"): with
(D2) `∂_tF(W) = −3A_{j,2}`, `F''(W) = A_{j,2}` and the Girsanov drift `κ q_j` of the driver, the drift of the mapped
driver `A_{j,0} = F_t(W_t)` is `−3A₂ + (κ/2)A₂ + κ q_j A₁ = A₁²(−κ/(2E_{j,0}) + Σ ρ_{j,m}/E_{j,m})`, `ρ_{j,m} = κ r_{j,m}`. -/
theorem dualD10_drift {κ A1 A2 E0 : ℝ} {n : ℕ} (r E : Fin n → ℝ) (hκ : κ ≠ 0) (hA1 : A1 ≠ 0) :
    -3 * A2 + κ / 2 * A2 + κ * dualQ κ A1 A2 E0 r E * A1 = A1 ^ 2 * (-(κ / (2 * E0)) + ∑ m, κ * r m / E m) := by
  unfold dualQ dualAlpha
  have e1 : κ * ((6 - κ) / (2 * κ) * (A2 / A1)) * A1 = (6 - κ) / 2 * A2 := by field_simp
  have hsum : κ * (∑ m, r m * (A1 / E m)) * A1 = A1 ^ 2 * ∑ m, κ * r m / E m := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  linear_combination e1 + hsum

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The hypotheses of the frozen-curve martingale from the enclosure data** (§A.1.3). -/
theorem exists_frzMartHyp {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsepδ : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) {q d : ℝ} (hd : 0 < d) (hq : 0 < q)
    (hqH : Disjoint (Metric.ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) {n : ℕ} {p : Fin n → ℝ}
    (hpH : ∀ m, Disjoint (Metric.ball (p m : ℂ) (2 * d)) (H₁ ∪ H₂)) (hpinj : Function.Injective p) (Tm : ℝ) :
    ∃ r a₀ γ Γ lam L : ℝ, ∀ [Nonempty Ω] (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (rr : Fin n → ℝ)
      (W₂ : ℝ → ℝ) (t₂ : ℝ) (S : Ω → ℝ≥0) (T : Ω → ℝ),
      (∀ ω, OwnData (drive κ B ω) (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (a ω) (W' ω)) →
      (∀ ω, (S ω : ℝ) ≤ T ω) → (∀ ω, T ω ≤ Tm) → (∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ H₁) →
      Continuous W₂ → ((W₂ 0 : ℝ) : ℂ) ∈ closure H₂ → q < W₂ 0 → 0 < t₂ → t₂ ≤ Tm → fwdHull W₂ t₂ ⊆ H₂ →
      FrzMartHyp κ B W' a (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) rr (W₂ t₂)
        (fun m => (fwdMap W₂ t₂ (p m)).re + W₂ t₂) S T r a₀ γ Γ lam L Tm := by
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha₀, hγ, hmain⟩ := exists_twoCurveD9 hH₁ hH₂ hδ hsepδ hd hq hqH hpH hpinj Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha₀ hγ Γ lam Tm
  refine ⟨r, a₀, γ, Γ, lam, L, fun κ B W' a rr W₂ t₂ S T hown hST hTm hK₁ hW₂ hW₂H hqW ht₂ ht₂m hK₂ => ?_⟩
  have hD := fun ω => hmain (drive κ B ω) W₂ t₂ (T ω) (a ω) (W' ω) κ rr (hown ω) hW₂ hW₂H hqW ht₂ ht₂m (hTm ω)
    (hK₁ ω) hK₂
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  exact ⟨hown, hST, hTm, fun ω => (hD ω).alive₀, fun ω m => (hD ω).alive m, (hD ω₀).ne, (hD ω₀).inj,
    fun ω => (hD ω).d9, hL⟩

namespace FrzMartHyp

variable {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ}
  {rr : Fin n → ℝ} {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}

/-- **Girsanov with the other curve frozen** (§A.1.3, (D8)): for ordinary `SLE_κ` (`W = √κB`) with the other curve
frozen and the (D9) hypotheses up to the stopping time `S` (`FrzMartHyp`), under `Q = (M̃_S/M̃_0) · P` the process
`X = B − ∫₀^{·∧S} √κ ∂_xℓ(u, W_u) du` (`ℓ = log M̃`) is a Brownian motion of `𝓕`. By `FrzData.LSX_driver_eq_dualQ`
the driver `W = √κ X + ∫₀^{·∧S} κ q_j du` acquires the drift `κ q_j`. -/
theorem isFilteredBrownianReal_girs {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hκ : 0 < κ) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hH : FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax) :
    IsFilteredBrownianReal 𝓕 (girsProcess (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX)
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hDL := isDriverLogField_frozen hκ hBm hBc hS hH
  have hSR : ∀ ω, S ω ≤ Tmax.toNNReal := fun ω => by
    rw [← Real.toNNReal_coe (r := S ω)]
    exact Real.toNNReal_le_toNNReal ((hH.le ω).trans (hH.leMax ω))
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  exact hDL.isFilteredBrownianReal_girsProcess hB hBc (Real.sqrt_pos.2 hκ) (hH.cutRad_pos ω₀) hS hSR

end FrzMartHyp

end InteractingSLE.ZhanGT4
