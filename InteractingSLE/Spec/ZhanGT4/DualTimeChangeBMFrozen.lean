/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTimeChangeBM

/-!
# (D10), V: the image driver is driven by a Brownian motion of the capacity time

Packet PROVE-ZHAN-GT4-A10. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L341–L355, R38):
(D10), "The time change `du = A²_{j,1} dt_j`, Lévy's characterization, …".

With the other curve frozen and the (D9) hypotheses up to `S` (`FrzD10Hyp`), under `Q = (M̃_S/M̃_0) · P`:

* the full clock `C'_t = a(t∧S) + (t − t∧S)` (`bmClk`) is continuous, strictly increasing, adapted, `C'_t ≥ min(a₀², 1) t`;
* the spliced noise `Y_t = (A_{j,0}(t∧S) − A_{j,0}(0) − J_{t∧S})/√κ + (B_t − B_{t∧S})` (`bmY`) has
  `exp(νY_t − ν²C'_t/2)` a `Q`-martingale for every `ν` (**`FrzD10Hyp.martingale_bmExp`**: up to `S` this is (D10), after
  `S` the Wald exponential of `B`; spliced by `setIntegral_mul_wald_eq_of_stopped` under `P` and Bayes' formula);
* hence (**`FrzD10Hyp.isFilteredBrownianReal_bm`**, `isFilteredBrownianReal_timeChange`) `B̂_u = Y_{C'⁻¹(u)}` is a
  `Q`-Brownian motion of the time-changed filtration, and for `u ≤ a(S)`
  `√κ B̂_u = W'(u) − W'(0) − ∫₀ᵘ (−κ/(2(W' − Ṽ₀)) + Σ ρ_m/(W' − Ṽ_m))` (**`FrzD10Hyp.bmY_invClockT_eq`**): the image
  driver solves the force-point equation driven by `B̂` up to `a(S)`.

The bound `|B| ≤ N_B` on `[0, S]` used to splice is `abs_B_le_of_hull` (the hull stays in a disc).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

section Frozen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The full capacity clock** `C'_t = a(t∧S) + (t − t∧S)`. -/
def bmClk (a : Ω → ℝ → ℝ) (S : Ω → ℝ≥0) (ω : Ω) (t : ℝ≥0) : ℝ :=
  a ω ((min t (S ω) : ℝ≥0) : ℝ) + ((t : ℝ) - ((min t (S ω) : ℝ≥0) : ℝ))

/-- **The spliced noise** `Y_t = (A_{j,0}(t∧S) − A_{j,0}(0) − J_{t∧S})/√κ + (B_t − B_{t∧S})`. -/
def bmY {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (φ : ℂ → ℂ) (rr : Fin n → ℝ) (ζ₀ : ℝ)
    (ζ : Fin n → ℝ) (S : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (W' ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)) - W' ω 0 -
    ∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ), (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u) / Real.sqrt κ +
    (B t ω - B (min t (S ω)) ω)

/-- The driver of ordinary `SLE_κ` is bounded by `7R/√κ` while its hull stays in `B̄(0, R)`. -/
theorem abs_B_le_of_hull {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous (B · ω)) {T : Ω → ℝ}
    {R : ℝ} (hR : 0 < R) (hK : ∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ Metric.closedBall (0 : ℂ) R)
    (hB0 : ∀ ω, B 0 ω = 0) (ω : Ω) (r : ℝ≥0) (hr : (r : ℝ) ≤ T ω) : |B r ω| ≤ 7 * R / Real.sqrt κ := by
  have hW : Continuous (drive κ B ω) := continuous_const.mul ((hBc ω).comp continuous_real_toNNReal)
  have hK' : fwdHull (drive κ B ω) (T ω) ⊆ Metric.closedBall ((0 : ℝ) : ℂ) R := by
    rw [Complex.ofReal_zero]; exact hK ω
  have hW0 : |drive κ B ω 0 - 0| ≤ R := by
    simp only [drive, Real.toNNReal_zero, hB0, mul_zero, sub_zero, abs_zero]; exact hR.le
  have h := abs_driver_sub_le hW (r.coe_nonneg.trans hr) hR hK' hW0 ⟨r.coe_nonneg, hr⟩
  simp only [drive, Real.toNNReal_coe, sub_zero, abs_mul, abs_of_pos (Real.sqrt_pos.2 hκ)] at h
  rw [le_div_iff₀ (Real.sqrt_pos.2 hκ)]
  linarith

/-- **The exponential of the spliced noise** `exp(νY_t − ν²C'_t/2)`. -/
def bmExp {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (φ : ℂ → ℂ) (rr : Fin n → ℝ) (ζ₀ : ℝ)
    (ζ : Fin n → ℝ) (S : Ω → ℝ≥0) (ν : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (ν * bmY κ B W' a φ rr ζ₀ ζ S t ω - ν ^ 2 * bmClk a S ω t / 2)

/-- `t ∧ S` is adapted (`= ∫₀ᵗ 1_{· < S}`). -/
theorem measurable_min_S {𝓕 : Filtration ℝ≥0 mΩ} {S : Ω → ℝ≥0} (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (rT : ℝ≥0) : Measurable[𝓕 rT] fun ω => ((min rT (S ω) : ℝ≥0) : ℝ) := by
  have hgc : ∀ ω, ContinuousOn ((fun _ _ => (1 : ℝ)) ω) (Icc 0 (S ω : ℝ)) := fun _ => continuousOn_const
  have hgm : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => (fun (_ : Ω) (_ : ℝ) => (1 : ℝ)) ω r) :=
    fun r => measurable_const.indicator (measurableSet_ge_of_isStoppingTime hS r)
  have h2 := measurable_cutInt (g := fun _ _ => (1 : ℝ)) hgc hS hgm rT
  have e : (fun ω => cutInt S (fun _ _ => (1 : ℝ)) ω rT) = fun ω => ((min rT (S ω) : ℝ≥0) : ℝ) := by
    funext ω
    rw [cutInt_eq_min hgc ω rT, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rwa [e] at h2

/-- A continuous adapted process stopped at `t ∧ S` is `𝓕_t`-measurable. -/
theorem measurable_stopped_min {𝓕 : Filtration ℝ≥0 mΩ} {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {X : ℝ≥0 → Ω → ℝ} (hXm : ∀ u, Measurable[𝓕 u] (X u))
    (hXc : ∀ ω, Continuous (X · ω)) (t : ℝ≥0) : Measurable[𝓕 t] fun ω => X (min t (S ω)) ω := by
  have hτ : IsStoppingTime 𝓕 fun ω => ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0) := by
    simpa only [WithTop.coe_min] using (isStoppingTime_const 𝓕 t).min hS
  have hXp : IsStronglyProgressive 𝓕 X :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun u => (hXm u).stronglyMeasurable) hXc
  have h := measurable_stoppedValue hXp hτ
  have e : stoppedValue X (fun ω => ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0)) = fun ω => X (min t (S ω)) ω := by
    funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
  rw [e] at h
  exact h.mono (hτ.measurableSpace_le_of_le_const fun ω => WithTop.coe_le_coe.2 (min_le_left _ _)) le_rfl

/-- **The `P`-martingale step of `exp(ℓ + ψ)` normalized at time `0`**: for driver log-fields `ℓ` and `ℓ + ψ` up to `S`,
`∫_A e^{(ℓ+ψ)(t∧S)} e^{−ℓ(0)} dP` does not depend on `t ≥ s` for `A ∈ 𝓕_s`. -/
theorem IsDriverLogField.setIntegral_mul_exp_neg_eq {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K K' : ℝ} {B : ℝ≥0 → Ω → ℝ}
    {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt ψ ℓx' ℓxx' ℓxxx' ℓt' : Ω → ℝ → ℝ → ℝ}
    (hL : IsDriverLogField 𝓕 σ ρ K B S ℓ ℓx ℓxx ℓxxx ℓt)
    (hL' : IsDriverLogField 𝓕 σ ρ K' B S (fun ω t x => ℓ ω t x + ψ ω t x) ℓx' ℓxx' ℓxxx' ℓt') {P : Measure Ω}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω * Real.exp (-ℓ ω 0 (σ * B 0 ω)) ∂P =
      ∫ ω in A, logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min s (S ω)) ω * Real.exp (-ℓ ω 0 (σ * B 0 ω)) ∂P := by
  have hP := hB.isProbabilityMeasure'
  have hAm : MeasurableSet A := 𝓕.le s A hA
  have hℓ0m : Measurable[𝓕 s] fun ω => ℓ ω 0 (σ * B 0 ω) := by
    have h := hL.meas0 0
    have e : {ω | (0 : ℝ≥0) ≤ S ω}.indicator (fun ω => ℓ ω ((0 : ℝ≥0) : ℝ) (σ * B 0 ω)) =
        fun ω => ℓ ω 0 (σ * B 0 ω) := by
      funext ω; rw [indicator_of_mem (by simp : ω ∈ {ω | (0 : ℝ≥0) ≤ S ω})]; rfl
    rw [e] at h
    exact h.mono (𝓕.mono zero_le) le_rfl
  have hℓ0b : ∀ ω, |ℓ ω 0 (σ * B 0 ω)| ≤ K := fun ω => by
    have h := hL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩
    simpa only [Real.toNNReal_zero] using h
  set ξ : Ω → ℝ := A.indicator fun ω => Real.exp (-ℓ ω 0 (σ * B 0 ω) - K) with hξ
  have hξm : Measurable[𝓕 s] ξ :=
    (Real.continuous_exp.measurable.comp (hℓ0m.neg.sub_const K)).indicator hA
  have hξb : ∀ ω, |ξ ω| ≤ 1 := fun ω => by
    by_cases hω : ω ∈ A
    · rw [hξ, indicator_of_mem hω, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.2
      linarith [(_root_.abs_le.1 (hℓ0b ω)).1]
    · rw [hξ, indicator_of_notMem hω, abs_zero]; exact zero_le_one
  have hM'm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω =>
      logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min u (S ω)) ω := fun u =>
    hL'.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) u
  have hint : ∀ u : ℝ≥0, Integrable (fun ω => ξ ω *
      logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min u (S ω)) ω) P := fun u =>
    ((integrable_const (Real.exp K')).mono' ((hM'm u).mono (𝓕.le u) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hL'.abs_logFieldExp_le hρ (min_le_right _ _))).bdd_mul
      ((hξm.mono (𝓕.le s) le_rfl).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
  have key : ∀ u : ℝ≥0, ∫ ω in A, logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min u (S ω)) ω *
      Real.exp (-ℓ ω 0 (σ * B 0 ω)) ∂P =
      Real.exp K * ∫ ω, ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min u (S ω)) ω ∂P := fun u => by
    rw [← integral_indicator hAm, ← integral_const_mul]
    congr 1; funext ω
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, hξ, indicator_of_mem hω, Real.exp_sub]
      have hK : Real.exp K ≠ 0 := (Real.exp_pos K).ne'
      field_simp
    · rw [indicator_of_notMem hω, hξ, indicator_of_notMem hω]; ring
  have h0 := hL'.integral_mul_logField_stopped_sub_eq_zero hB hBc hσ hρ hS hst hξm hξb
  rw [key t, key s]
  congr 1
  have hsub : (fun ω => ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω -
      ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min s (S ω)) ω) =
      fun ω => ξ ω * (logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω -
        logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min s (S ω)) ω) := by
    funext ω; ring
  have h1 : (∫ ω, ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min t (S ω)) ω ∂P) -
      ∫ ω, ξ ω * logFieldExp σ B (fun ω t x => ℓ ω t x + ψ ω t x) (min s (S ω)) ω ∂P = 0 := by
    rw [← integral_sub (hint t) (hint s), hsub]; exact h0
  linarith

/-- **The bounded factor of the splice** `R_u = e^{(ℓ+ψ)(u∧S)} e^{−ℓ(0)} / E_{u∧S}` (`E = wald ν B`). -/
def bmR {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (φ : ℂ → ℂ) (rr : Fin n → ℝ) (ζ₀ : ℝ)
    (ζ : Fin n → ℝ) (S : Ω → ℝ≥0) (ν : ℝ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  logFieldExp (Real.sqrt κ) B (fun ω t x => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell t x +
      d10Psi κ B W' a φ rr ζ₀ ζ ν S ω t x) (min u (S ω)) ω *
    Real.exp (-(frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell 0 (Real.sqrt κ * B 0 ω)) / wald ν B (min u (S ω)) ω

namespace FrzD10Hyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

theorem bmClk_zero (ω : Ω) : bmClk a S ω 0 = 0 := by
  simp only [bmClk, zero_le, min_eq_left, NNReal.coe_zero, sub_self, add_zero]
  exact (hH.own ω).a0

theorem continuous_bmClk (ω : Ω) : Continuous (bmClk a S ω) :=
  (hH.continuous_imgClk ω).add (NNReal.continuous_coe.sub
    (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))

theorem strictMono_bmClk (ω : Ω) : StrictMono (bmClk a S ω) := by
  intro t t' htt'
  have hmo := (hH.own ω).mono
  have hSm : (S ω : ℝ) ∈ Icc (0 : ℝ) (T ω) := ⟨(S ω).coe_nonneg, hH.le ω⟩
  have htt'r : (t : ℝ) < t' := htt'
  unfold bmClk
  rcases le_or_gt t' (S ω) with h' | h'
  · have ht : t ≤ S ω := htt'.le.trans h'
    rw [min_eq_left ht, min_eq_left h', sub_self, sub_self, add_zero, add_zero]
    exact hmo ⟨t.coe_nonneg, (NNReal.coe_le_coe.2 ht).trans (hH.le ω)⟩
      ⟨t'.coe_nonneg, (NNReal.coe_le_coe.2 h').trans (hH.le ω)⟩ htt'r
  · rw [min_eq_right h'.le]
    have hS' : (S ω : ℝ) < t' := h'
    rcases le_or_gt t (S ω) with h | h
    · rw [min_eq_left h, sub_self, add_zero]
      have := hmo.monotoneOn ⟨t.coe_nonneg, (NNReal.coe_le_coe.2 h).trans (hH.le ω)⟩ hSm (NNReal.coe_le_coe.2 h)
      linarith
    · rw [min_eq_right h.le]
      linarith

/-- `a(τ) ≥ a₀² τ` on `[0, T]` (`A_{j,1} ≥ a₀`). -/
theorem le_a (ω : Ω) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (T ω)) : a₀ ^ 2 * τ ≤ a ω τ := by
  rw [← (hH.own ω).integral_frzA_one_sq hτ]
  have hc := ((((hH.own ω).continuousOn_frzA 1).pow 2).mono (Icc_subset_Icc_right hτ.2))
  have h := intervalIntegral.integral_mono_on hτ.1 (μ := volume) (f := fun _ => a₀ ^ 2)
    (g := fun u => frzA (drive κ B ω) (W' ω) (a ω) φ 1 u ^ 2) intervalIntegrable_const
    (hc.intervalIntegrable_of_Icc hτ.1) fun u hu => by
      obtain ⟨h1, -, -, -⟩ := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).driver_bounds (hH.own ω) (hH.d9 ω)
        ⟨hu.1, hu.2.trans hτ.2⟩
      have ha := (hH.d9 ω).a0
      change a₀ ^ 2 ≤ (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 1 u ^ 2
      nlinarith
  simpa [intervalIntegral.integral_const, mul_comm] using h

/-- **Linear growth of the full clock**: `C'_r ≥ min(a₀², 1) r`. -/
theorem le_bmClk (ω : Ω) (t : ℝ≥0) : min (a₀ ^ 2) 1 * (t : ℝ) ≤ bmClk a S ω t := by
  have hm := hH.mem_Icc_min t ω
  have h1 := hH.le_a ω hm
  have hc1 : min (a₀ ^ 2) 1 ≤ a₀ ^ 2 := min_le_left _ _
  have hc2 : min (a₀ ^ 2) 1 ≤ 1 := min_le_right _ _
  have hc0 : 0 ≤ min (a₀ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
  have hmt : ((min t (S ω) : ℝ≥0) : ℝ) ≤ t := NNReal.coe_le_coe.2 (min_le_left _ _)
  unfold bmClk
  nlinarith [mul_le_mul_of_nonneg_right hc1 hm.1, mul_le_mul_of_nonneg_right hc2 (sub_nonneg.2 hmt)]

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- The full clock is adapted. -/
theorem measurable_bmClk (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (rT : ℝ≥0) :
    Measurable[𝓕 rT] fun ω => bmClk a S ω rT := by
  have h1 := hH.measurable_imgClk hBm hBc hS rT
  have hgc : ∀ ω, ContinuousOn ((fun _ _ => (1 : ℝ)) ω) (Icc 0 (S ω : ℝ)) := fun _ => continuousOn_const
  have hgm : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => (fun (_ : Ω) (_ : ℝ) => (1 : ℝ)) ω r) :=
    fun r => measurable_const.indicator (measurableSet_ge_of_isStoppingTime hS r)
  have h2 := measurable_cutInt (g := fun _ _ => (1 : ℝ)) hgc hS hgm rT
  have e : (fun ω => cutInt S (fun _ _ => (1 : ℝ)) ω rT) = fun ω => ((min rT (S ω) : ℝ≥0) : ℝ) := by
    funext ω
    rw [cutInt_eq_min hgc ω rT, intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  rw [e] at h2
  have e2 : (fun ω => bmClk a S ω rT) = fun ω => imgClk a S ω rT + ((rT : ℝ) - ((min rT (S ω) : ℝ≥0) : ℝ)) :=
    rfl
  rw [e2]
  exact h1.add (measurable_const.sub h2)

theorem bmY_zero (ω : Ω) : bmY κ B W' a φ rr ζ₀ ζ S 0 ω = 0 := by
  simp only [bmY, zero_le, min_eq_left, NNReal.coe_zero, (hH.own ω).a0, sub_self,
    intervalIntegral.integral_same, zero_div, add_zero]

theorem continuous_bmY (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    Continuous fun t => bmY κ B W' a φ rr ζ₀ ζ S t ω := by
  have hT0 := (hH.own ω).pos.le
  have hm : Continuous fun t : ℝ≥0 => ((min t (S ω) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hW'a : ContinuousOn (fun τ => W' ω (a ω τ)) (Icc 0 (T ω)) :=
    (hH.own ω).contW'.comp_continuousOn (hH.own ω).contA
  have hr := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).continuousOn_d10Rate (hH.own ω) (hH.d9 ω) (hH.alive₀ ω).choose_spec
    (v := fun m => (hH.alive ω m).choose) (fun m => (hH.alive ω m).choose_spec)
  have hJ : ContinuousOn (fun τ => ∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u)
      (Icc 0 (T ω)) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T ω) (μ := volume)
      (f := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate) (by rw [uIcc_of_le hT0]; exact hr.integrableOn_Icc)
    rwa [uIcc_of_le hT0] at h
  have h1 := (hW'a.comp_continuous hm fun t => hH.mem_Icc_min t ω)
  have h2 := (hJ.comp_continuous hm fun t => hH.mem_Icc_min t ω)
  have h3 : Continuous fun t : ℝ≥0 => B (min t (S ω)) ω := (hBc ω).comp (continuous_id.min continuous_const)
  exact (((h1.sub continuous_const).sub h2).div_const _).add ((hBc ω).sub h3)

omit hH in
theorem bmExp_eq (ν : ℝ) (t : ℝ≥0) (ω : Ω) :
    bmExp κ B W' a φ rr ζ₀ ζ S ν t ω = d10Exp κ B W' a φ rr ζ₀ ζ ν ω ((min t (S ω) : ℝ≥0) : ℝ) *
      (wald ν B t ω / wald ν B (min t (S ω)) ω) := by
  simp only [bmExp, d10Exp, wald, bmY, bmClk]
  rw [← Real.exp_sub, ← Real.exp_add]
  congr 1; ring

variable {𝓕 : Filtration ℝ≥0 mΩ}

theorem measurable_bmY [Nonempty Ω] (hκ : 0 < κ) (hBm : ∀ u, Measurable[𝓕 u] (B u))
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[𝓕 t] (bmY κ B W' a φ rr ζ₀ ζ S t) := by
  have hDL := isDriverLogField_frozen hκ hBm hBc hS hH.toFrzMartHyp
  have hDL' := hH.isDriverLogField_d10 hκ hBm hBc hS 1
  have hρ := hH.toFrzMartHyp.cutRad_pos (Classical.arbitrary Ω)
  have h1 := hDL.measurable_addExp (ψ := d10Psi κ B W' a φ rr ζ₀ ζ 1 S) hDL' hBc hρ hS t
  have h2 := hH.measurable_imgClk hBm hBc hS t
  have h3 := measurable_stopped_min hS hBm hBc t
  have e : bmY κ B W' a φ rr ζ₀ ζ S t = fun ω =>
      (Real.log (addExp (Real.sqrt κ) B S (d10Psi κ B W' a φ rr ζ₀ ζ 1 S) t ω) + imgClk a S ω t / 2) +
        (B t ω - B (min t (S ω)) ω) := by
    funext ω
    rw [hH.addExp_d10_eq 1 t ω, Real.log_exp]
    simp only [bmY, imgClk]
    ring
  rw [e]
  exact (h1.log.add (h2.div_const 2)).add ((hBm t).sub h3)

omit hH in
theorem bmR_min (ν : ℝ) (u : ℝ≥0) (ω : Ω) :
    bmR κ B W' a φ rr ζ₀ ζ S ν (min u (S ω)) ω = bmR κ B W' a φ rr ζ₀ ζ S ν u ω := by
  simp only [bmR, min_eq_left (min_le_right u (S ω))]

omit hH in
theorem bmR_mul_wald_min (ν : ℝ) (u : ℝ≥0) (ω : Ω) :
    bmR κ B W' a φ rr ζ₀ ζ S ν u ω * wald ν B (min u (S ω)) ω =
      logFieldExp (Real.sqrt κ) B (fun ω t x => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell t x +
        d10Psi κ B W' a φ rr ζ₀ ζ ν S ω t x) (min u (S ω)) ω *
      Real.exp (-(frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell 0 (Real.sqrt κ * B 0 ω)) := by
  rw [bmR, div_mul_cancel₀ _ (show wald ν B (min u (S ω)) ω ≠ 0 from (Real.exp_pos _).ne')]

/-- **The splice identity**: `exp(νY_u − ν²C'_u/2) · N⁰_u = R_u E_u` (`N⁰` the density process of `Q`). -/
theorem bmExp_mul_girsN (hκ : 0 < κ) (ν : ℝ) (u : ℝ≥0) (ω : Ω) :
    bmExp κ B W' a φ rr ζ₀ ζ S ν u ω *
      girsN (Real.sqrt κ) 0 B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
        (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX) u ω =
      bmR κ B W' a φ rr ζ₀ ζ S ν u ω * wald ν B u ω := by
  rw [bmExp_eq, show d10Exp κ B W' a φ rr ζ₀ ζ ν ω ((min u (S ω) : ℝ≥0) : ℝ) =
    addExp (Real.sqrt κ) B S (d10Psi κ B W' a φ rr ζ₀ ζ ν S) u ω from (hH.addExp_d10_eq ν u ω).symm,
    girsN_zero_eq (Real.sqrt_pos.2 hκ).ne', bmR, addExp]
  simp only [logFieldExp, Real.exp_add, Real.exp_sub, Real.exp_neg]
  have h1 : wald ν B (min u (S ω)) ω ≠ 0 := (Real.exp_pos _).ne'
  field_simp

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The `Q`-martingale of the spliced exponential** (`|B| ≤ N_B` on `[0, S]`). -/
theorem martingale_bmExp {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ}
    (hBb : ∀ ω (r : ℝ≥0), r ≤ S ω → |B r ω| ≤ NB) (ν : ℝ) :
    Martingale (bmExp κ B W' a φ rr ζ₀ ζ S ν) 𝓕
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hne : Nonempty Ω := ⟨ω₀⟩
  have hσ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hDL := isDriverLogField_frozen hκ hBm hBc hS hH.toFrzMartHyp
  have hDL' := hH.isDriverLogField_d10 hκ hBm hBc hS ν
  have hρ := hH.toFrzMartHyp.cutRad_pos ω₀
  have hSR : ∀ ω, S ω ≤ Tmax.toNNReal := fun ω => by
    rw [← Real.toNNReal_coe (r := S ω)]
    exact Real.toNNReal_le_toNNReal ((hH.le ω).trans (hH.leMax ω))
  have hQ := hDL.isProbabilityMeasure_girsMeasure hB hBc hσ hρ hS hSR
  set Kf := 2 * coefTot κ rr * scaleBound L with hKf
  set K' := 2 * coefTot κ rr * scaleBound L + d10K κ ν γ Γ L Tmax rr with hK'
  set cw := |ν| * NB + ν ^ 2 * Tmax / 2 with hcw
  -- `1/E_{u∧S}` is bounded
  have hinvw : ∀ u ω, (wald ν B (min u (S ω)) ω)⁻¹ ≤ Real.exp cw := fun u ω => by
    rw [wald, ← Real.exp_neg]
    apply Real.exp_le_exp.2
    have hb := hBb ω (min u (S ω)) (min_le_right _ _)
    have hm : ((min u (S ω) : ℝ≥0) : ℝ) ≤ Tmax :=
      (NNReal.coe_le_coe.2 (min_le_right _ _)).trans ((hH.le ω).trans (hH.leMax ω))
    have h1 : -(ν * B (min u (S ω)) ω) ≤ |ν| * NB := by
      have := neg_abs_le (ν * B (min u (S ω)) ω)
      rw [abs_mul] at this
      nlinarith [abs_nonneg ν, mul_le_mul_of_nonneg_left hb (abs_nonneg ν)]
    have h2 : ν ^ 2 * ((min u (S ω) : ℝ≥0) : ℝ) / 2 ≤ ν ^ 2 * Tmax / 2 := by
      have := mul_le_mul_of_nonneg_left hm (sq_nonneg ν); linarith
    rw [hcw]; linarith
  -- the factor `R`
  have hRb : ∀ u ω, |bmR κ B W' a φ rr ζ₀ ζ S ν u ω| ≤ Real.exp K' * Real.exp Kf * Real.exp cw := fun u ω => by
    have h1 := hDL'.abs_logFieldExp_le hρ (ω := ω) (min_le_right u (S ω))
    have h0 := hDL.abs_le hρ ω ⟨le_rfl, (S ω).coe_nonneg⟩
    simp only [Real.toNNReal_zero] at h0
    have h2 : Real.exp (-(frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell 0 (Real.sqrt κ * B 0 ω)) ≤ Real.exp Kf :=
      Real.exp_le_exp.2 (by linarith [(_root_.abs_le.1 h0).1])
    rw [bmR, div_eq_mul_inv, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (inv_pos.2 (show 0 < wald ν B (min u (S ω)) ω from Real.exp_pos _))]
    exact mul_le_mul (mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le) (hinvw u ω)
      (inv_pos.2 (show 0 < wald ν B (min u (S ω)) ω from Real.exp_pos _)).le (by positivity)
  have hRm : ∀ u, Measurable[𝓕 u] (bmR κ B W' a φ rr ζ₀ ζ S ν u) := fun u => by
    have h1 := hDL'.measurable_logFieldExp_stopped hBc hρ hS (fun ω => le_rfl) u
    have h0 : Measurable[𝓕 u] fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell 0 (Real.sqrt κ * B 0 ω) := by
      have h := hDL.meas0 0
      have e : {ω | (0 : ℝ≥0) ≤ S ω}.indicator (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell ((0 : ℝ≥0) : ℝ)
          (Real.sqrt κ * B 0 ω)) = fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell 0 (Real.sqrt κ * B 0 ω) := by
        funext ω; rw [indicator_of_mem (by simp : ω ∈ {ω | (0 : ℝ≥0) ≤ S ω})]; rfl
      rw [e] at h
      exact h.mono (𝓕.mono zero_le) le_rfl
    have h2 := measurable_stopped_min hS hBm hBc u
    have h3 := measurable_min_S hS u
    have hF : Continuous fun p : ℝ × ℝ × ℝ × ℝ =>
        p.1 * Real.exp (-p.2.1) / Real.exp (ν * p.2.2.1 - ν ^ 2 * p.2.2.2 / 2) :=
      (continuous_fst.mul (Real.continuous_exp.comp (continuous_fst.comp continuous_snd).neg)).div
        (Real.continuous_exp.comp ((continuous_const.mul (continuous_fst.comp (continuous_snd.comp continuous_snd))).sub
          ((continuous_const.mul (continuous_snd.comp (continuous_snd.comp continuous_snd))).div_const 2)))
        fun _ => (Real.exp_pos _).ne'
    exact hF.measurable.comp (h1.prodMk (h0.prodMk (h2.prodMk h3)))
  have hRc : ∀ ω, Continuous fun u => bmR κ B W' a φ rr ζ₀ ζ S ν u ω := fun ω => by
    have hm : Continuous fun u : ℝ≥0 => (((min u (S ω)) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_id.min continuous_const)
    have hmS : ∀ u : ℝ≥0, (((min u (S ω)) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (S ω) := fun u =>
      ⟨(min u (S ω)).coe_nonneg, NNReal.coe_le_coe.2 (min_le_right _ _)⟩
    have hℓ : Continuous fun u : ℝ≥0 => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell (((min u (S ω)) : ℝ≥0) : ℝ)
        (Real.sqrt κ * B (((min u (S ω) : ℝ≥0) : ℝ)).toNNReal ω) +
        d10Psi κ B W' a φ rr ζ₀ ζ ν S ω (((min u (S ω)) : ℝ≥0) : ℝ)
          (Real.sqrt κ * B (((min u (S ω) : ℝ≥0) : ℝ)).toNNReal ω) :=
      (hDL'.continuousOn_driver hBc hρ ω).comp_continuous hm hmS
    simp only [Real.toNNReal_coe] at hℓ
    have hw : Continuous fun u : ℝ≥0 => wald ν B (min u (S ω)) ω :=
      (continuous_wald hBc ν ω).comp (continuous_id.min continuous_const)
    exact ((Real.continuous_exp.comp hℓ).mul continuous_const).div hw fun _ => (Real.exp_pos _).ne'
  have hRp : IsStronglyProgressive 𝓕 (bmR κ B W' a φ rr ζ₀ ζ S ν) :=
    isStronglyProgressive_of_rightContinuous (fun u => (hRm u).stronglyMeasurable)
      fun ω u => (hRc ω).continuousWithinAt
  have h1 : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set Ω}, MeasurableSet[𝓕 s] A →
      ∫ ω in A, bmR κ B W' a φ rr ζ₀ ζ S ν t ω * wald ν B (min t (S ω)) ω ∂P =
        ∫ ω in A, bmR κ B W' a φ rr ζ₀ ζ S ν s ω * wald ν B (min s (S ω)) ω ∂P := fun {s t} hst {A} hA => by
    simp only [bmR_mul_wald_min]
    exact IsDriverLogField.setIntegral_mul_exp_neg_eq hDL hDL' hB hBc hσ.le hρ hS hst hA
  -- `exp(νY − ν²C'/2)`
  have hEm : ∀ u, Measurable[𝓕 u] (bmExp κ B W' a φ rr ζ₀ ζ S ν u) := fun u => by
    have hF : Continuous fun p : ℝ × ℝ => Real.exp (ν * p.1 - ν ^ 2 * p.2 / 2) := by fun_prop
    exact hF.measurable.comp ((hH.measurable_bmY hκ hBm hBc hS u).prodMk (hH.measurable_bmClk hBm hBc hS u))
  set Mb := |ν / Real.sqrt κ| * (2 * Γ + d10Bound κ γ rr * Tmax) + ν ^ 2 / 2 * Tmax with hMb
  have hEb : ∀ u ω, |bmExp κ B W' a φ rr ζ₀ ζ S ν u ω| ≤ Real.exp Mb * Real.exp cw * wald ν B u ω := fun u ω => by
    have hpos : 0 < d10Exp κ B W' a φ rr ζ₀ ζ ν ω ((min u (S ω) : ℝ≥0) : ℝ) *
        (wald ν B u ω / wald ν B (min u (S ω)) ω) := by
      unfold d10Exp wald; positivity
    rw [bmExp_eq, abs_of_pos hpos]
    have hd : d10Exp κ B W' a φ rr ζ₀ ζ ν ω ((min u (S ω) : ℝ≥0) : ℝ) ≤ Real.exp Mb := by
      rw [d10Exp]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (hH.abs_log_d10Exp_le ν ω (hH.mem_Icc_min u ω)))
    rw [div_eq_mul_inv]
    calc _ ≤ Real.exp Mb * (wald ν B u ω * Real.exp cw) :=
          mul_le_mul hd (mul_le_mul_of_nonneg_left (hinvw u ω) (Real.exp_pos _).le)
            (mul_nonneg (Real.exp_pos _).le (inv_pos.2 (Real.exp_pos _)).le) (Real.exp_pos _).le
      _ = _ := by ring
  have hEi : ∀ u, Integrable (bmExp κ B W' a φ rr ζ₀ ζ S ν u) P := fun u =>
    (((martingale_wald hB ν).integrable u).const_mul (Real.exp Mb * Real.exp cw)).mono'
      ((hEm u).mono (𝓕.le u) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hEb u ω)
  -- the density
  have hDmeas : Measurable (girsDensity (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
    have hmR := (hDL.measurable_girsN_zero hBc hσ.ne' hρ hS Tmax.toNNReal).mono (𝓕.le _) le_rfl
    have e : girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) =
        girsN (Real.sqrt κ) 0 B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
          (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX) Tmax.toNNReal :=
      funext fun ω => girsDensity_eq_girsN hσ.ne' (hSR ω)
    rw [e]; exact hmR
  have hDb : ∀ ω, ‖girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) ω‖ ≤
      Real.exp (2 * Kf) := fun ω => by
    rw [girsDensity_eq_girsN (ℓx := fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX) hσ.ne' (hSR ω), Real.norm_eq_abs]
    exact hDL.abs_girsN_zero_le hσ.ne' hρ _ ω
  have hDpos : ∀ ω, 0 ≤ girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) ω :=
    fun ω => (Real.exp_pos _).le
  have hQi : ∀ u, Integrable (bmExp κ B W' a φ rr ζ₀ ζ S ν u)
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := fun u => by
    rw [girsMeasure, integrable_withDensity_iff
      (f := fun ω => ENNReal.ofReal (girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) ω))
      (ENNReal.measurable_ofReal.comp hDmeas)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have e : (fun ω => bmExp κ B W' a φ rr ζ₀ ζ S ν u ω *
        (ENNReal.ofReal (girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) ω)).toReal) =
        fun ω => bmExp κ B W' a φ rr ζ₀ ζ S ν u ω *
          girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) ω := by
      funext ω; rw [ENNReal.toReal_ofReal (hDpos ω)]
    rw [e]
    exact (hEi u).mul_bdd (c := Real.exp (2 * Kf)) hDmeas.aestronglyMeasurable (Eventually.of_forall hDb)
  -- the set integrals under `Q`
  have key : ∀ (s u : ℝ≥0), s ≤ u → ∀ {A : Set Ω}, MeasurableSet[𝓕 s] A →
      ∫ ω in A, bmExp κ B W' a φ rr ζ₀ ζ S ν u ω
        ∂(girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) =
      ∫ ω in A, bmR κ B W' a φ rr ζ₀ ζ S ν u ω * wald ν B u ω ∂P := fun s u hsu A hA => by
    have hAm : MeasurableSet A := 𝓕.le s A hA
    have hY : Measurable[𝓕 u] (A.indicator (bmExp κ B W' a φ rr ζ₀ ζ S ν u)) := (hEm u).indicator (𝓕.mono hsu _ hA)
    have hYi : Integrable (A.indicator (bmExp κ B W' a φ rr ζ₀ ζ S ν u)) P := (hEi u).indicator hAm
    have hb := hDL.integral_mul_girsDensity hB hBc hσ hρ hS hSR u hY hYi
    rw [girsMeasure, MathFin.setIntegral_withDensity_ofReal hDmeas.aestronglyMeasurable hDpos _ hAm,
      ← integral_indicator hAm]
    have e1 : (A.indicator fun ω => bmExp κ B W' a φ rr ζ₀ ζ S ν u ω *
        girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) ω) =
        fun ω => A.indicator (bmExp κ B W' a φ rr ζ₀ ζ S ν u) ω *
          girsDensity (Real.sqrt κ) B S (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) ω := by
      funext ω; by_cases hω : ω ∈ A <;> simp [hω]
    rw [e1, hb, ← integral_indicator hAm]
    congr 1; funext ω
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, indicator_of_mem hω, hH.bmExp_mul_girsN hκ ν u ω]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
  refine ⟨fun u => (hEm u).stronglyMeasurable, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hQi t) (fun A _ _ => (hQi s).integrableOn)
    (fun A hA _ => ?_) ((hEm s).stronglyMeasurable.aestronglyMeasurable)).symm
  rw [key s t hst hA, key s s le_rfl hA]
  exact (setIntegral_mul_wald_eq_of_stopped hB hBc hS ν hRb hRm hRp (fun u ω => bmR_min ν u ω) h1 hst hA).symm

/-- **Lévy's characterization in the capacity time** (§A.1.3): under `Q = (M̃_S/M̃_0) · P`, the spliced noise read at the
inverse of the full clock, `B̂_u = Y_{C'⁻¹(u)}`, is a Brownian motion of the time-changed filtration `𝓗_u = 𝓕_{C'⁻¹(u)}`
(given `|B| ≤ N_B` on `[0, S]`, e.g. `FrzD10Hyp.abs_B_le`). -/
theorem isFilteredBrownianReal_bm {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ}
    (hBb : ∀ ω (r : ℝ≥0), r ≤ S ω → |B r ω| ≤ NB) :
    IsFilteredBrownianReal
      (Zhan.Retarget.timeChangeFilt 𝓕
        (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
          (hH.measurable_bmClk (fun u => hB.2.1 u) hBc hS))
        (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
      (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω)
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hne : Nonempty Ω := ⟨ω₀⟩
  have hDL := isDriverLogField_frozen hκ hBm hBc hS hH.toFrzMartHyp
  have hSR : ∀ ω, S ω ≤ Tmax.toNNReal := fun ω => by
    rw [← Real.toNNReal_coe (r := S ω)]
    exact Real.toNNReal_le_toNNReal ((hH.le ω).trans (hH.leMax ω))
  have hQ := hDL.isProbabilityMeasure_girsMeasure hB hBc (Real.sqrt_pos.2 hκ) (hH.toFrzMartHyp.cutRad_pos ω₀) hS hSR
  have ha₀ := (hH.d9 ω₀).a0
  exact isFilteredBrownianReal_timeChange (fun ω => hH.continuous_bmY hBc ω) (hH.measurable_bmY hκ hBm hBc hS)
    hH.bmY_zero hH.continuous_bmClk hH.strictMono_bmClk hH.bmClk_zero (lt_min (pow_pos ha₀ 2) one_pos)
    hH.le_bmClk (hH.measurable_bmClk hBm hBc hS) fun ν => hH.martingale_bmExp hκ hB hBc hS hBb ν

/-- **The image driver solves the force-point equation driven by `B̂` up to `a(S)`**: for `u ≤ a(S)`,
`√κ B̂_u = W'(u) − W'(0) − ∫₀ᵘ (−κ/(2(W' − Ṽ₀)) + Σ ρ_m/(W' − Ṽ_m))`. -/
theorem bmY_invClockT_eq {u : ℝ≥0} {ω : Ω} (hu : (u : ℝ) ≤ a ω (S ω)) :
    bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω =
      (W' ω u - W' ω 0 - ∫ v in (0 : ℝ)..u, imgDrift κ rr (W' ω) ζ₀ ζ v) / Real.sqrt κ := by
  have ha₀ := (hH.d9 ω).a0
  have hc : 0 < min (a₀ ^ 2) 1 := lt_min (pow_pos ha₀ 2) one_pos
  obtain ⟨-, hC, -⟩ := invClock_eq_coe hH.continuous_bmClk hH.bmClk_zero hc hH.le_bmClk u ω
  set θ := invClockT (bmClk a S) u ω with hθ
  have hθS : θ ≤ S ω := by
    by_contra h
    push Not at h
    have e : bmClk a S ω θ = a ω (S ω) + ((θ : ℝ) - S ω) := by simp only [bmClk, min_eq_right h.le]
    have hθS' : (S ω : ℝ) < θ := h
    linarith
  have haθ : a ω θ = u := by
    have e : bmClk a S ω θ = a ω θ := by simp only [bmClk, min_eq_left hθS, sub_self, add_zero]
    rw [← e, hC]
  have hmem : (θ : ℝ) ∈ Icc (0 : ℝ) (T ω) := ⟨θ.coe_nonneg, (NNReal.coe_le_coe.2 hθS).trans (hH.le ω)⟩
  simp only [bmY, min_eq_left hθS, sub_self, add_zero]
  rw [hH.d10Int_eq_imgDrift ω hmem, haθ]

/-- **The driver bound used by the splice**: if the hulls stay in `B̄(0, R)` up to `T`, then `|B| ≤ 7R/√κ` on `[0, S]`. -/
theorem abs_B_le (hκ : 0 < κ) (hBc : ∀ ω, Continuous (B · ω)) {R : ℝ} (hR : 0 < R)
    (hK : ∀ ω, fwdHull (drive κ B ω) (T ω) ⊆ Metric.closedBall (0 : ℂ) R) (ω : Ω) (r : ℝ≥0) (hr : r ≤ S ω) :
    |B r ω| ≤ 7 * R / Real.sqrt κ := by
  have hB0 : ∀ ω, B 0 ω = 0 := fun ω => by
    have h := (hH.own ω).zero
    simp only [drive, Real.toNNReal_zero] at h
    exact (mul_eq_zero.1 h).resolve_left (Real.sqrt_pos.2 hκ).ne'
  exact abs_B_le_of_hull hκ hBc hR hK hB0 ω r ((NNReal.coe_le_coe.2 hr).trans (hH.le ω))

end FrzD10Hyp

end Frozen

end InteractingSLE.ZhanGT4
