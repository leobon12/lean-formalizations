/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD10Frozen
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianTime

/-!
# (D10), III: the capacity time change

Packet PROVE-ZHAN-GT4-A10. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L353–L355, R38):
"The time change `du = A²_{j,1} dt_j`, Lévy's characterization, and uniqueness in law of the integrated force system
identify the claimed conditional image law inside this rectangle."

The (D10) exponential martingales of `DualD10Frozen` (`FrzD10Hyp.martingale_d10`) are read at the inverse of the
stopped image capacity clock `C_r = a(r ∧ S)`: `τ_u = inf{r : C_r ≥ u}` (`invClock`, `⊤` when `u > a(S)`), a
stopping time of `𝓕` for every `u` (`isStoppingTime_invClock`), nondecreasing in `u`. In the time-changed filtration
`𝓗_u = 𝓕_{τ_u}` (`Zhan.Retarget.timeChangeFilt`) and under `Q = (M̃_S/M̃_0) · P`, for every `ν`

  `exp(ν B̃_u − ν² (u ∧ a(S))/2)`,  `√κ B̃_u = W'(u ∧ a(S)) − W'(0) − J_{θ_u}`,  `θ_u = a⁻¹(u ∧ a(S))`,

is a martingale (**`FrzD10Hyp.martingale_d10_timeChange`**): `B̃` is a `Q`-Brownian motion of `𝓗` stopped at the
`𝓗`-stopping time `a(S)` (Lévy's characterization in exponential form), and by the substitution `v = a(t)` the
image driver `W'` solves the force-point equation `dW' = √κ dB̃ + (−κ/(2(W' − Ṽ₀)) + Σ ρ_m/(W' − Ṽ_m)) dv` on
`[0, a(S)]` (**`FrzD10Hyp.d10Int_eq_imgDrift`**).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)
open Sec2.TwoSeed (capTime coe_capTime)

/-! ### Cut integrals as integrals up to `t ∧ S` -/

section CutMin

variable {Ω : Type*} {S : Ω → ℝ≥0} {g : Ω → ℝ → ℝ}

/-- `∫₀ʳ g 1_{· < S} = ∫₀^{r∧S} g`. -/
theorem cutInt_eq_min (hgc : ∀ ω, ContinuousOn (g ω) (Icc 0 (S ω : ℝ))) (ω : Ω) (r : ℝ≥0) :
    cutInt S g ω r = ∫ u in (0 : ℝ)..((min r (S ω) : ℝ≥0) : ℝ), g ω u := by
  rcases le_total r (S ω) with h | h
  · rw [min_eq_left h]; exact cutInt_eq ω ⟨r.coe_nonneg, NNReal.coe_le_coe.2 h⟩
  · rw [min_eq_right h]
    have hS0 : (0 : ℝ) ≤ S ω := (S ω).coe_nonneg
    have hSr : (S ω : ℝ) ≤ r := NNReal.coe_le_coe.2 h
    have hI1 : IntervalIntegrable (fun u : ℝ => cutRate S g u.toNNReal ω) volume 0 (S ω) := by
      refine ((hgc ω).intervalIntegrable_of_Icc hS0).congr_uIoo fun u hu => ?_
      rw [uIoo_of_le hS0] at hu
      have hlt : u.toNNReal < S ω := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu.1.le]; exact hu.2
      simp only [cutRate, hlt, ↓reduceIte, Real.coe_toNNReal _ hu.1.le]
    have hz : EqOn (fun u : ℝ => cutRate S g u.toNNReal ω) (fun _ => (0 : ℝ)) (uIcc (S ω : ℝ) r) := fun u hu => by
      rw [uIcc_of_le hSr] at hu
      have : ¬ u.toNNReal < S ω := by
        rw [not_lt, ← NNReal.coe_le_coe, Real.coe_toNNReal _ (hS0.trans hu.1)]; exact hu.1
      simp only [cutRate, this, ↓reduceIte]
    have hI2 : IntervalIntegrable (fun u : ℝ => cutRate S g u.toNNReal ω) volume (S ω) r :=
      (intervalIntegrable_const (c := (0 : ℝ))).congr fun u hu => (hz (uIoc_subset_uIcc hu)).symm
    unfold cutInt
    rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2, intervalIntegral.integral_congr hz,
      intervalIntegral.integral_zero, add_zero]
    exact cutInt_eq ω ⟨hS0, le_rfl⟩

end CutMin

/-! ### The inverse of a continuous nondecreasing clock -/

section InvClock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open scoped Classical in
/-- **The inverse of a nondecreasing continuous clock** `C`: `τ_u = inf{r : u ≤ C_r}`, `⊤` if `C` never reaches
`u`. -/
def invClock (C : Ω → ℝ≥0 → ℝ) (u : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  if ∃ r, (u : ℝ) ≤ C ω r then ((sInf {r : ℝ≥0 | (u : ℝ) ≤ C ω r} : ℝ≥0) : WithTop ℝ≥0) else ⊤

variable {C : Ω → ℝ≥0 → ℝ}

/-- `τ_u ≤ r` iff `u ≤ C_r`. -/
theorem invClock_le_iff (hCc : ∀ ω, Continuous (C ω)) (hCm : ∀ ω, Monotone (C ω)) (u r : ℝ≥0) (ω : Ω) :
    invClock C u ω ≤ (r : WithTop ℝ≥0) ↔ (u : ℝ) ≤ C ω r := by
  unfold invClock
  split_ifs with h
  · have hmem : sInf {r : ℝ≥0 | (u : ℝ) ≤ C ω r} ∈ {r : ℝ≥0 | (u : ℝ) ≤ C ω r} :=
      (isClosed_le continuous_const (hCc ω)).csInf_mem h (OrderBot.bddBelow _)
    rw [WithTop.coe_le_coe]
    exact ⟨fun hle => le_trans hmem (hCm ω hle), fun hr => csInf_le (OrderBot.bddBelow _) hr⟩
  · push Not at h
    simp only [top_le_iff, WithTop.coe_ne_top, false_iff, not_le]
    exact h r

/-- The inverse clock is nondecreasing in `u`. -/
theorem invClock_mono (hCc : ∀ ω, Continuous (C ω)) (hCm : ∀ ω, Monotone (C ω)) (u v : ℝ≥0) (huv : u ≤ v)
    (ω : Ω) : invClock C u ω ≤ invClock C v ω := by
  by_cases h : invClock C v ω = ⊤
  · rw [h]; exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h
    rw [← hr, invClock_le_iff hCc hCm]
    have := (invClock_le_iff hCc hCm v r ω).1 hr.ge
    exact (NNReal.coe_le_coe.2 huv).trans this

/-- **The inverse clock is a stopping time** when the clock is adapted. -/
theorem isStoppingTime_invClock {𝓕 : Filtration ℝ≥0 mΩ} (hCc : ∀ ω, Continuous (C ω))
    (hCm : ∀ ω, Monotone (C ω)) (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => C ω r) (u : ℝ≥0) :
    IsStoppingTime 𝓕 (invClock C u) := by
  intro r
  have e : {ω | invClock C u ω ≤ (r : WithTop ℝ≥0)} = {ω | (u : ℝ) ≤ C ω r} := by
    ext ω; exact invClock_le_iff hCc hCm u r ω
  rw [e]
  exact measurableSet_le measurable_const (hmeas r)

/-- **The clock at the inverse clock**: if `C_0 ≤ u` and `C` reaches `u`, then `τ_u` is finite and `C_{τ_u} = u`. -/
theorem exists_invClock_eq (hCc : ∀ ω, Continuous (C ω)) {u : ℝ≥0} {ω : Ω}
    (h0 : C ω 0 ≤ u) {r : ℝ≥0} (hr : (u : ℝ) ≤ C ω r) :
    ∃ θ : ℝ≥0, invClock C u ω = θ ∧ C ω θ = u ∧ θ ≤ r := by
  have hex : ∃ r, (u : ℝ) ≤ C ω r := ⟨r, hr⟩
  set θ := sInf {r : ℝ≥0 | (u : ℝ) ≤ C ω r} with hθ
  have hmem : θ ∈ {r : ℝ≥0 | (u : ℝ) ≤ C ω r} :=
    (isClosed_le continuous_const (hCc ω)).csInf_mem hex (OrderBot.bddBelow _)
  obtain ⟨θ', hθ', hCθ'⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ θ from zero_le) (hCc ω).continuousOn ⟨h0, hmem⟩
  have hθθ' : θ ≤ θ' := csInf_le (OrderBot.bddBelow _) (show (u : ℝ) ≤ C ω θ' from hCθ'.ge)
  have he : θ' = θ := le_antisymm hθ'.2 hθθ'
  refine ⟨θ, ?_, he ▸ hCθ', csInf_le (OrderBot.bddBelow _) hr⟩
  unfold invClock
  simp only [hex, ↓reduceIte, hθ]

/-- If `C ≤ c` everywhere and `c < u`, then `τ_u = ⊤`. -/
theorem invClock_eq_top {u : ℝ≥0} {ω : Ω} {c : ℝ} (hC : ∀ r, C ω r ≤ c) (hu : c < u) : invClock C u ω = ⊤ := by
  have h : ¬ ∃ r, (u : ℝ) ≤ C ω r := by
    push Not
    exact fun r => lt_of_le_of_lt (hC r) hu
  unfold invClock
  simp only [h, ↓reduceIte]

end InvClock

/-! ### The stopped image capacity clock and the time-changed (D10) martingale -/

section Frozen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The stopped image capacity clock** `C_r = a(r ∧ S)`. -/
def imgClk (a : Ω → ℝ → ℝ) (S : Ω → ℝ≥0) (ω : Ω) (r : ℝ≥0) : ℝ := a ω ((min r (S ω) : ℝ≥0) : ℝ)

/-- **The original time at image time `u`**: `θ_u = τ_u ∧ N ∧ S` (`= a⁻¹(u ∧ a(S))`, `a_d10Theta`). -/
def d10Theta (a : Ω → ℝ → ℝ) (S : Ω → ℝ≥0) (N : ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  ((min (capTime (fun _ => N) (invClock (imgClk a S) u) ω) (S ω) : ℝ≥0) : ℝ)

/-- **The (D10) exponential at original time `τ`**: `exp((ν/√κ)(W'(a(τ)) − W'(0) − J_τ) − (ν²/2) a(τ))`. -/
def d10Exp {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (φ : ℂ → ℂ) (rr : Fin n → ℝ) (ζ₀ : ℝ)
    (ζ : Fin n → ℝ) (ν : ℝ) (ω : Ω) (τ : ℝ) : ℝ :=
  Real.exp (ν / Real.sqrt κ * (W' ω (a ω τ) - W' ω 0 -
    ∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u) - ν ^ 2 / 2 * a ω τ)

/-- **The image force point** `Ṽ(v) = g̃_v(ζ) = Re f̃_v(ζ) + W'(v)` of a real mark `ζ` in the image chain. -/
def imgV (W' : ℝ → ℝ) (ζ : ℝ) (v : ℝ) : ℝ := (fwdMap W' v (ζ : ℂ)).re + W' v

/-- **The force-point drift in the capacity time**: `−κ/(2(W' − Ṽ₀)) + Σ ρ_m/(W' − Ṽ_m)`, `ρ_m = κ r_m`. -/
def imgDrift {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (W' : ℝ → ℝ) (ζ₀ : ℝ) (ζ : Fin n → ℝ) (v : ℝ) : ℝ :=
  -(κ / (2 * (W' v - imgV W' ζ₀ v))) + ∑ m, κ * rr m / (W' v - imgV W' (ζ m) v)

namespace FrzD10Hyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

theorem mem_Icc_min (t : ℝ≥0) (ω : Ω) : ((min t (S ω) : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) (T ω) :=
  ⟨(min t (S ω)).coe_nonneg, (NNReal.coe_le_coe.2 (min_le_right _ _)).trans (hH.le ω)⟩

theorem continuous_imgClk (ω : Ω) : Continuous (imgClk a S ω) := by
  have hc : Continuous fun r : ℝ≥0 => ((min r (S ω) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  exact (hH.own ω).contA.comp_continuous hc fun r => hH.mem_Icc_min r ω

theorem monotone_imgClk (ω : Ω) : Monotone (imgClk a S ω) := fun r s hrs =>
  (hH.own ω).mono.monotoneOn (hH.mem_Icc_min r ω) (hH.mem_Icc_min s ω)
    (NNReal.coe_le_coe.2 (min_le_min_right _ hrs))

theorem imgClk_zero (ω : Ω) : imgClk a S ω 0 = 0 := by
  simp only [imgClk, zero_le, min_eq_left, NNReal.coe_zero]
  exact (hH.own ω).a0

theorem imgClk_le (ω : Ω) (r : ℝ≥0) : imgClk a S ω r ≤ a ω (S ω) :=
  (hH.own ω).mono.monotoneOn (hH.mem_Icc_min r ω) ⟨(S ω).coe_nonneg, hH.le ω⟩
    (NNReal.coe_le_coe.2 (min_le_right _ _))

theorem S_le_N {N : ℝ≥0} (hN : Tmax ≤ N) (ω : Ω) : S ω ≤ N :=
  NNReal.coe_le_coe.1 (((hH.le ω).trans (hH.leMax ω)).trans hN)

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The stopped clock is adapted**: `a(r ∧ S) = ∫₀ʳ A²_{j,1} 1_{· < S}`. -/
theorem measurable_imgClk (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (rT : ℝ≥0) :
    Measurable[𝓕 rT] fun ω => imgClk a S ω rT := by
  set g : Ω → ℝ → ℝ := fun ω u => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 1 u ^ 2 with hg
  have hgc : ∀ ω, ContinuousOn (g ω) (Icc 0 (S ω : ℝ)) := fun ω =>
    (((hH.own ω).continuousOn_frzA 1).pow 2).mono (Icc_subset_Icc_right (hH.le ω))
  have hgm : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => g ω r) := fun r => by
    obtain ⟨hA, -, -, -, -, -⟩ := hH.toFrzMartHyp.measurable_parts hBm hBc hS r
    convert (hA 1).pow_const 2 using 1
    funext ω
    by_cases hω : ω ∈ {ω | r ≤ S ω}
    · simp only [indicator_of_mem hω, hg]; rfl
    · simp only [indicator_of_notMem hω]; norm_num
  have e : (fun ω => imgClk a S ω rT) = fun ω => cutInt S g ω rT := by
    funext ω
    rw [cutInt_eq_min hgc ω rT]
    exact ((hH.own ω).integral_frzA_one_sq (hH.mem_Icc_min rT ω)).symm
  rw [e]
  exact measurable_cutInt hgc hS hgm rT

/-- The inverse image clock is a stopping time. -/
theorem isStoppingTime_invImgClk (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (u : ℝ≥0) :
    IsStoppingTime 𝓕 (invClock (imgClk a S) u) :=
  isStoppingTime_invClock hH.continuous_imgClk hH.monotone_imgClk (hH.measurable_imgClk hBm hBc hS) u

/-- **The clock at `θ_u`**: `a(θ_u) = u ∧ a(S)`. -/
theorem a_d10Theta {N : ℝ≥0} (hN : Tmax ≤ N) (u : ℝ≥0) (ω : Ω) :
    a ω (d10Theta a S N u ω) = min (u : ℝ) (a ω (S ω)) := by
  have hSN := hH.S_le_N hN ω
  by_cases hu : (u : ℝ) ≤ a ω (S ω)
  · have hr : (u : ℝ) ≤ imgClk a S ω (S ω) := by simp only [imgClk, min_self]; exact hu
    obtain ⟨θ, hθ, hCθ, hθS⟩ := exists_invClock_eq hH.continuous_imgClk
      (by rw [hH.imgClk_zero ω]; exact u.coe_nonneg) hr
    have hcap : capTime (fun _ => N) (invClock (imgClk a S) u) ω = θ := by
      have h := coe_capTime (fun _ => N) (invClock (imgClk a S) u) ω
      rw [hθ, min_eq_right (WithTop.coe_le_coe.2 (hθS.trans hSN))] at h
      exact WithTop.coe_injective h
    have hCθ' : imgClk a S ω θ = a ω θ := by simp only [imgClk, min_eq_left hθS]
    unfold d10Theta
    rw [hcap, min_eq_left hθS, min_eq_left hu, ← hCθ', hCθ]
  · push Not at hu
    have htop := invClock_eq_top (C := imgClk a S) (c := a ω (S ω)) (fun r => hH.imgClk_le ω r) hu
    have hcap : capTime (fun _ => N) (invClock (imgClk a S) u) ω = N :=
      Sec2.TwoSeed.capTime_eq_of_le (by rw [htop]; exact le_top)
    unfold d10Theta
    rw [hcap, min_eq_right hSN, min_eq_right hu.le]

/-- `|J_τ| ≤ d10Bound · τ` on `[0, T]`. -/
theorem abs_d10Int_le (ω : Ω) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (T ω)) :
    |∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u| ≤ d10Bound κ γ rr * τ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ) (C := d10Bound κ γ rr)
    (f := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate) fun u hu => by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hτ.1] at hu
      exact (frzDataOf κ B W' a φ rr ζ₀ ζ ω).abs_d10Rate_le (hH.own ω) (hH.d9 ω) ⟨hu.1.le, hu.2.trans hτ.2⟩
  rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hτ.1] at h

/-- `0 ≤ a(τ) ≤ τ` on `[0, T]` (`a' = A²_{j,1} ≤ 1`). -/
theorem a_mem_Icc (ω : Ω) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (T ω)) : a ω τ ∈ Icc 0 τ := by
  rw [← (hH.own ω).integral_frzA_one_sq hτ]
  refine ⟨intervalIntegral.integral_nonneg hτ.1 fun u _ => sq_nonneg _, ?_⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := τ) (C := 1)
    (f := fun u => frzA (drive κ B ω) (W' ω) (a ω) φ 1 u ^ 2) fun u hu => by
      rw [uIoc_of_le hτ.1] at hu
      obtain ⟨h1, h2, -, -⟩ := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).driver_bounds (hH.own ω) (hH.d9 ω)
        ⟨hu.1.le, hu.2.trans hτ.2⟩
      have ha := (hH.d9 ω).a0
      have : frzA (drive κ B ω) (W' ω) (a ω) φ 1 u ^ 2 ≤ 1 := by
        change (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 1 u ^ 2 ≤ 1; nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact this
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hτ.1, one_mul] at h
  exact (le_abs_self _).trans h

/-- The bound of the (D10) exponent on the protected rectangle. -/
theorem abs_log_d10Exp_le (ν : ℝ) (ω : Ω) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (T ω)) :
    |ν / Real.sqrt κ * (W' ω (a ω τ) - W' ω 0 - ∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u) -
      ν ^ 2 / 2 * a ω τ| ≤ |ν / Real.sqrt κ| * (2 * Γ + d10Bound κ γ rr * Tmax) + ν ^ 2 / 2 * Tmax := by
  have h1 := hH.drv ω τ hτ
  have h0 : |W' ω 0| ≤ Γ := by
    have := hH.drv ω 0 ⟨le_rfl, (hH.own ω).pos.le⟩; rwa [(hH.own ω).a0] at this
  have hJ := hH.abs_d10Int_le ω hτ
  have ha := hH.a_mem_Icc ω hτ
  have hτm : τ ≤ Tmax := hτ.2.trans (hH.leMax ω)
  have hγ := (hH.d9 ω).g0
  have hB0 : 0 ≤ d10Bound κ γ rr := mul_nonneg (div_nonneg (abs_nonneg _) hγ.le) (by positivity)
  have hX : |W' ω (a ω τ) - W' ω 0 - ∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u| ≤
      2 * Γ + d10Bound κ γ rr * Tmax := by
    have := mul_le_mul_of_nonneg_left hτm hB0
    calc _ ≤ |W' ω (a ω τ) - W' ω 0| + |∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u| :=
          abs_sub _ _
      _ ≤ (|W' ω (a ω τ)| + |W' ω 0|) + d10Bound κ γ rr * τ := add_le_add (abs_sub _ _) hJ
      _ ≤ _ := by linarith
  have hY : |ν ^ 2 / 2 * a ω τ| ≤ ν ^ 2 / 2 * Tmax := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 2 / 2), abs_of_nonneg ha.1]
    exact mul_le_mul_of_nonneg_left (ha.2.trans hτm) (by positivity)
  calc _ ≤ |ν / Real.sqrt κ * (W' ω (a ω τ) - W' ω 0 -
        ∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u)| + |ν ^ 2 / 2 * a ω τ| := abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hX (abs_nonneg _)) hY

/-- The (D10) exponential is continuous on `[0, T]`. -/
theorem continuousOn_d10Exp (ν : ℝ) (ω : Ω) :
    ContinuousOn (d10Exp κ B W' a φ rr ζ₀ ζ ν ω) (Icc 0 (T ω)) := by
  have hT0 := (hH.own ω).pos.le
  have hW'a : ContinuousOn (fun τ => W' ω (a ω τ)) (Icc 0 (T ω)) :=
    (hH.own ω).contW'.comp_continuousOn (hH.own ω).contA
  have hr := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).continuousOn_d10Rate (hH.own ω) (hH.d9 ω) (hH.alive₀ ω).choose_spec
    (v := fun m => (hH.alive ω m).choose) (fun m => (hH.alive ω m).choose_spec)
  have hJ : ContinuousOn (fun τ => ∫ u in (0 : ℝ)..τ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u)
      (Icc 0 (T ω)) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T ω) (μ := volume)
      (f := (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate) (by rw [uIcc_of_le hT0]; exact hr.integrableOn_Icc)
    rwa [uIcc_of_le hT0] at h
  unfold d10Exp
  exact Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul ((hW'a.sub continuousOn_const).sub hJ)).sub
    (continuousOn_const.mul (hH.own ω).contA))

/-- **(D10) in the capacity time** (§A.1.3, "The time change `du = A²_{j,1} dt_j`, Lévy's characterization"): with
`θ_u = a⁻¹(u ∧ a(S))` (`d10Theta`, any `N ≥ Tmax`), the processes `exp(ν B̃_u − (ν²/2) a(θ_u))`,
`√κ B̃_u = W'(a(θ_u)) − W'(0) − J_{θ_u}`, are `Q`-martingales of the time-changed filtration `𝓗_u = 𝓕_{τ_u}`. -/
theorem martingale_d10_timeChange {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ν : ℝ) (N : ℝ≥0) :
    Martingale (fun u ω => d10Exp κ B W' a φ rr ζ₀ ζ ν ω (d10Theta a S N u ω))
      (Zhan.Retarget.timeChangeFilt 𝓕 (hH.isStoppingTime_invImgClk (fun u => hB.2.1 u) hBc hS)
        (invClock_mono hH.continuous_imgClk hH.monotone_imgClk))
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
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
  have := (isDriverLogField_frozen hκ hBm hBc hS hH.toFrzMartHyp).isProbabilityMeasure_girsMeasure hB hBc
    (Real.sqrt_pos.2 hκ) (hH.toFrzMartHyp.cutRad_pos ω₀) hS hSR
  have hM : Martingale (fun t ω => d10Exp κ B W' a φ rr ζ₀ ζ ν ω ((min t (S ω) : ℝ≥0) : ℝ)) 𝓕
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) :=
    hH.martingale_d10 hκ hB hBc hS ν
  have hMc : ∀ ω, Continuous fun t : ℝ≥0 => d10Exp κ B W' a φ rr ζ₀ ζ ν ω ((min t (S ω) : ℝ≥0) : ℝ) := fun ω =>
    (hH.continuousOn_d10Exp ν ω).comp_continuous (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
      fun t => hH.mem_Icc_min t ω
  have hMb : ∀ t ω, |d10Exp κ B W' a φ rr ζ₀ ζ ν ω ((min t (S ω) : ℝ≥0) : ℝ)| ≤
      Real.exp (|ν / Real.sqrt κ| * (2 * Γ + d10Bound κ γ rr * Tmax) + ν ^ 2 / 2 * Tmax) := fun t ω => by
    rw [d10Exp, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hH.abs_log_d10Exp_le ν ω (hH.mem_Icc_min t ω)))
  have h := Zhan.Retarget.martingale_comp_timeChange (hH.isStoppingTime_invImgClk hBm hBc hS)
    (invClock_mono hH.continuous_imgClk hH.monotone_imgClk) hM hMc hMb N 1 0
  simp only [one_mul, add_zero] at h
  exact h

/-- **(D10) in the capacity time, explicit form**: for `N ≥ Tmax`, `exp(ν B̃_u − (ν²/2)(u ∧ a(S)))` with
`√κ B̃_u = W'(u ∧ a(S)) − W'(0) − J_{θ_u}` is a `Q`-martingale of `𝓗` for every `ν`: `B̃` is a `Q`-Brownian motion of
`𝓗` stopped at `a(S)` (Lévy's characterization in exponential form). -/
theorem martingale_d10_timeChange' {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ν : ℝ) {N : ℝ≥0}
    (hN : Tmax ≤ N) :
    Martingale (fun (u : ℝ≥0) ω => Real.exp (ν / Real.sqrt κ * (W' ω (min (u : ℝ) (a ω (S ω))) - W' ω 0 -
        ∫ v in (0 : ℝ)..d10Theta a S N u ω, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate v) -
        ν ^ 2 / 2 * min (u : ℝ) (a ω (S ω))))
      (Zhan.Retarget.timeChangeFilt 𝓕 (hH.isStoppingTime_invImgClk (fun u => hB.2.1 u) hBc hS)
        (invClock_mono hH.continuous_imgClk hH.monotone_imgClk))
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
  have h := hH.martingale_d10_timeChange hκ hB hBc hS ν N
  have e : (fun u ω => d10Exp κ B W' a φ rr ζ₀ ζ ν ω (d10Theta a S N u ω)) = fun (u : ℝ≥0) ω =>
      Real.exp (ν / Real.sqrt κ * (W' ω (min (u : ℝ) (a ω (S ω))) - W' ω 0 -
        ∫ v in (0 : ℝ)..d10Theta a S N u ω, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate v) -
        ν ^ 2 / 2 * min (u : ℝ) (a ω (S ω))) := by
    funext u ω
    simp only [d10Exp, hH.a_d10Theta hN u ω]
  rwa [e] at h

/-- **The substitution `v = a(t)`** (§A.1.3, `du = A²_{j,1} dt_j`): `J_θ = ∫₀^θ A²_{j,1}(…)(t) dt =
∫₀^{a(θ)} (−κ/(2(W' − Ṽ₀)) + Σ ρ_m/(W' − Ṽ_m))(v) dv` on `[0, T]`. -/
theorem d10Int_eq_imgDrift (ω : Ω) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (T ω)) :
    ∫ u in (0 : ℝ)..θ, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate u =
      ∫ v in (0 : ℝ)..a ω θ, imgDrift κ rr (W' ω) ζ₀ ζ v := by
  set d := frzDataOf κ B W' a φ rr ζ₀ ζ ω with hd
  have hown : OwnData d.W A d.φ (T ω) d.a d.W' := hH.own ω
  have hJ : Icc (0 : ℝ) θ ⊆ Icc 0 (T ω) := Icc_subset_Icc_right hθ.2
  have huI : uIcc (0 : ℝ) θ = Icc 0 θ := uIcc_of_le hθ.1
  -- the integrand in the form `(imgDrift ∘ a) · a'`
  have hEq : EqOn d.d10Rate (fun t => (imgDrift κ rr (W' ω) ζ₀ ζ ∘ a ω) t * frzA d.W d.W' d.a d.φ 1 t ^ 2)
      (uIcc 0 θ) := fun t ht => by
    rw [huI] at ht
    have hA0 : d.A 0 t = W' ω (a ω t) := hown.frzA_zero (hJ ht)
    simp only [FrzData.d10Rate, Function.comp, imgDrift, imgV, hA0]
    rw [mul_comm]
    rfl
  -- the image force points are continuous in image time
  obtain ⟨v₀, hv₀⟩ := hH.alive₀ ω
  have hv := fun m => (hH.alive ω m).choose_spec
  have hcV : ∀ (z : ℝ) (vz : ℝ → ℂ), IsForwardSol (W' ω) (z : ℂ) (a ω (T ω)) vz →
      ContinuousOn (imgV (W' ω) z) (Icc 0 (a ω (T ω))) := fun z vz hvz => by
    have e : EqOn (imgV (W' ω) z) (fun v => (vz v).re + W' ω v) (Icc 0 (a ω (T ω))) := fun v hv => by
      rw [imgV, InteractingSLE.fwdMap_eq_of_isForwardSol (W := W' ω) hown.contW' hvz hv]
    exact ((Complex.continuous_re.comp_continuousOn hvz.1).add (hown.contW'.continuousOn)).congr e
  have haT : a ω '' Icc 0 θ ⊆ Icc 0 (a ω (T ω)) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨?_, hown.mono.monotoneOn (hJ ht) ⟨(hown.pos).le, le_rfl⟩ (hJ ht).2⟩
    rw [← hown.a0]; exact hown.mono.monotoneOn ⟨le_rfl, hown.pos.le⟩ (hJ ht) ht.1
  have hγ := (hH.d9 ω).g0
  have hne : ∀ E : ℝ, γ ≤ |E| → E ≠ 0 := fun E hE h0 => by rw [h0, abs_zero] at hE; linarith
  have hgc : ContinuousOn (imgDrift κ rr (W' ω) ζ₀ ζ) (a ω '' Icc 0 θ) := by
    have h0 := (hcV ζ₀ v₀ hv₀).mono haT
    have hm := fun m => (hcV (ζ m) _ (hv m)).mono haT
    have hW := hown.contW'.continuousOn (s := a ω '' Icc 0 θ)
    unfold imgDrift
    refine (continuousOn_const.div (continuousOn_const.mul (hW.sub h0)) ?_).neg.add
      (continuousOn_finsetSum _ fun m _ => continuousOn_const.div (hW.sub (hm m)) ?_)
    · rintro _ ⟨t, ht, rfl⟩
      have e : W' ω (a ω t) - imgV (W' ω) ζ₀ (a ω t) = d.A 0 t - d.A20 t := by
        have hA0 : d.A 0 t = W' ω (a ω t) := hown.frzA_zero (hJ ht)
        rw [hA0]; rfl
      show (2 : ℝ) * (W' ω (a ω t) - imgV (W' ω) ζ₀ (a ω t)) ≠ 0
      rw [e]
      exact mul_ne_zero two_ne_zero (hne _ (by rw [abs_sub_comm]; exact ((hH.d9 ω).E0 t (hJ ht)).1))
    · rintro _ ⟨t, ht, rfl⟩
      have e : W' ω (a ω t) - imgV (W' ω) (ζ m) (a ω t) = d.A 0 t - d.B0 t m := by
        have hA0 : d.A 0 t = W' ω (a ω t) := hown.frzA_zero (hJ ht)
        rw [hA0]; rfl
      show W' ω (a ω t) - imgV (W' ω) (ζ m) (a ω t) ≠ 0
      rw [e]
      exact hne _ (by rw [abs_sub_comm]; exact ((hH.d9 ω).Em t (hJ ht) m).1)
  have hder : ∀ x ∈ Ioo (min 0 θ) (max 0 θ), HasDerivWithinAt (a ω) (frzA d.W d.W' d.a d.φ 1 x ^ 2) (Ioi x) x := by
    intro x hx
    rw [min_eq_left hθ.1, max_eq_right hθ.1] at hx
    have hx' : x ∈ Icc (0 : ℝ) (T ω) := ⟨hx.1.le, hx.2.le.trans hθ.2⟩
    have hnhds : Icc (0 : ℝ) (T ω) ∈ 𝓝 x := Icc_mem_nhds hx.1 (lt_of_lt_of_le hx.2 hθ.2)
    exact ((hown.hasDerivWithinAt_clock hx').1.hasDerivAt hnhds).hasDerivWithinAt
  have hcA : ContinuousOn (a ω) (Icc 0 (T ω)) := hown.contA
  have hsub := intervalIntegral.integral_comp_mul_deriv'' (a := 0) (b := θ)
    (hcA.mono (by rw [huI]; exact hJ)) hder
    ((((hown.continuousOn_frzA 1).pow 2)).mono (by rw [huI]; exact hJ)) (by rw [huI]; exact hgc)
  rw [intervalIntegral.integral_congr hEq, hsub, show a ω 0 = 0 from hown.a0]

/-- **(D10) in the capacity time, force-point form** (§A.1.3): for `N ≥ Tmax` and every `ν`,

  `exp(ν B̃_u − (ν²/2)(u ∧ a(S)))`, `√κ B̃_u = W'(u ∧ a(S)) − W'(0) − ∫₀^{u∧a(S)} (−κ/(2(W' − Ṽ₀)) + Σ ρ_m/(W' − Ṽ_m))`,

is a `Q`-martingale of the time-changed filtration `𝓗_u = 𝓕_{τ_u}`: the image driver `W'` solves the force-point
equation driven by the `Q`-Brownian motion `B̃` of `𝓗` (stopped at `a(S)`) — Lévy's characterization in exponential
form. -/
theorem martingale_d10_imgDrift {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (ν : ℝ) {N : ℝ≥0}
    (hN : Tmax ≤ N) :
    Martingale (fun (u : ℝ≥0) ω => Real.exp (ν / Real.sqrt κ * (W' ω (min (u : ℝ) (a ω (S ω))) - W' ω 0 -
        ∫ v in (0 : ℝ)..min (u : ℝ) (a ω (S ω)), imgDrift κ rr (W' ω) ζ₀ ζ v) -
        ν ^ 2 / 2 * min (u : ℝ) (a ω (S ω))))
      (Zhan.Retarget.timeChangeFilt 𝓕 (hH.isStoppingTime_invImgClk (fun u => hB.2.1 u) hBc hS)
        (invClock_mono hH.continuous_imgClk hH.monotone_imgClk))
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) := by
  have h := hH.martingale_d10_timeChange' hκ hB hBc hS ν hN
  have e : ∀ (u : ℝ≥0) ω, ∫ v in (0 : ℝ)..d10Theta a S N u ω, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).d10Rate v =
      ∫ v in (0 : ℝ)..min (u : ℝ) (a ω (S ω)), imgDrift κ rr (W' ω) ζ₀ ζ v := fun u ω => by
    have hmem : d10Theta a S N u ω ∈ Icc (0 : ℝ) (T ω) := hH.mem_Icc_min _ ω
    rw [hH.d10Int_eq_imgDrift ω hmem, hH.a_d10Theta hN u ω]
  simp only [e] at h
  exact h

end FrzD10Hyp

end Frozen

end InteractingSLE.ZhanGT4
