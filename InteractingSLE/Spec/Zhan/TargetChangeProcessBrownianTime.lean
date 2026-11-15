/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianMart

/-!
# `b̃` is a Brownian motion, part 4: the time change

Packet PROVE-SEC7-C9. The new clock `S(t) = C(t)` is continuous and strictly increasing on `[0, τ_sep)`, with
supremum the new horizon `T̃`. Its inverse `newT u = C⁻¹(u)` (`u < T̃`; `τ_sep` from `T̃` on; `0` off the good event)
is a stopping time of the usual augmentation `𝓖` for every `u` (`isStoppingTime_newT`): on the good event
`newT u ≤ r` iff `τ_sep ≤ r` or `u ≤ C(r ∧ σ_n)` for some `n`. The new filtration is `𝓗_u = 𝓖_{newT u}`
(`timeChangeFilt`).

A bounded continuous `𝓖`-martingale that is constant after a fixed time, read at `newT u`, is an `𝓗`-martingale
(`martingale_comp_timeChange`, optional sampling at possibly infinite stopping times, `setIntegral_capTime_eq`).
Applied to the localized martingales of part 3: at the new time `u`, the original time `newT u ∧ σ_m` is
`C⁻¹(u ∧ S_m)` with `S_m = C(σ_m)` (`min_capTime_newT_rLoc`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### Optional sampling for frozen martingales at possibly infinite stopping times -/

section Frozen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Optional sampling at possibly infinite stopping times, capped at `N`**, for a bounded continuous martingale,
at the times: `∫_A M_{τ₂ ∧ N} = ∫_A M_{τ₁ ∧ N}` for `τ₁ ≤ τ₂` and `A ∈ 𝓖_{τ₁}`. -/
theorem setIntegral_capTime_eq [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓖 P) (hMc : ∀ ω, Continuous (M · ω)) {C : ℝ} (hMb : ∀ r ω, |M r ω| ≤ C)
    (N : ℝ≥0) {τ₁ τ₂ : Ω → WithTop ℝ≥0}
    (h1 : IsStoppingTime 𝓖 τ₁) (h2 : IsStoppingTime 𝓖 τ₂) (h12 : ∀ ω, τ₁ ω ≤ τ₂ ω) {A : Set Ω}
    (hA : MeasurableSet[h1.measurableSpace] A) :
    ∫ ω in A, M (Sec2.TwoSeed.capTime (fun _ => N) τ₂ ω) ω ∂P =
      ∫ ω in A, M (Sec2.TwoSeed.capTime (fun _ => N) τ₁ ω) ω ∂P := by
  have hN := isStoppingTime_const 𝓖 N
  have hprog : IsStronglyProgressive 𝓖 M :=
    StronglyAdapted.isStronglyProgressive_of_continuous hM.stronglyAdapted hMc
  have hAm : MeasurableSet A := h1.measurableSpace_le A hA
  have hc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ →
      IsStoppingTime 𝓖 fun ω => (Sec2.TwoSeed.capTime (fun _ => N) τ ω : WithTop ℝ≥0) :=
    fun τ hτ => Sec2.TwoSeed.isStoppingTime_capTime hN hτ
  have hsv : ∀ τ : Ω → WithTop ℝ≥0, stoppedValue M
      (fun ω => (Sec2.TwoSeed.capTime (fun _ => N) τ ω : WithTop ℝ≥0)) =
      fun ω => M (Sec2.TwoSeed.capTime (fun _ => N) τ ω) ω := fun τ => by
    funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
  have hmeas : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ →
      Measurable fun ω => M (Sec2.TwoSeed.capTime (fun _ => N) τ ω) ω := fun τ hτ => by
    have h := (measurable_stoppedValue hprog (hc τ hτ)).mono (hc τ hτ).measurableSpace_le le_rfl
    rwa [hsv τ] at h
  have hint : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ →
      IntegrableOn (fun ω => M (Sec2.TwoSeed.capTime (fun _ => N) τ ω) ω) A P := fun τ hτ =>
    (Integrable.of_bound (hmeas τ hτ).aestronglyMeasurable C (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hMb _ ω)).integrableOn
  set S : Set Ω := {ω | τ₁ ω ≤ (N : WithTop ℝ≥0)} with hSdef
  have hSm : MeasurableSet S := measurableSet_le h1.measurable' measurable_const
  -- on `A ∩ S`: optional sampling at the bounded times `τᵢ ∧ N`
  have hA1 : MeasurableSet[(h1.min hN).measurableSpace] (A ∩ S) :=
    IsStoppingTime.measurableSet_inter_le h1 hN A hA
  have hcoe : ∀ τ : Ω → WithTop ℝ≥0, (fun ω => (Sec2.TwoSeed.capTime (fun _ => N) τ ω : WithTop ℝ≥0)) =
      fun ω => min (τ ω) (N : WithTop ℝ≥0) := fun τ => by
    funext ω; rw [Sec2.TwoSeed.coe_capTime, min_comm]
  have hle : (fun ω => min (τ₁ ω) (N : WithTop ℝ≥0)) ≤ fun ω => min (τ₂ ω) (N : WithTop ℝ≥0) :=
    fun ω => min_le_min (h12 ω) le_rfl
  have hOS := setIntegral_stoppedValue_eq_of_rightContinuous hM
    (fun ω t => (hMc ω).continuousWithinAt) (h1.min hN) (h2.min hN) hle
    (T := N) (fun ω => min_le_right _ _) hA1
  rw [← hcoe τ₁, ← hcoe τ₂, hsv, hsv] at hOS
  -- on `A \ S`: both times exceed `N`
  have hdiff : ∫ ω in A \ S, M (Sec2.TwoSeed.capTime (fun _ => N) τ₂ ω) ω ∂P =
      ∫ ω in A \ S, M (Sec2.TwoSeed.capTime (fun _ => N) τ₁ ω) ω ∂P := by
    refine setIntegral_congr_fun (hAm.diff hSm) fun ω hω => ?_
    have h1N : (N : WithTop ℝ≥0) < τ₁ ω := by
      have := hω.2
      simp only [hSdef, mem_ofPred_eq, not_le] at this
      exact this
    have e1 : Sec2.TwoSeed.capTime (fun _ => N) τ₁ ω = N := Sec2.TwoSeed.capTime_eq_of_le h1N.le
    have e2 : Sec2.TwoSeed.capTime (fun _ => N) τ₂ ω = N :=
      Sec2.TwoSeed.capTime_eq_of_le (h1N.le.trans (h12 ω))
    simp only [e1, e2]
  rw [← integral_inter_add_sdiff hSm (hint τ₂ h2), ← integral_inter_add_sdiff hSm (hint τ₁ h1), hOS,
    hdiff]

/-- **The time-changed filtration** `u ↦ 𝓖_{τ u}` of a nondecreasing family of stopping times. -/
def timeChangeFilt (𝓖 : Filtration ℝ≥0 mΩ) {τ : ℝ≥0 → Ω → WithTop ℝ≥0} (hτ : ∀ u, IsStoppingTime 𝓖 (τ u))
    (hmono : ∀ u v, u ≤ v → ∀ ω, τ u ω ≤ τ v ω) : Filtration ℝ≥0 mΩ where
  seq u := (hτ u).measurableSpace
  mono' u v huv := IsStoppingTime.measurableSpace_mono _ _ fun ω => hmono u v huv ω
  le' u := (hτ u).measurableSpace_le

theorem timeChangeFilt_apply (𝓖 : Filtration ℝ≥0 mΩ) {τ : ℝ≥0 → Ω → WithTop ℝ≥0}
    (hτ : ∀ u, IsStoppingTime 𝓖 (τ u)) (hmono : ∀ u v, u ≤ v → ∀ ω, τ u ω ≤ τ v ω) (u : ℝ≥0) :
    timeChangeFilt 𝓖 hτ hmono u = (hτ u).measurableSpace := rfl

/-- **A frozen bounded continuous martingale read at a time change is a martingale of the time-changed
filtration** (affine images included). -/
theorem martingale_comp_timeChange [IsFiniteMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
    {τ : ℝ≥0 → Ω → WithTop ℝ≥0} (hτ : ∀ u, IsStoppingTime 𝓖 (τ u))
    (hmono : ∀ u v, u ≤ v → ∀ ω, τ u ω ≤ τ v ω) {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 P)
    (hMc : ∀ ω, Continuous (M · ω)) {C : ℝ} (hMb : ∀ r ω, |M r ω| ≤ C) (N : ℝ≥0) (c d : ℝ) :
    Martingale (fun u ω => c * M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω + d)
      (timeChangeFilt 𝓖 hτ hmono) P := by
  have hprog : IsStronglyProgressive 𝓖 M :=
    StronglyAdapted.isStronglyProgressive_of_continuous hM.stronglyAdapted hMc
  have hN := isStoppingTime_const 𝓖 N
  have hmeas : ∀ u, Measurable[timeChangeFilt 𝓖 hτ hmono u] fun ω =>
      M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω := by
    intro u
    have hc := Sec2.TwoSeed.isStoppingTime_capTime hN (hτ u)
    have h := measurable_stoppedValue hprog hc
    have e : stoppedValue M (fun ω => (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω : WithTop ℝ≥0)) =
        fun ω => M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω := by
      funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
    rw [e] at h
    rw [timeChangeFilt_apply]
    refine h.mono (IsStoppingTime.measurableSpace_mono hc (hτ u) fun ω => ?_) le_rfl
    exact Sec2.TwoSeed.capTime_le_right _ _ ω
  have hadapt : StronglyAdapted (timeChangeFilt 𝓖 hτ hmono) fun u ω =>
      c * M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω + d :=
    fun u => (((hmeas u).const_mul c).add_const d).stronglyMeasurable
  have hint : ∀ u, Integrable (fun ω => c * M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω + d) P := fun u =>
    Integrable.of_bound ((hadapt u).mono ((timeChangeFilt 𝓖 hτ hmono).le u)).aestronglyMeasurable
      (|c| * C + |d|) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        calc |c * M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω + d|
            ≤ |c * M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω| + |d| := abs_add_le _ _
          _ ≤ |c| * C + |d| := by
            rw [abs_mul]; gcongr; exact hMb _ ω)
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((timeChangeFilt 𝓖 hτ hmono).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    ((hadapt s).mono le_rfl).aestronglyMeasurable).symm
  have hMint : ∀ u, Integrable (fun ω => M (Sec2.TwoSeed.capTime (fun _ => N) (τ u) ω) ω) P := fun u =>
    Integrable.of_bound ((hmeas u).mono ((timeChangeFilt 𝓖 hτ hmono).le u) le_rfl).aestronglyMeasurable
      C (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hMb _ ω)
  have hOS := setIntegral_capTime_eq hM hMc hMb N (hτ s) (hτ t) (fun ω => hmono s t hst ω) (A := A) hA
  rw [integral_add ((hMint t).const_mul c).integrableOn integrableOn_const,
    integral_add ((hMint s).const_mul c).integrableOn integrableOn_const, integral_const_mul,
    integral_const_mul, hOS]

end Frozen

/-! ### The inverse clock along a path -/

section ClockPath

variable {xk : ℝ} {w vk : ℝ≥0 → ℝ} {T : ℝ≥0∞} (h : SepUpTo w vk T) (hxk : 0 < xk)
include h hxk

/-- `C⁻¹(u) ≤ r ↔ u ≤ C(r)` for a new time `u < T̃` and an original time `r < T`. -/
theorem invClk_le_iff {u r : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) (hr : (r : ℝ≥0∞) < T) :
    (invClk (rate xk w vk) u).toNNReal ≤ r ↔ (u : ℝ) ≤ clk (rate xk w vk) r := by
  obtain ⟨S, hST, hR, huS, hmem, hci⟩ := newTime_spec h hxk hu
  set S' : ℝ≥0 := max S r with hS'
  have hS'T : (S' : ℝ≥0∞) < T := by rw [hS', ENNReal.coe_max]; exact max_lt hST hr
  have hR' := (h.isSep_of_lt hS'T).isRate hxk
  have hSS' : (S : ℝ) ≤ S' := by exact_mod_cast le_max_left S r
  have hrS' : (r : ℝ) ≤ S' := by exact_mod_cast le_max_right S r
  have hmem' : invClk (rate xk w vk) u ∈ Icc 0 (S' : ℝ) := ⟨hmem.1, hmem.2.trans hSS'⟩
  rw [Real.toNNReal_le_iff_le_coe, ← hR'.clk_le_clk hmem' ⟨r.coe_nonneg, hrS'⟩, hci]

/-- `r ≤ C⁻¹(u) ↔ C(r) ≤ u` for a new time `u < T̃` and an original time `r < T`. -/
theorem le_invClk_iff {u r : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) (hr : (r : ℝ≥0∞) < T) :
    r ≤ (invClk (rate xk w vk) u).toNNReal ↔ clk (rate xk w vk) r ≤ u := by
  obtain ⟨S, hST, hR, huS, hmem, hci⟩ := newTime_spec h hxk hu
  set S' : ℝ≥0 := max S r with hS'
  have hS'T : (S' : ℝ≥0∞) < T := by rw [hS', ENNReal.coe_max]; exact max_lt hST hr
  have hR' := (h.isSep_of_lt hS'T).isRate hxk
  have hSS' : (S : ℝ) ≤ S' := by exact_mod_cast le_max_left S r
  have hrS' : (r : ℝ) ≤ S' := by exact_mod_cast le_max_right S r
  have hmem' : invClk (rate xk w vk) u ∈ Icc 0 (S' : ℝ) := ⟨hmem.1, hmem.2.trans hSS'⟩
  rw [Real.le_toNNReal_iff_coe_le hmem.1, ← hR'.clk_le_clk ⟨r.coe_nonneg, hrS'⟩ hmem', hci]

/-- The clock of an original time `r < T` is below the new horizon. -/
theorem clk_lt_newHorizon' {r : ℝ≥0} (hr : (r : ℝ≥0∞) < T) :
    0 ≤ clk (rate xk w vk) r ∧ ((clk (rate xk w vk) r).toNNReal : ℝ≥0∞) < newHorizon xk w vk T := by
  have h1 := clk_lt_newHorizon h hxk hr
  have h0 : 0 ≤ clk (rate xk w vk) r := by
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hr with ⟨S', hrS', hS'T⟩
    exact ((h.isSep_of_lt hS'T).isRate hxk).clk_nonneg ⟨r.coe_nonneg, by exact_mod_cast hrS'.le⟩
  refine ⟨h0, ?_⟩
  rwa [ENNReal.ofNNReal_toNNReal]

/-- `C⁻¹(C(r)) = r` for `r < T`. -/
theorem invClk_clk_of_lt {r : ℝ≥0} (hr : (r : ℝ≥0∞) < T) :
    invClk (rate xk w vk) (clk (rate xk w vk) r) = r :=
  ((h.isSep_of_lt hr).isRate hxk).invClk_clk ⟨r.coe_nonneg, le_rfl⟩

/-- `C(C⁻¹(u)) = u` for `u < T̃`. -/
theorem clk_invClk_of_lt {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon xk w vk T) :
    clk (rate xk w vk) (invClk (rate xk w vk) u) = u := by
  obtain ⟨-, -, -, -, -, h'⟩ := newTime_spec h hxk hu
  exact h'

end ClockPath

/-! ### The inverse clock as a process -/

/-- An extended nonnegative real as an element of `WithTop ℝ≥0` (the same type). -/
def toWT (x : ℝ≥0∞) : WithTop ℝ≥0 := x

theorem toWT_le_coe_iff (x : ℝ≥0∞) (r : ℝ≥0) : toWT x ≤ (r : WithTop ℝ≥0) ↔ x ≤ (r : ℝ≥0∞) := Iff.rfl

theorem coe_le_toWT_iff (x : ℝ≥0∞) (r : ℝ≥0) : (r : WithTop ℝ≥0) ≤ toWT x ↔ (r : ℝ≥0∞) ≤ x := Iff.rfl

theorem coe_lt_toWT_iff (x : ℝ≥0∞) (r : ℝ≥0) : (r : WithTop ℝ≥0) < toWT x ↔ (r : ℝ≥0∞) < x := Iff.rfl

section NewT

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL j m : ℕ}

/-- The separation time along `ω`. -/
def sepT (W : ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω)

/-- The new clock rate along `ω`. -/
def rateT (xR : Fin (j + 1 + m) → ℝ) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ℝ → ℝ :=
  rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω)

/-- The new horizon along `ω`. -/
def horT (xR : Fin (j + 1 + m) → ℝ) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  newHorizon (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) (sepT W VR ζ ω)

open scoped Classical in
/-- **The inverse clock** `newT u = C⁻¹(u)` for `u < T̃`, `τ_sep` for `u ≥ T̃`, on the good event (`0` off it). -/
def newT (xR : Fin (j + 1 + m) → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (u : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then
    (if (u : ℝ≥0∞) < horT xR W VR ζ ω then ((invClk (rateT xR W VR ω) u).toNNReal : WithTop ℝ≥0)
      else toWT (sepT W VR ζ ω))
  else 0

/-- The new-time localizing times `S_n = C(σ_n)`. -/
def newS (xR : Fin (j + 1 + m) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (clk (rateT xR W VR ω) (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)).toNNReal

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

section Path

variable {ω : Ω} (hω : IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
  (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)

include hω hD hj in
theorem sepUpTo_of_good : SepUpTo (W · ω) (VR (LP.retargetIdx j m) · ω) (sepT W VR ζ ω) :=
  (retargetData_of_isSLEPathUpTo (hω.1.isSLEPathUpTo (sepTime_le _ _ _)) hD hj
    fun _ ht => lt_of_lt_sepTime ht).sep

include hω hωG hD hj in
theorem rLoc_lt_sepT (n : ℕ) : (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω : ℝ≥0∞) < sepT W VR ζ ω :=
  lt_sepTime_of_le_rLoc hω hωG hD hj le_rfl

include hω hωG hD hj in
/-- On a good path, `τ_sep ≤ r` iff every `σ_n ≤ r`. -/
theorem sepT_le_iff (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hTm : Monotone (T · ω))
    (r : ℝ≥0) : sepT W VR ζ ω ≤ r ↔ ∀ n, rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω ≤ r := by
  constructor
  · intro h n
    exact_mod_cast ((rLoc_lt_sepT hω hωG hD hj n).trans_le h).le
  · intro h
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, hrs, hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    obtain ⟨n₀, hn₀⟩ := exists_forall_le_rLoc hω hωG hD hj hgood hTm hs
    have := (hn₀ n₀ le_rfl).trans (h n₀)
    exact absurd (by exact_mod_cast hrs : r < s) (not_lt.2 this)

include hω hωG hD hj in
theorem newT_le_sepT (u : ℝ≥0) : newT xR G W VR ζ u ω ≤ toWT (sepT W VR ζ ω) := by
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  simp only [newT, hωG, ↓reduceIte]
  by_cases hu : (u : ℝ≥0∞) < horT xR W VR ζ ω
  · simp only [hu, ↓reduceIte]
    exact (coe_le_toWT_iff _ _).2 (invClk_lt (sepUpTo_of_good hω hD hj) hpos hu).le
  · simp only [hu, ↓reduceIte, le_refl]

include hω hωG hD hj in
/-- **On a good path, `newT u ≤ r` iff `τ_sep ≤ r` or `u ≤ C(r ∧ σ_n)` for some `n`.** -/
theorem newT_le_iff (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hTm : Monotone (T · ω))
    (u r : ℝ≥0) : newT xR G W VR ζ u ω ≤ r ↔ sepT W VR ζ ω ≤ r ∨
      ∃ n, (u : ℝ) ≤ clk (rateT xR W VR ω)
        ((min r (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) : ℝ≥0) : ℝ) := by
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hS := sepUpTo_of_good hω hD hj
  constructor
  · intro h
    by_cases hsep : sepT W VR ζ ω ≤ r
    · exact Or.inl hsep
    right
    rw [not_le] at hsep
    simp only [newT, hωG, ↓reduceIte] at h
    by_cases hu : (u : ℝ≥0∞) < horT xR W VR ζ ω
    · simp only [hu, ↓reduceIte] at h
      obtain ⟨s, hrs, hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsep
      obtain ⟨n₀, hn₀⟩ := exists_forall_le_rLoc hω hωG hD hj hgood hTm hs
      refine ⟨n₀, ?_⟩
      have hrσ : r ≤ rLoc (LP.retargetIdx j m) G T W VL VR B ζ n₀ ω :=
        (by exact_mod_cast hrs.le : r ≤ s).trans (hn₀ n₀ le_rfl)
      rw [min_eq_left hrσ]
      exact (invClk_le_iff hS hpos hu hsep).1 (WithTop.coe_le_coe.1 h)
    · simp only [hu, ↓reduceIte] at h
      exact absurd ((toWT_le_coe_iff _ _).1 h) (not_le.2 hsep)
  · rintro (h | ⟨n, hn⟩)
    · exact (newT_le_sepT hω hωG hD hj u).trans ((toWT_le_coe_iff _ _).2 h)
    · set r' := min r (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) with hr'
      have hr'T : (r' : ℝ≥0∞) < sepT W VR ζ ω :=
        lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) (rLoc_lt_sepT hω hωG hD hj n)
      obtain ⟨h0, hlt⟩ := clk_lt_newHorizon' hS hpos hr'T
      have hu : (u : ℝ≥0∞) < horT xR W VR ζ ω := by
        refine lt_of_le_of_lt ?_ hlt
        exact_mod_cast (Real.le_toNNReal_iff_coe_le h0).2 hn
      simp only [newT, hωG, ↓reduceIte, hu]
      exact WithTop.coe_le_coe.2 (((invClk_le_iff hS hpos hu hr'T).2 hn).trans (min_le_left _ _))

include hω hωG hD hj in
theorem newT_mono {u v : ℝ≥0} (huv : u ≤ v) : newT xR G W VR ζ u ω ≤ newT xR G W VR ζ v ω := by
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hS := sepUpTo_of_good hω hD hj
  by_cases hu : (u : ℝ≥0∞) < horT xR W VR ζ ω
  · by_cases hv : (v : ℝ≥0∞) < horT xR W VR ζ ω
    · simp only [newT, hωG, ↓reduceIte, hu, hv]
      refine WithTop.coe_le_coe.2 ((invClk_le_iff hS hpos hu (invClk_lt hS hpos hv)).2 ?_)
      have h0 : 0 ≤ invClk (rateT xR W VR ω) v := by
        obtain ⟨S, _, _, _, hm, _⟩ := newTime_spec hS hpos hv
        exact hm.1
      show (u : ℝ) ≤ clk (rateT xR W VR ω) ((invClk (rateT xR W VR ω) v).toNNReal : ℝ)
      rw [Real.coe_toNNReal _ h0]
      have hc : clk (rateT xR W VR ω) (invClk (rateT xR W VR ω) v) = v := clk_invClk_of_lt hS hpos hv
      rw [hc]
      exact_mod_cast huv
    · have h1 := newT_le_sepT hω hωG hD hj u
      simp only [newT, hωG, ↓reduceIte, hv] at h1 ⊢
      exact h1
  · have hv : ¬ (v : ℝ≥0∞) < horT xR W VR ζ ω := fun hv =>
      hu (lt_of_le_of_lt (by exact_mod_cast huv) hv)
    simp only [newT, hωG, ↓reduceIte, hu, hv, le_refl]

include hω hωG hD hj in
/-- **At the new time `u`, the original time `newT u ∧ σ_n` is `C⁻¹(u ∧ S_n)`.** -/
theorem min_capTime_newT_rLoc (n : ℕ) (u : ℝ≥0) :
    min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ u) ω)
      (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) =
      (invClk (rateT xR W VR ω) (min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)).toNNReal := by
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hS := sepUpTo_of_good hω hD hj
  set σ := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω with hσ
  have hσT : (σ : ℝ≥0∞) < sepT W VR ζ ω := rLoc_lt_sepT hω hωG hD hj n
  have hσn : σ ≤ n := rLoc_le_n n ω
  obtain ⟨h0, hlt⟩ := clk_lt_newHorizon' hS hpos hσT
  have h0' : 0 ≤ clk (rateT xR W VR ω) σ := h0
  have hSn : ((newS xR G T W VL VR B ζ n ω : ℝ≥0) : ℝ) = clk (rateT xR W VR ω) σ := by
    rw [newS, ← hσ, Real.coe_toNNReal _ h0']
  have hinvσ : (invClk (rateT xR W VR ω) (clk (rateT xR W VR ω) σ)).toNNReal = σ := by
    rw [show rateT xR W VR ω = rate (LP.retargetPos xR) (W · ω) (VR (LP.retargetIdx j m) · ω) from rfl,
      invClk_clk_of_lt hS hpos hσT, Real.toNNReal_coe]
  have hcap := Sec2.TwoSeed.coe_capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ u) ω
  by_cases hu : (u : ℝ≥0∞) < horT xR W VR ζ ω
  · simp only [newT, hωG, ↓reduceIte, hu] at hcap
    rw [← WithTop.coe_min] at hcap
    rw [WithTop.coe_inj.1 hcap, min_comm (n : ℝ≥0), min_assoc, min_eq_right hσn]
    by_cases huS : u ≤ newS xR G T W VL VR B ζ n ω
    · rw [min_eq_left huS]
      refine min_eq_left ((invClk_le_iff hS hpos hu hσT).2 ?_)
      show (u : ℝ) ≤ clk (rateT xR W VR ω) σ
      rw [← hSn]; exact_mod_cast huS
    · rw [not_le] at huS
      rw [min_eq_right huS.le, hSn, hinvσ]
      refine min_eq_right ?_
      by_contra hle
      rw [not_le] at hle
      have this : (u : ℝ) ≤ clk (rateT xR W VR ω) σ := (invClk_le_iff hS hpos hu hσT).1 hle.le
      rw [← hSn] at this
      exact absurd (by exact_mod_cast this : u ≤ newS xR G T W VL VR B ζ n ω) (not_le.2 huS)
  · simp only [newT, hωG, ↓reduceIte, hu] at hcap
    have hge : σ ≤ Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ u) ω := by
      rw [← WithTop.coe_le_coe, hcap]
      exact le_min (WithTop.coe_le_coe.2 hσn) ((coe_le_toWT_iff _ _).2 hσT.le)
    have huS : newS xR G T W VL VR B ζ n ω < u := by
      have : ((newS xR G T W VL VR B ζ n ω : ℝ≥0) : ℝ≥0∞) < u := by
        refine lt_of_lt_of_le ?_ (not_lt.1 hu)
        simp only [newS, ← hσ]; exact hlt
      exact_mod_cast this
    rw [min_eq_right hge, min_eq_right huS.le, hSn, hinvσ]

end Path

section Process

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T)
  (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)

include hE hGm hGc hgood hT hD hj in
/-- **The inverse clock is a stopping time of the usual augmentation.** -/
theorem isStoppingTime_newT (u : ℝ≥0) :
    IsStoppingTime (usualAugmentation 𝓕 P) (newT xR G W VR ζ u) := by
  intro r
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) r
  have hσ : ∀ n, MeasurableSet[usualAugmentation 𝓕 P r]
      {ω | rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω ≤ r} := fun n => by
    have := isStoppingTime_rLoc hE hGm hGc hgood hT n (k := LP.retargetIdx j m) r
    simpa only [WithTop.coe_le_coe] using this
  have hA : ∀ n, Measurable[usualAugmentation 𝓕 P r] fun ω =>
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min r (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω).2.2.2.2 :=
    fun n => (measurable_rCoord_stopped hE hGm hGc hgood hT hD hj n r).snd.snd.snd.snd
  have e : {ω | newT xR G W VR ζ u ω ≤ r} = Gᶜ ∪ (G ∩ ((⋂ n, {ω | rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω ≤ r})
      ∪ ⋃ n, {ω | (u : ℝ) ≤ (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min r (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω).2.2.2.2})) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, mem_union, mem_compl_iff, hω, not_true_eq_false, false_or, mem_inter_iff,
        true_and, mem_iInter, mem_iUnion]
      rw [newT_le_iff (hgood ω hω) hω hD hj hgood (hT.2.1 ω) u r,
        sepT_le_iff (hgood ω hω) hω hD hj hgood (hT.2.1 ω) r]
      simp only [rCoord, hω, ↓reduceIte, rCoordAt]
      rfl
    · simp only [newT, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff, not_false_eq_true, true_or,
        iff_true]
      exact_mod_cast (zero_le (a := r))
  rw [e]
  exact hG0.compl.union (hG0.inter ((MeasurableSet.iInter hσ).union
    (MeasurableSet.iUnion fun n => measurableSet_le measurable_const (hA n))))

include hgood hD hj in
theorem newT_mono' (u v : ℝ≥0) (huv : u ≤ v) (ω : Ω) :
    newT xR G W VR ζ u ω ≤ newT xR G W VR ζ v ω := by
  by_cases hω : ω ∈ G
  · exact newT_mono (hgood ω hω) hω hD hj huv
  · simp only [newT, hω, ↓reduceIte, le_refl]

/-- **The new filtration** `𝓗_u = 𝓖_{newT u}`. -/
def filtH : Filtration ℝ≥0 mΩ :=
  timeChangeFilt (usualAugmentation 𝓕 P) (isStoppingTime_newT hE hGm hGc hgood hT hD hj)
    (newT_mono' hgood hD hj)

include hE hGm hGc hgood hT hD hj in
/-- **The new localizing times are stopping times of the new filtration**: `S_n ≤ u ↔ σ_n ≤ newT u`. -/
theorem isStoppingTime_newS (n : ℕ) :
    IsStoppingTime (filtH hE hGm hGc hgood hT hD hj)
      fun ω => (newS xR G T W VL VR B ζ n ω : WithTop ℝ≥0) := by
  intro u
  have hσ := isStoppingTime_rLoc hE hGm hGc hgood hT n (k := LP.retargetIdx j m)
  have hτ := isStoppingTime_newT hE hGm hGc hgood hT hD hj u
  have h := hσ.measurableSet_stopping_time_le hτ
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have e : {ω | (newS xR G T W VL VR B ζ n ω : WithTop ℝ≥0) ≤ u} =
      {ω | (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω : WithTop ℝ≥0) ≤ newT xR G W VR ζ u ω} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    by_cases hω : ω ∈ G
    · have hg := hgood ω hω
      have hS := sepUpTo_of_good hg hD hj
      have hσT := rLoc_lt_sepT hg hω hD hj (T := T) (B := B) (VL := VL) n
      obtain ⟨h0, hlt⟩ := clk_lt_newHorizon' hS hpos hσT
      by_cases hu : (u : ℝ≥0∞) < horT xR W VR ζ ω
      · simp only [newT, hω, ↓reduceIte, hu, WithTop.coe_le_coe]
        have h1 := le_invClk_iff hS hpos hu hσT
        have h2 : newS xR G T W VL VR B ζ n ω ≤ u ↔ clk (rate (LP.retargetPos xR) (W · ω)
            (VR (LP.retargetIdx j m) · ω)) (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω) ≤ u := by
          rw [newS, Real.toNNReal_le_iff_le_coe]; rfl
        exact h2.trans h1.symm
      · simp only [newT, hω, ↓reduceIte, hu]
        refine iff_of_true ?_ ((coe_le_toWT_iff _ _).2 hσT.le)
        have : ((newS xR G T W VL VR B ζ n ω : ℝ≥0) : ℝ≥0∞) < u := lt_of_lt_of_le hlt (not_lt.1 hu)
        exact_mod_cast this.le
    · simp only [newS, rLoc_of_not_mem hω, newT, hω, ↓reduceIte, NNReal.coe_zero, clk_zero,
        Real.toNNReal_zero, zero_le, le_refl, WithTop.coe_zero]
  rw [e]
  exact h

end Process

end NewT

end Retarget

end Zhan

end InteractingSLE
