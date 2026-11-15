/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTimeChange

/-!
# (D10), IV: Lévy's characterization after the capacity time change (generic part)

Packet PROVE-ZHAN-GT4-A10. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L353–L355, R38): "The
time change `du = A²_{j,1} dt_j`, Lévy's characterization …".

* `setIntegral_mul_wald_eq_of_stopped` (PROVE-ZHAN-GT4-A9's `setIntegral_girsR_mul_wald_eq` with an abstract factor):
  if `R` is bounded, adapted, progressive and frozen after a stopping time `S`, and `R_t E_{t∧S}` is a martingale for the
  Wald exponential `E = exp(aB − a²t/2)` of a Brownian motion `B`, then so is `R_t E_t`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-! ### Splicing a stopped factor with the Wald exponential -/

section Splice

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}

/-- **Splicing at a stopping time**: for a bounded adapted progressive `R` frozen after `S` (`R_{t∧S} = R_t`) such that
`R_t E_{t∧S}` has the martingale property, `∫_A R_t E_t = ∫_A R_s E_s` for `A ∈ 𝓕_s`, `s ≤ t`, where `E = wald a B`. -/
theorem setIntegral_mul_wald_eq_of_stopped {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (a : ℝ)
    {Rr : ℝ≥0 → Ω → ℝ} {CR : ℝ} (hRb : ∀ u ω, |Rr u ω| ≤ CR) (hRad : ∀ u, Measurable[𝓕 u] (Rr u))
    (hRp : IsStronglyProgressive 𝓕 Rr) (hRmin : ∀ u ω, Rr (min u (S ω)) ω = Rr u ω)
    (h1 : ∀ {s t : ℝ≥0}, s ≤ t → ∀ {A : Set Ω}, MeasurableSet[𝓕 s] A →
      ∫ ω in A, Rr t ω * wald a B (min t (S ω)) ω ∂P = ∫ ω in A, Rr s ω * wald a B (min s (S ω)) ω ∂P)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓕 s] A) :
    ∫ ω in A, Rr t ω * wald a B t ω ∂P = ∫ ω in A, Rr s ω * wald a B s ω ∂P := by
  have hP := hB.isProbabilityMeasure'
  have hAm : MeasurableSet A := 𝓕.le s A hA
  set E := wald a B with hEdef
  have hRm : ∀ u, Measurable (Rr u) := fun u => (hRad u).mono (𝓕.le u) le_rfl
  have hM : Martingale E 𝓕 P := martingale_wald hB a
  have hMrc : ∀ ω u, ContinuousWithinAt (E · ω) (Ici u) u := fun ω u =>
    (continuous_wald hBc a ω).continuousWithinAt
  have hτ : ∀ u : ℝ≥0, IsStoppingTime 𝓕 fun ω => ((min u (S ω) : ℝ≥0) : WithTop ℝ≥0) := fun u => by
    simpa only [WithTop.coe_min] using (isStoppingTime_const 𝓕 u).min hS
  have hEτi : ∀ u : ℝ≥0, Integrable (fun ω => E (min u (S ω)) ω) P := fun u =>
    (tendsto_lintegral_stoppedValue_dyadicUpperTime hM.supermartingale hMrc (hτ u) (T := u)
      (fun ω => WithTop.coe_le_coe.2 (min_le_left _ _))).2.1
  have hEi : ∀ u, Integrable (E u) P := fun u => hM.integrable u
  have hRE : ∀ u (f : Ω → ℝ), Integrable f P → Integrable (fun ω => Rr u ω * f ω) P := fun u f hf =>
    hf.bdd_mul (c := CR) (hRm u).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hRb u ω)
  have hgt : MeasurableSet[𝓕 s] {ω | s < S ω} := by
    have h := (measurableSet_le_of_isStoppingTime hS s).compl
    have he : {ω | S ω ≤ s}ᶜ = {ω | s < S ω} := by ext ω; simp
    rwa [he] at h
  have hint : ∀ u : ℝ≥0, Integrable (fun ω => Rr u ω * (E u ω - E (min u (S ω)) ω)) P := fun u => by
    simp only [mul_sub]; exact (hRE u _ (hEi u)).sub (hRE u _ (hEτi u))
  have h2 : ∫ ω in A, Rr t ω * (E t ω - E (min t (S ω)) ω) ∂P =
      ∫ ω in A, Rr s ω * (E s ω - E (min s (S ω)) ω) ∂P := by
    rw [← integral_inter_add_sdiff (𝓕.le s _ hgt) (hint t).integrableOn,
      ← integral_inter_add_sdiff (𝓕.le s _ hgt) (hint s).integrableOn]
    congr 1
    · -- on `A ∩ {s < S}`: optional sampling at `t ∧ S`
      have hA₂ : MeasurableSet[𝓕 s] (A ∩ {ω | s < S ω}) := hA.inter hgt
      have hA₂m : MeasurableSet (A ∩ {ω | s < S ω}) := 𝓕.le s _ hA₂
      have hz : ∫ ω in A ∩ {ω | s < S ω}, Rr s ω * (E s ω - E (min s (S ω)) ω) ∂P = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun ω hω => by rw [min_eq_left hω.2.le, sub_self, mul_zero]
      rw [hz]
      have hA₂τ : MeasurableSet[(hτ t).measurableSpace] (A ∩ {ω | s < S ω}) := by
        refine ⟨(le_iSup (fun u => (𝓕 u : MeasurableSpace Ω)) s) _ hA₂, fun i => ?_⟩
        by_cases hsi : s ≤ i
        · exact (𝓕.mono hsi _ hA₂).inter ((hτ t) i)
        · have h : A ∩ {ω | s < S ω} ∩ {ω | ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0) ≤ i} = ∅ := by
            refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
            obtain ⟨⟨_, hsS⟩, hmin⟩ := hω
            have hmin' : min t (S ω) ≤ i := WithTop.coe_le_coe.1 hmin
            have : s ≤ min t (S ω) := le_min hst hsS.le
            exact hsi (this.trans hmin')
          rw [h]
          exact @MeasurableSet.empty _ (𝓕 i)
      set G := (A ∩ {ω | s < S ω}).indicator (fun ω => Rr t ω) with hGdef
      have hGm : StronglyMeasurable[(hτ t).measurableSpace] G := by
        have hsv := measurable_stoppedValue (hRp) (hτ t)
        have e : stoppedValue Rr (fun ω => ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0)) = Rr t := by
          funext ω; exact hRmin t ω
        rw [e] at hsv
        exact (hsv.indicator hA₂τ).stronglyMeasurable
      have hGb : ∀ ω, |G ω| ≤ CR := fun ω => by
        by_cases hω : ω ∈ A ∩ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω]; exact hRb t ω
        · rw [hGdef, indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hRb t ω)
      have hos := Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hM hMrc (hτ t)
        (isStoppingTime_const 𝓕 t) (fun ω => WithTop.coe_le_coe.2 (min_le_left _ _)) (T := t) (fun ω => le_rfl)
      have key := integral_mul_eq_of_ae_eq_condExp ((hτ t).measurableSpace_le) hos (hEi t) hGm hGb
      have eG : ∀ f : Ω → ℝ, ∫ ω, G ω * f ω ∂P = ∫ ω in A ∩ {ω | s < S ω}, Rr t ω * f ω ∂P := fun f => by
        rw [← integral_indicator hA₂m]
        congr 1; funext ω
        by_cases hω : ω ∈ A ∩ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω, indicator_of_mem hω]
        · rw [hGdef, indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
      have key' : ∫ ω in A ∩ {ω | s < S ω}, Rr t ω * E (min t (S ω)) ω ∂P =
          ∫ ω in A ∩ {ω | s < S ω}, Rr t ω * E t ω ∂P := by
        rw [← eG, ← eG]; exact key
      simp only [mul_sub]
      rw [integral_sub (hRE t _ (hEi t)).integrableOn (hRE t _ (hEτi t)).integrableOn, key', sub_self]
    · -- on `A \ {s < S}`: `S ≤ s`, a martingale step of `E` from `s` to `t`
      have hA₁ : MeasurableSet[𝓕 s] (A \ {ω | s < S ω}) := hA.diff hgt
      have hA₁m : MeasurableSet (A \ {ω | s < S ω}) := 𝓕.le s _ hA₁
      have hcongr : ∫ ω in A \ {ω | s < S ω}, Rr t ω * (E t ω - E (min t (S ω)) ω) ∂P =
          ∫ ω in A \ {ω | s < S ω}, Rr s ω * (E t ω - E (min s (S ω)) ω) ∂P := by
        refine setIntegral_congr_fun hA₁m fun ω hω => ?_
        have hSs : S ω ≤ s := not_lt.1 hω.2
        have hSt : S ω ≤ t := hSs.trans hst
        have hRts : Rr t ω = Rr s ω := by
          rw [← hRmin t ω, ← hRmin s ω, min_eq_right hSt, min_eq_right hSs]
        rw [hRts, min_eq_right hSt, min_eq_right hSs]
      rw [hcongr]
      set G := (A \ {ω | s < S ω}).indicator (fun ω => Rr s ω) with hGdef
      have hGm : StronglyMeasurable[𝓕 s] G :=
        ((hRad s).indicator hA₁).stronglyMeasurable
      have hGb : ∀ ω, |G ω| ≤ CR := fun ω => by
        by_cases hω : ω ∈ A \ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω]; exact hRb s ω
        · rw [hGdef, indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hRb s ω)
      have key := integral_mul_eq_of_ae_eq_condExp (𝓕.le s) (hM.condExp_ae_eq hst).symm (hEi t) hGm hGb
      have eG : ∀ f : Ω → ℝ, ∫ ω, G ω * f ω ∂P = ∫ ω in A \ {ω | s < S ω}, Rr s ω * f ω ∂P := fun f => by
        rw [← integral_indicator hA₁m]
        congr 1; funext ω
        by_cases hω : ω ∈ A \ {ω | s < S ω}
        · rw [hGdef, indicator_of_mem hω, indicator_of_mem hω]
        · rw [hGdef, indicator_of_notMem hω, indicator_of_notMem hω, zero_mul]
      have key' : ∫ ω in A \ {ω | s < S ω}, Rr s ω * E s ω ∂P = ∫ ω in A \ {ω | s < S ω}, Rr s ω * E t ω ∂P := by
        rw [← eG, ← eG]; exact key
      simp only [mul_sub]
      rw [integral_sub (hRE s _ (hEi t)).integrableOn (hRE s _ (hEτi s)).integrableOn,
        integral_sub (hRE s _ (hEi s)).integrableOn (hRE s _ (hEτi s)).integrableOn, key']
  -- assembly
  have e : ∀ u : ℝ≥0, ∫ ω in A, Rr u ω * E u ω ∂P =
      ∫ ω in A, Rr u ω * E (min u (S ω)) ω ∂P + ∫ ω in A, Rr u ω * (E u ω - E (min u (S ω)) ω) ∂P := fun u => by
    rw [← integral_add (hRE u _ (hEτi u)).integrableOn (hint u).integrableOn]
    congr 1; funext ω; ring
  rw [e t, e s, h1 hst hA, h2]

end Splice

/-! ### The inverse of a strictly increasing clock with linear growth -/

section Inverse

variable {Ω : Type*} {C : Ω → ℝ≥0 → ℝ} {c : ℝ}

/-- **The finite value of the inverse clock** (`τ_u` as an element of `ℝ≥0`). -/
def invClockT (C : Ω → ℝ≥0 → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ≥0 := (invClock C u ω).untopA

/-- For a continuous clock with `C_0 = 0` and `C_r ≥ c r`, the inverse clock is finite, `C_{τ_u} = u` and `τ_u ≤ u/c`. -/
theorem invClock_eq_coe (hCc : ∀ ω, Continuous (C ω)) (hC0 : ∀ ω, C ω 0 = 0) (hc : 0 < c)
    (hClb : ∀ ω r, c * r ≤ C ω r) (u : ℝ≥0) (ω : Ω) :
    invClock C u ω = invClockT C u ω ∧ C ω (invClockT C u ω) = u ∧ invClockT C u ω ≤ ((u : ℝ) / c).toNNReal := by
  have hr : (u : ℝ) ≤ C ω ((u : ℝ) / c).toNNReal := by
    have := hClb ω ((u : ℝ) / c).toNNReal
    rw [Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hc.le), mul_div_cancel₀ _ hc.ne'] at this
    exact this
  obtain ⟨θ, hθ, hCθ, hθr⟩ := exists_invClock_eq hCc (by rw [hC0]; exact u.coe_nonneg) hr
  have hT : invClockT C u ω = θ := by
    simp only [invClockT, hθ, WithTop.untopA, WithTop.untopD_coe]
  rw [hT]
  exact ⟨hθ, hCθ, hθr⟩

/-- **The inverse of a strictly increasing clock is continuous** (monotone and onto). -/
theorem continuous_invClockT (hCc : ∀ ω, Continuous (C ω)) (hCs : ∀ ω, StrictMono (C ω))
    (hC0 : ∀ ω, C ω 0 = 0) (hc : 0 < c) (hClb : ∀ ω r, c * r ≤ C ω r) (ω : Ω) :
    Continuous fun u => invClockT C u ω := by
  apply Monotone.continuous_of_surjective
  · intro u v huv
    have h := invClock_mono hCc (fun ω => (hCs ω).monotone) u v huv ω
    rw [(invClock_eq_coe hCc hC0 hc hClb u ω).1, (invClock_eq_coe hCc hC0 hc hClb v ω).1] at h
    exact WithTop.coe_le_coe.1 h
  · intro r
    refine ⟨(C ω r).toNNReal, ?_⟩
    have hCr0 : 0 ≤ C ω r := by rw [← hC0 ω]; exact (hCs ω).monotone zero_le
    have h2 := (invClock_eq_coe hCc hC0 hc hClb (C ω r).toNNReal ω).2.1
    rw [Real.coe_toNNReal _ hCr0] at h2
    exact (hCs ω).injective h2

end Inverse

/-! ### Lévy's characterization after a time change -/

section Levy

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {Y : ℝ≥0 → Ω → ℝ} {C : Ω → ℝ≥0 → ℝ} {c : ℝ}

/-- **Lévy's characterization after a time change** (the exponential form of Dambis–Dubins–Schwarz): let `Y` be a
continuous adapted process with `Y_0 = 0` and `C` a continuous adapted strictly increasing clock with `C_0 = 0` and
`C_r ≥ c r` (`c > 0`), such that `exp(νY_t − ν²C_t/2)` is a `Q`-martingale for every `ν`. Then `B̂_u = Y_{τ_u}`,
`τ_u = C⁻¹(u)`, is a Brownian motion of the time-changed filtration `𝓗_u = 𝓕_{τ_u}`. -/
theorem isFilteredBrownianReal_timeChange (hYc : ∀ ω, Continuous (Y · ω)) (hYm : ∀ t, Measurable[𝓕 t] (Y t))
    (hY0 : ∀ ω, Y 0 ω = 0) (hCc : ∀ ω, Continuous (C ω)) (hCs : ∀ ω, StrictMono (C ω)) (hC0 : ∀ ω, C ω 0 = 0)
    (hc : 0 < c) (hClb : ∀ ω r, c * r ≤ C ω r) (hCm : ∀ r : ℝ≥0, Measurable[𝓕 r] fun ω => C ω r)
    (hZ : ∀ ν : ℝ, Martingale (fun t ω => Real.exp (ν * Y t ω - ν ^ 2 * C ω t / 2)) 𝓕 Q) :
    IsFilteredBrownianReal
      (Zhan.Retarget.timeChangeFilt 𝓕 (isStoppingTime_invClock hCc (fun ω => (hCs ω).monotone) hCm)
        (invClock_mono hCc fun ω => (hCs ω).monotone))
      (fun u ω => Y (invClockT C u ω) ω) Q := by
  have hCmo : ∀ ω, Monotone (C ω) := fun ω => (hCs ω).monotone
  have hτ := isStoppingTime_invClock hCc hCmo hCm
  have hmono := invClock_mono hCc hCmo
  have hval := fun u ω => invClock_eq_coe hCc hC0 hc hClb u ω
  have hYp : IsStronglyProgressive 𝓕 Y :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun t => (hYm t).stronglyMeasurable) hYc
  have hsv : ∀ u, (fun ω => Y (invClockT C u ω) ω) = stoppedValue Y (invClock C u) := fun u => rfl
  have hadapt : StronglyAdapted (Zhan.Retarget.timeChangeFilt 𝓕 hτ hmono) fun u ω => Y (invClockT C u ω) ω :=
    fun u => by
      show StronglyMeasurable[(hτ u).measurableSpace] (fun ω => Y (invClockT C u ω) ω)
      rw [hsv u]
      exact (measurable_stoppedValue hYp (hτ u)).stronglyMeasurable
  have hcont : ∀ ω, Continuous fun u => Y (invClockT C u ω) ω := fun ω =>
    (hYc ω).comp (continuous_invClockT hCc hCs hC0 hc hClb ω)
  have hall : ∀ T, MathFin.IsExpQMartingale Q (Zhan.Retarget.timeChangeFilt 𝓕 hτ hmono)
      (fun u ω => Y (invClockT C u ω) ω) T := by
    intro T
    refine ⟨hadapt, ?_, fun a s t hst _ A hA => ?_⟩
    · refine Eventually.of_forall fun ω => ?_
      have h0 : invClockT C 0 ω = 0 := by
        have := (hval 0 ω).2.2
        simpa using this
      simp only [h0, hY0, Pi.zero_apply]
    · have hZrc : ∀ ω t, ContinuousWithinAt (fun t => Real.exp (a * Y t ω - a ^ 2 * C ω t / 2)) (Ici t) t :=
        fun ω t => by
          have h1 := hYc ω
          have h2 := hCc ω
          exact (by fun_prop : Continuous fun t => Real.exp (a * Y t ω - a ^ 2 * C ω t / 2)).continuousWithinAt
      have hle : invClock C s ≤ invClock C t := fun ω => hmono s t hst ω
      have hτT : ∀ ω, invClock C t ω ≤ (((t : ℝ) / c).toNNReal : WithTop ℝ≥0) := fun ω => by
        rw [(hval t ω).1]; exact WithTop.coe_le_coe.2 (hval t ω).2.2
      have hOS := setIntegral_stoppedValue_eq_of_rightContinuous (hZ a) hZrc (hτ s) (hτ t) hle hτT hA
      have e : ∀ u : ℝ≥0, stoppedValue (fun t ω => Real.exp (a * Y t ω - a ^ 2 * C ω t / 2)) (invClock C u) =
          fun ω => Real.exp (a * Y (invClockT C u ω) ω - a ^ 2 * (u : ℝ) / 2) := fun u => by
        funext ω
        show Real.exp (a * Y (invClockT C u ω) ω - a ^ 2 * C ω (invClockT C u ω) / 2) = _
        rw [(hval u ω).2.1]
      rw [e s, e t] at hOS
      exact hOS.symm
  exact ⟨MathFin.isBrownianReal_of_expMartingale hall (ae_of_all _ hcont), hadapt.adapted,
    (MathFin.isFilteredPreBrownian_of_expMartingale hall).indep⟩

end Levy

end InteractingSLE.ZhanGT4
