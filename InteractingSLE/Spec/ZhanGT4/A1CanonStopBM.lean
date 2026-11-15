/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField5Ext
import InteractingSLE.Spec.Coupling.WholeField5Germ
import InteractingSLE.Spec.Sec7.PhaseSelFullLevy
import InteractingSLE.Spec.ZhanGT4.DualGirsanovQ
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# A.1's Brownian bookkeeping: stopped image noises, exhaustion by caps, continuation

Packet PROVE-ZHAN-A1CANON. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (`ig1_followup_proofs.txt` L345–L425, R38:
"The time change `du = A² dt`, Lévy's characterization … identify the claimed conditional image law inside this
rectangle"; "exhaustion, optional sampling, and uniqueness in law extend (D10) to first contact"), follow-up 4 §2.5
(L841–L847, R71: "The finite-rectangle identities apply first to capped stopping prefixes; their limits are taken on
the same stopped history spaces"), follow-up 5 §1.3 (L203–L222, R73: "Countable protected-rectangle exhaustion gives
the law up to first contact").

Inside one protected rectangle the conditional image noise is a Brownian motion only up to the image of the rectangle
exit (its *cap*). This file patches the caps of a countable family and continues the noise after their supremum by an
independent Brownian motion, generically:

* `stopExp a N S`: the Wald exponential `exp(a N_{t∧S} − a²(t∧S)/2)`; `IsStoppedBM P 𝓗 N S`: it is a `𝓗`-martingale
  for every `a` (`N` is a Brownian motion stopped at `S`, exponential form);
* **`isStoppedBM_of_agree`**: if `N` agrees up to `S` with a Brownian motion `B` of a filtration `𝓖` that agrees with
  `𝓗` before `S` (the rectangle's own filtration), then `N` is a `𝓗`-Brownian motion stopped at `S`;
* `IsStoppedBM.max`, `isStoppedBM_capMax`: two (finitely many) caps patch to their maximum (optional stopping);
* **`isTCExpMartingale_capMax`**: the caps' running maxima announce the clock `ℓ_u = ⨆ₙ (u ∧ Tₙ)`
  (`WholeField.isTCExpMartingale_annClock`);
* **`isFilteredBrownianReal_capNoise`**: the completed noise `N_{ℓ_u} + β_u − β_{ℓ_u}` with an independent Brownian
  motion `β` is a Brownian motion of the product filtration, equal to `N_u` whenever `u` is below some cap.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Canon

/-! ### The stopped Wald exponential -/

section StopExp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The Wald exponential of `N` stopped at `S`**: `exp(a N_{t∧S} − a²(t∧S)/2)`. -/
def stopExp (a : ℝ) (N : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (a * N (min t (S ω)) ω - a ^ 2 * ((min t (S ω) : ℝ≥0) : ℝ) / 2)

/-- **`N` is a Brownian motion stopped at `S`** (exponential form): every stopped Wald exponential is a martingale. -/
def IsStoppedBM (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ) (N : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) : Prop :=
  ∀ a : ℝ, Martingale (stopExp a N S) 𝓗 P

omit mΩ in
theorem stopExp_eq_stoppedProcess (a : ℝ) (N : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) :
    stopExp a N S = stoppedProcess (wald a N) fun ω => (S ω : WithTop ℝ≥0) := by
  funext t ω
  simp only [stopExp, stoppedProcess, wald, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]

omit mΩ in
theorem continuous_stopExp {N : ℝ≥0 → Ω → ℝ} (hNc : ∀ ω, Continuous (N · ω)) (a : ℝ) (S : Ω → ℝ≥0) (ω : Ω) :
    Continuous fun t => stopExp a N S t ω := by
  have hm : Continuous fun t : ℝ≥0 => min t (S ω) := continuous_id.min continuous_const
  exact Real.continuous_exp.comp (((hNc ω).comp hm).const_mul a |>.sub
    (((NNReal.continuous_coe.comp hm).const_mul (a ^ 2)).div_const 2))

omit mΩ in
/-- `stopExp` at the minimum of two caps is `stopExp` at the first cap stopped at the second. -/
theorem stopExp_min (a : ℝ) (N : ℝ≥0 → Ω → ℝ) (S S' : Ω → ℝ≥0) :
    stopExp a N (fun ω => min (S ω) (S' ω)) = stoppedProcess (stopExp a N S) fun ω => (S' ω : WithTop ℝ≥0) := by
  funext t ω
  simp only [stopExp, stoppedProcess, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
  rw [min_assoc, min_comm (S' ω) (S ω), ← min_assoc, min_assoc t (S ω) (S' ω)]

omit mΩ in
/-- `stopExp` at the maximum of two caps: `X^{S ∨ S'} = X^S + X^{S'} − X^{S ∧ S'}` (pathwise). -/
theorem stopExp_max (a : ℝ) (N : ℝ≥0 → Ω → ℝ) (S S' : Ω → ℝ≥0) :
    stopExp a N (fun ω => max (S ω) (S' ω)) =
      stopExp a N S + stopExp a N S' - stopExp a N (fun ω => min (S ω) (S' ω)) := by
  funext t ω
  simp only [Pi.add_apply, Pi.sub_apply]
  rcases le_total (S ω) (S' ω) with h | h
  · simp only [stopExp, max_eq_right h, min_eq_left h]; ring
  · simp only [stopExp, max_eq_left h, min_eq_right h]; ring

end StopExp

/-! ### One rectangle: a Brownian motion of a larger filtration up to the cap -/

section Agree

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 𝓖 : Filtration ℝ≥0 mΩ}
  {N B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}

/-- The stopped Wald exponential of a continuous adapted noise is adapted (at a stopping time). -/
theorem stronglyAdapted_stopExp (hNc : ∀ ω, Continuous (N · ω)) (hNa : ∀ t, Measurable[𝓗 t] (N t))
    (hS : IsStoppingTime 𝓗 fun ω => (S ω : WithTop ℝ≥0)) (a : ℝ) : StronglyAdapted 𝓗 (stopExp a N S) := by
  have hW : StronglyAdapted 𝓗 (wald a N) := fun t => by
    have h : Measurable[𝓗 t] fun ω => Real.exp (a * N t ω - a ^ 2 * (t : ℝ) / 2) :=
      Real.measurable_exp.comp (((hNa t).const_mul a).sub measurable_const)
    exact h.stronglyMeasurable
  have hWc : ∀ ω, Continuous fun t => wald a N t ω := fun ω =>
    Real.continuous_exp.comp (((hNc ω).const_mul a).sub
      ((NNReal.continuous_coe.const_mul (a ^ 2)).div_const 2))
  rw [stopExp_eq_stoppedProcess]
  exact (hW.isStronglyProgressive_of_continuous hWc).stronglyAdapted_stoppedProcess hS

/-- **One rectangle** (A.1.3, "inside this rectangle"): let `B` be a Brownian motion of a filtration `𝓖`, `N` a
continuous `𝓗`-adapted process equal to `B` up to the `𝓗`-stopping time `S` almost surely, and let `𝓗` and `𝓖` agree
before `S` (`A ∩ {s < S} ∈ 𝓖_s` for `A ∈ 𝓗_s`). Then `N` is an `𝓗`-Brownian motion stopped at `S`. -/
theorem isStoppedBM_of_agree (hB : IsFilteredBrownianReal 𝓖 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hNc : ∀ ω, Continuous (N · ω)) (hNa : ∀ t, Measurable[𝓗 t] (N t))
    (hS : IsStoppingTime 𝓗 fun ω => (S ω : WithTop ℝ≥0))
    (hagree : ∀ (s : ℝ≥0) (A : Set Ω), MeasurableSet[𝓗 s] A → MeasurableSet[𝓖 s] (A ∩ {ω | s < S ω}))
    (heq : ∀ᵐ ω ∂P, ∀ t, t ≤ S ω → B t ω = N t ω) : IsStoppedBM P 𝓗 N S := by
  intro a
  have hP := hB.isProbabilityMeasure'
  -- `S` is a `𝓖`-stopping time
  have hSG : IsStoppingTime 𝓖 fun ω => (S ω : WithTop ℝ≥0) := by
    intro t
    have h := hagree t univ MeasurableSet.univ
    have e : {ω | (S ω : WithTop ℝ≥0) ≤ t} = (univ ∩ {ω | t < S ω})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_univ, true_and, not_lt]
      exact WithTop.coe_le_coe
    rw [e]
    exact h.compl
  -- the stopped Wald exponential of `B` is a `𝓖`-martingale
  have hMB : Martingale (stopExp a B S) 𝓖 P := by
    rw [stopExp_eq_stoppedProcess]
    exact InteractingSLE.Martingale.stoppedProcess_of_rightContinuous (martingale_wald hB a)
      (fun ω t => (Real.continuous_exp.comp (((hBc ω).const_mul a).sub
        ((NNReal.continuous_coe.const_mul (a ^ 2)).div_const 2))).continuousWithinAt) hSG
  have hae : ∀ t, stopExp a N S t =ᵐ[P] stopExp a B S t := fun t => by
    filter_upwards [heq] with ω hω
    simp only [stopExp, hω _ (min_le_right t (S ω))]
  have hadp := stronglyAdapted_stopExp hNc hNa hS a
  have hint : ∀ t, Integrable (stopExp a N S t) P := fun t => (hMB.integrable t).congr (hae t).symm
  refine ⟨hadp, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓗.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_) (hadp s).aestronglyMeasurable).symm
  have hgt : MeasurableSet {ω | s < S ω} := by
    have h := hagree s univ MeasurableSet.univ
    simpa using 𝓖.le s _ h
  have hAm : MeasurableSet A := 𝓗.le s A hA
  rw [← integral_inter_add_sdiff hgt (hint t).integrableOn, ← integral_inter_add_sdiff hgt (hint s).integrableOn]
  congr 1
  · rw [setIntegral_congr_ae (hAm.inter hgt) (Eventually.mono (hae t) fun ω h _ => h),
      setIntegral_congr_ae (hAm.inter hgt) (Eventually.mono (hae s) fun ω h _ => h)]
    exact hMB.setIntegral_eq hst (hagree s A hA)
  · refine setIntegral_congr_fun (hAm.diff hgt) fun ω hω => ?_
    have hle : S ω ≤ s := not_lt.1 hω.2
    simp only [stopExp, min_eq_right hle, min_eq_right (hle.trans hst)]

end Agree

/-! ### Patching caps -/

section Patch

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓗 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ}

/-- **Two caps patch to their maximum** (optional stopping at the second cap). -/
theorem IsStoppedBM.max [IsFiniteMeasure P] {S S' : Ω → ℝ≥0} (h : IsStoppedBM P 𝓗 N S)
    (h' : IsStoppedBM P 𝓗 N S') (hS' : IsStoppingTime 𝓗 fun ω => (S' ω : WithTop ℝ≥0))
    (hNc : ∀ ω, Continuous (N · ω)) : IsStoppedBM P 𝓗 N fun ω => max (S ω) (S' ω) := by
  intro a
  rw [stopExp_max, stopExp_min]
  exact ((h a).add (h' a)).sub (InteractingSLE.Martingale.stoppedProcess_of_rightContinuous (h a)
    (fun ω t => (continuous_stopExp hNc a S ω).continuousWithinAt) hS')

/-- The running maximum `Tₙ = max_{m ≤ n} S_m` of a family of caps. -/
def capMax (S : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 := (Finset.range (n + 1)).sup fun m => S m ω

omit mΩ in
theorem capMax_zero (S : ℕ → Ω → ℝ≥0) (ω : Ω) : capMax S 0 ω = S 0 ω := by
  simp [capMax]

omit mΩ in
theorem capMax_succ (S : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) : capMax S (n + 1) ω = max (capMax S n ω) (S (n + 1) ω) := by
  simp only [capMax, Finset.range_add_one (n := n + 1), Finset.sup_insert, max_comm]

omit mΩ in
theorem le_capMax (S : ℕ → Ω → ℝ≥0) {m n : ℕ} (hmn : m ≤ n) (ω : Ω) : S m ω ≤ capMax S n ω :=
  Finset.le_sup (f := fun m => S m ω) (Finset.mem_range.2 (Nat.lt_succ_of_le hmn))

omit mΩ in
theorem monotone_capMax (S : ℕ → Ω → ℝ≥0) (ω : Ω) : Monotone fun n => capMax S n ω := fun _ _ hmn =>
  Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hmn))

theorem isStoppingTime_capMax {S : ℕ → Ω → ℝ≥0} (hS : ∀ m, IsStoppingTime 𝓗 fun ω => (S m ω : WithTop ℝ≥0))
    (n : ℕ) : IsStoppingTime 𝓗 fun ω => (capMax S n ω : WithTop ℝ≥0) := by
  induction n with
  | zero => simpa only [capMax_zero] using hS 0
  | succ n ih =>
    have h := ih.max (hS (n + 1))
    simpa only [capMax_succ, WithTop.coe_max] using h

/-- **Finitely many caps patch to their running maximum.** -/
theorem isStoppedBM_capMax [IsFiniteMeasure P] {S : ℕ → Ω → ℝ≥0} (h : ∀ m, IsStoppedBM P 𝓗 N (S m))
    (hS : ∀ m, IsStoppingTime 𝓗 fun ω => (S m ω : WithTop ℝ≥0)) (hNc : ∀ ω, Continuous (N · ω)) (n : ℕ) :
    IsStoppedBM P 𝓗 N (capMax S n) := by
  induction n with
  | zero =>
    have e : capMax S 0 = S 0 := funext fun ω => capMax_zero S ω
    rw [e]; exact h 0
  | succ n ih =>
    have e : capMax S (n + 1) = fun ω => max (capMax S n ω) (S (n + 1) ω) := funext fun ω => capMax_succ S n ω
    rw [e]
    exact ih.max (h (n + 1)) (hS (n + 1)) hNc

/-- `u ∧ T` is `𝓗_u`-measurable for an `𝓗`-stopping time `T` with finite values. -/
theorem measurable_min_of_isStoppingTime {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓗 fun ω => (T ω : WithTop ℝ≥0))
    (u : ℝ≥0) : Measurable[𝓗 u] fun ω => min u (T ω) := by
  refine measurable_of_Iic (mδ := 𝓗 u) fun x => ?_
  by_cases hx : u ≤ x
  · have e : (fun ω => min u (T ω)) ⁻¹' Iic x = univ := by
      ext ω; simp only [mem_preimage, mem_Iic, mem_univ, iff_true]; exact (min_le_left _ _).trans hx
    rw [e]; exact @MeasurableSet.univ _ (𝓗 u)
  · push Not at hx
    have e : (fun ω => min u (T ω)) ⁻¹' Iic x = {ω | (T ω : WithTop ℝ≥0) ≤ x} := by
      ext ω
      simp only [mem_preimage, mem_Iic, min_le_iff, Set.mem_ofPred_eq, WithTop.coe_le_coe]
      exact ⟨fun h => h.resolve_left (not_le.2 hx), Or.inr⟩
    rw [e]
    exact 𝓗.mono hx.le _ (hT x)

/-- **The caps announce the clock `ℓ_u = ⨆ₙ (u ∧ Tₙ)`** (`Tₙ` the running maxima): the noise read at the clock has
the exponential-martingale data `IsTCExpMartingale` for `𝓗`. -/
theorem isTCExpMartingale_capMax [IsProbabilityMeasure P] {S : ℕ → Ω → ℝ≥0} (h : ∀ m, IsStoppedBM P 𝓗 N (S m))
    (hS : ∀ m, IsStoppingTime 𝓗 fun ω => (S m ω : WithTop ℝ≥0)) (hNc : ∀ ω, Continuous (N · ω))
    (hN0 : ∀ ω, N 0 ω = 0) :
    Sec6.Prop65.IsTCExpMartingale P 𝓗 (fun u ω => N (WholeField.annClock (capMax S) u ω) ω)
      (WholeField.annClock (capMax S)) := by
  have h' := WholeField.isTCExpMartingale_annClock (P := P) (𝒢 := fun _ : ℕ => 𝓗) (fun _ => monotone_const)
    (monotone_capMax S) (fun m u => measurable_min_of_isStoppingTime (isStoppingTime_capMax hS m) u) hNc hN0
    (fun m a => isStoppedBM_capMax h hS hNc m a)
  rwa [Sec7.PhaseSelFull.iSupFiltration_const] at h'

/-- Below a cap the clock is the identity. -/
theorem annClock_capMax_eq {S : ℕ → Ω → ℝ≥0} {u : ℝ≥0} {ω : Ω} {m : ℕ} (h : u ≤ S m ω) :
    WholeField.annClock (capMax S) u ω = u :=
  WholeField.annClock_eq_of_le (h.trans (le_capMax S le_rfl ω))

/-- **The completed image noise is a Brownian motion** (continuation after the caps by an independent Brownian motion
`β` on `Ω₀`): `B'_u = N_{ℓ_u} + β_u − β_{ℓ_u}` is a Brownian motion of `𝓗 ⊗ 𝓦` under `P ⊗ P₀`, with continuous paths,
and `B'_u = N_u` whenever `u` lies below some cap. -/
theorem isFilteredBrownianReal_capNoise [IsProbabilityMeasure P] {S : ℕ → Ω → ℝ≥0}
    (h : ∀ m, IsStoppedBM P 𝓗 N (S m)) (hS : ∀ m, IsStoppingTime 𝓗 fun ω => (S m ω : WithTop ℝ≥0))
    (hNc : ∀ ω, Continuous (N · ω)) (hN0 : ∀ ω, N 0 ω = 0) {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓦 : Filtration ℝ≥0 m₀} {β : ℝ≥0 → Ω₀ → ℝ}
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0) :
    IsFilteredBrownianReal (WholeField.prodFiltration 𝓗 𝓦)
        (WholeField.complNoise (fun u ω => N (WholeField.annClock (capMax S) u ω) ω)
          (WholeField.annClock (capMax S)) β) (P.prod P₀) ∧
      (∀ p, Continuous fun u => WholeField.complNoise (fun u ω => N (WholeField.annClock (capMax S) u ω) ω)
          (WholeField.annClock (capMax S)) β u p) ∧
      ∀ (p : Ω × Ω₀) (u : ℝ≥0) (m : ℕ), u ≤ S m p.1 →
        WholeField.complNoise (fun u ω => N (WholeField.annClock (capMax S) u ω) ω)
          (WholeField.annClock (capMax S)) β u p = N u p.1 := by
  obtain ⟨hB, hBc⟩ := WholeField.IsTCExpMartingale.isFilteredBrownianReal_complNoise
    (isTCExpMartingale_capMax h hS hNc hN0) (LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hβ)
    hβc hβ0
  refine ⟨hB, hBc, fun p u m hu => ?_⟩
  have hc := annClock_capMax_eq (S := S) (ω := p.1) hu
  rw [WholeField.complNoise_of_eq hc]
  simp only [hc]

end Patch

end InteractingSLE.ZhanGT4.A1Canon
