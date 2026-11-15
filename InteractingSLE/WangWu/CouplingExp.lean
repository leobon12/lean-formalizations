import InteractingSLE.Spec.Coupling.ExpMartingale
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Wang–Wu at `κ = 4`: characteristic-function martingales with a continuous bracket

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, proof of Proposition 3.7
("`Z_t(p) = exp(i M_t(p) + ½⟨M(p)⟩_t)`. Itô's formula makes `Z(p)` a complex local martingale, while
`|Z_t(p)| ≤ exp(E_0(p)/2)`"), ruling R31.

The landed engine `Coupling.martingale_exp_of_bracket` (PROVE-T11-L311) needs a *Lipschitz* bracket. For the tested
frozen mean the bracket `E_0(p) − E_t(p)` is only continuous (it is not Lipschitz once part of `supp p` approaches
swallowing). This file removes the Lipschitz condition by a time change:

* `tcClock A ω t = t + A_t(ω)` is a continuous strictly increasing bijection of `ℝ≥0`; its inverse `tcInv A u ω`
  consists of bounded stopping times; along it, `M` and `M² − A` remain martingales (optional sampling) and the bracket
  `A ∘ tcInv` is `1`-Lipschitz;
* `martingale_exp_of_continuous_bracket`: for a bounded continuous martingale `M` with `M² − A` a martingale and `A`
  continuous, nondecreasing, bounded, `A_0 = 0`: `exp(a M − a² A/2)` is a martingale for every real `a`;
* `setIntegral_cexp_eq_of_continuous_bracket`: the characteristic-function identity
  `∫_S exp(iθ M_t + θ² A_t/2) = ∫_S exp(iθ M_s + θ² A_s/2)` (`S ∈ 𝓕_s`, `s ≤ t`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### The clock and its inverse -/

section Clock

variable {A : ℝ≥0 → Ω → ℝ}

/-- The clock `C_t = t + A_t`. -/
def tcClock (A : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : ℝ≥0 := t + (A t ω).toNNReal

/-- Its inverse `γ_u = sup {t : C_t ≤ u}`. -/
def tcInv (A : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) : ℝ≥0 := sSup {t | tcClock A ω t ≤ u}

variable {ω : Ω}

theorem tcClock_nonneg_A (hA0 : A 0 ω = 0) (hAmono : Monotone fun t => A t ω) (t : ℝ≥0) :
    0 ≤ A t ω := hA0 ▸ hAmono (zero_le (a := t))

theorem strictMono_tcClock (hAmono : Monotone fun t => A t ω) : StrictMono (tcClock A ω) :=
  fun s t hst => by
    unfold tcClock
    exact add_lt_add_of_lt_of_le hst (Real.toNNReal_le_toNNReal (hAmono hst.le))

theorem le_tcClock (t : ℝ≥0) : t ≤ tcClock A ω t := le_self_add

theorem tcClock_zero (hA0 : A 0 ω = 0) : tcClock A ω 0 = 0 := by simp [tcClock, hA0]

theorem continuous_tcClock (hAc : Continuous fun t => A t ω) : Continuous (tcClock A ω) :=
  continuous_id.add (continuous_real_toNNReal.comp hAc)

theorem surjective_tcClock (hA0 : A 0 ω = 0) (hAc : Continuous fun t => A t ω) :
    Function.Surjective (tcClock A ω) := by
  intro u
  have h := intermediate_value_Icc (zero_le (a := u)) (continuous_tcClock hAc).continuousOn
  rw [tcClock_zero hA0] at h
  obtain ⟨t, -, ht⟩ := h ⟨zero_le (a := u), le_tcClock u⟩
  exact ⟨t, ht⟩

/-- The clock as an order isomorphism of `ℝ≥0`. -/
def tcIso (hA0 : A 0 ω = 0) (hAmono : Monotone fun t => A t ω) (hAc : Continuous fun t => A t ω) :
    ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (tcClock A ω) (strictMono_tcClock hAmono)
    (surjective_tcClock hA0 hAc)

variable (hA0 : A 0 ω = 0) (hAmono : Monotone fun t => A t ω) (hAc : Continuous fun t => A t ω)
include hA0 hAmono hAc

theorem tcIso_apply (t : ℝ≥0) : tcIso hA0 hAmono hAc t = tcClock A ω t := rfl

theorem tcInv_eq (u : ℝ≥0) : tcInv A u ω = (tcIso hA0 hAmono hAc).symm u := by
  unfold tcInv
  have hset : {t | tcClock A ω t ≤ u} = Iic ((tcIso hA0 hAmono hAc).symm u) := by
    ext t
    simp only [mem_ofPred_eq, mem_Iic]
    rw [← tcIso_apply hA0 hAmono hAc, OrderIso.le_symm_apply]
  rw [hset, csSup_Iic]

theorem tcInv_le_iff {u t : ℝ≥0} : tcInv A u ω ≤ t ↔ u ≤ tcClock A ω t := by
  rw [tcInv_eq hA0 hAmono hAc, OrderIso.symm_apply_le, tcIso_apply]

theorem tcClock_tcInv (u : ℝ≥0) : tcClock A ω (tcInv A u ω) = u := by
  rw [tcInv_eq hA0 hAmono hAc, ← tcIso_apply hA0 hAmono hAc, OrderIso.apply_symm_apply]

theorem tcInv_tcClock (t : ℝ≥0) : tcInv A (tcClock A ω t) ω = t := by
  rw [tcInv_eq hA0 hAmono hAc, ← tcIso_apply hA0 hAmono hAc, OrderIso.symm_apply_apply]

theorem monotone_tcInv : Monotone fun u => tcInv A u ω := fun u v huv => by
  simp only [tcInv_eq hA0 hAmono hAc]
  exact (tcIso hA0 hAmono hAc).symm.monotone huv

theorem continuous_tcInv : Continuous fun u => tcInv A u ω := by
  simp only [tcInv_eq hA0 hAmono hAc]
  exact (tcIso hA0 hAmono hAc).symm.continuous

theorem tcInv_le (u : ℝ≥0) : tcInv A u ω ≤ u := by
  have h := le_tcClock (A := A) (ω := ω) (tcInv A u ω)
  rwa [tcClock_tcInv hA0 hAmono hAc] at h

theorem tcInv_zero : tcInv A 0 ω = 0 := le_antisymm (tcInv_le hA0 hAmono hAc 0) (zero_le (a := _))

/-- Along the inverse clock, the bracket is `1`-Lipschitz. -/
theorem A_tcInv_sub_le {u v : ℝ≥0} (huv : u ≤ v) :
    A (tcInv A v ω) ω - A (tcInv A u ω) ω ≤ (v : ℝ) - u := by
  have hv := tcClock_tcInv hA0 hAmono hAc v
  have hu := tcClock_tcInv hA0 hAmono hAc u
  have hle := monotone_tcInv hA0 hAmono hAc huv
  have hv' : ((tcClock A ω (tcInv A v ω) : ℝ≥0) : ℝ) = tcInv A v ω + A (tcInv A v ω) ω := by
    rw [tcClock, NNReal.coe_add, Real.coe_toNNReal _ (tcClock_nonneg_A hA0 hAmono _)]
  have hu' : ((tcClock A ω (tcInv A u ω) : ℝ≥0) : ℝ) = tcInv A u ω + A (tcInv A u ω) ω := by
    rw [tcClock, NNReal.coe_add, Real.coe_toNNReal _ (tcClock_nonneg_A hA0 hAmono _)]
  rw [hv] at hv'
  rw [hu] at hu'
  have : ((tcInv A u ω : ℝ≥0) : ℝ) ≤ tcInv A v ω := by exact_mod_cast hle
  linarith

end Clock

/-! ### Martingales along the inverse clock -/

section Exp

variable {𝓕 : Filtration ℝ≥0 mΩ} {A : ℝ≥0 → Ω → ℝ}

/-- The inverse clock times are stopping times: `{γ_u ≤ t} = {u ≤ t + A_t}`. -/
theorem isStoppingTime_tcInv (hA : StronglyAdapted 𝓕 A) (hA0 : ∀ ω, A 0 ω = 0)
    (hAmono : ∀ ω, Monotone fun t => A t ω) (hAc : ∀ ω, Continuous fun t => A t ω) (u : ℝ≥0) :
    IsStoppingTime 𝓕 fun ω => ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0) := by
  intro t
  have : {ω | ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =
      {ω | (u : ℝ) ≤ t + A t ω} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    rw [tcInv_le_iff (hA0 ω) (hAmono ω) (hAc ω), ← NNReal.coe_le_coe, tcClock, NNReal.coe_add,
      Real.coe_toNNReal _ (tcClock_nonneg_A (hA0 ω) (hAmono ω) t)]
  rw [this]
  exact measurableSet_le measurable_const (measurable_const.add (hA t).measurable)

/-- The time-changed filtration `𝓕̃_u = 𝓕_{γ_u}`. -/
def tcFiltration (hγ : ∀ u, IsStoppingTime 𝓕 fun ω => ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0))
    (hmono : ∀ ω, Monotone fun u => tcInv A u ω) : Filtration ℝ≥0 mΩ where
  seq u := (hγ u).measurableSpace
  mono' u v huv := IsStoppingTime.measurableSpace_mono (hγ u) (hγ v) fun ω =>
    WithTop.coe_le_coe.2 (hmono ω huv)
  le' u := (hγ u).measurableSpace_le

theorem stoppedValue_coe (X : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) :
    stoppedValue X (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) ω = X (τ ω) ω := by
  simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]

/-- **Optional sampling along the inverse clock**: a right-continuous martingale, read at `γ_u`, is a martingale of
the time-changed filtration. -/
theorem martingale_tc [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓕 P)
    (hXrc : ∀ ω t, ContinuousWithinAt (X · ω) (Ici t) t)
    (hγ : ∀ u, IsStoppingTime 𝓕 fun ω => ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0))
    (hmono : ∀ ω, Monotone fun u => tcInv A u ω) (hle : ∀ u ω, tcInv A u ω ≤ u) :
    Martingale (fun u ω => X (tcInv A u ω) ω) (tcFiltration hγ hmono) P := by
  have hprog := isStronglyProgressive_of_rightContinuous hX.1 hXrc
  refine ⟨fun u => ?_, fun u v huv => ?_⟩
  · have := (measurable_stoppedValue hprog (hγ u)).stronglyMeasurable
    rwa [show stoppedValue X (fun ω => ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => X (tcInv A u ω) ω from funext (stoppedValue_coe X _)] at this
  · have h := Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hX hXrc (hγ u) (hγ v)
      (fun ω => WithTop.coe_le_coe.2 (hmono ω huv)) (T := v) (fun ω => WithTop.coe_le_coe.2 (hle v ω))
    rw [show stoppedValue X (fun ω => ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => X (tcInv A u ω) ω from funext (stoppedValue_coe X _),
      show stoppedValue X (fun ω => ((tcInv A v ω : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => X (tcInv A v ω) ω from funext (stoppedValue_coe X _)] at h
    exact h.symm

/-- **Exponential martingales with a continuous bracket.** For a bounded martingale `M` with continuous paths such
that `M² − A` is a martingale, where `A` is continuous, nondecreasing, bounded by `K'` and `A_0 = 0`:
`exp(a M − a² A/2)` is a martingale for every real `a`. -/
theorem martingale_exp_of_continuous_bracket [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ} {K K' : ℝ}
    (hM : Martingale M 𝓕 P) (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous fun t => M t ω)
    (hA0 : ∀ ω, A 0 ω = 0) (hAmono : ∀ ω, Monotone fun t => A t ω)
    (hAc : ∀ ω, Continuous fun t => A t ω) (hAK : ∀ t ω, A t ω ≤ K') (a : ℝ) :
    Martingale (fun t ω => Real.exp (a * M t ω - a ^ 2 * A t ω / 2)) 𝓕 P := by
  -- adaptedness of the bracket
  have hAad : StronglyAdapted 𝓕 A := fun t => by
    have h1 := hM2.1 t
    have h2 := (hM.1 t).pow 2
    have : A t = fun ω => M t ω ^ 2 - (M t ω ^ 2 - A t ω) := by funext ω; ring
    rw [this]; exact h2.sub h1
  have hγ := isStoppingTime_tcInv hAad hA0 hAmono hAc
  have hγmono : ∀ ω, Monotone fun u => tcInv A u ω := fun ω => monotone_tcInv (hA0 ω) (hAmono ω) (hAc ω)
  have hγle : ∀ u ω, tcInv A u ω ≤ u := fun u ω => tcInv_le (hA0 ω) (hAmono ω) (hAc ω) u
  set 𝓖 := tcFiltration hγ hγmono with h𝓖
  have hMrc : ∀ ω t, ContinuousWithinAt (M · ω) (Ici t) t := fun ω t => (hcont ω).continuousWithinAt
  have hNrc : ∀ ω t, ContinuousWithinAt ((fun t ω => M t ω ^ 2 - A t ω) · ω) (Ici t) t := fun ω t =>
    (((hcont ω).pow 2).sub (hAc ω)).continuousWithinAt
  have hMt := martingale_tc hM hMrc hγ hγmono hγle
  have hNt := martingale_tc hM2 hNrc hγ hγmono hγle
  have hE := Coupling.martingale_exp_of_bracket (𝓕 := 𝓖) (c := 1) hMt hNt (fun u ω => hK _ ω)
    (fun ω => (hcont ω).comp (continuous_tcInv (hA0 ω) (hAmono ω) (hAc ω)))
    (fun ω => by simp only [tcInv_zero (hA0 ω) (hAmono ω) (hAc ω), hA0 ω])
    (fun p q hpq ω => hAmono ω (hγmono ω hpq))
    (fun p q hpq ω => by rw [one_mul]; exact A_tcInv_sub_le (hA0 ω) (hAmono ω) (hAc ω) hpq) a
  set Z : ℝ≥0 → Ω → ℝ := fun u ω => Real.exp (a * M (tcInv A u ω) ω - a ^ 2 * A (tcInv A u ω) ω / 2)
    with hZdef
  have hZrc : ∀ ω u, ContinuousWithinAt (Z · ω) (Ici u) u := fun ω u => by
    have hc1 := (hcont ω).comp (continuous_tcInv (hA0 ω) (hAmono ω) (hAc ω))
    have hc2 := (hAc ω).comp (continuous_tcInv (hA0 ω) (hAmono ω) (hAc ω))
    exact (Real.continuous_exp.comp ((continuous_const.mul hc1).sub
      ((continuous_const.mul hc2).div_const 2))).continuousWithinAt
  -- the clock times are stopping times of the time-changed filtration
  have hC : ∀ t, IsStoppingTime 𝓖 fun ω => ((tcClock A ω t : ℝ≥0) : WithTop ℝ≥0) := by
    intro t u
    have : {ω | ((tcClock A ω t : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
        {ω | ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, WithTop.coe_lt_coe, not_lt]
      rw [tcInv_eq (hA0 ω) (hAmono ω) (hAc ω), ← tcIso_apply (hA0 ω) (hAmono ω) (hAc ω),
        OrderIso.le_symm_apply]
    rw [this]
    exact ((hγ u).measurableSet_lt' t).compl
  set Kc : ℝ≥0 := K'.toNNReal with hKc
  have hCb : ∀ t ω, tcClock A ω t ≤ t + Kc := fun t ω => by
    show t + (A t ω).toNNReal ≤ t + Kc
    exact add_le_add le_rfl (Real.toNNReal_le_toNNReal (hAK t ω))
  have hZC : ∀ t ω, Z (tcClock A ω t) ω = Real.exp (a * M t ω - a ^ 2 * A t ω / 2) := fun t ω => by
    simp only [hZdef, tcInv_tcClock (hA0 ω) (hAmono ω) (hAc ω)]
  -- adaptedness and integrability in the original time
  have hMm : ∀ t, StronglyMeasurable[𝓕 t] (M t) := hM.1
  have had : ∀ t, StronglyMeasurable[𝓕 t] (fun ω => Real.exp (a * M t ω - a ^ 2 * A t ω / 2)) :=
    fun t => (Real.measurable_exp.comp ((measurable_const.mul (hMm t).measurable).sub
      ((measurable_const.mul (hAad t).measurable).div_const 2))).stronglyMeasurable
  have hbd : ∀ t ω, ‖Real.exp (a * M t ω - a ^ 2 * A t ω / 2)‖ ≤ Real.exp (|a| * K) := fun t ω => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have hA0' : 0 ≤ A t ω := tcClock_nonneg_A (hA0 ω) (hAmono ω) t
    have h1 : a * M t ω ≤ |a| * K := (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hK t ω) (abs_nonneg a))
    nlinarith [sq_nonneg a]
  have hint : ∀ t, Integrable (fun ω => Real.exp (a * M t ω - a ^ 2 * A t ω / 2)) P := fun t =>
    Integrable.of_bound ((had t).mono (𝓕.le t)).aestronglyMeasurable _
      (Eventually.of_forall (hbd t))
  refine ⟨had, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hint t)
    (fun S _ _ => (hint s).integrableOn) (fun S hS _ => ?_) ((had s).aestronglyMeasurable)).symm
  -- `S ∈ 𝓕_s` is measurable for the stopped σ-algebra of the clock time `C_s`
  have hCiff : ∀ ω (t u : ℝ≥0), tcClock A ω t ≤ u ↔ t ≤ tcInv A u ω := fun ω t u => by
    rw [tcInv_eq (hA0 ω) (hAmono ω) (hAc ω), ← tcIso_apply (hA0 ω) (hAmono ω) (hAc ω),
      OrderIso.le_symm_apply]
  have hγle' : ∀ u r, MeasurableSet[𝓕 r] {ω | tcInv A u ω ≤ r} := fun u r => by
    have := hγ u r; simpa only [WithTop.coe_le_coe] using this
  have hγlt : ∀ u r, MeasurableSet[𝓕 r] {ω | tcInv A u ω < r} := fun u r => by
    have := (hγ u).measurableSet_lt r; simpa only [WithTop.coe_lt_coe] using this
  have hSC : MeasurableSet[(hC s).measurableSpace] S := by
    refine ((hC s).measurableSet S).2 ⟨?_, fun u => ?_⟩
    · refine (le_iSup (fun u => (𝓖 u : MeasurableSpace Ω)) (s + Kc)) _ ?_
      refine ((hγ (s + Kc)).measurableSet _).2 ⟨(le_iSup (fun u => (𝓕 u : MeasurableSpace Ω)) s) _ hS,
        fun r => ?_⟩
      have hset : S ∩ {ω | ((tcInv A (s + Kc) ω : ℝ≥0) : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)} =
          S ∩ {ω | tcInv A (s + Kc) ω ≤ r} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
      rw [hset]
      by_cases hrs : s ≤ r
      · exact MeasurableSet.inter (m := 𝓕 r) (𝓕.mono hrs _ hS) (hγle' _ r)
      · have hemp : S ∩ {ω | tcInv A (s + Kc) ω ≤ r} = ∅ := by
          refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
          have h1 : s ≤ tcInv A (s + Kc) ω := (hCiff ω s (s + Kc)).1 (hCb s ω)
          exact hrs (h1.trans hω.2)
        rw [hemp]; exact @MeasurableSet.empty _ (𝓕 r)
    · have hset : S ∩ {ω | ((tcClock A ω s : ℝ≥0) : WithTop ℝ≥0) ≤ (u : WithTop ℝ≥0)} =
          S ∩ {ω | tcInv A u ω < s}ᶜ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_lt]
        rw [hCiff]
      rw [hset]
      refine ((hγ u).measurableSet _).2 ⟨(le_iSup (fun u => (𝓕 u : MeasurableSpace Ω)) s) _
        (MeasurableSet.inter (m := 𝓕 s) hS (hγlt u s).compl), fun r => ?_⟩
      have hset' : S ∩ {ω | tcInv A u ω < s}ᶜ ∩
          {ω | ((tcInv A u ω : ℝ≥0) : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)} =
          S ∩ {ω | tcInv A u ω < s}ᶜ ∩ {ω | tcInv A u ω ≤ r} := by
        ext ω; simp only [mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
      rw [hset']
      by_cases hrs : s ≤ r
      · exact MeasurableSet.inter (m := 𝓕 r)
          (MeasurableSet.inter (m := 𝓕 r) (𝓕.mono hrs _ hS) (𝓕.mono hrs _ (hγlt u s).compl))
          (hγle' u r)
      · have hemp : S ∩ {ω | tcInv A u ω < s}ᶜ ∩ {ω | tcInv A u ω ≤ r} = ∅ := by
          refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
          have h1 : s ≤ tcInv A u ω := not_lt.1 hω.1.2
          exact hrs (h1.trans hω.2)
        rw [hemp]; exact @MeasurableSet.empty _ (𝓕 r)
  have h := setIntegral_stoppedValue_eq_of_rightContinuous hE hZrc (hC s) (hC t)
    (fun ω => WithTop.coe_le_coe.2 ((strictMono_tcClock (hAmono ω)).monotone hst)) (T := t + Kc)
    (fun ω => WithTop.coe_le_coe.2 (hCb t ω)) hSC
  simp only [stoppedValue_coe] at h
  simp only [hZC] at h
  exact h

/-- **The characteristic-function identity with a continuous bracket**: for `S ∈ 𝓕_s`, `s ≤ t`,
`∫_S exp(iθ M_t + θ² A_t/2) = ∫_S exp(iθ M_s + θ² A_s/2)`. -/
theorem setIntegral_cexp_eq_of_continuous_bracket [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    {K K' : ℝ} (hM : Martingale M 𝓕 P) (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    (hK : ∀ t ω, |M t ω| ≤ K) (hcont : ∀ ω, Continuous fun t => M t ω)
    (hA0 : ∀ ω, A 0 ω = 0) (hAmono : ∀ ω, Monotone fun t => A t ω)
    (hAc : ∀ ω, Continuous fun t => A t ω) (hAK : ∀ t ω, A t ω ≤ K') {s t : ℝ≥0} (hst : s ≤ t)
    {S : Set Ω} (hS : MeasurableSet[𝓕 s] S) (θ : ℝ) :
    ∫ ω in S, Complex.exp (Complex.I * θ * M t ω + θ ^ 2 * A t ω / 2) ∂P =
      ∫ ω in S, Complex.exp (Complex.I * θ * M s ω + θ ^ 2 * A s ω / 2) ∂P := by
  have hMm : ∀ r, Measurable (M r) := fun r => ((hM.stronglyAdapted r).mono (𝓕.le r)).measurable
  have hAm : ∀ r, Measurable (A r) := fun r => by
    have h1 := ((hM2.stronglyAdapted r).mono (𝓕.le r)).measurable
    have h2 := (hMm r).pow_const 2
    have : A r = fun ω => M r ω ^ 2 - (M r ω ^ 2 - A r ω) := by funext ω; ring
    rw [this]; exact h2.sub h1
  set K'' : ℝ := max K |K'| with hK''
  have hAb : ∀ r ω, |A r ω| ≤ K'' := fun r ω => by
    have h0 : 0 ≤ A r ω := tcClock_nonneg_A (hA0 ω) (hAmono ω) r
    rw [abs_of_nonneg h0]
    exact (hAK r ω).trans ((le_abs_self K').trans (le_max_right _ _))
  have hMb : ∀ r ω, |M r ω| ≤ K'' := fun r ω => (hK r ω).trans (le_max_left _ _)
  have hnegA : ∀ r ω, |-A r ω| ≤ K'' := fun r ω => by rw [abs_neg]; exact hAb r ω
  have hreal : ∀ a : ℝ, ∫ ω in S, Real.exp (a * M t ω + a ^ 2 * (-A t ω) / 2) ∂P =
      ∫ ω in S, Real.exp (a * M s ω + a ^ 2 * (-A s ω) / 2) ∂P := fun a => by
    have h := (martingale_exp_of_continuous_bracket hM hM2 hK hcont hA0 hAmono hAc hAK a).setIntegral_eq
      hst hS
    have e : ∀ r ω, a * M r ω + a ^ 2 * (-A r ω) / 2 = a * M r ω - a ^ 2 * A r ω / 2 :=
      fun r ω => by ring
    simp only [e]
    exact h.symm
  have hc := Coupling.integral_cexp_eq_of_forall_real (μ := P.restrict S) (ν := P.restrict S) (hMm t)
    (hAm t).neg (hMm s) (hAm s).neg (hMb t) (hnegA t) (hMb s) (hnegA s) hreal
    ((θ : ℂ) * Complex.I)
  have e : ∀ r ω, ((θ : ℂ) * Complex.I) * (M r ω : ℂ) + ((θ : ℂ) * Complex.I) ^ 2 *
      ((-A r ω : ℝ) : ℂ) / 2 = Complex.I * θ * M r ω + θ ^ 2 * A r ω / 2 := fun r ω => by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [Pi.neg_apply, e] at hc
  exact hc

end Exp

end WangWu

end InteractingSLE
