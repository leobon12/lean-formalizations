/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedMeas

/-!
# Zhan's A.1.6, the seeded field IX: the martingale on an `𝓕_ε`-event

Packet PROVE-ZHAN-GT4-A21. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L507, R38): "At positive own time, differentiating (D13)–(D15) by Itô and the force ODE
is the same cancelled calculation leading to (D8). The identity extends to time zero by bounded convergence on a
protected rectangle."

A19's `IsDriftLogField` asks for the per-path conditions on **every** path. The localization of §A.1.6 cuts off at
the first time `τ_k ≥ ε` at which a seed gap leaves `[1/k, k]`; on the paths whose gaps at time `ε` are already outside
that range the uniform constants fail at `ε` itself. The standard remedy is to work on the `𝓕_ε`-event `E` of good
paths: off `E` the field is replaced by `0` and the horizon by `ε` (`onEv`, `onEvB`, `onEvS`), which changes nothing
in `E[ξ 1_E (M_{t∧S} − M_{s∧S})]`.

* `atPath`, `unitFilt`: one path as a process on the one-point space (the per-path conditions of `IsDriftLogField`
  are those of `IsDriftLogField` on `Unit`);
* `isDriftLogField_localize`: per-path conditions on `E` plus adaptedness on `E` give `IsDriftLogField` for the
  modified data;
* **`integral_indicator_mul_stopped_sub_eq_zero`**: `E[1_E ξ (e^{ℓ(t∧S, W)} − e^{ℓ(s∧S, W)})] = 0`, `ε ≤ s ≤ t`;
* `isDriftLogField_seed_path`: the per-path seeded log-field (A20's `isDriftLogField_seed` on `Unit`);
* **`integral_indicator_mul_seed_stopped_sub_eq_zero`**: the seeded density is a martingale after `ε` on `E`, all
  hypotheses only on `E` (measurability from `seed_meas_inputs_on`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### One path as a process on the one-point space -/

/-- The path `ω` of a process, as a process on the one-point space. -/
def atPath (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → Unit → ℝ := fun t _ => X t ω

/-- The constant filtration of the one-point space. -/
def unitFilt : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
  ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

theorem driftDriver_atPath (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ω : Ω) (u : Unit) :
    driftDriver σ (atPath B ω) (atPath D ω) u = driftDriver σ B D ω := rfl

/-! ### The modified data off the event -/

open Classical in
/-- The field `ℓ` on `E`, `0` off `E`. -/
def onEv (E : Set Ω) (ℓ : Ω → ℝ → ℝ → ℝ) : Ω → ℝ → ℝ → ℝ := fun ω => if ω ∈ E then ℓ ω else fun _ _ => 0

open Classical in
/-- The drift rate `b` on `E`, `0` off `E`. -/
def onEvB (E : Set Ω) (b : Ω → ℝ → ℝ) : Ω → ℝ → ℝ := fun ω => if ω ∈ E then b ω else fun _ => 0

open Classical in
/-- The horizon `S` on `E`, `ε` off `E`. -/
def onEvS (E : Set Ω) (ε : ℝ≥0) (S : Ω → ℝ≥0) : Ω → ℝ≥0 := fun ω => if ω ∈ E then S ω else ε

section Mod

variable {E : Set Ω} {ω : Ω}

theorem onEv_of_mem (hω : ω ∈ E) (ℓ : Ω → ℝ → ℝ → ℝ) : onEv E ℓ ω = ℓ ω := by simp [onEv, hω]
theorem onEv_of_notMem (hω : ω ∉ E) (ℓ : Ω → ℝ → ℝ → ℝ) : onEv E ℓ ω = fun _ _ => 0 := by simp [onEv, hω]
theorem onEvB_of_mem (hω : ω ∈ E) (b : Ω → ℝ → ℝ) : onEvB E b ω = b ω := by simp [onEvB, hω]
theorem onEvB_of_notMem (hω : ω ∉ E) (b : Ω → ℝ → ℝ) : onEvB E b ω = fun _ => 0 := by simp [onEvB, hω]
theorem onEvS_of_mem (hω : ω ∈ E) (ε : ℝ≥0) (S : Ω → ℝ≥0) : onEvS E ε S ω = S ω := by simp [onEvS, hω]
theorem onEvS_of_notMem (hω : ω ∉ E) (ε : ℝ≥0) (S : Ω → ℝ≥0) : onEvS E ε S ω = ε := by simp [onEvS, hω]

/-- The modified horizon is a stopping time if `S ≥ ε` is one and `E` is an `𝓕_ε`-event. -/
theorem isStoppingTime_onEvS {𝓕 : Filtration ℝ≥0 mΩ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hεS : ∀ ω, ε ≤ S ω) (hE : MeasurableSet[𝓕 ε] E) :
    IsStoppingTime 𝓕 fun ω => (onEvS E ε S ω : WithTop ℝ≥0) := by
  intro u
  by_cases hu : ε ≤ u
  · have e : {ω | ((onEvS E ε S ω : ℝ≥0) : WithTop ℝ≥0) ≤ u} = (E ∩ {ω | (S ω : WithTop ℝ≥0) ≤ u}) ∪ Eᶜ := by
      ext ω
      by_cases hω : ω ∈ E
      · simp [onEvS, hω]
      · simp only [onEvS, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, false_and,
          not_false_eq_true, or_true, iff_true]
        exact_mod_cast hu
    rw [e]
    exact ((𝓕.mono hu _ hE).inter (hS u)).union (𝓕.mono hu _ hE).compl
  · have e : {ω | ((onEvS E ε S ω : ℝ≥0) : WithTop ℝ≥0) ≤ u} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, WithTop.coe_le_coe, not_le]
      by_cases hω : ω ∈ E
      · rw [onEvS_of_mem hω]; exact (not_le.1 hu).trans_le (hεS ω)
      · rw [onEvS_of_notMem hω]; exact not_le.1 hu
    rw [e]
    exact @MeasurableSet.empty _ (𝓕 u)

end Mod

/-! ### Localization -/

section Loc

variable {σ ρ K : ℝ} {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ} {E : Set Ω}

/-- The per-path conditions on `[ε, ε]` for the zero field hold trivially. -/
theorem hasDerivWithinAt_Icc_self (f : ℝ → ℝ) (y : ℝ) {t : ℝ} (ht : t ∈ Icc y y) :
    HasDerivWithinAt f 0 (Icc y y) t := by
  rw [Icc_self] at ht ⊢
  rw [mem_singleton_iff.1 ht]
  exact (hasFDerivWithinAt_singleton f y).hasDerivWithinAt

/-- **Localization of a drift log-field to an `𝓕_ε`-event.** If the per-path conditions of `IsDriftLogField` hold on
`E` and `ℓ, ℓ_x, ℓ_xx` along the driver are adapted on `E ∩ {r ≤ S}`, then the data modified off `E` (field `0`,
horizon `ε`) form a drift log-field. -/
theorem isDriftLogField_localize (𝓕 : Filtration ℝ≥0 mΩ) (hK : 0 ≤ K)
    (hpt : ∀ ω ∈ E, IsDriftLogField unitFilt σ ρ K (atPath B ω) (atPath D ω) (fun _ => b ω) ε (fun _ => S ω)
      (fun _ => ℓ ω) (fun _ => ℓx ω) (fun _ => ℓxx ω) (fun _ => ℓxxx ω) (fun _ => ℓt ω))
    (hm0 : ∀ r : ℝ≥0, ε ≤ r →
      Measurable[𝓕 r] ((E ∩ {ω | r ≤ S ω}).indicator fun ω => ℓ ω r (driftDriver σ B D ω r)))
    (hm1 : ∀ r : ℝ≥0, ε ≤ r →
      Measurable[𝓕 r] ((E ∩ {ω | r ≤ S ω}).indicator fun ω => ℓx ω r (driftDriver σ B D ω r)))
    (hm2 : ∀ r : ℝ≥0, ε ≤ r →
      Measurable[𝓕 r] ((E ∩ {ω | r ≤ S ω}).indicator fun ω => ℓxx ω r (driftDriver σ B D ω r))) :
    IsDriftLogField 𝓕 σ ρ K B D (onEvB E b) ε (onEvS E ε S) (onEv E ℓ) (onEv E ℓx) (onEv E ℓxx) (onEv E ℓxxx)
      (onEv E ℓt) := by
  have hmeas : ∀ (f : Ω → ℝ → ℝ → ℝ) (r : ℝ≥0),
      ({ω | r ≤ onEvS E ε S ω}.indicator fun ω => onEv E f ω r (driftDriver σ B D ω r)) =
        (E ∩ {ω | r ≤ S ω}).indicator fun ω => f ω r (driftDriver σ B D ω r) := fun f r => by
    funext ω
    by_cases hω : ω ∈ E
    · by_cases hr : r ≤ S ω
      · rw [indicator_of_mem (show ω ∈ {ω | r ≤ onEvS E ε S ω} by rw [mem_ofPred_eq, onEvS_of_mem hω]; exact hr),
          indicator_of_mem (show ω ∈ E ∩ {ω | r ≤ S ω} from ⟨hω, hr⟩), onEv_of_mem hω]
      · rw [indicator_of_notMem (show ω ∉ {ω | r ≤ onEvS E ε S ω} by rw [mem_ofPred_eq, onEvS_of_mem hω]; exact hr),
          indicator_of_notMem (fun h => hr h.2)]
    · rw [indicator_of_notMem (show ω ∉ E ∩ {ω | r ≤ S ω} from fun h => hω h.1)]
      by_cases hr : ω ∈ {ω | r ≤ onEvS E ε S ω}
      · rw [indicator_of_mem hr]; simp only [onEv_of_notMem hω]
      · rw [indicator_of_notMem hr]
  refine ⟨fun ω => ?_, hK, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_,
    fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω => ?_,
    fun r hr => by rw [hmeas]; exact hm0 r hr, fun r hr => by rw [hmeas]; exact hm1 r hr,
    fun r hr => by rw [hmeas]; exact hm2 r hr⟩ <;>
    by_cases hω : ω ∈ E <;>
    simp only [onEv_of_mem, onEv_of_notMem, onEvB_of_mem, onEvB_of_notMem, onEvS_of_mem, onEvS_of_notMem, hω,
      not_false_eq_true]
  · exact (hpt ω hω).le ()
  · exact le_rfl
  · exact (hpt ω hω).dD ()
  · exact fun t ht => hasDerivWithinAt_Icc_self _ _ ht
  · exact (hpt ω hω).contb ()
  · exact continuousOn_const
  · exact (hpt ω hω).bound_b ()
  · intro t _; rw [abs_zero]; exact hK
  · exact (hpt ω hω).dx ()
  · exact fun _ _ => hasDerivAt_const _ _
  · exact (hpt ω hω).dxx ()
  · exact fun _ _ => hasDerivAt_const _ _
  · exact (hpt ω hω).dxxx ()
  · exact fun _ _ => hasDerivAt_const _ _
  · exact (hpt ω hω).dt ()
  · exact fun _ _ => hasDerivWithinAt_const _ _ _
  · exact (hpt ω hω).cont ()
  · exact continuousOn_const
  · exact (hpt ω hω).contX ()
  · exact continuousOn_const
  · exact (hpt ω hω).contXX ()
  · exact continuousOn_const
  · exact (hpt ω hω).contT ()
  · exact continuousOn_const
  · exact (hpt ω hω).bound ()
  · intro _ _; simp only [abs_zero]; exact ⟨hK, hK, hK, hK, hK⟩
  · exact (hpt ω hω).gen ()
  · intro _ _; ring

/-- **The martingale identity on an `𝓕_ε`-event**: under the hypotheses of `isDriftLogField_localize`, for
`ε ≤ s ≤ t` and bounded `𝓕_s`-measurable `ξ`, `E[1_E ξ (e^{ℓ(t∧S, W_{t∧S})} − e^{ℓ(s∧S, W_{s∧S})})] = 0`. -/
theorem integral_indicator_mul_stopped_sub_eq_zero (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω}
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hpt : ∀ ω ∈ E, IsDriftLogField unitFilt σ ρ K (atPath B ω) (atPath D ω) (fun _ => b ω) ε (fun _ => S ω)
      (fun _ => ℓ ω) (fun _ => ℓx ω) (fun _ => ℓxx ω) (fun _ => ℓxxx ω) (fun _ => ℓt ω))
    (hE : MeasurableSet[𝓕 ε] E)
    (hm0 : ∀ r : ℝ≥0, ε ≤ r →
      Measurable[𝓕 r] ((E ∩ {ω | r ≤ S ω}).indicator fun ω => ℓ ω r (driftDriver σ B D ω r)))
    (hm1 : ∀ r : ℝ≥0, ε ≤ r →
      Measurable[𝓕 r] ((E ∩ {ω | r ≤ S ω}).indicator fun ω => ℓx ω r (driftDriver σ B D ω r)))
    (hm2 : ∀ r : ℝ≥0, ε ≤ r →
      Measurable[𝓕 r] ((E ∩ {ω | r ≤ S ω}).indicator fun ω => ℓxx ω r (driftDriver σ B D ω r)))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hεS : ∀ ω, ε ≤ S ω)
    {s t : ℝ≥0} (hεs : ε ≤ s) (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, E.indicator ξ ω * (Real.exp (ℓ ω (min t (S ω)) (driftDriver σ B D ω (min t (S ω))))
      - Real.exp (ℓ ω (min s (S ω)) (driftDriver σ B D ω (min s (S ω))))) ∂P = 0 := by
  have hL := isDriftLogField_localize 𝓕 hK hpt hm0 hm1 hm2
  have hS' := isStoppingTime_onEvS hS hεS hE
  have hξ' : Measurable[𝓕 s] (E.indicator ξ) := Measurable.indicator (m := 𝓕 s) hξ (𝓕.mono hεs _ hE)
  have hξb' : ∀ ω, |E.indicator ξ ω| ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]; exact hξb ω
    · rw [indicator_of_notMem hω, abs_zero]; exact zero_le_one
  have key := hL.integral_mul_stopped_sub_eq_zero hB hBc hσ hρ hS' hεs hst hξ' hξb'
  rw [← key]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ E
  · simp only [onEv_of_mem hω, onEvS_of_mem hω]
  · simp only [indicator_of_notMem hω, zero_mul]

end Loc

/-! ### The seeded density on an `𝓕_ε`-event -/

section Seed

variable {κ : ℝ} {n : ℕ} {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0} {d : Ω → SeedData n}

/-- **The seeded log-field along one path** (A20's `isDriftLogField_seed` on the one-point space): the per-path
conditions of `IsDriftLogField` for the seeded density of the path `ω`. -/
theorem isDriftLogField_seed_path (hκ : 0 < κ) (rr : Fin n → ℝ) (ω : Ω)
    (hdW : (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : (d ω).κ = κ) (hdr : (d ω).r = rr) {A : Set ℂ}
    {r a₀ γ Γ lam ρm L Tm : ℝ} (hεS : ε ≤ S ω) (hSTm : (S ω : ℝ) ≤ Tm)
    (h : OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hv₀ : ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀)
    (hc : (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam Tm L)
    (hV₀ : ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hG₀ : ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).G₀ (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Icc (ε : ℝ) (S ω)) t)
    (hV : ∀ m, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hVc : ∀ m, ContinuousOn ((d ω).V m) (Icc 0 (S ω)))
    (hD : ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) ((d ω).drift t) (Icc (ε : ℝ) (S ω)) t) :
    IsDriftLogField unitFilt (Real.sqrt κ) (3 * cutRad r a₀ γ / 4)
      (4 * (coefTot κ rr * scaleBound L) + |κ| * (coefTot κ rr * scaleBound L)) (atPath B ω) (atPath D ω)
      (fun _ => (d ω).drift) ε (fun _ => S ω) (fun _ => (d ω).ell) (fun _ => (d ω).ellX) (fun _ => (d ω).ellXX)
      (fun _ => (d ω).ellXXX) (fun _ => (d ω).ellT) :=
  isDriftLogField_seed unitFilt hκ rr (atPath B ω) (atPath D ω) ε (fun _ => S ω) (fun _ => d ω) (fun _ => hdW)
    (fun _ => hdκ) (fun _ => hdr) (A := fun _ => A) (fun _ => hεS) (fun _ => hSTm) (fun _ => h) (fun _ => hv₀)
    (fun _ => hc) hL (fun _ => hV₀) (fun _ => hG₀) (fun _ => hV) (fun _ => hVc) (fun _ => hD)
    (fun _ _ => Subsingleton.measurable) (fun _ _ => Subsingleton.measurable) (fun _ _ => Subsingleton.measurable)

/-- **The seeded density is a martingale after `ε` on an `𝓕_ε`-event `E`**: every per-path hypothesis of A20's
`integral_mul_seed_stopped_sub_eq_zero` is needed only on `E`, the measurability inputs come from the adaptedness of
`B`, `D` and the own-chart coordinates on `E ∩ {q ≤ S}` (`seed_meas_inputs_on`); for `ε ≤ s ≤ t` and bounded
`𝓕_s`-measurable `ξ`, `E[1_E ξ (e^{ℓ(t∧S, W_{t∧S})} − e^{ℓ(s∧S, W_{s∧S})})] = 0`. -/
theorem integral_indicator_mul_seed_stopped_sub_eq_zero (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω} (hκ : 0 < κ)
    (rr : Fin n → ℝ) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hDm : ∀ u, Measurable[𝓕 u] (D u)) (hDc : ∀ ω, Continuous (D · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (hεS : ∀ ω, ε ≤ S ω)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ} (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) {E : Set Ω}
    (hE : MeasurableSet[𝓕 ε] E) {r a₀ γ Γ lam ρm L Tm : ℝ} (hSTm : ∀ ω ∈ E, (S ω : ℝ) ≤ Tm)
    (h : ∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω ∈ E, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀)
    (hc : ∀ ω ∈ E, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam Tm L)
    (hV₀ : ∀ ω ∈ E, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hG₀ : ∀ ω ∈ E, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).G₀ (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Icc (ε : ℝ) (S ω)) t)
    (hV : ∀ ω ∈ E, ∀ m, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hVc : ∀ ω ∈ E, ∀ m, ContinuousOn ((d ω).V m) (Icc 0 (S ω)))
    (hD : ∀ ω ∈ E, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) ((d ω).drift t) (Icc (ε : ℝ) (S ω)) t)
    (hVm : ∀ (q : ℝ≥0) m, ε ≤ q → Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).V m q))
    (hV₀m : ∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).V₀ q))
    (hG₀m : ∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).G₀ q))
    {s t : ℝ≥0} (hεs : ε ≤ s) (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, E.indicator ξ ω * (Real.exp ((d ω).ell (min t (S ω)) (driftDriver (Real.sqrt κ) B D ω (min t (S ω))))
      - Real.exp ((d ω).ell (min s (S ω)) (driftDriver (Real.sqrt κ) B D ω (min s (S ω))))) ∂P = 0 := by
  rcases E.eq_empty_or_nonempty with hE0 | ⟨ω₀, hω₀⟩
  · simp only [hE0, indicator_empty, zero_mul, integral_zero]
  obtain ⟨hm0, hm1, hm2⟩ := seed_meas_inputs_on (fun u => hB.2.1 u) hBc hDm hDc hdW hdκ hdr hdφ hdζ hE hS h hv₀ hc
    hVm hV₀m hG₀m
  have hC0 : 0 ≤ coefTot κ rr * scaleBound L :=
    mul_nonneg (coefTot_ge (κ := κ) (r := rr)).2.2.2 (hL.base.L0.trans (le_scaleBound hL.base.L0).1)
  have hK : 0 ≤ 4 * (coefTot κ rr * scaleBound L) + |κ| * (coefTot κ rr * scaleBound L) := by positivity
  have hρ : 0 < 3 * cutRad r a₀ γ / 4 := by
    have := cutRad_pos (hc ω₀ hω₀).r0 (hc ω₀ hω₀).a0 (hc ω₀ hω₀).g0
    positivity
  exact integral_indicator_mul_stopped_sub_eq_zero 𝓕 hB hBc (Real.sqrt_nonneg _) hρ hK
    (fun ω hω => isDriftLogField_seed_path hκ rr ω (hdW ω) (hdκ ω) (hdr ω) (hεS ω) (hSTm ω hω) (h ω hω) (hv₀ ω hω)
      (hc ω hω) hL (hV₀ ω hω) (hG₀ ω hω) (hV ω hω) (hVc ω hω) (hD ω hω)) hE hm0 hm1 hm2 hS hεS hεs hst hξ hξb

end Seed

end InteractingSLE.ZhanGT4
