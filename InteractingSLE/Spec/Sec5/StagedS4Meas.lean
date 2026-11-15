/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Past

/-!
# Measurability of the restarted word's own-time map and restart capacity

Packet PROVE-STAGED-S4 (§5.2 of `planning/handoffs/PROVE-STAGED-S3.md`, the hypothesis `hθ` of
`ae_condExp_cand_of_meas`). On the glued space:

* `isKilledFamily_gCurve`: Word49's image curves on their pre-contact times form a measurable family of killed arcs
  (PROVE-PROP59-PIECES' `IsKilledFamily`) when the driver process is adapted before its lifetime;
* `measurableSet_lt_kLife_comp`, `measurable_kInvK_comp`: the lifetime events and the inverse capacity clock at a
  measurable random capacity;
* `measurableSet_s3Alive`, `measurable_s3Start`, **`measurable_s4Theta`**: the alive event, the restart capacity
  `S₀ = σ(τ)` (rational `τ`) and the own time `σ⁻¹(S₀ + r)` of a restarted time are measurable;
* `adaptedBefore_candW`, **`measurable_s4Theta_cand`**: for PIECES' candidate.

R48: only `h44` (R74) is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref Word49 StagedS3
open Restart Exist.StagedLaw Exist.Staged
open Sec7.AdmCode Prop513TreeExtract Prop513Schedule Prop513Target Prop59Pieces StagedRepLater
open Prop59Pieces.IsKilledFamily (kInvK kInv_lt_iff)
open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Sec7.Lemma71C (capClock)

/-! ### Measurable families of killed arcs at random capacities -/

section Family

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}

theorem measurableSet_lt_kLife_comp (hF : IsKilledFamily γ P) {R : Ω → ℝ≥0} (hR : Measurable R) :
    MeasurableSet {ω | (R ω : WithTop ℝ≥0) < kLife (γ ω) (P ω)} :=
  have h : MeasurableSet {ω | ((R ω : ℝ≥0) : ℝ≥0∞) < lifeE (γ ω) (P ω)} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp hR) hF.measurable_kLife
  h

/-- **The inverse capacity clock at a measurable random capacity is measurable.** -/
theorem measurable_kInvK_comp (hF : IsKilledFamily γ P) {R : Ω → ℝ≥0} (hR : Measurable R) :
    Measurable fun ω => kInvK (γ ω) (P ω) (R ω) := by
  refine measurable_of_Iio fun a => ?_
  have e : (fun ω => kInvK (γ ω) (P ω) (R ω)) ⁻¹' Iio a =
      ({ω | (R ω : WithTop ℝ≥0) < kLife (γ ω) (P ω)} ∩ ⋃ q : ℚ, {ω | (q : ℝ) < a} ∩ ({ω | (q : ℝ) ∈ P ω} ∩
        {ω | (R ω : ℝ) < ({ω | (q : ℝ) ∈ P ω}.indicator fun ω => capClock (γ ω) q) ω})) ∪
      ({ω | (R ω : WithTop ℝ≥0) < kLife (γ ω) (P ω)}ᶜ ∩ {ω | (0 : ℝ) < a}) := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_union, mem_inter_iff, mem_iUnion, mem_compl_iff, mem_ofPred_eq]
    by_cases hτ : (R ω : WithTop ℝ≥0) < kLife (γ ω) (P ω)
    · simp only [kInvK, hτ, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
      rw [kInv_lt_iff (hF.arc ω) hτ a]
      refine exists_congr fun q => and_congr_right fun _ => ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
      · rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from h.1)]; exact h.2
      · rw [indicator_of_mem (show ω ∈ {ω | (q : ℝ) ∈ P ω} from h.1)] at h; exact h.2
    · simp only [kInvK, hτ, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
  rw [e]
  refine ((measurableSet_lt_kLife_comp hF hR).inter (MeasurableSet.iUnion fun q => ?_)).union
    ((measurableSet_lt_kLife_comp hF hR).compl.inter (MeasurableSet.const _))
  exact (MeasurableSet.const _).inter ((hF.pre q).inter (measurableSet_lt
    (measurable_coe_nnreal_real.comp hR) (hF.cap q)))

end Family

/-! ### The glued image curves -/

section Glued

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ}
  {E : Set (Ω × HistorySpace 0 0)}

/-- **Word49's image curves form a measurable family of killed arcs.** -/
theorem isKilledFamily_gCurve (hW : AdaptedBefore 𝓕 (fun _ => ⊤) Wj) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) :
    IsKilledFamily (gCurve s (fun _ => ⊤) Wj E) (gPre s (fun _ => ⊤) Wj E) :=
  ⟨isKilledArc_gCurve hEg, measurableSet_mem_gPre hW hE hEg, measurable_indicator_capClock_gCurve hW hE hEg,
    fun q => measurable_gCurve hW hE q⟩

theorem measurableSet_s3Alive (hW : AdaptedBefore 𝓕 (fun _ => ⊤) Wj) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (τ : ℚ) : MeasurableSet (s3Alive s Wj E τ) :=
  hE.inter (measurableSet_mem_gPre hW hE hEg τ)

/-- **The restart capacity at a rational own time is measurable.** -/
theorem measurable_s3Start (hW : AdaptedBefore 𝓕 (fun _ => ⊤) Wj) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (τ : ℚ) : Measurable (s3Start s Wj E τ) := by
  classical
  have e : s3Start s Wj E τ = fun p => if p ∈ s3Alive s Wj E τ then
      (({p | (τ : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p}.indicator
        fun p => capClock (gCurve s (fun _ => ⊤) Wj E p) τ) p).toNNReal else 0 := by
    funext p
    by_cases hp : p ∈ s3Alive s Wj E τ
    · simp only [s3Start, hp, ↓reduceIte]
      rw [indicator_of_mem (show p ∈ {p | (τ : ℝ) ∈ gPre s (fun _ => ⊤) Wj E p} from hp.2)]
    · simp only [s3Start, hp, ↓reduceIte]
  rw [e]
  exact Measurable.ite (measurableSet_s3Alive hW hE hEg τ)
    (measurable_real_toNNReal.comp (measurable_indicator_capClock_gCurve hW hE hEg τ)) measurable_const

omit mΩ in
/-- The own time of a restarted time is the guarded inverse capacity clock at `S₀ + r`. -/
theorem s4Theta_eq_kInvK (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (τ : ℝ) (r : ℝ≥0)
    (p : Ω × HistorySpace 0 0) :
    s4Theta s Wj E τ r p = (kInvK (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)
      (s3Start s Wj E τ p + r)).toNNReal := by
  by_cases hr : ((s3Start s Wj E τ p + r : ℝ≥0) : WithTop ℝ≥0) <
      kLife (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)
  · simp only [kInvK, hr, ↓reduceIte, s4Theta, cfTheta]
  · rw [s4Theta, cfTheta_eq_zero hEg hr]
    simp only [kInvK, hr, ↓reduceIte, Real.toNNReal_zero]

/-- **The own time of a restarted time is measurable** (rational `τ`). -/
theorem measurable_s4Theta (hW : AdaptedBefore 𝓕 (fun _ => ⊤) Wj) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (τ : ℚ) (r : ℝ≥0) :
    Measurable (s4Theta s Wj E τ r) := by
  have e : s4Theta s Wj E τ r = fun p => (kInvK (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)
      (s3Start s Wj E τ p + r)).toNNReal := funext (s4Theta_eq_kInvK hEg τ r)
  rw [e]
  exact measurable_real_toNNReal.comp (measurable_kInvK_comp (isKilledFamily_gCurve hW hE hEg)
    ((measurable_s3Start hW hE hEg τ).add_const r))

end Glued

/-! ### The candidate -/

section Cand

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
  (ζ : Ω → ℝ≥0∞)

omit [StandardBorelSpace Ω] in
/-- The candidate's driver is a measurable process (adapted before `⊤` to the constant filtration). -/
theorem adaptedBefore_candW (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) :
    AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) (fun _ => ⊤) (candW x₀ h44 hκ hκ4 hb h ℓ t) := by
  intro r A hA
  have hqm : Measurable (qField x₀ κ h) :=
    (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
  have hm : Measurable fun ω => candW x₀ h44 hκ hκ4 hb h ℓ t r ω :=
    (measurable_pi_apply r).comp (measurable_continuedDriver
      (fun k => (measurable_codeDriver h44 hκ hκ4 _ _ k).comp hqm) _ _ _)
  have e : {ω | (r : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧ candW x₀ h44 hκ hκ4 hb h ℓ t r ω ∈ A} =
      (fun ω => candW x₀ h44 hκ hκ4 hb h ℓ t r ω) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_lt_top, true_and]
  rw [e]
  exact hm hA

omit [StandardBorelSpace Ω] in
/-- **The candidate's own-time map of a restarted time is measurable** (hypothesis `hθ` of
`ae_condExp_cand_of_meas`). -/
theorem measurable_s4Theta_cand (hhm : Measurable h) (ℓ : ℕ) (t : Fin ℓ → ℝ≥0) (s : ℝ≥0) (r : ℝ≥0) :
    Measurable (s4Theta s (candW x₀ h44 hκ hκ4 hb h ℓ t) (candEg x₀ h44 hκ hκ4 hb P h W ζ hhm ℓ t s)
      (lastO ℓ t : ℝ) r) :=
  measurable_s4Theta (adaptedBefore_candW x₀ h44 hκ hκ4 hb h hhm ℓ t) measurableSet_glueGood
    (fun p hp => isGood49_of_mem_glueGood p hp) (lastO ℓ t) r

end Cand

end InteractingSLE.Sec5.CrossCond.StagedS4
