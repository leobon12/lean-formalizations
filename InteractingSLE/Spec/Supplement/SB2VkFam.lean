/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VjRel
import InteractingSLE.Spec.Restart.ChartMeasFlow

/-!
# SB2(1)'s version half: the measurable driven family and the measurable driver

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108).

* `IsDrivenCurve.congr` (deterministic): a driven curve stays driven when changed off `[0, ∞)` only;
* **`exists_drivenFamily`**: for a measurable clock `a` that is a.s. `Vc.clockOf (flowLift)`, a family
  `ρ : Ω → ℝ → ℂ`, measurable at every `r ≥ 0`, with a.s. at a launch on the entrance event `ρ ω = liftR (flowLift ω)`
  on `[0, ∞)` if `ζ = ∞`, and `ρ ω = relCurve (liftR (flowLift ω)) (ζ − T_L)` there otherwise. `ρ ω r` is the jointly
  measurable absolute lift (`Vj.exists_joint_absLift`) read at the measurable entrance `Vj.entMeas a` plus the relative
  time `r` (resp. `clockOf (ζ − entMeas) r`).
* **`ae_isDrivenCurve_family`**: almost surely there, `ρ ω` is a driven curve (`Vd.ae_isDrivenCurve_lift`);
* **`exists_measurableDriver`** (no use of Theorem 1.3): `Lk.exists_measurable_driver_of_drivenCurves` on a family
  driven a.s. at a launch on the entrance event gives a measurable driver
  `W` from `0`, continuous before a measurable lifetime `U`, with a.s. `U ω = capLife (ρ ω)` and
  `IsGeneratingTrace (W · ω) T (capTrace (ρ ω))` for every `T < U ω`.

Theorem 1.3 and the named S3 input as before (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vk

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal

/-- **A driven curve stays driven when changed off `[0, ∞)` only.** -/
theorem IsDrivenCurve.congr {γ γ' : ℝ → ℂ} (hγ : IsDrivenCurve γ) (h : EqOn γ γ' (Ici 0)) : IsDrivenCurve γ' := by
  have himg : ∀ t : ℝ, γ' '' Icc 0 t = γ '' Icc 0 t := fun t =>
    image_congr fun x hx => (h (show x ∈ Ici (0 : ℝ) from hx.1)).symm
  have hcap : Sec7.Lemma71C.capClock γ' = Sec7.Lemma71C.capClock γ := funext fun t => by
    unfold Sec7.Lemma71C.capClock; rw [himg]
  have h0' : γ' 0 = 0 := by rw [← h (Set.mem_Ici.2 le_rfl)]; exact hγ.zero
  refine ⟨hγ.continuousOn.congr fun x hx => (h hx).symm, h0', fun S hS => ?_⟩
  obtain ⟨W, hWc, hW0, h0, hsm, hcc, hhull⟩ := hγ.localDriver S hS
  rw [hcap]
  exact ⟨W, hWc, hW0, h0, hsm, hcc, fun t ht => by rw [himg]; exact hhull t ht⟩

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

/-- **The measurable driven family** (the relative lift, reparametrized when the remaining life is finite). -/
theorem exists_drivenFamily (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {a : ℝ≥0 → Ω → ℝ≥0∞} (ha : ∀ t, Measurable (a t))
    (hae : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      ∀ t, a t ω = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) t) :
    ∃ ρ : Ω → ℝ → ℂ, (∀ r, 0 ≤ r → Measurable fun ω => ρ ω r) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0)) := by
  classical
  obtain ⟨G, F, hGm, hGn, hFm, hF⟩ := Vj.exists_joint_absLift h13 hS3 HP I D
  have he : Measurable (Vj.entMeas a) := Vj.measurable_entMeas ha
  have hζm : Measurable ζ := Restart.measurable_lifetime_of_isFlowLine HP.flow
  set tm : Ω → ℝ → ℝ≥0 := fun ω r =>
    if ζ ω = ⊤ then r.toNNReal else (clockOf ((ζ ω).toReal - (Vj.entMeas a ω).toReal) r).toNNReal with htm
  refine ⟨fun ω r => F (ω, (Vj.entMeas a ω).toNNReal + tm ω r), fun r _ => ?_, ?_⟩
  · have hL : Measurable fun ω => (ζ ω).toReal - (Vj.entMeas a ω).toReal := hζm.ennreal_toReal.sub he.ennreal_toReal
    have hcl : Continuous fun L : ℝ => (clockOf L r).toNNReal :=
      continuous_real_toNNReal.comp (continuous_id.mul continuous_const)
    have htmm : Measurable fun ω => tm ω r :=
      Measurable.ite (hζm (measurableSet_singleton ⊤)) measurable_const (hcl.measurable.comp hL)
    exact hFm.comp (measurable_id.prodMk (he.ennreal_toNNReal.add htmm))
  · have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGn
    filter_upwards [Vj.ae_entMeas_eq h13 hS3 HP hae, D.ae_mem_event_iff, hGae] with ω hent hev hωG hl hT
    have hωE : ω ∈ D.event := (hev hl).2 hT
    have he' := hent hl hT
    set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
    have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
    have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
    refine ⟨fun hζ r hr => ?_, fun hζ r hr => ?_⟩
    · have hr' : (0 : ℝ) ≤ r := hr
      show F (ω, (Vj.entMeas a ω).toNNReal + tm ω r) = _
      simp only [htm, hζ, ↓reduceIte]
      rw [he']
      rw [hF ω ⟨hωG, hωE⟩ _ (by rw [hζ]; exact ENNReal.coe_lt_top)]
      unfold Vi.absLift
      rw [add_tsub_cancel_left]
      rfl
    · have hr' : (0 : ℝ) ≤ r := hr
      set ℓ : ℝ := (ζ ω).toReal - TL.toReal with hℓ
      have hℓpos : 0 < ℓ := by
        rw [hℓ, sub_pos]
        exact (ENNReal.toReal_lt_toReal hTLtop hζ).2 hT
      have hcm := clockOf_mem_Ico hℓpos hr'
      show F (ω, (Vj.entMeas a ω).toNNReal + tm ω r) = _
      simp only [htm, hζ, ↓reduceIte]
      rw [he']
      have hlt : ((TL.toNNReal + (clockOf ℓ r).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        rw [← ENNReal.coe_toNNReal hζ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add,
          Real.coe_toNNReal _ hcm.1]
        have h1 := hcm.2
        rw [hℓ] at h1
        have h2 : TL.toReal = (TL.toNNReal : ℝ) := rfl
        have h3 : (ζ ω).toReal = ((ζ ω).toNNReal : ℝ) := rfl
        linarith
      rw [hF ω ⟨hωG, hωE⟩ _ hlt]
      unfold Vi.absLift
      rw [add_tsub_cancel_left]
      rfl

/-- **The family is a driven curve**, almost surely at a launch on the entrance event. -/
theorem ae_isDrivenCurve_family (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω → IsDrivenCurve (ρ ω) := by
  filter_upwards [hρ, Vd.ae_isDrivenCurve_lift h13 hS3 HP] with ω hρω hdr hl hT
  obtain ⟨h1, h2⟩ := hρω hl hT
  obtain ⟨d1, d2⟩ := hdr hl hT
  by_cases hζ : ζ ω = ⊤
  · have d : IsDrivenCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) := d1 hζ
    exact IsDrivenCurve.congr d fun x hx => ((h1 hζ) hx).symm
  · have d : IsDrivenCurve (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
        ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) := d2 hζ
    exact IsDrivenCurve.congr d fun x hx => ((h2 hζ) hx).symm

/-- **The measurable driver of the family**: measurable, from `0`, continuous before a measurable lifetime `U`;
almost surely at a launch on the entrance event, `U = capLife ρ` and the capacity reparametrization of `ρ` is a
generating trace on every horizon below `U`. -/
theorem exists_measurableDriver (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) {ρ : Ω → ℝ → ℂ}
    (hρm : ∀ r, 0 ≤ r → Measurable fun ω => ρ ω r)
    (hρd : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      IsDrivenCurve (ρ ω)) :
    ∃ (W : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ≥0∞), (∀ t, Measurable (W t)) ∧ Measurable U ∧ (∀ ω, W 0 ω = 0) ∧
      (∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < U ω}) ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        U ω = Sec7.Lemma71C.capLife (ρ ω) ∧
          ∀ T : ℝ≥0∞, T < U ω → IsGeneratingTrace (fun t => W t ω) T (capTrace (ρ ω)) := by
  have hgood : ∀ᵐ ω ∂P, (ω ∈ launchSet κ b jumps E (k + 1) →
      (ω ∈ D.event ↔ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω)) ∧
      (ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω → IsDrivenCurve (ρ ω)) := by
    filter_upwards [D.ae_mem_event_iff, hρd] with ω hev hd
    exact ⟨hev, hd⟩
  obtain ⟨G, hGm, hGn, hG⟩ := Vf.exists_measurable_conull hgood
  have hEv : MeasurableSet D.event := (D.absMarks_le HP 0) _ (D.marks_le_absMarks 0 _ (D.measurableSet_event HP))
  have hdr : ∀ ω ∈ G ∩ D.event, IsDrivenCurve (ρ ω) := fun ω hω => by
    have hl := D.event_subset hω.2
    exact (hG ω hω.1).2 hl (((hG ω hω.1).1 hl).1 hω.2)
  obtain ⟨W, U, hWm, hUm, hW0, hWc, hGW⟩ := Lk.exists_measurable_driver_of_drivenCurves hρm (hGm.inter hEv) hdr
  refine ⟨W, U, hWm, hUm, hW0, hWc, ?_⟩
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGn
  filter_upwards [hGae, D.ae_mem_event_iff] with ω hωG hev hl hT
  exact hGW ω ⟨hωG, (hev hl).2 hT⟩

end

end InteractingSLE.Theorem14.SB.Vk
