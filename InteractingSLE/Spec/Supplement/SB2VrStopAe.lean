/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VrStop

/-!
# D10's stops for SB2(1): steps 2 and 3, almost surely

Packet PROVE-AUX61-NOJUMP (decision D10). Almost surely at a launch on the entrance event, D10's physical stops
`physStop` of the flow's lift, the centred flow and the closed bad set of the flow-line word are strictly below the
relative lifetime `Vk.relLife`, nondecreasing, and increase to it.

* `strictBefore_of_top`, `strictBefore_of_fin`: the capacity clock of the lift is strictly increasing before the
  lifetime, since the lift (reparametrized when the lifetime is finite) is a driven curve (`Vd.ae_isDrivenCurve_lift`,
  `PocketTraversal.IsDrivenCurve.strictMonoOn_capClock`).
* **`ae_physStop`**: steps 2 and 3, from step 1 (`ae_tip_bad_of_isFlowLine`), step 3's core
  (`ae_notMem_closure_badSet`, with Lemma G12) and Theorem 1.3's closed trace (`IsFlowLine`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vr

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- With an infinite lifetime the capacity clock of a driven lift is strictly increasing. -/
theorem strictBefore_of_top {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hd : IsDrivenCurve (Vd.liftR γ)) : StrictBefore γ tL ⊤ :=
  fun _ _ hs₁ h12 _ => hd.strictMonoOn_capClock hs₁ (mem_Ici.2 (hs₁.trans h12.le)) h12

/-- With a finite lifetime the capacity clock of a lift whose reparametrization is driven is strictly increasing
before the lifetime. -/
theorem strictBefore_of_fin {γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {Z : ℝ≥0∞} (hZ : Z ≠ ⊤) (hTZ : (tL : ℝ≥0∞) < Z)
    (hd : IsDrivenCurve (relCurve (Vd.liftR γ) (Z.toReal - tL))) : StrictBefore γ tL Z := by
  intro s₁ s₂ hs₁ h12 hs₂
  set ℓ := Z.toReal - tL with hℓdef
  have hZr : (tL : ℝ) < Z.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hZ).2 hTZ
    simpa using this
  have hℓ : 0 < ℓ := by rw [hℓdef]; linarith
  have hs₂ℓ : s₂ < ℓ := by
    have h := (ENNReal.ofReal_lt_iff_lt_toReal (by linarith [tL.2]) hZ).1 hs₂
    rw [hℓdef]; linarith
  have hs₂0 : 0 ≤ s₂ := hs₁.trans h12.le
  set r₁ := s₁ / (ℓ - s₁) with hr₁
  set r₂ := s₂ / (ℓ - s₂) with hr₂
  have hp₁ : 0 < ℓ - s₁ := by linarith
  have hp₂ : 0 < ℓ - s₂ := by linarith
  have hr₁0 : 0 ≤ r₁ := div_nonneg hs₁ hp₁.le
  have hr₂0 : 0 ≤ r₂ := div_nonneg hs₂0 hp₂.le
  have hc : ∀ s : ℝ, 0 ≤ s → s < ℓ → clockOf ℓ (s / (ℓ - s)) = s := fun s _ hsℓ => by
    have hp : 0 < ℓ - s := by linarith
    unfold clockOf
    field_simp
    ring
  have hlt : r₁ < r₂ := by
    rw [hr₁, hr₂, div_lt_div_iff₀ hp₁ hp₂]; nlinarith
  have hm := hd.strictMonoOn_capClock (mem_Ici.2 hr₁0) (mem_Ici.2 hr₂0) hlt
  rw [Vk.capClock_relCurve hℓ hr₁0, Vk.capClock_relCurve hℓ hr₂0, hc s₁ hs₁ (by linarith),
    hc s₂ hs₂0 hs₂ℓ] at hm
  exact hm

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- The closed bad set of SB2(1)'s flow line (centred at its start `u`). -/
def sb2BadClosure (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (u ψ : ℝ) : Set ℂ :=
  closure (badSet (flowLineXL b jumps u) (flowLineXR b jumps u) (flowLineRhoL κ b jumps u ψ)
    (flowLineRhoR κ b jumps u ψ))

/-- **D10 steps 2 and 3 for SB2(1), almost surely.** At a launch on the entrance event, the physical stops of the
flow's lift are positive, strictly below the relative lifetime, nondecreasing, and increase to it. -/
theorem ae_physStop (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      (∀ m, 0 < physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) m) ∧
      (∀ m, physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) m < Vk.relLife κ b jumps E k u η ζ ω) ∧
      Monotone (physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω)) ∧
      ⨆ m, physStop (Ve.flowLift κ b jumps E k u η ζ ω) (fun t => η ω t - u) (sb2BadClosure κ b jumps u ψ)
          (Ve.entT κ b jumps E k u η ζ ω).toNNReal (ζ ω) m = Vk.relLife κ b jumps E k u η ζ ω := by
  have hflow := HP.flow
  obtain ⟨-, -, W, -, -, -, -, -, hgen⟩ := hflow
  filter_upwards [Vd.ae_clockData h13 hS3 HP, Vd.ae_isDrivenCurve_lift h13 hS3 HP, hgen,
    ae_tip_bad_of_isFlowLine HP.flow,
    ae_notMem_closure_badSet HP.kappa_pos HP.kappa_lt_four HP.boundary HP.field HP.flow]
    with ω hcd hdr hg hend hnv hl hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTZ : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [ENNReal.coe_toNNReal hTLtop]; exact hT
  have hζ0 : 0 < ζ ω := lt_of_le_of_lt (zero_le) hT
  have h0 := (hcd hl hT).1
  have hstr : StrictBefore (Ve.flowLift κ b jumps E k u η ζ ω) TL.toNNReal (ζ ω) := by
    by_cases hζ : ζ ω = ⊤
    · rw [hζ]; exact strictBefore_of_top ((hdr hl hT).1 hζ)
    · refine strictBefore_of_fin hζ hTZ ?_
      have := (hdr hl hT).2 hζ
      exact this
  have hcont : ContinuousOn (fun t => η ω t - u) {t | TL.toNNReal ≤ t ∧ (t : ℝ≥0∞) ≤ ζ ω} :=
    hg.2.1.mono fun t ht => ht.2
  have hend' : ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω → (fun t => η ω t - u) T ∈ sb2BadClosure κ b jumps u ψ := by
    intro T hTe
    have hb := hend hζ0 (by rw [← hTe]; exact ENNReal.coe_ne_top)
    rw [← hTe, ENNReal.toNNReal_coe] at hb
    exact subset_closure hb
  have hnv' : ∀ t : ℝ≥0, TL.toNNReal ≤ t → (t : ℝ≥0∞) < ζ ω →
      (fun t => η ω t - u) t ∉ sb2BadClosure κ b jumps u ψ := fun t _ ht => hnv hζ0 t ht
  have hd : 0 < infEDist ((fun t => η ω t - u) TL.toNNReal) (sb2BadClosure κ b jumps u ψ) := by
    rw [infEDist_pos_iff_notMem_closure, sb2BadClosure, closure_closure]
    exact hnv' _ le_rfl hTZ
  refine ⟨fun m => physStop_pos h0 hstr hTZ hcont hd m, fun m => physStop_lt h0 hstr hTZ hcont hend' m, physStop_mono,
    iSup_physStop h0 hstr hTZ hcont hend' isClosed_closure hnv'⟩

end

end InteractingSLE.Theorem14.SB.Vr
