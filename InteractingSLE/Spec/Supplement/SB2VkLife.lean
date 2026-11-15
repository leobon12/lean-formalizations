/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VkFam

/-!
# SB2(1)'s version half: the driver's lifetime is the relative lifetime

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half, ruling R108). The measurable driver of the family
`ρ` (`Vk.exists_measurableDriver`) has lifetime `capLife ρ`. The driver statement asks for the relative lifetime
`⨆ {capClock (liftR flowLift) s : T_L + s < ζ}`.

* `capLife_eq_iSup_of_eqOn` (deterministic, `ζ = ∞`): `capLife ρ = ⨆ s, capClock γ s` for `ρ = γ` on `[0, ∞)` with a
  monotone capacity clock;
* `capClock_relCurve`: `capClock (relCurve γ ℓ) r = capClock γ (clockOf ℓ r)` (the time change maps `[0, r]` onto
  `[0, clockOf ℓ r]`); **`capLife_relCurve_of_eqOn`** (deterministic, `ζ < ∞`): `capLife ρ = ⨆ {capClock γ s : s < ℓ}`;
* **`ae_capLife_eq`**: almost surely at a launch on the entrance event, `capLife (ρ ω)` is the relative lifetime of the
  flow's lift (monotone capacity clock from `Vd.ae_clockData`).

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

open Lv Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- The capacity clock only sees the curve on `[0, ∞)`. -/
theorem capClock_congr_Ici {ρ γ : ℝ → ℂ} (h : EqOn ρ γ (Ici 0)) (t : ℝ) : capClock ρ t = capClock γ t := by
  unfold capClock
  rw [image_congr fun x hx => h (show x ∈ Ici (0 : ℝ) from hx.1)]

/-- **The lifetime of a curve equal to `γ` on `[0, ∞)`** with a monotone capacity clock. -/
theorem capLife_eq_iSup_of_eqOn {ρ γ : ℝ → ℂ} (h : EqOn ρ γ (Ici 0)) (hmono : MonotoneOn (capClock γ) (Ici 0)) :
    Sec7.Lemma71C.capLife ρ = ⨆ s : ℝ≥0, ENNReal.ofReal (capClock γ s) := by
  unfold Sec7.Lemma71C.capLife
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun s => ?_)
  · rw [capClock_congr_Ici h]
    exact le_iSup_of_le (n : ℝ≥0) (by rw [NNReal.coe_natCast])
  · obtain ⟨n, hn⟩ := exists_nat_ge (s : ℝ)
    refine le_iSup_of_le n ?_
    rw [capClock_congr_Ici h]
    exact ENNReal.ofReal_le_ofReal (hmono (show (s : ℝ) ∈ Ici 0 from s.2)
      (mem_Ici.mpr (Nat.cast_nonneg _)) hn)

/-- **The capacity clock of the reparametrized curve.** -/
theorem capClock_relCurve {γ : ℝ → ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ) {r : ℝ} (hr : 0 ≤ r) :
    capClock (relCurve γ ℓ) r = capClock γ (clockOf ℓ r) := by
  have himg : clockOf ℓ '' Icc 0 r = Icc 0 (clockOf ℓ r) := by
    have hc : ContinuousOn (clockOf ℓ) (Icc 0 r) :=
      continuousOn_const.mul (continuousOn_id.div (continuousOn_const.add continuousOn_id) fun x hx => by
        have := hx.1; positivity)
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨clockOf_nonneg hℓ hx.1, (strictMonoOn_clockOf hℓ).monotoneOn hx.1 hr hx.2⟩
    · have := intermediate_value_Icc hr hc
      rwa [clockOf_zero] at this
  unfold capClock
  rw [show relCurve γ ℓ '' Icc 0 r = γ '' (clockOf ℓ '' Icc 0 r) from image_comp γ (clockOf ℓ) (Icc 0 r), himg]

/-- **The lifetime of a curve equal to the reparametrized `γ` on `[0, ∞)`**, `γ` with a monotone capacity clock
on `[0, ℓ)`. -/
theorem capLife_relCurve_of_eqOn {ρ γ : ℝ → ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ) (h : EqOn ρ (relCurve γ ℓ) (Ici 0))
    (hmono : MonotoneOn (capClock γ) (Ico 0 ℓ)) :
    Sec7.Lemma71C.capLife ρ = ⨆ (s : ℝ≥0) (_ : (s : ℝ) < ℓ), ENNReal.ofReal (capClock γ s) := by
  unfold Sec7.Lemma71C.capLife
  refine le_antisymm (iSup_le fun n => ?_) (iSup₂_le fun s hs => ?_)
  · rw [capClock_congr_Ici h, capClock_relCurve hℓ (Nat.cast_nonneg n)]
    have hm := clockOf_mem_Ico hℓ (Nat.cast_nonneg (α := ℝ) n)
    refine le_iSup₂_of_le (clockOf ℓ n).toNNReal (by rw [Real.coe_toNNReal _ hm.1]; exact hm.2) ?_
    rw [Real.coe_toNNReal _ hm.1]
  · -- a natural number `n` with `clockOf ℓ n ≥ s`
    have hsℓ : 0 < ℓ - s := sub_pos.2 hs
    obtain ⟨n, hn⟩ := exists_nat_ge ((s : ℝ) / (ℓ - s))
    have hn' : (s : ℝ) ≤ clockOf ℓ n := by
      unfold clockOf
      have h1 : (0 : ℝ) < 1 + n := by positivity
      rw [mul_div_assoc', le_div_iff₀ h1]
      have := (div_le_iff₀ hsℓ).1 hn
      nlinarith
    refine le_iSup_of_le n ?_
    rw [capClock_congr_Ici h, capClock_relCurve hℓ (Nat.cast_nonneg n)]
    have hm := clockOf_mem_Ico hℓ (Nat.cast_nonneg (α := ℝ) n)
    exact ENNReal.ofReal_le_ofReal (hmono ⟨s.2, hs⟩ hm hn')

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The family's lifetime is the relative lifetime of the flow's lift**, almost surely at a launch on the
entrance event. -/
theorem ae_capLife_eq (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {ρ : Ω → ℝ → ℂ}
    (hρ : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
        (ζ ω = ⊤ → EqOn (ρ ω) (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0)) ∧
        (ζ ω ≠ ⊤ → EqOn (ρ ω) (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
          ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Ve.entT κ b jumps E k u η ζ ω < ζ ω →
      Sec7.Lemma71C.capLife (ρ ω) =
        ⨆ (s : ℝ≥0) (_ : (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω),
        ENNReal.ofReal (capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) s) := by
  filter_upwards [hρ, Vd.ae_clockData h13 hS3 HP] with ω hρω hcd hl hT
  obtain ⟨h1, h2⟩ := hρω hl hT
  obtain ⟨-, hloc⟩ := hcd hl hT
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  -- monotonicity of the capacity clock of the lift on `[0, y]` for `T_L + y < ζ`
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ((TL.toNNReal + y.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
      capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) x ≤
        capClock (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) y := by
    intro x y hx hxy hyζ
    have hy : 0 ≤ y := hx.trans hxy
    have hm := (hloc (TL.toNNReal + y.toNNReal) le_self_add hyζ).2
    have key : ∀ z, z ∈ Icc (0 : ℝ) y →
        z ∈ Icc (0 : ℝ) (((TL.toNNReal + y.toNNReal : ℝ≥0) : ℝ) - (TL.toNNReal : ℝ)) := fun z hz =>
      ⟨hz.1, by rw [NNReal.coe_add, Real.coe_toNNReal _ hy]; linarith [hz.2]⟩
    exact hm (key x ⟨hx, hxy⟩) (key y ⟨hy, le_rfl⟩) hxy
  by_cases hζ : ζ ω = ⊤
  · rw [capLife_eq_iSup_of_eqOn (h1 hζ) fun x hx y hy hxy =>
      hmono x y hx hxy (by rw [hζ]; exact ENNReal.coe_lt_top)]
    refine iSup_congr fun s => ?_
    rw [iSup_pos (show (((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞)) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)]
  · set ℓ : ℝ := (ζ ω).toReal - TL.toReal with hℓ
    have hℓpos : 0 < ℓ := by
      rw [hℓ, sub_pos]; exact (ENNReal.toReal_lt_toReal hTLtop hζ).2 hT
    have hiff : ∀ s : ℝ≥0, (s : ℝ) < ℓ ↔ ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω := fun s => by
      rw [← ENNReal.coe_toNNReal hζ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add, hℓ, hTLr]
      constructor <;> intro h' <;> [skip; skip] <;>
        · have h3 : (ζ ω).toReal = ((ζ ω).toNNReal : ℝ) := rfl
          linarith
    rw [capLife_relCurve_of_eqOn hℓpos (h2 hζ) fun x hx y hy hxy => hmono x y hx.1 hxy (by
      rw [← ENNReal.coe_toNNReal hζ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, NNReal.coe_add,
        Real.coe_toNNReal _ (hx.1.trans hxy)]
      have := hy.2
      rw [hℓ, hTLr] at this
      have h3 : (ζ ω).toReal = ((ζ ω).toNNReal : ℝ) := rfl
      linarith)]
    exact iSup_congr fun s => iSup_congr_Prop (hiff s) fun _ => rfl

end

end InteractingSLE.Theorem14.SB.Vk
