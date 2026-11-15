/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SxStage

/-!
# GW2's stage identity: exhausting announced GB6 versions with FINITE stops, for every `s`

Packet PROVE-GW2-RELDET, ruling R106.

* `isGB6RelVersionA_constCap`: an announced version capped at a constant `K > 0` (stop `min(V, K)`), by
  `GW2SxCap.isGB6RelVersionA_ruleCap`.
* `exists_finite_family`: from an exhausting family of announced versions, an exhausting family whose stops are
  finite everywhere: index `n = ⟨m, k⟩` (`Nat.pair`), stop `min(V₀ m, k + 1)`. Every finite value below some `V₀ m`
  is below some new stop. Finite stops give PROVE-GW2-SDE's open item `stgStartM ≠ ⊤` for free (`stgStartM ≤ V`).
* `exists_versionsA_all`: `GW2SxStage.exists_versionsA_uncapped` for EVERY `s`. At `s = 0` the interior-tip event is
  null (GB6's `exists_versionsR_at_zero`, with vacuous announcements).
* `versionsA_timeCap_family`: any exhausting family stopped at the physical time `Δ` (the proof of
  `GW2SxStage.exists_versionsA_timeCap`, for an arbitrary family).
* **`exists_versionsA_fin_all`**, **`exists_versionsA_fin_timeCap`**: exhausting announced versions with finite stops,
  for any transient explored curve and every `s`, without and with the time cap.

Conditional helpers with distinct names; the inputs are the regularity of the two curves only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId

section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}

theorem iSup_capSeq {K : ℝ≥0} (hK : 0 < K) : ⨆ n, (capSeq K n : ℝ≥0∞) = K := by
  refine le_antisymm (iSup_le fun n => ENNReal.coe_le_coe.2 (capSeq_lt hK n).le) (le_of_forall_lt fun x hx => ?_)
  have hxt : x ≠ ⊤ := ne_top_of_lt hx
  have hx' : x.toNNReal < K := by
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hxt]
    exact hx
  obtain ⟨n, hn⟩ := exists_lt_capSeq hK hx'
  refine lt_iSup_iff.2 ⟨n, ?_⟩
  rw [← ENNReal.coe_toNNReal hxt]
  exact ENNReal.coe_lt_coe.2 hn

/-- **An announced version capped at a constant.** -/
theorem isGB6RelVersionA_constCap {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α R V) (hrecm : Measurable (gb6Rec s Wα ζα)) {K : ℝ≥0}
    (hK : 0 < K) :
    Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (ruleCapDrv R (ruleCapStop s Wα ζα (fun _ => (K : ℝ≥0∞)) R V))
      (ruleCapStop s Wα ζα (fun _ => (K : ℝ≥0∞)) R V) :=
  isGB6RelVersionA_ruleCap hver hrecm measurable_const (fun _ _ _ _ => rfl)
    (ae_of_all _ fun _ _ _ => ENNReal.coe_pos.2 hK) (ρa := fun n _ => (capSeq K n : ℝ≥0∞))
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ hnm => ENNReal.coe_le_coe.2 (capSeq_mono K hnm))
    (ae_of_all _ fun _ _ => ⟨fun _ n => ENNReal.coe_lt_coe.2 (capSeq_lt hK n), by rw [iSup_capSeq hK]⟩)

/-- **An exhausting family of announced versions with finite stops.** -/
theorem exists_finite_family {R₀ : ℕ → ℝ≥0 → Ω → ℝ} {V₀ : ℕ → Ω → ℝ≥0∞}
    (hRV : ∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R₀ m) (V₀ m)) (hrecm : Measurable (gb6Rec s Wα ζα)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R n) (V n)) ∧ (∀ n ω, V n ω ≤ V₀ n.unpair.1 ω) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧ ∀ ω (x : ℝ≥0∞), x ≠ ⊤ → ∀ m, x < V₀ m ω → ∃ n, x < V n ω := by
  set K : ℕ → ℝ≥0 := fun n => (n.unpair.2 : ℝ≥0) + 1 with hKdef
  have hK : ∀ n, 0 < K n := fun n => by positivity
  refine ⟨fun n => ruleCapDrv (R₀ n.unpair.1) (ruleCapStop s Wα ζα (fun _ => (K n : ℝ≥0∞)) (R₀ n.unpair.1)
      (V₀ n.unpair.1)), fun n => ruleCapStop s Wα ζα (fun _ => (K n : ℝ≥0∞)) (R₀ n.unpair.1) (V₀ n.unpair.1),
    fun n => isGB6RelVersionA_constCap (hRV n.unpair.1) hrecm (hK n), fun n ω => min_le_left _ _,
    fun n ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _), fun ω x hx m hxm => ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_gt x.toNNReal
  refine ⟨Nat.pair m k, ?_⟩
  change x < min (V₀ (Nat.pair m k).unpair.1 ω) (K (Nat.pair m k) : ℝ≥0∞)
  simp only [hKdef, Nat.unpair_pair]
  refine lt_min hxm ?_
  rw [← ENNReal.coe_toNNReal hx]
  exact ENNReal.coe_lt_coe.2 (hk.trans (lt_add_one _))

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Exhausting announced versions for any transient explored curve, for every `s`.** -/
theorem exists_versionsA_all [IsProbabilityMeasure P] (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  by_cases hs0 : s = 0
  · subst hs0
    have hα0 : ∀ᵐ ω ∂P, α ω 0 = 0 := hα.mono fun _ hω => hω.1
    obtain ⟨R, V, hRV, hex⟩ := exists_versionsR_at_zero (P := P) (W := W) (Wα := Wα) (ζα := ζα) (γ := γ) hα0
    refine ⟨R, V, fun m => ⟨hRV m, fun _ _ => 0, fun _ => measurable_const, fun _ _ _ _ _ => rfl,
      fun _ _ => ENNReal.zero_ne_top, fun _ _ _ _ => le_rfl, ?_⟩, hex⟩
    filter_upwards [ae_gb6RecGood hF hα 0, hα0] with ω hg hω hm
    obtain ⟨-, hH⟩ := (mem_gb6TS_iff hg).2 hm
    rw [hω] at hH
    exact ((lt_irrefl (0 : ℝ)) hH).elim
  · exact exists_versionsA_uncapped hF hα hNR hWm hW s (pos_iff_ne_zero.2 hs0)

/-- **Any exhausting family of announced versions, stopped at the physical time `Δ`.** -/
theorem versionsA_timeCap_family (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {R₀ : ℕ → ℝ≥0 → Ω → ℝ} {V₀ : ℕ → Ω → ℝ≥0∞}
    (hRV : ∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R₀ m) (V₀ m))
    (hex : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V₀ m ω)
    {Δ : ℝ≥0} (hΔ : 0 < Δ) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧ (∀ m ω, V m ω ≤ V₀ m ω) ∧
      (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ m, V m ω ≤ capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → t < Δ →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  have hcap := fun m => isGB6RelVersionA_timeCap hF hα hW (hRV m) hΔ
  have hcapae : ∀ᵐ ω ∂P, ∀ m, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ruleCapStop s Wα ζα (timeCapRule s Δ) (R₀ m) (V₀ m) ω =
        min (V₀ m ω) (capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) := ae_all_iff.2 fun m => (hcap m).2
  refine ⟨fun m => ruleCapDrv (R₀ m) (ruleCapStop s Wα ζα (timeCapRule s Δ) (R₀ m) (V₀ m)),
    fun m => ruleCapStop s Wα ζα (timeCapRule s Δ) (R₀ m) (V₀ m), fun m => (hcap m).1,
    fun m ω => min_le_left _ _, ?_, ?_⟩
  · filter_upwards [hcapae] with ω hω hs' hsH m
    rw [hω m hs' hsH]
    exact min_le_right _ _
  · filter_upwards [hcapae, hex, ae_timeCap_sample hF hα hW (hRV 0).1.1] with ω hω hexω hsam hs' hsH t ht htΔ
    obtain ⟨-, ha0, ham, -, -, -⟩ := hsam hs' hsH
    obtain ⟨m, hm⟩ := hexω hs' hsH t ht
    refine ⟨m, ?_⟩
    rw [hω m hs' hsH]
    refine lt_min hm ?_
    unfold capClock
    split_ifs with hΔT
    · have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < gb6Tc s γ α ω := (ENNReal.coe_le_coe.2 zero_le).trans_lt ht
      have hat : 0 ≤ gb6Clock s W Wα ω t := by
        rw [← ha0]
        exact ham.monotoneOn h0T ht zero_le
      have htΔ' := ham ht hΔT htΔ
      exact (ENNReal.ofReal_lt_ofReal_iff (hat.trans_lt htΔ')).2 htΔ'
    · exact ENNReal.ofReal_lt_top

/-- **Exhausting announced versions with finite stops, for any transient explored curve and every `s`.** -/
theorem exists_versionsA_fin_all [IsProbabilityMeasure P] (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R n) (V n)) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∃ n, ENNReal.ofReal (gb6Clock s W Wα ω t) < V n ω := by
  obtain ⟨R₀, V₀, hRV₀, hex₀⟩ := exists_versionsA_all hF hα hNR hWm hW s
  obtain ⟨R, V, hRV, -, hfin, hex⟩ := exists_finite_family hRV₀ (measurable_recOf_cfE hF s).2
  refine ⟨R, V, hRV, hfin, ?_⟩
  filter_upwards [hex₀] with ω hω hs hsH t ht
  obtain ⟨m, hm⟩ := hω hs hsH t ht
  exact hex ω _ ENNReal.ofReal_ne_top m hm

/-- **Exhausting announced versions with finite stops, stopped at the physical time `Δ`, for every `s`.** -/
theorem exists_versionsA_fin_timeCap [IsProbabilityMeasure P] (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) {Δ : ℝ≥0} (hΔ : 0 < Δ) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R n) (V n)) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ n, V n ω ≤ capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω → t < Δ →
        ∃ n, ENNReal.ofReal (gb6Clock s W Wα ω t) < V n ω := by
  have hW' : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) :=
    hW.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  obtain ⟨R₀, V₀, hRV₀, hex₀⟩ := exists_versionsA_all hF hα hNR hWm hW s
  obtain ⟨R₁, V₁, hRV₁, -, hcap₁, hex₁⟩ := versionsA_timeCap_family hF hα hW' hRV₀ hex₀ hΔ
  obtain ⟨R, V, hRV, hle, hfin, hex⟩ := exists_finite_family hRV₁ (measurable_recOf_cfE hF s).2
  refine ⟨R, V, hRV, hfin, ?_, ?_⟩
  · filter_upwards [hcap₁] with ω hω hs hsH n
    exact (hle n ω).trans (hω hs hsH _)
  · filter_upwards [hex₁] with ω hω hs hsH t ht htΔ
    obtain ⟨m, hm⟩ := hω hs hsH t ht htΔ
    exact hex ω _ ENNReal.ofReal_ne_top m hm

end Generic

end InteractingSLE.Theorem14.GW2Rd
