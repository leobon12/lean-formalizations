/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrWindow
import InteractingSLE.Spec.Sec7.R6TnChart

/-! # The real-window chain model from the landed current-chart facts -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Tr

open PocketStop PocketStopSide PocketTraversal Lemma71C R6Fc

/-- Convert `chart_facts` (or `chart_factsInf`) to the real-time model.
In particular the centered left mark is the actual geometric seed mark,
not an independently chosen force point. -/
theorem innerChain_of_facts {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}
    {V P : Set ℂ} {ψ E₀ : ℂ → ℂ} {W : ℝ → ℝ} {p : ℂ}
    (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hVP : V ⊆ P) (hψc : ContinuousOn ψ P) (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    (hW : Continuous W) (hW0 : W 0 = 0) {q₀ t₁ : ℝ≥0} (hq₀ : 0 < q₀) (hqt : q₀ < t₁)
    (hWeq : ∀ r ∈ Icc (0 : ℝ) t₁, segDriver (γ ω) r.toNNReal = W r)
    (htip : E₀ (extendFrom H (fwdMapInv W q₀) 0) = p)
    (hfacts : ∀ q : ℝ≥0, q < t₁ →
      (relChart c γ q ω).IsConformal ∧
      ((relChart c γ q ω).dom : Set ℂ) = V ∩ ψ ⁻¹' (H \ fwdHull W q) ∧
      (∀ w ∈ V, (relChart c γ q ω).1 w = fwdMap W q (ψ w)) ∧
      EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) (relChart c γ q ω).2.1 H ∧
      ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar) :
    ∃ M : InnerChain V P (fun q => relChart c γ q.toNNReal ω) p,
      M.time = q₀ ∧ ∀ q ∈ Ico M.time (M.time + M.horizon),
        R6Tn.leftSeed γ q.toNNReal ω = WangWu.chartAL M.driver q := by
  have htimepos : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have hgap : 0 < (t₁ : ℝ) - q₀ := sub_pos.2 (by exact_mod_cast hqt)
  have hqreal : ∀ q ∈ Ico (q₀ : ℝ) ((q₀ : ℝ) + ((t₁ : ℝ) - q₀)),
      0 ≤ q ∧ q.toNNReal < t₁ := by
    intro q hq
    have hq0 : 0 ≤ q := q₀.coe_nonneg.trans hq.1
    refine ⟨hq0, ?_⟩
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
    linarith [hq.2]
  let M : InnerChain V P (fun q => relChart c γ q.toNNReal ω) p := {
    coord := ψ, inverse := E₀, driver := W, time := q₀, horizon := (t₁ : ℝ) - q₀,
    time_pos := htimepos, horizon_pos := hgap, coord_bij := hψ,
    mem_boundary := hVP, coord_cont := hψc, inverse_eq := hE₀,
    driver_cont := hW, driver_zero := hW0, tip_cont := (hfacts q₀ hqt).2.2.2.2,
    tip_eq := htip,
    dom_eq := fun q hq => by
      have hf := (hfacts q.toNNReal (hqreal q hq).2).2.1
      rwa [Real.coe_toNNReal _ (hqreal q hq).1] at hf,
    conformal := fun q hq => (hfacts q.toNNReal (hqreal q hq).2).1,
    forward_eq := fun q hq w hw => by
      have hf := (hfacts q.toNNReal (hqreal q hq).2).2.2.1 w hw
      rwa [Real.coe_toNNReal _ (hqreal q hq).1] at hf,
    inverse_cont := fun q hq => ⟨_, (hfacts q.toNNReal (hqreal q hq).2).2.2.2⟩ }
  refine ⟨M, rfl, fun q hq => ?_⟩
  have hq0 : 0 ≤ q := (hqreal q hq).1
  have hqt' : q ≤ t₁ := by have := hq.2; change q < q₀ + ((t₁ : ℝ) - q₀) at this; linarith
  have hseed := seedL_eq hW (q := q.toNNReal) (γ := γ) (ω := ω)
    (fun s hs => hWeq s ⟨hs.1, hs.2.trans (by rwa [Real.coe_toNNReal _ hq0])⟩)
  simpa only [R6Tn.leftSeed, Real.coe_toNNReal _ hq0] using hseed

end InteractingSLE.Sec7.R6Tr
