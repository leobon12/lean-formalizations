/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcTrace
import InteractingSLE.Spec.Sec7.R6SafeMeet
import InteractingSLE.Spec.Sec7.PocketStopSideCloseGeometry

/-!
# One current pocket chart in explicit Loewner form

Packet PROVE-R6-FACE2. For the current chart `relChart (shiftChart (pChart A C ψ)) γ q ω` of a bounded Jordan pocket
(`ω ∈ A`, `γ` a driven curve, `q` below a live capacity time `t₁`), `chart_facts` fixes one continuous driver `W`
with a global Loewner trace agreeing with the canonical driver on `[0, t₁]` (`exists_loewnerTrace_of_driven`) and one
inverse boundary extension `E₀` of `ψ⁻¹`, and gives for every `q < t₁`: conformality, the domain
`C ∩ ψ⁻¹(ℍ ∖ K_q)` (`K_q = fwdHull W q`), the forward map `f_q ∘ ψ` on the domain, and the continuous inverse
extension `E₀ ∘ F̄_q` (`F̄_q` the boundary extension of `f_q⁻¹`). Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Fc

open PocketTraversal Lemma71C PocketStop PocketStopField
open SupercriticalConformalCovariance (IsConformalBijection)

variable {Ω : Type*} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **One current pocket chart in explicit Loewner form** (see the module docstring). -/
theorem chart_facts (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCb : Bornology.IsBounded (C ω)) {x₀ y₀ : ℂ}
    (hx₀ : x₀ ∉ C ω) (hψ : Sec6.IsJordanCoord (C ω) x₀ y₀ (ψ ω)) (hω : ω ∈ A) (hγ : IsDrivenCurve (γ ω))
    {t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < capLife (γ ω)) :
    ∃ E₀ : ℂ → ℂ, EqOn E₀ (Function.invFunOn (ψ ω) (C ω)) H ∧ ContinuousOn E₀ Hbar ∧
      MapsTo E₀ Hbar (closure (C ω) \ {x₀}) ∧
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) t₁, segDriver (γ ω) r.toNNReal = W r) ∧
    ∃ η : ℝ → ℂ, IsLoewnerTrace W η ∧ (∀ s : ℝ, 0 ≤ s → s ≤ t₁ → η s = γ ω (capInv (γ ω) s)) ∧
    ∀ q : ℝ≥0, q < t₁ →
      (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).IsConformal ∧
      ((relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).dom : Set ℂ) =
        C ω ∩ ψ ω ⁻¹' (H \ fwdHull W q) ∧
      (∀ w ∈ C ω, (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).1 w = fwdMap W q (ψ ω w)) ∧
      EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z))
        (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω).2.1 H ∧
      ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar := by
  obtain ⟨hc, hdom, hfwd⟩ := R5Phase.shiftChart_dom_facts hCo hCH hψc n ω hω
  have hinv : (shiftChart (pChart A C ψ ω) (n ω)).2.1 = Function.invFunOn (ψ ω) (C ω) := pInv_of_mem hω
  obtain ⟨E₀, hE₀, hE₀c, hE₀m⟩ := PocketStopSide.exists_inverse_extension_of_jordan_coord hCb hx₀ hψ hc hdom hfwd
  rw [hinv] at hE₀
  obtain ⟨W, hWc, hW0, hWeq, η, hη, hηeq⟩ := exists_loewnerTrace_of_driven hγ ht₁
  have hWeq' : ∀ r ∈ Icc (0 : ℝ) t₁, segDriver (γ ω) r.toNNReal = W r := fun r hr => (hWeq hr).symm
  refine ⟨E₀, hE₀, hE₀c, hE₀m, W, hWc, hW0, hWeq', η, hη, hηeq, fun q hq => ?_⟩
  have hq' : (q : ℝ) < t₁ := by exact_mod_cast hq
  have hlive : (q : ℝ≥0∞) < capLife (γ ω) := lt_trans (by exact_mod_cast hq) ht₁
  have hrel : relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω =
      (shiftChart (pChart A C ψ ω) (n ω)).loewner W q :=
    loewner_congr _ q.coe_nonneg hq' hWeq'
  have hK : fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q = fwdHull W q :=
    fwdHull_eq_of_eqOn q.coe_nonneg hq' fun r hr => hWeq' r hr
  obtain ⟨hFc, hFeq, hFm⟩ := extendFrom_props hη hWc hW0 q.coe_nonneg
  refine ⟨PocketStopSide.isConformal_relChart_of_driven hγ hlive hc, ?_, fun w hw => ?_, fun z hz => ?_,
    hE₀c.comp hFc hFm⟩
  · rw [R6Safe.relChart_dom_eq_inter (n := n) hCo hCH hψc hω hγ hlive, hK]
  · rw [hrel]
    show fwdMap W q ((shiftChart (pChart A C ψ ω) (n ω)).1 w) = _
    rw [hfwd hw]
  · rw [hrel]
    show E₀ (extendFrom H (fwdMapInv W q) z) = (shiftChart (pChart A C ψ ω) (n ω)).2.1 (fwdMapInv W q z)
    rw [hFeq hz, hinv]
    exact hE₀ (QuantumZipper.RS.fwdMapInv_mem_H hWc hW0 q.coe_nonneg hz)

end InteractingSLE.Sec7.R6Fc
