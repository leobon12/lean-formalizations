/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceSelection

/-!
# Active futures in the component selected by infinity

PROVE-R7-GAPEQ. Forbidden-side avoidance and the proved physical component selection
give confinement of the own-mapped future, including visit limits and gap endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan

/-- Interior own-mapped future visits lie in the lift of the unique unbounded
component. No Jordan chart or active-prime-end equality is assumed here. -/
theorem ownFuture_mem_unbounded_component {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : ℝ → ℝ} {η : ℝ → ℂ} {F : Set ℂ} {τ s : ℝ} {p : ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hs0 : 0 ≤ s) (hτs : τ ≤ s)
    (hallowed : AllowedUnboundedComponents W (cfPocket R L r) F τ)
    (hp : ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p))
    (havoid : ∀ t, s ≤ t → η t ∉ F) :
    ∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
      trMap W s t 0 ∈ fwdMap W s ''
        connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p := by
  intro t hst htC htH
  have he := traceMapOut_trMap_zero hη hW hW0 hs0 hst
  have htD : η t ∈ H \ fwdHull W s := he ▸ trMap_zero_mem_domain hW hW0 hs0 htH
  refine ⟨η t, allowed_mem_unbounded_component h h0 hW hallowed hτs hp
    (η t) ⟨htC, htD⟩ (havoid t hst), ?_⟩
  rw [← he, fwdMap_trMap_zero hW hW0 hs0 htH]

/-- Limits of pocket visits, including erased gap endpoints, lie in the closure of
the selected physical component's current lift. -/
theorem ownFuture_mem_closure_unbounded_component {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : ℝ → ℝ} {η : ℝ → ℂ} {F : Set ℂ} {τ s a : ℝ} {p : ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hs0 : 0 ≤ s) (hτs : τ ≤ s)
    (hallowed : AllowedUnboundedComponents W (cfPocket R L r) F τ)
    (hp : ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p))
    (havoid : ∀ t, s ≤ t → η t ∉ F)
    (ha : a ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r}) :
    trMap W s a 0 ∈ closure (fwdMap W s ''
      connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) := by
  exact ownFuture_mem_closure_face hη hW hW0 (h.isCfPocketInf h0).isOpen hs0
    (ownFuture_mem_unbounded_component h h0 hη hW hW0 hs0 hτs hallowed hp havoid) ha

end InteractingSLE.Sec7.R7EndFace
