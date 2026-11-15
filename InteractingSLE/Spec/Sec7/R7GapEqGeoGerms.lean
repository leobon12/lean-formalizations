/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinAttach

/-!
# Attachment input in the form of R.5's incident germ comparison

PROVE-R7-GAPEQ. The earlier and later conditional means may differ. Only their difference's
zero germ along the same incident filter is needed. This is the form supplied by the R.5
local increment argument of PROVE-POCKET-SIDEIN; no equality of complete means is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE.Sec7.R7GapEqGeo

open Sec6 R7StopIn Aux37Attach R7GapEqFin

/-- **One-barrier attachment constancy from R.5-compatible incident germs.** The named
`hcompare` is left to the field argument. Its zero-increment clause allows the means to be
chosen with different labels, as required by Astra follow-up 5 §3. -/
theorem barrierAttachConst_of_increment_germs
    {η B : ℝ → ℂ} {C : Set ℂ} {τ σ : ℝ}
    (hη : ContinuousOn η (Ici 0)) (hBc : ContinuousOn B (Icc 0 1)) (hBi : InjOn B (Icc 0 1))
    (hrev : R16.IsReverseVisitOrder B fun t => η '' Icc 0 t)
    (hτ0 : 0 ≤ τ) (hτ : η τ = B 1) (marks : Finset ℝ)
    {χ lam lam' ε θ : ℝ} (hχ : 0 < χ) (hlam : lam - lam' = Real.pi * χ / 2)
    (hside : (ε = 1 ∧ θ ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) ∨
      (ε = -1 ∧ θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)))
    (hcompare : ∀ r s v v₁ v₂ : ℚ, IsAttachWitness η C B τ σ r s v v₁ v₂ →
      (∀ x ∈ marks, x ∉ Icc (v : ℝ) v₂) →
      ∃ (G : Filter ℂ) (Mold Mnow Lf Lc : ℂ → ℝ) (k : ℤ), G.NeBot ∧
        Tendsto (fun z => Mnow z - Mold z) G (𝓝 0) ∧
        Tendsto (fun z => Mold z + χ * Lf z) G (𝓝 (ε * lam - θ * χ)) ∧
        Tendsto (fun z => Mnow z + χ * Lc z) G (𝓝 (ε * lam' - Real.pi * χ)) ∧
        Tendsto (fun z => Lf z - Lc z) G (𝓝 (2 * Real.pi * k))) :
    BarrierAttachConst η C B τ σ := by
  apply barrierAttachConst_of_germs hη hBc hBi hrev hτ0 hτ marks hχ hlam hside
  intro r s v v₁ v₂ hw hm
  obtain ⟨G, Mold, Mnow, Lf, Lc, k, hG, hdiff, hflow, hcf, harg⟩ :=
    hcompare r s v v₁ v₂ hw hm
  refine ⟨G, Mnow, Lf, Lc, k, hG, ?_, hcf, harg⟩
  have hlim := hdiff.add hflow
  rw [zero_add] at hlim
  exact hlim.congr fun z => by ring

end InteractingSLE.Sec7.R7GapEqGeo
