import QuantumZipper.Proofs.Zipper.SWCoreB7bTrans
import QuantumZipper.Proofs.Zipper.SWCoreN2Final
import QuantumZipper.Proofs.Zipper.BdryWinMkFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b (2): uniform boundary transport over a finite-parameter family, almost surely

Decision D64. For a finite-parameter family `q ↦ Ψ q` of maps of one rational boundary class,
Lipschitz in `q` on the `ρ`-thickening and indexed by a bounded set with a Lipschitz retraction,
the free field satisfies a.s. the uniform boundary transport over the family, for every
continuous test function supported in `(a,b)`:

* `ae_transport_family` — from the proved window node (`SWCore.bdryWindowStmt_holds`), the proved
  family distortion core (`SWCore.swcn2_bdryDistFam`) and the family transport
  `SWCore.transport_fam` (SWC-B5's proof restricted to the family).

Sources: Sheffield–Wang, arXiv:1605.06171, Thm 4.3 (p. 19) and Lemmas 3.4–3.5, through the cited
repository nodes. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Uniform boundary transport over a finite-parameter family, a.s.** -/
theorem ae_transport_family (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ) (K : Set (Fin n → ℝ)) {a b ρ M m : ℚ} {L R : ℝ}
    {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : (a : ℝ) < b) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (a : ℝ) b →
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ K,
        |∫ t, f t ∂bdryApprox γ (coordChange (X ω) (Ψ q) (Qc γ)) k -
          ∫ u in Icc (Ψ q (a : ℝ)).re (Ψ q (b : ℝ)).re,
            f (Function.invFunOn (fun t : ℝ => (Ψ q t).re) (Icc (a : ℝ) b) u)
              ∂qBoundaryMeasure γ (X ω)| ≤ η := by
  obtain ⟨c, c', hc, hc', hW⟩ := bdryWindowStmt_holds γ hγ hγ2
  have hS : Ψ '' K ⊆ BdryClass a b ρ M m := by
    rintro _ ⟨q, hq, rfl⟩; exact hcl q hq
  filter_upwards [hW P X hX, swcn2_bdryDistFam hX γ Ψ K hab hρ hm hL hcl hlip hπ hπK hπid hR hKR,
    RegSample.ae_isRegularSample hX, BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2]
    with ω hω1 hω2 hω3 hω4 f hf hfc hfs η hη
  haveI := hω4.1
  have hDS : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ ∈ Ψ '' K, ∀ t ∈ Icc (a : ℝ) b,
      |avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - Qc γ * CoordChange.cc ψ t (radius k) -
        evalReg (X ω) (foldedCircle (((ψ t).re : ℝ) : ℂ) (radius k * ‖deriv ψ t‖))| ≤ η := by
    intro η hη
    filter_upwards [hω2 η hη] with k hk
    rintro _ ⟨q, hq, rfl⟩ t ht
    exact hk q hq t ht
  filter_upwards [transport_fam hγ hc hc' hω1 hω3 a b ρ M m hρ hm hS hDS hf hfc hfs hη]
    with k hk q hq
  exact hk (Ψ q) ⟨q, hq, rfl⟩

end SWCore
end QuantumZipper
