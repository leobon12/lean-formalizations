import QuantumZipper.Proofs.Zipper.SWCoreB7bFamAS

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-WT (2): integrability of test functions against the family, almost surely

Task SWC-B7b-WT (decision D64). On the event of `SWCore.ae_transport_family`, every continuous
nonnegative test function supported in `(a,b)` is, eventually in `k`, integrable against all the
boundary approximations `bdryApprox γ (coordChange (X ω) (Ψ q) (Qc γ)) k`, `q ∈ K`
(`ae_integrable_family`): the upper bound of `SWCore.transport_nonneg_fam` makes the lower
integral finite. Same a.s. event as `ae_transport_family`; own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Eventual integrability of nonnegative test functions over the family, a.s.** -/
theorem ae_integrable_family (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {n : ℕ} (Ψ : (Fin n → ℝ) → ℂ → ℂ) (K : Set (Fin n → ℝ)) {a b ρ M m : ℚ} {L R : ℝ}
    {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : (a : ℝ) < b) (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    (hR : 0 ≤ R) (hKR : ∀ q ∈ K, ‖q‖ ≤ R) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (a : ℝ) b →
      (∀ t, 0 ≤ f t) → ∀ᶠ k in atTop, ∀ q ∈ K,
        Integrable f (bdryApprox γ (coordChange (X ω) (Ψ q) (Qc γ)) k) := by
  obtain ⟨c, c', hc, hc', hW⟩ := bdryWindowStmt_holds γ hγ hγ2
  have hS : Ψ '' K ⊆ BdryClass a b ρ M m := by
    rintro _ ⟨q, hq, rfl⟩; exact hcl q hq
  filter_upwards [hW P X hX, swcn2_bdryDistFam hX γ Ψ K hab hρ hm hL hcl hlip hπ hπK hπid hR hKR,
    RegSample.ae_isRegularSample hX, BdryExist.ae_isVagueLimitR_qBoundaryMeasure hX hγ hγ2]
    with ω hω1 hω2 hω3 hω4 f hf hfc hfs hf0
  haveI := hω4.1
  have hDS : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ ψ ∈ Ψ '' K, ∀ t ∈ Icc (a : ℝ) b,
      |avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - Qc γ * CoordChange.cc ψ t (radius k) -
        evalReg (X ω) (foldedCircle (((ψ t).re : ℝ) : ℂ) (radius k * ‖deriv ψ t‖))| ≤ η := by
    intro η hη
    filter_upwards [hω2 η hη] with k hk
    rintro _ ⟨q, hq, rfl⟩ t ht
    exact hk q hq t ht
  filter_upwards [transport_nonneg_fam hγ hc hc' hω1 hω3 a b ρ M m hρ hm hS hDS hf hfc hfs hf0
    (ε := 1) one_pos] with k hk q hq
  have h1 := (hk (Ψ q) ⟨q, hq, rfl⟩).1
  exact (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
    (Eventually.of_forall hf0)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1)

end SWCore
end QuantumZipper
