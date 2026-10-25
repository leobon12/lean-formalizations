import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaLower
import SupercriticalLQGUniqueness.B2.PfeWeyl.Inputs

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem finite_small_annulus_costs
    {G : ℕ → LSCMetric} {D : LSCMetric} {K' K'' : Set ℂ}
    (hsmall : SmallAnnulusCosts G D K' K'')
    (s : Finset ℂ) (hs : ∀ z ∈ s, z ∈ K' ∧ IsNonsingular D z)
    (δ ρ : ℝ) (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∃ A : (z : ℂ) → z ∈ s → EuclideanAnnulus,
      (∀ z (hz : z ∈ s),
        IsRationalDoubleAnnulus (A z hz) ∧
        dist z (A z hz).center < (A z hz).innerRadius ∧
        (A z hz).outerRadius < ρ ∧
        (A z hz).toSet ⊆ K'') ∧
      ∀ᶠ n in atTop, ∀ z (hz : z ∈ s),
        aroundDist (G n) (A z hz) < ENNReal.ofReal δ := by
  classical
  have hchoice : ∀ z : {z // z ∈ s}, ∃ A : EuclideanAnnulus,
      IsRationalDoubleAnnulus A ∧
      dist z.1 A.center < A.innerRadius ∧ A.outerRadius < ρ ∧
      A.toSet ⊆ K'' ∧
      ∀ᶠ n in atTop, aroundDist (G n) A < ENNReal.ofReal δ := by
    intro z
    exact hsmall z.1 (hs z.1 z.2).1 (hs z.1 z.2).2 δ hδ ρ hρ
  choose A hA using hchoice
  refine ⟨fun z hz => A ⟨z, hz⟩, ?_, ?_⟩
  · intro z hz
    exact ⟨(hA ⟨z, hz⟩).1, (hA ⟨z, hz⟩).2.1,
      (hA ⟨z, hz⟩).2.2.1, (hA ⟨z, hz⟩).2.2.2.1⟩
  · have hall : ∀ᶠ n in atTop, ∀ z ∈ s.attach,
        aroundDist (G n) (A z) < ENNReal.ofReal δ :=
      (Filter.eventually_all_finset s.attach).2 fun z _ => (hA z).2.2.2.2
    filter_upwards [hall] with n hn z hz
    exact hn ⟨z, hz⟩ (Finset.mem_attach s ⟨z, hz⟩)

end SupercriticalLQGUniqueness.B2.PfeAxioms
