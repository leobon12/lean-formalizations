import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteLimitSkC

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_internal_eq_countable_localized_observable_of_smallAnnulusCosts_skC
    (hSkSB : B2.DG20Lim.DG20LimitSkC)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    {U : Set ℂ} (H : CompactExhaustion U) (x y : U)
    (W V : ℕ → Set ℂ)
    (hgeo : ∀ n,
      IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
      closure (W n) ⊆ U ∧
      (H n).image Subtype.val ⊆ W n ∧
      (x : ℂ) ∈ W n ∧ (y : ℂ) ∈ W n ∧
      IsOpen (V n) ∧ IsCompact (closure (V n)) ∧
      closure (V n) ⊆ U ∧ closure (W n) ⊆ V n ∧
      IsCompact (frontier (V n)) ∧
      (frontier (V n)).Nonempty ∧
      Disjoint (closure (W n)) (frontier (V n)))
    (hsmall : ∀ᵐ ω ∂P, ∀ n,
      PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω))
        (D (h ω)) (closure (W n)) (V n)) :
    ∀ᵐ ω ∂P,
      (D (h ω)).internal U (x, y) =
        ⨅ n : ℕ, lowerLocalizedNeighborhoodObservable ξ
          ε (fun k => m (ε k))
          ⟨(x : ℂ),
            (hgeo n).2.2.2.2.2.2.2.2.2.1
              (subset_closure (hgeo n).2.2.2.2.1)⟩
          ⟨(y : ℂ),
            (hgeo n).2.2.2.2.2.2.2.2.2.1
              (subset_closure (hgeo n).2.2.2.2.2.1)⟩
          (h ω) := by
  have hHeat := ae_internal_eq_countable_heat_observable_of_smallAnnulusCosts_skC
    hSkSB ξ Q hQ m hm ε hε D hD P h hh X hX H x y W V hgeo hsmall
  have hLoc : ∀ᵐ ω ∂P, ∀ n, ∀ x y : V n,
      lowerNeighborhoodObservable
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω)) (V n) x y =
      lowerLocalizedNeighborhoodObservable ξ
        ε (fun k => m (ε k)) x y (h ω) := by
    apply ae_all_iff.mpr
    intro n
    have hVb : Bornology.IsBounded (V n) :=
      (hgeo n).2.2.2.2.2.2.2.1.isBounded.subset subset_closure
    exact (ae_lowerNeighborhoodObservable_localized_eq_heat_of_normalized
      P h hh ξ (hgeo n).2.2.2.2.2.2.1 hVb
      ε hε (fun k => m (ε k)) X hX).mono fun ω hω x y => (hω x y).symm
  filter_upwards [hHeat, hLoc] with ω hHω hLω
  rw [hHω]
  apply iInf_congr
  intro n
  exact hLω n _ _

end SupercriticalLQGUniqueness.B2.PfeAxioms
