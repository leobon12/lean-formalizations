import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4InternalFinite
import SupercriticalLQGUniqueness.B2.Strong.AroundFinite

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.DDDF
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.Strong

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem ae_aroundDist_lt_top_of_section4
    (hS : DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioo (0 : ℝ) 1)
    (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m
      (fun n => ⟨(ε n : ℝ), (ε n).property.1⟩) D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (A : EuclideanAnnulus) :
    ∀ᵐ ω ∂P, aroundDist (D (h ω)) A < ∞ := by
  have hk : ∀ k : Fin 4, ∀ᵐ ω ∂P,
      (D (h ω)).internalSetDist (cfgOpens A k : Set ℂ)
        (Subtype.val ⁻¹' cfgSet₁ A k) (Subtype.val ⁻¹' cfgSet₂ A k) < ∞ := by
    intro k
    obtain ⟨-, hUc, -, -, -, -, hn₁, hn₂, hs₁, hs₂, hd⟩ :=
      axiomV_data A.center (annL A) (annΔ A) (annΔ_pos A) k
    obtain ⟨x, hx⟩ := hn₁.nonempty
    obtain ⟨y, hy⟩ := hn₂.nonempty
    let xv : cfgOpens A k := ⟨x, hs₁ hx⟩
    let yv : cfgOpens A k := ⟨y, hs₂ hy⟩
    have hxy : x ≠ y := by
      intro he
      exact Set.disjoint_left.mp hd hx (he ▸ hy)
    have hfin := ae_internal_lt_top_of_section4 hS ξ Q hQ m hm ε D hD
      P h hh X hX (cfgOpens A k) hUc xv yv hxy
    filter_upwards [hfin] with ω hω
    exact lt_of_le_of_lt
      (iInf₂_le_of_le xv hx (iInf₂_le yv hy)) hω
  filter_upwards [ae_all_iff.2 hk] with ω hω
  exact aroundDist_lt_top_of_internalSetDist _ A hω

end SupercriticalLQGUniqueness.B2.PfeAxioms
