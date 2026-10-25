import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledInternalUpperTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.ConnectedCompactBuffer
import SupercriticalLQGUniqueness.B2.Strong.AroundFinite

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.CircleAvg
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.Strong

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_sector_upper_tail_of_section4
    (hS : DG20Section4)
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
    (A : EuclideanAnnulus) (k : Fin 4) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | ENNReal.ofReal (2 * M) <
          (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))).internalSetDist
              (cfgOpens A k : Set ℂ)
              (Subtype.val ⁻¹' cfgSet₁ A k)
              (Subtype.val ⁻¹' cfgSet₂ A k)} ≤ ENNReal.ofReal η := by
  obtain ⟨-, hUc, -, -, -, -, hn₁, hn₂, hs₁, hs₂, hd⟩ :=
    axiomV_data A.center (annL A) (annΔ A) (annΔ_pos A) k
  obtain ⟨x, hx⟩ := hn₁.nonempty
  obtain ⟨y, hy⟩ := hn₂.nonempty
  let xv : cfgOpens A k := ⟨x, hs₁ hx⟩
  let yv : cfgOpens A k := ⟨y, hs₂ hy⟩
  have hxy : (xv : ℂ) ≠ (yv : ℂ) := by
    intro he
    change x = y at he
    exact Set.disjoint_left.mp hd hx (he ▸ hy)
  obtain ⟨V, hVc, hK, hKU, hxV, hyV⟩ :=
    exists_connected_compact_buffer (cfgOpens A k) hUc xv yv
  let xV : V := ⟨x, hxV⟩
  let yV : V := ⟨y, hyV⟩
  have hT := scaled_internal_upper_tail_of_section4
    hS ξ Q hQ m hm ε hε D hD P h hh X hX
    V hVc (subset_closure : (V : Set ℂ) ⊆ closure (V : Set ℂ))
    hK hKU xV yV hxy
  intro η hη
  obtain ⟨M, hM, hTail⟩ := hT η hη
  refine ⟨M, hM, ?_⟩
  intro r c hc
  have hsub : {ω | ENNReal.ofReal (2 * M) <
      (B2.LscTop.smulMetric
        ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
          Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
        (B2.LscTop.dilate r (D (h ω)))).internalSetDist
          (cfgOpens A k : Set ℂ)
          (Subtype.val ⁻¹' cfgSet₁ A k)
          (Subtype.val ⁻¹' cfgSet₂ A k)} ⊆
      {ω | ENNReal.ofReal (2 * M) <
        (B2.LscTop.smulMetric
          ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
            Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
          (B2.LscTop.dilate r (D (h ω)))).internal
            (cfgOpens A k : Set ℂ)
            (⟨x, hKU (subset_closure hxV)⟩,
              ⟨y, hKU (subset_closure hyV)⟩)} := by
    intro ω hω
    change ENNReal.ofReal (2 * M) < _ at hω
    change ENNReal.ofReal (2 * M) < _
    apply hω.trans_le
    unfold LSCMetric.internalSetDist
    exact iInf_le_of_le xv (iInf_le_of_le hx (iInf₂_le yv hy))
  exact (measure_mono hsub).trans (hTail r c hc)

end SupercriticalLQGUniqueness.B2.PfeAxioms
