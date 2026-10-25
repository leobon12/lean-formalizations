import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledSectorUpperTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.AroundSectorTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.CircleAvg
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.Strong

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_around_upper_tail_of_section4
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
    (A : EuclideanAnnulus) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | (ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M) +
          ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M)) <
          aroundDist (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))) A} ≤ ENNReal.ofReal η +
            ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η := by
  intro η hη
  choose Mk hMk hTk using fun k : Fin 4 =>
    scaled_sector_upper_tail_of_section4 hS ξ Q hQ m hm ε hε D hD
      P h hh X hX A k η hη
  let Msum : ℝ := ∑ k : Fin 4, Mk k
  have hMsum : 0 < Msum := by
    dsimp [Msum]
    exact (hMk 0).trans_le (Finset.single_le_sum
      (fun k _ => (hMk k).le) (Finset.mem_univ 0))
  let M : ℝ := 2 * Msum
  have hM : 0 < M := mul_pos (by norm_num) hMsum
  have hMkM (k : Fin 4) : 2 * Mk k ≤ M := by
    dsimp [M]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.single_le_sum (fun j _ => (hMk j).le) (Finset.mem_univ k)
  let I := {p : Ioi (0 : ℝ) × Ioi (0 : ℝ) //
    Tendsto (fun n => (p.1 : ℝ) *
      (m ⟨(ε n : ℝ) / (p.1 : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε n).property p.1.property)⟩ : ℝ) /
      (m (ε n) : ℝ)) atTop (𝓝 (p.2 : ℝ))}
  let E (i : I) (ω : Ω) : LSCMetric := B2.LscTop.smulMetric
    ⟨(i.1.2 : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) i.1.1 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr i.1.2.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate i.1.1 (D (h ω)))
  have hsector : ∀ i : I, ∀ k : Fin 4,
      P {ω | ENNReal.ofReal M <
        (E i ω).internalSetDist (cfgOpens A k : Set ℂ)
          (Subtype.val ⁻¹' cfgSet₁ A k)
          (Subtype.val ⁻¹' cfgSet₂ A k)} ≤ ENNReal.ofReal η := by
    intro i k
    have hsub : {ω | ENNReal.ofReal M <
        (E i ω).internalSetDist (cfgOpens A k : Set ℂ)
          (Subtype.val ⁻¹' cfgSet₁ A k)
          (Subtype.val ⁻¹' cfgSet₂ A k)} ⊆
        {ω | ENNReal.ofReal (2 * Mk k) <
          (E i ω).internalSetDist (cfgOpens A k : Set ℂ)
            (Subtype.val ⁻¹' cfgSet₁ A k)
            (Subtype.val ⁻¹' cfgSet₂ A k)} := by
      intro ω hω
      exact (ENNReal.ofReal_le_ofReal (hMkM k)).trans_lt hω
    exact (measure_mono hsub).trans (hTk k i.1.1 i.1.2 i.property)
  obtain ⟨M', hM', htail⟩ := (show ∃ M' : ℝ, 0 < M' ∧
      ∀ i : I, P {ω | (ENNReal.ofReal (2 * M') + ENNReal.ofReal (2 * M') +
          ENNReal.ofReal (2 * M') + ENNReal.ofReal (2 * M')) <
        aroundDist (E i ω) A} ≤ ENNReal.ofReal η +
        ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η from
    ⟨M, hM, around_upper_tail_of_sector_upper_tail P E
      (fun _ => A) M hM (ENNReal.ofReal η) (fun i k => hsector i k)⟩)
  refine ⟨M', hM', ?_⟩
  intro r c hc
  exact htail ⟨(r, c), hc⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
