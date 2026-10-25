import SupercriticalLQGUniqueness.B2.PfeAxioms.CanonicalAcrossLowerTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAcrossLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.UniformLimsupLower

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_across_lower_tail_of_perc
    (hPerc : DG20PercEstimate')
    (ξ : Ioi (0 : ℝ))
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
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | acrossDist (B2.LscTop.smulMetric
          ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
            Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
          (B2.LscTop.dilate r (D (h ω)))) A < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
  obtain ⟨T, ε₀, hT, hε₀, htail⟩ :=
    finite_across_lower_tail_uniform_fieldScale hPerc ξ m hm P h hh A η hη
  refine ⟨2 * T, by positivity, ?_⟩
  intro r c hc
  let g : Ω → DistC := fun ω => fieldScale r (h ω)
  obtain ⟨Y, hY, hConv⟩ :=
    exists_scaled_across_limit_of_ratio ξ m ε D hD P h hh X hX hsmall A r c hc
  have hδ0 : Tendsto (fun n => (ε n : ℝ) / (r : ℝ)) atTop (𝓝 0) := by
    simpa using hε.div_const (r : ℝ)
  have hev : ∀ᶠ n in atTop, (ε n : ℝ) / (r : ℝ) < min ε₀ 1 :=
    hδ0.eventually (Iio_mem_nhds (lt_min hε₀ (by norm_num)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  let e : ℕ → Ioo (0 : ℝ) 1 := fun n =>
    ⟨(ε (n + N) : ℝ) / (r : ℝ),
      div_pos (ε (n + N)).property r.property,
      lt_of_lt_of_le (hN (n + N) (by omega)) (min_le_right _ _)⟩
  let δ (n : ℕ) : Ioi (0 : ℝ) := ⟨(e n : ℝ), (e n).property.1⟩
  let F (n : ℕ) (ω : Ω) : ℝ≥0∞ := acrossDist
    (PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (δ n)) (Y (δ n) ω)) A
  have hYtail : ∀ n, P {ω | F n ω < ENNReal.ofReal T⁻¹} ≤
      ENNReal.ofReal η := by
    intro n
    have hlt : (e n : ℝ) < ε₀ :=
      lt_of_lt_of_le (hN (n + N) (by omega)) (min_le_left _ _)
    simpa only [F, δ, e, g] using
      htail (e n) r r.property hlt (Y (δ n)) (hY (δ n))
  have hlimsup : ∀ᵐ ω ∂P, limsup (fun n => F n ω) atTop ≤
      acrossDist (B2.LscTop.smulMetric
        ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
          Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
        (B2.LscTop.dilate r (D (h ω)))) A := by
    filter_upwards [hConv] with ω hω
    have hmono : StrictMono (fun n : ℕ => n + N) :=
      strictMono_nat_of_lt_succ (fun n => by omega)
    have hs := (hω.comp hmono.tendsto_atTop).limsup_eq
    simpa [F, δ, e, Function.comp_def] using hs.le
  have hres := uniform_lower_tail_of_ae_limsup_le P
    (fun (_ : Unit) n ω => F n ω)
    (fun (_ : Unit) ω => acrossDist (B2.LscTop.smulMetric
      ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
      (B2.LscTop.dilate r (D (h ω)))) A)
    T⁻¹ η (inv_pos.mpr hT) (fun _ n => hYtail n) (fun _ => hlimsup) ()
  have heq : T⁻¹ / 2 = (2 * T)⁻¹ := by field_simp
  simpa only [heq] using hres

end SupercriticalLQGUniqueness.B2.PfeAxioms
