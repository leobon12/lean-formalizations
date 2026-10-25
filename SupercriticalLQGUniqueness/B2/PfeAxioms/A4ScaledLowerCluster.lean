import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAroundLowerTailSkC
import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometrySubsequence

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set LQGMetric LQGMetric.DFGPS
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem smallAnnulusCosts_comp_strictMono
    (G : ℕ → LSCMetric) (D : LSCMetric) (K' K'' : Set ℂ)
    (hG : PfeWeyl.SmallAnnulusCosts G D K' K'')
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    PfeWeyl.SmallAnnulusCosts (fun n => G (ψ n)) D K' K'' := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨A, h1, h2, h3, h4, h5⟩ := hG z hz hns δ hδ ρ hρ
  exact ⟨A, h1, h2, h3, h4, hψ.tendsto_atTop.eventually h5⟩

 


theorem scaled_across_lower_of_finite_tail
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
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
    (A : EuclideanAnnulus) (η T ε₀ : ℝ) (hT : 0 < T) (hε₀ : 0 < ε₀)
    (htail : ∀ (δ : Ioo (0 : ℝ) 1) (r : ℝ), 0 < r →
      (δ : ℝ) < ε₀ →
      ∀ (Y : Ω → C(ℂ, ℝ)),
        IsHeatSmoothing P (fun ω => fieldScale r (h ω))
          ⟨(δ : ℝ), δ.property.1⟩ Y →
      P {ω | acrossDist
        (PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m ⟨(δ : ℝ), δ.property.1⟩) (Y ω)) A <
          ENNReal.ofReal T⁻¹} ≤ ENNReal.ofReal η)
    (r c : Ioi (0 : ℝ))
    (hc : Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ))) :
    P {ω | acrossDist (B2.LscTop.smulMetric
      ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
      (B2.LscTop.dilate r (D (h ω)))) A < ENNReal.ofReal (2 * T)⁻¹} ≤
      ENNReal.ofReal η := by
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
    simpa only [F, δ, e] using
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

 

theorem scaled_across_lower_tail_cluster_of_perc
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
      ∀ (r c : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | acrossDist (B2.LscTop.smulMetric
          ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
            Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
          (B2.LscTop.dilate r (D (h ω)))) A < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
  obtain ⟨T, ε₀, hT, hε₀, htail⟩ :=
    finite_across_lower_tail_uniform_fieldScale hPerc ξ m hm P h hh A η hη
  refine ⟨2 * T, by positivity, ?_⟩
  intro r c ψ hψ hc
  have hsmallψ : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε (ψ n)))
          (X (ε (ψ n)) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)) := by
    intro k
    filter_upwards [hsmall k] with ω hω
    exact smallAnnulusCosts_comp_strictMono _ _ _ _ hω ψ hψ
  exact scaled_across_lower_of_finite_tail ξ m (fun n => ε (ψ n))
    (hε.comp hψ.tendsto_atTop) D (subseqLimit_comp_strictMono ξ m ε D hD ψ hψ)
    P h hh X hX hsmallψ A η T ε₀ hT hε₀ htail r c hc

 

theorem scaled_around_lower_tail_cluster_of_perc_skC
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hSkC : B2.DG20Lim.DG20LimitSkC)
    (hPerc : DG20PercEstimate')
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
    (hsmall : ∀ k : ℕ, ∀ᵐ ω ∂P,
      PfeWeyl.SmallAnnulusCosts
        (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (ε n)) (X (ε n) ω))
        (D (h ω)) (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1)))
    (A : EuclideanAnnulus) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | aroundDist (B2.LscTop.smulMetric
          ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
            Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
          (B2.LscTop.dilate r (D (h ω)))) A < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
  let I := {p : Ioi (0 : ℝ) × Ioi (0 : ℝ) × (ℕ → ℕ) //
    StrictMono p.2.2 ∧
    Tendsto (fun n => (p.1 : ℝ) *
      (m ⟨(ε (p.2.2 n) : ℝ) / (p.1 : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε (p.2.2 n)).property p.1.property)⟩ : ℝ) /
      (m (ε (p.2.2 n)) : ℝ)) atTop (𝓝 (p.2.1 : ℝ))}
  let E (i : I) (ω : Ω) : LSCMetric := B2.LscTop.smulMetric
    ⟨(i.1.2.1 : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) i.1.1 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr i.1.2.1.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate i.1.1 (D (h ω)))
  have hGeom := B2.DG20Lim.limitEuclideanControl0_of_dg20LimitSkC hSkC
    ξ Q hQ m ε D hm hε hD P h hh
  have hcont : ∀ i : I, ∀ᵐ ω ∂P,
      Continuous (B2.PfeWeyl.euclidForget (E i ω)) := by
    intro i
    filter_upwards [hGeom] with ω hω
    exact continuous_euclidForget_smul_dilate_of_control (D (h ω)) hω
      ⟨(i.1.2.1 : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) i.1.1 0),
        Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr i.1.2.1.property) (Real.exp_pos _))⟩
      i.1.1
  have hcross : ∀ B : EuclideanAnnulus, ∀ η : ℝ, 0 < η →
      ∃ M : ℝ, 0 < M ∧ ∀ i : I,
        P {ω | acrossDist (E i ω) B < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η := by
    intro B η hη
    obtain ⟨M, hM, htail⟩ := scaled_across_lower_tail_cluster_of_perc
      hPerc ξ m hm ε hε D hD P h hh X hX hsmall B η hη
    exact ⟨M, hM, fun i => htail i.1.1 i.1.2.1 i.1.2.2 i.property.1 i.property.2⟩
  have hTail := around_lower_tail_of_across_lower_tail P E A hcont hcross
  intro η hη
  obtain ⟨M, hM, hBound⟩ := hTail η hη
  exact ⟨M, hM, fun r c ψ hψ hc => hBound ⟨(r, c, ψ), hψ, hc⟩⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
