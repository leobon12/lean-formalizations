import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAcrossUpperFixed
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledAroundUpperTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometrySubsequence

 














set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS LQGMetric.LFPP LQGMetric.CircleAvg
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.Strong

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem scaled_internal_upper_of_point_tail
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (V : TopologicalSpace.Opens ℂ)
    {K U : Set ℂ} (hVK : (V : Set ℂ) ⊆ K)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) (M η : ℝ) (hM : 0 < M)
    (hTail : ∀ (δ : Ioo (0 : ℝ) 1) (r : ℝ), 0 < r →
        P {ω | ENNReal.ofReal M <
          ENNReal.ofReal ((m ⟨(δ : ℝ), δ.property.1⟩ : ℝ)⁻¹) *
            crossLenIn (ξ : ℝ)
              (heatMollify (δ : ℝ) (fieldScale r (h ω))) V
                {(x : ℂ)} {(y : ℂ)}} ≤ ENNReal.ofReal η)
    (r c : Ioi (0 : ℝ))
    (hc : Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ))) :
    P {ω | ENNReal.ofReal (2 * M) <
      (B2.LscTop.smulMetric
        ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
          Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
        (B2.LscTop.dilate r (D (h ω)))).internal U
          (⟨(x : ℂ), hKU (hVK x.property)⟩,
            ⟨(y : ℂ), hKU (hVK y.property)⟩)} ≤ ENNReal.ofReal η := by
  let g : Ω → DistC := fun ω => fieldScale r (h ω)
  have hg : IsNormalizedWholePlaneGFF g P :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_new_of_old
      (isNormalizedWPGFF_fieldScale hh.1 r.property)
  obtain ⟨Y, hY, hConv⟩ :=
    exists_scaled_lfpp_subseq_limit_of_ratio ξ m ε D hD P h hh X hX r c hc
  have hδ0 : Tendsto (fun n => (ε n : ℝ) / (r : ℝ)) atTop (𝓝 0) := by
    simpa using hε.div_const (r : ℝ)
  have hsmall : ∀ᶠ n in atTop, (ε n : ℝ) / (r : ℝ) < 1 :=
    hδ0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
  let e : ℕ → Ioo (0 : ℝ) 1 := fun n =>
    ⟨(ε (n + N) : ℝ) / (r : ℝ),
      ⟨div_pos (ε (n + N)).property r.property, hN (n + N) (by omega)⟩⟩
  let δ (n : ℕ) : Ioi (0 : ℝ) :=
    ⟨(e n : ℝ), (e n).property.1⟩
  let L (ω : Ω) : LSCMetric := B2.LscTop.smulMetric
    ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate r (D (h ω)))
  let Z (ω : Ω) : ℝ≥0∞ :=
    (L ω).internal U
      (⟨(x : ℂ), hKU (hVK x.property)⟩,
        ⟨(y : ℂ), hKU (hVK y.property)⟩)
  let F (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ENNReal.ofReal ((m (δ n) : ℝ)⁻¹) *
      crossLenIn (ξ : ℝ) (Y (δ n) ω) V {(x : ℂ)} {(y : ℂ)}
  have hTailY : ∀ n, P {ω | ENNReal.ofReal M < F n ω} ≤ ENNReal.ofReal η := by
    intro n
    have hYeq := B2.DG20Pt.dg20_heat_smoothing_ae_heatMollify
      P g hg (δ n) (Y (δ n)) (hY (δ n))
    have hsub : ∀ᵐ ω ∂P,
        ENNReal.ofReal M < F n ω →
        ENNReal.ofReal M <
          ENNReal.ofReal ((m (δ n) : ℝ)⁻¹) *
            crossLenIn (ξ : ℝ)
              (heatMollify (δ n : ℝ) (fieldScale r (h ω)))
              V {(x : ℂ)} {(y : ℂ)} := by
      filter_upwards [hYeq] with ω hEq
      intro hlt
      have hcost : crossLenIn (ξ : ℝ) (Y (δ n) ω)
          V {(x : ℂ)} {(y : ℂ)} =
          crossLenIn (ξ : ℝ) (heatMollify (δ n : ℝ) (g ω))
            V {(x : ℂ)} {(y : ℂ)} := by
        congr 1
        funext z
        exact hEq z
      simpa only [F, g, hcost] using hlt
    exact (measure_mono_ae hsub).trans (hTail (e n) (r : ℝ) r.property)
  have hC : ∀ᵐ ω ∂P,
      Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m (δ n)) (Y (δ n) ω)) atTop (𝓝 (L ω)) := by
    filter_upwards [hConv] with ω hω
    change Tendsto (fun n => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
      (m ⟨(ε (n + N) : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε (n + N)).property r.property)⟩)
      (Y ⟨(ε (n + N) : ℝ) / (r : ℝ),
        Set.mem_Ioi.mpr (div_pos (ε (n + N)).property r.property)⟩ ω))
      atTop (𝓝 (L ω))
    exact hω.comp (tendsto_add_atTop_nat N)
  have hZ : ∀ᵐ ω ∂P, Z ω ≤ liminf (fun n => F n ω) atTop := by
    filter_upwards [hC] with ω hω
    have hB := buffered_internal_le_liminf_lfppDOn (ξ : ℝ)
      (fun n => m (δ n)) (fun n => Y (δ n) ω)
      (L ω) hω hVK hK hKU x y
    have hEq : (fun n => ENNReal.ofReal ((m (δ n) : ℝ)⁻¹) *
        lfppDOn (ξ : ℝ) (Y (δ n) ω) V x y) = fun n => F n ω := by
      funext n
      simp only [F, LQGMetric.DFGPS.crossLenIn_singleton]
    rwa [hEq] at hB
  exact uniform_upper_tail_of_ae_le_liminf P
    (fun (_ : Unit) n ω => F n ω) (fun (_ : Unit) ω => Z ω)
    M η hM (fun _ n => hTailY n) (fun _ => hZ) ()

 



theorem scaled_internal_upper_tail_cluster_of_section4
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
    (V : TopologicalSpace.Opens ℂ) (hVc : IsConnected (V : Set ℂ))
    {K U : Set ℂ} (hVK : (V : Set ℂ) ⊆ K)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (x y : V) (hxy : (x : ℂ) ≠ (y : ℂ)) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | ENNReal.ofReal (2 * M) <
          (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))).internal U
              (⟨(x : ℂ), hKU (hVK x.property)⟩,
                ⟨(y : ℂ), hKU (hVK y.property)⟩)} ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨M, hM, hTail⟩ := scaled_point_cost_upper_tail
    hS ξ Q hQ m hm V hVc (x : ℂ) (y : ℂ)
    x.property y.property hxy P h hh η hη
  refine ⟨M, hM, ?_⟩
  intro r c ψ hψ hc
  exact scaled_internal_upper_of_point_tail ξ m (fun n => ε (ψ n))
    (hε.comp hψ.tendsto_atTop) D (subseqLimit_comp_strictMono ξ m ε D hD ψ hψ)
    P h hh X hX V hVK hK hKU x y M η hM hTail r c hc

 

theorem scaled_across_upper_tail_cluster_of_section4_buffered
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
    (A : EuclideanAnnulus)
    (V : TopologicalSpace.Opens ℂ) (hVc : IsConnected (V : Set ℂ))
    (hVcompact : IsCompact (closure (V : Set ℂ)))
    (x y : V) (hx : (x : ℂ) ∈ A.innerBoundary)
    (hy : (y : ℂ) ∈ A.outerBoundary) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧
      ∀ (r c : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | ENNReal.ofReal (2 * M) <
          acrossDist (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))) A} ≤ ENNReal.ofReal η := by
  have hxy : (x : ℂ) ≠ (y : ℂ) := by
    intro he
    exact Set.disjoint_left.mp (B2.Strong.disjoint_boundaries A) hx (he ▸ hy)
  have hT := scaled_internal_upper_tail_cluster_of_section4
    hS ξ Q hQ m hm ε hε D hD P h hh X hX V hVc
    subset_closure hVcompact (subset_univ _) x y hxy
  intro η hη
  obtain ⟨M, hM, hTail⟩ := hT η hη
  refine ⟨M, hM, ?_⟩
  intro r c ψ hψ hc
  let L (ω : Ω) : LSCMetric := B2.LscTop.smulMetric
    ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
      Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
    (B2.LscTop.dilate r (D (h ω)))
  calc
    P {ω | ENNReal.ofReal (2 * M) < acrossDist (L ω) A}
      ≤ P {ω | ENNReal.ofReal (2 * M) <
          (L ω).internal Set.univ
            (⟨(x : ℂ), Set.mem_univ _⟩,
              ⟨(y : ℂ), Set.mem_univ _⟩)} := by
        apply measure_mono
        intro ω hω
        have hle : acrossDist (L ω) A ≤
            (L ω).internal Set.univ
              (⟨(x : ℂ), Set.mem_univ _⟩,
                ⟨(y : ℂ), Set.mem_univ _⟩) := by
          calc
            acrossDist (L ω) A ≤ L ω ((x : ℂ), (y : ℂ)) :=
              iInf₂_le_of_le _ hx (iInf₂_le _ hy)
            _ ≤ (L ω).internal Set.univ
                (⟨(x : ℂ), Set.mem_univ _⟩,
                  ⟨(y : ℂ), Set.mem_univ _⟩) :=
              B2.PfeLocal.edist_le_internal (L ω) Set.univ
                (⟨(x : ℂ), Set.mem_univ _⟩,
                  ⟨(y : ℂ), Set.mem_univ _⟩)
        exact hω.trans_le hle
    _ ≤ ENNReal.ofReal η := hTail r c ψ hψ hc

 

theorem scaled_across_upper_tail_cluster_of_section4
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
      ∀ (r c : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | ENNReal.ofReal (2 * M) <
          acrossDist (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))) A} ≤ ENNReal.ofReal η := by
  let R : ℝ := A.outerRadius + 1
  let V : TopologicalSpace.Opens ℂ :=
    ⟨Metric.ball A.center R, Metric.isOpen_ball⟩
  have hR : 0 < R := by
    dsimp [R]
    linarith [A.innerRadius_pos, A.innerRadius_lt_outerRadius]
  have hVcompact : IsCompact (closure (V : Set ℂ)) :=
    (isCompact_closedBall A.center R).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall
  let x : V := ⟨A.center + (A.innerRadius : ℂ), by
    change dist (A.center + (A.innerRadius : ℂ)) A.center < R
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos A.innerRadius_pos]
    dsimp [R]
    linarith [A.innerRadius_lt_outerRadius]⟩
  let y : V := ⟨A.center + (A.outerRadius : ℂ), by
    change dist (A.center + (A.outerRadius : ℂ)) A.center < R
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius)]
    dsimp [R]
    linarith⟩
  have hx : (x : ℂ) ∈ A.innerBoundary := by
    change dist (A.center + (A.innerRadius : ℂ)) A.center = A.innerRadius
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos A.innerRadius_pos]
  have hy : (y : ℂ) ∈ A.outerBoundary := by
    change dist (A.center + (A.outerRadius : ℂ)) A.center = A.outerRadius
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius)]
  exact scaled_across_upper_tail_cluster_of_section4_buffered
    hS ξ Q hQ m hm ε hε D hD P h hh X hX A V
    (Metric.isConnected_ball hR) hVcompact x y hx hy

 

theorem scaled_sector_upper_tail_cluster_of_section4
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
      ∀ (r c : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c : ℝ)) →
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
  have hT := scaled_internal_upper_tail_cluster_of_section4
    hS ξ Q hQ m hm ε hε D hD P h hh X hX
    V hVc (subset_closure : (V : Set ℂ) ⊆ closure (V : Set ℂ))
    hK hKU xV yV hxy
  intro η hη
  obtain ⟨M, hM, hTail⟩ := hT η hη
  refine ⟨M, hM, ?_⟩
  intro r c ψ hψ hc
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
  exact (measure_mono hsub).trans (hTail r c ψ hψ hc)

 

theorem scaled_around_upper_tail_cluster_of_section4
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
      ∀ (r c : Ioi (0 : ℝ)) (ψ : ℕ → ℕ), StrictMono ψ →
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε (ψ n) : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε (ψ n)).property r.property)⟩ : ℝ) /
          (m (ε (ψ n)) : ℝ)) atTop (𝓝 (c : ℝ)) →
        P {ω | (ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M) +
          ENNReal.ofReal (2 * M) + ENNReal.ofReal (2 * M)) <
          aroundDist (B2.LscTop.smulMetric
            ⟨(c : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0),
              Set.mem_Ioi.mpr (mul_pos (inv_pos.mpr c.property) (Real.exp_pos _))⟩
            (B2.LscTop.dilate r (D (h ω)))) A} ≤ ENNReal.ofReal η +
            ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η := by
  intro η hη
  choose Mk hMk hTk using fun k : Fin 4 =>
    scaled_sector_upper_tail_cluster_of_section4 hS ξ Q hQ m hm ε hε D hD
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
    exact (measure_mono hsub).trans
      (hTk k i.1.1 i.1.2.1 i.1.2.2 i.property.1 i.property.2)
  obtain ⟨M', hM', htail⟩ := (show ∃ M' : ℝ, 0 < M' ∧
      ∀ i : I, P {ω | (ENNReal.ofReal (2 * M') + ENNReal.ofReal (2 * M') +
          ENNReal.ofReal (2 * M') + ENNReal.ofReal (2 * M')) <
        aroundDist (E i ω) A} ≤ ENNReal.ofReal η +
        ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η from
    ⟨M, hM, around_upper_tail_of_sector_upper_tail P E
      (fun _ => A) M hM (ENNReal.ofReal η) (fun i k => hsector i k)⟩)
  refine ⟨M', hM', ?_⟩
  intro r c ψ hψ hc
  exact htail ⟨(r, c, ψ), hψ, hc⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
