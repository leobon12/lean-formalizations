import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledLFPPSubseqLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.ScaledPointCostUpperTail
import SupercriticalLQGUniqueness.B2.PfeAxioms.UniformLiminfUpper
import SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.DFGPS LQGMetric.LFPP
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem scaled_internal_upper_tail_of_section4
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
      ∀ (r c : Ioi (0 : ℝ)),
        Tendsto (fun n => (r : ℝ) *
          (m ⟨(ε n : ℝ) / (r : ℝ),
            Set.mem_Ioi.mpr (div_pos (ε n).property r.property)⟩ : ℝ) /
          (m (ε n) : ℝ)) atTop (𝓝 (c : ℝ)) →
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
  intro r c hc
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

end SupercriticalLQGUniqueness.B2.PfeAxioms
