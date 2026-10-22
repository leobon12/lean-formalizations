import HigherDimLQGMetric.Locality.MarkedTwoTrunc
import HigherDimLQGMetric.Locality.MetricLift
import HigherDimLQGMetric.Locality.SkorokhodMarksGraph

/-! Truncated metrics on a marked Skorokhod representation of the stable
field and ambient LFPP limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_ae_marked_rep_two_trunc_subseq
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hL2c : L2c_trunc) (εs : ℕ → ℝ)
    (hεs : ∀ n, 0 < εs n) (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (Φ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ)) (hΦ : Measurable Φ)
    (K : Set (Rd d)) (hK : IsCompact K)
    (hΦsupp : ∀ x z, z ∉ K → (Φ x).2 z = 0)
    {E : Type} [MeasurableSpace E] (Q : Measure E)
    (Z : ℕ → E → ((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) ×
      C(Rd d × Rd d, ℝ))
    (Zlim : E → ((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) ×
      C(Rd d × Rd d, ℝ))
    (hZm : ∀ n, Measurable (Z n)) (hZlimm : Measurable Zlim)
    (hZlaw : ∀ n, Q.map (Z n) = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))), lfppSeq κ ξ εs (h ω) n)))
    (hZlimlaw : Q.map Zlim = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Φ (pairJ ⊤ (h ω))), (Dh ω).1)))
    (hZc : ∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e)))
    (hZgood : ∀ᵐ e ∂Q, IsContLengthFn (Zlim e).2 ∧
      IsProperFn (Zlim e).2) :
    let Xn : ℕ → E → DistRd d := fun n e => pairJInv ⊤ (Z n e).1.1
    let D : E → ContMetric d := fun e => l7a_metricLift (Zlim e).2
    let cn : ℕ → E → ℝ := fun n e => (Z n e).1.2.1
    let c : E → ℝ := fun e => (Zlim e).1.2.1
    let Fn : ℕ → E → C(Rd d, ℝ) := fun n e => (Z n e).1.2.2
    let F : E → C(Rd d, ℝ) := fun e => (Zlim e).1.2.2
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns k))
                (addConst (Xn (ns k) e) (-cn (ns k) e))) p)
          (fun p => (weylScale ξ (ContinuousMap.const (Rd d) (-c e))
            (D e) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns k)))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns k))
                (addConst (Xn (ns k) e) (-cn (ns k) e) -
                  ofCont (Fn (ns k) e))) p)
          (fun p => (weylScale ξ
            (ContinuousMap.const (Rd d) (-c e) - F e)
            (D e) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) := by
  dsimp only
  let μ : Measure (DistRd d) := P.map h
  letI : IsProbabilityMeasure μ := inferInstance
  have hhμ : IsNormalizedLGF (id : DistRd d → DistRd d) μ := hh.map_id
  let Xn : ℕ → E → DistRd d := fun n e => pairJInv ⊤ (Z n e).1.1
  let Xlim : E → DistRd d := fun e => pairJInv ⊤ (Zlim e).1.1
  let D : E → ContMetric d := fun e => l7a_metricLift (Zlim e).2
  let cn : ℕ → E → ℝ := fun n e => (Z n e).1.2.1
  let c : E → ℝ := fun e => (Zlim e).1.2.1
  let Fn : ℕ → E → C(Rd d, ℝ) := fun n e => (Z n e).1.2.2
  let F : E → C(Rd d, ℝ) := fun e => (Zlim e).1.2.2
  have hXn (n : ℕ) : Measurable (Xn n) :=
    (measurable_pairJInv ⊤).comp
      ((measurable_fst.comp measurable_fst).comp (hZm n))
  have hfield := l7a_marked_stage_graph hd κ hκ ξ εs hεs
    P h hh Φ hΦ Q Z hZm hZlaw
  have hlaw (n : ℕ) : Q.map (Xn n) = μ := hfield.1 n
  have hlimfield := l7a_marked_limit_graph P h hh.1.measurable
    Dh hDh Φ hΦ Q Zlim hZlimm hZlimlaw
  have hlimlaw : Q.map Xlim = μ := hlimfield.1
  have hgood : ∀ᵐ e ∂Q, (D e).IsLength ∧ IsProperFn (D e).1 := by
    filter_upwards [hZgood] with e he
    exact ⟨l7a_metricLift_isLength he.1,
      (l7a_metricLift_val he.1.1) ▸ he.2⟩
  have hgraph : ∀ᵐ e ∂Q, ∀ n, (Z n e).2 =
      lfppSeq κ ξ εs (Xn n e) n :=
    ae_all_iff.mpr hfield.2.2
  have hfull : ∀ᵐ e ∂Q, Tendsto
      (fun n => lfppSeq κ ξ εs (Xn n e) n) atTop (𝓝 (D e).1) := by
    filter_upwards [hgraph, hZgood] with e he hg
    have ht := (continuous_snd.tendsto (Zlim e)).comp (hZc e)
    have hDe : (D e).1 = (Zlim e).2 := l7a_metricLift_val hg.1.1
    rw [hDe]
    have hEq : (fun n => lfppSeq κ ξ εs (Xn n e) n) =
        (fun n => (Z n e).2) := funext fun n => (he n).symm
    rw [hEq]
    simpa only [Function.comp_def] using ht
  have hcn : ∀ᵐ e ∂Q, Tendsto (fun n => cn n e) atTop (𝓝 (c e)) := by
    apply Filter.Eventually.of_forall
    intro e
    have hc : Continuous (fun q : ((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) ×
        C(Rd d × Rd d, ℝ) => q.1.2.1) := by fun_prop
    exact hc.continuousAt.tendsto.comp (hZc e)
  have hFn : ∀ᵐ e ∂Q, Tendsto (fun n => Fn n e) atTop (𝓝 (F e)) := by
    apply Filter.Eventually.of_forall
    intro e
    have hc : Continuous (fun q : ((CoordJ → ℝ) × (ℝ × C(Rd d, ℝ))) ×
        C(Rd d × Rd d, ℝ) => q.1.2.2) := by fun_prop
    exact hc.continuousAt.tendsto.comp (hZc e)
  have hsupp : ∀ᵐ e ∂Q, ∀ n z, z ∉ K → Fn n e z = 0 := by
    filter_upwards [ae_all_iff.mpr hfield.2.1] with e he n z hz
    rw [show Fn n e = (Φ (Z n e).1.1).2 from congrArg Prod.snd (he n)]
    exact hΦsupp _ z hz
  exact l7a_ae_marked_two_trunc_subseq hd κ hκ ξ hL2c εs hεs hεt
    μ hhμ Q Xlim Xn hXn hlaw hlimlaw D hgood hfull
    cn c Fn F hcn hFn K hK hsupp

end HigherDimLQGMetric
