import HigherDimLQGMetric.Locality.NormalizedMetric
import HigherDimLQGMetric.Locality.MarkedRepTrunc

/-! Both truncated ambient metrics converge on a common further subsequence
of the second coupling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_second_two_trunc_subseq
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (hL2c : L2c_trunc)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : IsNormalizedLGF h P) (hDh : Measurable Dh)
    (Ψ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ)) (hΨ : Measurable Ψ)
    (K : Set (Rd d)) (hK : IsCompact K)
    (hΨsupp : ∀ x z, z ∉ K → (Ψ x).2 z = 0)
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    (ns : ℕ → ℕ) (hns : StrictMono ns)
    {E : Type} [MeasurableSpace E] (Q : Measure E)
    (Z : ℕ → E → L7aJointState S T W W')
    (Zlim : E → L7aJointState S T W W')
    (hZm : ∀ n, Measurable (Z n)) (hZlimm : Measurable Zlim)
    (hstage : ∀ n, Q.map (fun e => (Z n e).1) = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))),
        lfppSeq κ ξ εs (h ω) (ns n))))
    (hbase : Q.map (fun e => (Zlim e).1) = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))), (Dh ω).1)))
    (hZc : ∀ e, Tendsto (fun n => Z n e) atTop (𝓝 (Zlim e)))
    (hgood : ∀ᵐ e ∂Q, IsContLengthFn (Zlim e).1.2 ∧
      IsProperFn (Zlim e).1.2) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns (τ k))))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns (τ k)))
                (l7a_markedField₁ (Z (τ k) e).1)) p)
          (fun p => (weylScale ξ
            (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1))
            (l7a_metricLift (Zlim e).1.2) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) ∧
      (∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun k (p : Rd d × Rd d) =>
            (aEps κ ξ (εs (ns (τ k))))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs (ns (τ k)))
                (l7a_markedField₂ (Z (τ k) e).1)) p)
          (fun p => (weylScale ξ
            (ContinuousMap.const (Rd d) (-(Zlim e).1.1.2.1) -
              (Zlim e).1.1.2.2)
            (l7a_metricLift (Zlim e).1.2) p.1 p.2).toReal) atTop
          (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R)) := by
  let ε' : ℕ → ℝ := fun n => εs (ns n)
  have hε' (n : ℕ) : 0 < ε' n := hεs (ns n)
  have hε'0 : Tendsto ε' atTop (𝓝 0) :=
    hεt.comp hns.tendsto_atTop
  let Zb : ℕ → E → L7aMarkedBase d := fun n e => (Z n e).1
  let Zblim : E → L7aMarkedBase d := fun e => (Zlim e).1
  have hZbm (n : ℕ) : Measurable (Zb n) :=
    measurable_fst.comp (hZm n)
  have hZblimm : Measurable Zblim := measurable_fst.comp hZlimm
  have hZbc (e : E) : Tendsto (fun n => Zb n e) atTop
      (𝓝 (Zblim e)) :=
    (continuous_fst.tendsto (Zlim e)).comp (hZc e)
  obtain ⟨τ, hτ, h₁, h₂⟩ :=
    l7a_ae_marked_rep_two_trunc_subseq hd κ hκ ξ hL2c
      ε' hε' hε'0 P h Dh hh hDh Ψ hΨ K hK hΨsupp
      Q Zb Zblim hZbm hZblimm hstage hbase hZbc hgood
  exact ⟨τ, hτ, h₁, h₂⟩

end HigherDimLQGMetric
