import HigherDimLQGMetric.Locality.GraphLaw
import HigherDimLQGMetric.Limits.AeMapImage
import LQGMetric.Prob.PolishContinuousMap

/-! A finite-scale LFPP graph identity on any law-preserving representation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_ae_graph_of_joint_law {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) (n : ℕ)
    {E : Type*} [MeasurableSpace E] (Q : Measure E)
    (Z : E → (CoordJ → ℝ) × C(Rd d × Rd d, ℝ)) (hZ : Measurable Z)
    (hlaw : Q.map Z = P.map
      (fun ω => (pairJ ⊤ (h ω), lfppSeq κ ξ εs (h ω) n))) :
    ∀ᵐ e ∂Q, (Z e).2 =
      lfppSeq κ ξ εs (pairJInv ⊤ (Z e).1) n := by
  letI : PolishSpace C(Rd d × Rd d, ℝ) :=
    LQGMetric.polishSpace_continuousMap _ _
  obtain ⟨F, hFm, hFe, hlawgraph⟩ :=
    l7a_lfpp_joint_law_graph hd κ hκ ξ εs hεs P h hh n
  let μ : Measure (DistRd d) := P.map h
  let t : DistRd d → (CoordJ → ℝ) × C(Rd d × Rd d, ℝ) :=
    fun g => (pairJ ⊤ g, F g)
  have ht : Measurable t := (measurable_pairJ ⊤).prodMk hFm
  let p : ((CoordJ → ℝ) × C(Rd d × Rd d, ℝ)) → Prop :=
    fun q => q.2 = lfppSeq κ ξ εs (pairJInv ⊤ q.1) n
  have hp : ∀ᵐ g ∂μ, p (t g) := by
    filter_upwards [hFe] with g he
    change F g = lfppSeq κ ξ εs (pairJInv ⊤ (pairJ ⊤ g)) n
    rw [pairJInv_pairJ]
    exact he
  have hmap : ∀ᵐ q ∂μ.map t, p q :=
    l6c_ae_map_of_ae_sb μ t ht p hp
  have hZmap : ∀ᵐ q ∂Q.map Z, p q := by
    rw [hlaw, hlawgraph]
    exact hmap
  exact ae_of_ae_map hZ.aemeasurable hZmap

end HigherDimLQGMetric
