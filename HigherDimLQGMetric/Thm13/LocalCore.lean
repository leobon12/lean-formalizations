import HigherDimLQGMetric.Thm13.LocalUpper

/-! A countable field-local formula for a limiting internal metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

def l8_localFormula {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (U : TopologicalSpace.Opens (Rd d)) (g : DistRd d)
    (u v : Rd d) : ℝ≥0∞ :=
  ⨅ i : l7a_CompIndex U,
    l8_localInternal hd hκ ξ εs hεs (l7a_compDomain U i) g u v

theorem l8_measurable_localFormula {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (U : TopologicalSpace.Opens (Rd d)) (u v : Rd d) :
    Measurable (fun g : DistRd d =>
      l8_localFormula hd hκ ξ εs hεs U g u v) :=
  Measurable.iInf fun i =>
    l8_measurable_localInternal hd hκ ξ εs hεs
      (l7a_compDomain U i) u v

theorem l8_localFormula_congr_of_restrictTo
    {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (U : TopologicalSpace.Opens (Rd d))
    {g g' : DistRd d} (heq : restrictTo U g = restrictTo U g') :
    l8_localFormula hd hκ ξ εs hεs U g =
      l8_localFormula hd hκ ξ εs hεs U g' := by
  funext u v
  unfold l8_localFormula
  apply iInf_congr
  intro i
  exact l8_localInternal_congr_of_restrictTo hd hκ ξ εs hεs
    hεt (l7a_compDomain U i) U
    (l7a_compDomain_closure_compact U i)
    (l7a_compDomain_closure_subset U i) heq u v

theorem l8_localFormula_eq_internal_of_ambient_limit
    {d : ℕ} {κ : Rd d → ℝ}
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (U : TopologicalSpace.Opens (Rd d))
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hconv : Tendsto (fun n =>
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).1)
      atTop (𝓝 D.1)) (u v : Rd d) :
    l8_localFormula hd hκ ξ εs hεs U g u v = D.internal U u v := by
  let Dn : ℕ → ContMetric d := fun n =>
    l8_truncScaledMetric hd hκ ξ (hεs n) g
  have hDn (n : ℕ) : (Dn n).IsLength :=
    l8_truncScaledMetric_isLength hd hκ ξ (hεs n) g
  have hlow : D.internal U u v ≤
      l8_localFormula hd hκ ξ εs hεs U g u v := by
    unfold l8_localFormula
    apply le_iInf
    intro i
    let W := l7a_compDomain U i
    by_cases hu : u ∈ W
    · by_cases hv : v ∈ W
      · exact l8_internal_liminf_ge_enlarged_domain Dn D hD hconv W U
          (l7a_compDomain_connected U i).isPreconnected
          (l7a_compDomain_closure_compact U i)
          (l7a_compDomain_closure_subset U i) u v hu hv
      · have htop : (fun n => (Dn n).internal W u v) =
            (fun _ : ℕ => (⊤ : ℝ≥0∞)) := by
          funext n
          exact (Dn n).internal_eq_top_of_notMem_right hv
        change D.internal U u v ≤
          liminf (fun n => (Dn n).internal W u v) atTop
        rw [htop, liminf_const]
        exact le_top
    · have htop : (fun n => (Dn n).internal W u v) =
          (fun _ : ℕ => (⊤ : ℝ≥0∞)) := by
        funext n
        exact (Dn n).internal_eq_top_of_notMem_left hu
      change D.internal U u v ≤
        liminf (fun n => (Dn n).internal W u v) atTop
      rw [htop, liminf_const]
      exact le_top
  have hupp : l8_localFormula hd hκ ξ εs hεs U g u v ≤
      D.internal U u v := by
    rw [l7a_internal_eq_iInf_compDomain]
    unfold l8_localFormula
    apply iInf_mono
    intro i
    let W := l7a_compDomain U i
    by_cases hu : u ∈ W
    · by_cases hv : v ∈ W
      · exact l8_internal_liminf_le_internal Dn D hDn hconv W
          (l7a_compDomain_connected U i).isPreconnected u v hu hv
      · rw [D.internal_eq_top_of_notMem_right hv]
        exact le_top
    · rw [D.internal_eq_top_of_notMem_left hu]
      exact le_top
  exact le_antisymm hupp hlow

end HigherDimLQGMetric
