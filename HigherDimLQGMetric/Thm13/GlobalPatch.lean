import HigherDimLQGMetric.Thm13.MetricTotal

/-!
# Countable patch from localized LFPP limits

All inputs to the patch are defined on the full distribution space. Its
countable edge and chain formulas make the output a measurable continuous
metric, with a Euclidean fallback away from the continuous metric locus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- A local edge, admitted only when its Euclidean span is below `1/(m+1)`. -/
def l8_patchStep (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (m : ℕ) (u v : Rd d) : ℝ≥0∞ :=
  if dist u v < 1 / ((m : ℝ) + 1) then
    l8_localEdge hd hκ ξ εs hεs g u v else ⊤

theorem l8_measurable_patchStep (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (m : ℕ) (u v : Rd d) :
    Measurable (fun g : DistRd d => l8_patchStep hd hκ ξ εs hεs g m u v) := by
  by_cases huv : dist u v < 1 / ((m : ℝ) + 1)
  · simpa only [l8_patchStep, huv, ↓reduceIte] using
      l8_measurable_localEdge hd hκ ξ εs hεs u v
  · simp only [l8_patchStep, huv, ↓reduceIte]
    exact measurable_const

/-- Sum of the edges through a finite list of interior vertices. -/
def l8_patchChain (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (m : ℕ) : Rd d → List (Rd d) → Rd d → ℝ≥0∞
  | u, [], v => l8_patchStep hd hκ ξ εs hεs g m u v
  | u, q :: qs, v => l8_patchStep hd hκ ξ εs hεs g m u q +
      l8_patchChain hd hκ ξ εs hεs g m q qs v

theorem l8_measurable_patchChain (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (m : ℕ) (u v : Rd d) (qs : List (Rd d)) :
    Measurable (fun g : DistRd d => l8_patchChain hd hκ ξ εs hεs g m u qs v) := by
  induction qs generalizing u with
  | nil => exact l8_measurable_patchStep hd hκ ξ εs hεs m u v
  | cons q qs ih =>
      exact (l8_measurable_patchStep hd hκ ξ εs hεs m u q).add (ih q)

/-- Infimum over rational-coordinate interior vertices. -/
def l8_patchInf (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (m : ℕ) (u v : Rd d) : ℝ≥0∞ :=
  ⨅ qs : List (Fin d → ℚ),
    l8_patchChain hd hκ ξ εs hεs g m u
      (qs.map HigherDimLFPP.ratPt) v

theorem l8_measurable_patchInf (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (m : ℕ) (u v : Rd d) :
    Measurable (fun g : DistRd d => l8_patchInf hd hκ ξ εs hεs g m u v) :=
  Measurable.iInf fun _ => l8_measurable_patchChain hd hκ ξ εs hεs m u v _

/-- The patch never shortens an ambient metric if each local edge dominates it. -/
theorem l8_patchInf_lower (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d)
    (hEdge : ∀ u v : Rd d,
      ENNReal.ofReal (D.1 (u, v)) ≤ l8_localEdge hd hκ ξ εs hεs g u v)
    (m : ℕ) (u v : Rd d) :
    ENNReal.ofReal (D.1 (u, v)) ≤ l8_patchInf hd hκ ξ εs hεs g m u v := by
  have hstep (x y : Rd d) :
      edist (D.pt x) (D.pt y) ≤ l8_patchStep hd hκ ξ εs hεs g m x y := by
    rw [ContMetric.edist_pt]
    unfold l8_patchStep
    split_ifs
    · exact hEdge x y
    · exact le_top
  have hchain (l : List (Rd d)) : ∀ x y : Rd d,
      edist (D.pt x) (D.pt y) ≤
        l8_patchChain hd hκ ξ εs hεs g m x l y := by
    induction l with
    | nil => exact hstep
    | cons q qs ih =>
        intro x y
        calc
          edist (D.pt x) (D.pt y) ≤
              edist (D.pt x) (D.pt q) + edist (D.pt q) (D.pt y) :=
            edist_triangle _ _ _
          _ ≤ l8_patchChain hd hκ ξ εs hεs g m x (q :: qs) y :=
            add_le_add (hstep x q) (ih q y)
  rw [← ContMetric.edist_pt]
  exact le_iInf fun qs => hchain (qs.map HigherDimLFPP.ratPt) u v

theorem l8_patchInf_ge_of_ambient_convergence (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d)
    (hconv : ∀ u v : Rd d,
      Tendsto (fun n => (l8_truncScaledMetric hd hκ ξ (hεs n) g).1 (u, v))
        atTop (𝓝 (D.1 (u, v))))
    (m : ℕ) (u v : Rd d) :
    ENNReal.ofReal (D.1 (u, v)) ≤ l8_patchInf hd hκ ξ εs hεs g m u v :=
  l8_patchInf_lower hd hκ ξ εs hεs g D
    (l8_localEdge_ge_ambient hd hκ ξ εs hεs g D hconv) m u v

/-- Pointwise patch value before continuous extension. -/
def l8_patchF (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (p : Rd d × Rd d) : ℝ :=
  limUnder atTop (fun m => (l8_patchInf hd hκ ξ εs hεs g m p.1 p.2).toReal)

theorem l8_measurable_patchF (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (p : Rd d × Rd d) :
    Measurable (fun g : DistRd d => l8_patchF hd hκ ξ εs hεs g p) :=
  (StronglyMeasurable.limUnder (fun m =>
    (ENNReal.measurable_toReal.comp
      (l8_measurable_patchInf hd hκ ξ εs hεs m p.1 p.2)).stronglyMeasurable)).measurable

/-- Global measurable assignment, totalized by continuous extension and a metric fallback. -/
def l8_patch (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) : ContMetric d :=
  l8_toContMetric (L8.contQ d (fun a => l8_patchF hd hκ ξ εs hεs g (L8.Qd d a)))

theorem l8_measurable_patch (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n) :
    Measurable (l8_patch hd hκ ξ εs hεs) := by
  unfold l8_patch
  exact l8_measurable_toContMetric.comp
    (L8.measurable_contQ (d := d) (fun a =>
      l8_measurable_patchF hd hκ ξ εs hεs (L8.Qd d a)))

/-- The patch recovers a given continuous metric once its rational-chain
infima have been identified with that metric at every mesh size. -/
theorem l8_patch_eq_of_patchInf (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d)
    (hInf : ∀ m : ℕ, ∀ u v : Rd d,
      l8_patchInf hd hκ ξ εs hεs g m u v = ENNReal.ofReal (D.1 (u, v))) :
    l8_patch hd hκ ξ εs hεs g = D := by
  have hF : ∀ p : Rd d × Rd d,
      l8_patchF hd hκ ξ εs hεs g p = D.1 p := by
    intro p
    unfold l8_patchF
    simp only [hInf, ENNReal.toReal_ofReal (D.nonneg p.1 p.2)]
    exact tendsto_const_nhds.limUnder_eq
  have heq : (fun a => l8_patchF hd hκ ξ εs hεs g (L8.Qd d a)) =
      D.1 ∘ L8.Qd d := funext fun a => hF _
  unfold l8_patch
  rw [heq, L8.contQ_comp, l8_toContMetric_coe]

end HigherDimLQGMetric
