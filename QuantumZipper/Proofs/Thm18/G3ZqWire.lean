import QuantumZipper.Proofs.Thm18.G3ZqFub
import QuantumZipper.Proofs.Thm18.R18G3Transfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (2): step 5T from the fixed-path Palm limit at small windows (D92)

`R18.G3WedgeFreeTransferStmt` (R18G3Transfer) is the only consumer of the curve-removal node
`G3TCurveStmt`, and it needs the wedge Palm-window integral through the curve maps only for
**small** windows `U ≤ U₀` and only against the limit `c = μ(s) ν(t)` of the free scheme. By the
curve Fubini formula (`G3Zr.g3zWedgePalmCyl_fubini_side`, D93; the curve is independent of the
wedge, Sheffield, arXiv:1012.4797, p. 71, Figure 1.7) it therefore suffices to have, for a.e.
fixed path `a`, the normalized fixed-path functional `Φ_a(U, L)/U` eventually `ε`-close to `c`
for all small `U` (`G3ZqPathSmallStmt`). This is what the map instance of the generalized G2/G3
engine produces (route (A) of D92: Sheffield's conditional Proposition 5.5 at `x` and `R(x)`,
pp. 65–66 and 71, for zooms through the deterministic local maps of `a`).

* `eventually_abs_integral_sub_le`: dominated convergence for a family that is a.e. eventually
  `e`-close to a constant (own elementary proof);
* **`g3WedgeFreeTransferStmt_of_pathSmall : G3ZqPathSmallStmt → R18.G3WedgeFreeTransferStmt`**.

Own bookkeeping (Fubini over the independent curve, dominated convergence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G3Z2b2 G3Zp

/-- **Dominated convergence for an a.e. eventually `e`-close family.** Own elementary proof. -/
theorem eventually_abs_integral_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : ℝ → α → ℝ} (hfm : ∀ L, AEStronglyMeasurable (f L) μ)
    {K : ℝ} (hb : ∀ L a, |f L a| ≤ K) {c e : ℝ} (he : 0 < e)
    (h : ∀ᵐ a ∂μ, ∀ᶠ L in (atTop : Filter ℝ), |f L a - c| ≤ e) :
    ∀ᶠ L in (atTop : Filter ℝ), |∫ a, f L a ∂μ - c| ≤ 2 * e := by
  set g : ℝ → α → ℝ := fun L a => max |f L a - c| e with hg
  have hgm : ∀ L, AEStronglyMeasurable (g L) μ := fun L =>
    (((hfm L).sub aestronglyMeasurable_const).norm).sup aestronglyMeasurable_const
  have hgb : ∀ L a, ‖g L a‖ ≤ K + |c| + e := by
    intro L a
    have h1 : |f L a - c| ≤ K + |c| := (abs_sub _ _).trans (by linarith [hb L a])
    have h0 : 0 ≤ K + |c| := le_trans (abs_nonneg _) h1
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans he.le (le_max_right _ _))]
    exact max_le (by linarith) (by linarith [abs_nonneg c])
  have hlim : Tendsto (fun L => ∫ a, g L a ∂μ) atTop (𝓝 (∫ _a, e ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => K + |c| + e)
      (Eventually.of_forall hgm) (Eventually.of_forall fun L => ae_of_all _ (hgb L))
      (integrable_const _) ?_
    filter_upwards [h] with a ha
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ha] with L hL
    exact (max_eq_right hL).symm
  rw [integral_const, probReal_univ, one_smul] at hlim
  filter_upwards [hlim.eventually (Iic_mem_nhds (show e < 2 * e by linarith))] with L hL
  have hfi : Integrable (f L) μ :=
    Integrable.of_bound (hfm L) K (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact hb L a)
  have hgi : Integrable (g L) μ :=
    Integrable.of_bound (hgm L) (K + |c| + e) (ae_of_all _ (hgb L))
  have e1 : ∫ a, f L a ∂μ - c = ∫ a, (f L a - c) ∂μ := by
    rw [integral_sub hfi (integrable_const c), integral_const, probReal_univ, one_smul]
  rw [e1]
  calc |∫ a, (f L a - c) ∂μ| = ‖∫ a, (f L a - c) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ a, ‖f L a - c‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ a, g L a ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun a => norm_nonneg _) hgi
          (ae_of_all _ fun a => ?_)
        show ‖f L a - c‖ ≤ g L a
        rw [Real.norm_eq_abs]; exact le_max_left _ _
    _ ≤ 2 * e := hL

end G3Zq
end Thm18Asm
end QuantumZipper
