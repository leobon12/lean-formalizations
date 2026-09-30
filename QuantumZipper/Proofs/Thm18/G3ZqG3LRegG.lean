import QuantumZipper.Proofs.Thm18.G3ZqG3LMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Region locality from ball locality under a goodness condition `Gd`

Copy of `G3ZqG3LReg.lean` with the plain goodness of the full scheme fields replaced by an
abstract condition `Gd` (`G3ZqZoomBallLocGZ`): the region-locality hypotheses `G3pRegLocXZ`,
`G3pRegLocRZ` follow from ball locality under `Gd` once the full field of the scheme satisfies
`Gd` a.s. at every point. For the map zoom `Gd = g3zMapGd` (pulled-back goodness).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

local notation "Ω₀" => gffBase.Ω

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- **Generic step**: ball locality ⇒ the region/full symmetric difference is eventually small. -/
theorem eventually_real_symmDiff_le_of_ballG
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {Gd : FieldSample → ℝ → Prop} (hB : G3ZqZoomBallLocGZ Z Gd)
    {s : Set LawD} (hs : s ∈ lawCyl)
    {P : Measure (Ω₀ × ℝ)} [IsFiniteMeasure P] {Y Y' : Ω₀ × ℝ → FieldSample}
    (hY : Measurable Y) (hY' : Measurable Y') {X : Ω₀ × ℝ → ℝ} (hX : Measurable X)
    {E : Set (Ω₀ × ℝ)} (hE : MeasurableSet E) {W : Set ℂ} (hWo : IsOpen W)
    (hEW : ∀ p ∈ E, (X p : ℂ) ∈ W) (hag : ∀ p, FcAgree W (Y p) (Y' p))
    (hgood : ∀ᵐ p ∂P, Gd (Y' p) (X p)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ C in (atTop : Filter ℝ), P.real (((fun p => Z C (Y p) (X p)) ⁻¹' s ∩ E) ∆
      ((fun p => Z C (Y' p) (X p)) ⁻¹' s ∩ E)) ≤ ε := by
  have hsm := measurableSet_lawCyl hs
  set S : ℝ → Set (Ω₀ × ℝ) := fun C => ((fun p => Z C (Y p) (X p)) ⁻¹' s ∩ E) ∆
      ((fun p => Z C (Y' p) (X p)) ⁻¹' s ∩ E) with hS
  have hSm : ∀ C, MeasurableSet (S C) := fun C =>
    ((((hZm C).comp (hY.prodMk hX)) hsm).inter hE).symmDiff
      ((((hZm C).comp (hY'.prodMk hX)) hsm).inter hE)
  have hlim : Tendsto (fun C => ∫⁻ p, (S C).indicator 1 p ∂P) atTop (𝓝 (∫⁻ _p, 0 ∂P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun C => measurable_one.indicator (hSm C))
      (Eventually.of_forall fun C => ae_of_all _ fun p =>
        Set.indicator_le (fun _ _ => le_rfl) p)
      (by rw [lintegral_const, one_mul]; exact measure_ne_top _ _) ?_
    filter_upwards [hgood] with p hp
    refine tendsto_const_nhds.congr' ?_
    by_cases hpE : p ∈ E
    · have hev := hB s hs (Y p) (Y' p) (X p) W hWo (hag p) (hEW p hpE) hp
      filter_upwards [hev] with C hC
      have hn : p ∉ S C := by
        simp only [hS, mem_symmDiff, mem_inter_iff, mem_preimage]
        tauto
      rw [indicator_of_notMem hn]
    · refine Eventually.of_forall fun C => ?_
      have hn : p ∉ S C := by
        simp only [hS, mem_symmDiff, mem_inter_iff, mem_preimage]
        tauto
      exact (indicator_of_notMem hn _).symm
  simp only [lintegral_zero] at hlim
  have hlim' : Tendsto (fun C => P (S C)) atTop (𝓝 0) := by
    refine hlim.congr fun C => ?_
    rw [lintegral_indicator_one (hSm C)]
  filter_upwards [hlim'.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))] with C hC
  exact ENNReal.toReal_le_of_le_ofReal hε.le hC.le

end R18
end QuantumZipper
