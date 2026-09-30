import QuantumZipper.Proofs.Thm18.G2Close
import QuantumZipper.Proofs.Thm18.G3PalmRTight
import QuantumZipper.Proofs.Thm18.Thm18Headline
import QuantumZipper.Proofs.Thm18.G3G2FullMix
import QuantumZipper.Proofs.Thm18.G3G2Scale
import QuantumZipper.Proofs.Thm18.G2FullMixGeo
import QuantumZipper.Proofs.Thm18.G3G2LocZoom
import QuantumZipper.Proofs.Thm18.G3G2Filter
import QuantumZipper.Proofs.Thm18.G3ConcreteMarkov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (5d): free-field two-point decorrelation for the concrete scheme

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
p. 71: "we condition on the restriction of the GFF to the complement of `B₁ := B_ε(x)` and
`B₂ := B_ε(R(x))` … Proposition 5.5 implies that even with this conditioning … the zoomed-in
figures converge in law … the conditional law of the restrictions of `h` to the two halves … are
independent by the standard GFF Markov property … in the `ε → 0` limit the `γ`-quantum wedges are
independent of each other."

`g3FreeTwoPoint_holds`: along `g3Filter`, the Palm law of the pair of full-field zooms at `x` and
at its length partner `R(x)` factorizes on cylinder rectangles in the limit. This is the part of
`Thm18Asm.g3_of_scheme` / `g3Stmt_of_openNodesV2` that does not use `G3TransferFullStmt`, and
all its inputs are proved:

* conditional independence of the region zooms given the field outside both half-discs and the
  Palm length (`condIndepCE_twoHalfDisc_palm`, the body of `g3MarkovStmt_concrete`);
* the `L¹` convergence of the conditional probabilities (`G2ConcreteStmt`, assembled as in
  `g3Stmt_of_openNodesV2` from `g3PalmRTightStmt_holds`, `g3AreaStmt_holds`, `g2FixMixStmt_holds`);
* `abs_real_inter_sub_le_of_condIndep` (G3Core), for the joint rectangles;
* the region-to-full-field locality `G3LocStmt` (`g3LocStmt_of_scale`) with
  `abs_measureReal_inter_sub_le` (G3G2Loc).

The marginal limits are the joint limit with `univ` in the other slot. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **G2 for the concrete scheme**, with all inputs proved (as in `g3Stmt_of_openNodesV2`). -/
theorem g3_g2ConcreteStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2ConcreteStmt γ :=
  g2ConcreteStmt_of_palmR_area_mix hγ hγ2
    (g3GeoPalmRStmt_of_tight hγ hγ2 (g3PalmRTightStmt_holds hγ hγ2)) (g3AreaStmt_holds hγ hγ2)
    (g2FullMixStmt_of_geo_fix (g3GeoStmt_of_tight hγ hγ2 (g3PalmRTightStmt_holds hγ hγ2))
      (g2FixMixStmt_holds hγ hγ2))

/-- **Locality of the zooms**, with all inputs proved. -/
theorem g3_locStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G3LocStmt γ :=
  g3LocStmt_of_scale (g3ScaleStmt_of_geo_area
    (g3GeoStmt_of_tight hγ hγ2 (g3PalmRTightStmt_holds hγ hγ2)) (g3AreaStmt_holds hγ hγ2))

/-- **Two-point decorrelation of the free-field zooms** (Sheffield p. 71). -/
theorem g3FreeTwoPoint_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ μ ν : Measure LawD, IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      ∀ s ∈ lawCyl, ∀ t ∈ lawCyl,
        Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ g3Vf γ i ⁻¹' t)) g3Filter
          (𝓝 (μ.real s * ν.real t)) ∧
        Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s)) g3Filter (𝓝 (μ.real s)) ∧
        Tendsto (fun i => (g3PalmLaw γ i).real (g3Vf γ i ⁻¹' t)) g3Filter (𝓝 (ν.real t)) := by
  obtain ⟨μ, ν, hμ, hν, hU, hV⟩ := g3_g2ConcreteStmt_holds hγ hγ2
  have hL := g3_locStmt_holds hγ hγ2
  -- the joint limit for the region zooms
  have hreg : ∀ s ∈ lawCyl, ∀ t ∈ lawCyl,
      Tendsto (fun i => (g3PalmLaw γ i).real (g3U γ i ⁻¹' s ∩ g3V γ i ⁻¹' t)) g3Filter
        (𝓝 (μ.real s * ν.real t)) := by
    intro s hs t ht
    have hsm := measurableSet_lawCyl hs
    have htm := measurableSet_lawCyl ht
    have ha : μ.real s ∈ Icc (0 : ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
    have herr := (hU s hs).add (hV t ht)
    rw [add_zero] at herr
    have hd : Tendsto (fun i => (g3PalmLaw γ i).real (g3U γ i ⁻¹' s ∩ g3V γ i ⁻¹' t) -
        μ.real s * ν.real t) g3Filter (𝓝 0) := by
      refine squeeze_zero_norm (fun i => ?_) herr
      rw [Real.norm_eq_abs]
      have := isProbabilityMeasure_g3 γ i
      exact abs_real_inter_sub_le_of_condIndep (outsideSigmaPalm_le_g3 i) (measurable_g3U' γ i)
        (measurable_g3V' γ i)
        (condIndepCE_twoHalfDisc_palm gffBase.gff i.r₁_pos i.r₂_pos i.dist_le (L₀ := L₀)
          (measurable_g3W γ i) (integrable_g3W γ i) (measurable_g3U γ i) (measurable_g3V γ i))
        hsm htm ha
    simpa using hd.add_const (μ.real s * ν.real t)
  -- the joint limit for the full-field zooms
  have hfull : ∀ s ∈ lawCyl, ∀ t ∈ lawCyl,
      Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ g3Vf γ i ⁻¹' t)) g3Filter
        (𝓝 (μ.real s * ν.real t)) := by
    intro s hs t ht
    have hsm := measurableSet_lawCyl hs
    have htm := measurableSet_lawCyl ht
    have herr : Tendsto (fun i => (g3PalmLaw γ i).real ((g3U γ i ⁻¹' s) ∆ (g3Uf γ i ⁻¹' s)) +
        (g3PalmLaw γ i).real ((g3V γ i ⁻¹' t) ∆ (g3Vf γ i ⁻¹' t))) g3Filter (𝓝 0) := by
      simpa using (hL.1 s hs).add (hL.2 t ht)
    have hd : Tendsto (fun i => (g3PalmLaw γ i).real (g3U γ i ⁻¹' s ∩ g3V γ i ⁻¹' t) -
        (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ g3Vf γ i ⁻¹' t)) g3Filter (𝓝 0) := by
      refine squeeze_zero_norm (fun i => ?_) herr
      rw [Real.norm_eq_abs]
      exact abs_measureReal_inter_sub_le _ (measurable_g3U' γ i hsm) (measurable_g3Uf γ i hsm)
        (measurable_g3V' γ i htm) (measurable_g3Vf γ i htm)
    have := (hreg s hs t ht).sub hd
    simpa using this
  refine ⟨μ, ν, hμ, hν, fun s hs t ht => ⟨hfull s hs t ht, ?_, ?_⟩⟩
  · simpa using hfull s hs univ univ_mem_lawCyl
  · simpa using hfull univ univ_mem_lawCyl t ht

end R18
end QuantumZipper
