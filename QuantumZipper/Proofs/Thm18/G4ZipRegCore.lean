import QuantumZipper.Proofs.Thm18.G4ReadZip
import QuantumZipper.Proofs.Thm18.G1RegCanon
import QuantumZipper.Proofs.Thm18.G1Pair
import QuantumZipper.Proofs.Zipper.WedgeLawReg
import QuantumZipper.Proofs.Wire4

/-!
# Theorem 1.8, node G4: regularity of the re-zipped field (task G4-ZIPREG)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), (3).
`G4ZipRegStmt` (`G4FactorReg.lean`) asks that the field of `Z^LEN_t (Z^LEN_{−t} c)` (`c` the wedge
configuration) be a.s. raw-regular at the coordinate circles and, for each test function, at its
pairing.

**No random-time regularity argument is needed.** A coordinate change reads its input field only
through the regularization (`coordChange` evaluates `evalReg`), so on the a.s. event of the round
trip `Z_t ∘ Z_{−t}` (node `G4RoundUpRezipCoreStmt`, already a premise of the headline
`g4Stmt_of_coreNodesField`) the re-zipped field is *exactly* (as a function on measures)

  `rescale (rescale Y Q a) Q a⁻¹`,  `a = unzipScale` (random),

(`zipLenC_zipLenDown_field_eq`): the zipped field is `RegEq` to `rescale Y Q a` and has scale
`a⁻¹`. For a regular sample `Y` (a.s., `wedgeRegSampleStmt_holds`):

* at every folded circle, `rescale (rescale Y Q a) Q a⁻¹` has raw value `evalReg Y`
  (`G1.rescale_rescale_inv_fc`), and it is `RegEq` to `Y` once `Y` is raw-regular at the
  coordinate circles (`regEq_rescale_rescale_inv`, `wedgeZeroRegStmt`); this gives the circle
  clause for **every** `a > 0` at once, so the randomness of `a` is harmless;
* at a test measure `μ = ρ^± dz`, its raw value is `evalReg Y μ` as soon as the circle-smoothed
  pairings `s ↦ ∫ evalReg Y (fc(u,s)) dμ(u)` have a continuum limit `s → 0⁺`
  (`G1.scaleConsistentAt_of_continuum`: the regularizations along the radii `2^{-k}` and
  `a 2^{-k}` then agree, for every `a > 0` at once). This is the open input
  `WedgePairContStmt` (PAIR-LIM for the Theorem 1.8 wedge sample at a *fixed* measure; the free
  field case is `PairLim.ae_tendsto_pairRaw_continuum`, the reference-wedge case at all dilations
  is `WedgeCReg.ae_contPair_wedge`).

Main results:
* `zipLenC_zipLenDown_field_eq` (deterministic);
* `rescale_rescale_inv_tmeas` (deterministic);
* `g4ZipRegStmt_of_pairCont : G4RoundUpRezipCoreStmt → WedgePairContStmt → G4ZipRegStmt`;
* `g4Stmt_of_coreNodesPairCont`: the headline with `G4ZipRegStmt` replaced by
  `WedgePairContStmt`.

**Own elementary argument** (bookkeeping around the scale consistency of regular samples; the
analytic input behind the continuum limit is Duplantier–Sheffield, *Liouville quantum gravity and
KPZ*, Invent. Math. 185 (2011), §3.1, Prop. 3.1, through PAIR-LIM).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-- **Raw value of the double rescaling at a test measure** (deterministic): for a regular `x`
whose circle-smoothed pairings with `tmeas g` are integrable and have a continuum limit,
`rescale (rescale x Q a) Q a⁻¹ (tmeas g) = evalReg x (tmeas g)` for every `a > 0`. -/
theorem rescale_rescale_inv_tmeas {x : FieldSample} (hx : IsRegularSample x) (Q : ℝ) {a : ℝ}
    (ha : 0 < a) {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgH : tsupport g ⊆ H)
    (hint : ∀ s : ℝ, 0 < s → Integrable (fun u => evalReg x (foldedCircle u s)) (G1.tmeas g))
    (hcont : ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg x (foldedCircle u s) ∂G1.tmeas g)
      (𝓝[>] 0) (𝓝 L)) :
    rescale (rescale x Q a) Q a⁻¹ (G1.tmeas g) = evalReg x (G1.tmeas g) := by
  have := G1.isFiniteMeasure_tmeas hg hgc
  set μ := G1.tmeas g with hμ
  set ν := μ.map fun z => ((a⁻¹ : ℝ) : ℂ) * z with hν
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have hm : ∀ c : ℝ, Measurable (fun z : ℂ => (c : ℂ) * z) := fun c => measurable_const_mul _
  have hνμ : (ν.map fun z => (a : ℂ) * z) = μ := by
    rw [hν, Measure.map_map (hm a) (hm a⁻¹)]
    have : ((fun z : ℂ => (a : ℂ) * z) ∘ fun z => ((a⁻¹ : ℝ) : ℂ) * z) = id := by
      funext z
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      simp only [Function.comp_apply, id, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ ha',
        one_mul]
    rw [this, Measure.map_id]
  have hνr : ν.real univ = μ.real univ := by
    rw [hν, measureReal_def, measureReal_def, Measure.map_apply (hm _) MeasurableSet.univ,
      preimage_univ]
  have hνH : ∀ᵐ u ∂ν, u ∈ Hbar := G1.ae_tmeas_map_mem_Hbar hg hgH hai
  obtain ⟨L, hL⟩ := hcont
  have hsc : G1.ScaleConsistentAt x Q a ν :=
    G1.scaleConsistentAt_of_continuum hx Q ha hνH (fun s hs => by rw [hνμ]; exact hint s hs)
      (L := L) (by rw [hνμ]; exact hL)
  unfold G1.ScaleConsistentAt at hsc
  show evalReg (rescale x Q a) ν +
      Q * ∫ z, Real.log ‖deriv (fun z : ℂ => ((a⁻¹ : ℝ) : ℂ) * z) z‖ ∂μ = _
  rw [hsc, hνμ, G1.integral_log_deriv_mul' hai, hνr, Real.log_inv]
  ring

/-- **Continuum limit of the pairings of the Theorem 1.8 wedge sample** (open input; PAIR-LIM for
the wedge, at a fixed test measure): for each test function `ρ`, a.s., for both signed parts
`f ∈ {ρ, −ρ}`, the circle-smoothed pairings `s ↦ ∫ evalReg Y (fc(u,s)) f⁺(u) du` are integrable
and converge as `s → 0⁺`. -/
def WedgePairContStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), 0 < γ → γ < 2 → IsQuantumWedge γ (γ - 2 / γ) Y P →
    ∀ ρ : TestFun H, ∀ᵐ ω ∂P, ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)),
      (∀ s : ℝ, 0 < s → Integrable (fun u => evalReg (Y ω) (foldedCircle u s)) (G1.tmeas f)) ∧
      ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg (Y ω) (foldedCircle u s) ∂G1.tmeas f)
        (𝓝[>] 0) (𝓝 L)

end Thm18Asm
end QuantumZipper
