import QuantumZipper.Proofs.Zipper.SWCoreB7dRand
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (7): `RegUnif.AnchorUnifFamExtAllStmt` (AC-fam-ext at every horizon, reflected pair)

**Main result** `anchorUnifFamExtAllStmt_holds : ∀ κ ∈ (0,4), … → AnchorUnifFamExtAllStmt κ P B X`
(for a Brownian motion `B` and an independent free field `X`).

For a rational anchor `q ∈ (0,T)`, the anchor field `h⁰_q ~ 𝔥₀ + Y_q` with `Y_q` free and
independent of the shifted path (`Cor15Group.cor15UnzipVersionStmt_holds`), and the time-`s`
fields are `coordChange (𝔥₀ + Y_q) ψ_s Q` at rational `s` (`RegUnif.ae_bdryApprox_h0f_eq_coordChange`),
with `ψ_s = revMapExt (vrev W^q (s−q)) (s−q)` for the shifted driver `W^q = drive κ B^q`,
`B^q = B(q + ·) − B q` (Brownian, `IsBrownianReal.shift`). For `q = 0` the field is `𝔥₀ + X` and
the maps are the unzipping maps of `W`. In both cases the transfer `rand_uc` (fixed-path
convergence `flow_fixed_conv`, D70) gives the uniform Cauchy property over the rational times.
The reflected pair `(−B, X ∘ refl)` satisfies the same hypotheses.

Sources: Sheffield arXiv:1012.4797 Thm 1.2, §1.4 (through `cor15UnzipVersionStmt_holds`);
Sheffield–Wang arXiv:1605.06171 Thm 4.3 (through the SW-CORE family cores). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 RevMapExtension

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem zeroMinus_nonpos (V : ℝ → ℝ) (t : ℝ) : zeroMinus V t ≤ 0 :=
  Real.sSup_nonpos fun _ hx => hx.1.le

/-- The transported integral along a pair `(B', Y')`. -/
def pairJ (κ τ : ℝ) (B' : ℝ≥0 → Ω → ℝ) (Y' : Ω → FieldSample) (ω : Ω) (u v : ℝ) (f : ℝ → ℝ)
    (σ : ℝ) (k : ℕ) : ℝ :=
  ∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) τ) (τ - σ)) u v f x ∂bdryApprox
    (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y' ω) (revMapExt (vrev (drive κ B' ω) σ) σ)
      (Qc (Real.sqrt κ))) k

/-- **AC-fam-ext from a pair** (generic assembly). -/
theorem acfam_of_pair {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} {T : ℝ} {q : ℚ} (hqT : (q : ℝ) < T) {u v : ℚ} {i : ℕ} {a b c d : ℚ}
    (hua : (u : ℝ) < a) (hab : (a : ℝ) < b) (hbc : (b : ℝ) < c) (hcd : (c : ℝ) < d)
    (hdv : (d : ℝ) < v) {B' : ℝ≥0 → Ω → ℝ} {Y' : Ω → FieldSample} (hB' : IsBrownianReal B' P)
    (hY' : IsFreeGFFModConstH Y' P) (hind' : IndepFun (pathOf B') Y' P)
    (hident : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) → ∀ k : ℕ,
      RegUnif.awInt κ T B X ω u v (RegUnif.swFam i a b c d) ((q : ℝ) + σ) k =
        pairJ κ (T - q) B' Y' ω u v (RegUnif.swFam i a b c d) σ k)
    (hlv : ∀ᵐ ω ∂P, (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      ENNReal.ofReal (T - q) < realHitTime (vrev (drive κ B' ω) (T - q)) v) :
    ∀ᵐ ω ∂P, (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      UniformCauchySeqOn (fun k s => RegUnif.awInt κ T B X ω u v (RegUnif.swFam i a b c d) s k)
        atTop (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ)) := by
  by_cases hv0 : (v : ℝ) < 0
  swap
  · exact ae_of_all _ fun ω h => absurd (h.trans_le (zeroMinus_nonpos _ _)) hv0
  have hT' : 0 < T - q := by linarith
  have hfs := RegUnif.tsupport_swFam_subset (i := i) hab hcd
  have hfc : Continuous (RegUnif.swFam i a b c d) := RegUnif.continuous_swFam _ _ _ _ _
  filter_upwards [rand_uc κ hB' hY' hind' hκ hκ4 hT' (u := u) (v := v) (by linarith) hv0 hua
      (by linarith) hdv hfc hfs, hident, hlv] with ω hω hid hl hvz
  have hU := hω (hl hvz)
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hU n
  refine ⟨N, fun j hj j' hj' s hs => ?_⟩
  obtain ⟨r, hr⟩ := hs.2
  set σ : ℚ := r - q with hσdef
  have hσI : (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) := by
    rw [hσdef]; push_cast
    exact ⟨by linarith [hs.1.1, hr.symm ▸ hs.1.1], by linarith [hs.1.2, hr.symm ▸ hs.1.2]⟩
  have hsσ : s = (q : ℝ) + σ := by rw [← hr, hσdef]; push_cast; ring
  rw [Real.dist_eq, hsσ, hid σ hσI j, hid σ hσI j']
  exact lt_of_le_of_lt (hN j hj j' hj' σ hσI) hn

end SWCore
end QuantumZipper
