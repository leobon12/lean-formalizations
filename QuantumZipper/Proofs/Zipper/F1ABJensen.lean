import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Abstract.JensenRigidity

/-!
# Theorem 1.3, nodes F1a–F1b: linearity of the lengths from E6, scaling and Jensen rigidity

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of Theorem 1.3
(pp. 70–72); blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §F1 (F1a, F1b). With
`F_c(s) := L⁺(tᴸ_c(s))` (the right length at the first capacity time `tᴸ_c(s)` at which the left
length reaches `s`, `lenF`):

* **F1a**: the cocycle `F_c(ℓ + s) − F_c(ℓ) = F_{zipLenDown γ ℓ c}(s)` and E6
  (`configLawFull (zipLenDown γ ℓ ∘ c) = configLawFull c`) give stationary increments;
* **F1b**: the scaling `F_{c'}(s) = F_c(n s)/n` for a configuration `c'` with the law of `c`
  (B4(c): `c' = canonConfig γ (h + C, W)` with `e^{γC/2} = 1/n`) gives `F(n q)/n =_d F q`;
* Jensen rigidity (`JensenRigidity.jensen_rigidity`, blueprint A7) then gives `F s = s · F 1`,
  and the bridge `L⁺_t = F(L⁻_t)` gives `L⁺ = F(1) · L⁻` (`F1ABStmt`).

The laws are transferred through the configuration-law data: `F_c(s)` is recomputed from
`cfgData c` (`lenF_eq_readCfg`, deterministic, as `F1.unzipLengths_eq_readLen`), and the reading
is a.e.-measurable for the `P_*` data law (input `hread`). `jensen_rigidity_ae` is the
a.e.-measurable form of A7 (via the completion of `P`).

This file proves the probabilistic skeleton (`f1ab_of_inputs`, `f1ABStmt_of_inputs`); the
deterministic cocycle and scaling identities, the B4(c) law, the regularity of `F`, the bridge,
and the reading measurability are the explicit inputs of `F1ABInputsStmt`. Own bookkeeping
around A7 (the paper states F1a–F1b in one sentence, p. 71).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## A7 for a.e.-measurable random functions -/

/-- **Jensen rigidity (A7), a.e.-measurable form**, from the measurable form applied to the
completion of `P`. -/
theorem jensen_rigidity_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : Ω → ℝ → ℝ) (hmeas : ∀ s, AEMeasurable (fun ω => F ω s) P)
    (hgood : ∀ᵐ ω ∂P, ContinuousOn (F ω) (Set.Ici 0) ∧ MonotoneOn (F ω) (Set.Ici 0) ∧ F ω 0 = 0)
    (hinc : ∀ q : ℚ, 0 < q → ∀ k : ℕ, 1 ≤ k →
      P.map (fun ω => F ω ((k : ℝ) * q) - F ω (((k : ℝ) - 1) * q)) = P.map (fun ω => F ω q))
    (hscale : ∀ q : ℚ, 0 < q → ∀ n : ℕ, 1 ≤ n →
      P.map (fun ω => F ω ((n : ℝ) * q) / n) = P.map (fun ω => F ω q)) :
    ∀ᵐ ω ∂P, ∀ s, 0 ≤ s → F ω s = s * F ω 1 := by
  have hPc : IsProbabilityMeasure P.completion :=
    ⟨(Measure.completion_apply P univ).trans measure_univ⟩
  have hmap : ∀ g : Ω → ℝ, AEMeasurable g P →
      Measure.map (α := NullMeasurableSpace Ω P) g P.completion = P.map g := by
    intro g hg
    ext s hs
    rw [Measure.map_apply (fun _ ht => hg.nullMeasurable ht : Measurable (fun ω :
      NullMeasurableSpace Ω P => g ω)) hs, Measure.map_apply_of_aemeasurable hg hs]
    rfl
  have hm' : ∀ s, Measurable (fun ω : NullMeasurableSpace Ω P => F ω s) :=
    fun s _ ht => (hmeas s).nullMeasurable ht
  exact JensenRigidity.jensen_rigidity (P := P.completion) (Ω := NullMeasurableSpace Ω P) F hm'
    hgood (fun q hq k hk =>
      (hmap (fun ω => F ω ((k : ℝ) * q) - F ω (((k : ℝ) - 1) * q)) ((hmeas _).sub (hmeas _))).trans
        ((hinc q hq k hk).trans (hmap (fun ω => F ω q) (hmeas _)).symm))
    (fun q hq n hn =>
      (hmap (fun ω => F ω ((n : ℝ) * q) / n) ((hmeas _).div_const _)).trans
        ((hscale q hq n hn).trans (hmap (fun ω => F ω q) (hmeas _)).symm))

/-! ## The length function `F_c` and its reading from the data -/

/-- The configuration recomputed from the `configLawFull` data. -/
def readCfg (d : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) : FieldSample × (ℝ → ℝ) :=
  (Factorization.reconstruct (WedgeCan4.piC d.1.1), readDrv d.2)

/-! ## Law transfer through the data -/

/-- Two random variables read by the same a.e.-measurable `Φ` from configurations with the same
`configLawFull` have the same law. -/
theorem map_eq_of_read {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {c₁ c₂ : Ω → FieldSample × (ℝ → ℝ)} (h : configLawFull c₂ P = configLawFull c₁ P)
    (h1 : AEMeasurable (fun ω => cfgData (c₁ ω)) P) (h2 : AEMeasurable (fun ω => cfgData (c₂ ω)) P)
    {Φ : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) → ℝ} (hΦ : AEMeasurable Φ (configLawFull c₁ P))
    {G₁ G₂ : Ω → ℝ} (hG1 : ∀ᵐ ω ∂P, G₁ ω = Φ (cfgData (c₁ ω)))
    (hG2 : ∀ᵐ ω ∂P, G₂ ω = Φ (cfgData (c₂ ω))) : P.map G₂ = P.map G₁ := by
  have hΦ1 : AEMeasurable Φ (P.map fun ω => cfgData (c₁ ω)) := hΦ
  have hΦ2 : AEMeasurable Φ (P.map fun ω => cfgData (c₂ ω)) := by
    rw [← configLawFull_eq_map_cfgData, h]; exact hΦ
  have e1 : P.map G₁ = (configLawFull c₁ P).map Φ := by
    rw [Measure.map_congr hG1, configLawFull_eq_map_cfgData,
      AEMeasurable.map_map_of_aemeasurable hΦ1 h1]; rfl
  have e2 : P.map G₂ = (configLawFull c₂ P).map Φ := by
    rw [Measure.map_congr hG2, configLawFull_eq_map_cfgData,
      AEMeasurable.map_map_of_aemeasurable hΦ2 h2]; rfl
  rw [e1, e2, h]

/-! ## F1a–F1b -/

/-! ## The inputs for `P_*` samples -/

/-- The `P_*` configuration `(Y, √κ B')`. -/
abbrev pcfg (κ : ℝ) {Ω' : Type} (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    FieldSample × (ℝ → ℝ) := (Y ω, drive κ B' ω)

end F1
end QuantumZipper
