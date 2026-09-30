import QuantumZipper.Proofs.Thm18.G4GoodSetBasic
import QuantumZipper.Proofs.Thm18.G4WedgeCert

/-!
# Theorem 1.8, node G4: a Borel good set at the random unzipping time

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1). Task
G4-GOODSET.

`g4UnzipGoodSetStmt_of_roundUp` proves `G4UnzipGoodSetStmt` from the round-trip node
`G4RoundUpStmt` (already a hypothesis of `g4LenDrvReadStmt_of_nodes`), which is used only for
the positivity of the unzipping time `t'` and scale `a`.

Route (canonical space + tightness, **own argument**). For each `n ≥ 1`, the time reversal
`V_n = √κ B'_n` of the SLE driver at time `n` (a Brownian motion times `√κ`,
`Thm14FromThm13.isBrownianReal_revBM`) lies a.s. in the Borel fixed-time good set `G_n` of
Theorem 1.4 (`Thm14OptB.exists_goodDriverSet'`, the canonical-space argument), hence a.s. in a
countable union of compact subsets `K_{n,m} ⊆ G_n` (tightness, `exists_compacts_ae`). The good
set is the countable union of the compact images
`gsMap n (K_{n,m} × {(t,r) : t ∈ [1/(j+1), n], r ∈ [0,j+1], r√t = 1} × [1/(j+1), j+1])`,
Borel because compact. All its elements are good (`goodP_gsMap`: goodness at time `n` gives
goodness at every earlier time and scale), and it contains the pair `(g*, t'/a²)` at the random
time `t'`, with `n = ⌈t'⌉₊`. No measurability of `t'` or `a` is needed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

open Thm14WeldingData Thm14GoodDriverSet

/-- The compact parameter set `{(t, r) | t ∈ [1/(j+1), n], r ∈ [0, j+1], r √t = 1}`. -/
def gsParam (n j : ℕ) : Set (ℝ × ℝ) :=
  (Icc (1 / ((j : ℝ) + 1)) n ×ˢ Icc 0 ((j : ℝ) + 1)) ∩ {x | x.2 * Real.sqrt x.1 = 1}

theorem isCompact_gsParam (n j : ℕ) : IsCompact (gsParam n j) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_eq (continuous_snd.mul (Real.continuous_sqrt.comp continuous_fst))
      continuous_const)

/-- Compacts of good drivers on `[0,n]` whose union contains a.s. the time reversal at `n` of
the SLE_κ driver, `κ = γ² < 4`. -/
theorem exists_goodCompacts {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (n : ℕ) :
    ∃ K : ℕ → Set C(Icc (0 : ℝ) n, ℝ), (∀ m, IsCompact (K m)) ∧
      (∀ m, ∀ V ∈ K m, GoodDriver n (extIccPath (Nat.cast_nonneg n) V)) ∧
      ∀ᵐ ω ∂P, 0 < n →
        Continuous (drive (γ ^ 2) (Thm14FromThm13.revBM B (n : ℝ).toNNReal) ω) ∧
        ∃ m, pathC n (drive (γ ^ 2) (Thm14FromThm13.revBM B (n : ℝ).toNNReal) ω) ∈ K m := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ => ∅, fun _ => isCompact_empty, fun _ _ h => h.elim,
      ae_of_all _ fun _ h => (lt_irrefl _ h).elim⟩
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 < 4 := by nlinarith
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hB' := Thm14FromThm13.isBrownianReal_revBM hB (n : ℝ).toNNReal
  obtain ⟨G, hGm, hG, hae⟩ := Thm14OptB.exists_goodDriverSet' CaraR.revMapCaratheodory
    RS.rohdeSchrammSimple hκ hκ4 hn' P _ hB'
  obtain ⟨K, hKc, hKG, hKae⟩ := exists_compacts_ae (aemeasurable_pathC_drive hB' (γ ^ 2) n)
    hGm (hae.mono fun _ h => h.2)
  refine ⟨K, hKc, fun m V hV => hG V (hKG m hV), ?_⟩
  filter_upwards [hae, hKae] with ω h1 h2 _
  exact ⟨h1.1, h2⟩

end Thm18Asm
end QuantumZipper
