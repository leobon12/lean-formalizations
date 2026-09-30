import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocMain
import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocPair
import QuantumZipper.Proofs.Zipper.D3PlusN2ContPair
import QuantumZipper.Proofs.Zipper.D3PlusN2LipMain
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarMain
import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpread

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3-REM, step 1: the log-scale remainder is read from the embedded window

Task T13-HARD3-REM. `LSCCRemReadStmt`: on the window event
`resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R`, the remainder
`lsccR γ r α L X ω = lsccS + Tc` of the log scale equals
`log r + log (scaleSur γ 0 K (resField K W, 0))`, `W = n2Emb …` the circle-average embedded
model field, except on events of probability `→ 0` as `L → ∞`.

Proof (copy of `n2ZModelLoc_of_reg`, `D3PlusN2ModelLocMain.lean`): off the null set where the
model field fails to be locally good on `halfDisc r` (from the proved node `N2ZModelRegStmt`,
`n2ZModelReg_of_contPair`), a disagreement on the window event forces the embedding scale
`a = n2EmbScale = r e^{−Tc}` to exceed `r/K`, whose probability tends to `0`
(`tendsto_prob_n2EmbScale_gt`). When `a K ≤ r`, the window scale is `s / a` with `s` the model's
local scale on `halfDisc r` (`n2_scale_transfer`), and `scaleSur γ L r = s` on the good event
(`scaleSur_eq`, `mem_goodN1_of_pos`), so `lsccS = log s = log a + log (s/a)
= log r − Tc + log sK` and `lsccR = log r + log sK`.

Source: Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.8 (p. 79: after the
circle-average embedding the surfaces agree near `0`); Sheffield arXiv:1012.4797, proof of
Prop. 1.6 (p. 25). The Lean steps are own elementary arguments on the project's tools.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

open Prop16Area.G

/-- **Readout of the log-scale remainder from the embedded window.** -/
def LSCCRemReadStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K R : ℕ, 0 < K → Tendsto (fun L => P {ω | resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R ∧
      lsccR γ r α L X ω ≠
        Real.log r + Real.log (scaleSur γ 0 K (resField K (n2Emb γ α L r X ω), 0))}) atTop (𝓝 0)

/-- **The remainder readout holds** (DMS arXiv:1409.7055, proof of Prop. 4.8, p. 79). -/
theorem lsccRemRead_holds : LSCCRemReadStmt := by
  intro γ α r Ω _ P _ X hγ hγ2 hα hr hX K R hK
  have hReg := n2ZModelReg_of_contPair
    (n2ZContPair_of_osc (n2ZPairOsc_of_firstMode n2ZFirstModeStmt_holds))
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hδ : 0 < r / K := by positivity
  set N := {ω | ¬ ∀ L : ℝ, IsLocallyGoodOn γ (halfDisc r) (n2Model γ α L r X ω)} with hN
  have hN0 : P N = 0 :=
    ae_iff.1 ((hReg γ α r P X hγ hγ2 hα hr hX).mono fun ω h L => (h L).1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_prob_n2EmbScale_gt hγ hα hr hX hδ) (fun _ => bot_le) (fun L => ?_)
  calc _ ≤ P ({ω | r / K < n2EmbScale γ α L r X ω} ∪ N) := measure_mono ?_
    _ ≤ P {ω | r / K < n2EmbScale γ α L r X ω} + P N := measure_union_le _ _
    _ = P {ω | r / K < n2EmbScale γ α L r X ω} := by rw [hN0, add_zero]
  intro ω hω
  obtain ⟨hG, hne⟩ := hω
  by_cases hbad : ω ∈ N
  · exact Or.inr hbad
  refine Or.inl ?_
  by_contra hle
  simp only [mem_ofPred_eq, not_lt] at hle
  have hall : ∀ L : ℝ, IsLocallyGoodOn γ (halfDisc r) (n2Model γ α L r X ω) := by
    by_contra h; exact hbad h
  have hloc := hall L
  have ha := n2EmbScale_pos (γ := γ) (α := α) (L := L) hr X ω
  have hKa : n2EmbScale γ α L r X ω * K ≤ r := by
    rwa [le_div_iff₀ hK'] at hle
  obtain ⟨h0, hlt⟩ := hG
  have hR2 : (1 : ℝ) ≤ (R : ℝ) + 2 := by
    have := R.cast_nonneg (α := ℝ); linarith
  have hltK : scaleSur γ 0 K (resField K (n2Emb γ α L r X ω), 0) < K :=
    hlt.trans_le (div_le_self hK'.le hR2)
  set a := n2EmbScale γ α L r X ω with hadef
  set s := scaleParamOn γ (n2Model γ α L r X ω) (halfDisc r) with hsdef
  have htr : scaleSur γ 0 K (resField K (n2Emb γ α L r X ω), 0) = s / a :=
    n2_scale_transfer (y := n2Model γ α L r X ω) hγ ha hKa hloc h0 hltK
  have hs : 0 < s := by
    rw [htr] at h0
    exact (div_pos_iff_of_pos_right ha).1 h0
  have hgood := mem_goodN1_of_pos (γ := γ) (L := L) (r := r)
    (p := (localZ X r ω, circData α fun _ => 0)) hs
  have hS : lsccS γ r α L X ω = Real.log s := by
    simp only [lsccS]
    rw [scaleSur_eq hgood]
    rfl
  apply hne
  have hla : Real.log a =
      Real.log r + -ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω := by
    rw [hadef, n2EmbScale, Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp]
  simp only [lsccR]
  rw [hS, htr, Real.log_div hs.ne' ha.ne', hla]
  ring

end D3Plus
end QuantumZipper
