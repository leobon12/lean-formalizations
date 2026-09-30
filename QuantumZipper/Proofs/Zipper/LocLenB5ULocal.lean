import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.LocLenGlue
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.Thm13HeadlineV9
import QuantumZipper.Proofs.Zipper.JointModFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R3b: the uniform local (off-tip) limits `UnifLocalStmt`

`unifLocalStmt_of_extAll`: from the proved off-tip window node UO
(`RegUnif.unifOffTipAllStmt_of_extAll`: atomless local limits of `bdryApprox γ h⁰_s` on every
rational window avoiding `0`, a.s. for all `s ∈ [0,T]`) the windows are glued
(`E1.exists_isVagueLimitOnR_of_windows`, the sheaf property of Radon measures, Bourbaki,
*Integration*, Ch. III §2 No. 1, Prop. 1) to an atomless local limit on `{0}ᶜ`. No tip input
(`TipCore`, UT, UG, UA) is used: the tip is excluded, as in Sheffield arXiv:1012.4797 p. 56
(the boundary measure away from the tip) and Berestycki–Powell arXiv:2404.16642 Def 8.12
p. 281 (lengths of open boundary arcs). The gluing and the rational approximation of windows are
own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2

/-- A compact interval avoiding `0` lies in a rational window avoiding `0`. -/
theorem exists_rat_window_of_Icc_subset {p q : ℝ} (h : Icc p q ⊆ ({0} : Set ℝ)ᶜ) :
    ∃ u v : ℚ, (0 : ℝ) ∉ Icc (u : ℝ) v ∧ Icc p q ⊆ Ioo (u : ℝ) v := by
  by_cases hp : 0 < p
  · obtain ⟨u, hu0, hup⟩ := exists_rat_btwn hp
    obtain ⟨v, hv1, -⟩ := exists_rat_btwn (lt_add_one (max p q))
    refine ⟨u, v, fun h0 => by linarith [h0.1], fun y hy => ⟨by linarith [hy.1], ?_⟩⟩
    linarith [hy.2, le_max_right p q]
  · by_cases hq : q < 0
    · obtain ⟨u, -, hu1⟩ := exists_rat_btwn (sub_one_lt (min p q))
      obtain ⟨v, hqv, hv0⟩ := exists_rat_btwn hq
      refine ⟨u, v, fun h0 => by linarith [h0.2], fun y hy => ⟨?_, by linarith [hy.2]⟩⟩
      linarith [hy.1, min_le_left p q]
    · exact absurd rfl (h ⟨not_lt.1 hp, not_lt.1 hq⟩)

/-- **Deterministic gluing off the tip**: atomless local limits on all rational windows avoiding
`0` give an atomless local limit on `{0}ᶜ` (regular sample). -/
theorem exists_atomless_offTip_of_ratWindows {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    (hw : ∀ u v : ℚ, (0 : ℝ) ∉ Icc (u : ℝ) v →
      ∃ ν, IsVagueLimitOnR (Ioo (u : ℝ) v) (bdryApprox γ x) ν ∧ ∀ y, ν {y} = 0) :
    ∃ ν : Measure ℝ, IsVagueLimitOnR ({0}ᶜ) (bdryApprox γ x) ν ∧ ∀ y, ν {y} = 0 := by
  obtain ⟨μ, hμ⟩ := E1.exists_isVagueLimitOnR_of_windows (νs := bdryApprox γ x)
    isOpen_compl_singleton (fun k => LogSing.isFiniteMeasureOnCompacts_bdryApprox hx γ k)
    (fun p q h => by
      obtain ⟨u, v, h0, hsub⟩ := exists_rat_window_of_Icc_subset h
      obtain ⟨ν, hν, -⟩ := hw u v h0
      exact ⟨_, E1.isVagueLimitOnR_restrict_open hν isOpen_Ioo
        (Ioo_subset_Icc_self.trans hsub)⟩)
  refine ⟨μ, hμ, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    exact measure_mono_null (fun z hz => by simpa using hz) hμ.1
  · obtain ⟨u, v, h0, hsub⟩ := exists_rat_window_of_Icc_subset (p := y) (q := y)
      (fun z hz => by
        rw [Icc_self, mem_singleton_iff] at hz
        subst hz; exact hy)
    obtain ⟨ν, hν, hat⟩ := hw u v h0
    have hWsub : Ioo (u : ℝ) v ⊆ ({0} : Set ℝ)ᶜ := fun z hz hz0 => by
      rw [mem_singleton_iff] at hz0
      subst hz0; exact h0 (Ioo_subset_Icc_self hz)
    have e : μ.restrict (Ioo (u : ℝ) v) = ν := LocalRule.isVagueLimitOnR_unique isOpen_Ioo
      (E1.isVagueLimitOnR_restrict_open hμ isOpen_Ioo hWsub) hν
    have hyI : ({y} : Set ℝ) ⊆ Ioo (u : ℝ) v := singleton_subset_iff.2 (hsub ⟨le_rfl, le_rfl⟩)
    rw [← hat y, ← e, Measure.restrict_apply (measurableSet_singleton y), inter_eq_left.2 hyI]

variable {Ω : Type} [MeasurableSpace Ω]

/-- **`UnifLocalStmt` from AC-fam-ext** (no tip input): the proved UO windows glued off the tip. -/
theorem unifLocalStmt_of_extAll {κ T : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : RegUnif.AnchorUnifFamExtAllStmt κ P B X) : UnifLocalStmt κ T P B X := by
  filter_upwards [RegUnif.unifOffTipAllStmt_of_extAll hκ hκ4 hB hX hind hF T hT,
    RegUnif.ae_forall_isRegularSample (γ := Real.sqrt κ) hB hX hind] with ω hUO hreg
  intro s hs
  have hx : IsRegularSample (h0f κ s B X ω) := by
    rw [h0f_eq_unzippedField]; exact (hreg s hs.1).1
  exact exists_atomless_offTip_of_ratWindows hx (hUO s hs)

/-- **`UnifLocalStmt` holds** (closed form, `E5.extAllInput_holds`). -/
theorem unifLocalStmt_holds {κ T : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    UnifLocalStmt κ T P B X :=
  unifLocalStmt_of_extAll hκ hκ4 hT hB hX hind (E5.extAllInput_holds κ P B X hκ hκ4 hB hX hind)

end LocLen
end QuantumZipper
