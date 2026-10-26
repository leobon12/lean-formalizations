import SupercriticalLFPPAS.Frozen.Lfpp_ae_lscTendsto
import SupercriticalLFPPAS.Frozen.Exists_jointHeatVersion
import SupercriticalLFPPAS.Assembly.AllXi
import SupercriticalLFPPAS.Implementation.JointHeatVersion
import Mathlib.Util.AssertNoSorry

/-! Release audit of the advertised theorems: the two frozen theorems, then the supporting theorems (proved, not
frozen). Every `#print axioms` report must list only axioms among `propext`, `Classical.choice` and `Quot.sound`
(any subset). -/
set_option autoImplicit false

-- Frozen theorems: Theorem 1.1, and the existence of jointly continuous heat versions.
assert_no_sorry SupercriticalLFPPAS.lfpp_ae_lscTendsto
#print axioms SupercriticalLFPPAS.lfpp_ae_lscTendsto
assert_no_sorry SupercriticalLFPPAS.exists_jointHeatVersion
#print axioms SupercriticalLFPPAS.exists_jointHeatVersion

-- Theorem 1.1 for every ξ > 0.
assert_no_sorry SupercriticalLFPPAS.Assembly.lfpp_ae_lscTendsto_allXi
#print axioms SupercriticalLFPPAS.Assembly.lfpp_ae_lscTendsto_allXi

/-- The all-ξ theorem implies the frozen Theorem 1.1 (drop the hypothesis `xiCrit < ξ`). -/
example : type_of% @SupercriticalLFPPAS.lfpp_ae_lscTendsto :=
  fun ξ _ => SupercriticalLFPPAS.Assembly.lfpp_ae_lscTendsto_allXi ξ

/-- The two statements differ exactly by that hypothesis. -/
example : (type_of% @SupercriticalLFPPAS.lfpp_ae_lscTendsto) =
    ∀ ξ : Set.Ioi (0 : ℝ), SupercriticalConformalCovariance.xiCrit < (ξ : ℝ) →
      type_of% (SupercriticalLFPPAS.Assembly.lfpp_ae_lscTendsto_allXi ξ) := rfl

-- Jointly continuous heat versions: uniqueness at every ε at once, and the pathwise form of existence.
assert_no_sorry SupercriticalLFPPAS.ae_eq_of_jointHeatVersions
#print axioms SupercriticalLFPPAS.ae_eq_of_jointHeatVersions
assert_no_sorry SupercriticalLFPPAS.Implementation.exists_jointHeatVersion_pathwise
#print axioms SupercriticalLFPPAS.Implementation.exists_jointHeatVersion_pathwise

-- Without the joint-continuity hypothesis the statement is false: the refuted reading `RefutedV1.Thm11v1`.
assert_no_sorry SupercriticalLFPPAS.RefutedV1.not_thm11v1
#print axioms SupercriticalLFPPAS.RefutedV1.not_thm11v1

/-- The refuted reading is the frozen Theorem 1.1 without the joint-continuity hypothesis: the frozen statement
follows from it, so the hypothesis is the only difference that matters. -/
example (H : SupercriticalLFPPAS.RefutedV1.Thm11v1) : type_of% @SupercriticalLFPPAS.lfpp_ae_lscTendsto := by
  intro ξ hξ m hm Ω _ P _ h hh X hX _ L hL
  exact H ξ hξ m hm P h hh X hX L hL
