import QuantumZipper.Proofs.Zipper.LocLenStmts
import QuantumZipper.Proofs.Zipper.LocLenGlue
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.YBdryMerge2Tip
import QuantumZipper.Proofs.Zipper.WedgeYGoodArea
import QuantumZipper.Proofs.Zipper.SWCoreA9Main
import QuantumZipper.Proofs.Zipper.Thm13HeadlineV9

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), R3a: the unzipped `Γ⁰` fields are good off the tip

`YGoodOffAllStmt` (LocLenStmts.lean): a.s., for all `t ≥ 0`, `y_t = F2.unzY κ X W t` is
`IsLQGGoodOff (√κ) · {0}`. This is the old proof of `WedgeUnzip.YGoodAllStmt`
(`E6.e6n_yGoodAll`, via `yGoodAll_of_unif_merge`) **with the tip removed**: no tip input
(`TipCore`, `UnifTipStmt`, `UnifGlobalStmt`, `YTipOffStmt`) is used.

* Off-tip dyadic windows: UO at every horizon (`RegUnif.unifOffTipAllStmt_of_extAll`, from
  `F1.ExtAllInput` = Sheffield–Wang arXiv:1605.06171 Thm 4.3 in the D64 family form), all times
  via the horizons `T = n + 1`.
* Offset merging off the tip: `WedgeUnzip.YMergeOffTipStmt` (test functions whose support avoids
  `0`), combined with the dyadic window limits by the local copy
  `hasBdryLimitOn_of_dyadic_merge` of `WedgeUnzip.hasBdryLimit_of_dyadic_merge`.
* Real windows avoiding `0` are covered by slightly larger rational windows (`HasBdryLimitOn.mono`),
  glued by `isLQGGoodOff_of_windows`.
* Area part and regularity: unchanged (`WedgeUnzip.yAreaLimAll_of_merge`,
  `WedgeUnzip.ae_forall_isRegularSample_unzY`).

Paper: Sheffield arXiv:1012.4797 p. 56 (the boundary lengths of the unzipped field are read away
from the tip, one measure per side); Sheffield–Wang arXiv:1605.06171 Thm 4.3 (the off-tip limits).
Wiring: own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **Local copy of `WedgeUnzip.hasBdryLimit_of_dyadic_merge`**: a dyadic local vague limit on `U`
plus offset merging for test functions supported in `U` give the offset-uniform local limit. -/
theorem hasBdryLimitOn_of_dyadic_merge {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {U : Set ℝ} {ν : Measure ℝ} (hν : IsVagueLimitOnR U (bdryApprox γ x) ν)
    (hm : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      Tendsto (WedgeUnzip.bdryMergeDiff γ x f) goodFilter (𝓝 0)) :
    HasBdryLimitOn γ x U ν := by
  obtain ⟨F, hF⟩ := hx
  refine ⟨hν.1, hν.2.1, fun f hf hfc hfU => ?_⟩
  have h1 : Tendsto (fun i : ℕ × ℝ => ∫ t, f t ∂bdryApprox γ x i.1) goodFilter
      (𝓝 (∫ t, f t ∂ν)) :=
    (hν.2.2 f hf hfc hfU).comp (tendsto_fst (f := (atTop : Filter ℕ)) (g := 𝓟 (Icc (1 : ℝ) 2)))
  have h2 := (hm f hf hfc hfU).add h1
  rw [zero_add] at h2
  refine h2.congr fun i => ?_
  simp only [WedgeUnzip.bdryMergeDiff]
  rw [← GoodSample.bdryR_radius γ hF i.1, one_mul]
  ring

/-- A real window `[p,q]` avoiding `0` lies in a rational window `[u,v]` avoiding `0`. -/
theorem exists_rat_window_avoid_zero {p q : ℝ} (h0 : (0 : ℝ) ∉ Icc p q) :
    ∃ u v : ℚ, (u : ℝ) ≤ p ∧ q ≤ v ∧ (0 : ℝ) ∉ Icc (u : ℝ) v := by
  have : 0 < p ∨ q < 0 := by
    by_contra h
    exact h0 ⟨not_lt.1 fun hp => h (Or.inl hp), not_lt.1 fun hq => h (Or.inr hq)⟩
  rcases this with hp | hq
  · obtain ⟨u, hu0, hup⟩ := exists_rat_btwn hp
    obtain ⟨v, hv⟩ := exists_rat_gt q
    exact ⟨u, v, hup.le, hv.le, fun h => (not_le.2 hu0) h.1⟩
  · obtain ⟨v, hqv, hv0⟩ := exists_rat_btwn hq
    obtain ⟨u, hu⟩ := exists_rat_lt p
    exact ⟨u, v, hu.le, hqv.le, fun h => (not_le.2 hv0) h.2⟩

/-- **`YGoodOffAllStmt` from AC-fam-ext, offset merging off the tip and area merging** (no tip
input). -/
theorem yGoodOffAll_of_extAll (hExt : F1.ExtAllInput) (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hYA : WedgeUnzip.YAreaMergeStmt) : YGoodOffAllStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hUO := RegUnif.unifOffTipAllStmt_of_extAll hκ hκ4 hB hX hind
    (hExt κ P B X hκ hκ4 hB hX hind)
  have hy := F2.ae_forall_nonneg_of_horizons (P := P) (Q := fun s ω =>
      ∀ u v : ℚ, (0 : ℝ) ∉ Icc (u : ℝ) v →
        ∃ ν, IsVagueLimitOnR (Ioo (u : ℝ) v) (bdryApprox (Real.sqrt κ) (B2.h0f κ s B X ω)) ν ∧
          ∀ x, ν {x} = 0)
    fun n => hUO _ (Nat.cast_add_one_pos n)
  filter_upwards [hy, hYO κ hκ hκ4 P B X hB hX hind,
    WedgeUnzip.yAreaLimAll_of_merge hYA κ hκ hκ4 P B X hB hX hind,
    WedgeUnzip.ae_forall_isRegularSample_unzY (κ := κ) hB hX hind]
    with ω hyω hmω haω hrω t ht
  refine isLQGGoodOff_of_windows isClosed_singleton (hrω t ht) (haω t ht) fun p q hpq => ?_
  have h0 : (0 : ℝ) ∉ Icc p q := fun h =>
    (eq_empty_iff_forall_notMem.1 hpq) 0 ⟨h, rfl⟩
  obtain ⟨u, v, hu, hv, huv⟩ := exists_rat_window_avoid_zero h0
  obtain ⟨ν, hν, -⟩ := hyω t ht u v huv
  rw [F2.h0f_eq_unzY] at hν
  have hW := hasBdryLimitOn_of_dyadic_merge (hrω t ht) hν fun f hf hfc hfU =>
    hmω t ht f hf hfc fun h0' => huv (Ioo_subset_Icc_self (hfU h0'))
  exact ⟨_, hW.mono isOpen_Ioo (Ioo_subset_Ioo hu hv)⟩

/-- **`YGoodOffAllStmt` from offset merging off the tip alone**: `F1.ExtAllInput` and
`YAreaMergeStmt` are proved (`E5.extAllInput_holds`, `SWCore.yAreaMergeStmt_holds`). -/
theorem yGoodOffAll_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) : YGoodOffAllStmt :=
  yGoodOffAll_of_extAll E5.extAllInput_holds hYO SWCore.yAreaMergeStmt_holds

end LocLen
end QuantumZipper
