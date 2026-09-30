import QuantumZipper.Proofs.Zipper.SWCoreB7cInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7d (2): a measurable replacement of the transported test functions

`awTest F u v f` is defined by choice. For `F` continuous and strictly increasing on `[u,v]` it
equals the explicit formula `awProxy F u v f x = f (invQ F u v x)` on `(F u, F v)` and `0` elsewhere,
where `invQ F u v x = ⨆_{y ∈ ℚ} (y if y ∈ [u,v], F y ≤ x; else u)` is the inverse read off
countably many values (`awTest_eq_awProxy`). If the values `F y` depend measurably on a parameter,
the proxy is jointly measurable (`measurable_awProxy`). This is the measurable test function of the
D70 transfer event. Own elementary proof.
-/

noncomputable section

open MeasureTheory Filter Set Topology

namespace QuantumZipper
namespace SWCore

open RegUnif

/-- The inverse of `F` on `[u,v]` read off rational points. -/
def invQ (F : ℝ → ℝ) (u v x : ℝ) : ℝ :=
  ⨆ y : ℚ, if (y : ℝ) ∈ Icc u v ∧ F y ≤ x then (y : ℝ) else u

/-- The explicit transported test function. -/
def awProxy (F : ℝ → ℝ) (u v : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if F u < x ∧ x < F v then f (invQ F u v x) else 0

theorem invQ_eq {F : ℝ → ℝ} {u v : ℝ} (hc : ContinuousOn F (Icc u v))
    (hm : StrictMonoOn F (Icc u v)) {y₀ : ℝ} (hy₀ : y₀ ∈ Ioo u v) :
    invQ F u v (F y₀) = y₀ := by
  have hy₀I := Ioo_subset_Icc_self hy₀
  have hbdd : BddAbove (range fun y : ℚ =>
      if (y : ℝ) ∈ Icc u v ∧ F y ≤ F y₀ then (y : ℝ) else u) := by
    refine ⟨v, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp only
    split_ifs with h
    · exact h.1.2
    · linarith [hy₀.1, hy₀.2]
  have hle : ∀ y : ℚ, (if (y : ℝ) ∈ Icc u v ∧ F y ≤ F y₀ then (y : ℝ) else u) ≤ y₀ := by
    intro y
    split_ifs with h
    · by_contra hlt
      push_neg at hlt
      exact absurd h.2 (not_le.2 (hm hy₀I h.1 hlt))
    · exact hy₀.1.le
  refine le_antisymm (ciSup_le hle) ?_
  refine le_of_forall_lt fun c hc' => ?_
  obtain ⟨y, hy1, hy2⟩ := exists_rat_btwn (max_lt hc' hy₀.1)
  have hyI : (y : ℝ) ∈ Icc u v := ⟨(le_max_right _ _).trans hy1.le, by linarith [hy₀.2]⟩
  have hFy : F y ≤ F y₀ := (hm.monotoneOn) hyI hy₀I hy2.le
  refine lt_of_lt_of_le (lt_of_le_of_lt (le_max_left c u) hy1) ?_
  refine le_trans ?_ (le_ciSup hbdd y)
  simp [hyI, hFy]

/-- **The explicit formula for `awTest`.** -/
theorem awTest_eq_awProxy {F : ℝ → ℝ} {u v : ℝ} (huv : u < v) (hc : ContinuousOn F (Icc u v))
    (hm : StrictMonoOn F (Icc u v)) (f : ℝ → ℝ) : awTest F u v f = awProxy F u v f := by
  funext x
  unfold awProxy
  split_ifs with hx
  · obtain ⟨y₀, hy₀, hFy₀⟩ := intermediate_value_Ioo huv.le hc hx
    rw [awTest_apply_of hm.injOn f hy₀ hFy₀, ← hFy₀, invQ_eq hc hm hy₀]
  · refine awTest_eq_zero_of fun y hy hFy => ?_
    exfalso
    apply hx
    rw [← hFy]
    exact ⟨hm ⟨le_rfl, huv.le⟩ (Ioo_subset_Icc_self hy) hy.1,
      hm (Ioo_subset_Icc_self hy) ⟨huv.le, le_rfl⟩ hy.2⟩

/-- **Joint measurability of the proxy** in (parameter, point). -/
theorem measurable_awProxy {E : Type*} [MeasurableSpace E] {Fe : E → ℝ → ℝ}
    (hF : ∀ y : ℝ, Measurable fun e => Fe e y) (u v : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun p : E × ℝ => awProxy (Fe p.1) u v f p.2 := by
  have hinv : Measurable fun p : E × ℝ => invQ (Fe p.1) u v p.2 := by
    unfold invQ
    refine Measurable.iSup fun y => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    refine (MeasurableSet.const _).inter ?_
    exact measurableSet_le ((hF y).comp measurable_fst) measurable_snd
  unfold awProxy
  refine Measurable.ite ?_ (hf.comp hinv) measurable_const
  exact (measurableSet_lt ((hF u).comp measurable_fst) measurable_snd).inter
    (measurableSet_lt measurable_snd ((hF v).comp measurable_fst))

end SWCore
end QuantumZipper
