import QuantumZipper.Proofs.Zipper.UnifUOAnchor
import QuantumZipper.Proofs.Zipper.UnifUGReduce
import QuantumZipper.Proofs.Zipper.UnifClColl
import QuantumZipper.Proofs.Loewner.CaraR1

/-!
# UNIF-UO (3): the off-tip windows `UnifOffTipStmt` (UO)

Task UNIF-UO (decision D26). `RegUnif.UnifOffTipStmt` (UO, `UnifUGReduce.lean`) asks: a.s., for
all `s ∈ [0,T]` and all rational windows `(u,v)` of the time-`s` picture with `0 ∉ [u,v]`, an
atomless local vague limit of `bdryApprox γ h⁰_s` on `(u,v)`.

* **`ae_offTip_minus`** (minus side, `v < 0`), from `AnchorUnifFamExtStmt` (AC-fam-ext): at
  `s = 0` by the fixed-time result `ae_zero_time_atomless`; at `s ∈ (0,T]` the map
  `F_s = realRevMap V (T − s)` sends `(−∞, 0₋(T − s))` increasingly onto a set whose closure
  contains `(−∞, 0)` (`F_s → −∞` at `−∞`, `F_s → 0` at `0₋(T − s)⁻`, `B5.realRevMap_endpoints`),
  so `[u,v] ⊆ F_s(a,b)` for a rational window `a < b < 0₋(T − s)`; a rational anchor
  `q ∈ [0,s)` with `b < 0₋(T − q)` exists by continuity of `0₋`; the extended anchor
  (`ae_anchor_ext`) gives an atomless limit on `F_s(a,b)`, restricted to `(u,v)`.
  This covers windows on the unzipped curve, on the outer real line, and straddling `O⁻_s`.
* **`UnifOffTipPlusStmt`** (plus side, `u > 0`): open, a hypothesis here. D26 routes it through
  the reflection `B ↦ −B` (`F1Reflect`); the reflection identity for the unzipped fields
  `h0f κ s (−B) (X ∘ refl)` is not in the repository.
* **`unifOffTipStmt_of_ext`**: AC-fam-ext + plus side ⇒ UO; **`unifGlobal_unifAtomless_of_ext`**:
  with the tip statement UT, ⇒ UG ∧ UA.

The reductions are own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

variable {Ω : Type} [MeasurableSpace Ω]

/-- **UO, plus side** (open): windows `0 < u` of the time-`s` picture. -/
def UnifOffTipPlusStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ∀ u v : ℚ, (0 : ℝ) < u →
    ∃ ν, IsVagueLimitOnR (Ioo (u : ℝ) v) (bdryApprox (Real.sqrt κ) (h0f κ s B X ω)) ν ∧
      ∀ x, ν {x} = 0

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

theorem restrict_singleton_eq_zero {ν : Measure ℝ} (hat : ∀ x, ν {x} = 0) (S : Set ℝ) (x : ℝ) :
    ν.restrict S {x} = 0 :=
  nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (hat x).le)

/-- **UO, minus side**, from AC-fam-ext. -/
theorem ae_offTip_minus (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtStmt κ T P B X) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ∀ u v : ℚ, (v : ℝ) < 0 →
      ∃ ν, IsVagueLimitOnR (Ioo (u : ℝ) v) (bdryApprox (Real.sqrt κ) (h0f κ s B X ω)) ν ∧
        ∀ x, ν {x} = 0 := by
  filter_upwards [ae_anchor_ext hκ hκ4 hT hB hX hind hF, ae_zero_time_atomless hκ hκ4 hB hX,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB,
    ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le P B hB,
    hB.eval_zero_ae_eq_zero]
    with ω hA h0 hzm hcont hK hKs hB0 s hs u v hv
  rcases hs.1.eq_or_lt with hs0 | hs0
  · -- time `0`: the fixed-time global atomless limit
    subst hs0
    obtain ⟨ν, hν, hat⟩ := h0
    exact ⟨ν.restrict (Ioo (u : ℝ) v), InfMass.isVagueLimitOnR_restrict hν isOpen_Ioo,
      restrict_singleton_eq_zero hat _⟩
  obtain ⟨-, -, -, hzc, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hWc : Continuous (drive κ B ω) := drive_continuous hcont
  have hVc : Continuous V := continuous_vrev hWc T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set t := T - s with htdef
  have ht : 0 ≤ t := by rw [htdef]; linarith [hs.2]
  set F := realRevMap V t with hFdef
  -- `F → 0` at `0₋(t)⁻`
  obtain ⟨-, -, -, hC⟩ := realRevMap_endpoints hVc hV0 hT hK (continuous_vrev hWc s)
    (vrev_zero hs0.le) hs0 (hKs s hs0) ht (by rw [htdef]; ring)
    (fun r hr => (vrev_shift hs0.le hs.2 hr).symm)
  set c := zeroMinus V t with hcdef
  obtain ⟨l, hlc, hl⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hC.eventually (lt_mem_nhds hv))
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show l < c from hlc)
  have hFb : (v : ℝ) < F b := hl ⟨hb1, hb2⟩
  -- `F → −∞` at `−∞`
  obtain ⟨m, hm⟩ := eventually_atBot.1 ((CaraR.tendsto_realRevMap_atBot hVc ht).eventually
    (eventually_lt_atBot (u : ℝ)))
  obtain ⟨a, ha⟩ := exists_rat_lt (min m (b : ℝ))
  have hab : (a : ℝ) < b := ha.trans_le (min_le_right _ _)
  have hFa : F a < u := hm a (ha.trans_le (min_le_left _ _)).le
  -- a rational anchor `q ∈ [0,s)` at which `(a,b)` is still live
  have htm : t ∈ Icc 0 T := ⟨ht, by rw [htdef]; linarith⟩
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hzc t htm) (c - b) (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self s hδ) hs0)
  have hq0 : (0 : ℝ) ≤ q := ((le_max_right _ _).trans_lt hq1).le
  have hbq : (b : ℝ) < zeroMinus V (T - q) := by
    have hmem : T - q ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith⟩
    have hd : dist (T - q) t < δ := by
      rw [Real.dist_eq, abs_lt, htdef]
      constructor <;> linarith [(le_max_left _ _).trans_lt hq1]
    have := hδc hmem hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  obtain ⟨μ, hμ, hat⟩ := hA q a b hq0 (hq2.trans_le hs.2) hab hbq s ⟨hq2.le, hs.2⟩
  have hsub : Ioo (u : ℝ) v ⊆ Ioo (F a) (F b) := fun x hx =>
    ⟨hFa.trans hx.1, hx.2.trans hFb⟩
  exact ⟨μ.restrict (Ioo (u : ℝ) v), isVagueLimitOnR_restrict_open hμ isOpen_Ioo hsub,
    restrict_singleton_eq_zero hat _⟩

/-- **UO from AC-fam-ext and the plus side.** -/
theorem unifOffTipStmt_of_ext (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamExtStmt κ T P B X) (hP : UnifOffTipPlusStmt κ T P B X) :
    UnifOffTipStmt κ T P B X := by
  filter_upwards [ae_offTip_minus hκ hκ4 hT hB hX hind hF, hP] with ω hm hp s hs u v h0
  by_cases hv : (v : ℝ) < 0
  · exact hm s hs u v hv
  by_cases hu : (0 : ℝ) < u
  · exact hp s hs u v hu
  -- the remaining windows are empty
  have hvu : (v : ℝ) < u := by
    by_contra h
    exact h0 ⟨not_lt.1 hu, not_lt.1 hv⟩
  obtain ⟨μ, hμ, hat⟩ := hm s hs (-2) (-1) (by norm_num)
  have he : Ioo (u : ℝ) v = ∅ := Ioo_eq_empty (not_lt.2 hvu.le)
  exact ⟨μ.restrict (Ioo (u : ℝ) v), isVagueLimitOnR_restrict_open hμ isOpen_Ioo
    (by rw [he]; exact empty_subset _), restrict_singleton_eq_zero hat _⟩

end RegUnif
end QuantumZipper
