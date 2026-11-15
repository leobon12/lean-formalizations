/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.FanTipFiber
import InteractingSLE.Spec.Sec6.Aux39Fresh
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Lemma R.1 after the repair: the active domain and fresh-tip uniqueness

Packet PROVE-R16. Supplement §5.2, **Lemma R.1** (`source/spec/p433-480.md` L939–L942, p. 472):

> The restriction `g_s|E` extends continuously and injectively to `Ē`. … If `p = η(s)` is an interior
> physical point, then `v_s(p) = W_s`.
>
> *Proof.* The whole open set `E` is disjoint from the full counterflow range. It is connected to the
> untouched original boundary arc incident to the original target `x`. Thus `E ⊂ D_s` … Aux. 30 now
> gives the asserted Jordan boundary embedding … At a current interior tip Aux. 136 says that this
> preimage is the unique active inverse preimage, namely `W_s`.

Ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` L297–L303) keeps from R.1 only the
exterior Jordan embedding (Aux. 30–31) and deletes the all-contact assertion; its fresh-contact
replacement is **Lemma 1.1** (fresh-tip uniqueness, L37–L61), used through Lemma 1.4
(`R2RefAttach.lean`).

Lemma 1.1 itself is PROVE-AUX36-41's `Sec6.fresh_tip_fibre` (`Spec/Sec6/Aux39Fresh.lean`, stated with
`trMap W 0 T`). This file restates it in the form of PROVE-SEC7-E's `Sec7.IsSingletonTipFiber` (the
singleton tip fibre (TS1)/(SF1) of Aux. 135–136, whose use R41 removes) with PROVE-YUAN-M1B's
`IsCutTime` hypothesis, and proves the first step of R.1.

## Main results

* `IsLoewnerTrace.subset_activeDomain_of_not_isBounded`: R.1's first step, `E ⊂ D_s`, with the target
  at `∞` of the Loewner chart;
* `IsLoewnerTrace.isSingletonTipFiber_of_isCutTime`: **Lemma 1.1** as a singleton tip fibre at every
  fresh interior tip;
* `IsLoewnerTrace.eq_zero_of_extendFrom_eq_of_isCutTime`: the endpoint form used by Lemma 1.4 ("its
  lifted incoming endpoint equals `W_a`").
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Lemma R.1, first step** (`source/spec/p433-480.md` L941: "The whole open set `E` is disjoint from
the full counterflow range. It is connected to the untouched original boundary arc incident to the
original target `x`. Thus `E ⊂ D_s`"). In the Loewner chart the target is `∞`: a preconnected unbounded
subset of `ℍ` disjoint from `η([0, s])` lies in the active domain `D_s = ℍ \ K_s`. -/
theorem IsLoewnerTrace.subset_activeDomain_of_not_isBounded (hη : IsLoewnerTrace W η) {s : ℝ}
    (hs : 0 ≤ s) {E : Set ℂ} (hE : IsPreconnected E) (hEu : ¬ Bornology.IsBounded E)
    (hEH : E ⊆ H) (hEη : Disjoint E (η '' Icc 0 s)) : E ⊆ H \ fwdHull W s := by
  rw [hη.2.2 s hs]
  exact HalfPlaneSep.subset_H_diff_fillH_of_not_isBounded (hη.isCompact_image s).isClosed hE hEu
    fun z hz => ⟨hEH hz, Set.disjoint_left.1 hEη hz⟩

/-- **Lemma 1.1 of the singleton-tip elimination note (fresh-tip uniqueness)**
(`ig1_ztip_elimination.txt` L37–L43, ruling R41), as a singleton tip fibre: at every positive time
`T` at which the continuous Loewner trace `η` visits an interior point for the first time,
`f_T⁻¹({η(T)}) ∩ ℝ = {W_T}`. A restatement of `Sec6.fresh_tip_fibre` (PROVE-AUX36-41). -/
theorem IsLoewnerTrace.isSingletonTipFiber_of_isCutTime (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (hcut : YuanSimpleApprox.IsCutTime η T) : Sec7.IsSingletonTipFiber W T := by
  intro v hv
  rw [hη.loewnerTip_eq hW hW0 hT.le] at hv
  exact Sec6.fresh_tip_fibre hη hW hW0 hT hcut.1 hcut.2
    (by rw [YuanSimpleApprox.trMap_zero_left hW0]; exact hv)

/-- **Lemma 1.1, endpoint form** (as used in Lemma 1.4: "Its incoming endpoint maps to the fresh
interior tip, so the deterministic fresh-tip lemma makes it `W_a`"): a real point `q` (centred
coordinate) whose boundary image under `F̄_T` is a freshly visited interior tip `η(T)` is the
driver, `q = 0`. -/
theorem IsLoewnerTrace.eq_zero_of_extendFrom_eq_of_isCutTime (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (hcut : YuanSimpleApprox.IsCutTime η T) {q : ℝ}
    (hq : extendFrom H (fwdMapInv W T) (q : ℂ) = η T) : q = 0 :=
  hη.isSingletonTipFiber_of_isCutTime hW hW0 hT hcut q (by rw [hq, hη.loewnerTip_eq hW hW0 hT.le])

end InteractingSLE
