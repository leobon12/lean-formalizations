/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlFam
import InteractingSLE.Spec.Supplement.GW2SgDec
import InteractingSLE.Spec.Supplement.GW2SkRec
import InteractingSLE.Spec.Supplement.GW2Root2Cap
import InteractingSLE.WangWu.Defs

/-!
# Decision D26: the candidate's zero lifetime is the bad launch point

Packet PROVE-GW2-RELDET (round 25, decision D26). The candidate dies at its launch (`ζ = 0`) exactly when its launch
point `0` lies in the bad set of its canonical launch word, almost surely on the history's success.

* `flowLineXR_nonneg`, `flowLineXL_nonpos`: the marks of a flow-line word from `0` lie on their own side of `0`;
* **`threshold_seed_iff_isBadPoint`**: the seed of the flow-line word is a continuation-threshold state iff `0` is a
  bad point of the word (NOJUMP's `SB.Vq.IsBadPoint`);
* **`zero_mem_closure_badSet_iff`**: `0` lies in the closure of the bad set iff it is a bad point;
* **`badDist_zero_eq_zero_iff`**: the launch distance at `0` (`badDist … w 0`) vanishes iff the seed is a threshold
  state;
* **`ae_ae_life_zero_iff`**, **`ae_life_zero_iff`**: under the conditional law of the past, then almost surely, on
  the history's success: `ζ = 0 ↔ badDist κ θ (candWord ω) 0 = 0`. The direction `⇐` is
  `IsIntegratedSLEPath.lifetime_eq_zero_of_threshold` (`ae_lifetime_eq_zero_of_threshold`); the direction `⇒` (its
  converse, the fact D26 asks for: a launch point that is not bad gives `ζ > 0`) is the path clause
  `threshold_of_eq_zero` of the frozen `IsIntegratedSLEPath`;
* **`ae_life_pos_of_launch_good`**: the D26 fact in the form `badDist … ≠ 0 → 0 < ζ`;
* `launchWordRec`, `launchBadRec`: the canonical launch word and the zero-lifetime event read off a STAGE RECORD
  (`augRec (stageEncRec c r l) y`, any second component `y`); **`launchWordRec_augRec`**, **`ae_mem_launchBadRec_iff`**:
  on the history's success the stage record is in `launchBadRec` iff `ζ = 0`, almost surely; and with the time-order
  guard, iff the launch gauge's start distance (`launchStart`, read from (record, relative path)) is `0`
  (`ae_launchStart_eq_zero_iff`), and then the launch gauge's life is `⊤` (`ae_schedLaunchLife_eq_top_of_zero`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513Schedule
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### The seed of a flow-line word -/

section Seed

theorem flowLineXR_nonneg (b : ℝ → ℝ) (J : Finset ℝ) (j : Fin (flowLineNR b J 0)) : 0 ≤ flowLineXR b J 0 j := by
  induction j using Fin.cases with
  | zero => exact le_of_eq (Fin.cons_zero (α := fun _ => ℝ) 0 _).symm
  | succ i =>
    have hmem := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (0 < ·)) rfl i
    have hpos : 0 < ((jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl i := (Finset.mem_filter.1 hmem).2
    have e : flowLineXR b J 0 i.succ = ((jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl i - 0 := rfl
    rw [e, sub_zero]
    exact hpos.le

theorem flowLineXL_nonpos (b : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL b J 0)) : flowLineXL b J 0 i ≤ 0 := by
  induction i using Fin.cases with
  | zero => exact le_of_eq (Fin.cons_zero (α := fun _ => ℝ) 0 _)
  | succ k =>
    have hmem := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (· < 0)) rfl (Fin.rev k)
    have hneg : ((jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev k) < 0 := (Finset.mem_filter.1 hmem).2
    have e : flowLineXL b J 0 k.succ = ((jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev k) - 0 := rfl
    rw [e, sub_zero]
    exact hneg.le

/-- **The seed of a flow-line word is a threshold state iff `0` is a bad point.** -/
theorem threshold_seed_iff_isBadPoint (κ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (θ : ℝ) :
    ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 (flowLineXL b J 0)
        (flowLineXR b J 0) ↔
      SB.Vq.IsBadPoint (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0 := by
  have hR : SB.Vq.wR (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ) 0 =
      ∑ j ∈ Finset.univ.filter (fun j => flowLineXR b J 0 j = 0), flowLineRhoR κ b J 0 θ j := by
    unfold SB.Vq.wR
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun _ _ => rfl
    exact ⟨fun h => le_antisymm h (flowLineXR_nonneg b J j), fun h => h.le⟩
  have hL : SB.Vq.wL (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ) 0 =
      ∑ i ∈ Finset.univ.filter (fun i => flowLineXL b J 0 i = 0), flowLineRhoL κ b J 0 θ i := by
    unfold SB.Vq.wL
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    exact ⟨fun h => le_antisymm (flowLineXL_nonpos b J i) h, fun h => h.ge⟩
  unfold ForceWord.ThresholdCondition SB.Vq.IsBadPoint
  simp only [Complex.zero_re, Complex.zero_im, le_refl, true_and]
  rw [hR, hL]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- **`0` is in the closure of the bad set of a flow-line word iff it is a bad point.** -/
theorem zero_mem_closure_badSet_iff {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ) :
    (0 : ℂ) ∈ closure (SB.Vr.badSet (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ)) ↔
      SB.Vq.IsBadPoint (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
        (flowLineRhoR κ b J 0 θ) 0 := by
  refine ⟨fun h => ?_, fun h => subset_closure h⟩
  rw [closure_badSet_flowLine hκ hb θ, mem_badSetC_iff, Complex.zero_re] at h
  obtain ⟨-, h0⟩ := h
  rw [badPreB, closure_union] at h0
  rcases h0 with hr | hl
  · -- bad points just right of `0`
    have hfr : ∃ᶠ y in 𝓝[>] (0 : ℝ), 0 < y ∧ Sec4.cumWeightRight κ (rightLim b y + θ * chiC κ) ≤ -2 :=
      frequently_nhdsWithin_iff.2 ((mem_closure_iff_frequently.1 hr).mono fun y hy => ⟨hy, hy.1⟩)
    obtain ⟨y, ⟨hy0, hy⟩, hwy⟩ := (hfr.and_eventually
      (eventually_wR_eq (flowLineXR b J 0) (flowLineRhoR κ b J 0 θ))).exists
    refine ⟨Complex.zero_im, Or.inl ⟨by rw [Complex.zero_re], ?_⟩⟩
    rw [Complex.zero_re, ← hwy, wR_eq_cumWeightRight hκ hb θ hy0]
    exact hy
  · -- bad points just left of `0`
    have hfl : ∃ᶠ y in 𝓝[<] (0 : ℝ), y < 0 ∧ Sec4.cumWeightLeft κ (leftLim b y + θ * chiC κ) ≤ -2 :=
      frequently_nhdsWithin_iff.2 ((mem_closure_iff_frequently.1 hl).mono fun y hy => ⟨hy, hy.1⟩)
    obtain ⟨y, ⟨hy0, hy⟩, hwy⟩ := (hfl.and_eventually
      (eventually_wL_eq (flowLineXL b J 0) (flowLineRhoL κ b J 0 θ))).exists
    refine ⟨Complex.zero_im, Or.inr ⟨by rw [Complex.zero_re], ?_⟩⟩
    rw [Complex.zero_re, ← hwy, wL_eq_cumWeightLeft hκ hb θ hy0]
    exact hy

/-- **The launch distance at `0` vanishes iff the seed of the flow-line word is a threshold state.** -/
theorem badDist_zero_eq_zero_iff {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) (w : BoundaryWord) :
    badDist κ θ w 0 = 0 ↔ ForceWord.ThresholdCondition (flowLineRhoL κ w.fn w.jumps 0 θ)
      (flowLineRhoR κ w.fn w.jumps 0 θ) 0 (flowLineXL w.fn w.jumps 0) (flowLineXR w.fn w.jumps 0) := by
  rw [badDist_eq_zero_iff, ← closure_badSet_flowLine hκ w.isPiecewiseConstantBoundaryData θ,
    zero_mem_closure_badSet_iff hκ w.isPiecewiseConstantBoundaryData θ, threshold_seed_iff_isBadPoint]

/-- **The lifetime of a path vanishes iff its seed is a threshold state** (both clauses of the frozen
`IsIntegratedSLEPath`). -/
theorem IsIntegratedSLEPath.lifetime_eq_zero_iff {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    ζ = 0 ↔ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  refine ⟨fun hz => ?_, fun hth => WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hth⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h0, -⟩ := hp
  exact h0 hz

end Seed

/-! ### The zero lifetime under the conditional law, then almost surely -/

section Ae

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

omit [StandardBorelSpace Ω] in
theorem measurable_candWord : Measurable (candWord c r l a) := by
  have hCm : ∀ j, Measurable (GW2Olm.futFam c r l a j) := fun j =>
    measurable_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.hβA.1 c.hh.1 j
  have hpm := measurable_pastMap (κ := c.κ) runMeasStatement c.hb (GW2Olm.futSpec c r l a) (fun j _ => hCm j)
    (fun j _ => isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h j) (GW2Olm.curIdx c r l) le_rfl
  exact (measurable_pastWord c.βA c.c₀ _ _ c.hβA.1 _).comp hpm

include h13 in
/-- **Under the conditional law of the past**, on the history's success: the candidate's lifetime is `0` iff the
launch distance of its canonical word at `0` vanishes. -/
theorem ae_ae_life_zero_iff :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), oldSuccess c r l ω →
      (candLife c r l a ω = 0 ↔ badDist c.κ (candAngle c r l a) (candWord c r l a ω) 0 = 0) := by
  classical
  set spec := GW2Olm.futSpec c r l a with hspec
  set C := GW2Olm.futFam c r l a with hCdef
  set k := GW2Olm.curIdx c r l with hkdef
  have hCm : ∀ j, Measurable (C j) := fun j =>
    measurable_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec) spec.1 c.hβA.1 c.hh.1 j
  have hCreg : ∀ j ω, IsRegularDriver (C j ω) := fun j ω =>
    isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec) spec.1 c.h j ω
  have hpm : Measurable (pastMap c.κ c.b c.jumps spec C k) :=
    measurable_pastMap runMeasStatement c.hb spec (fun j _ => hCm j) (fun j _ => hCreg j) k le_rfl
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := by
    change pastSigma c.κ c.b c.jumps spec C k ≤ mΩ
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hlenL : (futureProgram c r l a).length = k + 1 := by
    simp only [hkdef, GW2Olm.curIdx, futureProgram, List.length_append, List.length_singleton]
  have hk : k < spec.2.2.length := by
    rw [hspec, GW2Olm.futSpec, GW2Schedule.length_scheduleProgram, hlenL]; omega
  have hprog := isFlowProg_spec (rootPt r.1) true (futureProgram c r l a)
  have hL := measurableSet_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl hprog
    (specDelta_ne_top _) C hk.le
  have : StandardBorelSpace (PastData k) := inferInstance
  have : MeasurableSpace.CountablySeparated (PastData k) := inferInstance
  have hatom0 := ae_ae_eq_of_comap (P := c.P) hpm
  rw [← pastSigma_eq_comap] at hatom0
  have hW := (canon_stageLaw c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec) h13 c.hβA c.hb
    c.hc₀J c.hc₀ c.hh (spec := spec) rfl hprog (specDelta_ne_top _) k).1
  filter_upwards [stageOK_canonWord c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec) h13 c.hβA
      c.hb c.hh rfl hprog (specDelta_ne_top _) hW,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := c.P) h𝒢 hL.compl, hatom0] with ω₀ hst hcompl hatom
  by_cases hA : AllSucc (specDelta spec) (fun j => C j ω₀) k
  · have hl := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl hprog
      (specDelta_ne_top _) (fun j => C j ω₀) hk).1 hA
    obtain ⟨h', -, hWd⟩ := hst _ _ hl
    obtain ⟨h'', 𝓕, VL, VR, B, -, hcpl⟩ := hWd
    filter_upwards [hcpl.1.2.2.2.2, hatom] with ω hp hpω _
    have hword : candWord c r l a ω = candWord c r l a ω₀ := by
      unfold candWord canonWord
      rw [hpω]
    rw [hword, badDist_zero_eq_zero_iff c.hκ]
    exact IsIntegratedSLEPath.lifetime_eq_zero_iff hp
  · filter_upwards [hcompl hA] with ω hω hold
    exact absurd (Gm.allSucc_future_of_oldSuccess c r l a ω hold) hω

include h13 in
/-- **The candidate's lifetime is `0` iff its launch point is bad**, almost surely on the history's success. -/
theorem ae_life_zero_iff :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω →
      (candLife c r l a ω = 0 ↔ badDist c.κ (candAngle c r l a) (candWord c r l a ω) 0 = 0) := by
  classical
  set spec := GW2Olm.futSpec c r l a with hspec
  set k := GW2Olm.curIdx c r l with hkdef
  have hCm : Measurable (GW2Olm.futFam c r l a k) :=
    measurable_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec) spec.1 c.hβA.1 c.hh.1 k
  have hζm : Measurable (candLife c r l a) := measurable_snd.comp hCm
  have hpm : Measurable (pastMap c.κ c.b c.jumps spec (GW2Olm.futFam c r l a) k) :=
    measurable_pastMap runMeasStatement c.hb spec
      (fun j _ => measurable_canonFam c.hκ c.h12p c.βA c.c₀ (specAngle spec) (specDelta spec) spec.1 c.hβA.1 c.hh.1 j)
      (fun j _ => isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h j) k le_rfl
  have h𝒢 : GW2Olm.pastG c r l a ≤ mΩ := by
    change pastSigma c.κ c.b c.jumps spec (GW2Olm.futFam c r l a) k ≤ mΩ
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  have hdm : Measurable fun ω => badDist c.κ (candAngle c r l a) (candWord c r l a ω) 0 :=
    measurable_badDist_comp c.κ _ (measurable_candWord c r l a) measurable_const
  have hO : MeasurableSet {ω | oldSuccess c r l ω} := measurableSet_oldSuccess c r l
  have hz : MeasurableSet {ω | candLife c r l a ω = 0} := hζm (measurableSet_singleton 0)
  have hd : MeasurableSet {ω | badDist c.κ (candAngle c r l a) (candWord c r l a ω) 0 = 0} :=
    hdm (measurableSet_singleton 0)
  have hker := ae_ae_life_zero_iff h13 c r l a
  have h1 : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → candLife c r l a ω = 0 →
      badDist c.κ (candAngle c r l a) (candWord c r l a ω) 0 = 0 := by
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 (measurableSet_imp_of hO (measurableSet_imp_of hz hd)) ?_
    filter_upwards [hker] with ω₀ hk0
    filter_upwards [hk0] with ω hω hold
    exact (hω hold).1
  have h2 : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → badDist c.κ (candAngle c r l a) (candWord c r l a ω) 0 = 0 →
      candLife c r l a ω = 0 := by
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 (measurableSet_imp_of hO (measurableSet_imp_of hd hz)) ?_
    filter_upwards [hker] with ω₀ hk0
    filter_upwards [hk0] with ω hω hold
    exact (hω hold).2
  filter_upwards [h1, h2] with ω h1 h2 hold
  exact ⟨h1 hold, h2 hold⟩

include h13 in
/-- **D26's fact: a launch point that is not bad gives a positive lifetime**, almost surely on the history's
success (the converse of `IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold` for the candidate). -/
theorem ae_life_pos_of_launch_good :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → badDist c.κ (candAngle c r l a) (candWord c r l a ω) 0 ≠ 0 →
      0 < candLife c r l a ω := by
  filter_upwards [ae_life_zero_iff h13 c r l a] with ω hω hold hne
  exact pos_iff_ne_zero.2 fun hz => hne ((hω hold).1 hz)

include h13 in
/-- **The launch gauge's start distance vanishes iff the candidate dies at its launch**, almost surely on the
history's success (time-ordered history). -/
theorem ae_launchStart_eq_zero_iff (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω →
      (launchStart c.κ (candAngle c r l a) (launchWordOf c r l a) (fun t => schedW c r l a t ω) = 0 ↔
        candLife c r l a ω = 0) := by
  filter_upwards [ae_life_zero_iff h13 c r l a, Gm.ae_futureJoined_trace h13 c r] with ω hω hP hold
  have hword : launchWordOf c r l a (fun t => schedW c r l a t ω) = candWord c r l a ω :=
    launchWordOf_schedW hord hold (hP l a hold).1
  unfold launchStart
  rw [hword]
  exact (hω hold).symm

include h13 in
/-- **At a zero lifetime the launch gauge's life is `⊤`** (almost surely on the history's success, time-ordered
history): the strict family `exists_schedVersionsA_strict_launch` then exhausts every relative clock value before the
first contact. -/
theorem ae_schedLaunchLife_eq_top_of_zero (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → candLife c r l a ω = 0 → schedLaunchLife c r l a ω = ⊤ := by
  classical
  filter_upwards [ae_launchStart_eq_zero_iff h13 c r l a hord] with ω hω hold hz
  have h0 := (hω hold).2 hz
  unfold schedLaunchLife launchLife
  exact ite_eq_right_of_eq_false _ _ (eq_false fun h => h.1 h0)

end Ae

/-! ### The zero lifetime read off the stage record -/

section Rec

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

theorem length_historyProgram : (historyProgram c r l).length = (entryList l).length + 1 := by
  simp only [historyProgram, schedOf, List.length_cons, List.length_reverse]

/-- **The canonical launch word read off a stage record** (the stopped history records of its first component). -/
def launchWordRec (z : RecData) : BoundaryWord :=
  pastWord c.βA c.c₀ (rootPt r.1) (specAngle (GW2Olm.futSpec c r l a)) (GW2Olm.curIdx c r l)
    (fun i => stgPastDec ((entryList l).length + 1) (pairEnc.symm z).1 (Fin.cast (length_historyProgram c r l) i))

/-- **The zero-lifetime event read off a stage record**: the launch point is in the bad set of its launch word. -/
def launchBadRec : Set RecData :=
  {z | badDist c.κ (candAngle c r l a) (launchWordRec c r l a z) 0 = 0}

theorem measurable_launchWordRec : Measurable (launchWordRec c r l a) := by
  refine (measurable_pastWord c.βA c.c₀ _ _ c.hβA.1 _).comp ?_
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_pi_apply _).comp ((measurable_stgPastDec _).comp (measurable_fst.comp pairEnc.symm.measurable))

theorem measurableSet_launchBadRec : MeasurableSet (launchBadRec c r l a) :=
  (measurable_badDist_comp c.κ _ (measurable_launchWordRec c r l a) measurable_const) (measurableSet_singleton 0)

variable {c r l a}

/-- **On the history's success the word read off any stage record of the history is the canonical launch word.** -/
theorem launchWordRec_augRec {ω : Ω} (hold : oldSuccess c r l ω) (y : Ω → RecData) :
    launchWordRec c r l a (augRec (stageEncRec c r l) y ω) = candWord c r l a ω := by
  have hs := Gm.allSucc_future_of_oldSuccess c r l a ω hold
  have hlen : GW2Olm.curIdx c r l ≤ (GW2Olm.futSpec c r l a).2.2.length := by
    rw [GW2Olm.futSpec, GW2Schedule.length_scheduleProgram]
    simp only [GW2Olm.curIdx, futureProgram, List.length_append, List.length_singleton]
    omega
  unfold launchWordRec candWord canonWord
  congr 1
  rw [pastMap_of_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec (rootPt r.1) true _)
    (specDelta_ne_top _) (GW2Olm.futFam c r l a) hlen hs]
  funext i
  simp only [augRec, MeasurableEquiv.symm_apply_apply, stgPastDec_stageEncRec]
  have hi : (i : ℕ) < (historyProgram c r l).length := i.2
  have h := stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h (rootPt r.1)
    ((candidateAngle c r a : ℝ), historyTime c r l + candidateCap c r a) hi ω
  exact h.symm

variable (c r l a)

/-- **The stage record is in `launchBadRec` iff the candidate dies at its launch**, almost surely on the history's
success, for every second component of the stage record. -/
theorem ae_mem_launchBadRec_iff [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u}) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → ∀ y : Ω → RecData,
      (augRec (stageEncRec c r l) y ω ∈ launchBadRec c r l a ↔ candLife c r l a ω = 0) := by
  filter_upwards [ae_life_zero_iff h13 c r l a] with ω hω hold y
  change badDist c.κ (candAngle c r l a) (launchWordRec c r l a (augRec (stageEncRec c r l) y ω)) 0 = 0 ↔ _
  rw [launchWordRec_augRec hold y]
  exact (hω hold).symm

end Rec

end InteractingSLE.Theorem14.GW2Rd
