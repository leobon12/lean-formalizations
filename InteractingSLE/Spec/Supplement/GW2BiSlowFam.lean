/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BiSlowStop

/-!
# Decision D3's slow stage stops and slow variables on a version family (S1, S3; root `0`)

Packet PROVE-GW2-BUF (round 6). For a family `(R n, V n)` of announced GB6 versions of the schedule instance with
monotone finite caps, the slow stage variable `n` is SDE's corrected schedule instance on version `n + 1` with the
lower cap `V n` as its stop (`GW2Bh.lowCapStop`). Writing `slowStageVar` for it:

* **`lowCapStop_good_family`**: the stop is `StageStop.Good` for every `n`, given strict caps on the record event
  (`hstrict`). Strictness is a property of the family, the request to RELDET recorded in the handoff;
* **`ae_slowStageVar_stop_eq`**: on live samples, the stop is `V n − rootHistCap` when `rootHistCap < V (n+1)`, and
  `0` otherwise;
* **`vDriverIdN_slowStageVar`** and **`vStopCoversN_slowStageVar`**: SDE's `VDriverIdN` (every `n`) and `VStopCoversN`
  for any version-indexed package whose slow variable `n` is `slowStageVar n`. `VStopCoversN` needs coverage of the
  gain eventually in `n` (RELDET's family: `exists_schedVersions_slowFacts`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv GW2Sde GW2Sdi GW2Sdx GW2Rd GW2TipSystem
  GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

section Family

variable (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞}
  (hA : ∀ n, Supp8.Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n))
  (ch : ℕ → GW2Sdh.SchedChoice Ω)

/-- The slow instance of version `n + 1`. -/
abbrev slowInst (n : ℕ) : StageInst Ω := schedInstS c r l a (GW2Sdh.schedGT h13 c r l a) (hA (n + 1)) (ch n)

/-- **Decision D3's slow stage stop `n`**: the cap `V n` on the instance of version `n + 1`. -/
abbrev slowCapStop (n : ℕ) : StageStop Ω :=
  lowCapStop c l (slowInst h13 c r l a hA ch n) (V n) (hA n).1.2.choose

/-- **Decision D3's slow stage variable `n`.** -/
abbrev slowStageVar (n : ℕ) : StageVar Ω :=
  (slowInst h13 c r l a hA ch n).var c r l (slowCapStop h13 c r l a hA ch n)

/-- **The slow stage stops are good** (strict caps on the record event). -/
theorem lowCapStop_good_family (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω) (hfin : ∀ n ω, V n ω ≠ ⊤)
    (hstrict : ∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < V (n + 1) ω)
    (hI : ∀ n, (slowInst h13 c r l a hA ch n).Good c r l) (n : ℕ) :
    (slowCapStop h13 c r l a hA ch n).Good (slowInst h13 c r l a hA ch n) c r l := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hW : ∀ᵐ ω ∂c.P, Continuous (schedW c r l a · ω) ∧ schedW c r l a 0 ω = 0 ∧
      IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  obtain ⟨hρm, hρ, -⟩ := (hA n).1.2.choose_spec
  have hrule := ae_lowCap_rule_eq hfl hα hW (hA n).1 (hA (n + 1)).1.1 (ae_of_all _ (hmono n))
  refine lowCapStop_good (hI n) hρm hρ (hA n).1.1.2.2.2.2.1 (hfin (n + 1)) ?_ (ae_of_all _ (hmono n)) ?_
  · filter_upwards [hrule, ae_gb6RecGood hfl hα c.s] with ω hω hgood hm
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hgood).2 hm
    exact hω hs hsH
  · filter_upwards [hstrict] with ω hω hm
    exact hω hm n

/-- **The slow stop on live samples.** -/
theorem ae_slowStageVar_stop_eq (hroot : rootPt r.1 = 0) (n : ℕ) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V (n + 1) ξ →
      (slowStageVar h13 c r l a hA ch n).stop ξ = V n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
  classical
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  filter_upwards [ae_exactPair_root0 h13 c r l a hroot, ae_gb6RecGood hfl hα c.s,
    ae_stgStart_eq_histCap h13 c r l a hroot (V (n + 1))] with ξ hpair hgood hst hlive hV
  obtain ⟨hsζ, hsH, -, -, -⟩ := hpair hlive
  have hm : gb6Rec c.s c.W c.ζ ξ ∈ gb6TS c.s := (mem_gb6TS_iff hgood).1 ⟨hsζ, hsH⟩
  change (if gb6Rec c.s c.W c.ζ ξ ∈ gb6TS c.s then V n ξ - (stgStart c.s (schedW c r l a) c.W c.ζ
    (GW2Sdh.schedGT h13 c r l a) (V (n + 1)) (RootJ31.historyTime c r l) ξ : ℝ≥0∞) else 0) = _
  simp only [hm, ↓reduceIte]
  rw [hst hlive hV]

omit hA ch in
/-- **The physical clock at the history time is the history's capacity** (root `0`, live samples, RELDET's good
set). -/
theorem ae_physClock_eq_histCap (hroot : rootPt r.1 = 0) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      Supp8.RelSafe.physClock c.s (schedW c r l a) c.W c.ζ (GW2Sdh.schedGT h13 c r l a) (RootJ31.historyTime c r l) ξ =
        ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨hgood, -, hGT⟩ := GW2Sdh.schedGT_spec h13 c r l a
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  filter_upwards [ae_exactPair_root0 h13 c r l a hroot, hGT, ae_gb6RecGood hfl hα c.s]
    with ξ hpair hGTξ hrec hlive
  obtain ⟨hsζ, hsH, hTc, -, hK⟩ := hpair hlive
  have hm : gb6Rec c.s c.W c.ζ ξ ∈ gb6TS c.s := (mem_gb6TS_iff hrec).1 ⟨hsζ, hsH⟩
  have hξ : ξ ∈ GW2Sdh.schedGT h13 c r l a := hGTξ.2 hm
  have hT : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ξ :=
    (ENNReal.coe_le_coe.2 le_self_add).trans_lt hTc
  rw [Supp8.RelSafe.physClock_eq_gb6Clock hgood hξ hT]
  unfold GW2Sdg.rootHistCap GW2Sdg.rootCapAt
  rw [GW2Bf.forwardCapacity_future_eq_exact c r l a ξ le_self_add, (hK _ le_self_add).2]
  rfl

/-- **SDE's `VDriverIdN` for the slow stage variables.** -/
theorem vDriverIdN_slowStageVar (hroot : rootPt r.1 = 0) (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    (hfin : ∀ n ω, V n ω ≠ ⊤) {Vp : VPkgXFamily.{u}} (n : ℕ)
    (hvar : (Vp Ω c r).slowVar l a n = slowStageVar h13 c r l a hA ch n) :
    VDriverIdN Vp Ω c r l a n := by
  classical
  refine vDriverIdN_of_schedInstS h13 c r l a n hroot (hA (n + 1)) (ch n) (fun u ξ => by rw [hvar]; rfl) ?_
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  filter_upwards [ae_slowStageVar_stop_eq h13 c r l a hA ch hroot n, ae_exactPair_root0 h13 c r l a hroot,
    ae_gb6RecGood hfl hα c.s, ae_physClock_eq_histCap h13 c r l a hroot] with ξ hstop hpair hgood hcl u hu hlt
  rw [hvar] at hlt
  have hgain : 0 < GW2Sdg.rootGain c r l a ξ := lt_of_le_of_lt zero_le hu
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
    rw [GW2Sdg.sourceSample_fst]
    exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hgain.ne')
  by_cases hV : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V (n + 1) ξ
  · rw [hstop hlive hV] at hlt
    exact hlt.trans_le (tsub_le_tsub_right (hmono n ξ) _)
  · -- the history's capacity is past the next cap: the stop is `0`
    exfalso
    obtain ⟨hsζ, hsH, -, -, -⟩ := hpair hlive
    have hm : gb6Rec c.s c.W c.ζ ξ ∈ gb6TS c.s := (mem_gb6TS_iff hgood).1 ⟨hsζ, hsH⟩
    have h0 : (slowStageVar h13 c r l a hA ch n).stop ξ = 0 := by
      change (if gb6Rec c.s c.W c.ζ ξ ∈ gb6TS c.s then V n ξ - (stgStart c.s (schedW c r l a) c.W c.ζ
        (GW2Sdh.schedGT h13 c r l a) (V (n + 1)) (RootJ31.historyTime c r l) ξ : ℝ≥0∞) else 0) = 0
      simp only [hm, ↓reduceIte]
      refine tsub_eq_zero_of_le ?_
      have hfin' : stgStartM c.s (schedW c r l a) c.W c.ζ (GW2Sdh.schedGT h13 c r l a) (V (n + 1))
          (RootJ31.historyTime c r l) ξ ≠ ⊤ := ne_top_of_le_ne_top (hfin (n + 1) ξ) (min_le_right _ _)
      change V n ξ ≤ ((stgStartM c.s (schedW c r l a) c.W c.ζ (GW2Sdh.schedGT h13 c r l a) (V (n + 1))
        (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞)
      rw [ENNReal.coe_toNNReal hfin']
      change V n ξ ≤ min (Supp8.RelSafe.physClock c.s (schedW c r l a) c.W c.ζ (GW2Sdh.schedGT h13 c r l a)
        (RootJ31.historyTime c r l) ξ) (V (n + 1) ξ)
      rw [hcl hlive, min_eq_right (not_lt.1 hV)]
      exact hmono n ξ
    rw [h0] at hlt
    exact (not_lt.2 zero_le) hlt

/-- **SDE's `VStopCoversN` for the slow stage variables**, from coverage of the gain eventually in `n`. -/
theorem vStopCoversN_slowStageVar (hroot : rootPt r.1 = 0) (hmono : ∀ n ω, V n ω ≤ V (n + 1) ω)
    {Vp : VPkgXFamily.{u}} (hvar : ∀ n, (Vp Ω c r).slowVar l a n = slowStageVar h13 c r l a hA ch n)
    (hcov : ∀ᵐ ξ ∂c.P, ∀ᶠ n in atTop,
      (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) ≤ V n ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞)) :
    VStopCoversN Vp Ω c r l a := by
  filter_upwards [hcov, ae_all_iff.2 fun n => ae_slowStageVar_stop_eq h13 c r l a hA ch hroot n]
    with ξ hcovξ hstopξ _
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ GW2Sdg.rootGain c r l a ξ) with h0 | hpos
  · refine Eventually.of_forall fun n => ?_
    rw [← h0, ENNReal.coe_zero]
    exact zero_le
  · have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
      rw [GW2Sdg.sourceSample_fst]
      exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) (ENNReal.coe_ne_zero.2 hpos.ne')
    filter_upwards [hcovξ] with n hn
    have hlt : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < V n ξ :=
      tsub_pos_iff_lt.1 ((ENNReal.coe_pos.2 hpos).trans_le hn)
    rw [hvar n, hstopξ n hlive (hlt.trans_le (hmono n ξ))]
    exact hn

end Family

/-- **Decision D3's slow facts for the slow stage variables on RELDET's monotone family** (root `0`): for any choices
and any version-indexed package whose slow variable `n` is `slowStageVar n`, `VDriverIdN` for every `n` and
`VStopCoversN`; and, given strict caps on the record event and good instances, every slow stop is good. -/
theorem exists_slowStageVars (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞)
      (hA : ∀ n, Supp8.Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)),
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ (ch : ℕ → GW2Sdh.SchedChoice Ω) {Vp : VPkgXFamily.{u}},
        (∀ n, (Vp Ω c r).slowVar l a n = slowStageVar h13 c r l a hA ch n) →
        (∀ n, VDriverIdN Vp Ω c r l a n) ∧ VStopCoversN Vp Ω c r l a ∧
        ((∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < V (n + 1) ω) →
          (∀ n, (slowInst h13 c r l a hA ch n).Good c r l) →
          ∀ n, (slowCapStop h13 c r l a hA ch n).Good (slowInst h13 c r l a hA ch n) c r l) := by
  obtain ⟨R, V, hA, hmono, hfin, hev⟩ := exists_schedVersionsA_mono h13 c r l a
  refine ⟨R, V, hA, hmono, hfin, fun ch Vp hvar => ⟨fun n => ?_, ?_, fun hstrict hI n => ?_⟩⟩
  · exact vDriverIdN_slowStageVar h13 c r l a hA ch hroot hmono hfin n (hvar n)
  · exact vStopCoversN_slowStageVar h13 c r l a hA ch hroot hmono hvar
      (ae_stopCovers_eventually h13 c r l a hroot hev)
  · exact lowCapStop_good_family h13 c r l a hA ch hmono hfin hstrict hI n

end InteractingSLE.Theorem14.GW2Bh
