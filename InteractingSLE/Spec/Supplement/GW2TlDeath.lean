/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlLaw
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# N4 item 1 in launch coordinates, part 7: the death is the first zero of the launch distance, almost surely

Packet PROVE-GW2-RELDET (decision D20). For the schedule instance, `candDist c r l a ω σ` is the distance of the
launch trace of the explored driver (`launchTr`) to the bad set of the launch word read off the explored driver
(`launchWordOf`), at the candidate's own time `σ`. On the history's success, for `P`-almost every sample with a
positive candidate lifetime `ζ`:

* it is positive at every own time `σ ≤ cap` before `ζ`;
* if `ζ ≤ cap`, it vanishes at `ζ`.

So the candidate's death is the first zero of `candDist` (**`ae_candDist`**). Proof: under the conditional law of the
past this is `ae_candidate_life_canonWord` (the read-off word is the canonical word, `launchWordOf_schedW`; the launch
trace is the candidate's trace, `shiftNN_schedW`); the statement is carried to `P` through countably many Borel events
(`ae_of_ae_condExpKernel`) and the continuity of `candDist`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513Schedule

section Defs

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The candidate's angle. -/
abbrev candAngle : ℝ := specAngle (GW2Olm.futSpec c r l a) (GW2Olm.curIdx c r l)

/-- The candidate's lifetime. -/
abbrev candLife (ω : Ω) : ℝ≥0∞ := (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2

/-- **The launch distance of the explored driver** at the candidate's own time `σ`. -/
abbrev candDist (ω : Ω) (σ : ℝ≥0) : ℝ :=
  launchDist c.κ (candAngle c r l a) (launchWordOf c r l a) (historyTime c r l) (fun t => schedW c r l a t ω) σ

theorem measurable_candDist (σ : ℝ≥0) : Measurable fun ω => candDist c r l a ω σ :=
  (measurable_launchDist (measurable_launchWordOf c r l a) σ).comp
    (measurable_pi_iff.2 fun t => measurable_schedW c r l a t)

end Defs

/-! ### One sample -/

/-- Two functions continuous from the left at a positive time and equal before it are equal at it. -/
theorem eq_of_eqOn_Iio {f g : ℝ≥0 → ℂ} {τ : ℝ≥0} (hτ : 0 < τ) (hf : ContinuousWithinAt f (Iio τ) τ)
    (hg : ContinuousWithinAt g (Iio τ) τ) (h : EqOn f g (Iio τ)) : f τ = g τ := by
  have : (𝓝[<] τ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hτ⟩
  exact tendsto_nhds_unique hf.tendsto (hg.tendsto.congr' (eventually_nhdsWithin_of_forall fun x hx => (h hx).symm))

section Sample

variable {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)} {a : ℕ} {ω : Ω}

/-- **One sample**: on the history's success, if the candidate's trace has D10's two properties against the bad set
of the canonical word, the launch distance read off the explored driver is positive before the death and zero at a
death before the cap. -/
theorem candDist_of_death (hord : TimeOrdered 0 (historyProgram c r l)) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace (fun t => schedW c r l a t ω) ⊤ γ)
    {w : BoundaryWord} (hw : launchWordOf c r l a (fun t => schedW c r l a t ω) = w)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun t => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t)
      (candLife c r l a ω) η)
    (hoff : ∀ t : ℝ≥0, (t : ℝ≥0∞) < candLife c r l a ω →
      η t ∉ closure (SB.Vr.badSet (flowLineXL w.fn w.jumps 0) (flowLineXR w.fn w.jumps 0)
        (flowLineRhoL c.κ w.fn w.jumps 0 (candAngle c r l a)) (flowLineRhoR c.κ w.fn w.jumps 0 (candAngle c r l a))))
    (hbad : candLife c r l a ω ≠ ⊤ → SB.Vq.IsBadPoint (flowLineXL w.fn w.jumps 0) (flowLineXR w.fn w.jumps 0)
        (flowLineRhoL c.κ w.fn w.jumps 0 (candAngle c r l a)) (flowLineRhoR c.κ w.fn w.jumps 0 (candAngle c r l a))
        (η (candLife c r l a ω).toNNReal))
    (hζ0 : 0 < candLife c r l a ω) :
    (∀ σ : ℝ≥0, σ ≤ candidateCap c r a → (σ : ℝ≥0∞) < candLife c r l a ω → 0 < candDist c r l a ω σ) ∧
      (candLife c r l a ω ≤ candidateCap c r a → candDist c r l a ω (candLife c r l a ω).toNNReal = 0) := by
  set W : ℝ≥0 → ℝ := fun t => schedW c r l a t ω with hWdef
  set D := GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω with hD
  set T := historyTime c r l with hT
  have hreg : IsRegularDriver D := isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h _ ω
  have hWc : Continuous W := continuous_schedW c r l a ω
  have hW0 : W 0 = 0 := schedW_zero c r l a ω
  have hbset : closure (SB.Vr.badSet (flowLineXL w.fn w.jumps 0) (flowLineXR w.fn w.jumps 0)
      (flowLineRhoL c.κ w.fn w.jumps 0 (candAngle c r l a)) (flowLineRhoR c.κ w.fn w.jumps 0 (candAngle c r l a))) =
      GW2Sdn.badSetC c.κ w.fn (candAngle c r l a) 0 :=
    closure_badSet_flowLine c.hκ w.isPiecewiseConstantBoundaryData _
  -- the launch trace is the candidate's trace before its cap and its lifetime
  have hagree : ∀ σ : ℝ≥0, σ ≤ candidateCap c r a → (σ : ℝ≥0∞) < candLife c r l a ω → launchTr T W σ = η σ := by
    intro σ hσc hσζ
    unfold launchTr
    rw [LP.traceAt_congr (w' := D.1) fun v hv => shiftNN_schedW hord hold hgood
      (le_min (ENNReal.coe_le_coe.2 (hv.trans hσc)) ((ENNReal.coe_le_coe.2 hv).trans hσζ.le))]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hreg.1 hreg.2.1 hσζ
  have hdist : ∀ σ : ℝ≥0, candDist c r l a ω σ = badDist c.κ (candAngle c r l a) w (launchTr T W σ) := by
    intro σ
    show badDist c.κ (candAngle c r l a) (launchWordOf c r l a W) (launchTr T W σ) = _
    rw [hw]
  refine ⟨fun σ hσc hσζ => ?_, fun hζc => ?_⟩
  · rw [hdist, hagree σ hσc hσζ, badDist_pos_iff, ← hbset]
    exact hoff σ hσζ
  · have hne : candLife c r l a ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hζc
    set ζ := (candLife c r l a ω).toNNReal with hζ
    have hζe : (ζ : ℝ≥0∞) = candLife c r l a ω := ENNReal.coe_toNNReal hne
    have hζpos : 0 < ζ := by
      rw [← ENNReal.coe_lt_coe, hζe]; exact hζ0
    have hζcap : ζ ≤ candidateCap c r a := by
      rw [← ENNReal.coe_le_coe, hζe]; exact hζc
    -- at the lifetime by continuity from the left
    have heq : launchTr T W ζ = η ζ := by
      refine eq_of_eqOn_Iio hζpos (continuous_launchTr hγ hWc hW0).continuousWithinAt ?_ fun σ hσ => ?_
      · refine (hη.2.1 ζ (show (ζ : ℝ≥0∞) ≤ candLife c r l a ω from hζe.le)).mono fun t ht => ?_
        show (t : ℝ≥0∞) ≤ candLife c r l a ω
        rw [← hζe]; exact ENNReal.coe_le_coe.2 (le_of_lt ht)
      · have hσζ : (σ : ℝ≥0∞) < candLife c r l a ω := by rw [← hζe]; exact ENNReal.coe_lt_coe.2 hσ
        exact hagree σ ((le_of_lt hσ).trans hζcap) hσζ
    rw [hdist, heq, badDist_eq_zero_iff, ← hbset]
    exact subset_closure (hbad hne)

end Sample

/-! ### Under the conditional law, then almost surely -/

section Ae

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **Under the conditional law of the past**, the launch distance read off the explored driver is positive before
the candidate's death and zero at a death before the cap. -/
theorem ae_ae_candDist (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), oldSuccess c r l ω →
      0 < candLife c r l a ω →
      (∀ σ : ℝ≥0, σ ≤ candidateCap c r a → (σ : ℝ≥0∞) < candLife c r l a ω → 0 < candDist c r l a ω σ) ∧
        (candLife c r l a ω ≤ candidateCap c r a → candDist c r l a ω (candLife c r l a ω).toNNReal = 0) := by
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
  have hP := Gm.ae_futureJoined_trace h13 c r
  have hR := ae_schedW_regular h13 c r l a
  filter_upwards [ae_candidate_life_canonWord h13 c r l a,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := c.P) h𝒢 hL.compl, hatom0,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := c.P) h𝒢 hP,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := c.P) h𝒢 hR] with ω₀ hdeath hcompl hatom hPk hRk
  by_cases hA : AllSucc (specDelta spec) (fun j => C j ω₀) k
  · have hl := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl hprog
      (specDelta_ne_top _) (fun j => C j ω₀) hk).1 hA
    filter_upwards [hdeath _ _ hl, hatom, hPk, hRk] with ω hη hpω hPω hRω hold hζ0
    obtain ⟨η, hη, hfacts⟩ := hη
    obtain ⟨hoff, hbad⟩ := hfacts hζ0
    have hgood := (hPω l a hold).1
    have hword : launchWordOf c r l a (fun t => schedW c r l a t ω) = candWord c r l a ω₀ := by
      rw [launchWordOf_schedW hord hold hgood]
      unfold canonWord
      rw [hpω]
      rfl
    exact candDist_of_death hord hold hgood hRω.2.2.1 hword hη hoff hbad hζ0
  · filter_upwards [hcompl hA] with ω hω hold
    exact absurd (Gm.allSucc_future_of_oldSuccess c r l a ω hold) hω

omit [StandardBorelSpace Ω] in
/-- An implication of measurable events is measurable. -/
theorem measurableSet_imp_of {p q : Ω → Prop} (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω}) :
    MeasurableSet {ω | p ω → q ω} := by
  have e : {ω | p ω → q ω} = {ω | p ω}ᶜ ∪ {ω | q ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [e]
  exact hp.compl.union hq

include h13 in
/-- **The candidate's death is the first zero of the launch distance, almost surely**: on the history's success, at
a positive lifetime, the launch distance read off the explored driver is positive at every own time `≤ cap` before
the death and vanishes at a death before the cap. -/
theorem ae_candDist (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω →
      (∀ σ : ℝ≥0, σ ≤ candidateCap c r a → (σ : ℝ≥0∞) < candLife c r l a ω → 0 < candDist c r l a ω σ) ∧
        (candLife c r l a ω ≤ candidateCap c r a → candDist c r l a ω (candLife c r l a ω).toNNReal = 0) := by
  classical
  set spec := GW2Olm.futSpec c r l a with hspec
  set k := GW2Olm.curIdx c r l with hkdef
  set cap := candidateCap c r a with hcap
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
  have hFm : ∀ σ, Measurable fun ω => candDist c r l a ω σ := measurable_candDist c r l a
  have hO : MeasurableSet {ω | oldSuccess c r l ω} := measurableSet_oldSuccess c r l
  have hpos : MeasurableSet {ω | 0 < candLife c r l a ω} := measurableSet_lt measurable_const hζm
  -- the continuity of the launch distance, almost surely
  have hcont : ∀ᵐ ω ∂c.P, Continuous fun σ => candDist c r l a ω σ := by
    filter_upwards [ae_schedW_regular h13 c r l a] with ω hω
    exact continuous_launchDist hω.2.2.1 hω.1 hω.2.1
  have hker := ae_ae_candDist h13 c r l a hord
  have hcontK := Sec7.Aux122Disint.ae_ae_condExpKernel (P := c.P) h𝒢 hcont
  -- (1) a positive infimum over the rational times up to `s`
  have hE2 : ∀ s : ℚ≥0, ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω → (s : ℝ≥0) ≤ cap →
      ((s : ℝ≥0) : ℝ≥0∞) < candLife c r l a ω →
      0 < ⨅ q : ℚ≥0, (if (q : ℝ≥0) ≤ (s : ℝ≥0) then candDist c r l a ω q else 1) := by
    intro s
    have hm : MeasurableSet {ω | oldSuccess c r l ω → 0 < candLife c r l a ω → (s : ℝ≥0) ≤ cap →
        ((s : ℝ≥0) : ℝ≥0∞) < candLife c r l a ω →
        0 < ⨅ q : ℚ≥0, (if (q : ℝ≥0) ≤ (s : ℝ≥0) then candDist c r l a ω q else 1)} := by
      refine measurableSet_imp_of hO (measurableSet_imp_of hpos (measurableSet_imp_of (MeasurableSet.const _)
        (measurableSet_imp_of (measurableSet_lt measurable_const hζm) (measurableSet_lt measurable_const ?_))))
      exact Measurable.iInf fun q => Measurable.ite (MeasurableSet.const _) (hFm _) measurable_const
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hm ?_
    filter_upwards [hker, hcontK] with ω₀ hk0 hc0
    filter_upwards [hk0, hc0] with ω hω hcω hold hζ0 hsc hsζ
    obtain ⟨h1, -⟩ := hω hold hζ0
    -- the launch distance is positive on the compact `[0, s]`
    obtain ⟨σ₀, hσ₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le (a := (s : ℝ≥0))))
      hcω.continuousOn
    have hle : ∀ σ ∈ Icc (0 : ℝ≥0) s, σ ≤ cap ∧ (σ : ℝ≥0∞) < candLife c r l a ω := fun σ hσ =>
      ⟨hσ.2.trans hsc, (ENNReal.coe_le_coe.2 hσ.2).trans_lt hsζ⟩
    have hm0 : 0 < candDist c r l a ω σ₀ := h1 σ₀ (hle σ₀ hσ₀).1 (hle σ₀ hσ₀).2
    refine lt_of_lt_of_le (lt_min hm0 one_pos) (le_ciInf fun q => ?_)
    split_ifs with hq
    · exact (min_le_left _ _).trans (hmin ⟨zero_le, hq⟩)
    · exact min_le_right _ _
  -- (2) the cap itself
  have hE2c : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω → (cap : ℝ≥0∞) < candLife c r l a ω →
      0 < candDist c r l a ω cap := by
    have hm : MeasurableSet {ω | oldSuccess c r l ω → 0 < candLife c r l a ω → (cap : ℝ≥0∞) < candLife c r l a ω →
        0 < candDist c r l a ω cap} :=
      measurableSet_imp_of hO (measurableSet_imp_of hpos (measurableSet_imp_of
        (measurableSet_lt measurable_const hζm) (measurableSet_lt measurable_const (hFm _))))
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hm ?_
    filter_upwards [hker] with ω₀ hk0
    filter_upwards [hk0] with ω hω hold hζ0 hcζ
    exact (hω hold hζ0).1 cap le_rfl hcζ
  -- (3) the death before the cap
  have hE3 : ∀ᵐ ω ∂c.P, oldSuccess c r l ω → 0 < candLife c r l a ω → candLife c r l a ω ≤ cap →
      evalDn (fun σ => candDist c r l a ω σ) (candLife c r l a ω).toNNReal = 0 := by
    have hm : MeasurableSet {ω | oldSuccess c r l ω → 0 < candLife c r l a ω → candLife c r l a ω ≤ cap →
        evalDn (fun σ => candDist c r l a ω σ) (candLife c r l a ω).toNNReal = 0} := by
      refine measurableSet_imp_of hO (measurableSet_imp_of hpos (measurableSet_imp_of
        (measurableSet_le hζm measurable_const) ?_))
      exact (measurable_evalDn (p := fun ω σ => candDist c r l a ω σ) hFm hζm.ennreal_toNNReal)
        (measurableSet_singleton 0)
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hm ?_
    filter_upwards [hker, hcontK] with ω₀ hk0 hc0
    filter_upwards [hk0, hc0] with ω hω hcω hold hζ0 hζc
    rw [evalDn_eq_of_continuousWithinAt hcω.continuousWithinAt]
    exact (hω hold hζ0).2 hζc
  rw [← ae_all_iff] at hE2
  filter_upwards [hE2, hE2c, hE3, hcont] with ω h2 h2c h3 hcω hold hζ0
  refine ⟨fun σ hσc hσζ => ?_, fun hζc => ?_⟩
  · rcases eq_or_lt_of_le hσc with hσe | hσlt
    · rw [hσe]
      exact h2c hold hζ0 (by rw [← hσe]; exact hσζ)
    -- a rational time between `σ` and `min cap ζ`
    have hσm : (σ : ℝ≥0∞) < min (cap : ℝ≥0∞) (candLife c r l a ω) := lt_min (ENNReal.coe_lt_coe.2 hσlt) hσζ
    obtain ⟨b, hb1, hb2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hσm
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hb1))
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (σ.coe_nonneg.trans hq1.le)
    set s : ℚ≥0 := ⟨q, hq0⟩ with hsdef
    have hs : ((s : ℝ≥0) : ℝ) = q := rfl
    have hσs : σ ≤ (s : ℝ≥0) := NNReal.coe_le_coe.1 (by rw [hs]; exact hq1.le)
    have hsb : ((s : ℝ≥0) : ℝ≥0∞) < min (cap : ℝ≥0∞) (candLife c r l a ω) :=
      (ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 (by rw [hs]; exact hq2))).trans hb2
    have hsc : (s : ℝ≥0) ≤ cap := ENNReal.coe_le_coe.1 ((le_of_lt hsb).trans (min_le_left _ _))
    have hsζ : ((s : ℝ≥0) : ℝ≥0∞) < candLife c r l a ω := hsb.trans_le (min_le_right _ _)
    have hinf := h2 s hold hζ0 hsc hsζ
    set m := ⨅ q : ℚ≥0, (if (q : ℝ≥0) ≤ (s : ℝ≥0) then candDist c r l a ω q else 1) with hmdef
    have hbdd : BddBelow (range fun q : ℚ≥0 => (if (q : ℝ≥0) ≤ (s : ℝ≥0) then candDist c r l a ω q else 1)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨q, rfl⟩
      dsimp only
      split_ifs
      · exact badDist_nonneg _ _
      · exact zero_le_one
    -- every rational time `≤ s` has distance at least `m`; so does `σ`, by continuity
    by_contra hneg
    have hlt : candDist c r l a ω σ < m := lt_of_le_of_lt (not_lt.1 hneg) hinf
    obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hcω.continuousAt (m - candDist c r l a ω σ) (by linarith)
    obtain ⟨q', hq'σ, hq'd⟩ : ∃ q' : ℚ≥0, (q' : ℝ≥0) ≤ σ ∧ dist (q' : ℝ≥0) σ < δ := by
      by_cases hσ0 : (σ : ℝ) - δ < 0
      · refine ⟨0, by simp, ?_⟩
        rw [NNReal.dist_eq]
        have : ((0 : ℚ≥0) : ℝ≥0) = 0 := by simp
        rw [this, NNReal.coe_zero, zero_sub, abs_neg, abs_of_nonneg σ.coe_nonneg]
        linarith
      · obtain ⟨q₁, h1, h2⟩ := exists_rat_btwn (show (σ : ℝ) - δ < σ by linarith)
        have hq₁ : (0 : ℚ) ≤ q₁ := by exact_mod_cast (not_lt.1 hσ0).trans h1.le
        let q₂ : ℚ≥0 := ⟨q₁, hq₁⟩
        have hc : ((q₂ : ℝ≥0) : ℝ) = q₁ := rfl
        refine ⟨q₂, NNReal.coe_le_coe.1 (by rw [hc]; exact h2.le), ?_⟩
        rw [NNReal.dist_eq, hc, abs_sub_lt_iff]
        constructor <;> linarith
    have hF := hδF hq'd
    rw [Real.dist_eq, abs_lt] at hF
    have hterm : m ≤ candDist c r l a ω (q' : ℝ≥0) := by
      have := ciInf_le hbdd q'
      simp only [hq'σ.trans hσs, ↓reduceIte] at this
      exact this
    linarith [hF.2]
  · have h := h3 hold hζ0 hζc
    rwa [evalDn_eq_of_continuousWithinAt hcω.continuousWithinAt] at h

end Ae

end InteractingSLE.Theorem14.GW2Rd
