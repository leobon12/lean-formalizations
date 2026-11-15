/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdxCover

/-!
# The lossy slow comparison through the cut sample (decision D3a)

Packet PROVE-GW2-SDE (round 11). Decision D3a corrects D3: the caps stay below the candidate's lifetime, so when the
candidate dies inside the sample's buffer every stop is below the gain, and "eventually `gain ≤ stop n`"
(`GW2Sdx.VStopCoversN`) fails. The lossy slow fact must CUT THE RECORD: JOINTDET's
`exists_slowWindow_of_stoppedEvolution` applies to the cut sample `RootV7.cutRecord (stop) sample` (lifetime `≤` stop,
reads below the lifetime), and the loss set `{cut sample ∈ slowSet} \ {sample ∈ slowSet}` is eventually left by every
sample as soon as the stops exhaust the sample's lifetime.

* `SlowBufferFactCut` (deterministic clauses with the drift clause in finding F1's `≤` form, measurable stop, reads
  below `min(lifetime, stop)`), `slowBufferFactCut_of_exact`, `RestartWindow.mono`; **`slow_comparison_cut`**:
  `win.e.P win.slowEvent ≤ μ {cut sample ∈ slowSet}`;
* `cutLoss`, **`eventually_notMem_cutLoss`** (deterministic: the stops exhaust the lifetime ⇒ the loss set is
  eventually left), `tendsto_measure_of_ae_eventually_notMem'` (measurable only eventually);
* `RetainedSlowBufferCutN` (eventually the cut fact; the stops exhaust the lifetime kernel-a.s.),
  **`retainedSlowComparisonsLossy_of_stoppedSDE_cut`** (the lossy slow binder);
* BUF's indexed input of D3a, `VStopExhaustsN` (on the gate, `∀ u < gain, eventually u < stop n`), with D3's
  `VDriverIdN`; `ShellFactLe` (F1's `≤` drift clause); **`ae_slowBufferCut_vpkgX`** (any drift bound `C` of the
  shells); `VPairInputsXC`, **`retainedComparisonsLossyXC_vpkg`**,
  **`retainedComparisonsLossyXC_vpkg_scaled`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdy

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2Sdh GW2Sdi GW2Sdx GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootL6 GW2TipSystem.RootN4 GW2TipSystem.RootV7 Sec5

/-! ### The cut slow fact and the cut comparison -/

/-- **The cut slow buffer fact** (decision D3a): the deterministic clauses of `SlowBufferFact`, a measurable stop, and
the sample's reads below the minimum of its lifetime and the stop. -/
def SlowBufferFactCut {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} (z : SlowData Ω κ) (μ : Measure Ω)
    (driftBound : ℝ) (sample : Ω → DriverRecord) : Prop :=
  (∀ i, z.φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    (z.start, z.xL, z.xR) ∈ Prop59Stage.startsU ∧
    Prop59Stage.stageDriftBound κ z.ρL₀ z.ρR₀ ≤ driftBound ∧
    Measurable z.dynamics.stop ∧
    ∀ᵐ ξ ∂μ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 → ((q : ℝ≥0) : ℝ≥0∞) < z.dynamics.stop ξ →
      (sample ξ).2 q = z.start + z.dynamics.W q ξ

theorem slowBufferFactCut_of_exact {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} {z : SlowData Ω κ} {μ : Measure Ω}
    {driftBound : ℝ} {sample : Ω → DriverRecord} (h : SlowBufferFact z μ driftBound sample)
    (hm : Measurable z.dynamics.stop) : SlowBufferFactCut z μ driftBound sample :=
  ⟨h.1, h.2.1, h.2.2.1.symm.le, hm, h.2.2.2.2.mono fun _ h q hq _ => h q hq⟩

/-- **Restart windows are monotone in the drift bound** (finding F1: the drift clause in `≤` form). -/
def _root_.InteractingSLE.Theorem14.GW2TipSystem.RootS5.RestartWindow.mono {κ C C' : ℝ} {J : Set ℝ}
    (w : RootS5.RestartWindow.{u} κ C J) (hC : C ≤ C') : RootS5.RestartWindow.{u} κ C' J :=
  { w with hdrift := w.hdrift.mono fun _ h hA => (h hA).mono fun _ hr h0 h1 h2 => (hr h0 h1 h2).trans hC }

@[simp] theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.RootS5.RestartWindow.mono_slowEvent {κ C C' : ℝ}
    {J : Set ℝ} (w : RootS5.RestartWindow.{u} κ C J) (hC : C ≤ C') :
    (w.mono hC).e.P (w.mono hC).slowEvent = w.e.P w.slowEvent := rfl

/-- **The cut slow comparison** (decision D3a): the stopped SDE and the cut fact give a slow window whose slow
probability is at most the probability that the sample, cut at the stop, is slow. -/
theorem slow_comparison_cut {Ω : Type u} [mΩ : MeasurableSpace Ω] {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : SlowData Ω κ) {driftBound : ℝ} {sample : Ω → DriverRecord}
    (hsample : Measurable sample)
    (hSDE : z.dynamics.IsStopped μ κ z.xL (angleWordL κ z.φ z.mL z.ρL₀) z.xR (angleWordR κ z.φ z.mR z.ρR₀))
    (hB : SlowBufferFactCut z μ driftBound sample) :
    ∃ win : RootS5.RestartWindow.{u} κ driftBound (Icc (-angleWeightBound κ) (angleWeightBound κ)),
      win.e.P win.slowEvent ≤ μ {ξ | cutRecord (z.dynamics.stop ξ) (sample ξ) ∈ slowSet} := by
  obtain ⟨hφ, hy, hC, hm, hread⟩ := hB
  have hs' : Measurable fun ξ => cutRecord (z.dynamics.stop ξ) (sample ξ) := measurable_cutRecord hm hsample
  have hstop' : ∀ᵐ ξ ∂μ, (cutRecord (z.dynamics.stop ξ) (sample ξ)).1 ≤ z.dynamics.stop ξ :=
    Eventually.of_forall fun _ => min_le_left _ _
  have hread' : ∀ᵐ ξ ∂μ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (cutRecord (z.dynamics.stop ξ) (sample ξ)).1 →
      (cutRecord (z.dynamics.stop ξ) (sample ξ)).2 q = z.start + z.dynamics.W q ξ := by
    filter_upwards [hread] with ξ h q hq
    change ((q : ℝ≥0) : ℝ≥0∞) < min (z.dynamics.stop ξ) (sample ξ).1 at hq
    change (if ((q : ℝ≥0) : ℝ≥0∞) < min (z.dynamics.stop ξ) (sample ξ).1 then (sample ξ).2 q else 0) = _
    rw [ite_eq_left hq]
    exact h q (hq.trans_le (min_le_right _ _)) (hq.trans_le (min_le_left _ _))
  obtain ⟨win, hwin⟩ := GW2JDetR10.exists_slowWindow_of_stoppedEvolution hκ hκ4 z.ρL₀ z.ρR₀ z.mL z.mR z.φ hφ z.xL
    z.xR z.start hy μ z.dynamics.filtration z.dynamics.W z.dynamics.VL z.dynamics.VR z.dynamics.B z.dynamics.stop
    hSDE.1 hSDE.2 hs' hstop' hread'
  refine ⟨win.mono hC, hwin.trans_eq ?_⟩
  rw [Measure.map_apply hs' measurableSet_slowSet]
  rfl

/-! ### The loss set -/

/-- The loss set of the cut at `L`: the cut sample is slow, the sample is not. -/
def cutLoss {Ω : Type*} (L : Ω → ℝ≥0∞) (sample : Ω → DriverRecord) : Set Ω :=
  {ξ | cutRecord (L ξ) (sample ξ) ∈ slowSet ∧ sample ξ ∉ slowSet}

theorem measurableSet_cutLoss {Ω : Type*} [MeasurableSpace Ω] {L : Ω → ℝ≥0∞} {sample : Ω → DriverRecord}
    (hL : Measurable L) (hs : Measurable sample) : MeasurableSet (cutLoss L sample) :=
  (measurable_cutRecord hL hs measurableSet_slowSet).inter (hs measurableSet_slowSet).compl

/-- **The loss set is eventually left once the cuts exhaust the lifetime** (deterministic). -/
theorem eventually_notMem_cutLoss {Ω : Type*} {L : ℕ → Ω → ℝ≥0∞} {sample : Ω → DriverRecord} {ξ : Ω}
    (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 → ∀ᶠ n in atTop, ((q : ℝ≥0) : ℝ≥0∞) < L n ξ) :
    ∀ᶠ n in atTop, ξ ∉ cutLoss (L n) sample := by
  by_cases hs : sample ξ ∈ slowSet
  · exact Eventually.of_forall fun _ hξ => hξ.2 hs
  · simp only [slowSet, mem_ofPred_eq, not_forall, not_le] at hs
    obtain ⟨q, hq1, hqζ, hbad⟩ := hs
    filter_upwards [h q hqζ] with n hn hξ
    have hlt : ((q : ℝ≥0) : ℝ≥0∞) < min (L n ξ) (sample ξ).1 := lt_min hn hqζ
    have hc := hξ.1 q hq1 hlt
    change (if ((q : ℝ≥0) : ℝ≥0∞) < min (L n ξ) (sample ξ).1 then (sample ξ).2 q else 0) ≤ 7 / 4 at hc
    rw [ite_eq_left hlt] at hc
    exact absurd hc (not_le.2 hbad)

/-- `tendsto_measure_of_ae_eventually_notMem` for sets that are measurable only eventually. -/
theorem tendsto_measure_of_ae_eventually_notMem' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {B : ℕ → Set α} (hB : ∀ᶠ n in atTop, MeasurableSet (B n))
    (h : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ B n) : Tendsto (fun n => μ (B n)) atTop (𝓝 0) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hB
  have h' := tendsto_measure_of_ae_eventually_notMem (μ := μ) (B := fun n => B (n + n₀))
    (fun n => hn₀ _ (Nat.le_add_left _ _))
    (h.mono fun _ hx => (tendsto_add_atTop_nat n₀).eventually hx)
  exact (tendsto_add_atTop_iff_nat n₀).1 h'

/-! ### The lossy slow binder from the cut facts -/

/-- **The cut slow facts, eventually in the version index** (decision D3a): eventually in `n` the cut fact of `S n`,
and, kernel-a.s., the stops of `S n` exhaust the sample's lifetime. -/
def RetainedSlowBufferCutN (D : ConstructionFamily.{u}) (S : ℕ → ComparisonFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      (∀ᶠ n in atTop, SlowBufferFactCut ((S n Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((D Ω c).experiment r).driftBound (((D Ω c).experiment r).data.sample l a)) ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ∀ q : ℚ≥0,
        ((q : ℝ≥0) : ℝ≥0∞) < (((D Ω c).experiment r).data.sample l a ξ).1 →
        ∀ᶠ n in atTop, ((q : ℝ≥0) : ℝ≥0∞) < ((S n Ω c r).slow l a ω).dynamics.stop ξ

/-- **The lossy slow binder from the eventual stopped SDE and the cut facts** (decision D3a). -/
theorem retainedSlowComparisonsLossy_of_stoppedSDE_cut (D : ConstructionFamily.{u}) (S : ℕ → ComparisonFamily.{u})
    (hSDE : RetainedStoppedSlowSDEN D S) (hBuffer : RetainedSlowBufferCutN D S) :
    RetainedSlowComparisonsLossyStatement D := by
  intro Ω _ _ c r k l hl a
  filter_upwards [hSDE Ω c r k l hl a, hBuffer Ω c r k l hl a] with ω hs hb hω ε hε
  obtain ⟨hcut, hex⟩ := hb hω
  set μ := condExpKernel c.P (c.sigma r l) ω
  set sample := ((D Ω c).experiment r).data.sample l a
  have hsm : Measurable sample := ((D Ω c).experiment r).sampleMeas l a
  set L : ℕ → Ω → ℝ≥0∞ := fun n => ((S n Ω c r).slow l a ω).dynamics.stop
  have hlim : Tendsto (fun n => μ (cutLoss (L n) sample)) atTop (𝓝 0) :=
    tendsto_measure_of_ae_eventually_notMem' (hcut.mono fun n hn => measurableSet_cutLoss hn.2.2.2.1 hsm)
      (hex.mono fun ξ hξ => eventually_notMem_cutLoss hξ)
  obtain ⟨n, hn1, hn2, hn3⟩ := ((hs hω).and (hcut.and ((tendsto_order.1 hlim).2 ε hε))).exists
  obtain ⟨win, hwin⟩ := slow_comparison_cut c.hκ c.hκ4 μ ((S n Ω c r).slow l a ω) hsm hn1 hn2
  refine ⟨win, hwin.trans ?_⟩
  change _ ≤ (μ.map sample) slowSet + ε
  rw [Measure.map_apply hsm measurableSet_slowSet]
  calc μ {ξ | cutRecord (L n ξ) (sample ξ) ∈ slowSet}
      ≤ μ (sample ⁻¹' slowSet ∪ cutLoss (L n) sample) := by
        refine measure_mono fun ξ hξ => ?_
        by_cases h : sample ξ ∈ slowSet
        · exact Or.inl h
        · exact Or.inr ⟨hξ, h⟩
    _ ≤ μ (sample ⁻¹' slowSet) + μ (cutLoss (L n) sample) := measure_union_le _ _
    _ ≤ μ (sample ⁻¹' slowSet) + ε := by gcongr

/-! ### BUF's input of D3a and the successor pair -/

section Inputs

variable (V : VPkgXFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The stops exhaust the gain** (decision D3a, BUF): on the retained gate, every capacity below the gain is
eventually below the stop of version `n`. -/
def VStopExhaustsN : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ u : ℝ≥0, u < rootGain c r l a ξ →
    ∀ᶠ n in atTop, (u : ℝ≥0∞) < ((V Ω c r).slowVar l a n).stop ξ

end Inputs

/-- **The shell clauses with the drift clause in `≤` form** (finding F1). -/
def ShellFactLe (κ driftBound : ℝ) (z : SlowShell) : Prop :=
  (∀ i, z.φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧ (z.start, z.xL, z.xR) ∈ Prop59Stage.startsU ∧
    Prop59Stage.stageDriftBound κ z.ρL₀ z.ρR₀ ≤ driftBound

theorem ShellFact.le {κ C : ℝ} {z : SlowShell} (h : ShellFact κ C z) : ShellFactLe κ C z :=
  ⟨h.1, h.2.1, h.2.2.symm.le⟩

/-- **The cut slow facts for J32 from the indexed inputs** (decision D3a): at P-a.e. alive history, the cut fact of
every version (reads from `VDriverIdN`, the start from `GW2Bf.histStart`, the shell from `VShellChoice`), and the
stops exhaust the sample's lifetime kernel-a.s. (from `VStopExhaustsN`). -/
theorem ae_slowBufferCut_vpkgX (h13 : Exist.Theorem13Statement.{u}) (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hmeas : HistOrdered c r l → ∀ n, Measurable ((V Ω c r).slowVar l a n).stop)
    (hdrv : ∀ n, VDriverIdN V Ω c r l a n) (hex : VStopExhaustsN V Ω c r l a) (C : ℝ)
    (hshell : ∀ᵐ ω ∂c.P,
      ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
        ShellFactLe c.κ C ((V Ω c r).slowShell l a ω) ∧ ((V Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      (∀ n, SlowBufferFactCut ((comparisonFamilyN ((V.at n).frameN lam) Ω c r).slow l a ω)
        (condExpKernel c.P (c.sigma r l) ω) C (RootJ32.sourceSample c r l a)) ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ∀ q : ℚ≥0,
        ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
        ∀ᶠ n in atTop,
          ((q : ℝ≥0) : ℝ≥0∞) < ((comparisonFamilyN ((V.at n).frameN lam) Ω c r).slow l a ω).dynamics.stop ξ := by
  by_cases hord : HistOrdered c r l
  swap
  · exact Eventually.of_forall fun ω halive => absurd (RootJ32.alive_spec c r l ω halive).2.2 hord
  have hv₀ := GW2Bf.v0_le_historyTime c r l hord
  have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hG : MeasurableSet[c.sigma r l] (rootGate c r l) := RootK32.measurableSet_sourceBuffer_gate c r l
  have h4 : (4 : ℝ≥0∞) ^ r.2 ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4' : (4 : ℝ≥0∞) ^ r.2 ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hgood : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ n, ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
      ((q : ℝ≥0) : ℝ≥0∞) < ((V.at n).frameN lam Ω c r).base.stop (((V.at n).frameN lam Ω c r).base.slowVar l a) ξ →
        (RootJ32.sourceSample c r l a ξ).2 q = GW2Bf.histStart c r l ξ +
          ((V.at n).frameN lam Ω c r).base.drv l (((V.at n).frameN lam Ω c r).base.slowVar l a) q ξ := by
    filter_upwards [GW2Bf.ae_j32Start_eq_histStart h13 c r l hv₀, ae_all_iff.2 hdrv] with ξ hst hd hξG n q hq hqs
    have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 :=
      lt_of_le_of_lt zero_le (hq.trans_eq (RootJ32.sourceSample_fst c r l a ξ))
    have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < rootGain c r l a ξ :=
      div_four_pow_lt r.2 (by rw [← GW2Bf.j32Sample_fst]; exact hq)
    have hus : ((((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 : ℝ≥0)) : ℝ≥0∞) < ((V Ω c r).slowVar l a n).stop ξ := by
      rw [vpkg_slow_stop' (V.at n) lam Ω c r l a ξ] at hqs
      have : ((((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 : ℝ≥0)) : ℝ≥0∞) = ((q : ℝ≥0) : ℝ≥0∞) / (4 : ℝ≥0∞) ^ r.2 := by
        rw [ENNReal.coe_div (pow_ne_zero _ (by norm_num)), ENNReal.coe_pow]
        rfl
      rw [this, ENNReal.div_lt_iff (Or.inl h4) (Or.inl h4'), mul_comm]
      exact hqs
    rw [GW2Bf.j32Sample_snd c r l a ξ hq, hst a hlive, hd n hξG _ hu hus, vpkg_slow_drv (V.at n) lam Ω c r l a q ξ]
  have hexP : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
      ∀ᶠ n in atTop, ((q : ℝ≥0) : ℝ≥0∞) <
        ((V.at n).frameN lam Ω c r).base.stop (((V.at n).frameN lam Ω c r).base.slowVar l a) ξ := by
    filter_upwards [hex] with ξ h hξG q hq
    have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < rootGain c r l a ξ :=
      div_four_pow_lt r.2 (by rw [← GW2Bf.j32Sample_fst]; exact hq)
    filter_upwards [h hξG _ hu] with n hn
    rw [vpkg_slow_stop' (V.at n) lam Ω c r l a ξ]
    have : ((((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 : ℝ≥0)) : ℝ≥0∞) = ((q : ℝ≥0) : ℝ≥0∞) / (4 : ℝ≥0∞) ^ r.2 := by
      rw [ENNReal.coe_div (pow_ne_zero _ (by norm_num)), ENNReal.coe_pow]
      rfl
    rw [this, ENNReal.div_lt_iff (Or.inl h4) (Or.inl h4'), mul_comm] at hn
    exact hn
  filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hgood, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hexP,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 (GW2Bf.measurable_histStart c r l),
    KernelTower.ae_condExpKernel_compl_eq_zero h𝒢 hG, hshell] with ω hgd hexk hfz hGc hsh halive
  obtain ⟨hcov, hold, -⟩ := RootJ32.alive_spec c r l ω halive
  have hωG : ω ∈ rootGate c r l := ⟨hcov, hold⟩
  have hGξ : ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ξ ∈ rootGate c r l := ae_iff.2 (hGc.1 hωG)
  obtain ⟨hshf, hst⟩ := hsh halive
  refine ⟨fun n => ⟨hshf.1, hshf.2.1, hshf.2.2, ?_, ?_⟩, ?_⟩
  · show Measurable (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.stop
    rw [slowData_stop]
    exact fun t ht => by
      have hm := (hmeas hord n).div_const ((rootScale r.2 : ℝ≥0) : ℝ≥0∞)
      exact hm ht
  · filter_upwards [hgd, hfz, hGξ] with ξ h hξ hξG q hq hqs
    show _ = (((V.at n).frameN lam Ω c r).base.slowData l a ω).start +
      (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.W q ξ
    change ((q : ℝ≥0) : ℝ≥0∞) < (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.stop ξ at hqs
    rw [slowData_stop] at hqs
    rw [h hξG n q hq hqs, hξ, slowData_W]
    exact congrArg (· + _) hst.symm
  · filter_upwards [hexk, hGξ] with ξ h hξG q hq
    filter_upwards [h hξG q hq] with n hn
    show ((q : ℝ≥0) : ℝ≥0∞) < (((V.at n).frameN lam Ω c r).base.slowData l a ω).dynamics.stop ξ
    rw [slowData_stop]
    exact hn

/-- **The named inputs of the successor pair for J32 with D3a's slow inputs**: as `GW2Sdx.VPairInputsX`, with
`VStopExhaustsN` (the stops exhaust the gain) in place of `VStopCoversN`. -/
structure VPairInputsXC (V : ℕ → VPkgXFamily.{u}) (lam : NearDil.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  safe : ∀ k : ℕ, VPkgXSafe (V k)
  words : ∀ k : ℕ, VWordsX RootJ32.constructionFamily (V k) lam
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), VNearImgL ((V k).at 0) lam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a n : ℕ,
      VDriverIdN (V 0) Ω c r l a n
  stopExhausts : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VStopExhaustsN (V 0) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VShellChoice ((V 0).at 0) Ω c r l a

/-- **The successor pair for J32 with D3a's cut slow facts: the lossy near binder and the lossy slow binder**
(decisions D1, D3, D3a; R113, R114; Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossyXC_vpkg (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (V : ℕ → VPkgXFamily.{u})
    (lam : NearDil.{u}) (hV : VPairInputsXC V lam) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsLossyStatement RootJ32.constructionFamily.{u} := by
  have hsde : ∀ k, RetainedStoppedSDEStatementN RootJ32.constructionFamily
      (comparisonFamilyN (((V k).at 0).frameN lam)) fun n => comparisonFamilyN (((V k).at n).frameN lam) :=
    fun k => retainedStoppedSDEStatementN_vpkgX h12p₀ h13₀ h13 (V k) lam hV.lam_ne aliveOrdered_rootJ32 (hV.safe k)
      (hV.words k)
  refine ⟨retainedNearModelsLossy_of_nearSDE RootJ32.constructionFamily
    (fun k => comparisonFamilyN (((V k).at 0).frameN lam)) (fun k => (hsde k).near) ?_,
    retainedSlowComparisonsLossy_of_stoppedSDE_cut RootJ32.constructionFamily
      (fun n => comparisonFamilyN (((V 0).at n).frameN lam)) (hsde 0).slow ?_⟩
  · intro Ω _ _ c r l k
    filter_upwards [(hsde k).near Ω c r l,
      nearImgPathLossy_vpkg ((V k).at 0) lam Ω c r l (hV.lam_ne Ω c r l) (hV.nearImg k Ω c r l)]
      with ω hs hi halive n
    filter_upwards [hs halive n, hi halive n] with m h1 h2
    exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2
  · intro Ω _ _ c r k l hl a
    filter_upwards [ae_slowBufferCut_vpkgX h13 (V 0) lam Ω c r l a
      (fun hTO n => ((hV.safe 0).slowSafe n Ω c r k l hl hTO a).2.measurable_stop) (hV.driverId Ω c r k l hl a)
      (hV.stopExhausts Ω c r k l hl a) _
      ((hV.shell Ω c r k l hl a).mono fun _ h ha => ⟨ShellFact.le (h ha).1, (h ha).2⟩)]
      with ω h halive
    exact ⟨Eventually.of_forall (h halive).1, (h halive).2⟩

/-- **The successor pair with D3a's cut slow facts on the scaled cover.** -/
theorem retainedComparisonsLossyXC_vpkg_scaled (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (V : ℕ → VPkgXFamily.{u})
    (lam : NearDil.{u}) (hV : VPairInputsXC V lam) (gap : RootCv.GapFamily.{u}) :
    RetainedNearModelsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap) ∧
      RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap) :=
  have h := retainedComparisonsLossyXC_vpkg h12p₀ h13₀ h13 V lam hV
  ⟨retainedNearModelsLossy_withScaledCover gap (scaledCoverEvent_subset_rootJ32 gap) h.1,
    retainedSlowComparisonsLossy_withScaledCover gap (scaledCoverEvent_subset_rootJ32 gap) h.2⟩

end InteractingSLE.Theorem14.GW2Sdy
