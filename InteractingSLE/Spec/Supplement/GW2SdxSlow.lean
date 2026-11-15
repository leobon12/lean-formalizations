/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdxSafe
import InteractingSLE.Spec.Supplement.GW2SdiLossy

/-!
# The lossy slow comparison (ruling R119, decision D3)

Packet PROVE-GW2-SDE (round 10). Decision D3: the stage instance is indexed by the member `n` of RELDET's exhausting
version family, and the slow buffer fact becomes LOSSY with a loss tending to `0` in `n`, as R114 did for the near
fact. This file is the slow mirror of `GW2SdiLossy`:

* `SlowBufferFactLossy z μ C sample ε` (the two almost-sure clauses of `SlowBufferFact` off a set of `μ`-measure
  `≤ ε`), `slowBufferFactLossy_of_exact`;
* **`slow_comparison_lossy`**: `win.e.P win.slowEvent ≤ μ.map sample slowSet + ε` (the sample is replaced by a dead
  record on a measurable hull of the loss set; JOINTDET's `exists_slowWindow_of_stoppedEvolution` does the rest);
* `HasSlowComparisonModelsLossy` (`∀ ε > 0, ∃ w, w.e.P w.slowEvent ≤ p + ε`), `HasSlowComparisonModels.lossy`, and
  **`HasSlowComparisonModelsLossy.exists_modelSlow`**: the SAME conclusion as `HasSlowComparisonModels.exists_modelSlow`
  (`p₀ ≤ p + ε` for every `ε`, and `p₀` does not depend on the window);
* **`RetainedSlowComparisonsLossyStatement D`** (the lossy slow binder), `retainedSlowComparisonsLossy_of_exact`;
* `RetainedSlowBufferLossyN D S` (for every `j`, eventually in `n`, the lossy slow fact with loss `(j + 1)⁻¹`),
  **`retainedSlowComparisonsLossy_of_stoppedSDE_buffer`**;
* `retainedNearModelsLossy_of_nearSDE` (the near half alone), and the successor pair
  **`retainedComparisonsLossyN_of_stoppedSDE_buffer`** (lossy near and lossy slow binders);
* `tendsto_measure_of_ae_eventually_notMem`: measurable sets that almost every point eventually leaves have measure
  tending to `0` (the limit step of D3: the loss sets `{gain > stop n}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdx

open GW2JDetR11 GW2Sdi GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4
  GW2TipSystem.RootV7 Sec5

/-- **Measurable sets that almost every point eventually leaves have measure tending to `0`.** -/
theorem tendsto_measure_of_ae_eventually_notMem {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {B : ℕ → Set α} (hB : ∀ n, MeasurableSet (B n)) (h : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ B n) :
    Tendsto (fun n => μ (B n)) atTop (𝓝 0) := by
  set T : ℕ → Set α := fun n => ⋃ m ≥ n, B m with hT
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hB m
  have hanti : Antitone T := fun n n' hnn' x hx => by
    simp only [hT, mem_iUnion] at hx ⊢
    obtain ⟨m, hm, hx⟩ := hx
    exact ⟨m, hnn'.trans hm, hx⟩
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hTm n).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have h0 : μ (⋂ n, T n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with x hx hmem
    obtain ⟨N, hN⟩ := eventually_atTop.1 hx
    have hxN := mem_iInter.1 hmem N
    simp only [hT, mem_iUnion] at hxN
    obtain ⟨m, hm, hxm⟩ := hxN
    exact hN m hm hxm
  rw [h0] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => measure_mono fun x hx => mem_iUnion₂.2 ⟨n, le_rfl, hx⟩

/-! ### The lossy slow fact and the lossy slow comparison -/

/-- **The lossy slow buffer fact**: the deterministic clauses of `SlowBufferFact`, and its two almost-sure clauses off
a set `N` of `μ`-measure at most `ε`. -/
def SlowBufferFactLossy {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} (z : SlowData Ω κ) (μ : Measure Ω)
    (driftBound : ℝ) (sample : Ω → DriverRecord) (ε : ℝ≥0∞) : Prop :=
  (∀ i, z.φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    (z.start, z.xL, z.xR) ∈ Prop59Stage.startsU ∧
    driftBound = Prop59Stage.stageDriftBound κ z.ρL₀ z.ρR₀ ∧
    ∃ N : Set Ω, μ N ≤ ε ∧ (∀ᵐ ξ ∂μ, ξ ∉ N → (sample ξ).1 ≤ z.dynamics.stop ξ) ∧
      ∀ᵐ ξ ∂μ, ξ ∉ N → ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ξ).1 →
        (sample ξ).2 q = z.start + z.dynamics.W q ξ

theorem slowBufferFactLossy_of_exact {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} {z : SlowData Ω κ} {μ : Measure Ω}
    {driftBound : ℝ} {sample : Ω → DriverRecord} (h : SlowBufferFact z μ driftBound sample) (ε : ℝ≥0∞) :
    SlowBufferFactLossy z μ driftBound sample ε :=
  ⟨h.1, h.2.1, h.2.2.1, ∅, by simp, h.2.2.2.1.mono fun _ h _ => h, h.2.2.2.2.mono fun _ h _ => h⟩

/-- **The lossy slow comparison**: the stopped SDE and the lossy slow fact give a slow window whose slow probability
is at most the sample's conditional slow probability plus the loss. -/
theorem slow_comparison_lossy {Ω : Type u} [mΩ : MeasurableSpace Ω] {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (z : SlowData Ω κ) {driftBound : ℝ} {sample : Ω → DriverRecord}
    (hsample : Measurable sample) {ε : ℝ≥0∞}
    (hSDE : z.dynamics.IsStopped μ κ z.xL (angleWordL κ z.φ z.mL z.ρL₀) z.xR (angleWordR κ z.φ z.mR z.ρR₀))
    (hB : SlowBufferFactLossy z μ driftBound sample ε) :
    ∃ win : RootS5.RestartWindow.{u} κ driftBound (Icc (-angleWeightBound κ) (angleWeightBound κ)),
      win.e.P win.slowEvent ≤ (μ.map sample) slowSet + ε := by
  classical
  obtain ⟨hφ, hy, hC, N, hN, hstop, hread⟩ := hB
  subst hC
  set N' := toMeasurable μ N with hN'
  let junk : DriverRecord := (0, fun _ => 0)
  let sample' : Ω → DriverRecord := N'.piecewise (fun _ => junk) sample
  have hs' : Measurable sample' :=
    Measurable.piecewise (measurableSet_toMeasurable μ N) measurable_const hsample
  have hin : ∀ ξ, ξ ∈ N' → sample' ξ = junk := fun ξ hξ => Set.piecewise_eq_of_mem _ _ _ hξ
  have hout : ∀ ξ, ξ ∉ N' → sample' ξ = sample ξ := fun ξ hξ => Set.piecewise_eq_of_notMem _ _ _ hξ
  have hsub : ∀ ξ, ξ ∉ N' → ξ ∉ N := fun ξ hξ hN => hξ (subset_toMeasurable μ N hN)
  have hstop' : ∀ᵐ ξ ∂μ, (sample' ξ).1 ≤ z.dynamics.stop ξ := by
    filter_upwards [hstop] with ξ h
    by_cases hξ : ξ ∈ N'
    · rw [hin ξ hξ]
      exact zero_le
    · rw [hout ξ hξ]
      exact h (hsub ξ hξ)
  have hread' : ∀ᵐ ξ ∂μ, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample' ξ).1 →
      (sample' ξ).2 q = z.start + z.dynamics.W q ξ := by
    filter_upwards [hread] with ξ h q hq
    by_cases hξ : ξ ∈ N'
    · rw [hin ξ hξ] at hq
      exact absurd hq (not_lt.2 zero_le)
    · rw [hout ξ hξ] at hq ⊢
      exact h (hsub ξ hξ) q hq
  obtain ⟨win, hwin⟩ := GW2JDetR10.exists_slowWindow_of_stoppedEvolution hκ hκ4 z.ρL₀ z.ρR₀ z.mL z.mR z.φ hφ z.xL
    z.xR z.start hy μ z.dynamics.filtration z.dynamics.W z.dynamics.VL z.dynamics.VR z.dynamics.B z.dynamics.stop
    hSDE.1 hSDE.2 hs' hstop' hread'
  refine ⟨win, hwin.trans ?_⟩
  rw [Measure.map_apply hs' measurableSet_slowSet]
  calc μ (sample' ⁻¹' slowSet) ≤ μ (sample ⁻¹' slowSet ∪ N') := by
        refine measure_mono fun ξ hξ => ?_
        by_cases h : ξ ∈ N'
        · exact Or.inr h
        · refine Or.inl ?_
          change sample' ξ ∈ slowSet at hξ
          rwa [hout ξ h] at hξ
    _ ≤ μ (sample ⁻¹' slowSet) + μ N' := measure_union_le _ _
    _ = (μ.map sample) slowSet + μ N := by
        rw [Measure.map_apply hsample measurableSet_slowSet, hN', measure_toMeasurable]
    _ ≤ (μ.map sample) slowSet + ε := by gcongr

/-! ### Lossy slow models: the uniform slow constant survives -/

/-- **Lossy slow comparison models**: for every `ε > 0`, a restart window dominated up to `ε`. -/
def HasSlowComparisonModelsLossy {Ω L : Type*} [MeasurableSpace Ω] (κ C : ℝ) (J : Set ℝ) (P : Measure Ω)
    (A : L → Set Ω) (depth : L → ℕ) (p : L → ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ (k : ℕ) l, depth l = 2 * k + 4 → ∀ a, ∀ᵐ ω ∂P, ω ∈ A l → ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ w : RootS5.RestartWindow.{u} κ C J, w.e.P w.slowEvent ≤ p l a ω + ε

theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.RootS5.HasSlowComparisonModels.lossy {Ω L : Type*}
    [MeasurableSpace Ω] {κ C : ℝ} {J : Set ℝ} {P : Measure Ω} {A : L → Set Ω} {depth : L → ℕ}
    {p : L → ℕ → Ω → ℝ≥0∞} (h : RootS5.HasSlowComparisonModels.{u} κ C J P A depth p) :
    HasSlowComparisonModelsLossy.{u} κ C J P A depth p := by
  intro k l hl a
  filter_upwards [h k l hl a] with ω hω hωA ε _
  obtain ⟨w, hw⟩ := hω hωA
  exact ⟨w, hw.trans le_self_add⟩

/-- **The uniform slow constant from lossy models**: the same conclusion as
`RootS5.HasSlowComparisonModels.exists_modelSlow` (Lemma 5.10). -/
theorem HasSlowComparisonModelsLossy.exists_modelSlow {Ω L : Type*} [MeasurableSpace Ω] {κ C : ℝ} {J : Set ℝ}
    {P : Measure Ω} {A : L → Set Ω} {depth : L → ℕ} {p : L → ℕ → Ω → ℝ≥0∞}
    (hModels : HasSlowComparisonModelsLossy.{u} κ C J P A depth p) (hκ : 0 < κ) (hJ : IsCompact J)
    (hJ2 : J ⊆ Ioi (-2)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ ≤ 1 ∧
      ∀ (k : ℕ) l, depth l = 2 * k + 4 → ∀ a, ∀ᵐ ω ∂P, ω ∈ A l → ENNReal.ofReal p₀ ≤ p l a ω := by
  obtain ⟨p₀, hp₀, hp₀1, hbound⟩ := RootS5.exists_uniform_slow_probability.{u} (C := C) hκ hJ hJ2
  refine ⟨p₀, hp₀, hp₀1, fun k l hl a => ?_⟩
  filter_upwards [hModels k l hl a] with ω hω hωA
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨w, hw⟩ := hω hωA ε (by exact_mod_cast hε)
  exact (hbound w).trans hw

/-! ### The lossy slow binder and the successor pair -/

/-- **The lossy slow binder** (decision D3): C24's slow comparisons with slack `ε` for every `ε > 0`. -/
def RetainedSlowComparisonsLossyStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    HasSlowComparisonModelsLossy.{u} c.κ ((D Ω c).experiment r).driftBound
      (Icc (-angleWeightBound c.κ) (angleWeightBound c.κ)) c.P
      (((D Ω c).experiment r).data.alive ((D Ω c).G r)) List.length
      (fun l a ω => ((D Ω c).experiment r).retained.kernel l a ω slowSet)

theorem retainedSlowComparisonsLossy_of_exact {D : ConstructionFamily.{u}} (h : RetainedSlowComparisonsStatement D) :
    RetainedSlowComparisonsLossyStatement D := fun Ω _ _ c r => (h Ω c r).lossy

/-- **The lossy slow buffer facts, eventually in the version index** (decision D3): for every `j`, for all large `n`,
the slow fact of `S n` with loss `(j + 1)⁻¹`. -/
def RetainedSlowBufferLossyN (D : ConstructionFamily.{u}) (S : ℕ → ComparisonFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ j : ℕ, ∀ᶠ n in atTop,
      SlowBufferFactLossy ((S n Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((D Ω c).experiment r).driftBound (((D Ω c).experiment r).data.sample l a) ((j : ℝ≥0∞) + 1)⁻¹

/-- **The lossy slow binder from the eventual stopped SDE and the eventual lossy slow facts.** -/
theorem retainedSlowComparisonsLossy_of_stoppedSDE_buffer (D : ConstructionFamily.{u}) (S : ℕ → ComparisonFamily.{u})
    (hSDE : RetainedStoppedSlowSDEN D S) (hBuffer : RetainedSlowBufferLossyN D S) :
    RetainedSlowComparisonsLossyStatement D := by
  intro Ω _ _ c r k l hl a
  filter_upwards [hSDE Ω c r k l hl a, hBuffer Ω c r k l hl a] with ω hs hb hω ε hε
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  have hj' : ((j : ℝ≥0∞) + 1)⁻¹ ≤ ε := (ENNReal.inv_le_inv.2 le_self_add).trans hj.le
  obtain ⟨n, hn1, hn2⟩ := ((hs hω).and (hb hω j)).exists
  obtain ⟨win, hwin⟩ := slow_comparison_lossy c.hκ c.hκ4 (condExpKernel c.P (c.sigma r l) ω)
    ((S n Ω c r).slow l a ω) (((D Ω c).experiment r).sampleMeas l a) hn1 hn2
  refine ⟨win, hwin.trans ?_⟩
  change _ ≤ ((condExpKernel c.P (c.sigma r l) ω).map (((D Ω c).experiment r).data.sample l a)) slowSet + ε
  gcongr

/-- **The lossy near binder from the near half of the stopped SDE alone**
(`retainedNearModelsLossy_of_stoppedSDE_buffer` reads only `.near`). -/
theorem retainedNearModelsLossy_of_nearSDE (D : ConstructionFamily.{u}) (C : ℕ → ComparisonFamily.{u})
    (hSDE : ∀ k, RetainedStoppedNearSDE D (C k)) (hBuffer : RetainedNearBufferLossy D C) :
    RetainedNearModelsLossyStatement D := by
  intro Ω _ _ c r l k
  filter_upwards [hSDE k Ω c r l, hBuffer Ω c r l k] with ω hs hb hω
  let z := (C k Ω c r).near l ω
  refine ⟨z.family, fun n => ?_⟩
  filter_upwards [hs hω n, hb hω n] with m hmSDE hmBuffer
  refine ⟨z.candidate n m, ?_⟩
  change z.family.crossProb m n ≤
    ((condExpKernel c.P (c.sigma r l) ω).map
      (((D Ω c).experiment r).data.sample l (z.candidate n m)))
      (((D Ω c).experiment r).data.reach l (z.candidate n m)) + ((k : ℝ≥0∞) + 1)⁻¹
  exact near_comparison_lossy c.hκ (condExpKernel c.P (c.sigma r l) ω) z
    (fun a => ((D Ω c).experiment r).sampleMeas l a)
    (((D Ω c).experiment r).data.reach l) n m hmSDE hmBuffer

/-- **The successor pair** (decisions D1, D3): the lossy near binder from the near half for `C k` and the near facts
with loss `(k + 1)⁻¹`; the lossy slow binder from the slow half eventually in `n` for `S n` and the slow facts with
loss tending to `0` in `n`. -/
theorem retainedComparisonsLossyN_of_stoppedSDE_buffer (D : ConstructionFamily.{u}) (C S : ℕ → ComparisonFamily.{u})
    (hNearSDE : ∀ k, RetainedStoppedNearSDE D (C k)) (hNear : RetainedNearBufferLossy D C)
    (hSlowSDE : RetainedStoppedSlowSDEN D S) (hSlow : RetainedSlowBufferLossyN D S) :
    RetainedNearModelsLossyStatement D ∧ RetainedSlowComparisonsLossyStatement D :=
  ⟨retainedNearModelsLossy_of_nearSDE D C hNearSDE hNear,
    retainedSlowComparisonsLossy_of_stoppedSDE_buffer D S hSlowSDE hSlow⟩

end InteractingSLE.Theorem14.GW2Sdx
