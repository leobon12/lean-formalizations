/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR11Assembly

/-!
# GW2's lossy near interface (ruling R114)

Packet PROVE-GW2-SDE (round 6). Ruling R114 (F-DEATH): the exact near fact (`GW2JDetR11.NearBufferFact`) forces the
near stop to be the force-buffer exit before the sample dies. The separation-level buffer can end first, so the near
interface becomes LOSSY: for every `ε > 0` the near fact holds off a set of conditional probability `≤ ε`, via ROOT2's
measurable buffer selection with arbitrarily small conditional loss. PROVE-GW2-SDE checks whether JOINTDET's
`retainedComparisons_of_stoppedSDE_buffer` survives the loss and otherwise proves the lossy variant.

**The check.** JOINTDET's near binder `RetainedNearModelsStatement D` (`RootN4.HasNearCrossingModels`) asks, per
history, a family `f` with `f.crossProb m n ≤ p l a ω` EXACTLY for some candidate `a`. A lossy fact only gives
`f.crossProb m n ≤ p l a ω + ε`, with the candidate depending on `ε`, so the exact binder does not follow. But every
consumer of the binder (`RootN4.testClaims_of_nearModels`, `RootC24`/`GW2Swc`'s `testClaims_of_nearModels_unitEvent`,
`RootW8`, `RootS5` claims) uses it ONLY through `HasNearCrossingModels.modelCross`, the limit statement
`∀ δ > 0, ∃ a, 1 − δ < p l a ω`. That limit survives the loss. So this file proves the lossy variant:

* `NearBufferFactLossy z μ sample reach n m ε` (the exact fact off a set of `μ`-measure `≤ ε`),
  `nearBufferFactLossy_of_exact`;
* **`near_comparison_lossy`**: `f.crossProb m n ≤ μ.map sample (reach) + ε` (JOINTDET's `near_comparison` with the
  bad set added to the reach event);
* `HasNearCrossingModelsLossy` (slack `(k + 1)⁻¹` for every `k`), `HasNearCrossingModels.lossy`, and
  **`HasNearCrossingModelsLossy.modelCross`**: the SAME conclusion as `RootN4.HasNearCrossingModels.modelCross`;
* `RetainedNearModelsLossyStatement D`, `RetainedNearBufferLossy D C` (the near buffer facts with loss `(k + 1)⁻¹`
  for the comparison family `C k`), `RetainedSlowBufferStatement` (the slow field of `RetainedBufferStatement`);
* **`retainedNearModelsLossy_of_stoppedSDE_buffer`**, `retainedSlowComparisons_of_slowBuffer` (JOINTDET's slow transfer
  from the slow field alone), and **`retainedComparisonsLossy_of_stoppedSDE_buffer`** (both binders, near lossy).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdi

open GW2JDetR11 GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4 GW2TipSystem.RootV7
  Supp12.DSReach CS3Cross Sec5

/-! ### The lossy near fact and the lossy near comparison -/

/-- **The lossy near buffer fact**: the exact clauses of `NearBufferFact` off a set `N` of `μ`-measure at most `ε`. -/
def NearBufferFactLossy {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} (z : NearData Ω κ) (μ : Measure Ω)
    (sample : ℕ → Ω → DriverRecord) (reach : ℕ → Set DriverRecord) (n m : ℕ) (ε : ℝ≥0∞) : Prop :=
  MeasurableSet (reach (z.candidate n m)) ∧ ∃ N : Set Ω, μ N ≤ ε ∧
    ∀ᵐ ξ ∂μ, ξ ∉ N → 0 < (z.dynamics n m).stop ξ ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = (z.dynamics n m).stop ξ → v < (n : ℝ≥0) →
        Coupling.stateAt (z.dynamics n m).W (z.dynamics n m).VL
          (z.dynamics n m).VR v ξ ∉ nearBuffer z.family n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < (z.dynamics n m).stop ξ →
        Coupling.stateAt (z.dynamics n m).W (z.dynamics n m).VL
          (z.dynamics n m).VR t ξ ∈ nearTarget z.family →
        sample (z.candidate n m) ξ ∈ reach (z.candidate n m)

theorem nearBufferFactLossy_of_exact {Ω : Type u} [MeasurableSpace Ω] {κ : ℝ} {z : NearData Ω κ} {μ : Measure Ω}
    {sample : ℕ → Ω → DriverRecord} {reach : ℕ → Set DriverRecord} {n m : ℕ}
    (h : NearBufferFact z μ sample reach n m) (ε : ℝ≥0∞) : NearBufferFactLossy z μ sample reach n m ε :=
  ⟨h.1, ∅, by simp, h.2.mono fun _ h _ => h⟩

/-- **The lossy near comparison**: the stopped SDE and the lossy buffer fact give the reference family's crossing
probability up to the loss. -/
theorem near_comparison_lossy {Ω : Type u} [mΩ : MeasurableSpace Ω] {κ : ℝ} (hκ : 0 < κ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (z : NearData Ω κ) {sample : ℕ → Ω → DriverRecord}
    (hsample : ∀ a, Measurable (sample a)) (reach : ℕ → Set DriverRecord) (n m : ℕ) {ε : ℝ≥0∞}
    (hSDE : (z.dynamics n m).IsStopped μ κ z.family.xL (z.family.ρLs m) z.family.xR (z.family.ρRs m))
    (hBuffer : NearBufferFactLossy z μ sample reach n m ε) :
    z.family.crossProb m n ≤ (μ.map (sample (z.candidate n m))) (reach (z.candidate n m)) + ε := by
  let d := z.dynamics n m
  let f := z.family
  obtain ⟨N, hN, hNae⟩ := hBuffer.2
  obtain ⟨Ω', mΩ', μ', _, π, hπ, 𝓕', W', VL', VR', B', ζ', hmarginal, hE', hag⟩ :=
    Restart.StoppedCont.stoppedContinuationStatement hκ f.xL f.xR
      (f.ρLs m) (f.ρRs m) (f.hw m).1 μ d.filtration d.W d.VL d.VR d.B d.stop
      hSDE.1 hSDE.2
  let e : EvolutionData.{u} f.nL f.nR := ⟨Ω', mΩ', μ', 𝓕', W', VL', VR', B', ζ'⟩
  have heq := GW2JDetR10.reach_probability_eq_of_same_word hκ f.hnL f.hnR
    f.hε (show 0 < 1 / ((n : ℝ) + 1) by positivity) f.hη f.hxL0 f.hxR0
    f.hxL f.hxR (f.hw m) (f.sequence m) e (f.hE m) hE' (n : ℝ≥0) (n : ℝ)
    (nearTarget f) (nearBuffer f n) (isOpen_nearTarget f) (isOpen_nearBuffer f n)
    (inBuffer_of_mem_nearBuffer f n)
  change (f.sequence m).P (reachEvent (n : ℝ≥0) (nearTarget f) (nearBuffer f n)
    (f.sequence m).W (f.sequence m).VL (f.sequence m).VR (f.sequence m).lifetime) ≤ _
  have hNμ' : μ' (π ⁻¹' N) ≤ ε := by
    calc μ' (π ⁻¹' N) ≤ (μ'.map π) N := Measure.le_map_apply hπ.aemeasurable N
      _ = μ N := by rw [hmarginal]
      _ ≤ ε := hN
  rw [heq, Measure.map_apply (hsample _) hBuffer.1, ← hmarginal,
    Measure.map_apply hπ ((hsample _) hBuffer.1)]
  have hdata : ∀ᵐ ξ ∂μ',
      (∀ t : ℝ≥0, (t : ℝ≥0∞) = d.stop (π ξ) →
        ContinuousOn (fun v => Coupling.stateAt d.W d.VL d.VR v (π ξ)) (Iic t)) ∧
      (π ξ ∉ N → 0 < d.stop (π ξ) ∧
        (∀ v : ℝ≥0, (v : ℝ≥0∞) = d.stop (π ξ) → v < (n : ℝ≥0) →
          Coupling.stateAt d.W d.VL d.VR v (π ξ) ∉ nearBuffer f n) ∧
        ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < d.stop (π ξ) →
          Coupling.stateAt d.W d.VL d.VR t (π ξ) ∈ nearTarget f →
          sample (z.candidate n m) (π ξ) ∈ reach (z.candidate n m)) :=
    ae_of_ae_map hπ.aemeasurable (hmarginal.symm ▸ (hSDE.2.and hNae))
  calc μ' (reachEvent (n : ℝ≥0) (nearTarget f) (nearBuffer f n) W' VL' VR' ζ')
      ≤ μ' (π ⁻¹' (sample (z.candidate n m) ⁻¹' reach (z.candidate n m)) ∪ π ⁻¹' N) := by
        refine measure_mono_ae ?_
        filter_upwards [hdata, hag, hE'.2.2.2.2] with ξ hd hξ hp hreach
        by_cases hξN : π ξ ∈ N
        · exact Or.inr hξN
        refine Or.inl ?_
        have hd2 := hd.2 hξN
        change IsIntegratedSLEPath κ f.xL f.xR (f.ρLs m) (f.ρRs m)
          (fun v => W' v ξ) (fun i v => VL' i v ξ) (fun j v => VR' j v ξ)
          (fun v => B' v ξ) (ζ' ξ) at hp
        obtain ⟨t, htT, htζ, htO, htB⟩ := hreach
        have hstate : ∀ v : ℝ≥0, (v : ℝ≥0∞) < d.stop (π ξ) →
            Coupling.stateAt W' VL' VR' v ξ = Coupling.stateAt d.W d.VL d.VR v (π ξ) := by
          intro v hv
          obtain ⟨hW, hL, hR⟩ := hξ.2 v hv
          exact Prod.ext hW (Prod.ext (funext hL) (funext hR))
        have htV := GW2JDetR10.lt_stop_of_buffer_exit
          (f := fun v => Coupling.stateAt d.W d.VL d.VR v (π ξ))
          (g := fun v => Coupling.stateAt W' VL' VR' v ξ) hd2.1
          (hp.isForcePath.continuousOn_w.prodMk
            ((continuousOn_pi.2 hp.isForcePath.continuousOn_vL).prodMk
              (continuousOn_pi.2 hp.isForcePath.continuousOn_vR))) hd.1 hstate hd2.2.1
          htT htζ htB
        exact hd2.2.2 t htT htV (hstate t htV ▸ htO)
    _ ≤ μ' (π ⁻¹' (sample (z.candidate n m) ⁻¹' reach (z.candidate n m))) + μ' (π ⁻¹' N) :=
        measure_union_le _ _
    _ ≤ μ' (π ⁻¹' (sample (z.candidate n m) ⁻¹' reach (z.candidate n m))) + ε := by gcongr

/-! ### Lossy near models: the limit statement survives -/

/-- **Lossy near-crossing models**: for every `k`, a reference family dominated up to `(k + 1)⁻¹`. -/
def HasNearCrossingModelsLossy {Ω L : Type*} [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω) (A : L → Set Ω)
    (p : L → ℕ → Ω → ℝ≥0∞) : Prop :=
  ∀ l (k : ℕ), ∀ᵐ ω ∂P, ω ∈ A l → ∃ f : NearCrossingFamily.{u} κ,
    ∀ n, ∀ᶠ m in atTop, ∃ a, f.crossProb m n ≤ p l a ω + ((k : ℝ≥0∞) + 1)⁻¹

theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.RootN4.HasNearCrossingModels.lossy {Ω L : Type*}
    [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω} {A : L → Set Ω} {p : L → ℕ → Ω → ℝ≥0∞}
    (h : HasNearCrossingModels.{u} κ P A p) : HasNearCrossingModelsLossy.{u} κ P A p := by
  intro l k
  filter_upwards [h l] with ω hω hωA
  obtain ⟨f, hf⟩ := hω hωA
  exact ⟨f, fun n => (hf n).mono fun _ ⟨a, ha⟩ => ⟨a, ha.trans le_self_add⟩⟩

/-- **The model crossing clause from lossy models**: the same conclusion as `HasNearCrossingModels.modelCross`
(Theorem 1.3). -/
theorem HasNearCrossingModelsLossy.modelCross {Ω L : Type*} [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω}
    {A : L → Set Ω} {p : L → ℕ → Ω → ℝ≥0∞} (hNear : HasNearCrossingModelsLossy.{u} κ P A p)
    (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∀ l (δ : ℝ≥0∞), 0 < δ → ∀ᵐ ω ∂P, ω ∈ A l → ∃ a, 1 - δ < p l a ω := by
  intro l δ hδ
  set δ₁ : ℝ≥0∞ := min δ 1 with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ one_pos
  have hδ₁1 : δ₁ ≤ 1 := min_le_right _ _
  have hh0 : δ₁ / 2 ≠ 0 := (ENNReal.half_pos hδ₁0.ne').ne'
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hh0
  have hk' : ((k : ℝ≥0∞) + 1)⁻¹ ≤ δ₁ / 2 :=
    (ENNReal.inv_le_inv.2 (le_self_add)).trans hk.le
  filter_upwards [hNear l k] with ω hω hωA
  obtain ⟨f, hf⟩ := hω hωA
  obtain ⟨a, ha⟩ := f.exists_lt_of_domination h13 hκ hκ4 (p := fun a => p l a ω + ((k : ℝ≥0∞) + 1)⁻¹) hf
    (ENNReal.half_pos hδ₁0.ne')
  refine ⟨a, ?_⟩
  have h1 : 1 - δ₁ / 2 < p l a ω + δ₁ / 2 := ha.trans_le (by gcongr)
  have hfin : δ₁ / 2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ENNReal.half_le_self.trans hδ₁1)
  have hle : δ₁ / 2 ≤ 1 - δ₁ / 2 :=
    ENNReal.le_sub_of_add_le_left hfin (by rw [ENNReal.add_halves]; exact hδ₁1)
  have h2 : 1 - δ₁ / 2 - δ₁ / 2 < p l a ω := ENNReal.sub_lt_of_lt_add hle h1
  rw [tsub_tsub, ENNReal.add_halves] at h2
  exact lt_of_le_of_lt (tsub_le_tsub_left (min_le_left _ _) _) h2

/-! ### The lossy near binder and the lossy pair -/

/-- **The lossy near binder** (R114): C24's near models with slack `(k + 1)⁻¹` for every `k`. -/
def RetainedNearModelsLossyStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    HasNearCrossingModelsLossy.{u} c.κ c.P (((D Ω c).experiment r).data.alive ((D Ω c).G r))
      (fun l a ω => ((D Ω c).experiment r).retained.kernel l a ω (((D Ω c).experiment r).data.reach l a))

theorem retainedNearModelsLossy_of_exact {D : ConstructionFamily.{u}} (h : RetainedNearModelsStatement D) :
    RetainedNearModelsLossyStatement D := fun Ω _ _ c r => (h Ω c r).lossy

/-- **The lossy near buffer facts** for comparison families `C k` with loss `(k + 1)⁻¹` (the near candidates may
depend on `k`: ROOT2's buffer selection with conditional loss below `(k + 1)⁻¹`). -/
def RetainedNearBufferLossy (D : ConstructionFamily.{u}) (C : ℕ → ComparisonFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (k : ℕ),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearBufferFactLossy ((C k Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((D Ω c).experiment r).data.sample l)
        (((D Ω c).experiment r).data.reach l) n m ((k : ℝ≥0∞) + 1)⁻¹

/-- The slow field of `RetainedBufferStatement`. -/
def RetainedSlowBufferStatement (D : ConstructionFamily.{u}) (C : ComparisonFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      SlowBufferFact ((C Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        ((D Ω c).experiment r).driftBound (((D Ω c).experiment r).data.sample l a)

/-- **The lossy near binder from the stopped SDE and the lossy near buffer facts.** -/
theorem retainedNearModelsLossy_of_stoppedSDE_buffer (D : ConstructionFamily.{u}) (C : ℕ → ComparisonFamily.{u})
    (hSDE : ∀ k, RetainedStoppedSDEStatement D (C k)) (hBuffer : RetainedNearBufferLossy D C) :
    RetainedNearModelsLossyStatement D := by
  intro Ω _ _ c r l k
  filter_upwards [(hSDE k).near Ω c r l, hBuffer Ω c r l k] with ω hs hb hω
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

/-- **JOINTDET's slow transfer from the slow field alone** (`retainedSlowComparisonsStatement_of_stoppedSDE_buffer`
uses only `hBuffer.slow`). -/
theorem retainedSlowComparisons_of_slowBuffer (D : ConstructionFamily.{u}) (C : ComparisonFamily.{u})
    (hSDE : RetainedStoppedSDEStatement D C) (hBuffer : RetainedSlowBufferStatement D C) :
    RetainedSlowComparisonsStatement D := by
  intro Ω _ _ c r
  dsimp only
  intro k l hl a
  filter_upwards [hSDE.slow Ω c r k l hl a, hBuffer Ω c r k l hl a]
    with ω hs hb hω
  let z := (C Ω c r).slow l a ω
  obtain ⟨hφ, hy, hC, hstop, hread⟩ := hb hω
  have hE := hs hω
  obtain ⟨win, hwin⟩ := GW2JDetR10.exists_slowWindow_of_stoppedEvolution
    c.hκ c.hκ4 z.ρL₀ z.ρR₀ z.mL z.mR z.φ hφ z.xL z.xR z.start hy
    (condExpKernel c.P (c.sigma r l) ω) z.dynamics.filtration z.dynamics.W
    z.dynamics.VL z.dynamics.VR z.dynamics.B z.dynamics.stop hE.1 hE.2
    (((D Ω c).experiment r).sampleMeas l a) hstop hread
  change ∃ win : RootS5.RestartWindow.{u} c.κ ((D Ω c).experiment r).driftBound
    (Icc (-angleWeightBound c.κ) (angleWeightBound c.κ)),
      win.e.P win.slowEvent ≤ ((condExpKernel c.P (c.sigma r l) ω).map
        (((D Ω c).experiment r).data.sample l a)) RootV7.slowSet
  rw [hC]
  exact ⟨win, hwin⟩

/-- **Both C24 binders with the lossy near binder** (R114): the comparison families `C k` satisfy the stopped SDE,
their near buffer facts hold with loss `(k + 1)⁻¹`, and the slow buffer facts hold for `C 0`. -/
theorem retainedComparisonsLossy_of_stoppedSDE_buffer (D : ConstructionFamily.{u}) (C : ℕ → ComparisonFamily.{u})
    (hSDE : ∀ k, RetainedStoppedSDEStatement D (C k)) (hNear : RetainedNearBufferLossy D C)
    (hSlow : RetainedSlowBufferStatement D (C 0)) :
    RetainedNearModelsLossyStatement D ∧ RetainedSlowComparisonsStatement D :=
  ⟨retainedNearModelsLossy_of_stoppedSDE_buffer D C hSDE hNear,
    retainedSlowComparisons_of_slowBuffer D (C 0) (hSDE 0) hSlow⟩

end InteractingSLE.Theorem14.GW2Sdi
