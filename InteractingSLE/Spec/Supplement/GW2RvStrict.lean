/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzMono
import InteractingSLE.Spec.Supplement.GW2TkStrict


/-!
# GW2 at a root `x`: strictly increasing caps (decision D12 at a root)

Packet PROVE-GW2-ROOTX, round 4. RELDET's `GW2TkStrict` at a root `x`: the stage instance on version `n + 1` with
the slow stop `V n − start` needs `V n < V (n + 1)` on the good records. GB6's level stops of the root-`x`
separation readout rescaled to start at `3` (`GW2Rd.aeSeparationReadout_scale3`) are strictly increasing at every
sample (`GW2Rd.strictMono_localStop_of_eq_three`):

* **`exists_versionsXA_of_capGauge_strict`** (any cap gauge, for D3a's capped family at a root),
  `exists_finite_family_strictX`, `exists_versionsXA_fin_strict`;
* `ae_source_cf_complete`; **`exists_schedVersionsXA_strict`**: the schedule instance's root-`x` versions at
  `rootPt r.1 ≥ 0`, finite, monotone at every sample, strictly increasing on the good records, exhausting eventually.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rv

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC
  GW2TipSystem GW2Rd GW2Rz

section Family

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
  {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}

/-- **Announced capped root-`x` versions with STRICTLY INCREASING stops, for any cap gauge** (RELDET's
`GW2Rd.exists_versionsA_of_capGauge_strict` at a root `x`: the separation readout rescaled to start at `3`). -/
theorem exists_versionsXA_of_capGauge_strict [IsProbabilityMeasure P]
    (hF : IsFlowLineDriver κ b J θ P h W' ζ') (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    {Gζ : GaugeReadout} (hGζm : ∀ t, Measurable (Gζ t)) (hGζc : IsCausal Gζ) (hGζ0 : ∀ t p, 0 ≤ Gζ t p)
    {Lζ : Ω → ℝ≥0∞}
    (hζ : ∀ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), CoordX x s P W' ζ' w γ α D L →
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → 0 < Lζ ω ∧
        ContinuousOn (fun t => Gζ t (cfRec s W' ζ' ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω → 0 < Gζ t (cfRec s W' ζ' ω, fun u => D u ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → Gζ t (cfRec s W' ζ' ω, fun u => D u ω) = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsRelVersionXA x s P W' ζ' w γ α (R m) (V m)) ∧ (∀ ω, StrictMono fun m => V m ω) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ m, V m ω < Lζ ω) ∧
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        ENNReal.ofReal (clockX x s W' ζ' w t ω) < Lζ ω →
        ∃ m, ENNReal.ofReal (clockX x s W' ζ' w t ω) < V m ω := by
  have hrecm : Measurable (cfRec s W' ζ') := (measurable_recOf_cfE hF s).2
  obtain ⟨D, L, hC, hLive⟩ := exists_coordX_live hF hα hNR hcf hwm hwc hw0 hγ hs hx
  obtain ⟨D', L', Lg, g, G', hC', hrd, hle, -, hLg⟩ := exists_capReadoutX hC hrecm hLive hGζm hGζc hGζ0
    (hζ D L hC)
  have hrd3 := aeSeparationReadout_scale3 hrd
  refine ⟨fun m => coordDriver (D := D') (g := scale3 g) m, fun m ω => (coordStop (g := scale3 g) m ω : ℝ≥0∞),
    fun m => isRelVersionXA_capCoord hC' hrd3 hle m,
    fun ω => fun _ _ hmm' => ENNReal.coe_lt_coe.2 (strictMono_localStop_of_eq_three (hrd3.continuous ω)
      (scale3_zero hrd.zero_pos ω) hmm'), ?_, ?_⟩
  · filter_upwards [hLg] with ω hω hm m
    exact (coordStop_lt_capX hrd3 m ω).trans_le ((hω hm).le.trans (min_le_right _ _))
  · filter_upwards [hLg, hC.relative] with ω hLgω hrel hm t ht htζ
    obtain ⟨-, hK⟩ := hrel hm
    obtain ⟨-, hlt, -⟩ := hK t ht
    have h1 : ENNReal.ofReal (clockX x s W' ζ' w t ω) < Lg ω := by
      rw [hLgω hm]
      exact lt_min hlt htζ
    exact GW2Rd.exists_lt_coordStop_cap (Wα := W') (ζα := ζ') hrd3 h1

/-- **A capped root-`x` family stays strictly increasing**: member `n` capped at `n + 1` (RELDET's
`GW2Rd.exists_finite_family_strict` at a root). -/
theorem exists_finite_family_strictX {x : ℝ} {s : ℝ≥0} {R₀ : ℕ → ℝ≥0 → Ω → ℝ} {V₀ : ℕ → Ω → ℝ≥0∞}
    (hRV : ∀ m, IsRelVersionXA x s P W' ζ' w γ α (R₀ m) (V₀ m)) (hmono : ∀ ω, Monotone fun m => V₀ m ω)
    (hstrict : ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → StrictMono fun m => V₀ m ω)
    (hrecm : Measurable (cfRec s W' ζ')) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA x s P W' ζ' w γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → StrictMono fun n => V n ω) ∧
      (∀ n ω, V n ω ≤ V₀ n ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ ω (y : ℝ≥0∞), y ≠ ⊤ → ∀ m, y < V₀ m ω → ∀ᶠ n in atTop, y < V n ω := by
  set K : ℕ → ℝ≥0 := fun n => (n : ℝ≥0) + 1 with hKdef
  have hK : ∀ n, 0 < K n := fun n => by positivity
  have hKs : StrictMono fun n => (K n : ℝ≥0∞) := fun n n' hnn' => by
    simp only [hKdef]
    exact ENNReal.coe_lt_coe.2 (by exact_mod_cast Nat.add_lt_add_right hnn' 1)
  refine ⟨fun n => ruleCapDrv (R₀ n) (ruleCapStop s W' ζ' (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n)),
    fun n => ruleCapStop s W' ζ' (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n),
    fun n => isRelVersionXA_constCap (hRV n) hrecm (hK n), fun ω n n' hnn' => ?_, ?_,
    fun n ω => min_le_left _ _,
    fun n ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _), fun ω y hy m hym => ?_⟩
  · change min (V₀ n ω) (K n : ℝ≥0∞) ≤ min (V₀ n' ω) (K n' : ℝ≥0∞)
    exact min_le_min (hmono ω hnn') (hKs.monotone hnn')
  · filter_upwards [hstrict] with ω hω hrec n n' hnn'
    change min (V₀ n ω) (K n : ℝ≥0∞) < min (V₀ n' ω) (K n' : ℝ≥0∞)
    exact min_lt_min (hω hrec hnn') (hKs hnn')
  · obtain ⟨k, hk⟩ := exists_nat_gt y.toNNReal
    filter_upwards [eventually_ge_atTop (max m k)] with n hn
    change y < min (V₀ n ω) (K n : ℝ≥0∞)
    refine lt_min (hym.trans_le (hmono ω (le_of_max_le_left hn))) ?_
    rw [← ENNReal.coe_toNNReal hy]
    refine ENNReal.coe_lt_coe.2 (hk.trans_le ?_)
    simp only [hKdef]
    have hkn : (k : ℝ≥0) ≤ n := by exact_mod_cast le_of_max_le_right hn
    exact hkn.trans (le_add_of_nonneg_right zero_le_one)

/-- **Exhausting announced root-`x` versions with finite monotone stops, strictly increasing on the good records,
for every `s`.** -/
theorem exists_versionsXA_fin_strict [IsProbabilityMeasure P]
    (hF : IsFlowLineDriver κ b J θ P h W' ζ') (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA x s P W' ζ' w γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → StrictMono fun n => V n ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX x s W' ζ' w t ω) < V n ω := by
  have hrecm := (measurable_recOf_cfE hF s).2
  by_cases hs0 : s = 0
  · subst hs0
    obtain ⟨R₀, V₀, hRV₀, -⟩ := exists_versionsXA_mono_all hF hα hNR hcf hwm hwc hw0 hγ 0 hx
    have hnull := ae_notMem_goodX_zero hF hα (α := α) x
    obtain ⟨R, V, hRV, hmono, hstrict, -, hfin, -⟩ := exists_finite_family_strictX (V₀ := fun _ => V₀ 0)
      (fun _ => hRV₀ 0) (fun _ => monotone_const) (hnull.mono fun ω hω hm => absurd hm hω) hrecm
    refine ⟨R, V, hRV, hmono, hstrict, hfin, ?_⟩
    filter_upwards [hnull] with ω hω hm using absurd hm hω
  · obtain ⟨R₀, V₀, hRV₀, hst₀, -, hex₀⟩ := exists_versionsXA_of_capGauge_strict hF hα hNR hcf hwm hwc hw0 hγ
      (pos_iff_ne_zero.2 hs0) hx (Gζ := fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
      (fun _ _ => zero_le_one) (Lζ := fun _ => ⊤) fun _ _ _ => ae_of_all _ fun _ _ =>
        ⟨ENNReal.zero_lt_top, continuousOn_const, fun _ _ _ => zero_lt_one,
          fun _ _ ht => absurd ht ENNReal.coe_ne_top⟩
    obtain ⟨R, V, hRV, hmono, hstrict, -, hfin, hex⟩ := exists_finite_family_strictX hRV₀
      (fun ω => (hst₀ ω).monotone) (ae_of_all _ fun ω _ => hst₀ ω) hrecm
    refine ⟨R, V, hRV, hmono, hstrict, hfin, ?_⟩
    filter_upwards [hex₀] with ω hω hm t ht
    obtain ⟨m, hm'⟩ := hω hm t ht ENNReal.ofReal_lt_top
    exact hex ω _ ENNReal.ofReal_ne_top m hm'

end Family

section Sched

open GW2TipSystem.RootC24 GW2TipSystem.RootJ31

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

omit [StandardBorelSpace Ω] in
include h13 in
/-- **The source counterflow is complete almost surely.** -/
theorem ae_source_cf_complete : ∀ᵐ ω ∂c.P, c.ζ ω = ⊤ ∧ Continuous (c.W · ω) ∧ c.W 0 ω = 0 := by
  filter_upwards [GW1LaunchClock.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ] with ω h1 h2
  exact ⟨h2, h1.1, h1.2.1⟩

include h13 in
/-- **The schedule instance's root-`x` versions with strictly increasing caps** (RELDET's
`GW2Rd.exists_schedVersionsA_strict` at the root point `rootPt r.1 ≥ 0`): finite, monotone at every sample, strictly
increasing on the good records, exhausting eventually in the index. -/
theorem exists_schedVersionsXA_strict (hx : 0 ≤ rootPt r.1) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ n, V n ω < V (n + 1) ω) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hγ : ∀ᵐ ω ∂c.P, IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) ∧
      Tendsto (fun t => ‖schedTr c r l a ω t‖) atTop atTop :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.2.2.1, h.2.2.2⟩
  obtain ⟨R, V, hRV, hmono, hstrict, hfin, hex⟩ := exists_versionsXA_fin_strict hfl hα (ae_source_noReturn h13 c)
    (ae_source_cf_complete h13 c) (measurable_schedW c r l a) (continuous_schedW c r l a) (schedW_zero c r l a)
    hγ c.s hx
  exact ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n),
    hstrict.mono fun ω hω hm n => hω hm (Nat.lt_succ_self n), hfin, hex⟩

end Sched

end InteractingSLE.Theorem14.GW2Rv
