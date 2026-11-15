/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SyVer
import InteractingSLE.Spec.Supplement.GW2SvVer
import InteractingSLE.Spec.Supplement.GW2RootK32Buffers

/-!
# Decision D3: monotone exhausting GB6 versions at the schedule instance

Packet PROVE-GW2-RELDET, decision D3 of `planning/reviews/DECISIONS-FABLE-1.md`. The stage instance is indexed by the
member `n` of the exhausting version family, and the slow fact is lossy with a loss tending to `0` in `n`. The limit
needs the family to exhaust EVENTUALLY in `n`: every relative clock value before the first contact is below `V n`
for all large `n`. `GW2SyVer.exists_schedVersionsA` gives only "for some `n`".

* `exists_versionsA_of_capGauge_mono`: `GW2SvVer.exists_versionsA_of_capGauge` with monotone stops. The stops are
  GB6's positive-distance stops `coordStop m`, monotone in `m` (`RootK32.monotone_localStop`).
* `exists_versionsA_mono_all`: monotone exhausting announced versions for every `s`. At `s = 0` the interior-tip event
  is null and any constant family works.
* `exists_finite_family_mono`: capping member `n` at the constant `n + 1` keeps the stops monotone, makes them finite,
  and gives eventual exhaustion.
* **`exists_versionsA_fin_mono`**, **`exists_schedVersionsA_mono`**: exhausting announced versions with finite,
  monotone stops (`V n ω ≤ V (n + 1) ω`), exhausting eventually in `n`; generic, and at the schedule instance from
  Theorem 1.3. **`exists_schedGB6_mono`**: `GW2SyVer.exists_schedGB6` with this family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC
  GW2TipSystem

/-- **Announced capped versions with MONOTONE stops, for any explored curve and any cap gauge** (the proof of
`exists_versionsA_of_capGauge`, keeping the monotonicity of GB6's stops). -/
theorem exists_versionsA_of_capGauge_mono {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ}
    {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) (hs : 0 < s)
    {Gζ : GaugeReadout} (hGζm : ∀ t, Measurable (Gζ t)) (hGζc : IsCausal Gζ) (hGζ0 : ∀ t p, 0 ≤ Gζ t p)
    {Lζ : Ω → ℝ≥0∞}
    (hζ : ∀ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), RelativeDriverCoordinates s P W Wα ζα γ α D L →
      ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → 0 < Lζ ω ∧
        ContinuousOn (fun t => Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω → 0 < Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → Gζ t (gb6Rec s Wα ζα ω, fun u => D u ω) = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧ (∀ ω, Monotone fun m => V m ω) ∧
      (∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → ∀ m, V m ω < Lζ ω) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ENNReal.ofReal (gb6Clock s W Wα ω t) < Lζ ω → ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hF s).2
  have hgoodrec := ae_gb6RecGood hF hα s
  have hW' : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) :=
    hW.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  -- relative coordinates
  obtain ⟨_, 𝓕α, _, _, _, _, hCα⟩ := id hF
  have hWa : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) (fun _ => (⊤ : ℝ≥0∞)) W := by
    intro t A hA
    have e : {ω | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧ W t ω ∈ A} = W t ⁻¹' A := by
      ext ω
      simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, mem_preimage]
    rw [e]
    exact (hWm t) hA
  have hcfE : ∀ᵐ ω ∂P, (fun _ : Ω => (⊤ : ℝ≥0∞)) ω = ⊤ ∧ W 0 ω = 0 ∧ Continuous (W · ω) ∧
      IsGeneratingTrace (W · ω) ⊤ (γ ω) := hW'.mono fun _ h => ⟨rfl, h.2.1, h.1, h.2.2⟩
  have hflE : ∀ᵐ ω ∂P, Wα 0 ω = 0 ∧ ContinuousOn (Wα · ω) {t | (t : ℝ≥0∞) < ζα ω} ∧
      IsGeneratingTrace (Wα · ω) (ζα ω) (α ω) := by
    filter_upwards [Supp8.GB6.ae_driver_zero_continuousOn hF, hα] with ω hr ht using ⟨hr.1, hr.2, ht⟩
  obtain ⟨D, L, hC⟩ := SourceC.exists_relative_driver (P := P) hWa hCα.1.2.1 hcfE hflE s hs
  -- the live readout and the cap
  have hLive := hasLiveReadout_nr hF hα hNR hW s hs hC
  obtain ⟨D', L', Lg, g, G', hC', hrd, hle, -, hLg⟩ := exists_capReadout hC hrecm hgoodrec hLive hGζm hGζc hGζ0
    (hζ D L hC)
  refine ⟨fun m => coordDriver (D := D') (g := g) m, fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
    fun m => isGB6RelVersionA_capCoord hC' hrd hle m,
    fun ω _ _ hmm' => ENNReal.coe_le_coe.2 (RootK32.monotone_localStop (hrd.continuous ω) hmm'), ?_, ?_⟩
  · -- the cap
    filter_upwards [hLg] with ω hω hm m
    exact (coordStop_lt_cap hrd m ω).trans_le ((hω hm).le.trans (min_le_right _ _))
  · -- exhaustion below the cap before the first contact
    filter_upwards [hLg, hgoodrec, hC.relative] with ω hLgω hg hrel hs' hsH t ht htζ
    have hm : gb6Rec s Wα ζα ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs', hsH⟩
    obtain ⟨-, hK⟩ := hrel hs' hsH
    obtain ⟨-, hlt, -⟩ := hK t ht
    have h1 : ENNReal.ofReal (gb6Clock s W Wα ω t) < Lg ω := by
      rw [hLgω hm]
      exact lt_min hlt htζ
    exact exists_lt_coordStop_cap hrd h1

section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Monotone exhausting announced versions for any transient explored curve, for every `s`.** -/
theorem exists_versionsA_mono_all [IsProbabilityMeasure P] (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧ (∀ ω, Monotone fun m => V m ω) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∃ m, ENNReal.ofReal (gb6Clock s W Wα ω t) < V m ω := by
  by_cases hs0 : s = 0
  · subst hs0
    obtain ⟨R, V, hRV, -⟩ := exists_versionsA_all hF hα hNR hWm hW 0
    have hα0 : ∀ᵐ ω ∂P, α ω 0 = 0 := hα.mono fun _ hω => hω.1
    refine ⟨fun _ => R 0, fun _ => V 0, fun _ => hRV 0, fun _ => monotone_const, ?_⟩
    filter_upwards [hα0] with ω hω _ hH
    rw [hω] at hH
    exact ((lt_irrefl (0 : ℝ)) hH).elim
  · obtain ⟨R, V, hRV, hmono, -, hex⟩ := exists_versionsA_of_capGauge_mono hF hα hNR hWm hW s
      (pos_iff_ne_zero.2 hs0) (Gζ := fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
      (fun _ _ => zero_le_one) (Lζ := fun _ => ⊤) fun _ _ _ => ae_of_all _ fun _ _ =>
        ⟨ENNReal.zero_lt_top, continuousOn_const, fun _ _ _ => zero_lt_one,
          fun _ _ ht => absurd ht ENNReal.coe_ne_top⟩
    exact ⟨R, V, hRV, hmono, hex.mono fun ω hω hs' hsH t ht => hω hs' hsH t ht ENNReal.ofReal_lt_top⟩

/-- **A monotone exhausting family capped at `n + 1`: finite monotone stops, eventual exhaustion.** -/
theorem exists_finite_family_mono {R₀ : ℕ → ℝ≥0 → Ω → ℝ} {V₀ : ℕ → Ω → ℝ≥0∞}
    (hRV : ∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R₀ m) (V₀ m)) (hmono : ∀ ω, Monotone fun m => V₀ m ω)
    (hrecm : Measurable (gb6Rec s Wα ζα)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ n ω, V n ω ≤ V₀ n ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ ω (x : ℝ≥0∞), x ≠ ⊤ → ∀ m, x < V₀ m ω → ∀ᶠ n in atTop, x < V n ω := by
  set K : ℕ → ℝ≥0 := fun n => (n : ℝ≥0) + 1 with hKdef
  have hK : ∀ n, 0 < K n := fun n => by positivity
  refine ⟨fun n => ruleCapDrv (R₀ n) (ruleCapStop s Wα ζα (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n)),
    fun n => ruleCapStop s Wα ζα (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n),
    fun n => isGB6RelVersionA_constCap (hRV n) hrecm (hK n), fun ω n n' hnn' => ?_, fun n ω => min_le_left _ _,
    fun n ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _), fun ω x hx m hxm => ?_⟩
  · change min (V₀ n ω) (K n : ℝ≥0∞) ≤ min (V₀ n' ω) (K n' : ℝ≥0∞)
    refine min_le_min (hmono ω hnn') (ENNReal.coe_le_coe.2 ?_)
    simp only [hKdef]
    gcongr
  · obtain ⟨k, hk⟩ := exists_nat_gt x.toNNReal
    filter_upwards [eventually_ge_atTop (max m k)] with n hn
    change x < min (V₀ n ω) (K n : ℝ≥0∞)
    refine lt_min (hxm.trans_le (hmono ω (le_of_max_le_left hn))) ?_
    rw [← ENNReal.coe_toNNReal hx]
    refine ENNReal.coe_lt_coe.2 (hk.trans_le ?_)
    simp only [hKdef]
    have hkn : (k : ℝ≥0) ≤ n := by exact_mod_cast le_of_max_le_right hn
    exact hkn.trans (le_add_of_nonneg_right zero_le_one)

/-- **Exhausting announced versions with finite monotone stops, exhausting eventually, for every `s`.** -/
theorem exists_versionsA_fin_mono [IsProbabilityMeasure P] (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock s W Wα ω t) < V n ω := by
  obtain ⟨R₀, V₀, hRV₀, hmono₀, hex₀⟩ := exists_versionsA_mono_all hF hα hNR hWm hW s
  obtain ⟨R, V, hRV, hmono, -, hfin, hex⟩ := exists_finite_family_mono hRV₀ hmono₀ (measurable_recOf_cfE hF s).2
  refine ⟨R, V, hRV, hmono, hfin, ?_⟩
  filter_upwards [hex₀] with ω hω hs hsH t ht
  obtain ⟨m, hm⟩ := hω hs hsH t ht
  exact hex ω _ ENNReal.ofReal_ne_top m hm

end Generic

section Sched

open GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Supp8.RelSafe

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **Exhausting announced GB6 versions at the schedule instance with finite MONOTONE stops, exhausting eventually in
the index** (decision D3's export). -/
theorem exists_schedVersionsA_mono :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  obtain ⟨R, V, hRV, hmono, hfin, hex⟩ := exists_versionsA_fin_mono hfl hα (ae_source_noReturn h13 c)
    (measurable_schedW c r l a) (ae_schedW_regular h13 c r l a) c.s
  exact ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n), hfin, hex⟩

include h13 in
/-- **GB6 at the schedule instance, bundled, with the monotone version family** (`GW2SyVer.exists_schedGB6` with
`exists_schedVersionsA_mono` in place of `exists_schedVersionsA`). -/
theorem exists_schedGB6_mono :
    (∀ t, Measurable (schedW c r l a t)) ∧
    (∀ t ≤ historyTime c r l, MeasurableSpace.comap (schedW c r l a t) inferInstance ≤ c.sigma r l) ∧
    (∃ GT : Set Ω, (∀ ω ∈ GT, PhysGood c.s (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s)) ∧
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω :=
  ⟨measurable_schedW c r l a, fun _ ht => comap_schedW_le_sigma c r l a ht, exists_goodSet_sched h13 c r l a,
    exists_schedVersionsA_mono h13 c r l a⟩

end Sched

end InteractingSLE.Theorem14.GW2Rd
