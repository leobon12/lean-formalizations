/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TgMono
import InteractingSLE.Spec.Supplement.GW2SdzLife

/-!
# Decision D12: strictly increasing caps of the schedule instance's versions

Packet PROVE-GW2-RELDET (D12 of `planning/reviews/DECISIONS-FABLE-3.md`; the stage instance on version `n + 1` with
stop `V n − start` needs `V n < V (n + 1)`). **Finding:** the landed families are monotone but NOT strictly increasing.
GB6's stops are `localStop g m = gaugeStop g (min (g 0 / 2) (1/(m+1))) (m + 1)`. When `g 0` is small the level
`g 0 / 2` is the same for several consecutive `m`, and the stops coincide whenever the gauge reaches that level before
the cap. Here the separation readout is rescaled by the record-measurable factor `3 / g 0` (it then starts at `3`, so
every level is `1/(m+1)`, strictly decreasing), and the stops become strictly increasing at every sample.

* `le_apply_gaugeStop`, **`gaugeStop_lt_gaugeStop`**: a lower level with a later cap gives a strictly later stop;
  **`strictMono_localStop_of_eq_three`**;
* `scale3`, `scale3G`, **`aeSeparationReadout_scale3`**: the rescaled readout;
* **`exists_versionsA_of_capGauge_strict`**: `exists_versionsA_of_capGauge_mono` with strictly increasing stops;
* `exists_finite_family_strict`, `exists_versionsA_fin_strict`;
* **`exists_schedVersionsA_strict`** (RELDET's family, successor of `exists_schedVersionsA_mono`) and
  **`exists_schedVersionsA_strict_gauge`** (PROVE-GW2-SDE's capped family, successor of
  `GW2Sdz.exists_schedVersionsA_mono_gauge`): finite, monotone at every sample, strictly increasing on the record
  event (at every sample for the capped family), exhausting.
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

/-! ### Strictly increasing stops -/

/-- At the first passage below a level that the gauge starts above, the gauge is at least that level. -/
theorem le_apply_gaugeStop {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε : ℝ} {c : ℝ≥0} (h0 : ε < g 0) :
    ε ≤ g (gaugeStop g ε c) := by
  set τ := gaugeStop g ε c with hτ
  have hbefore : ∀ t < τ, ε < g t := by
    intro t ht
    by_contra hn
    exact (not_le.2 ht) (gaugeStop_le_of_le (ht.le.trans (gaugeStop_le g ε c)) (not_lt.1 hn))
  by_contra hn
  have hlt : g τ < ε := not_le.1 hn
  obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ τ from zero_le) hg.continuousOn
    (show (g τ + ε) / 2 ∈ Icc (g τ) (g 0) by constructor <;> linarith)
  have huτ : u < τ := lt_of_le_of_ne hu.2 fun he => by
    rw [he] at hgu
    linarith
  have := hbefore u huτ
  linarith

/-- **A lower level with a later cap gives a strictly later first passage.** -/
theorem gaugeStop_lt_gaugeStop {g : ℝ≥0 → ℝ} (hg : Continuous g) {ε ε' : ℝ} {c c' : ℝ≥0} (hεε : ε' < ε)
    (h0 : ε < g 0) (hcc : c < c') : gaugeStop g ε c < gaugeStop g ε' c' := by
  set τ := gaugeStop g ε c with hτ
  set τ' := gaugeStop g ε' c' with hτ'
  by_contra hn
  have hle : τ' ≤ τ := not_lt.1 hn
  have hτ'c : τ' < c' := (hle.trans (gaugeStop_le g ε c)).trans_lt hcc
  have hmem : g τ' ≤ ε' := gaugeStop_mem hg hτ'c
  rcases hle.lt_or_eq with hlt | heq
  · have : ε < g τ' := by
      by_contra hn'
      exact (not_le.2 hlt) (gaugeStop_le_of_le (hlt.le.trans (gaugeStop_le g ε c)) (not_lt.1 hn'))
    linarith
  · have := le_apply_gaugeStop (c := c) hg h0
    rw [← hτ, ← heq] at this
    linarith

theorem gaugeLevel_three (m : ℕ) : gaugeLevel 3 m = 1 / ((m : ℝ) + 1) := by
  have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact min_eq_right (by linarith)

/-- **GB6's stops are strictly increasing for a continuous gauge starting at `3`.** -/
theorem strictMono_localStop_of_eq_three {g : ℝ≥0 → ℝ} (hg : Continuous g) (h3 : g 0 = 3) :
    StrictMono (localStop g) := by
  refine strictMono_nat_of_lt_succ fun m => ?_
  unfold localStop
  rw [h3, gaugeLevel_three, gaugeLevel_three]
  refine gaugeStop_lt_gaugeStop hg ?_ ?_ ?_
  · push_cast
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  · rw [h3]
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    linarith
  · push_cast
    exact (lt_add_one _).trans_le (le_of_eq (by ring))

/-! ### The rescaled readout -/

/-- The gauge rescaled to start at `3`. -/
def scale3 {Ω : Type*} (g : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => g t ω * (3 / g 0 ω)

/-- The readout rescaled to start at `3` (the factor read from the record). -/
def scale3G (G : GaugeReadout) : GaugeReadout := fun t p => G t p * (3 / G 0 (p.1, fun _ => 0))

theorem scale3_zero {Ω : Type*} {g : ℝ≥0 → Ω → ℝ} (h0 : ∀ ω, 0 < g 0 ω) (ω : Ω) : scale3 g 0 ω = 3 := by
  simp only [scale3]
  field_simp [(h0 ω).ne']

/-- **The rescaled readout is a separation readout with the same life.** -/
theorem aeSeparationReadout_scale3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {rec : Ω → RecData}
    {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞} {g : ℝ≥0 → Ω → ℝ} {G : GaugeReadout}
    (hrd : AESeparationReadout P rec D L g G) : AESeparationReadout P rec D L (scale3 g) (scale3G G) where
  measurable t := (hrd.measurable t).mul (measurable_const.div (hrd.measurable 0))
  continuous ω := (hrd.continuous ω).mul continuous_const
  zero_pos ω := by rw [scale3_zero hrd.zero_pos ω]; norm_num
  positive ω t ht := mul_pos (hrd.positive ω t ht) (div_pos three_pos (hrd.zero_pos ω))
  terminal ω t ht := by simp only [GW2Rd.scale3, hrd.terminal ω t ht, zero_mul]
  readout_measurable t := (hrd.readout_measurable t).mul (measurable_const.div
    ((hrd.readout_measurable 0).comp (measurable_fst.prodMk measurable_const)))
  causal t r w w' h := by
    simp only [scale3G]
    rw [hrd.causal t r w w' h]
  readout := by
    filter_upwards [hrd.readout] with ω hω
    obtain ⟨h0, ht⟩ := hω
    refine ⟨?_, fun t hlt => ?_⟩
    · simp only [scale3G, GW2Rd.scale3]
      rw [h0]
    · simp only [scale3G, GW2Rd.scale3]
      rw [ht t hlt, h0]

/-! ### The families -/

/-- **Announced capped versions with STRICTLY INCREASING stops, for any explored curve and any cap gauge** (the proof
of `exists_versionsA_of_capGauge_mono`, with the separation readout rescaled to start at `3`). -/
theorem exists_versionsA_of_capGauge_strict {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
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
      (∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R m) (V m)) ∧ (∀ ω, StrictMono fun m => V m ω) ∧
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
  have hrd3 := aeSeparationReadout_scale3 hrd
  refine ⟨fun m => coordDriver (D := D') (g := scale3 g) m, fun m ω => (coordStop (g := scale3 g) m ω : ℝ≥0∞),
    fun m => isGB6RelVersionA_capCoord hC' hrd3 hle m,
    fun ω => fun _ _ hmm' => ENNReal.coe_lt_coe.2 (strictMono_localStop_of_eq_three (hrd3.continuous ω)
      (scale3_zero hrd.zero_pos ω) hmm'), ?_, ?_⟩
  · -- the cap
    filter_upwards [hLg] with ω hω hm m
    exact (coordStop_lt_cap hrd3 m ω).trans_le ((hω hm).le.trans (min_le_right _ _))
  · -- exhaustion below the cap before the first contact
    filter_upwards [hLg, hgoodrec, hC.relative] with ω hLgω hg hrel hs' hsH t ht htζ
    have hm : gb6Rec s Wα ζα ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs', hsH⟩
    obtain ⟨-, hK⟩ := hrel hs' hsH
    obtain ⟨-, hlt, -⟩ := hK t ht
    have h1 : ENNReal.ofReal (gb6Clock s W Wα ω t) < Lg ω := by
      rw [hLgω hm]
      exact lt_min hlt htζ
    exact exists_lt_coordStop_cap hrd3 h1


section Generic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A capped family stays strictly increasing**: member `n` capped at `n + 1`, as in `exists_finite_family_mono`. -/
theorem exists_finite_family_strict {R₀ : ℕ → ℝ≥0 → Ω → ℝ} {V₀ : ℕ → Ω → ℝ≥0∞}
    (hRV : ∀ m, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R₀ m) (V₀ m)) (hmono : ∀ ω, Monotone fun m => V₀ m ω)
    (hstrict : ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → StrictMono fun m => V₀ m ω)
    (hrecm : Measurable (gb6Rec s Wα ζα)) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → StrictMono fun n => V n ω) ∧
      (∀ n ω, V n ω ≤ V₀ n ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ ω (x : ℝ≥0∞), x ≠ ⊤ → ∀ m, x < V₀ m ω → ∀ᶠ n in atTop, x < V n ω := by
  set K : ℕ → ℝ≥0 := fun n => (n : ℝ≥0) + 1 with hKdef
  have hK : ∀ n, 0 < K n := fun n => by positivity
  have hKs : StrictMono fun n => (K n : ℝ≥0∞) := fun n n' hnn' => by
    simp only [hKdef]
    exact ENNReal.coe_lt_coe.2 (by exact_mod_cast Nat.add_lt_add_right hnn' 1)
  refine ⟨fun n => ruleCapDrv (R₀ n) (ruleCapStop s Wα ζα (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n)),
    fun n => ruleCapStop s Wα ζα (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n),
    fun n => isGB6RelVersionA_constCap (hRV n) hrecm (hK n), fun ω n n' hnn' => ?_, ?_,
    fun n ω => min_le_left _ _,
    fun n ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _), fun ω x hx m hxm => ?_⟩
  · change min (V₀ n ω) (K n : ℝ≥0∞) ≤ min (V₀ n' ω) (K n' : ℝ≥0∞)
    exact min_le_min (hmono ω hnn') (hKs.monotone hnn')
  · filter_upwards [hstrict] with ω hω hrec n n' hnn'
    change min (V₀ n ω) (K n : ℝ≥0∞) < min (V₀ n' ω) (K n' : ℝ≥0∞)
    exact min_lt_min (hω hrec hnn') (hKs hnn')
  · obtain ⟨k, hk⟩ := exists_nat_gt x.toNNReal
    filter_upwards [eventually_ge_atTop (max m k)] with n hn
    change x < min (V₀ n ω) (K n : ℝ≥0∞)
    refine lt_min (hxm.trans_le (hmono ω (le_of_max_le_left hn))) ?_
    rw [← ENNReal.coe_toNNReal hx]
    refine ENNReal.coe_lt_coe.2 (hk.trans_le ?_)
    simp only [hKdef]
    have hkn : (k : ℝ≥0) ≤ n := by exact_mod_cast le_of_max_le_right hn
    exact hkn.trans (le_add_of_nonneg_right zero_le_one)

/-- **Exhausting announced versions with finite, monotone stops, strictly increasing on the record event, for every
`s`** (the trivial cap gauge). -/
theorem exists_versionsA_fin_strict [IsProbabilityMeasure P] (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζα ω → α' v ≠ 0)
    (hWm : ∀ t, Measurable (W t))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → StrictMono fun n => V n ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock s W Wα ω t) < V n ω := by
  have hrecm := (measurable_recOf_cfE hF s).2
  by_cases hs0 : s = 0
  · -- at `s = 0` the record event is null: a constant family
    subst hs0
    obtain ⟨R₀, V₀, hRV₀, -⟩ := exists_versionsA_all hF hα hNR hWm hW 0
    have hα0 : ∀ᵐ ω ∂P, α ω 0 = 0 := hα.mono fun _ hω => hω.1
    have hnull : ∀ᵐ ω ∂P, gb6Rec 0 Wα ζα ω ∉ gb6TS 0 := by
      filter_upwards [ae_gb6RecGood hF hα 0, hα0] with ω hg hω hm
      obtain ⟨-, hH⟩ := (mem_gb6TS_iff hg).2 hm
      rw [hω] at hH
      exact (lt_irrefl (0 : ℝ)) hH
    obtain ⟨R, V, hRV, hmono, hstrict, -, hfin, -⟩ := exists_finite_family_strict (V₀ := fun _ => V₀ 0)
      (fun _ => hRV₀ 0) (fun _ => monotone_const)
      (hnull.mono fun ω hω hm => absurd hm hω) hrecm
    refine ⟨R, V, hRV, hmono, hstrict, hfin, ?_⟩
    filter_upwards [hα0] with ω hω _ hH
    rw [hω] at hH
    exact ((lt_irrefl (0 : ℝ)) hH).elim
  · obtain ⟨R₀, V₀, hRV₀, hst₀, -, hex₀⟩ := exists_versionsA_of_capGauge_strict hF hα hNR hWm hW s
      (pos_iff_ne_zero.2 hs0) (Gζ := fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
      (fun _ _ => zero_le_one) (Lζ := fun _ => ⊤) fun _ _ _ => ae_of_all _ fun _ _ =>
        ⟨ENNReal.zero_lt_top, continuousOn_const, fun _ _ _ => zero_lt_one,
          fun _ _ ht => absurd ht ENNReal.coe_ne_top⟩
    obtain ⟨R, V, hRV, hmono, hstrict, -, hfin, hex⟩ := exists_finite_family_strict hRV₀
      (fun ω => (hst₀ ω).monotone) (ae_of_all _ fun ω _ => hst₀ ω) hrecm
    refine ⟨R, V, hRV, hmono, hstrict, hfin, ?_⟩
    filter_upwards [hex₀] with ω hω hs' hsH t ht
    obtain ⟨m, hm⟩ := hω hs' hsH t ht ENNReal.ofReal_lt_top
    exact hex ω _ ENNReal.ofReal_ne_top m hm

end Generic

section Sched

open GW2TipSystem.RootC24 GW2TipSystem.RootJ31

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **D12: the schedule instance's versions with strictly increasing caps** (successor of `exists_schedVersionsA_mono`):
finite, monotone at every sample, strictly increasing on the record event, exhausting eventually in the index. -/
theorem exists_schedVersionsA_strict :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  obtain ⟨R, V, hRV, hmono, hstrict, hfin, hex⟩ := exists_versionsA_fin_strict hfl hα (ae_source_noReturn h13 c)
    (measurable_schedW c r l a) (ae_schedW_regular h13 c r l a) c.s
  exact ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n),
    hstrict.mono fun ω hω hm n => hω hm (Nat.lt_succ_self n), hfin, hex⟩

include h13 in
/-- **D12 for the capped family: strictly increasing caps strictly below a cap gauge's life** (successor of
`GW2Sdz.exists_schedVersionsA_mono_gauge`). -/
theorem exists_schedVersionsA_strict_gauge (hs : 0 < c.s) {Gζ : GaugeReadout} (hGζm : ∀ t, Measurable (Gζ t))
    (hGζc : IsCausal Gζ) (hGζ0 : ∀ t p, 0 ≤ Gζ t p) {Lζ : Ω → ℝ≥0∞}
    (hζ : ∀ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞),
      RelativeDriverCoordinates c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α D L →
      ∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → 0 < Lζ ω ∧
        ContinuousOn (fun t => Gζ t (gb6Rec c.s c.W c.ζ ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) < Lζ ω → 0 < Gζ t (gb6Rec c.s c.W c.ζ ω, fun u => D u ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → (t : ℝ≥0∞) = Lζ ω → Gζ t (gb6Rec c.s c.W c.ζ ω, fun u => D u ω) = 0) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, Q3Stop.IsGB6RelVersionA c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      (∀ᵐ ω ∂c.P, gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s → ∀ n, V n ω < Lζ ω) ∧
      ∀ᵐ ω ∂c.P, (c.s : ℝ≥0∞) < c.ζ ω → c.α ω c.s ∈ H → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ω →
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < Lζ ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ω t) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  obtain ⟨R₀, V₀, hRV₀, hst₀, hlt₀, hex₀⟩ := exists_versionsA_of_capGauge_strict hfl hα (ae_source_noReturn h13 c)
    (measurable_schedW c r l a) (ae_schedW_regular h13 c r l a) c.s hs hGζm hGζc hGζ0 hζ
  obtain ⟨R, V, hRV, hmono, hstrict, hle, hfin, hex⟩ := exists_finite_family_strict hRV₀
    (fun ω => (hst₀ ω).monotone) (ae_of_all _ fun ω _ => hst₀ ω) (measurable_recOf_cfE hfl c.s).2
  refine ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n),
    hstrict.mono fun ω hω hm n => hω hm (Nat.lt_succ_self n), hfin, ?_, ?_⟩
  · filter_upwards [hlt₀] with ω hω hrec n using (hle n ω).trans_lt (hω hrec n)
  · filter_upwards [hex₀] with ω hω hs' hsH t ht hlt
    obtain ⟨m, hm⟩ := hω hs' hsH t ht hlt
    exact hex ω _ ENNReal.ofReal_ne_top m hm

end Sched

end InteractingSLE.Theorem14.GW2Rd
