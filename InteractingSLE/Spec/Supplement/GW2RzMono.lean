/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzCap
import InteractingSLE.Spec.Supplement.GW2SxCap
import InteractingSLE.Spec.Supplement.GW2TgMono
import InteractingSLE.Spec.Supplement.GW2RootK32Buffers


/-!
# GW2 at a root `x`: the monotone exhausting version family (decisions D8, D3, D3a; layer 4e)

Packet PROVE-GW2-ROOTX, round 3. RELDET's `GW2SxCap`, `GW2SyFin` and `GW2TgMono` at a root `x`:

* **`isRelVersionXA_ruleCap`** (an announced root-`x` version capped at an announced positive path rule; this is the
  form decision D3a's cap `min (V n) (D n)` takes at a root `x`), `isRelVersionXA_constCap`;
* **`exists_versionsXA_of_capGauge_mono`**: announced capped root-`x` versions with monotone stops for any cap gauge
  (GB6's positive-distance stops are monotone, `RootK32.monotone_localStop`);
* `ae_notMem_goodX_zero` (at `s = 0` the good records are null), `exists_versionsXA_mono_all`,
  `exists_finite_family_monoX`, **`exists_versionsXA_fin_mono`**: finite monotone stops exhausting eventually in the
  index every root-`x` clock value before the root-`x` contact, on the good records;
* **`exists_schedVersionsXA_mono`**: the same at the schedule instance at a root point `rootPt r.1 ≥ 0`, from
  Theorem 1.3 (the explored driver `schedW` is continuous from `0` everywhere).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rz

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.RelDrv.Version Supp8.GB6.HullId Supp8.GB6.SourceC
  GW2TipSystem GW2Rd

/-! ### Capping a root-`x` version at a path rule -/

section Cap

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Capping an announced root-`x` version at an announced positive path rule** (RELDET's
`GW2Rd.isGB6RelVersionA_ruleCap` at a root `x`). -/
theorem isRelVersionXA_ruleCap {P : Measure Ω} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsRelVersionXA x s P W' ζ' w γ α R V) (hrecm : Measurable (cfRec s W' ζ'))
    {ρ' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ'm : Measurable ρ') (hρ' : IsPathRule ρ')
    (hpos : ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → 0 < ρ' (cfRec s W' ζ' ω, fun u => R u ω))
    {ρa : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρam : ∀ n, Measurable (ρa n)) (hρa : ∀ n, IsPathRule (ρa n))
    (hρamono : ∀ x, Monotone fun n => ρa n x)
    (hann : ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s →
      (ρ' (cfRec s W' ζ' ω, fun u => R u ω) < V ω →
        ∀ n, ρa n (cfRec s W' ζ' ω, fun u => R u ω) < ρ' (cfRec s W' ζ' ω, fun u => R u ω)) ∧
        min (V ω) (⨆ n, ρa n (cfRec s W' ζ' ω, fun u => R u ω)) =
          min (V ω) (ρ' (cfRec s W' ζ' ω, fun u => R u ω))) :
    IsRelVersionXA x s P W' ζ' w γ α (ruleCapDrv R (ruleCapStop s W' ζ' ρ' R V))
      (ruleCapStop s W' ζ' ρ' R V) := by
  obtain ⟨⟨⟨hRm, hRc, hR0, -, hVm, -, hae⟩, ρ, hρm, hρ, hVρ⟩, ρs, hρsm, hρs, hρsfin, hρsmono, hannV⟩ := hver
  set V' := ruleCapStop s W' ζ' ρ' R V with hV'def
  set R' := ruleCapDrv R V' with hR'def
  have hRpm : Measurable fun ω => (cfRec s W' ζ' ω, fun u => R u ω) :=
    hrecm.prodMk (measurable_pi_iff.mpr hRm)
  have hV'm : Measurable V' := hVm.min (hρ'm.comp hRpm)
  have hR'm : ∀ t, Measurable (R' t) := measurable_ruleCapDrv hRm hRc hV'm
  have hR'pm : Measurable fun ω => (cfRec s W' ζ' ω, fun u => R' u ω) :=
    hrecm.prodMk (measurable_pi_iff.mpr hR'm)
  -- the capped rule
  set ρ'' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun x => min (ρ x) (ρ' x) with hρ''def
  have hρ''m : Measurable ρ'' := hρm.min hρ'm
  have hρ'' : IsPathRule ρ'' := isPathRule_min hρ hρ'
  have hV'ρ : ∀ᵐ ω ∂P, V' ω = ρ'' (cfRec s W' ζ' ω, fun u => R' u ω) := by
    filter_upwards [hVρ] with ω hω
    have e1 : V' ω = ρ'' (cfRec s W' ζ' ω, fun u => R u ω) := by
      simp only [hV'def, ruleCapStop, hρ''def, hω]
      rfl
    rw [e1]
    exact (hρ'' _ _ _ fun u hu => ruleCapDrv_agree ω u (e1 ▸ hu)).symm
  refine ⟨⟨⟨hR'm, continuous_ruleCapDrv hRc V', ruleCapDrv_zero hR0 V', fun ω t ht => ruleCapDrv_after ht,
    hV'm, fun t => ⟨_, measurableSet_le hρ''m measurable_const, isDetUpTo_pathRule_le hρ'' t, ?_⟩, ?_⟩,
    ρ'', hρ''m, hρ'', hV'ρ⟩, fun n x => min (ρs n x) (ρa n x), fun n => (hρsm n).min (hρam n),
    fun n => isPathRule_min (hρs n) (hρa n), fun n x => ne_top_of_le_ne_top (hρsfin n x) (min_le_left _ _),
    fun x => fun n m hnm => min_le_min (hρsmono x hnm) (hρamono x hnm), ?_⟩
  · -- the stopping sets
    filter_upwards [hV'ρ] with ω hω
    rw [hω]
  · -- positivity, coverage and the hull identity
    filter_upwards [hae, hpos] with ω hω hposω hm
    obtain ⟨hV0, hcov, hhull⟩ := hω hm
    refine ⟨lt_min hV0 (hposω hm), fun u hu => hcov u (hu.trans_le (min_le_left _ _)), fun t ht hle => ?_⟩
    rw [← hhull t ht (hle.trans (min_le_left _ _))]
    refine (fwdHull_eq_of_agree (continuous_ruleCapDrv hRc V' ω) (hRc ω) fun u hu => ?_)
    refine (ruleCapDrv_agree ω u ?_).symm
    calc (u : ℝ≥0∞) = ENNReal.ofReal (u : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ ENNReal.ofReal (max (clockX x s W' ζ' w t ω) 0) := ENNReal.ofReal_le_ofReal hu
      _ = ENNReal.ofReal (clockX x s W' ζ' w t ω) := by
          rcases le_total (clockX x s W' ζ' w t ω) 0 with h0 | h0
          · rw [max_eq_right h0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h0]
          · rw [max_eq_left h0]
      _ ≤ V' ω := hle
  · -- the announcement
    filter_upwards [hannV, hann] with ω hVω hρ'ω hm
    obtain ⟨hlt, hsup⟩ := hVω hm
    obtain ⟨hlt', hsup'⟩ := hρ'ω hm
    have hV'e : V' ω = min (V ω) (ρ' (cfRec s W' ζ' ω, fun u => R u ω)) := rfl
    -- the announcing rules read the same at `R` and at `R'`
    have hlt'' : ∀ n, min (ρs n (cfRec s W' ζ' ω, fun u => R u ω)) (ρa n (cfRec s W' ζ' ω, fun u => R u ω)) <
        V' ω := fun n => by
      rw [hV'e]
      by_cases hρV : ρ' (cfRec s W' ζ' ω, fun u => R u ω) < V ω
      · rw [min_eq_right hρV.le]
        exact (min_le_right _ _).trans_lt (hlt' hρV n)
      · rw [min_eq_left (not_lt.1 hρV)]
        exact (min_le_left _ _).trans_lt (hlt n)
    have he : ∀ n, min (ρs n (cfRec s W' ζ' ω, fun u => R' u ω)) (ρa n (cfRec s W' ζ' ω, fun u => R' u ω)) =
        min (ρs n (cfRec s W' ζ' ω, fun u => R u ω)) (ρa n (cfRec s W' ζ' ω, fun u => R u ω)) := fun n =>
      isPathRule_min (hρs n) (hρa n) _ _ _ fun u hu => ruleCapDrv_agree ω u (hu.trans (hlt'' n).le)
    simp only [he]
    refine ⟨hlt'', ?_⟩
    have hsup'' := iSup_inf_of_monotone (f := fun n => ρs n (cfRec s W' ζ' ω, fun u => R u ω))
      (g := fun n => ρa n (cfRec s W' ζ' ω, fun u => R u ω)) (hρsmono _) (hρamono _)
    rw [hsup'', hsup, hsup', hV'e]

/-- **An announced root-`x` version capped at a constant.** -/
theorem isRelVersionXA_constCap {P : Measure Ω} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {w : ℝ≥0 → Ω → ℝ} {γ α : Ω → ℝ≥0 → ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsRelVersionXA x s P W' ζ' w γ α R V) (hrecm : Measurable (cfRec s W' ζ')) {K : ℝ≥0}
    (hK : 0 < K) :
    IsRelVersionXA x s P W' ζ' w γ α (ruleCapDrv R (ruleCapStop s W' ζ' (fun _ => (K : ℝ≥0∞)) R V))
      (ruleCapStop s W' ζ' (fun _ => (K : ℝ≥0∞)) R V) :=
  isRelVersionXA_ruleCap hver hrecm measurable_const (fun _ _ _ _ => rfl)
    (ae_of_all _ fun _ _ => ENNReal.coe_pos.2 hK) (ρa := fun n _ => (capSeq K n : ℝ≥0∞))
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ hnm => ENNReal.coe_le_coe.2 (capSeq_mono K hnm))
    (ae_of_all _ fun _ _ => ⟨fun _ n => ENNReal.coe_lt_coe.2 (capSeq_lt hK n), by rw [iSup_capSeq hK]⟩)

end Cap

/-! ### Monotone exhausting versions at a root `x` -/

section Family

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
  {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}

/-- **Announced capped root-`x` versions with monotone stops, for any cap gauge** (RELDET's
`GW2Rd.exists_versionsA_of_capGauge_mono` at a root `x`). -/
theorem exists_versionsXA_of_capGauge_mono [IsProbabilityMeasure P]
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
      (∀ m, IsRelVersionXA x s P W' ζ' w γ α (R m) (V m)) ∧ (∀ ω, Monotone fun m => V m ω) ∧
      (∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ m, V m ω < Lζ ω) ∧
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        ENNReal.ofReal (clockX x s W' ζ' w t ω) < Lζ ω →
        ∃ m, ENNReal.ofReal (clockX x s W' ζ' w t ω) < V m ω := by
  have hrecm : Measurable (cfRec s W' ζ') := (measurable_recOf_cfE hF s).2
  obtain ⟨D, L, hC, hLive⟩ := exists_coordX_live hF hα hNR hcf hwm hwc hw0 hγ hs hx
  obtain ⟨D', L', Lg, g, G', hC', hrd, hle, -, hLg⟩ := exists_capReadoutX hC hrecm hLive hGζm hGζc hGζ0
    (hζ D L hC)
  refine ⟨fun m => coordDriver (D := D') (g := g) m, fun m ω => (coordStop (g := g) m ω : ℝ≥0∞),
    fun m => isRelVersionXA_capCoord hC' hrd hle m,
    fun ω _ _ hmm' => ENNReal.coe_le_coe.2 (RootK32.monotone_localStop (hrd.continuous ω) hmm'), ?_, ?_⟩
  · filter_upwards [hLg] with ω hω hm m
    exact (coordStop_lt_capX hrd m ω).trans_le ((hω hm).le.trans (min_le_right _ _))
  · filter_upwards [hLg, hC.relative] with ω hLgω hrel hm t ht htζ
    obtain ⟨-, hK⟩ := hrel hm
    obtain ⟨-, hlt, -⟩ := hK t ht
    have h1 : ENNReal.ofReal (clockX x s W' ζ' w t ω) < Lg ω := by
      rw [hLgω hm]
      exact lt_min hlt htζ
    exact GW2Rd.exists_lt_coordStop_cap (Wα := W') (ζα := ζ') hrd h1

/-- At `s = 0` the good records are null (the record's trace starts on the real line). -/
theorem ae_notMem_goodX_zero (hF : IsFlowLineDriver κ b J θ P h W' ζ')
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω)) (x : ℝ) :
    ∀ᵐ ω ∂P, cfRec 0 W' ζ' ω ∉ goodX x 0 := by
  filter_upwards [ae_gb6RecGood hF hα 0, hα] with ω hg hαω hm
  obtain ⟨-, hH⟩ := (mem_gb6TS_iff hg).2 hm.1
  rw [hαω.1] at hH
  exact (lt_irrefl (0 : ℝ)) hH

/-- **Monotone exhausting announced root-`x` versions, for every `s`.** -/
theorem exists_versionsXA_mono_all [IsProbabilityMeasure P]
    (hF : IsFlowLineDriver κ b J θ P h W' ζ') (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ m, IsRelVersionXA x s P W' ζ' w γ α (R m) (V m)) ∧ (∀ ω, Monotone fun m => V m ω) ∧
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        ∃ m, ENNReal.ofReal (clockX x s W' ζ' w t ω) < V m ω := by
  by_cases hs0 : s = 0
  · subst hs0
    have hnull := ae_notMem_goodX_zero hF hα (α := α) x
    -- a constant family: the clauses on the good records are vacuous
    refine ⟨fun _ _ _ => 0, fun _ _ => 1, fun _ => ⟨⟨⟨fun _ => measurable_const, fun _ => continuous_const,
      fun _ => rfl, fun _ _ _ => rfl, measurable_const, fun t => ?_, ?_⟩, fun _ => 1, measurable_const,
      fun _ _ _ _ => rfl, ae_of_all _ fun _ => rfl⟩, fun _ _ => 0, fun _ => measurable_const,
      fun _ _ _ _ _ => rfl, fun _ _ => ENNReal.zero_ne_top, fun _ => monotone_const, ?_⟩,
      fun _ => monotone_const, ?_⟩
    · refine ⟨{_y | (1 : ℝ≥0∞) ≤ t}, ?_, fun _ _ _ _ => Iff.rfl, ae_of_all _ fun _ => Iff.rfl⟩
      by_cases ht : (1 : ℝ≥0∞) ≤ t
      · simp only [ht, ofPred_true, MeasurableSet.univ]
      · simp only [ht, ofPred_false, MeasurableSet.empty]
    · filter_upwards [hnull] with ω hω hm using absurd hm hω
    · filter_upwards [hnull] with ω hω hm using absurd hm hω
    · filter_upwards [hnull] with ω hω hm using absurd hm hω
  · obtain ⟨R, V, hRV, hmono, -, hex⟩ := exists_versionsXA_of_capGauge_mono hF hα hNR hcf hwm hwc hw0 hγ
      (pos_iff_ne_zero.2 hs0) hx (Gζ := fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
      (fun _ _ => zero_le_one) (Lζ := fun _ => ⊤) fun _ _ _ => ae_of_all _ fun _ _ =>
        ⟨ENNReal.zero_lt_top, continuousOn_const, fun _ _ _ => zero_lt_one,
          fun _ _ ht => absurd ht ENNReal.coe_ne_top⟩
    exact ⟨R, V, hRV, hmono, hex.mono fun ω hω hm t ht => hω hm t ht ENNReal.ofReal_lt_top⟩

/-- **A monotone exhausting root-`x` family capped at `n + 1`: finite monotone stops, eventual exhaustion.** -/
theorem exists_finite_family_monoX {x : ℝ} {s : ℝ≥0} {R₀ : ℕ → ℝ≥0 → Ω → ℝ} {V₀ : ℕ → Ω → ℝ≥0∞}
    (hRV : ∀ m, IsRelVersionXA x s P W' ζ' w γ α (R₀ m) (V₀ m)) (hmono : ∀ ω, Monotone fun m => V₀ m ω)
    (hrecm : Measurable (cfRec s W' ζ')) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA x s P W' ζ' w γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ n ω, V n ω ≤ V₀ n ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ ω (y : ℝ≥0∞), y ≠ ⊤ → ∀ m, y < V₀ m ω → ∀ᶠ n in atTop, y < V n ω := by
  set K : ℕ → ℝ≥0 := fun n => (n : ℝ≥0) + 1 with hKdef
  have hK : ∀ n, 0 < K n := fun n => by positivity
  refine ⟨fun n => ruleCapDrv (R₀ n) (ruleCapStop s W' ζ' (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n)),
    fun n => ruleCapStop s W' ζ' (fun _ => (K n : ℝ≥0∞)) (R₀ n) (V₀ n),
    fun n => isRelVersionXA_constCap (hRV n) hrecm (hK n), fun ω n n' hnn' => ?_, fun n ω => min_le_left _ _,
    fun n ω => ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _), fun ω y hy m hym => ?_⟩
  · change min (V₀ n ω) (K n : ℝ≥0∞) ≤ min (V₀ n' ω) (K n' : ℝ≥0∞)
    refine min_le_min (hmono ω hnn') (ENNReal.coe_le_coe.2 ?_)
    simp only [hKdef]
    gcongr
  · obtain ⟨k, hk⟩ := exists_nat_gt y.toNNReal
    filter_upwards [eventually_ge_atTop (max m k)] with n hn
    change y < min (V₀ n ω) (K n : ℝ≥0∞)
    refine lt_min (hym.trans_le (hmono ω (le_of_max_le_left hn))) ?_
    rw [← ENNReal.coe_toNNReal hy]
    refine ENNReal.coe_lt_coe.2 (hk.trans_le ?_)
    simp only [hKdef]
    have hkn : (k : ℝ≥0) ≤ n := by exact_mod_cast le_of_max_le_right hn
    exact hkn.trans (le_add_of_nonneg_right zero_le_one)

/-- **Exhausting announced root-`x` versions with finite monotone stops, exhausting eventually, for every `s`.** -/
theorem exists_versionsXA_fin_mono [IsProbabilityMeasure P]
    (hF : IsFlowLineDriver κ b J θ P h W' ζ') (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (s : ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA x s P W' ζ' w γ α (R n) (V n)) ∧ (∀ ω, Monotone fun n => V n ω) ∧
      (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX x s W' ζ' w t ω) < V n ω := by
  obtain ⟨R₀, V₀, hRV₀, hmono₀, hex₀⟩ := exists_versionsXA_mono_all hF hα hNR hcf hwm hwc hw0 hγ s hx
  obtain ⟨R, V, hRV, hmono, -, hfin, hex⟩ := exists_finite_family_monoX hRV₀ hmono₀ (measurable_recOf_cfE hF s).2
  refine ⟨R, V, hRV, hmono, hfin, ?_⟩
  filter_upwards [hex₀] with ω hω hm t ht
  obtain ⟨m, hm'⟩ := hω hm t ht
  exact hex ω _ ENNReal.ofReal_ne_top m hm'

end Family

/-! ### The schedule instance at a root -/

section Sched

open GW2TipSystem.RootC24 GW2TipSystem.RootJ31

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **Exhausting announced root-`x` versions at the schedule instance** (decision D8; RELDET's
`GW2Rd.exists_schedVersionsA_mono` at the root point `x = rootPt r.1 ≥ 0`): finite monotone stops, exhausting
eventually in the index every root-`x` clock value before the root-`x` contact, on the good records. -/
theorem exists_schedVersionsXA_mono (hx : 0 ≤ rootPt r.1) :
    ∃ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
      (∀ n, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n)) ∧
      (∀ n ω, V n ω ≤ V (n + 1) ω) ∧ (∀ n ω, V n ω ≠ ⊤) ∧
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < V n ω := by
  obtain ⟨_, _, _, hfl, hα⟩ := source_counterflow c
  have hcf : ∀ᵐ ω ∂c.P, c.ζ ω = ⊤ ∧ Continuous (c.W · ω) ∧ c.W 0 ω = 0 := by
    filter_upwards [GW1LaunchClock.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, c.hζ] with ω h1 h2
    exact ⟨h2, h1.1, h1.2.1⟩
  have hγ : ∀ᵐ ω ∂c.P, IsGeneratingTrace (schedW c r l a · ω) ⊤ (schedTr c r l a ω) ∧
      Tendsto (fun t => ‖schedTr c r l a ω t‖) atTop atTop :=
    (ae_schedW_regular h13 c r l a).mono fun _ h => ⟨h.2.2.1, h.2.2.2⟩
  obtain ⟨R, V, hRV, hmono, hfin, hex⟩ := exists_versionsXA_fin_mono hfl hα (ae_source_noReturn h13 c) hcf
    (measurable_schedW c r l a) (continuous_schedW c r l a) (schedW_zero c r l a) hγ c.s hx
  exact ⟨R, V, hRV, fun n ω => hmono ω (Nat.le_succ n), hfin, hex⟩

end Sched

end InteractingSLE.Theorem14.GW2Rz
