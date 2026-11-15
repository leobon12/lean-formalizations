/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SxTime
import InteractingSLE.Spec.Supplement.GW2JDetR6Actual
import InteractingSLE.Spec.Supplement.GW2JDetR6Prefix

/-!
# GW2's stage identity: announced GB6 versions stopped at a physical time

Packet PROVE-GW2-RELDET, ruling R106. Every announced R-form version `(R, V)` of GB6's relative exploration can be
stopped at the relative clock of a deterministic physical time `Δ > 0` of the explored curve
(`isGB6RelVersionA_timeCap`): cap `V` at JOINTDET's physical-capacity level rule (`GW2SxTime.timeCapRule`) with
`GW2SxCap.isGB6RelVersionA_ruleCap`. Almost surely on the interior-tip event the capped stop is
`min(V, a(Δ))` if `Δ` precedes the first contact `T_c`, and `V` otherwise.

* `ae_timeCap_sample`: almost surely on the interior-tip event, the relative clock is a clock before `T_c`, and the
  time cap satisfies `min(V, timeCapRule Δ) = min(V, capClock Δ)` for every `Δ`. Proved from the two generating
  traces (JOINTDET's inverse-capacity chain) and the version's own hull identity, which makes the rational prefix
  capacities read the physical times.
* `timeCap_announce`: the announcing physical times `Δ_k ↑ Δ` (`Δ_k < Δ`) give the announcement the cap lemma needs.

There is no new hypothesis beyond the regularity of the two curves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId Sec7.Lemma71I GW2JDetR3

/-! ### The announcing physical times -/

/-- The announcing physical times `Δ_k = Δ (k + 1)/(k + 2)`. -/
def capSeq (Δ : ℝ≥0) (k : ℕ) : ℝ≥0 := Δ * Q3Stop.annCap 0 k

theorem capSeq_lt {Δ : ℝ≥0} (hΔ : 0 < Δ) (k : ℕ) : capSeq Δ k < Δ := by
  have h := Q3Stop.annCap_lt 0 k
  rw [Nat.cast_zero, zero_add] at h
  exact mul_lt_of_lt_one_right hΔ h

theorem capSeq_mono (Δ : ℝ≥0) : Monotone (capSeq Δ) := fun _ _ hkl => by
  unfold capSeq
  gcongr
  exact Q3Stop.annCap_mono 0 hkl

theorem exists_lt_capSeq {Δ : ℝ≥0} (hΔ : 0 < Δ) {t : ℝ≥0} (ht : t < Δ) : ∃ k, t < capSeq Δ k := by
  have h1 : t / Δ < ((0 : ℕ) : ℝ≥0) + 1 := by
    rw [Nat.cast_zero, zero_add]
    exact (div_lt_one hΔ).2 ht
  obtain ⟨N, hN⟩ := Q3Stop.exists_lt_annCap 0 h1
  refine ⟨N, ?_⟩
  have h2 := hN N le_rfl
  rw [div_lt_iff₀ hΔ] at h2
  unfold capSeq
  rw [mul_comm]
  exact h2

/-! ### The announcement along one sample -/

theorem eq_of_min_lt {V x : ℝ≥0∞} (h : min V x < V) : min V x = x ∧ x < V := by
  rcases min_lt_iff.1 h with h' | h'
  · exact absurd h' (lt_irrefl _)
  · exact ⟨min_eq_right h'.le, h'⟩

/-- **The announcement of the time cap along one sample.** -/
theorem timeCap_announce {V Tc : ℝ≥0∞} {a : ℝ≥0 → ℝ} {ρ : ℝ≥0 → ℝ≥0∞} (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc}) (hac : ContinuousOn a {t | (t : ℝ≥0∞) < Tc})
    (hcov : ∀ u : ℝ≥0, (u : ℝ≥0∞) < V → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ (u : ℝ) < a t)
    (hmin : ∀ Δ', min V (ρ Δ') = min V (capClock Tc a Δ')) {Δ : ℝ≥0} (hΔ : 0 < Δ) :
    (ρ Δ < V → ∀ n, (Finset.range (n + 1)).sup (fun k => ρ (capSeq Δ k)) < ρ Δ) ∧
      min V (⨆ n, (Finset.range (n + 1)).sup fun k => ρ (capSeq Δ k)) = min V (ρ Δ) := by
  have hk : ∀ k, (capSeq Δ k : ℝ≥0∞) < Δ := fun k => ENNReal.coe_lt_coe.2 (capSeq_lt hΔ k)
  constructor
  · intro hlt n
    have h1 := hmin Δ
    rw [min_eq_right hlt.le] at h1
    obtain ⟨hcc, hcV⟩ := eq_of_min_lt (h1 ▸ hlt)
    have hΔT : (Δ : ℝ≥0∞) < Tc := by
      by_contra hT
      simp only [capClock, hT, ↓reduceIte] at hcV
      exact absurd hcV (not_lt.2 le_top)
    have hc : capClock Tc a Δ = ENNReal.ofReal (a Δ) := by simp only [capClock, hΔT, ↓reduceIte]
    have hρΔ : ρ Δ = ENNReal.ofReal (a Δ) := by rw [h1, hcc, hc]
    have haΔ : 0 < a Δ := by
      rw [← ha0]
      exact ham (show ((0 : ℝ≥0) : ℝ≥0∞) < Tc from (ENNReal.coe_le_coe.2 zero_le).trans_lt hΔT) hΔT hΔ
    have hlt' : ∀ k, ρ (capSeq Δ k) < ρ Δ := by
      intro k
      have hkT : (capSeq Δ k : ℝ≥0∞) < Tc := (hk k).trans hΔT
      have hak : ENNReal.ofReal (a (capSeq Δ k)) < ENNReal.ofReal (a Δ) :=
        (ENNReal.ofReal_lt_ofReal_iff haΔ).2 (ham hkT hΔT (capSeq_lt hΔ k))
      have hkV : ENNReal.ofReal (a (capSeq Δ k)) < V := hak.trans (hc ▸ hcV)
      have h2 := hmin (capSeq Δ k)
      simp only [capClock, hkT, ↓reduceIte, min_eq_right hkV.le] at h2
      obtain ⟨h3, -⟩ := eq_of_min_lt (h2 ▸ hkV)
      rw [← h3, h2, hρΔ]
      exact hak
    exact (Finset.sup_lt_iff (bot_lt_iff_ne_bot.2 (ne_bot_of_gt (hlt' 0)))).2 fun k _ => hlt' k
  · -- the supremum of the running maxima is the supremum of the announcing values
    have hsup : (⨆ n, (Finset.range (n + 1)).sup fun k => ρ (capSeq Δ k)) = ⨆ k, ρ (capSeq Δ k) := by
      refine le_antisymm (iSup_le fun n => Finset.sup_le fun k _ => le_iSup (fun k => ρ (capSeq Δ k)) k)
        (iSup_le fun k => ?_)
      exact (Finset.le_sup (f := fun k => ρ (capSeq Δ k)) (Finset.mem_range.2 (Nat.lt_succ_self k))).trans
        (le_iSup (fun n => (Finset.range (n + 1)).sup fun k => ρ (capSeq Δ k)) k)
    have hcap : min V (⨆ k, capClock Tc a (capSeq Δ k)) = min V (capClock Tc a Δ) := by
      by_cases hΔT : (Δ : ℝ≥0∞) < Tc
      · have hkT : ∀ k, (capSeq Δ k : ℝ≥0∞) < Tc := fun k => (hk k).trans hΔT
        have e : (⨆ k, capClock Tc a (capSeq Δ k)) = capClock Tc a Δ := by
          simp only [capClock, hkT, hΔT, ↓reduceIte]
          refine le_antisymm (iSup_le fun k => ENNReal.ofReal_le_ofReal
            (ham.monotoneOn (hkT k) hΔT (capSeq_lt hΔ k).le)) (le_of_forall_lt fun c hc => ?_)
          have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < Tc} := isOpen_lt ENNReal.continuous_coe continuous_const
          have hcont : ContinuousAt (fun t => ENNReal.ofReal (a t)) Δ :=
            ENNReal.continuous_ofReal.continuousAt.comp (hac.continuousAt (hopen.mem_nhds hΔT))
          obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds (hcont.eventually (lt_mem_nhds hc)) ⟨0, hΔ⟩
          obtain ⟨k, hlk⟩ := exists_lt_capSeq hΔ hl
          exact lt_iSup_iff.2 ⟨k, hsub ⟨hlk, (capSeq_lt hΔ k).le⟩⟩
        rw [e]
      · have e : capClock Tc a Δ = ⊤ := by simp only [capClock, hΔT, ↓reduceIte]
        rw [e, min_top_right]
        refine min_eq_left (le_of_forall_lt fun c hc => ?_)
        obtain ⟨u, hcu, huV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
        obtain ⟨t, htT, hut⟩ := hcov u huV
        have htΔ : t < Δ := ENNReal.coe_lt_coe.1 (htT.trans_le (not_lt.1 hΔT))
        obtain ⟨k, htk⟩ := exists_lt_capSeq hΔ htΔ
        refine hcu.trans (lt_iSup_iff.2 ⟨k, ?_⟩)
        by_cases hkT : (capSeq Δ k : ℝ≥0∞) < Tc
        · simp only [capClock, hkT, ↓reduceIte]
          have hat : (u : ℝ) < a (capSeq Δ k) := hut.trans_le (ham.monotoneOn htT hkT htk.le)
          rw [← ENNReal.ofReal_coe_nnreal]
          exact (ENNReal.ofReal_lt_ofReal_iff (u.coe_nonneg.trans_lt hat)).2 hat
        · simp only [capClock, hkT, ↓reduceIte]
          exact ENNReal.coe_lt_top
    rw [hsup, inf_iSup_eq, hmin Δ, ← hcap, inf_iSup_eq]
    exact iSup_congr fun k => hmin (capSeq Δ k)

/-! ### Almost surely along the samples -/

section Sample

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}

/-- **The time cap along almost every sample of a GB6 version.** -/
theorem ae_timeCap_sample (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {s : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hver : IsGB6RelVersion s P W Wα ζα γ α R V) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      0 < V ω ∧ gb6Clock s W Wα ω 0 = 0 ∧
      StrictMonoOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      ContinuousOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω ∧ (u : ℝ) < gb6Clock s W Wα ω t) ∧
      ∀ Δ : ℝ≥0, min (V ω) (timeCapRule s Δ (gb6Rec s Wα ζα ω, fun u => R u ω)) =
        min (V ω) (capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) := by
  obtain ⟨-, hRc, hR0, -, -, -, hae⟩ := hver
  filter_upwards [ae_driver_zero_continuousOn hF, hα, hW, hae] with ω hfl hαω hWω haeω hs hsH
  obtain ⟨h0, hc⟩ := hfl
  obtain ⟨hWc, hW0, hγ⟩ := hWω
  obtain ⟨hV0, hcov, hhull⟩ := haeω hs hsH
  have hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ⊤} := hWc.continuousOn
  have hTc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc s γ α ω →
      (t : ℝ≥0∞) < min (gb6Tc s γ α ω) ⊤ := fun t ht => lt_min ht ENNReal.coe_lt_top
  obtain ⟨-, -, ha0, hm, hcont, -, -⟩ :=
    exists_inverse_capacity_chain Wα ζα ω hαω hc h0 hs hsH hγ hw hW0 ENNReal.zero_lt_top
  have he : EqOn (rdrv (gb6Rec s Wα ζα ω)) (Ito.rpath (Wα · ω)) (Icc 0 s) := GaugeE.record_prefix_eq s h0 hc hs
  have hclock : (fun t : ℝ≥0 => relClock (rdrv (gb6Rec s Wα ζα ω)) s (Ito.rpath (W · ω)) t) =
      gb6Clock s W Wα ω := by
    funext t
    rw [relClock_eq_of_eqOn s.coe_nonneg he]
    rfl
  have ha0' : gb6Clock s W Wα ω 0 = 0 := by
    rw [← hclock]
    exact ha0
  have hm' : StrictMonoOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} := by
    rw [← hclock]
    exact hm.mono fun t ht => hTc t ht
  have hc' : ContinuousOn (gb6Clock s W Wα ω) {t | (t : ℝ≥0∞) < gb6Tc s γ α ω} := by
    rw [← hclock]
    exact hcont.mono fun t ht => hTc t ht
  -- the rational prefix capacities of the relative driver read the physical times
  have hread : ∀ (q : ℚ≥0) (t : ℝ≥0), (t : ℝ≥0∞) < gb6Tc s γ α ω → gb6Clock s W Wα ω t = ((q : ℝ≥0) : ℝ) →
      ((q : ℝ≥0) : ℝ≥0∞) ≤ V ω →
      prefixCapacity s q (gb6Rec s Wα ζα ω) (killedCode ((fun u => R u ω), ⊤)) = t := by
    intro q t ht hat hqV
    have hle : ENNReal.ofReal (gb6Clock s W Wα ω t) ≤ V ω := by
      rw [hat, ENNReal.ofReal_coe_nnreal]
      exact hqV
    have hK : QuantumZipper.fwdHull (Ito.rpath fun u => R u ω) ((q : ℝ≥0) : ℝ) =
        relMap (Ito.rpath (Wα · ω)) s '' QuantumZipper.fwdHull (Ito.rpath (W · ω)) t := by
      have h1 := hhull t ht hle
      rw [hat] at h1
      exact h1
    have hmap : relMap (rdrv (gb6Rec s Wα ζα ω)) s = relMap (Ito.rpath (Wα · ω)) s :=
      GaugeE.record_relMap_eq s h0 hc hs
    have hinv : relInv (rdrv (gb6Rec s Wα ζα ω)) s '' QuantumZipper.fwdHull (Ito.rpath fun u => R u ω)
        ((q : ℝ≥0) : ℝ) = QuantumZipper.fwdHull (Ito.rpath (W · ω)) t := by
      rw [hK, ← hmap]
      exact relInv_image_relMap_before_contact Wα ζα ω hαω hc h0 hs hγ hw hW0 (hTc t ht)
    unfold prefixCapacity
    rw [GW2JDetR6.physicalCapacity_live_prefix s _ (e := ((fun u => R u ω), ⊤)) (hRc ω).continuousOn (hR0 ω)
      ENNReal.coe_lt_top le_rfl hγ hw hW0 ENNReal.coe_lt_top hinv, ENNReal.ofReal_coe_nnreal]
  exact ⟨hV0, ha0', hm', hc', hcov, fun Δ => min_timeCapRule ha0' hm' hc' hread hcov Δ⟩

/-- **Announced GB6 versions stopped at a physical time.** -/
theorem isGB6RelVersionA_timeCap (hF : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (Wα · ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (W · ω) ⊤ (γ ω))
    {s : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} (hver : Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α R V)
    {Δ : ℝ≥0} (hΔ : 0 < Δ) :
    Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (ruleCapDrv R (ruleCapStop s Wα ζα (timeCapRule s Δ) R V))
      (ruleCapStop s Wα ζα (timeCapRule s Δ) R V) ∧
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ruleCapStop s Wα ζα (timeCapRule s Δ) R V ω = min (V ω) (capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) := by
  have hrecm : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hF s).2
  have hS := ae_timeCap_sample hF hα hW hver.1.1
  have hgood := ae_gb6RecGood hF hα s
  set ρa : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
    fun n x => (Finset.range (n + 1)).sup fun k => timeCapRule s (capSeq Δ k) x with hρadef
  have hρam : ∀ n, Measurable (ρa n) := by
    intro n
    have e : ρa n = fun x => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k => timeCapRule s (capSeq Δ k) x) := funext fun x => (Finset.sup'_eq_sup _ _).symm
    rw [e]
    exact Finset.measurable_range_sup'' fun k _ => measurable_timeCapRule s _
  have hρa : ∀ n, IsPathRule (ρa n) := fun n =>
    Q3Stop.isPathRule_finsetSup (fun k => isPathRule_timeCapRule s _) _
  have hρamono : ∀ x, Monotone fun n => ρa n x := fun x n m hnm =>
    Finset.sup_mono (Finset.range_subset_range.2 (Nat.succ_le_succ hnm))
  refine ⟨isGB6RelVersionA_ruleCap hver hrecm (measurable_timeCapRule s Δ) (isPathRule_timeCapRule s Δ) ?_
    hρam hρa hρamono ?_, ?_⟩
  · -- positivity of the cap
    filter_upwards [hS] with ω hω hs hsH
    obtain ⟨hV0, ha0, ham, -, -, hmin⟩ := hω hs hsH
    have hpos : 0 < min (V ω) (capClock (gb6Tc s γ α ω) (gb6Clock s W Wα ω) Δ) := by
      refine lt_min hV0 ?_
      unfold capClock
      split_ifs with hΔT
      · refine ENNReal.ofReal_pos.2 ?_
        rw [← ha0]
        exact ham (show ((0 : ℝ≥0) : ℝ≥0∞) < gb6Tc s γ α ω from
          (ENNReal.coe_le_coe.2 zero_le).trans_lt hΔT) hΔT hΔ
      · exact ENNReal.zero_lt_top
    rw [← hmin Δ] at hpos
    exact hpos.trans_le (min_le_right _ _)
  · -- the announcement
    filter_upwards [hS, hgood] with ω hω hg hm
    obtain ⟨hs, hsH⟩ := (mem_gb6TS_iff hg).2 hm
    obtain ⟨-, ha0, ham, hac, hcov, hmin⟩ := hω hs hsH
    exact timeCap_announce (ρ := fun Δ' => timeCapRule s Δ' (gb6Rec s Wα ζα ω, fun u => R u ω)) ha0 ham hac hcov
      hmin hΔ
  · -- the capped stop
    filter_upwards [hS] with ω hω hs hsH
    exact (hω hs hsH).2.2.2.2.2 Δ

end Sample

end InteractingSLE.Theorem14.GW2Rd
