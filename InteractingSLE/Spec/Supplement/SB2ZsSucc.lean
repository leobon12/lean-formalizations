/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ZsStop
import InteractingSLE.Spec.Supplement.SB2ZsFin

/-!
# SB2(1) at announced stops, part 2: the stop version and the identification at every stop

Packet PROVE-T14-SB2DRV (round 15, decision D4 = option (B)). SB2(1)'s version half at announced stops strictly
before the lifetime: a sequence of lifetime-generic line versions `ver m` (`SB2LineVersionG`, driver `W m` frozen at
the stop, every lifetime `Λ w = V m`), with stops that are record-path rules announced by finite record-path rules
(the shape of BW1's `IsBW1RelVersion`), each below the continuation threshold of its word type.

* **`SB2LineVersionS`**: the consumer's form of the successor version half (PROVE-AUX61-NOJUMP produces it; the
  construction of the stops is decision D10);
* **`ae_isStopDrvMatch_of_versionS`**: almost surely on the entrance event, for every `m`, the stop `V m` is at most
  the lifetime of the canonical driver code of (launch word, chart field), and `W m` is that code at the dyadic times
  before `V m`. K2's (S) and (L) at each stop are the proved kernel half (`sb2LineKernelRStatement_provedG`); the
  identification is `Cond.ae_isStopDrvMatch_of_hasSafeLaw_rule_on` (stopped K2, Aux. lemma 54 in its regular-stop
  form, Theorem 1.2) on every admissible type cell; on the entrance event the seed is admissible because
  `0 < V m ≤ thr`.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only. No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets
open Supp8.GB6.RelDrv (IsStopDrvMatch)
open Supp8.GB6.HullId (IsPathRule)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **SB2(1)'s line version at announced stops** (decision D4, option (B)): for every `m` a lifetime-generic line
version `ver m` whose lifetimes are all the stop `V m`; the stop is a record-path rule `V m = ρ m (record, W m)` of an
entrance-measurable record, announced on the entrance event by finite measurable record-path rules `ρs m n`,
nondecreasing in `n`; and on the type cell of every word type the stop is at most the continuation threshold of
`W m`. -/
structure SB2LineVersionS (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ)
    {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀) where
  ver : ℕ → SB2LineVersionG HP I D
  V : ℕ → Ω → ℝ≥0∞
  record : Ω → RecData
  record_meas : Measurable[D.marks] record
  ρ : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρs : ℕ → ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞
  ρ_meas : ∀ m, Measurable (ρ m)
  ρ_rule : ∀ m, IsPathRule (ρ m)
  ρs_meas : ∀ m n, Measurable (ρs m n)
  ρs_rule : ∀ m n, IsPathRule (ρs m n)
  ρs_fin : ∀ m n x, ρs m n x ≠ ⊤
  ρs_mono : ∀ m x, Monotone fun n => ρs m n x
  Λ_eq : ∀ m w, (ver m).Λ w = V m
  V_eq : ∀ m ω, V m ω = ρ m (record ω, fun s => (ver m).W s ω)
  ann : ∀ m, ∀ᵐ ω ∂P, ω ∈ D.event → (∀ n, ρs m n (record ω, fun s => (ver m).W s ω) < V m ω) ∧
    ⨆ n, ρs m n (record ω, fun s => (ver m).W s ω) = V m ω
  V_le_thr : ∀ m, ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ I.word D.event w →
    V m ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (ver m).W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω

/-- **The stop versions are the canonical driver code before every stop** (from Theorems 1.2–1.3 alone): almost
surely on the entrance event, for every `m`, `V m` is at most the lifetime of the canonical driver code of the launch
word and the chart field, and `W m` is that code at the dyadic times before `V m`. -/
theorem ae_isStopDrvMatch_of_versionS (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (S : SB2LineVersionS HP I D) :
    ∀ᵐ ω ∂P, ω ∈ D.event → ∀ m, IsStopDrvMatch (driverCode h12p HP.kappa_pos ψ
      (I.word ω, Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω)
      (S.V m ω) := by
  suffices hm : ∀ m, ∀ᵐ ω ∂P, ω ∈ D.event → IsStopDrvMatch (driverCode h12p HP.kappa_pos ψ
      (I.word ω, Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω))) (fun t => (S.ver m).W t ω)
      (S.V m ω) by
    filter_upwards [ae_all_iff.2 hm] with ω hω hF m using hω m hF
  intro m
  set Vd := S.ver m with hVd
  have hK := sb2LineKernelRStatement_provedG h12p h13 κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd
  have h𝒢m : D.marks ≤ mΩ := D.marks_le HP
  have hcw : Measurable[D.marks] I.word := I.word_measurable.mono D.past_le_marks le_rfl
  have hc : IsMeasChart D.marks I.chart := I.chart_measurable.mono D.past_le_marks
  have hFev : MeasurableSet[D.marks] D.event := D.measurableSet_event HP
  have hcell : ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      IsStopDrvMatch (driverCode h12p HP.kappa_pos ψ
        (I.word ω, Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω))) (fun t => Vd.W t ω)
        (S.V m ω) := by
    intro w hw
    obtain ⟨hlaw, hmem⟩ := hK w hw
    rw [S.Λ_eq m w] at hlaw hmem
    have hxL0 : ∀ ω i, cellXL κ ψ I.word w ω i ≤ 0 := fun ω => (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.1
    have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ I.word w ω j := fun ω =>
      (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.2
    have hxLa : ∀ ω, Antitone (cellXL κ ψ I.word w ω) := fun ω => (FCDet.isOrderedForceWord_typeXL (I.word ω)).1
    have hxRm : ∀ ω, Monotone (cellXR κ ψ I.word w ω) := fun ω =>
      (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.1
    have hword : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
        flowLineNL (I.word ω).fn (I.word ω).jumps 0 = w.1 ∧ flowLineNR (I.word ω).fn (I.word ω).jumps 0 = w.2.1 ∧
        truncWord w.1 w.2.1 (padFL κ ψ (I.word ω).fn (I.word ω).jumps) =
          ((cellXL κ ψ I.word w ω, cellXR κ ψ I.word w ω), (typedRhoL w, typedRhoR w)) :=
      Eventually.of_forall fun ω hω => k2_word_of_mem_wordTypeCell hω.1
    exact Cond.ae_isStopDrvMatch_of_hasSafeLaw_rule_on h12p h13 HP.kappa_pos Vd.marks_le
      (measurableSet_seedCell hcw hFev w) hcw (measurable_cellXL hcw w) (measurable_cellXR hcw w) hxL0 hxR0 hxLa
      hxRm hword Vd.W_zero Vd.W_cont Vd.W_adapted HP.field.1 hc.1 (fun z => h𝒢m _ (hc.2.2.2.1 z))
      (fun z => (hc.2.2.2.2.1 z).mono h𝒢m le_rfl) (fun z => (hc.2.2.2.2.2.2 z).mono h𝒢m le_rfl) hc.2.1
      (fun φ => (integrableOn_chartPairing HP I φ).mono_set
        ((seedCell_subset w).trans D.event_subset)) S.record_meas (S.ρ_meas m) (S.ρ_rule m) (S.ρs_meas m)
      (S.ρs_rule m) (S.ρs_fin m) (S.ρs_mono m) (S.V_eq m)
      ((S.ann m).mono fun ω h hω => h (seedCell_subset w hω))
      ((S.V_le_thr m w hw).mono fun ω h hω => h hω.1) hlaw hmem
  filter_upwards [(ae_ball_iff I.types_countable).2 hcell, I.cover,
    (ae_ball_iff I.types_countable).2 (S.V_le_thr m), S.ann m] with ω hcode hcov hle hann hF
  obtain ⟨w₀, hw₀e⟩ : ∃ w₀, angleWordType κ ψ (I.word ω) = w₀ := ⟨_, rfl⟩
  have hw₀ : w₀ ∈ I.types := hw₀e ▸ hcov (D.event_subset hF)
  have hcellω : ω ∈ wordTypeCell κ ψ I.word D.event w₀ := ⟨hF, hw₀e⟩
  have hxL0 : ∀ ω i, cellXL κ ψ I.word w₀ ω i ≤ 0 := fun ω =>
    (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.1
  have hxR0 : ∀ ω j, 0 ≤ cellXR κ ψ I.word w₀ ω j := fun ω =>
    (FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.2
  have hpos : 0 < FCDet.thr (typedRhoL w₀) (typedRhoR w₀) Vd.W (cellXL κ ψ I.word w₀) (cellXR κ ψ I.word w₀) ω :=
    lt_of_lt_of_le (lt_of_le_of_lt zero_le ((hann hF).1 0)) (hle w₀ hw₀ hcellω)
  exact hcode w₀ hw₀ ⟨hcellω, not_seed_of_thr_pos Vd.W_zero Vd.W_cont hxL0 hxR0 hpos⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] mΩ in
/-- **A stopped match and a full match of one code agree before the stop** (deterministic): the stop is at most the
full lifetime, and two drivers continuous before their lifetimes with the same dyadic values agree. -/
theorem eqOn_of_isStopDrvMatch_of_isDriverCodeMatch {p : Sec2.Assembly.PCode × ℝ≥0∞} {W Wc : ℝ≥0 → ℝ}
    {e L : ℝ≥0∞} (hm : IsStopDrvMatch p W e) (hc : IsDriverCodeMatch p Wc L)
    (hW : ContinuousOn W {t | (t : ℝ≥0∞) < e}) (hWc : ContinuousOn Wc {t | (t : ℝ≥0∞) < L}) :
    e ≤ L ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < e → W t = Wc t := by
  obtain ⟨hL, -, hd⟩ := hc
  have heL : e ≤ L := hL ▸ hm.1
  refine ⟨heL, Supp8.GB6.RelDrv.eqOn_of_dyad_lt hW (hWc.mono fun t ht => lt_of_lt_of_le ht heL)
    fun n k hnk => ?_⟩
  rw [hm.2 n k hnk, hd n k (lt_of_lt_of_le hnk heL)]

/-- **SB2(1)'s identification output at the stops** (the input of the endpoint `Vn.ae_relEndpoint_of_identified` and
of E7's assembly): for every driver `Wc` continuous before `L` that matches the canonical driver code with lifetime
`L` almost surely on the entrance event (for instance the landed canonical conditional driver of the launch chart),
almost surely on the entrance event every stop is at most `L` and `W m = Wc` before `V m`. -/
theorem ae_eqOn_of_versionS (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    (S : SB2LineVersionS HP I D) {Wc : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}
    (hWc : ∀ ω, ContinuousOn (fun t => Wc t ω) {t | (t : ℝ≥0∞) < L ω})
    (hcode : ∀ᵐ ω ∂P, ω ∈ D.event → IsDriverCodeMatch (driverCode h12p HP.kappa_pos ψ
      (I.word ω, Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω))) (fun t => Wc t ω) (L ω)) :
    ∀ᵐ ω ∂P, ω ∈ D.event → ∀ m, S.V m ω ≤ L ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → (S.ver m).W t ω = Wc t ω := by
  filter_upwards [ae_isStopDrvMatch_of_versionS h12p h13 HP I hu₀ D S, hcode] with ω hm hc hF m
  exact eqOn_of_isStopDrvMatch_of_isDriverCodeMatch (hm hF m) (hc hF) ((S.ver m).W_cont ω).continuousOn (hWc ω)

end InteractingSLE.Theorem14.SB.Lv
