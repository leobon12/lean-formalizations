/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefChartReg
import InteractingSLE.Spec.Sec7.Lemma725RefSafeWire

/-!
# Lemma 7.25's pocket field data with the pocket chart kept explicit

Packet PROVE-LEMMA725REF4, item 1 (a)–(b). Specification §7.4, Aux. lemmas 119, 122, 124–125 and Lemma 7.25's proof
(`source/spec/p385-432.md` L171–L250, L489–L515, pp. 393–398, 413–414); Aux. lemmas 35–36
(`source/spec/p145-192.md` L908–L940, `source/spec/p193-240.md` L1–L78).

PROVE-LEMMA725REF3's named input `Lemma725RefSafe.PocketChartFieldStatement κ r_L r_R` asks for the pocket of Lemma 7.25
with a pocket chart `c` and its field-level data **on the same sample space**: the physical kernel `PocketKernel` and
the mean identification `PocketMeanIdent` for that chart, the marked union law of the canonical set `ℍ ∖ activeDom`,
the chart regularity on all of `Ω`, the field `h` with `h − u` a zero-boundary GFF, and the determination `hdet`. The
landed strip-level glue (PROVE-STRIPSYS26–35: `pocketStopChartLaw_of_sideLimit`, `pocketUnionPtChartLaw_of_stop`,
`pocketKernel_of_unionLaw`, `pocketMeanIdent_of_pt`) produces exactly these objects, but each layer hides the chart
behind an `∃`. Here the last layers are replicated with the chart explicit — the shifted canonical pocket chart
`c = shiftChart (pChart A C ψ) n` of PROVE-STRIPSYS35 — every mathematical step being a call to a landed lemma, and
the chart regularity comes from `Lemma725RefChartReg`.

## Main results

* **`pocketChartData_of_stop`**: for pocket data on `A` (open pocket `C ⊆ ℍ`, a conformal bijection `ψ : C → ℍ`
  measurable at fixed points for the walls, the ambient-domain identity `ψ(C ∩ (ℍ ∖ F_q)) = ℍ ∖ K^{rel}_q`), a
  walls-measurable branch integer `n` and a constant `a`, the two remaining field-level inputs at every relative
  capacity time (`PocketStopUnionLaw`, `PocketStopSideLimit` for the shifted canonical chart) give, for the field
  `h₀ + u` and the chart `c`, the physical kernel, the mean identification, the hitting measurability and the marked
  locality of `ℍ ∖ activeDom`, and the chart regularity — the hypotheses of `PocketChartFieldStatement` other than the
  word, the traversal and `hdet`;
* **`pocketChartFieldStatement_of_stop`**: hence `PocketChartFieldStatement κ r_L r_R`, given in addition the word, the
  traversal and marks, and the determination `hdet` of the killed relative history by a walls' record and the pocket
  field `chartTransport c 1 a χ(κ) (h₀ + u)`.

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex
open QuantumZipper (H fwdHull zeroGFFTestCov chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma725RefChart

open Restart.DomainMarkov Restart.DomainMarkov.K2 PhaseSel PocketCoupling LocalSets Coupling MartChar
  PocketTraversal Lemma71C LawUnique PocketStop WholeField PocketStopField Lemma725RefSafe

universe u

section Gen

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The field-level pocket data for the explicit shifted canonical pocket chart** (the content of
`pocketStopChartLaw_of_sideLimit` and `pocketUnionPtChartLaw_of_stop` with the chart kept explicit): the chart is
regular on all of `Ω` (conformal; walls-measurable domain events, forward values and lift values; continuous harmonic
lift), the canonical sets `ℍ ∖ activeDom` are hitting-measurable and history-local for the centred field, and there are
σ-algebras `𝓜_q` and means `M_q` with the physical kernel and the mean identification for the field `h₀ + u`. -/
theorem pocketChartData_of_stop [IsProbabilityMeasure P] {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀
      u (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q) :
    (∀ ω, (shiftChart (pChart A C ψ ω) (n ω)).IsConformal) ∧
    (∀ z, MeasurableSet[𝓦] {ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}) ∧
    (∀ z, Measurable[𝓦] ({ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}.indicator
      fun ω => (shiftChart (pChart A C ψ ω) (n ω)).1 z)) ∧
    (∀ z, Measurable[𝓦] ({ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}.indicator
      fun ω => (shiftChart (pChart A C ψ ω) (n ω)).2.2 z)) ∧
    (∀ ω, ContinuousOn (shiftChart (pChart A C ψ ω) (n ω)).2.2 (shiftChart (pChart A C ψ ω) (n ω)).dom) ∧
    (∀ ω, InnerProductSpace.HarmonicOnNhd (shiftChart (pChart A C ψ ω) (n ω)).2.2
      (shiftChart (pChart A C ψ ω) (n ω)).dom) ∧
    (∀ s, Measurable[mΩ, hittingSigma] (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) s)) ∧
    (∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s)
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) s) h₀ P) ∧
    ∃ (𝓜 : ℝ≥0 → MeasurableSpace Ω) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens),
      PocketKernel 𝓦 P A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω))
        (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) 𝓜 M ∧
      PocketMeanIdent κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a (chiC κ) M := by
  set c : Ω → Chart := fun ω => shiftChart (pChart A C ψ ω) (n ω) with hcdef
  have hprops := pChart_props hCo hCH hψ
  have hcc : ∀ ω, (c ω).IsConformal := fun ω => (hprops ω).2.2.1
  have hpch := isPocketChartOn_pChart (mΩ := 𝓦) hA hCo hCH hψ hCm hψm
  have hcOn : IsPocketChartOn 𝓦 A C ψ c := isPocketChartOn_shift hpch.1 hCm hn
  have hℓ : ∀ ω ∈ A, IsDerivLog (c ω).1 (fun z => pLog A C ψ ω z - n ω * (2 * π * I)) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (pLog A C ψ ω z - n ω * (2 * π * I)).im := fun ω hω =>
    ⟨isDerivLog_sub_int (hpch.2 ω hω).1 (n ω), fun z hz => by
      change (pChart A C ψ ω).2.2 z - 2 * π * (n ω : ℝ) = _
      rw [im_sub_int_mul, (hpch.2 ω hω).2 z hz]⟩
  have hinj : ∀ ω ∈ A, InjOn (ψ ω) (C ω) := fun ω hω => (hψ ω hω).2.injOn
  have hpre : ∀ q : ℝ≥0, locPrefixSigma 𝓦 A γ q ≤ mΩ := PocketUnionPt.locPrefixSigma_le h𝓦 hA hγ hγm
  -- `pocketStopChartLaw_of_sideLimit`, with the chart explicit
  have hact : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → activeDom A γ c q ω = C ω ∩ (H \ F q ω) :=
    fun q ω hω hq => PocketUnionPt.activeDom_eq_inter hω hq (hcOn.1 ω hω).1 (hcOn.1 ω hω).2.1
      (hcOn.1 ω hω).2.2.1 (hinj ω hω) (hgeo q ω hω hq)
  have hlaw : ∀ q : ℝ≥0, PocketUnionPt.PocketStopLaw 𝓦 P A γ C (F q) h₀ (activeCompl A γ c q) q := fun q =>
    pocketStopLaw_activeCompl (hpre q) (hact q) hCo (hFo q) (hU q)
  have hloc : ∀ q, IsLocalSet (activeCompl A γ c q) h₀ P := fun q =>
    ((isLocalSet_tfae hh₀ (hlaw q).1 (hlaw q).2.1).out 1 4).1
      (IsHistoryAvoidanceLocal.isAvoidanceLocal (hlaw q).2.2.1)
  have h𝔥 : ∀ φ : TestOn upperHalfPlaneOpens, smoothDist upperHalfPlaneOpens u φ = ∫ z, u z * φ z :=
    smoothDist_eq_integral hu
  have hmeanAt : ∀ q : ℝ≥0, PocketUnionPt.PocketStopMeanAt κ ρL ρR P A γ xL xR c a (chiC κ) h₀
      (smoothDist upperHalfPlaneOpens u) (activeCompl A γ c q) (fun ω => C ω ∩ (H \ F q ω)) q := by
    intro q
    refine pocketStopMeanAt_of_sideLimit hh₀ (hlaw q).1 (hloc q) (fun ω hω hq => ?_)
      (fun ω hω hq => (hact q ω hω hq).symm) hγ (fun ω hω => ⟨(hcOn.1 ω hω).1, (hℓ ω hω).1, (hℓ ω hω).2⟩) hu hub
      h𝔥 (hside q)
    rw [activeCompl, sdiff_sdiff_cancel_left]
    rw [hact q ω hω hq]
    exact inter_subset_right.trans sdiff_subset
  -- `pocketUnionPtChartLaw_of_stop`, with the chart explicit
  have hgex : ∀ q, ∃ g, IsLocalSetMean (activeCompl A γ c q) h₀ P g := fun q =>
    IsLocalSet.exists_isLocalSetMean hh₀ (hlaw q).1 (hloc q)
  choose g hg using hgex
  have h𝓦ℋ : ∀ q : ℝ≥0, ∀ s, MeasurableSet[𝓦] s → MeasurableSet[locPrefixSigma 𝓦 A γ q] s :=
    fun q s hs => le_sup_left (b := MeasurableSpace.generateFrom _) _ hs
  have hUL : PocketUnionLaw 𝓦 P A γ c h₀ (fun q => activeCompl A γ c q) (fun q => locPrefixSigma 𝓦 A γ q) g := by
    intro q
    obtain ⟨hKm, -, hhist, hgeoK⟩ := hlaw q
    refine ⟨hKm, hpre q, hloc q, hhist, hg q, le_sup_right.trans le_sup_left, ?_, ?_⟩
    · exact PocketUnionPt.measurable_compl_activeDom (h𝓦ℋ q _ hA) (PocketUnionPt.measurableSet_live A γ q) hCo
        (fun z => h𝓦ℋ q _ (hCm z)) (hact q) hgeoK
    · refine Eventually.of_forall fun ω => ?_
      by_cases hl : ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)
      · rw [hact q ω hl.1 hl.2]
        obtain ⟨hfr, hF, hKC⟩ := hgeoK ω hl.1 hl.2
        refine ⟨fun z hz => ⟨hz.2.1, fun hzK => hz.2.2 (hKC ⟨hzK, hz.1⟩)⟩, fun z hz =>
          PocketUnionPt.connectedComponentIn_subset_inter (hCo ω hl.1) hfr (fun x hx => ?_) hz⟩
        refine hF ⟨?_, hx.1⟩
        by_contra hxF
        exact hx.2 ⟨hx.1, hxF⟩
      · rw [PocketUnionPt.activeDom_eq_empty hl]
        exact ⟨empty_subset _, fun z hz => hz.elim⟩
  have hpt : PocketMeanPt κ ρL ρR P A γ xL xR c a (chiC κ)
      fun q ω => g q ω + smoothDist upperHalfPlaneOpens u := by
    intro q
    filter_upwards [hmeanAt q (g q) (hg q)] with ω hω hωA hq
    obtain ⟨v, hvc, hvrep, hvid⟩ := hω hωA hq
    have hE : (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) = C ω ∩ (H \ F q ω) := by
      rw [← activeDom_eq hωA hq]
      exact hact q ω hωA hq
    refine ⟨v, by rw [hE]; exact hvc, fun φ hφ => hvrep φ (by rw [← hE]; exact hφ), fun w hw => ?_⟩
    have hz : (c ω).2.1 w ∈ C ω ∩ (H \ F q ω) := by
      rw [← hE]
      exact mem_image_of_mem _ hw
    have h := hvid _ hz
    rwa [(hcOn.1 ω hωA).1.2.2 w hw.1] at h
  refine ⟨hcc, fun z => measurableSet_mem_dom_shiftChart hCo hCH hψ hA hCm n z,
    fun z => measurable_fwd_shiftChart hCo hCH hψ hA hψm n z,
    fun z => measurable_lift_shiftChart hCo hCH hψ hA hCm hψm hn z,
    continuousOn_lift_shiftChart hCo hCH hψ n, harmonicOnNhd_lift_shiftChart hCo hCH hψ n, fun s => (hlaw s).1,
    fun s => (hlaw s).2.2.1, _, _, pocketKernel_of_unionLaw hh₀ _ (fun _ => rfl) hUL,
    pocketMeanIdent_of_pt hγ (fun ω hω => (hcOn.1 ω hω).2.2.2) hpt⟩

/-- **`PocketChartFieldStatement` from the pocket data with the explicit shifted canonical chart.** On a standard
Borel probability space with walls' σ-algebra `𝓦`, a walls-event `A` of positive probability, the word `(ρL; ρR)` with
seed weights `r_L, r_R` and all side partial sums `> −2`, a driven traversal `γ` on `A` with walls-measurable marks,
pocket data `(C, ψ, F)`, a walls-measurable branch integer `n` and a constant `a`, the two remaining field-level inputs
at every relative capacity time (`PocketStopUnionLaw`, `PocketStopSideLimit`), and the determination of the killed
relative history by a walls' record `E` and the pocket field `chartTransport c 1 a χ(κ) (h₀ + u)` (`hdet`; the field
of the conclusion is `h = h₀ + u`, centred by `u`). -/
theorem pocketChartFieldStatement_of_stop [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) (hxRd : ∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) (hxRi : ∀ ω ∈ A, Monotone (xR ω))
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀
      u (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q)
    {ε : Type u} [MeasurableSpace ε] [StandardBorelSpace ε] {E : Ω → ε}
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace (nL + 1) (nR + 1)} (hEm : Measurable[𝓦] E)
    (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, ω ∈ A → ∀ hc : (shiftChart (pChart A C ψ ω) (n ω)).IsConformal,
      killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) xL)
        (geomRW (fun t ω => segDriver (γ ω) t) xR) (fun ω => capLife (γ ω)) ω =
          g (E ω, Chart.chartTransport hc 1 a (chiC κ) (h₀ ω + smoothDist upperHalfPlaneOpens u))) :
    PocketChartFieldStatement.{u} κ rL rR := by
  obtain ⟨hcc, hdom, hfwd, hliftm, hliftc, hlift, hKm, hKloc, 𝓜, M, hker, hmean⟩ :=
    pocketChartData_of_stop h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hFo hgeo hh₀ hu hub hn hU hside
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) u) P := by
    rw [centredField_add_smoothDist]
    exact hh₀
  have hKloc' : ∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s)
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) s)
      (centredField (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) u) P := by
    rw [centredField_add_smoothDist]
    exact hKloc
  exact ⟨nL, nR, ρL, ρR, hρL, hρR, hsL, hsR, Ω, 𝓦, mΩ, inferInstance, P, inferInstance, A, γ, xL, xR,
    fun ω => shiftChart (pChart A C ψ ω) (n ω), hcc, a, chiC κ, fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u, u,
    𝓜, M, ε, inferInstance, inferInstance, E, g, h𝓦, hA, hPA, hγ, hγm, hunb, hxLm, hxRm, hseedL, hseedR, hxLd,
    hxRd, hxLi, hxRi, hdom, hfwd, hliftm, hliftc, hlift, measurable_add_smoothDist hh₀.measurable u, hu, hh0, hker,
    hmean, hKm, hKloc', hEm, hg, by filter_upwards [hdet] with ω hω hωA using hω hωA (hcc ω)⟩

end Gen

end InteractingSLE.Sec7.Lemma725RefChart
