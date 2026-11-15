/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KdAssemble

/-!
# SB2(1)'s driver link from a per-sample identification of the actual remainder

Packet PROVE-T14-SB2DRV. The landed conditional assembly
`sb2DriverLinkAmbStatement_of_erasedInputs` (PROVE-T14-SB2K2) asks, through
`SB2ErasedDriverInputsStatement`, for a **measurable** driver `D` matching the canonical code on the
whole launch event, with a generating trace and the remainder link there. Two of these demands are
artifacts of that interface and are removed here:

* measurability of the actual relative driver: the canonical conditional driver of the launch chart
  (`exists_condFlowLineDriverOn_of_chartField`, already landed) is measurable and regular at every
  sample, and it matches the canonical code almost surely on the launch event
  (`ae_codeMatch_of_isCondFlowLineDriverOn`: Theorem 1.2 under the conditional laws);
* a generating trace off the entrance event `{T_L < ζ}`: the target's link
  (`IsRemainderLink`) is vacuous there (`ae_remainderLink_of_condDriver_trace_visit`).

What remains is the **per-sample identification** `SB2RemainderCodeStatement`: almost surely on the
launch event and on the entrance event, the actual remainder of the upper flow, read in the launch
chart, is the generating trace of *some* driver continuous before its lifetime that matches the
canonical code of (launch word, chart field). It contains no measurability requirement and no
conditional law. `sb2RemainderCodeStatement_of_erasedInputs` shows it is implied by the old input.

* **`sb2DriverLinkAmbStatement_of_remainderCode`**: `SB2DriverLinkAmbStatement` from Theorems
  1.2–1.3 and `SB2RemainderCodeStatement`.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4 Exist.Staged Exist.StagedLaw Restart WalkInf Sec2.Assembly

/-! ### Two generic steps -/

/-- **A code determines a continuous driver before its lifetime**: two drivers continuous before
their lifetimes that match the same code have the same lifetime and agree before it. -/
theorem eq_of_driverCodeMatch {p : PCode × ℝ≥0∞} {W W' : ℝ≥0 → ℝ} {V V' : ℝ≥0∞}
    (hW : ContinuousOn W {t | (t : ℝ≥0∞) < V}) (hW' : ContinuousOn W' {t | (t : ℝ≥0∞) < V'})
    (h : IsDriverCodeMatch p W V) (h' : IsDriverCodeMatch p W' V') :
    V = V' ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V → W t = W' t := by
  obtain ⟨hV, -, hd⟩ := h
  obtain ⟨hV', -, hd'⟩ := h'
  have hVV : V = V' := hV.trans hV'.symm
  refine ⟨hVV, fun t ht => ?_⟩
  subst hVV
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < V} :=
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hc := (hW t ht).continuousAt (hopen.mem_nhds ht)
  have hc' := (hW' t ht).continuousAt (hopen.mem_nhds ht)
  have hlim := tendsto_dyad_flr t
  refine tendsto_nhds_unique (hc.tendsto.comp hlim)
    ((hc'.tendsto.comp hlim).congr' (Eventually.of_forall fun n => ?_))
  have hle : (dyad n (flr n t) : ℝ≥0∞) < V :=
    (ENNReal.coe_le_coe.2 (dyad_flr_le n t)).trans_lt ht
  simp only [Function.comp_apply]
  rw [hd n _ hle, hd' n _ hle]

/-- **Determination under the conditional laws** (Theorem 1.2's parametric form in universe `u`): a
measurable conditional flow-line driver in a `𝒢`-measurable chart, with the data of a `𝒢`-measurable
word, matches the canonical code of (word, chart field) almost surely on the live event. -/
theorem ae_codeMatch_of_isCondFlowLineDriverOn
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ)
    {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h) {cw : Ω → BoundaryWord}
    (hcw : Measurable[𝒢] cw) {c : Ω → Chart} (hc : IsMeasChart 𝒢 c)
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀)
    {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hWm : ∀ t, Measurable (W t)) (hVm : Measurable V)
    (hD : IsCondFlowLineDriverOn κ θ 𝒢 P F h c (fun ω => (cw ω).fn) (fun ω => (cw ω).jumps) W V) :
    ∀ᵐ ω ∂P, ω ∈ F →
      IsDriverCodeMatch (driverCode h12p hκ θ
        (cw ω, Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω))) (fun t => W t ω) (V ω) := by
  set G : Ω → PCode × ℝ≥0∞ := fun ω =>
    driverCode h12p hκ θ (cw ω, Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω)) with hGdef
  have hcm := hc.mono h𝒢
  have hHc : Measurable fun ω => Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' hc.1 hcm.2.2.2.1 hcm.2.2.2.2.1 hcm.2.2.2.2.2.2 hc.2.1
      hhm 1 0 (chiC κ)
  have hGm : Measurable G := (measurable_driverCode h12p hκ θ).comp ((hcw.mono h𝒢 le_rfl).prodMk hHc)
  have hQm := Cond.measurableSet_driverCodeMatch_self hGm hWm hVm
  have hFm : MeasurableSet F := h𝒢 _ hF
  have hEm : MeasurableSet ({ω | IsDriverCodeMatch (G ω) (fun t => W t ω) (V ω)} ∪ Fᶜ) :=
    hQm.union hFm.compl
  have hk : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      ω ∈ {ω | IsDriverCodeMatch (G ω) (fun t => W t ω) (V ω)} ∪ Fᶜ := by
    filter_upwards [hD, hcc, Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢 hcw,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hF.compl] with ω₀ hD₀ hcc₀ hcw₀ hout
    by_cases hω₀ : ω₀ ∈ F
    · obtain ⟨-, h', hct, hfl⟩ := hD₀ hω₀
      filter_upwards [Cond.ae_driverCodeMatch_of_isFlowLineDriver_univ h12p hκ θ h13 (cw ω₀) hfl,
        hcc₀ hω₀, hcw₀] with ω hω hcω hcwω
      left
      have hY : Chart.chartTransport (hc.1 ω) 1 0 (chiC κ) (h ω) = h' ω := by
        apply IsChartTransport.unique (hc.1 ω₀) _ (hct ω)
        rw [← hcω]
        exact CondDriverBridge.isChartTransport_chartTransport_of_continuousOn (hc.1 ω) (hc.2.1 ω)
          1 0 (chiC κ) (h ω)
      show IsDriverCodeMatch (G ω) (fun t => W t ω) (V ω)
      rw [hGdef]
      simp only
      rw [hcwω, hY]
      exact hω
    · filter_upwards [hout hω₀] with ω hω
      exact Or.inr hω
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hEm hk] with ω hω hωF
  rcases hω with h1 | h1
  · exact h1
  · exact absurd hωF h1

/-- **The remainder link under the conditional laws from the entrance event alone**: as
`ae_remainderLink_of_condDriver_trace`, with the geometric trace and link asked only where the
physical curve enters (`firstVisit < ζ`); off it the link is vacuous. -/
theorem ae_remainderLink_of_condDriver_trace_visit
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {θ : ℝ}
    {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h𝒢 : 𝒢 ≤ mΩ) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {m : Ω → ℝ}
    {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {η γ : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {L : Ω → ℝ}
    (hcond : IsCondFlowLineDriverOn κ θ 𝒢 P F h
      (fun ω => (c ω).recenter (m ω)) bc jc W V)
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c ω = c ω₀ ∧ m ω = m ω₀)
    (hreg : ∀ ω, IsRegularDriver ((fun t => W t ω), V ω))
    (hgeom : ∀ᵐ ω ∂P, ω ∈ F → firstVisit (η ω) (ζ ω) (L ω) < ζ ω →
      IsGeneratingTrace (fun t => W t ω) (V ω) (γ ω) ∧
      IsRemainderLink (c ω) (η ω) (ζ ω) (L ω)
        (fun t => γ ω t + m ω) (V ω)) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      IsRemainderLink (c ω₀) (η ω) (ζ ω) (L ω)
        (fun t => GW2aSingle.chosenTrace W V ω t + m ω₀) (V ω) := by
  filter_upwards [hcond, hcc,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hgeom,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hF]
    with ω₀ hcond₀ hcc₀ hgeom₀ hF₀ hmem
  obtain ⟨-, _, -, hfl⟩ := hcond₀ hmem
  filter_upwards [GW2aSingle.ae_chosenTrace h13 hκ hfl,
    hcc₀ hmem, hgeom₀, hF₀ hmem] with ω hchosen hcm hgeomω hFω
  rw [← hcm.1, ← hcm.2]
  intro hvis
  obtain ⟨hgen, hclock⟩ := hgeomω hFω hvis
  refine hclock.congr_rel (fun s hs => ?_) hvis
  rw [IsGeneratingTrace.eq_of_le hchosen.1 hgen (hreg ω).1 (hreg ω).2.1 hs.le]

/-! ### The per-sample identification and the assembly -/

/-- **Named input: SB2(1)'s per-sample identification of the actual remainder** (supplement
pp. 631–633: "That portion is the canonical upper flow of the conditional field in `D_A` [...] with its
original stop reconstructed"; "Integrated uniqueness and the field-determining graphs identify the
actual relative ordinary flows"). For every SB2(1) launch problem and every compatible launch chart
record, almost surely on the launch event and on the entrance event `{T_L < ζ}` (`T_L` the first visit of
the upper flow to `L = min(A ∩ ℝ)`), the actual remainder of the upper flow, read through the launch
chart, is linked (`IsRemainderLink`) to a generating trace of some driver, continuous before its
lifetime, matching the canonical code of the launch word and of the field read in the recentred
version chart. No measurability of that driver and no conditional law is asked. -/
def SB2RemainderCodeStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ),
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      ∃ (W : ℝ≥0 → ℝ) (V : ℝ≥0∞) (γ : ℝ≥0 → ℂ),
        ContinuousOn W {t | (t : ℝ≥0∞) < V} ∧
        IsDriverCodeMatch (driverCode h12p H.kappa_pos ψ
          (I.word ω, Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω))) W V ∧
        IsGeneratingTrace W V γ ∧
        IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => γ t + launchEntry κ b jumps E (k + 1) u ω) V

/-- The old erased-driver input implies the per-sample identification. -/
theorem sb2RemainderCodeStatement_of_erasedInputs {h12p : Theorem12ParamStatement.{u}}
    (hin : SB2ErasedDriverInputsStatement h12p) : SB2RemainderCodeStatement h12p := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ H I
  obtain ⟨D, γ, -, hDr, hcode, hgeom⟩ := hin κ b jumps P h E k u ψ η ζ H I
  filter_upwards [hcode, hgeom] with ω hc hg hF _
  exact ⟨(D ω).1, (D ω).2, γ ω, (hDr ω).1, hc hF, (hg hF).1, (hg hF).2⟩

/-- **SB2(1)'s clauses (1) and (3) at the launches after the first** (`SB2DriverLinkAmbStatement`)
from Theorems 1.2–1.3 and the per-sample identification `SB2RemainderCodeStatement`. The driver is the
landed canonical conditional driver of the launch chart; its code match comes from Theorem 1.2 under
the conditional laws; on the entrance event the identified driver is this one
(`eq_of_driverCodeMatch`), so its generating trace and link transfer; off it the link is vacuous. -/
theorem sb2DriverLinkAmbStatement_of_remainderCode
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hrem : SB2RemainderCodeStatement h12p) : SB2DriverLinkAmbStatement.{u} := by
  classical
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hER hreg
    k u ψ hu hψ hL hH η ζ hη hS1
  let H : SB2LaunchProblem κ b jumps P h E k u ψ η ζ :=
    ⟨hκ, hκ4, hb, hh, hadm, hE, hER, hreg, hu, hψ, hL, hH, hη, hS1⟩
  let w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS : IsStagedHistory κ b jumps P h w (E w) := hE w hprog
  have hR : StagedPiecesRegular κ b jumps P w (E w) := hER w hprog
  have hamb : ∀ t, t < 0 → t ∉ jumps →
      b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  obtain ⟨m, cw, T, hm, hcw, hmc, heq, hG, hcc, hT, hcover⟩ :=
    exists_k2Launch_countable_types hκ hb hh (w := w) rfl hS hR
      (hreg w) hamb k ψ hu
  let I : K2LaunchInputs κ b jumps P h E k u ψ :=
    ⟨m, cw, T, hm, hcw, hmc, heq, hG, hcc, hT, hcover⟩
  have h𝒢 := hS.2.1 (k + 1)
  have hF : MeasurableSet[pastSigma κ b jumps w (E w) (k + 1)]
      (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma hb hS.1 (hreg w) (k + 1)
  have hr := measurable_pastMap (κ := κ) runMeasStatement hb w
    (fun j _ => hS.1 j) (fun j _ => hreg w j) (k + 1) le_rfl
  obtain ⟨D, hDm, hDr, hD⟩ := exists_condFlowLineDriverOn_of_chartField
    h12p h13 hκ ψ hr hh.1 hcw hmc hcc hG
  have hWm : ∀ t, Measurable (fun ω => (D ω).1 t) :=
    fun t => (measurable_pi_apply t).comp hDm.fst
  have hVm : Measurable (fun ω => (D ω).2) := hDm.snd
  have hcode := ae_codeMatch_of_isCondFlowLineDriverOn h12p h13 hκ ψ h𝒢 hF hh.1 hcw hmc
    (hcc.mono fun _ h _ => h) hWm hVm hD
  have hQ := hrem κ b jumps P h E k u ψ η ζ H I
  let γ : Ω → ℝ≥0 → ℂ := fun ω =>
    if hx : ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (D ω).1 (D ω).2 γ' ∧
        IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => γ' t + launchEntry κ b jumps E (k + 1) u ω) (D ω).2
    then hx.choose else 0
  have hgeom : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
      IsGeneratingTrace (fun t => (D ω).1 t) (D ω).2 (γ ω) ∧
      IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
        (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
        (fun t => γ ω t + launchEntry κ b jumps E (k + 1) u ω) (D ω).2 := by
    filter_upwards [hQ, hcode] with ω hQω hcω hFω hvis
    obtain ⟨W', V', γ', hW'c, hW'code, hgen, hlink⟩ := hQω hFω hvis
    obtain ⟨hVV, hWW⟩ := eq_of_driverCodeMatch hW'c (hDr ω).1 hW'code (hcω hFω)
    have hx : ∃ γ'' : ℝ≥0 → ℂ, IsGeneratingTrace (D ω).1 (D ω).2 γ'' ∧
        IsRemainderLink (launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω)
          (realMin (lowerPrefix κ b jumps E (k + 1) u ω))
          (fun t => γ'' t + launchEntry κ b jumps E (k + 1) u ω) (D ω).2 := by
      refine ⟨γ', ?_, ?_⟩
      · rw [← hVV]
        exact StoppedK2.isGeneratingTrace_congr hWW hgen
      · rw [← hVV]
        exact hlink
    have hγ : γ ω = hx.choose := dite_eq_left_of_eq_true (eq_true hx)
    rw [hγ]
    exact hx.choose_spec
  have hDa := hD.congr_chart
    (heq.mono fun ω he hFω => ⟨(he hFω).symm, rfl, rfl⟩)
  have hfreeze : ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps w (E w) (k + 1)) ω₀),
        launchChart κ b jumps E (k + 1) ω = launchChart κ b jumps E (k + 1) ω₀ ∧
        launchEntry κ b jumps E (k + 1) u ω = launchEntry κ b jumps E (k + 1) u ω₀ := by
    filter_upwards [CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ)
      (b := b) (jumps := jumps) w (fun j _ => hreg w j) h𝒢 le_rfl]
      with ω₀ hrun _
    filter_upwards [hrun] with ω hrunω
    refine ⟨?_, (launchEntry_eq_of_run_eq (u := u) hrunω).2⟩
    unfold launchChart
    rw [launches_run_succ_of_run_eq w hrunω]
  exact ⟨fun ω => (cw ω).fn, fun ω => (cw ω).jumps,
    fun t ω => (D ω).1 t, fun ω => (D ω).2, hDa,
    ae_remainderLink_of_condDriver_trace_visit h13 hκ h𝒢 hF hDa hfreeze hDr hgeom⟩

/-- The ambient upper launch conclusion (`Ly.SB2UpperLaunchEntryLAmbStatement`, the form SB3
consumes) from Theorems 1.2–1.3, the active word and the per-sample identification. -/
theorem sb2UpperLaunchEntryLAmbStatement_of_remainderCode
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hword : SB2ActiveWordAmbStatement.{u})
    (hrem : SB2RemainderCodeStatement h12p) :
    Ly.SB2UpperLaunchEntryLAmbStatement.{u} :=
  sb2UpperLaunchEntryLAmbStatement_of_parts h13 hword
    (sb2DriverLinkAmbStatement_of_remainderCode h12p h13 hrem)

end InteractingSLE.Theorem14.SB.Lv
