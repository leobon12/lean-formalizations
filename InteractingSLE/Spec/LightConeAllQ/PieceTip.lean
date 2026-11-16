/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.LightConeAllQ.Statements
import InteractingSLE.Spec.Supplement.GW2LaterPass
import InteractingSLE.Spec.Supplement.GW2aStepBW1
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# Interior switching tips at every deterministic schedule, from the one-flow-line fixed-time statement

Packet PROVE-T14-ALLQ (ruling R126). The one-flow-line statement `GW2aStep.FlowFixedTimeInteriorStatement` (a
deterministic positive own time before the lifetime is almost surely an interior tip) is applied to each piece of a
GW2 schedule under its conditional law given the retained past (`IsStagedHistory`). The conclusion is carried back to
`P` through a measurable event built from the inverse Loewner maps of the stopped piece at the points `i/(n+1)`
(Carathéodory measurability, `GW2Later.measurable_fwdMapInv_apply`).

* `schedDelta_pos`: the own times of a schedule with positive increasing times are positive;
* `tipSeq`, `measurable_tipSeq`: the measurable approximants of the tip of a stopped piece;
* `ae_interiorStop_piece`: one piece of a GW2 flow program has an interior tip at its deterministic own time, almost
  surely on its success (conditional helper: the one-flow-line statement is a hypothesis);
* `gw2InteriorScheduleAllQ_of_fix`: the core `GW2InteriorScheduleAllQStatement` from the one-flow-line statement
  (conditional helper).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

universe u

namespace InteractingSLE.LightConeAllQ

open Theorem14 Theorem14.GW2Later Theorem14.GW2Schedule Theorem14.GW2Sched Theorem14.GW2aMulti Theorem14.GW2Cone
  Exist.Staged Exist.StagedLaw

/-- **The own times of a schedule are positive** (positive, strictly increasing schedule times). -/
theorem schedDelta_pos {Θ : Set ℝ} {Q : Set ℝ≥0} {l : List (ℝ × ℝ≥0)} (hl : IsSchedule Θ Q l)
    (hQ : ∀ q ∈ Q, 0 < q) {j : ℕ} (hj : j < l.length) : 0 < schedDelta 0 l j := by
  unfold schedDelta
  rw [ENNReal.coe_pos, tsub_pos_iff_lt, List.getD_eq_getElem _ _ hj]
  cases j with
  | zero => exact hQ _ (hl.1 _ (List.getElem_mem hj)).2
  | succ j =>
    show (l.getD j (0, 0)).2 < l[j + 1].2
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.pairwise_iff_getElem.1 hl.2 j (j + 1) (by omega) hj (by omega)

section Tip

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The inverse Loewner map at `i/(n+1)` of a driver stopped at `S` on the event `M` (`0` off `M`), at time `T`:
the measurable approximants of the tip of the stopped piece. -/
def tipSeq (M : Set Ω) (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (S : Ω → ℝ≥0∞) (T : ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  fwdMapInv (fun x : ℝ => stopProc M e S x.toNNReal ω) T (yPt n)

omit mΩ in
/-- On `M`, the approximants are the inverse maps of the stopped driver. -/
theorem tipSeq_eq {M : Set Ω} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {S : Ω → ℝ≥0∞} {T : ℝ} {ω : Ω} (hω : ω ∈ M)
    (n : ℕ) : tipSeq M e S T n ω = fwdMapInv (stopR (e ω).1 (S ω)) T (yPt n) := by
  unfold tipSeq
  rw [stopProc_eq hω]

/-- **The approximants are measurable** (a measurable driver, continuous up to a finite stop on `M`, starting at
`0` on `M`). -/
theorem measurable_tipSeq {M : Set Ω} (hM : MeasurableSet M) {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (he : Measurable e)
    {S : Ω → ℝ≥0∞} (hS : Measurable S) (hSt : ∀ ω ∈ M, S ω ≠ ⊤)
    (hc : ∀ ω ∈ M, ContinuousOn (e ω).1 {t | (t : ℝ≥0∞) ≤ S ω}) (h0 : ∀ ω ∈ M, (e ω).1 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) (n : ℕ) : Measurable (tipSeq M e S T n) :=
  measurable_fwdMapInv_apply (B := stopProc M e S) (measurable_stopProc hM he hS hSt hc)
    (continuous_stopProc hSt hc) (stopProc_zero h0) hT ⟨yPt n, yPt_mem_H n⟩

/-- The event that a sequence of points eventually stays at height at least `1/(m+1)` for some `m`. -/
def EventuallyHigh (Z : ℕ → Ω → ℂ) : Set Ω :=
  {ω | ∃ m : ℕ, ∀ᶠ n in atTop, 1 / ((m : ℝ) + 1) ≤ (Z n ω).im}

theorem measurableSet_eventuallyHigh {Z : ℕ → Ω → ℂ} (hZ : ∀ n, Measurable (Z n)) :
    MeasurableSet (EventuallyHigh Z) := by
  have e : EventuallyHigh Z = ⋃ m : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n),
      {ω | 1 / ((m : ℝ) + 1) ≤ (Z n ω).im} := by
    ext ω
    simp only [EventuallyHigh, eventually_atTop, mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [e]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => measurableSet_le measurable_const (Complex.measurable_im.comp (hZ n))

omit mΩ in
/-- A limit in `ℍ` is eventually high. -/
theorem mem_eventuallyHigh_of_tendsto {Z : ℕ → Ω → ℂ} {ω : Ω} {p : ℂ} (hp : p ∈ H)
    (hZ : Tendsto (fun n => Z n ω) atTop (𝓝 p)) : ω ∈ EventuallyHigh Z := by
  have hpos : 0 < p.im := hp
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  refine ⟨m, ?_⟩
  have him : Tendsto (fun n => (Z n ω).im) atTop (𝓝 p.im) := (Complex.continuous_im.tendsto p).comp hZ
  exact (him.eventually (lt_mem_nhds hm)).mono fun n hn => hn.le

omit mΩ in
/-- An eventually high sequence converging to `p` has `p ∈ ℍ`. -/
theorem mem_H_of_eventuallyHigh {Z : ℕ → Ω → ℂ} {ω : Ω} {p : ℂ} (hω : ω ∈ EventuallyHigh Z)
    (hZ : Tendsto (fun n => Z n ω) atTop (𝓝 p)) : p ∈ H := by
  obtain ⟨m, hm⟩ := hω
  have him : Tendsto (fun n => (Z n ω).im) atTop (𝓝 p.im) := (Complex.continuous_im.tendsto p).comp hZ
  have hle : 1 / ((m : ℝ) + 1) ≤ p.im := ge_of_tendsto him hm
  show 0 < p.im
  exact lt_of_lt_of_le (by positivity) hle

end Tip

section Piece

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **One piece of a GW2 flow program has an interior tip at its deterministic own time, almost surely on its
success** (conditional helper: the one-flow-line statement `hFix` is a hypothesis). The pieces before `j` succeed on
a retained event `L`, on which instruction `j` launches with angle `θ j`. Under the conditional law given the retained
past, the piece is a flow line of a GFF with piecewise-constant data, so `hFix` makes its tip at the positive own time
`Δ j` interior. The measurable event `A` (failure before `j`, death of the piece by `Δ j`, or eventually high
approximants on the regular samples) is almost sure under almost every conditional law, hence almost sure; on it and
on the success of piece `j`, the approximants converge to the trace point at `Δ j`, which is therefore in `ℍ`. -/
theorem ae_interiorStop_piece (hFix : GW2aStep.FlowFixedTimeInteriorStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}
    (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    {j : ℕ} (hj : j < spec.2.2.length) (hθ : θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hΔpos : 0 < Δ j) :
    ∀ᵐ ω ∂P, AllSucc Δ (fun i => E i ω) (j + 1) → IsInteriorStop (E j ω).1 (Δ j) := by
  classical
  have h𝒢 : pastSigma κ b jumps spec E j ≤ mΩ := hS.2.1 j
  have hEm : ∀ i, Measurable (E i) := hS.1
  -- the success event before `j` is retained
  set L : Set Ω := {ω | AllSucc Δ (fun i => E i ω) j} with hLdef
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec E j] L := measurableSet_allSucc hgw hprog hΔ E hj.le
  have hLm : MeasurableSet L := h𝒢 _ hL𝒢
  have hlaunch : ∀ ω ∈ L, (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j =
      some (succChart spec.1 Δ (fun i => E i ω) j, θ j) := fun ω hω =>
    (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω) hj).1 hω
  have hinstr : instrTime spec j = Δ j := instrTime_eq_of_isFlowProg hprog hj
  -- the regular samples
  obtain ⟨G, hGae, hGm, hGp⟩ := hR.ae_pieceRegular.exists_measurable_mem
  have hregj : ∀ ω ∈ L ∩ G, GW1P.PieceRegular (E j ω).1 (min (Δ j) (E j ω).2) := fun ω hω => by
    have hpr := hGp ω hω.2 j _ _ (hlaunch ω hω.1)
    rwa [hinstr] at hpr
  -- the measurable approximants of the tip at the own time
  set Sp : Ω → ℝ≥0∞ := fun ω => min (Δ j) (E j ω).2 with hSpdef
  have hSpm : Measurable Sp := measurable_const.min (measurable_snd.comp (hEm j))
  set T₀ : ℝ := (((Δ j).toNNReal : ℝ≥0) : ℝ) with hT₀def
  set Z : ℕ → Ω → ℂ := tipSeq (L ∩ G) (E j) Sp T₀ with hZdef
  have hZm : ∀ n, Measurable (Z n) := measurable_tipSeq (hLm.inter hGm) (hEm j) hSpm
    (fun ω _ => ne_top_of_le_ne_top (hΔ j) (min_le_left _ _)) (fun ω hω => (hregj ω hω).2.1)
    (fun ω hω => (hregj ω hω).1) (NNReal.coe_nonneg _)
  -- the measurable event
  set A : Set Ω := (Lᶜ ∪ {ω | (E j ω).2 ≤ Δ j}) ∪ (G ∩ EventuallyHigh Z) with hAdef
  have hAm : MeasurableSet A :=
    (hLm.compl.union (measurableSet_le (measurable_snd.comp (hEm j)) measurable_const)).union
      (hGm.inter (measurableSet_eventuallyHigh hZm))
  -- the approximants converge to the radial limit of the stopped piece
  have hΔeq : (((Δ j).toNNReal : ℝ≥0) : ℝ≥0∞) = Δ j := ENNReal.coe_toNNReal (hΔ j)
  have hZlim : ∀ ω ∈ L ∩ G, Δ j < (E j ω).2 → ∀ p : ℂ,
      Chart.id.tipAt (fun r : ℝ≥0 => (E j ω).1 (min (r : ℝ≥0∞) (Δ j)).toNNReal) (Δ j).toNNReal p →
      Tendsto (fun n => Z n ω) atTop (𝓝 p) := by
    intro ω hω hs p hp
    have hSp : Sp ω = Δ j := min_eq_left hs.le
    have e : ∀ n, Z n ω = fwdMapInv (stopR (E j ω).1 (Δ j)) T₀ (yPt n) := fun n => by
      rw [hZdef, tipSeq_eq hω n, hSp]
    have hg : Tendsto (fun y : ℝ => fwdMapInv (stopR (E j ω).1 (Δ j)) T₀ ((y : ℂ) * Complex.I)) (𝓝[>] 0)
        (𝓝 p) := hp
    exact (tendsto_comp_yPt hg).congr fun n => (e n).symm
  -- the kernel step
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E j) ω₀), ω ∈ A := by
    filter_upwards [hS.2.2.2 j, Sec7.Aux122Disint.ae_ae_condExpKernel (p := fun ω => ω ∈ G) h𝒢 hGae,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL𝒢,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL𝒢.compl] with ω₀ hst hGk hLin hLout
    by_cases hω₀ : ω₀ ∈ L
    · obtain ⟨b', jumps', h', hb', -, hfl⟩ := hst _ _ (hlaunch ω₀ hω₀)
      have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
      have hpos : 0 < (Δ j).toNNReal := ENNReal.toNNReal_pos hΔpos.ne' (hΔ j)
      have hfix := hFix κ hκ hκ4 (θ j) hθ b' jumps' hb' _ h' hG' _ _ hfl (Δ j).toNNReal hpos
      filter_upwards [hfix, hGk, hLin hω₀] with ω hfω hGω hLω
      by_cases hs : Δ j < (E j ω).2
      · rw [hΔeq] at hfω
        obtain ⟨p, hpH, hp⟩ := hfω hs
        exact Or.inr ⟨hGω, mem_eventuallyHigh_of_tendsto hpH (hZlim ω ⟨hLω, hGω⟩ hs p hp)⟩
      · exact Or.inl (Or.inr (not_lt.1 hs))
    · filter_upwards [hLout hω₀] with ω hω
      exact Or.inl (Or.inl hω)
  -- back to `P`
  have hP : ∀ᵐ ω ∂P, ω ∈ A := Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hAm hker
  filter_upwards [hP, hGae] with ω hAω hGω hsucc
  have hL : ω ∈ L := hsucc.mono (Nat.le_succ j)
  have hs : Δ j < (E j ω).2 := hsucc j (Nat.lt_succ_self j)
  rcases hAω with (hc | hc) | ⟨-, hT⟩
  · exact absurd hL hc
  · exact absurd hs (not_lt.2 hc)
  · obtain ⟨hW0, hWc, α, hα, -⟩ := hregj ω ⟨hL, hGω⟩
    rw [min_eq_left hs.le] at hWc hα
    have htip := CounterflowRange.tendsto_tip_stopped_of_tendsto (c := Chart.id) (f := fun z => z) hα hWc hW0
      (t := (Δ j).toNNReal) hΔeq.le ((continuous_id.tendsto _).mono_left nhdsWithin_le_nhds)
    show ∃ p ∈ H, Chart.id.tipAt _ _ p
    exact ⟨α (Δ j).toNNReal, mem_H_of_eventuallyHigh hT (hZlim ω ⟨hL, hGω⟩ hs _ htip), htip⟩

/-- **The core from the one-flow-line statement** (conditional helper): GB9a's interior-switch condition at every
deterministic schedule, piece by piece (`ae_interiorStop_piece`); the own times of a schedule are positive and finite,
and on success each piece stops at its own time. -/
theorem gw2InteriorScheduleAllQ_of_fix (hFix : GW2aStep.FlowFixedTimeInteriorStatement.{u}) :
    GW2InteriorScheduleAllQStatement.{u} := by
  intro κ hκ hκ4 b jumps _hb Ω _ _ P _ h _hh Θ hΘ _hΘc Q _hQc _hQd hQpos E hE hR x _hx l hl k hk
  set spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩ with hspec
  have hBC : IsBoundaryContinuedProgram spec.2.2 :=
    isBoundaryContinuedProgram_scheduleProgram (mem_Icc_of_isSchedule hΘ hl) 0
  have hprog : IsFlowProg spec.2.2 (schedAngle l) (schedDelta 0 l) := isFlowProg_scheduleProgram 0 l
  have hlen : spec.2.2.length = l.length := length_scheduleProgram 0 l
  have hpiece : ∀ j, ∀ᵐ ω ∂P, j < k → AllSucc (schedDelta 0 l) (fun i => E spec i ω) (j + 1) →
      IsInteriorStop (E spec j ω).1 (schedDelta 0 l j) := by
    intro j
    by_cases hjk : j < k
    · have hjl : j < l.length := lt_trans hjk hk
      filter_upwards [ae_interiorStop_piece hFix hκ hκ4 (spec := spec) rfl hprog (schedDelta_ne_top 0 l)
        (hE spec hBC) (hR spec hBC) (by rw [hlen]; exact hjl)
        (schedAngle_mem_Icc (mem_Icc_of_isSchedule hΘ hl) hjl) (schedDelta_pos hl hQpos hjl)] with ω hω _
        using hω
    · exact Eventually.of_forall fun ω h => absurd h hjk
  filter_upwards [ae_all_iff.2 hpiece] with ω hω hs j hj
  have hjl : j < spec.2.2.length := by rw [hlen]; exact lt_trans hj hk
  show IsInteriorStop (E spec j ω).1 (pieceStop spec (fun i => E spec i ω) j)
  rw [pieceStop, instrTime_eq_of_isFlowProg hprog hjl, min_eq_left (hs j hj).le]
  exact hω j hj (hs.mono (Nat.succ_le_of_lt hj))

end Piece

end InteractingSLE.LightConeAllQ
