/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aChainPath
import InteractingSLE.Spec.Sec5.TwoMarkAdapt8Transport
import InteractingSLE.Spec.Sec6.Prop65Point
import InteractingSLE.Spec.Supplement.BR3RefPath
import InteractingSLE.Spec.Supplement.HullDetGenBR4aWire

/-!
# BR4a's relative chain: the inverse relative clock and the adaptedness of the relative driver

Packet PROVE-T14-BR4A2. For a random driver `w` (continuous at every sample, adapted to a filtration `𝓖`) and a
`𝓖₀`-measurable good event `G` on which every sample is good (`IsGoodSample`: generating trace, visit of `v`, unbounded
capacity clock before the visit):

* `exists_gap_le`: an infinite new horizon before a finite time forces the flowed pole arbitrarily close to the driver
  (a positive gap would bound Zhan's clock rate `α²/q⁴`);
* the announcing times `annSeq` (first time the gap is `≤ 1/(n+1)`, capped at `n`) are stopping times strictly before
  the first visit and exhaust it (`annSeq_lt`, `exists_le_annSeq`);
* **`relTime`** (Zhan's inverse clock at `q/a²`, TwoMark's `Clock7.inverseTime`): **`isStoppingTime_relTime`**,
  `monotone_relTime`, and on the good event **`relTime_spec`** (a finite time before the visit at which `clock v` is
  `q`);
* **`stronglyAdapted_relProc`**: the relative driver `relProc` (zero off `G`) is adapted to the stopped σ-algebras
  `q ↦ 𝓖_{relTime q}` (TwoMark's `Adapt8.adaptedBefore_of_coords` with the stopped Zhan coordinates,
  `stoppedCoords_regular`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Theorem14.BR4aChain

open Zhan.Retarget MartChar.RealFlow BR4aPath

/-! ### A positive gap bound would bound the clock -/

/-- If Zhan's new horizon is infinite before a finite `T₀`, the target comes arbitrarily close to the driver
before `T₀` (a gap `≥ δ` would bound the clock rate `α²/q⁴ ≤ a²/δ⁴`). -/
theorem exists_gap_le {w vk : ℝ≥0 → ℝ} {a : ℝ} {T₀ : ℝ≥0} (hd : PullData w vk a T₀)
    (hN : newHorizon a w vk T₀ = ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℝ≥0, s < T₀ ∧ vk s - w s ≤ δ := by
  by_contra hcon
  push Not at hcon
  have ha := hd.pos
  have hbd : newHorizon a w vk T₀ ≤ ENNReal.ofReal (T₀ * (a ^ 2 / δ ^ 4)) := by
    refine iSup₂_le fun S hS => ENNReal.ofReal_le_ofReal ?_
    have hS' : S < T₀ := ENNReal.coe_lt_coe.1 hS
    have hR := hd.isRate hS
    have hle : ∀ x ∈ Icc (0 : ℝ) S, rate a w vk x ≤ a ^ 2 / δ ^ 4 := by
      intro x hx
      have hxT : x.toNNReal < T₀ := lt_of_le_of_lt (Real.toNNReal_le_toNNReal hx.2) (by simpa using hS')
      have hg : δ ≤ gap w vk x := (hcon _ hxT).le
      have hα0 := alpha_pos ha w vk x
      have hα := Theorem14.BR3Ref.alpha_le (w := w) (vk := vk) ha hx.1
      unfold rate
      rw [div_le_div_iff₀ (pow_pos (hδ.trans_le hg) 4) (by positivity)]
      have h1 : alpha a w vk x ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hα0.le hα 2
      have h2 : δ ^ 4 ≤ gap w vk x ^ 4 := pow_le_pow_left₀ hδ.le hg 4
      nlinarith [pow_pos hδ 4, sq_nonneg a]
    calc clk (rate a w vk) S = ∫ x in (0 : ℝ)..S, rate a w vk x := rfl
      _ ≤ ∫ _ in (0 : ℝ)..S, a ^ 2 / δ ^ 4 :=
        intervalIntegral.integral_mono_on S.coe_nonneg (hR.intervalIntegrable ⟨le_rfl, S.coe_nonneg⟩
          ⟨S.coe_nonneg, le_rfl⟩) intervalIntegrable_const hle
      _ = S * (a ^ 2 / δ ^ 4) := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
      _ ≤ T₀ * (a ^ 2 / δ ^ 4) := by gcongr
  rw [hN] at hbd
  exact ENNReal.ofReal_ne_top (top_le_iff.1 hbd)


/-! ### The processes of a random driver -/

/-- **A good sample** for the target change to `v`: a continuous driver from `0` with a complete generating trace,
visiting `v` through `∞`, whose capacity clock `clock v` is unbounded before the first visit. -/
def IsGoodSample (v : ℝ) (w : ℝ≥0 → ℝ) : Prop :=
  Continuous w ∧ w 0 = 0 ∧ (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ γ) ∧
    (v : ℂ) ∈ infinitySourceChart.tipSet w ⊤ ∧
    ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} ∧
      M ≤ clock v (fun s : ℝ => w s.toNNReal) t

section Proc

variable {Ω : Type*}

/-- The oriented driver process. -/
def oProc (v : ℝ) (w : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => oDrv v (w · ω) t

/-- The flowed pole process. -/
def tProc (v : ℝ) (w : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => tgt v (w · ω) t

/-- The first visit of `v`. -/
def tipT (v : ℝ) (w : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ := firstTipTime infinitySourceChart (w · ω) {(v : ℂ)}

/-- The announcing times: the first time the gap of the flowed pole is `≤ 1/(n+1)`, capped at `n`. -/
def annSeq (v : ℝ) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ≥0 :=
  Sec6.Prop65.hitLe (fun t ω => tProc v w t ω - oProc v w t ω) (1 / ((n : ℝ) + 1)) n

/-- **The inverse relative clock** (Zhan's inverse clock at the scaled time `q/a²`, stopped at the first visit and
zero off the good event). -/
def relTime (G : Set Ω) (v : ℝ) (w : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) : Ω → WithTop ℝ≥0 :=
  Sec5.TwoMark.Clock7.inverseTime G (scl v) (oProc v w) (tProc v w) (tipT v w) ((q : ℝ) / scl v ^ 2).toNNReal

/-- **The relative driver process** (zero off the good event). -/
def relProc (G : Set Ω) (v : ℝ) (w : ℝ≥0 → Ω → ℝ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then relDrv v (w · ω) q else 0

variable {G : Set Ω} {v : ℝ} {w : ℝ≥0 → Ω → ℝ}

theorem continuous_oProc (hwc : ∀ ω, Continuous (w · ω)) (ω : Ω) : Continuous (oProc v w · ω) :=
  continuous_oDrv (hwc ω) v

theorem continuous_tProc (hwc : ∀ ω, Continuous (w · ω)) (ω : Ω) : Continuous (tProc v w · ω) := by
  have h := continuousOn_rightImg ((continuous_oProc (v := v) hwc ω).comp continuous_real_toNNReal) (scl v)
  exact (h.comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg)

theorem continuous_gap (hwc : ∀ ω, Continuous (w · ω)) (ω : Ω) :
    Continuous fun t => tProc v w t ω - oProc v w t ω :=
  (continuous_tProc hwc ω).sub (continuous_oProc hwc ω)

/-! ### Facts on the good event -/

theorem IsGoodSample.spec (hv : v ≠ 0) {w : ℝ≥0 → ℝ} (hg : IsGoodSample v w) :
    ∃ T₀ : ℝ≥0, firstTipTime infinitySourceChart w {(v : ℂ)} = T₀ ∧ 0 < T₀ ∧
      PullData (oDrv v w) (tgt v w) (scl v) T₀ ∧ newHorizon (scl v) (oDrv v w) (tgt v w) T₀ = ⊤ ∧
      Continuous (relDrv v w) ∧ relDrv v w 0 = 0 ∧
      ∀ t : ℝ≥0, t < T₀ →
        fwdHull (fun s : ℝ => relDrv v w s.toNNReal) (clock v (fun s : ℝ => w s.toNNReal) t) =
            BR4aPath.mob v '' fwdHull (fun s : ℝ => w s.toNNReal) t ∧
          clock v (fun s : ℝ => w s.toNNReal) t = relClk v w t := by
  obtain ⟨hw, hw0, ⟨γ, hγ⟩, hvis, hclk⟩ := hg
  obtain ⟨T₀, hT, hT0, -⟩ := exists_firstTipTime_notMem hw hw0 hγ hv hvis
  obtain ⟨hd, hN, hc, h0, hK⟩ := relDrv_spec hw hw0 hγ hv hvis hclk
  rw [hT] at hd hN hK
  exact ⟨T₀, hT, hT0, hd, hN, hc, h0, fun t ht => hK t (by exact_mod_cast ht)⟩

/-- On a good sample the announcing times are strictly before the first visit. -/
theorem annSeq_lt (hwc : ∀ ω, Continuous (w · ω)) (hv : v ≠ 0) {ω : Ω} (hg : IsGoodSample v (w · ω)) (n : ℕ) :
    (annSeq v w n ω : ℝ≥0∞) < tipT v w ω := by
  obtain ⟨T₀, hT, -, hd, hN, -⟩ := hg.spec hv
  obtain ⟨s, hsT, hs⟩ := exists_gap_le hd hN (δ := 1 / ((n : ℝ) + 1)) (by positivity)
  have h1 := (Sec6.Prop65.exitTime_le_iff' (continuous_gap (v := v) hwc) (1 / ((n : ℝ) + 1)) s ω).2
    ⟨s, ⟨zero_le, le_rfl⟩, hs⟩
  have h2 : ((annSeq v w n ω : ℝ≥0) : WithTop ℝ≥0) ≤ s := by
    rw [annSeq, Sec6.Prop65.coe_hitLe]; exact (min_le_left _ _).trans h1
  rw [tipT, hT]
  exact_mod_cast lt_of_le_of_lt (WithTop.coe_le_coe.1 h2) hsT

/-- On a good sample the announcing times exhaust the time before the first visit. -/
theorem exists_le_annSeq (hwc : ∀ ω, Continuous (w · ω)) (hv : v ≠ 0) {ω : Ω} (hg : IsGoodSample v (w · ω))
    (s : ℝ≥0) (hs : (s : ℝ≥0∞) < tipT v w ω) : ∃ n, s ≤ annSeq v w n ω := by
  obtain ⟨T₀, hT, -, hd, -⟩ := hg.spec hv
  rw [tipT, hT, ENNReal.coe_lt_coe] at hs
  have hsep := hd.sep.isSep_of_lt (S := s) (by exact_mod_cast hs)
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le (a := s)))
    (continuous_gap (v := v) hwc ω).continuousOn
  have hpos : ∀ r ∈ Icc (0 : ℝ≥0) s, 0 < tProc v w r ω - oProc v w r ω := fun r hr => by
    have := hsep.pos r ⟨r.coe_nonneg, by exact_mod_cast hr.2⟩
    simpa [gap, oProc, tProc] using this
  set m := tProc v w r₀ ω - oProc v w r₀ ω with hm
  have hm0 : 0 < m := hpos r₀ hr₀
  obtain ⟨n, hn⟩ := exists_nat_gt (max (s : ℝ) (1 / m))
  refine ⟨n, Sec6.Prop65.le_hitLe_of_forall (continuous_gap hwc) ?_ fun r hr => ?_⟩
  · exact_mod_cast (le_max_left _ _).trans hn.le
  · have h1 : 1 / ((n : ℝ) + 1) < m := by
      rw [div_lt_iff₀ (by positivity)]
      have := (le_max_right (s : ℝ) (1 / m)).trans_lt hn
      rw [div_lt_iff₀ hm0] at this
      nlinarith
    exact h1.trans_le (hmin ⟨zero_le, hr⟩)

theorem sepUpTo_of_good (hv : v ≠ 0) {ω : Ω} (hg : IsGoodSample v (w · ω)) :
    SepUpTo (oProc v w · ω) (tProc v w · ω) (tipT v w ω) := by
  obtain ⟨T₀, hT, -, hd, -⟩ := hg.spec hv
  rw [tipT, hT]
  exact hd.sep

theorem newHorizon_of_good (hv : v ≠ 0) {ω : Ω} (hg : IsGoodSample v (w · ω)) :
    newHorizon (scl v) (oProc v w · ω) (tProc v w · ω) (tipT v w ω) = ⊤ := by
  obtain ⟨T₀, hT, -, -, hN, -⟩ := hg.spec hv
  rw [tipT, hT]
  exact hN

theorem gap_pos_of_good (hv : v ≠ 0) {ω : Ω} (hg : IsGoodSample v (w · ω)) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < tipT v w ω) : 0 < tProc v w s ω - oProc v w s ω := by
  have hsep := (sepUpTo_of_good hv hg).isSep_of_lt (S := s) (by simpa using hs)
  have := hsep.pos s ⟨s.coe_nonneg, le_rfl⟩
  simpa [gap, oProc, tProc] using this

/-- **The inverse relative clock on a good sample**: a finite original time before the first visit, at which the
capacity clock `clock v` equals `q`. -/
theorem relTime_spec (hv : v ≠ 0) {ω : Ω} (hω : ω ∈ G) (hg : IsGoodSample v (w · ω)) (q : ℝ≥0) :
    ∃ t : ℝ≥0, relTime G v w q ω = t ∧ (t : ℝ≥0∞) < tipT v w ω ∧ clock v (fun s : ℝ => w s.toNNReal ω) t = q := by
  have hs := sepUpTo_of_good hv hg
  have hN := newHorizon_of_good hv hg
  have ha := scl_pos hv
  set u : ℝ≥0 := ((q : ℝ) / scl v ^ 2).toNNReal with hu
  have hu' : (u : ℝ≥0∞) < newHorizon (scl v) (oProc v w · ω) (tProc v w · ω) (tipT v w ω) := by
    rw [hN]; exact ENNReal.coe_lt_top
  obtain ⟨S, hST, -, -, hmem, hci⟩ := newTime_spec hs ha hu'
  set t : ℝ≥0 := (invClk (rate (scl v) (oProc v w · ω) (tProc v w · ω)) u).toNNReal with ht
  have htT : (t : ℝ≥0∞) < tipT v w ω := invClk_lt hs ha hu'
  refine ⟨t, ?_, htT, ?_⟩
  · unfold relTime Sec5.TwoMark.Clock7.inverseTime
    rw [← hu]
    simp only [hω, hu', ↓reduceIte, ht]
  · obtain ⟨T₀, hT, -, -, -, -, -, hK⟩ := hg.spec hv
    rw [tipT, hT, ENNReal.coe_lt_coe] at htT
    rw [(hK t htT).2, relClk]
    have h1 : ((t : ℝ≥0) : ℝ) = invClk (rate (scl v) (oProc v w · ω) (tProc v w · ω)) u :=
      Real.coe_toNNReal _ hmem.1
    have h2 : (u : ℝ) = (q : ℝ) / scl v ^ 2 := Real.coe_toNNReal _ (by positivity)
    have hci' : clk (rate (scl v) (oDrv v (w · ω)) (tgt v (w · ω))) t = u := by rw [h1]; exact hci
    rw [hci', h2]
    field_simp


variable [mΩ : MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 mΩ}

theorem measurable_oProc (hwm : ∀ t, Measurable[𝓖 t] (w t)) (t : ℝ≥0) : Measurable[𝓖 t] (oProc v w t) :=
  (hwm t).const_mul _

theorem measurable_tProc (hwc : ∀ ω, Continuous (w · ω)) (hwm : ∀ t, Measurable[𝓖 t] (w t)) (t : ℝ≥0) :
    Measurable[𝓖 t] (tProc v w t) :=
  Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable (𝓕 := 𝓖) (W := oProc v w)
    (measurable_oProc hwm) (continuous_oProc hwc) measurable_const t

theorem isStoppingTime_annSeq (hwc : ∀ ω, Continuous (w · ω)) (hwm : ∀ t, Measurable[𝓖 t] (w t)) (n : ℕ) :
    IsStoppingTime 𝓖 fun ω => (annSeq v w n ω : WithTop ℝ≥0) :=
  Sec6.Prop65.isStoppingTime_hitLe (continuous_gap hwc) (fun t =>
    (measurable_tProc hwc hwm t).sub (measurable_oProc hwm t)) _ _



/-! ### The stopping times and the adaptedness of the relative driver -/

section Meas

theorem adaptedBefore_top {X : ℝ≥0 → Ω → ℝ} (hX : ∀ t, Measurable[𝓖 t] (X t)) :
    AdaptedBefore 𝓖 (fun _ => ⊤) X := fun t A hA => by
  show MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ⊤ ∧ X t ω ∈ A}
  simp only [ENNReal.coe_lt_top, true_and]
  exact hX t hA

variable (hwc : ∀ ω, Continuous (w · ω)) (hwm : ∀ t, Measurable[𝓖 t] (w t)) (hv : v ≠ 0)
  (hG : MeasurableSet[𝓖 0] G) (hgood : ∀ ω ∈ G, IsGoodSample v (w · ω))

include hwc hwm hv hG hgood

theorem measurable_stoppedClock (n : ℕ) (r : ℝ≥0) :
    Measurable[𝓖 r] fun ω => if ω ∈ G then
      clk (rate (scl v) (oProc v w · ω) (tProc v w · ω)) (min r (annSeq v w n ω)) else 0 :=
  Sec5.TwoMark.Clock7.measurable_stopped_clock (e := fun _ => ⊤) (adaptedBefore_top (measurable_oProc hwm))
    (adaptedBefore_top (measurable_tProc hwc hwm)) (isStoppingTime_annSeq hwc hwm n) hG
    (fun _ _ => ENNReal.coe_lt_top) (fun ω _ => (continuous_gap hwc ω).continuousOn)
    (fun ω hω _ hs => gap_pos_of_good hv (hgood ω hω)
      ((ENNReal.coe_le_coe.2 hs).trans_lt (annSeq_lt hwc hv (hgood ω hω) n))) r

/-- **The inverse relative clock is a stopping time** of the filtration. -/
theorem isStoppingTime_relTime (q : ℝ≥0) : IsStoppingTime 𝓖 (relTime G v w q) :=
  Sec5.TwoMark.Clock7.isStoppingTime_inverseTime (scl_pos hv) hG (isStoppingTime_annSeq hwc hwm)
    (fun ω hω => sepUpTo_of_good hv (hgood ω hω)) (fun ω hω n => annSeq_lt hwc hv (hgood ω hω) n)
    (fun ω hω => exists_le_annSeq hwc hv (hgood ω hω)) (measurable_stoppedClock hwc hwm hv hG hgood) _

omit mΩ hwc hwm hG in
theorem monotone_relTime (ω : Ω) : Monotone fun q => relTime G v w q ω := fun _ _ hqq' =>
  Sec5.TwoMark.Clock7.inverseTime_mono (scl_pos hv) (fun ω hω => sepUpTo_of_good hv (hgood ω hω)) _ _
    (Real.toNNReal_le_toNNReal (div_le_div_of_nonneg_right (NNReal.coe_le_coe.2 hqq') (sq_nonneg _))) ω


/-- The stopped coordinates (pole flow, `α`, `β`, clock; driver in the second slot) of the target change at the
announcing time `n` are adapted and continuous. -/
theorem stoppedCoords_regular (n : ℕ) :
    (∀ r, Measurable[𝓖 r] (Sec5.TwoMark.Adapt8.stoppedCoords (Fin.elim0 : Fin 0 → ℝ) (fun _ : Fin 1 => (0 : ℝ))
      (scl v) 0 G (oProc v w) (oProc v w) (fun i => i.elim0) (fun _ => tProc v w) (annSeq v w n) r)) ∧
    ∀ ω, Continuous fun r => Sec5.TwoMark.Adapt8.stoppedCoords (Fin.elim0 : Fin 0 → ℝ) (fun _ : Fin 1 => (0 : ℝ))
      (scl v) 0 G (oProc v w) (oProc v w) (fun i => i.elim0) (fun _ => tProc v w) (annSeq v w n) r ω := by
  have ha := scl_pos hv
  have hA := isStoppingTime_annSeq (v := v) hwc hwm n
  have hσU : ∀ ω ∈ G, (annSeq v w n ω : ℝ≥0∞) < tipT v w ω := fun ω hω => annSeq_lt hwc hv (hgood ω hω) n
  have hpos : ∀ ω ∈ G, ∀ s ≤ annSeq v w n ω, 0 < tProc v w s ω - oProc v w s ω := fun ω hω s hs =>
    gap_pos_of_good hv (hgood ω hω) ((ENNReal.coe_le_coe.2 hs).trans_lt (hσU ω hω))
  let g := gapStopR (0 : Fin 1) G (oProc v w) (fun _ => tProc v w) (annSeq v w n)
  obtain ⟨hgm, hgc, hg0⟩ := Sec5.TwoMark.Adapt8.stopped_gap_regular (e := fun _ => ⊤)
    (adaptedBefore_top (measurable_oProc hwm)) (adaptedBefore_top (measurable_tProc hwc hwm)) hA hG
    (fun _ _ => ENNReal.coe_lt_top) (fun ω _ => (continuous_gap hwc ω).continuousOn) hpos
  have hRc : ∀ ω ∈ G, ContinuousOn (fun t => rCoordAt (scl v) (0 : Fin 1) (oProc v w · ω)
      (fun i (s : ℝ≥0) => (i.elim0 : ℝ≥0 → Ω → ℝ) s ω) (fun _ s => tProc v w s ω) t) (Iic (annSeq v w n ω)) := by
    intro ω hω
    have hS := (sepUpTo_of_good hv (hgood ω hω)).isSep_of_lt (S := annSeq v w n ω) (by simpa using hσU ω hω)
    have hmaps : MapsTo (fun t : ℝ≥0 => (t : ℝ)) (Iic (annSeq v w n ω)) (Icc 0 (annSeq v w n ω : ℝ)) :=
      fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht⟩
    have hα := (hS.continuousOn_alpha (xk := scl v)).comp NNReal.continuous_coe.continuousOn hmaps
    have hβ := (hS.continuousOn_beta (xk := scl v)).comp NNReal.continuous_coe.continuousOn hmaps
    have hC := ((hS.isRate ha).continuousOn_clk).comp NNReal.continuous_coe.continuousOn hmaps
    exact (continuousOn_pi.2 fun i => i.elim0).prodMk
      ((continuousOn_pi.2 fun _ => (continuous_tProc hwc ω).continuousOn).prodMk (hα.prodMk (hβ.prodMk hC)))
  refine ⟨fun r => ?_, fun ω => ?_⟩
  · let K : ℝ≥0 → Ω → RCoord 0 1 := fun s ω =>
      ((fun i => i.elim0), (fun _ => tProc v w s ω), alphaK (scl v) g s ω, betaK (scl v) g s ω, clkK (scl v) g s ω)
    have hK : ∀ s, Measurable[𝓖 s] (K s) := fun s =>
      (@Measurable.of_eval Ω (Fin 0) (fun _ => ℝ) (𝓖 s) _ _ fun i => i.elim0).prodMk
        ((@Measurable.of_eval Ω (Fin 1) (fun _ => ℝ) (𝓖 s) _ _ fun _ => measurable_tProc hwc hwm s).prodMk
          ((Sec5.TwoMark.Adapt8.measurable_alphaK hgm hgc s).prodMk
            ((Sec5.TwoMark.Adapt8.measurable_betaK hgm hgc hg0 s).prodMk
              (Sec5.TwoMark.Clock7.measurable_clkK hgm hgc hg0 s))))
    have hRm := Ito.measurable_stopped_of_agree hA hK hG
      (((Fin.elim0 : Fin 0 → ℝ), (fun _ : Fin 1 => (0 : ℝ)), scl v, -1, 0) : RCoord 0 1) (X := fun s ω =>
        rCoordAt (scl v) (0 : Fin 1) (oProc v w · ω) (fun i (r : ℝ≥0) => (i.elim0 : ℝ≥0 → Ω → ℝ) r ω)
          (fun _ r => tProc v w r ω) s)
      (fun ω hω s hs' => by
        obtain ⟨hα, hβ⟩ := Sec5.TwoMark.Adapt8.stopped_coefficients_eq (a := scl v) (W := oProc v w)
          (V := tProc v w) hω hs'
        have hC := Sec5.TwoMark.Clock7.clkK_gapStop_eq (a := scl v) (W := oProc v w) (V := tProc v w) hω hs'
        simp only [K, g, rCoordAt, hα, hβ, hC]
        refine Prod.ext (funext fun i => i.elim0) rfl) hRc r
    have hBm := Ito.measurable_stopped_of_agree (X := oProc v w) hA (measurable_oProc (v := v) hwm) hG 0
      (fun _ _ _ _ => rfl) (fun ω _ => (continuous_oProc hwc ω).continuousOn) r
    exact hRm.prodMk hBm
  · by_cases hω : ω ∈ G
    · simp only [Sec5.TwoMark.Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte]
      exact ((hRc ω hω).comp_continuous (continuous_id.min continuous_const)
        (fun t => mem_Iic.2 (min_le_right _ _))).prodMk
        ((continuous_oProc hwc ω).comp (continuous_id.min continuous_const))
    · simp only [Sec5.TwoMark.Adapt8.stoppedCoords, rCoord, hω, ↓reduceIte]
      exact continuous_const


/-- **The relative driver is adapted to the stopped σ-algebras of the inverse relative clock.** -/
theorem stronglyAdapted_relProc :
    StronglyAdapted (Supp8.HullDetGen.stoppedFiltration (isStoppingTime_relTime hwc hwm hv hG hgood)
      (monotone_relTime hv hgood)) (relProc G v w) := by
  intro q
  refine Measurable.stronglyMeasurable ?_
  have ha := scl_pos hv
  set Φ : RCoord 0 1 × ℝ → ℝ := fun p => p.1.2.2.2.1 + p.1.2.2.1 / (p.1.2.1 0 - p.2) with hΦdef
  have hΦ : Measurable Φ :=
    measurable_fst.snd.snd.snd.fst.add (measurable_fst.snd.snd.fst.div
      (((measurable_pi_apply 0).comp measurable_fst.snd.fst).sub measurable_snd))
  have hX : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : ℝ≥0∞) < newHorizon (scl v) (oProc v w · ω) (tProc v w · ω) (tipT v w ω) →
      newDrv (scl v) (oProc v w · ω) (tProc v w · ω) u =
        Φ (rCoordAt (scl v) (0 : Fin 1) (oProc v w · ω) (fun i (t : ℝ≥0) => (i.elim0 : ℝ≥0 → Ω → ℝ) t ω)
            (fun _ t => tProc v w t ω) (invClk (rate (scl v) (oProc v w · ω) (tProc v w · ω)) u).toNNReal,
          oProc v w (invClk (rate (scl v) (oProc v w · ω) (tProc v w · ω)) u).toNNReal ω) := by
    intro ω hω u hu
    obtain ⟨S, -, -, -, hmem, -⟩ := newTime_spec (sepUpTo_of_good hv (hgood ω hω)) ha hu
    simp only [hΦdef, newDrv, newPath, mobPath, Zhan.Retarget.mob, rCoordAt, Real.coe_toNNReal _ hmem.1]
  have hAB := Sec5.TwoMark.Adapt8.adaptedBefore_of_coords (𝓕 := 𝓖) (xL := Fin.elim0)
    (xR := fun _ : Fin 1 => (0 : ℝ)) (k := 0) (W := oProc v w) (B := oProc v w) (VL := fun i => i.elim0)
    (VR := fun _ => tProc v w) (U := tipT v w) (A := annSeq v w) ha hG (isStoppingTime_annSeq hwc hwm)
    (fun ω hω => sepUpTo_of_good hv (hgood ω hω)) (fun ω hω n => annSeq_lt hwc hv (hgood ω hω) n)
    (fun ω hω => exists_le_annSeq hwc hv (hgood ω hω)) (measurable_stoppedClock hwc hwm hv hG hgood)
    (fun n => (stoppedCoords_regular hwc hwm hv hG hgood n).1)
    (fun n => (stoppedCoords_regular hwc hwm hv hG hgood n).2) hΦ hX
  set u : ℝ≥0 := ((q : ℝ) / scl v ^ 2).toNNReal with hu
  have hτ := isStoppingTime_relTime hwc hwm hv hG hgood q
  have hGτ : MeasurableSet[hτ.measurableSpace] G := by
    have hle := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓖 0) hτ fun ω => by
      simp only [WithTop.coe_zero]; exact zero_le
    rw [IsStoppingTime.measurableSpace_const] at hle
    exact hle _ hG
  intro B hB
  have hset : relProc G v w q ⁻¹' B =
      {ω | (u : ℝ≥0∞) < (if ω ∈ G then newHorizon (scl v) (oProc v w · ω) (tProc v w · ω) (tipT v w ω) else 0) ∧
        newDrv (scl v) (oProc v w · ω) (tProc v w · ω) u ∈ (fun x => sgn v * (scl v * x)) ⁻¹' B} ∪
      (Gᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_preimage, relProc, hω, ↓reduceIte, newHorizon_of_good hv (hgood ω hω), ENNReal.coe_lt_top,
        true_and, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_true_eq_false, false_and, or_false]
      rfl
    · simp only [mem_preimage, relProc, hω, ↓reduceIte, not_lt_zero, false_and, mem_ofPred_eq, mem_union,
        mem_inter_iff, mem_compl_iff, not_false_eq_true, true_and, false_or]
  rw [hset]
  refine MeasurableSet.union ?_ (hGτ.compl.inter (MeasurableSet.const _))
  exact hAB u _ ((measurable_const.mul (measurable_const.mul measurable_id)) hB)

end Meas

end Proc

end InteractingSLE.Theorem14.BR4aChain
