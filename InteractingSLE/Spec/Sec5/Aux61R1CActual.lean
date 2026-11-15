/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CIncid
import InteractingSLE.Spec.Sec5.Aux61R1CBuild
import InteractingSLE.Spec.Sec5.Aux61SlitWSettingFields

/-!
# The actual restart records are regular, and good under the source's restart conditions

Packet PROVE-AUX61-R1CHART. For a source setting `S`, the record of the actual sample at the counterflow time `s` and a
rational own time `q` is `actRec S q p` (the record `RestartChoices.record` of any index with restart time `q`).

* `ae_regRec`: almost surely, for every rational `q > 0`, the actual record is regular (`RegRec`): the own state is
  continuous with infinite lifetime, the own trace generates the chain, the flow line is a proper arc (injective, in
  `ℍ` after time `0`), and the good counterflow history protects the original target.
* `ae_actRec_reading`: almost surely the record readers are the physical objects: the record trace is the flow line
  on `[0, q]`, the record driver is the own driver there, and the record hull is the glued counterflow hull.
* `ae_mem_goodSet_of_frequent`: almost surely, for every rational `q > 0`, the actual record is good as soon as the
  source's restart conditions hold: the tip `η(q)` is at positive distance from the counterflow hull `K_s`, and the
  current access (the own inverse map at `q` near `0`) frequently lies in a component of the retained domain
  `ℍ ∖ (K_s ∪ η[0, q])` with `1` in its closure. This is the form the history cover needs.
  `ae_mem_goodSet_of_fresh`: the same with the access given by a fresh segment of the flow line after `q`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61R1C

open LawUnique Restart.FlowStopIdentG Aux61Restart Aux61Marks Aux61Asm2
open Aux61SlitW (rationalTime SourceSetting)
open Aux61ULoc (stopRec)
open GlueCond (cfHullQ)

universe u

/-! ### Deterministic lemmas on killed histories and proper arcs -/

section Det

variable {nL nR : ℕ} {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {ω : Ω}

/-- The samples of a stopped killed history of infinite lifetime are the states. -/
theorem stopRec_killed_sample (hζ : ζ ω = ⊤) {r : ℝ≥0} {p : ℕ × ℕ} (hp : dyadicTime p ≤ r) :
    (stopRec r (killedHistory W VL VR ζ ω)).2 p = (W (dyadicTime p) ω, fun i => VL i (dyadicTime p) ω,
      fun j => VR j (dyadicTime p) ω) := by
  simp only [stopRec, Sec4.stopHistory, hp, ↓reduceIte, killedHistory, hζ, ENNReal.coe_lt_top]

/-- **The stopped record of a continuous state of infinite lifetime carries the state certificate.** -/
theorem stateCert_stopRec_killed (hζ : ζ ω = ⊤) (hW0 : W 0 ω = 0)
    (hc : Continuous fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (r : ℝ≥0) :
    StateCert r (stopRec r (killedHistory W VL VR ζ ω)) := by
  refine ⟨?_, fun m => ?_⟩
  · rw [stopRec_killed_sample hζ (by simp [dyadicTime])]
    simp [dyadicTime, hW0]
  · have hu := (isCompact_Icc (a := (0 : ℝ≥0)) (b := r)).uniformContinuousOn_of_continuous hc.continuousOn
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 hu (1 / ((m : ℝ) + 1)) (by positivity)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
    refine ⟨k, fun p p' hp hp' hd => ?_⟩
    rw [stopRec_killed_sample hζ hp, stopRec_killed_sample hζ hp']
    exact (hδu _ ⟨zero_le, hp⟩ _ ⟨zero_le, hp'⟩ (hd.trans hk)).le

/-- The state read from the stopped record of a continuous state of infinite lifetime. -/
theorem histState_stopRec_killed (hζ : ζ ω = ⊤)
    (hc : Continuous fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) {r t : ℝ≥0} (ht : t ≤ r) :
    histState (stopRec r (killedHistory W VL VR ζ ω)) t = (W t ω, fun i => VL i t ω, fun j => VR j t ω) := by
  rw [histState_stopRec_of_le ht, histState_killedHistory hc.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)]

/-- The frozen driver read from the stopped record is the driver frozen at `r`. -/
theorem frozenDrv_stopRec_killed (hζ : ζ ω = ⊤)
    (hc : Continuous fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (r t : ℝ≥0) :
    frozenDrv r (stopRec r (killedHistory W VL VR ζ ω)) t = W (min t r) ω := by
  rw [frozenDrv, histState_stopRec_killed hζ hc (min_le_right t r)]

/-- **Positive separation of disjoint pieces of an injective path**, as a rational lower bound. -/
theorem exists_one_div_le_norm_sub {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0)) (hinj : InjOn γ (Ici 0)) {b c d : ℝ}
    (hb : 0 ≤ b) (hbc : b < c) (hcd : c ≤ d) :
    ∃ m : ℕ, ∀ u ∈ Icc 0 b, ∀ v ∈ Icc c d, 1 / ((m : ℝ) + 1) ≤ ‖γ u - γ v‖ := by
  have hK : IsCompact (Icc (0 : ℝ) b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hne : (Icc (0 : ℝ) b ×ˢ Icc c d).Nonempty := ⟨(0, c), ⟨le_rfl, hb⟩, le_rfl, hcd⟩
  have hsub1 : MapsTo Prod.fst (Icc (0 : ℝ) b ×ˢ Icc c d) (Ici 0) := fun x hx => hx.1.1
  have hsub2 : MapsTo Prod.snd (Icc (0 : ℝ) b ×ˢ Icc c d) (Ici 0) := fun x hx =>
    (hb.trans (hbc.le.trans hx.2.1) : (0 : ℝ) ≤ x.2)
  have hf : ContinuousOn (fun x : ℝ × ℝ => ‖γ x.1 - γ x.2‖) (Icc (0 : ℝ) b ×ˢ Icc c d) :=
    ((hc.comp continuousOn_fst hsub1).sub (hc.comp continuousOn_snd hsub2)).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hf
  have hpos : 0 < ‖γ x₀.1 - γ x₀.2‖ := by
    refine norm_pos_iff.2 (sub_ne_zero.2 fun he => ?_)
    have h := hinj (hsub1 hx₀) (hsub2 hx₀) he
    have h1 : x₀.1 ≤ b := hx₀.1.2
    have h2 : c ≤ x₀.2 := hx₀.2.1
    linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  exact ⟨m, fun u hu v hv => hm.le.trans (hmin (show (u, v) ∈ Icc (0 : ℝ) b ×ˢ Icc c d from ⟨hu, hv⟩))⟩

/-- **A positive lower bound of the imaginary part** of a path in `ℍ` on a compact window away from `0`. -/
theorem exists_one_div_le_im {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0)) (hH : ∀ t, 0 < t → γ t ∈ H) {a d : ℝ}
    (ha : 0 < a) : ∃ m : ℕ, ∀ u ∈ Icc a d, 1 / ((m : ℝ) + 1) ≤ (γ u).im := by
  rcases (Icc a d).eq_empty_or_nonempty with he | hne
  · exact ⟨0, fun u hu => by rw [he] at hu; exact absurd hu (notMem_empty u)⟩
  have hsub : MapsTo id (Icc a d) (Ici 0) := fun x hx => (ha.le.trans hx.1 : (0 : ℝ) ≤ x)
  have hf : ContinuousOn (fun x => (γ x).im) (Icc a d) :=
    Complex.continuous_im.comp_continuousOn (hc.mono fun x hx => hsub hx)
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
  have hpos : 0 < (γ x₀).im := hH x₀ (ha.trans_le hx₀.1)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  exact ⟨m, fun u hu => hm.le.trans (hmin hu)⟩

end Det

/-! ### The actual records -/

variable (S : SourceSetting.{u})

/-- **The record of the actual sample** at the counterflow time `s` and the own time `q`. -/
def actRec (q : ℚ) (p : S.Ω × HistorySpace 0 0) : Rec S.nL S.nR :=
  (stopRec (rationalTime S.s) p.2,
    stopRec (rationalTime q) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))

theorem RestartChoices.record_eq_actRec (C : RestartChoices S) (i : C.ι) (p : S.Ω × HistorySpace 0 0) :
    C.record i p = actRec S (C.q i) p := rfl

/-- On the good paths the own state is continuous. -/
theorem continuous_state_of_isGoodPath {ω : S.Ω} (hg : Aux50Hit.IsGoodPath S.own.W S.own.VL S.own.VR S.life ω) :
    Continuous fun t => (S.own.W t ω, fun i => S.own.VL i t ω, fun j => S.own.VR j t ω) := by
  obtain ⟨hζ, -, hW, hL, hR⟩ := hg
  have huniv : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < S.life ω} → Continuous f := fun h =>
    continuousOn_univ.1 (h.mono fun t _ => by rw [mem_ofPred_eq, hζ]; exact ENNReal.coe_lt_top)
  exact (huniv hW).prodMk ((continuous_pi fun i => huniv (hL i)).prodMk (continuous_pi fun j => huniv (hR j)))

/-- **Almost surely the record readers are the physical objects**: on `[0, q]` the record trace is the flow line and
the record driver is the own driver; the record hull is the glued counterflow hull. -/
theorem ae_actRec_reading : ∀ᵐ p ∂S.μ, ∀ q : ℚ,
    (∀ t : ℝ, t ≤ q → recTrace (actRec S q p).2 t = S.path p.1 t.toNNReal) ∧
    (∀ t : ℝ≥0, recU q t (actRec S q p) = S.own.W (min t (rationalTime q)) p.1) ∧
    recHull (rationalTime S.s) (actRec S q p) = cfHullQ (rationalTime S.s) p.2 := by
  filter_upwards [ae_trace_eq_and_continuous S, ae_mem_goodCfSet S, S.physical_path] with p htr hcf hg q
  refine ⟨fun t ht => ?_, fun t => ?_, historyHull_stopRec_eq_cfHullQ hcf _⟩
  · have hle : t.toNNReal ≤ rationalTime q := Real.toNNReal_le_toNNReal ht
    show histTrace 0 (stopRec (rationalTime q) _) t.toNNReal = _
    rw [histTrace_stopRec_of_le hle, htr.1]
  · exact frozenDrv_stopRec_killed hg.1.1 (continuous_state_of_isGoodPath S hg.1) _ _

/-- **Almost surely the actual records are regular** at every rational own time `q > 0`. -/
theorem ae_regRec : ∀ᵐ p ∂S.μ, ∀ q : ℚ, 0 < q → RegRec (rationalTime S.s) q (actRec S q p) := by
  have htrace := WangWu.ae_glue_fst (μ := S.P) S.kernel S.measCounterField S.own.trace
  filter_upwards [ae_actRec_reading S, S.physical_path, S.counterflow_good, htrace] with p hread hg hcf hgen q hq
  have hc := continuous_state_of_isGoodPath S hg.1
  have hζ : S.life p.1 = ⊤ := hg.1.1
  set r := rationalTime q with hr
  have hqq : (0 : ℚ) ≤ q := hq.le
  have hrq : (r : ℝ) = q := coe_rationalTime hqq
  have harc := hg.2.2
  refine ⟨hq, stateCert_stopRec_killed hζ hg.1.2.1 hc r, ?_, ?_, ?_, ?_⟩
  · -- the trace certificate
    have hS := stateCert_stopRec_killed hζ hg.1.2.1 hc r
    have hcont := hS.continuous_frozenDrv
    refine (Sec7.RandRestart.mem_traceSet_iff hcont.continuousOn hS.frozenDrv_zero
      fun _ _ => ⟨_, (hcont.tendsto _).mono_left nhdsWithin_le_nhds⟩).2 ?_
    have hgen' : IsGeneratingTrace (fun t => S.own.W t p.1) (r : ℝ≥0∞) (fun t => S.path p.1 t - ((0 : ℝ) : ℂ)) := by
      rw [hζ] at hgen
      exact ⟨hgen.1, hgen.2.1.mono fun _ _ => (le_top : _ ≤ (⊤ : ℝ≥0∞)),
        fun t ht => hgen.2.2 t (lt_of_lt_of_le ht le_top)⟩
    refine Sec7.RandRestart.TraceEvent.congr ⟨_, hgen', fun h => absurd h ENNReal.coe_ne_top⟩ fun t ht => ?_
    rw [frozenDrv_stopRec_killed hζ hc, min_eq_left (ENNReal.coe_le_coe.1 ht.le)]
  · -- injectivity
    intro b c hb hbc hcq
    obtain ⟨m, hm⟩ := exists_one_div_le_norm_sub (b := (b : ℝ)) (c := (c : ℝ)) (d := (q : ℝ)) harc.cont harc.inj
      (by exact_mod_cast hb) (by exact_mod_cast hbc) (by exact_mod_cast hcq)
    refine ⟨m, fun u v hu0 hub hcv hvq => ?_⟩
    rw [(hread q).1 u (by exact_mod_cast hub.trans (hbc.le.trans hcq)), (hread q).1 v (by exact_mod_cast hvq)]
    exact hm u ⟨by exact_mod_cast hu0, by exact_mod_cast hub⟩ v ⟨by exact_mod_cast hcv, by exact_mod_cast hvq⟩
  · -- interior position
    intro a ha haq
    obtain ⟨m, hm⟩ := exists_one_div_le_im (a := (a : ℝ)) (d := (q : ℝ)) harc.cont harc.mem_H
      (by exact_mod_cast ha)
    refine ⟨m, fun u hau huq => ?_⟩
    rw [(hread q).1 u (by exact_mod_cast huq)]
    exact hm u ⟨by exact_mod_cast hau, by exact_mod_cast huq⟩
  · -- protection of the original target
    have h := original_target_protected_of_goodHit hcf (rationalTime S.s)
    show (1 : ℂ) ∉ closure (WangWu.negInv '' fwdHull (CrossCond.Word49.cfDrv0 (rationalTime S.s)
      (stopRec (rationalTime S.s) p.2)) (rationalTime S.s))
    rwa [show stopRec (rationalTime S.s) p.2 = GlueCond.cfStop (rationalTime S.s) p.2 from rfl,
      CrossCond.Word49.cfDrv0_cfStop]

/-- **The source's restart conditions make the actual record good** (almost surely, for every rational `q > 0`): the
tip at positive distance from the glued counterflow hull, and the current access frequently in a component of the
physical retained domain with `1` in its closure. -/
theorem ae_mem_goodSet_of_frequent : ∀ᵐ p ∂S.μ, ∀ q : ℚ, 0 < q →
    0 < infDist (S.path p.1 (rationalTime q)) (cfHullQ (rationalTime S.s) p.2) →
    ∀ b : ℂ, (1 : ℂ) ∈ closure (restartComponent (cfHullQ (rationalTime S.s) p.2)
      (fun t : ℝ => S.path p.1 t.toNNReal) q b) →
    (∃ᶠ w in 𝓝[H] 0, fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) q w ∈
      restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal) q b) →
    actRec S q p ∈ Aux61R1C.goodSet (rationalTime S.s) q := by
  filter_upwards [ae_regRec S, ae_actRec_reading S, S.physical_path] with p hreg hread hg q hq hK b hb hf
  have hy := hreg q hq
  obtain ⟨htr, hU, hhull⟩ := hread q
  have hqq : (0 : ℚ) ≤ q := hq.le
  have hrq : ((rationalTime q : ℝ≥0) : ℝ) = q := coe_rationalTime hqq
  have hη : EqOn (recη q (actRec S q p)) (fun t : ℝ => S.path p.1 t.toNNReal) (Icc 0 (q : ℝ)) := fun t ht => by
    rw [recη_of_le hqq _ ht.2, htr t ht.2]
  have hcomp : restartComponent (recHull (rationalTime S.s) (actRec S q p)) (recη q (actRec S q p)) q b =
      restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal) q b := by
    unfold restartComponent retainedDomain
    rw [hhull, hη.image_eq]
  have htip : recTrace (actRec S q p).2 q = S.path p.1 (rationalTime q) := htr q le_rfl
  have hW : Continuous fun t : ℝ => S.own.W t.toNNReal p.1 :=
    ((continuous_fst.comp (continuous_state_of_isGoodPath S hg.1))).comp continuous_real_toNNReal
  have hy' := hy.facts
  have hdrv : ∀ w ∈ H, fwdMapInv (Ito.rpath fun t => recU q t (actRec S q p)) (rationalTime q) w =
      fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) q w := by
    intro w hw
    rw [hrq]
    refine LP.fwdMapInv_eq_of_eqOn_Icc (Chart.continuous_rpath_of_continuous hy'.2.1)
      hW (Chart.rpath_zero_of hy'.2.2.1) (by simpa using hg.1.2.1) (by exact_mod_cast hqq) (fun t ht => ?_) hw
    show recU q t.toNNReal (actRec S q p) = S.own.W t.toNNReal p.1
    rw [hU, min_eq_left (Real.toNNReal_le_toNNReal (ht.2.trans hrq.symm.le) |>.trans_eq (Real.toNNReal_coe))]
  refine mem_goodSet_of_frequent (rationalTime_s_pos S) hy ?_ (hcomp ▸ hb) ?_
  · rwa [htip, hhull]
  · rw [hcomp]
    refine (hf.and_eventually self_mem_nhdsWithin).mono fun w hw => ?_
    rw [hdrv w hw.2]
    exact hw.1

/-- **The source's fresh-segment form** (Astra follow-up 4, Part (1), §1.1): almost surely, for every rational `q > 0`,
the actual record is good when the tip is at positive distance from the glued counterflow hull and the flow line after
`q` runs for a while in a component of the physical retained domain with `1` in its closure (R1's
`Aux61Restart.history_current_incidence_of_fresh_segment` turns the segment into the frequent current access). -/
theorem ae_mem_goodSet_of_fresh : ∀ᵐ p ∂S.μ, ∀ q : ℚ, 0 < q →
    0 < infDist (S.path p.1 (rationalTime q)) (cfHullQ (rationalTime S.s) p.2) →
    ∀ (b : ℂ) (T : ℝ), (1 : ℂ) ∈ closure (restartComponent (cfHullQ (rationalTime S.s) p.2)
      (fun t : ℝ => S.path p.1 t.toNNReal) q b) → (q : ℝ) < T →
    MapsTo (fun t : ℝ => S.path p.1 t.toNNReal) (Ioc (q : ℝ) T)
      (restartComponent (cfHullQ (rationalTime S.s) p.2) (fun t : ℝ => S.path p.1 t.toNNReal) q b) →
    actRec S q p ∈ Aux61R1C.goodSet (rationalTime S.s) q := by
  filter_upwards [ae_mem_goodSet_of_frequent S, S.physical_path, ae_mem_goodCfSet S] with p hgood hg hcf q hq hK b T
    hb hqT hseg
  have hrq : ((rationalTime q : ℝ≥0) : ℝ) = q := coe_rationalTime hq.le
  have hW : Continuous fun t : ℝ≥0 => S.own.W t p.1 := continuous_fst.comp (continuous_state_of_isGoodPath S hg.1)
  have hhull : historyHull (rationalTime S.s) (fun _ : Unit => stopRec (rationalTime S.s) p.2) () =
      cfHullQ (rationalTime S.s) p.2 := historyHull_stopRec_eq_cfHullQ hcf ()
  have harc := hg.2.2
  obtain ⟨b', hb', hf⟩ := history_current_incidence_of_fresh_segment (Ω := Unit) (s := rationalTime S.s)
    (r := rationalTime q) (q := q) hrq (Y := fun _ => stopRec (rationalTime S.s) p.2)
    (η := fun _ t => S.path p.1 t.toNNReal) (U := fun t _ => S.own.W t p.1) (fun _ => hW) (fun _ => hg.1.2.1)
    (fun _ => hg.2.1) (fun _ => harc.inj.mono Icc_subset_Ici_self) (fun _ t ht => harc.mem_H t ht.1)
    (fun _ => ⟨b, T, by rwa [hhull], by rwa [hrq], by rwa [hhull, hrq]⟩) ()
  rw [hhull] at hb' hf
  refine hgood q hq hK b' hb' ?_
  change ∃ᶠ w in 𝓝[H] 0, fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) ((rationalTime q : ℝ≥0) : ℝ) w ∈ _ at hf
  rwa [hrq] at hf

end InteractingSLE.Sec5.Aux61R1C
