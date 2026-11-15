/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HQJunction
import InteractingSLE.Spec.Sec5.Prop49QExitKilled

/-!
# The junction exit of a killed `SLE_κ(ρ)` word

Packet PROVE-PROP51H (`FwdNoContactQStatement`). The image word of the flow line in the counterflow chart is only
known up to its first contact with the counterflow hull (a killed word, `CrossCond.Theta`). As for Aux. lemma 22's
left span (PROVE-GLUECOND9/11, `Prop49Exit.ae_leftExit_of_killed_ord`), the junction end of the integrated word
(`Prop51HQJunction`) is transferred to the killed word by restarting at rational times: the canonical solution from the
restarted state agrees with the killed word before the killing time, and its junction end is a Borel event of
solution codes.

* `JStart`, `jendCode`, `jexitCode`: the restart event (a code whose start has negative left and positive right marks
  and its last left mark strictly left of the first has a strip end at its last left mark), Borel by Lusin–Souslin;
  **`codeLaw_compl_jexitCode_eq_zero`**: it has full canonical law at every separated ordered start
  (`ae_jEnd_of_integrated_ord`);
* `junctionExit_of_restart` (one path; `Prop49Exit.leftExit_of_restart` with the end point kept): a killed trace in
  `ℍ` converges at its killing time, to a point of `ℍ` or to `F̄_q(y)`, `y` the restarted junction;
* **`ae_junctionExit_of_killed`**: the junction exit of a killed word.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop51H

open Prop49Exit Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### The junction end as a Borel event of solution codes -/

section Code

variable {j nR : ℕ} {a : ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin nR → ℝ}

/-- `EndCond` with a fixed end point only sees the driver before the horizon. -/
theorem endCond_congr {e y : ℝ} {S : ℝ≥0} (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (h : EndCond e w τ S y) : EndCond e w' τ S y := by
  obtain ⟨hS0, hSτ, hy0, hye, htr, hav, hlim⟩ := h
  have hlt : ∀ t : ℝ≥0, t < S → w t = w' t := fun t ht =>
    hww' t (lt_of_lt_of_le (by exact_mod_cast ht) hSτ)
  have hta : ∀ p : ℝ≥0, p < S → LP.traceAt p w = LP.traceAt p w' := fun p hp =>
    LP.traceAt_congr fun s hs => hlt s (lt_of_le_of_lt hs hp)
  refine ⟨hS0, hSτ, hy0, hye, fun r hr => mem_traceSet_congr (fun t ht => hlt t (ht.trans hr)) (htr r hr),
    fun n r hr => ?_, fun k => ?_⟩
  · obtain ⟨m, hm⟩ := hav n r hr
    exact ⟨m, fun p hp => by rw [← hta p (lt_of_le_of_lt (by exact_mod_cast hp) hr)]; exact hm p hp⟩
  · obtain ⟨m, hm⟩ := hlim k
    exact ⟨m, fun p hp hpS => by rw [← hta p hpS]; exact hm p hp hpS⟩

/-- The pairs (code, end time, end point) of a strip end at the last left mark (bound: the first left mark). -/
def JEndSet (a : ℝ) (ρL : Fin (j + 1) → ℝ) (ρR : Fin nR → ℝ) : Set (XCode (j + 1) nR × (ℝ≥0 × ℝ)) :=
  EndSet a ρL ρR (fun s => s.1 0) ∩ {p | p.2.2 = (startOf p.1).1 (Fin.last j)}

/-- **The codes with a strip end at the last left mark.** -/
def jendCode (a : ℝ) (ρL : Fin (j + 1) → ℝ) (ρR : Fin nR → ℝ) : Set (XCode (j + 1) nR) :=
  Prod.fst '' JEndSet a ρL ρR

theorem measurableSet_jendCode : MeasurableSet (jendCode a ρL ρR) := by
  have he : Measurable fun s : (Fin (j + 1) → ℝ) × (Fin nR → ℝ) => s.1 0 :=
    (measurable_pi_apply 0).comp measurable_fst
  have hJ : MeasurableSet (JEndSet a ρL ρR) := by
    refine (measurableSet_endSet a ρL ρR he).inter (measurableSet_eq_fun (measurable_snd.comp measurable_snd) ?_)
    exact ((measurable_pi_apply (Fin.last j)).comp measurable_fst).comp (measurable_startOf.comp measurable_fst)
  exact hJ.image_of_measurable_injOn measurable_fst (injOn_fst_endSet.mono inter_subset_left)

/-- The coding on canonical codes from a start. -/
theorem mem_jendCode_iff {s : (Fin (j + 1) → ℝ) × (Fin nR → ℝ)} {x : XCode (j + 1) nR}
    (hx : x ∈ CRel a s.1 s.2 ρL ρR) :
    x ∈ jendCode a ρL ρR ↔ ∃ S : ℝ≥0, EndCond (s.1 0) (cw x) (cζ x) S (s.1 (Fin.last j)) := by
  obtain ⟨hxF, hst⟩ := mem_cRelF_iff.2 hx
  constructor
  · rintro ⟨⟨x', S, y⟩, ⟨⟨-, h⟩, hy⟩, rfl⟩
    simp only [mem_ofPred_eq] at hy
    rw [hst] at h hy
    rw [hy] at h
    exact ⟨S, h⟩
  · rintro ⟨S, h⟩
    exact ⟨(x, S, s.1 (Fin.last j)), ⟨⟨hxF, by rw [hst]; exact h⟩, by simp only [mem_ofPred_eq]; rw [hst]⟩, rfl⟩

/-- A start with negative left and positive right marks, the last left mark strictly left of the first. -/
def JStart (s : (Fin (j + 1) → ℝ) × (Fin nR → ℝ)) : Prop := SignStart s ∧ s.1 (Fin.last j) < s.1 0

theorem measurableSet_jStart : MeasurableSet {s : (Fin (j + 1) → ℝ) × (Fin nR → ℝ) | JStart s} := by
  refine measurableSet_signStart.inter ?_
  exact measurableSet_lt ((measurable_pi_apply _).comp measurable_fst) ((measurable_pi_apply _).comp measurable_fst)

/-- **The junction restart event**: a code whose start is a `JStart` has a strip end at its last left mark. -/
def jexitCode (a : ℝ) (ρL : Fin (j + 1) → ℝ) (ρR : Fin nR → ℝ) : Set (XCode (j + 1) nR) :=
  {x | JStart (startOf x)}ᶜ ∪ jendCode a ρL ρR

theorem measurableSet_jexitCode : MeasurableSet (jexitCode a ρL ρR) :=
  (measurableSet_jStart.preimage measurable_startOf).compl.union measurableSet_jendCode

theorem codeLaw_compl_jexitCode_of_not {s : (Fin (j + 1) → ℝ) × (Fin nR → ℝ)} (hs : ¬ JStart s) :
    codeLaw a ρL ρR (jexitCode a ρL ρR)ᶜ s = 0 := by
  refine measure_mono_null (fun f hf => ?_) measure_empty
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxe⟩ := hf
  simp only [Prod.mk.injEq] at hxe
  exact hxS (Or.inl (show ¬ JStart (startOf x) by rw [hxe.1]; exact hs))

theorem mem_jexitCode_iff {s : (Fin (j + 1) → ℝ) × (Fin nR → ℝ)} (hs : JStart s) {x : XCode (j + 1) nR}
    (hx : x ∈ CRel a s.1 s.2 ρL ρR) :
    x ∈ jexitCode a ρL ρR ↔ ∃ S : ℝ≥0, EndCond (s.1 0) (cw x) (cζ x) S (s.1 (Fin.last j)) := by
  rw [← mem_jendCode_iff hx]
  have hst := (mem_cRelF_iff.2 hx).2
  constructor
  · rintro (h | h)
    · exact absurd (show JStart (startOf x) by rw [hst]; exact hs) h
    · exact h
  · exact Or.inr

/-- **The junction restart event has full canonical law at every separated ordered start** (`0 < κ ≤ 4`, at least one
right mark, prefix sums at least `κ/2 − 2` before the junction and on the right, left total at most `κ/2 − 4`). -/
theorem codeLaw_compl_jexitCode_eq_zero {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hn : 0 < nR)
    (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR) (hlow : ∑ i, ρL i ≤ κ / 2 - 4)
    (s : (Fin (j + 1) → ℝ) × (Fin nR → ℝ)) (hsep : SepStart s) (hF : IsOrderedForceWord s.1 s.2) :
    codeLaw κ ρL ρR (jexitCode κ ρL ρR)ᶜ s = 0 := by
  by_cases hs : JStart s
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
      exists_isIntegratedSLEEvolution_assembled (a := κ) hκ hF
    exact codeLaw_compl_eq_zero_of_ae hκ hsep hE₀ measurableSet_jexitCode
      (Φ := fun w τ => ∃ S : ℝ≥0, EndCond (s.1 0) w τ S (s.1 (Fin.last j)))
      (fun x hx _ => mem_jexitCode_iff hs hx)
      (fun w w' τ hww' ⟨S, h⟩ => ⟨S, endCond_congr w w' τ hww' h⟩)
      (ae_jEnd_of_integrated_ord hκ hκ4 (j + nR) le_rfl hE₀ hF.1 hs.1.1 hs.2 hF.2.2.1 hs.1.2 hn hpre hlow)
  · exact codeLaw_compl_jexitCode_of_not hs

end Code

/-! ### The pathwise junction exit after a restart -/

section Pathwise

/-- **The pathwise junction exit** (`Prop49Exit.leftExit_of_restart` with the end point `y` kept). Let `γ` generate
the chain of `w` before `T`, in `ℍ` at positive times; let `c` agree with the restarted driver `w(q + ·) − w(q)` before
`T − q` and have a strip end `(S, y)`; let `F̄_q(y) ∉ ℍ`. Then `T` is finite and `γ` converges at `T`, to a point of
`ℍ` or to `F̄_q(y)`. -/
theorem junctionExit_of_restart {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → Sec7.IsGeneratingTraceIcc w s γ)
    (hγH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T → γ t ∈ H) {q : ℝ≥0} (hq0 : 0 < q) (hqT : (q : ℝ≥0∞) < T)
    {c : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} (hcc : ContinuousOn c {t | (t : ℝ≥0∞) < ζc}) (hc0 : c 0 = 0)
    (hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T - q → c t = w (q + t) - w q)
    {e : ℝ} {S : ℝ≥0} {y : ℝ} (hend : EndCond e c ζc S y)
    (hgeo : extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) y ∉ H) :
    T ≠ ⊤ ∧ ∃ z : ℂ, Tendsto γ (𝓝[<] T.toNNReal) (𝓝 z) ∧
      (z ∈ H ∨ z = extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) y) := by
  obtain ⟨hS0, hSζ, -, -, htr, hav, hlim⟩ := hend
  set F := extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) with hFdef
  -- the extension `F̄_q`
  obtain ⟨t₂, hqt₂, ht₂T⟩ := exists_real_btwn_of_lt hqT
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  have hwfz := continuous_frozenDrive_of_lt hwc ht₂T
  have hW0' : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  obtain ⟨hFeq, -, hEq, hFc, -, -, hF0⟩ := (hγ q hqT).extend_props hqt₂ hwfz hw0
  have hFc' : ContinuousOn F Hbar := by rw [hFdef, hFeq]; exact hFc
  have hF0' : F 0 = γ q := by rw [hFdef, hFeq]; exact hF0
  have hFH : ∀ v ∈ H, F v ∈ H := fun v hv => by
    rw [hFdef, hFeq, hEq hv]
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hwfz hW0' q.coe_nonneg hv).1
  -- the concatenation `X` of `w` before `q` and `c` after `q`
  set X : ℝ≥0 → ℝ := concatAt q w (w q) c with hXdef
  have hcq : w q + c 0 = w q := by rw [hc0, add_zero]
  have hXc : ContinuousOn X {s | (s : ℝ≥0∞) < (q : ℝ≥0∞) + ζc} := continuousOn_concatAt hqT hwc hcc hcq
  have hX0 : X 0 = 0 := by rw [hXdef, concatAt_of_lt hq0]; exact hw0
  have hXw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → X t = w t := by
    intro t ht
    rcases lt_or_ge t q with htq | htq
    · exact concatAt_of_lt htq
    · rw [hXdef, concatAt_of_le htq]
      have hlt : ((t - q : ℝ≥0) : ℝ≥0∞) < T - q := by
        rw [Assembly2.coe_lt_sub_iff, add_tsub_cancel_of_le htq]; exact ht
      rw [hagree _ hlt, add_tsub_cancel_of_le htq]
      ring
  have hshift : Sec7.shiftNN X q = c := by
    funext u
    simp only [Sec7.shiftNN, hXdef, concatAt_of_le (le_add_of_nonneg_right zero_le : q ≤ q + u),
      concatAt_of_le (le_refl q), add_tsub_cancel_left, tsub_self, hc0]
    ring
  have h₁ : Sec7.IsGeneratingTraceIcc X q γ :=
    WangWu.ImgDrv.IsGeneratingTraceIcc.congr_of_lt (hγ q hqT) hqT fun t ht => (hXw t ht).symm
  have hSζ' : ∀ r : ℝ≥0, r ≤ S → (r : ℝ≥0∞) ≤ ζc := fun r hr => (by exact_mod_cast hr : (r : ℝ≥0∞) ≤ S).trans hSζ
  -- traces of `c` on `[0, r]`, `r < S` rational, around each time `u < S`
  have hctr : ∀ u : ℝ≥0, u < S → ∃ r : ℚ≥0, u < (r : ℝ≥0) ∧ (r : ℝ≥0) < S ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace c ((r : ℝ≥0) : ℝ≥0∞) η := by
    intro u hu
    obtain ⟨r, hr1, hr2⟩ := exists_nnrat_btwn' u.coe_nonneg (show (u : ℝ) < S from hu)
    have hr2' : (r : ℝ≥0) < S := by exact_mod_cast hr2
    exact ⟨r, by exact_mod_cast hr1, hr2', exists_trace_of_trQ hcc hc0 hSζ htr hr2'⟩
  -- the key identity `γ(q + u) = F̄_q(η(u))`
  have hKI : ∀ u : ℝ≥0, 0 < u → u < S → ((q + u : ℝ≥0) : ℝ≥0∞) < T → γ (q + u) = F (LP.traceAt u c) := by
    intro u hu0 huS hquT
    obtain ⟨r, hur, hrS, η, hη⟩ := hctr u huS
    have hXr : ContinuousOn X {s | (s : ℝ≥0∞) < (q : ℝ≥0∞) + ((r : ℝ≥0) : ℝ≥0∞)} :=
      hXc.mono fun s (hs : (s : ℝ≥0∞) < (q : ℝ≥0∞) + ((r : ℝ≥0) : ℝ≥0∞)) =>
        show (s : ℝ≥0∞) < (q : ℝ≥0∞) + ζc from lt_of_lt_of_le hs (add_le_add_right (hSζ' _ hrS.le) _)
    have hJ := (Sec7.IsGeneratingTraceIcc.join hXr hX0 h₁ (by rw [hshift]; exact hη)).1
    have e1 : LP.traceAt (q + u) X = Sec7.joinTrace X q γ η (q + u) :=
      LP.traceAt_eq_of_isGeneratingTrace hJ hXr hX0 (by exact_mod_cast add_lt_add_right hur q)
    have e2 : LP.traceAt (q + u) X = LP.traceAt (q + u) w :=
      LP.traceAt_congr fun s hs => hXw s (lt_of_le_of_lt (by exact_mod_cast hs) hquT)
    obtain ⟨s', hs'1, hs'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hquT
    have e3 : LP.traceAt (q + u) w = γ (q + u) :=
      LP.traceAt_eq_of_isGeneratingTrace (hγ s' hs'2).1 (hwc.mono fun t ht => lt_trans ht hs'2) hw0 hs'1
    have e4 := Sec7.joinTrace_of_lt (w := X) (η₁ := γ) (η₂ := η) (lt_add_of_pos_right q hu0)
    have e5 : fwdMapInv (fun s : ℝ => X s.toNNReal) q = fwdMapInv (fun s : ℝ => w s.toNNReal) q := by
      refine fwdMapInv_eq_of_eqOn q.coe_nonneg hqt₂ fun r hr => hXw _ ?_
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hr.2) ht₂T
    have e6 : η u = LP.traceAt u c := (traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hrS.le) hur).symm
    rw [← e3, ← e2, e1, e4, e5, add_tsub_cancel_left, e6]
  -- the evaluation of `c` is continuous before `S` and lies in `ℍ̄`
  have hcont : ∀ u : ℝ≥0, u < S → ContinuousAt (fun t => LP.traceAt t c) u := by
    intro u hu
    obtain ⟨r, hur, hrS, η, hη⟩ := hctr u hu
    have hηc : ContinuousAt η u :=
      (hη.2.1.mono fun t (ht : t ∈ Iic (r : ℝ≥0)) => by exact_mod_cast ht).continuousAt (Iic_mem_nhds hur)
    refine hηc.congr ?_
    filter_upwards [Iio_mem_nhds hur] with t ht
    exact (traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hrS.le) ht).symm
  have hHbar : ∀ u : ℝ≥0, u < S → LP.traceAt u c ∈ Hbar := by
    intro u hu
    obtain ⟨r, hur, hrS, η, hη⟩ := hctr u hu
    rw [traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hrS.le) hur]
    exact Sec7.IsGeneratingTrace.mem_Hbar hη (hcc.mono fun t ht => lt_of_lt_of_le ht (hSζ' _ hrS.le)) hc0
      (by exact_mod_cast hur.le)
  have hyH : ((y : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im by simp
  have hconvS : Tendsto (fun t => LP.traceAt t c) (𝓝[<] S) (𝓝 (y : ℂ)) := tendsto_of_limQ hlim hcont
  have hFy : Tendsto (fun t => F (LP.traceAt t c)) (𝓝[<] S) (𝓝 (F y)) :=
    (hFc' _ hyH).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hconvS, by
      filter_upwards [self_mem_nhdsWithin] with t ht using hHbar t ht⟩)
  have hevS : ∀ᶠ u in 𝓝[<] S, 0 < u := eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hS0)
  rcases lt_trichotomy (((q + S : ℝ≥0)) : ℝ≥0∞) T with hlt | heq | hgt
  · -- `q + S < T` is impossible
    exfalso
    obtain ⟨s', hs'1, hs'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    have hγc : ContinuousAt γ (q + S) :=
      ((hγ s' hs'2).1.2.1.mono fun t (ht : t ∈ Iic s') => by exact_mod_cast ht).continuousAt
        (Iic_mem_nhds (by exact_mod_cast hs'1))
    have h1 : Tendsto (fun u => γ (q + u)) (𝓝[<] S) (𝓝 (γ (q + S))) :=
      (hγc.tendsto.comp ((continuous_const.add continuous_id).tendsto S)).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun u => γ (q + u)) (𝓝[<] S) (𝓝 (F y)) := by
      refine hFy.congr' ?_
      filter_upwards [hevS, self_mem_nhdsWithin] with u hu0 hu
      refine (hKI u hu0 hu (lt_of_le_of_lt ?_ hlt)).symm
      have : q + u ≤ q + S := add_le_add_right hu.le q
      exact_mod_cast this
    have : (𝓝[<] S).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hS0⟩
    have heq := tendsto_nhds_unique h1 h2
    have hmem := hγH (q + S) (by positivity) hlt
    rw [heq] at hmem
    exact hgeo hmem
  · -- `T = q + S`: convergence to `F̄_q(y)`
    have hT : T.toNNReal = q + S := by rw [← heq, ENNReal.toNNReal_coe]
    refine ⟨heq ▸ ENNReal.coe_ne_top, F y, ?_, Or.inr rfl⟩
    rw [hT]
    refine (tendsto_comp_tsub hS0 hFy).congr' ?_
    have hq : ∀ᶠ t in 𝓝[<] (q + S), q < t :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (lt_add_of_pos_right q hS0))
    filter_upwards [hq, self_mem_nhdsWithin] with t hqt ht
    have hu0 : 0 < t - q := tsub_pos_of_lt hqt
    have huS : t - q < S := by rw [tsub_lt_iff_left hqt.le]; exact ht
    have htT : (((q + (t - q) : ℝ≥0)) : ℝ≥0∞) < T := by
      rw [add_tsub_cancel_of_le hqt.le, ← heq]; exact_mod_cast ht
    have := hKI (t - q) hu0 huS htT
    rw [add_tsub_cancel_of_le hqt.le] at this
    exact this.symm
  · -- `T < q + S`: convergence to a point of `ℍ`
    have hTfin : T ≠ ⊤ := ne_top_of_lt hgt
    set T₀ := T.toNNReal with hT₀
    have hT₀T : (T₀ : ℝ≥0∞) = T := ENNReal.coe_toNNReal hTfin
    have hqT₀ : q < T₀ := by rw [← hT₀T] at hqT; exact_mod_cast hqT
    have hT₀S : T₀ < q + S := by rw [← hT₀T] at hgt; exact_mod_cast hgt
    set u₀ := T₀ - q with hu₀
    have hu₀0 : 0 < u₀ := tsub_pos_of_lt hqT₀
    have hu₀S : u₀ < S := by rw [hu₀, tsub_lt_iff_left hqT₀.le]; exact hT₀S
    set v := LP.traceAt u₀ c with hv
    -- `v` is not a nonzero real
    have hvreal : ∀ n : ℕ, v ∉ GlueCond.farReal n := by
      intro n
      obtain ⟨r', hr'1, hr'2⟩ := exists_nnrat_btwn' u₀.coe_nonneg (show (u₀ : ℝ) < S from hu₀S)
      have hr'S : (r' : ℝ≥0) < S := by exact_mod_cast hr'2
      obtain ⟨r₂, hr₂1, hr₂S, η, hη⟩ := hctr _ hr'S
      have hηc : ContinuousOn η (Icc 0 (r' : ℝ≥0)) :=
        hη.2.1.mono fun t ht => by exact_mod_cast ht.2.trans hr₂1.le
      have hηtr : ∀ p : ℚ≥0, p ≤ r' → LP.traceAt p c = η p := fun p hp =>
        traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hr₂S.le)
          (lt_of_le_of_lt (show (p : ℝ≥0) ≤ r' from by exact_mod_cast hp) hr₂1)
      have hvη : v = η u₀ := traceAt_eq_of_trace hη hcc hc0 (hSζ' _ hr₂S.le)
        (lt_trans (by exact_mod_cast hr'1) hr₂1)
      rw [hvη]
      exact notMem_farReal_of_avoidQ hr'S hηc le_rfl hηtr hav n hu₀0 (by exact_mod_cast hr'1.le)
    have hvH : F v ∈ H := by
      have hvbar := hHbar u₀ hu₀S
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ v.im from hvbar) with him | him
      · have hv0 : v = 0 := by
          by_contra hne
          have hre : v.re ≠ 0 := fun h0 => hne (Complex.ext h0 him.symm)
          obtain ⟨n, hn⟩ := exists_mem_farReal hre
          have hvr : v = ((v.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him.symm])
          exact hvreal n (by rw [hvr]; exact hn)
        rw [hv0, hF0']
        exact hγH q hq0 hqT
      · exact hFH v him
    refine ⟨hTfin, F v, ?_, Or.inl hvH⟩
    have hcT : Tendsto (fun t => LP.traceAt (t - q) c) (𝓝 T₀) (𝓝 v) := by
      have hc : Continuous fun t : ℝ≥0 => t - q := continuous_id.sub continuous_const
      exact (hcont u₀ hu₀S).tendsto.comp (hc.tendsto T₀)
    have hFv : Tendsto (fun t => F (LP.traceAt (t - q) c)) (𝓝[<] T₀) (𝓝 (F v)) := by
      refine (hFc' v (hHbar u₀ hu₀S)).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hcT.mono_left nhdsWithin_le_nhds, ?_⟩)
      have hq : ∀ᶠ t in 𝓝[<] T₀, q < t := eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hqT₀)
      filter_upwards [hq, self_mem_nhdsWithin] with t hqt ht
      refine hHbar _ (lt_of_le_of_lt (tsub_le_tsub_right (le_of_lt ht) q) hu₀S)
    refine hFv.congr' ?_
    have hq : ∀ᶠ t in 𝓝[<] T₀, q < t := eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hqT₀)
    filter_upwards [hq, self_mem_nhdsWithin] with t hqt ht
    have hu0 : 0 < t - q := tsub_pos_of_lt hqt
    have huS : t - q < S := lt_of_le_of_lt (tsub_le_tsub_right (le_of_lt ht) q) hu₀S
    have htT : (((q + (t - q) : ℝ≥0)) : ℝ≥0∞) < T := by
      rw [add_tsub_cancel_of_le hqt.le, ← hT₀T]; exact_mod_cast ht
    have := hKI (t - q) hu0 huS htT
    rw [add_tsub_cancel_of_le hqt.le] at this
    exact this.symm


end Pathwise

/-! ### The junction exit of a killed word -/

section Killed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓘 : Filtration ℝ≥0 mΩ}

/-- **The junction exit of a killed `SLE_κ(ρ)` word** (`0 < κ ≤ 4`; Aux. lemma 22's empty-span case through the
restart; `Prop49Exit.ae_leftExit_of_killed_ord` with the junction end). Let `(W, V)` be a killed word before `T` (the
integrated equations of its random initial word before `T`, a Brownian motion of a filtration, adapted,
`{q < T} ∈ 𝓘_q`, the marks strictly separated from the driver at positive times, almost surely some left mark
strictly right of the last one, below the threshold at `0`), with at least one right mark, whose left weights before
the last one and whose right weights have prefix sums at least `κ/2 − 2` and whose left total is at most `κ/2 − 4`,
and assume that almost surely `F̄_t` sends the restarted junction `V_last(t) − W(t)` off `ℍ`. Then almost surely `T`
is finite and every trace generating the word in `ℍ` before `T` converges at `T`, either to a point of `ℍ` or to
`F̄_q(V_last(q) − W(q))` for a positive time `q < T`. -/
theorem ae_junctionExit_of_killed {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {n j : ℕ} {ρL : Fin (j + 1) → ℝ}
    {ρR : Fin n → ℝ} (hn : 0 < n) (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR)
    (hlow : ∑ i, ρL i ≤ κ / 2 - 4)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓘 B P) (hBc : ∀ ω, Continuous (B · ω))
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ}
    (hWa : StronglyAdapted 𝓘 W) (hVLa : ∀ i, StronglyAdapted 𝓘 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓘 (VR j)) {T : Ω → ℝ≥0∞}
    (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {ω | (q : ℝ≥0∞) < T ω}) (hT0 : ∀ ω, 0 < T ω)
    (hE : ∀ᵐ ω ∂P, Sec7.Aux117.IsWordEntrance κ (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR
      (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (T ω))
    (hsepL : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ i, VL i t ω < W t ω)
    (hsepR : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ j, W t ω < VR j t ω)
    (hfl : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T ω → ∃ i, VL (Fin.last j) t ω < VL i t ω)
    (hthr : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω))
    (hgeo : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T ω →
      extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) t) ((VL (Fin.last j) t ω - W t ω : ℝ) : ℂ) ∉ H) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, (∀ s : ℝ≥0, (s : ℝ≥0∞) < T ω → Sec7.IsGeneratingTraceIcc (W · ω) s γ) →
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T ω → γ t ∈ H) →
      T ω ≠ ⊤ ∧ ∃ z : ℂ, Tendsto γ (𝓝[<] (T ω).toNNReal) (𝓝 z) ∧
        (z ∈ H ∨ ∃ q : ℝ≥0, 0 < q ∧ (q : ℝ≥0∞) < T ω ∧
          z = extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) q)
            ((VL (Fin.last j) q ω - W q ω : ℝ) : ℂ)) := by
  have hS : ∀ s : (Fin (j + 1) → ℝ) × (Fin n → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw κ ρL ρR (jexitCode κ ρL ρR)ᶜ s = 0 :=
    fun s hsep hF => codeLaw_compl_jexitCode_eq_zero hκ hκ4 hn hpre hlow s hsep hF
  have hR := ae_restart_code hκ hB hBc hWa hVLa hVRa hTq hT0 measurableSet_jexitCode hS hE hsepL hsepR hthr
  filter_upwards [hR, hE, hfl, hgeo] with ω hω hEω hflω hgeoω γ hγ hγH
  obtain ⟨q, -, hqpos, hqT⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (hT0 ω)
  have hq0 : 0 < q := by
    have h : (0 : ℝ≥0) < (q : ℝ).toNNReal := by exact_mod_cast hqpos
    exact_mod_cast Real.toNNReal_pos.1 h
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
  have hqT' : (q' : ℝ≥0∞) < T ω := hqT
  obtain ⟨x, hxC, hxS, -, hagree⟩ := hω q hq0 hqT'
  have hq'0 : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  -- the restarted state is a junction start
  have hst : JStart (stAt W VL VR q' ω) := by
    refine ⟨⟨fun i => ?_, fun j' => ?_⟩, ?_⟩
    · show VL i q' ω - W q' ω < 0
      linarith [hsepL ω q' hq'0 hqT' i]
    · show 0 < VR j' q' ω - W q' ω
      linarith [hsepR ω q' hq'0 hqT' j']
    · show VL (Fin.last j) q' ω - W q' ω < VL 0 q' ω - W q' ω
      obtain ⟨i, hi⟩ := hflω q' hq'0 hqT'
      have hmono : VL i q' ω ≤ VL 0 q' ω := hEω.antitone_vL q' hqT' (Fin.zero_le i)
      linarith
  obtain ⟨S, hend⟩ := (mem_jexitCode_iff hst hxC).1 hxS
  have hxp := hxC.1.2.2
  obtain ⟨hTne, z, hz, hzalt⟩ := junctionExit_of_restart (w := fun t => W t ω) (T := T ω)
    hEω.continuousOn_w hEω.w_zero hγ hγH hq'0 hqT' hxp.isForcePath.continuousOn_w hxp.1
    (fun t ht => (hagree t ht).1) hend (hgeoω q' hq'0 hqT')
  refine ⟨hTne, z, hz, ?_⟩
  rcases hzalt with h | h
  · exact Or.inl h
  · exact Or.inr ⟨q', hq'0, hqT', h⟩

end Killed

end InteractingSLE.Sec5.Prop51H
