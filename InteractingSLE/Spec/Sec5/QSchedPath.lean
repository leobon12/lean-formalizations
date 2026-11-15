/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedKernel
import InteractingSLE.Spec.Sec5.Prop513WireRegularity

/-!
# The physical prefix of a finite extreme-angle schedule, piece by piece

Packet PROVE-QSCHED. Deterministic facts about the concatenated driver of a schedule whose pieces are good
(continuous from `0`, with injective generating traces in `ℍ`). With `τ k` the schedule time before piece `k`,
`d k` its own duration and `f_j = fwdMapInv (rpath w_j) (d j)` the inverse Loewner maps of the pieces:

* `tailDrv`: the continued driver from piece `k` on; it is `catPath w_k (d k) (tailDrv (k + 1))`;
* **`pathTrace_add`**: the trace of the whole path at `τ k + s` is `C_k` of the trace of the tail at `s`, with
  `C_k = f₀ ∘ ⋯ ∘ f_{k−1}` (`chartInv`);
* **`pathTrace_notMem_image`**: the prefix `Γ((0, τ k])` lies outside `C_k(ℍ)`;
* **`isFirstHitQ_pathTrace`**: first contacts of an image counterflow with piece `k` (all rational times) give the
  physical first contact with `Γ((0, τ k + q′])` at `Γ(τ k + q′)`, for `0 < q′ ≤ d k` (`isFirstHitQ_of_chart` for
  `k > 0`, a time change for `k = 0`);
* `driverTree_eq_pathTrace`: the canonical tree coordinates are this trace on the closed horizon.

R48: deterministic; nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdMapInv fwdHull)

namespace InteractingSLE.Sec5.QSched

open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.Lemma71I (realPath)
open Sec7.StripSideHeightProb (catPath catPath_of_le catPath_zero continuous_catPath)
open Prop513TreeExtract Prop513Schedule

/-! ### First contacts: congruence and time change -/

/-- `IsFirstHitQ η β q` only reads `η` on `(0, q]`. -/
theorem isFirstHitQ_congr_left {η η' β : ℝ → ℂ} {q : ℝ} (hq : 0 < q) (h : ∀ t ∈ Ioc 0 q, η t = η' t) :
    IsFirstHitQ η β q ↔ IsFirstHitQ η' β q := by
  have hq' : η q = η' q := h q ⟨hq, le_rfl⟩
  have himg : η '' Ioc 0 q = η' '' Ioc 0 q := image_congr h
  unfold IsFirstHitQ
  rw [hq', himg]

/-- **A continuous increasing clock from `0` does not change first contacts**: if `R(β(ℓ u)) = R(β₂ u)` for `u > 0`,
the first contacts of `β₂` are first contacts of `β`. -/
theorem isFirstHitQ_of_clock {η : ℝ → ℂ} {β β₂ : ℝ≥0 → ℂ} {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ)
    (hℓm : StrictMono ℓ) (hℓ0 : ℓ 0 = 0) (hrel : ∀ u : ℝ≥0, 0 < u → negInv (β (ℓ u)) = negInv (β₂ u)) {q : ℝ}
    (h : IsFirstHitQ η (fun s : ℝ => β₂ s.toNNReal) q) : IsFirstHitQ η (fun s : ℝ => β s.toNNReal) q := by
  obtain ⟨u, hu0, hu, hbefore⟩ := h
  have hu0' : 0 < u.toNNReal := Real.toNNReal_pos.2 hu0
  have hℓpos : 0 < ℓ u.toNNReal := by rw [← hℓ0]; exact hℓm hu0'
  refine ⟨(ℓ u.toNNReal : ℝ), by exact_mod_cast hℓpos, ?_, fun v hv => ?_⟩
  · simp only [Real.toNNReal_coe]
    rw [hrel _ hu0']
    exact hu
  · have hv0 : 0 < v.toNNReal := Real.toNNReal_pos.2 hv.1
    have hvlt : v.toNNReal < ℓ u.toNNReal := (Real.toNNReal_lt_iff_lt_coe hv.1.le).2 hv.2
    obtain ⟨w, hw, hwv⟩ : v.toNNReal ∈ ℓ '' Icc 0 u.toNNReal :=
      intermediate_value_Icc zero_le hℓc.continuousOn ⟨by rw [hℓ0]; exact zero_le, hvlt.le⟩
    have hw0 : 0 < w := by
      rcases eq_or_lt_of_le hw.1 with h' | h'
      · rw [← h', hℓ0] at hwv
        exact absurd hwv.symm hv0.ne'
      · exact h'
    have hwu : w < u.toNNReal := lt_of_le_of_ne hw.2 fun h' => by
      rw [h'] at hwv
      exact absurd hwv hvlt.ne'
    have hwu' : (w : ℝ) < u := by
      have := NNReal.coe_lt_coe.2 hwu
      rwa [Real.coe_toNNReal _ hu0.le] at this
    have hb := hbefore (w : ℝ) ⟨by exact_mod_cast hw0, hwu'⟩
    simp only [Real.toNNReal_coe] at hb
    show negInv (β v.toNNReal) ∉ _
    rw [← hwv, hrel w hw0]
    exact hb

/-! ### Schedule times -/

section Times

variable (s : Schedule)

/-- The schedule time before piece `k` (`0` before the first piece). -/
def tau : ℕ → ℝ≥0
  | 0 => 0
  | k + 1 => ((scheduleList s).getD k (0, 0)).2

/-- The own duration of piece `k`. -/
def dur (k : ℕ) : ℝ≥0 := ((scheduleList s).getD k (0, 0)).2 - tau s k

variable {s}

theorem tau_succ_eq {k : ℕ} (hk : k < (scheduleList s).length) : tau s (k + 1) = ((scheduleList s)[k]).2 := by
  simp only [tau, List.getD_eq_getElem _ _ hk]

theorem dur_eq {k : ℕ} (hk : k < (scheduleList s).length) :
    dur s k = ((scheduleList s)[k]).2 - tau s k := by
  simp only [dur, List.getD_eq_getElem _ _ hk]

/-- The schedule times increase strictly. -/
theorem tau_lt_getElem {k : ℕ} (hk : k < (scheduleList s).length) : tau s k < ((scheduleList s)[k]).2 := by
  have hS := isSchedule_scheduleList s
  rcases k with _ | k
  · obtain ⟨q, hq, he⟩ := (hS.1 _ (List.getElem_mem hk)).2
    change (0 : ℝ≥0) < _
    rw [he]
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq)
  · rw [tau_succ_eq (Nat.lt_of_succ_lt hk)]
    exact List.pairwise_iff_getElem.1 hS.2 k (k + 1) (Nat.lt_of_succ_lt hk) hk (Nat.lt_succ_self k)

theorem dur_pos {k : ℕ} (hk : k < (scheduleList s).length) : 0 < dur s k := by
  rw [dur_eq hk]
  exact tsub_pos_of_lt (tau_lt_getElem hk)

theorem tau_succ {k : ℕ} (hk : k < (scheduleList s).length) : tau s (k + 1) = tau s k + dur s k := by
  rw [tau_succ_eq hk, dur_eq hk, add_tsub_cancel_of_le (tau_lt_getElem hk).le]

theorem tau_mono {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ (scheduleList s).length) : tau s j ≤ tau s k := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hjk) with h | h
    · rw [tau_succ (by omega)]
      exact (ih (by omega) (by omega)).trans le_self_add
    · rw [h]

/-- The last schedule time is the terminal time. -/
theorem tau_length : tau s (scheduleList s).length = terminal s := by
  have hl : scheduleList s ≠ [] := fun h => s.2.1 (List.map_eq_nil_iff.1 h)
  obtain ⟨n, hn⟩ : ∃ n, (scheduleList s).length = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (List.length_pos_iff.2 hl).ne'
  rw [terminal_eq_lastTime, lastTime_eq_getLast _ _ hl, hn, tau_succ_eq (by omega), List.getLast_eq_getElem]
  simp only [hn, Nat.add_sub_cancel]

/-- The instruction time of piece `k` is its duration. -/
theorem instrTime_eq_dur {k : ℕ} (hk : k < (scheduleList s).length) :
    Exist.StagedLaw.instrTime (scheduleSpec s) k = (dur s k : ℝ≥0∞) := by
  have hk' : k < (scheduleProgram 0 (scheduleList s)).length := by
    rwa [length_scheduleProgram]
  have h := Theorem14.GW2Schedule.isFlowProg_scheduleProgram 0 (scheduleList s) k hk'
  change (match (scheduleProgram 0 (scheduleList s))[k]? with
    | some (Sum.inl (_, t)) => t
    | _ => ⊤) = _
  rw [h]
  rcases k with _ | k <;> rfl

/-- The length of the program is the length of the schedule. -/
theorem length_scheduleSpec : (scheduleSpec s).2.2.length = (scheduleList s).length :=
  length_scheduleProgram 0 _

end Times

/-! ### The tail drivers and the traces -/

section Tail

variable {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : Schedule)

/-- The continued driver from piece `k` on. -/
def tailDrv (k : ℕ) (ω : Ω) : ℝ≥0 → ℝ := continuedDriver E k (tau s k) ((scheduleList s).drop k) ω

/-- The trace of the continued driver from piece `k` on. -/
def pathTrace (k : ℕ) (ω : Ω) : ℝ≥0 → ℂ := fun t => LP.traceAt t (tailDrv E s k ω)

/-- The composed inverse Loewner maps of the pieces before `k`. -/
def chartInv : ℕ → Ω → ℂ → ℂ
  | 0, _ => id
  | k + 1, ω => fun z => chartInv k ω (fwdMapInv (Ito.rpath (E k ω).1) (dur s k) z)

variable {E s}

theorem tailDrv_succ {k : ℕ} (hk : k + 1 < (scheduleList s).length) (ω : Ω) :
    tailDrv E s k ω = catPath (E k ω).1 (dur s k) (tailDrv E s (k + 1) ω) := by
  have e1 := List.drop_eq_getElem_cons (l := scheduleList s) (Nat.lt_of_succ_lt hk)
  have e2 := List.drop_eq_getElem_cons (l := scheduleList s) hk
  unfold tailDrv
  rw [e1, e2, tau_succ_eq (Nat.lt_of_succ_lt hk), dur_eq (Nat.lt_of_succ_lt hk)]
  rfl

theorem tailDrv_last {k : ℕ} (hk : k + 1 = (scheduleList s).length) (ω : Ω) :
    tailDrv E s k ω = (E k ω).1 := by
  have e1 := List.drop_eq_getElem_cons (l := scheduleList s) (show k < (scheduleList s).length by omega)
  have e2 : (scheduleList s).drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
  unfold tailDrv
  rw [e1, e2]
  rfl

theorem tailDrv_of_le {k : ℕ} (hk : k < (scheduleList s).length) (ω : Ω) {t : ℝ≥0} (ht : t ≤ dur s k) :
    tailDrv E s k ω t = (E k ω).1 t := by
  rcases Nat.lt_or_ge (k + 1) (scheduleList s).length with h | h
  · rw [tailDrv_succ h, catPath_of_le ht]
  · rw [tailDrv_last (by omega)]

theorem tailDrv_zero (ω : Ω) : tailDrv E s 0 ω = continuedDriver E 0 0 (scheduleList s) ω := rfl

/-- The good pieces of the schedule at `ω` (the hypothesis of `continuedDriver_trace`). -/
def GoodPieces (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : Schedule) (ω : Ω) : Prop :=
  ∀ j < (scheduleList s).length, Continuous (E j ω).1 ∧ (E j ω).1 0 = 0 ∧
    ∃ η, IsGeneratingTrace (E j ω).1 ⊤ η ∧ Function.Injective η ∧ ∀ t, 0 < t → η t ∈ H

variable {ω : Ω}

theorem tail_trace (hg : GoodPieces E s ω) {k : ℕ} (hk : k < (scheduleList s).length) :
    Continuous (tailDrv E s k ω) ∧ tailDrv E s k ω 0 = 0 ∧
      IsGeneratingTrace (tailDrv E s k ω) ⊤ (pathTrace E s k ω) ∧ ∀ t, 0 < t → pathTrace E s k ω t ∈ H := by
  have hne : (scheduleList s).drop k ≠ [] := by
    rw [ne_eq, List.drop_eq_nil_iff]
    omega
  obtain ⟨hc, h0, η, hη, -, hH⟩ := continuedDriver_trace E ω k (tau s k) ((scheduleList s).drop k) hne
    fun i hki hi => hg i (by rw [List.length_drop] at hi; omega)
  have he : pathTrace E s k ω = η := funext fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top
  rw [he]
  exact ⟨hc, h0, hη, hH⟩

theorem piece_trace (hg : GoodPieces E s ω) {k : ℕ} (hk : k < (scheduleList s).length) :
    IsGeneratingTrace (E k ω).1 ⊤ (fun t => LP.traceAt t (E k ω).1) ∧
      ∀ t, 0 < t → LP.traceAt t (E k ω).1 ∈ H := by
  obtain ⟨hc, h0, η, hη, -, hH⟩ := hg k hk
  have he : ∀ t, LP.traceAt t (E k ω).1 = η t := fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hη hc.continuousOn h0 ENNReal.coe_lt_top
  refine ⟨?_, fun t ht => by rw [he t]; exact hH t ht⟩
  rw [show (fun t => LP.traceAt t (E k ω).1) = η from funext he]
  exact hη

/-- The tail's trace is the piece's trace during the piece. -/
theorem pathTrace_eq_piece {k : ℕ} (hk : k < (scheduleList s).length) {t : ℝ≥0} (ht : t ≤ dur s k) :
    pathTrace E s k ω t = LP.traceAt t (E k ω).1 :=
  LP.traceAt_congr fun _ hr => tailDrv_of_le hk ω (hr.trans ht)

/-- **One piece**: the tail's trace after the piece is the inverse Loewner map of the piece applied to the next
tail's trace. -/
theorem pathTrace_succ_add (hg : GoodPieces E s ω) {k : ℕ} (hk : k + 1 < (scheduleList s).length) {u : ℝ≥0}
    (hu : 0 < u) : pathTrace E s k ω (dur s k + u) =
      fwdMapInv (Ito.rpath (E k ω).1) (dur s k) (pathTrace E s (k + 1) ω u) := by
  obtain ⟨hc₀, h00, η₀, hη₀, -, -⟩ := hg k (Nat.lt_of_succ_lt hk)
  obtain ⟨hc₁, h10, hη₁, hH₁⟩ := tail_trace hg hk
  have hW : Continuous (Ito.rpath (E k ω).1) := hc₀.comp continuous_real_toNNReal
  have hW0 : Ito.rpath (E k ω).1 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
  have hgen := LoewnerConcat.isGeneratingTrace_catPath (a := dur s k) hc₀ h00 hc₁ h10
    (hη₀.mono_horizon le_top) hη₁ hH₁
  have hcat : Continuous (catPath (E k ω).1 (dur s k) (tailDrv E s (k + 1) ω)) := continuous_catPath hc₀ hc₁ h10
  change LP.traceAt (dur s k + u) (tailDrv E s k ω) = _
  rw [tailDrv_succ hk, LP.traceAt_eq_of_isGeneratingTrace hgen hcat.continuousOn (catPath_zero h00)
    ENNReal.coe_lt_top, LoewnerConcat.joinedTrace_add hu,
    extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 (dur s k).coe_nonneg) (hH₁ u hu)]

/-- The composed inverse maps send `ℍ` into `ℍ` injectively. -/
theorem chartInv_mapsTo_injOn (hg : GoodPieces E s ω) :
    ∀ k, k ≤ (scheduleList s).length → MapsTo (chartInv E s k ω) H H ∧ InjOn (chartInv E s k ω) H
  | 0, _ => ⟨fun _ hz => hz, injOn_id _⟩
  | k + 1, hk => by
    obtain ⟨hm, hi⟩ := chartInv_mapsTo_injOn hg k (by omega)
    obtain ⟨hc, h0, -⟩ := hg k (by omega)
    have hW : Continuous (Ito.rpath (E k ω).1) := hc.comp continuous_real_toNNReal
    have hW0 : Ito.rpath (E k ω).1 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h0
    have hfm : MapsTo (fwdMapInv (Ito.rpath (E k ω).1) (dur s k)) H H := fun z hz =>
      QuantumZipper.RS.fwdMapInv_mem_H hW hW0 (dur s k).coe_nonneg hz
    have hfi := QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 (dur s k).coe_nonneg
    exact ⟨hm.comp hfm, hi.comp hfi hfm⟩

/-- **The whole path piece by piece**: at `τ k + u` the trace is `C_k` of the tail's trace at `u`. -/
theorem pathTrace_add (hg : GoodPieces E s ω) :
    ∀ k, k < (scheduleList s).length → ∀ u : ℝ≥0, 0 < u →
      pathTrace E s 0 ω (tau s k + u) = chartInv E s k ω (pathTrace E s k ω u)
  | 0, _, u, _ => by simp only [tau, zero_add, chartInv, id]
  | k + 1, hk, u, hu => by
    rw [tau_succ (by omega), add_assoc,
      pathTrace_add hg k (by omega) (dur s k + u) (add_pos_of_pos_of_nonneg (dur_pos (by omega)) hu.le),
      pathTrace_succ_add hg hk hu]
    rfl

/-- **The prefix lies outside the image of the composed inverse maps**: `Γ((0, τ k]) ∩ C_k(ℍ) = ∅`. -/
theorem pathTrace_notMem_image (hg : GoodPieces E s ω) :
    ∀ k, k < (scheduleList s).length → ∀ t : ℝ≥0, 0 < t → t ≤ tau s k →
      pathTrace E s 0 ω t ∉ chartInv E s k ω '' H
  | 0, _, t, ht, htk => absurd htk (not_le.2 ht)
  | k + 1, hk, t, ht, htk => by
    obtain ⟨hm, hi⟩ := chartInv_mapsTo_injOn hg k (by omega)
    obtain ⟨hc₀, h00, -⟩ := hg k (by omega)
    have hW : Continuous (Ito.rpath (E k ω).1) := hc₀.comp continuous_real_toNNReal
    have hW0 : Ito.rpath (E k ω).1 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using h00
    have hfm : MapsTo (fwdMapInv (Ito.rpath (E k ω).1) (dur s k)) H H := fun z hz =>
      QuantumZipper.RS.fwdMapInv_mem_H hW hW0 (dur s k).coe_nonneg hz
    rcases le_or_gt t (tau s k) with htk' | htk'
    · rintro ⟨z, hz, hze⟩
      exact pathTrace_notMem_image hg k (by omega) t ht htk' ⟨_, hfm hz, hze⟩
    · rintro ⟨z, hz, hze⟩
      set u : ℝ≥0 := t - tau s k with hudef
      have hu : 0 < u := tsub_pos_of_lt htk'
      have htu : t = tau s k + u := (add_tsub_cancel_of_le htk'.le).symm
      have hud : u ≤ dur s k := by
        rw [tau_succ (by omega)] at htk
        exact tsub_le_iff_left.2 htk
      obtain ⟨hc₁, h10, hη₁, hH₁⟩ := tail_trace hg (show k < (scheduleList s).length by omega)
      have hrw := pathTrace_add hg k (by omega) u hu
      rw [← htu] at hrw
      have hin : pathTrace E s k ω u ∈ fwdMapInv (Ito.rpath (E k ω).1) (dur s k) '' H := by
        refine ⟨z, hz, hi (hfm hz) (hH₁ u hu) ?_⟩
        rw [← hrw, ← hze]
        rfl
      obtain ⟨hc₂, h20, hη₂, -⟩ := tail_trace hg hk
      rw [tailDrv_succ hk] at hη₁
      exact RestartSw.notMem_fwdMapInv_image_of_le hc₀ h00 hc₂ h20 hη₁ hud (hH₁ u hu) hin

/-- **The physical first contact at a time of piece `k`**: from the image counterflow's first contacts with the
piece's trace at every positive rational time and its relation to the physical counterflow `γ` through the chart
`C_k` and a clock `ℓ` (with interiority of the image when `k > 0`), the counterflow `γ` first contacts
`Γ((0, τ k + q′])` at `Γ(τ k + q′)`, for `0 < q′ ≤ d k`. -/
theorem isFirstHitQ_pathTrace (hg : GoodPieces E s ω) {k : ℕ} (hk : k < (scheduleList s).length)
    {γ η₂ : ℝ≥0 → ℂ} {ℓ : ℝ≥0 → ℝ≥0} (hη₂ : Continuous η₂) (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓ0 : ℓ 0 = 0)
    (hrel : ∀ u : ℝ≥0, 0 < u → (0 < k → negInv (η₂ u) ∈ H) ∧ negInv (γ (ℓ u)) = chartInv E s k ω (negInv (η₂ u)))
    (hfirst : ∀ r : ℚ, 0 < r → IsFirstHitQ (realPath fun t => LP.traceAt t (E k ω).1) (fun s : ℝ => η₂ s.toNNReal) r)
    {q' : ℝ} (hq' : 0 < q') (hqd : q' ≤ dur s k) :
    IsFirstHitQ (realPath (pathTrace E s 0 ω)) (fun s : ℝ => γ s.toNNReal) ((tau s k : ℝ) + q') := by
  obtain ⟨hpt, hpH⟩ := piece_trace hg hk
  have hpc : Continuous fun t => LP.traceAt t (E k ω).1 :=
    continuousOn_univ.1 (hpt.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hreal : IsFirstHitQ (realPath fun t => LP.traceAt t (E k ω).1) (fun s : ℝ => η₂ s.toNNReal) q' := by
    refine RestartSw.isFirstHitQ_of_forall_rat (hpc.comp continuous_real_toNNReal).continuousOn
      (fun r hr h0 => ?_) (hη₂.comp continuous_real_toNNReal) hfirst hq'
    have := hpH r.toNNReal (Real.toNNReal_pos.2 hr)
    change LP.traceAt r.toNNReal (E k ω).1 = 0 at h0
    rw [h0] at this
    exact lt_irrefl 0 (show (0 : ℂ).im > 0 from this)
  have htail : IsFirstHitQ (realPath (pathTrace E s k ω)) (fun s : ℝ => η₂ s.toNNReal) q' := by
    refine (isFirstHitQ_congr_left hq' fun t ht => ?_).1 hreal
    change LP.traceAt t.toNNReal (E k ω).1 = pathTrace E s k ω t.toNNReal
    rw [pathTrace_eq_piece hk]
    have := Real.toNNReal_le_toNNReal (ht.2.trans hqd)
    rwa [Real.toNNReal_coe] at this
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [tau, NNReal.coe_zero, zero_add]
    have hc := isFirstHitQ_of_clock hℓc hℓm hℓ0 (β := γ) (β₂ := η₂) (fun u hu => (hrel u hu).2) htail
    refine (isFirstHitQ_congr_left hq' fun t _ => ?_).1 hc
    rfl
  · obtain ⟨hm, hi⟩ := chartInv_mapsTo_injOn hg k hk.le
    obtain ⟨-, -, -, hH⟩ := tail_trace hg hk
    exact RestartSw.isFirstHitQ_of_chart hi (fun u hu => pathTrace_add hg k hk u hu) hH
      (fun t ht htk => pathTrace_notMem_image hg k hk t ht htk) hℓc hℓm hℓ0
      (fun u hu => ⟨(hrel u hu).1 hk0, (hrel u hu).2⟩) hq' htail

end Tail

end InteractingSLE.Sec5.QSched
