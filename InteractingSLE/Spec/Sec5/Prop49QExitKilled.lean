/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitAux22

/-!
# The left exit of a killed `SLE_κ(ρ)` word

Packet PROVE-GLUECOND9 (G6 of Proposition 4.9's direction: "Aux. lemma 22, with a semi-infinite left span, gives an
actual finite first upper endpoint", specification p. 120, Remark 4.10). Let `(W, V)` be a killed word before `T`
(the integrated equations of its random initial word before `T`, a Brownian motion of a filtration, the marks strictly
separated from the driver and strictly ordered at positive times before `T`), generated before `T` by a trace `γ` in
`ℍ`, whose weights satisfy Zhan's strip hypotheses for the left span beyond the last left mark. Assume the geometric
fact that the inverse map `F̄_t` at a positive time `t < T` sends the real points left of the last left mark to
points off `ℍ`. Then almost surely `T` is finite and `γ` converges at `T`: either to a point of `ℍ`, or to
`F̄_q(y)` for a positive time `q < T` and a real `y` left of the last left mark at `q`
(**`ae_leftExit_of_killed`**).

Proof: restart at a positive rational `q < T` (`ae_restart_code` with the code event `exitCode` of
`Prop49QExitAux22`): the canonical solution from the restarted state has a left strip end at a time `S` and a point
`y`, and its trace is joined to `γ` at `q` (`Sec7.IsGeneratingTraceIcc.join`), so `γ(q + u) = F̄_q(η(u))` before
`min S (T − q)`. If `q + S < T`, then `γ(q + S) = F̄_q(y) ∉ ℍ`, impossible; so `T ≤ q + S < ∞`, and `γ` converges to
`F̄_q(y)` (when `T = q + S`) or to `F̄_q(η(T − q)) ∈ ℍ` (when `T < q + S`; the trace avoids `ℝ \ {0}` before `S`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop49Exit

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### Analytic helpers -/

section Helpers

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The limit along rational times is the limit**, for an evaluation continuous before `S`. -/
theorem tendsto_of_limQ {S : ℝ≥0} {y : ℝ} (hlim : LimQ w S y)
    (hc : ∀ u : ℝ≥0, u < S → ContinuousAt (fun t => LP.traceAt t w) u) :
    Tendsto (fun t => LP.traceAt t w) (𝓝[<] S) (𝓝 (y : ℂ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := hlim k
  refine ⟨1 / ((m : ℝ) + 1), by positivity, fun u hu hdu => ?_⟩
  have huS : u < S := hu
  rw [NNReal.dist_eq, abs_lt] at hdu
  have hlo : (S : ℝ) - 1 / ((m : ℝ) + 1) < u := by linarith [hdu.2]
  -- rational times `p_k → u` inside the window
  have hseq : ∀ k' : ℕ, ∃ p : ℚ≥0, max ((S : ℝ) - 1 / ((m : ℝ) + 1)) ((u : ℝ) - 1 / ((k' : ℝ) + 1)) <
      ((p : ℝ≥0) : ℝ) ∧ ((p : ℝ≥0) : ℝ) < u ∨
      ((p : ℝ≥0) : ℝ) = u := by
    intro k'
    by_cases hu0 : (u : ℝ) = 0
    · exact ⟨0, Or.inr (by simp [hu0])⟩
    · have hupos : 0 < (u : ℝ) := lt_of_le_of_ne u.coe_nonneg (Ne.symm hu0)
      have hmax : max 0 (max ((S : ℝ) - 1 / ((m : ℝ) + 1)) ((u : ℝ) - 1 / ((k' : ℝ) + 1))) < u := by
        have : (0 : ℝ) < 1 / ((k' : ℝ) + 1) := by positivity
        exact max_lt hupos (max_lt hlo (by linarith))
      obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn' (le_max_left _ _) hmax
      exact ⟨p, Or.inl ⟨lt_of_le_of_lt (le_max_right _ _) hp1, hp2⟩⟩
  choose p hp using hseq
  have hpu : Tendsto (fun k' => ((p k' : ℚ≥0) : ℝ≥0)) atTop (𝓝 u) := by
    rw [← NNReal.tendsto_coe]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun k' : ℕ => (u : ℝ) - 1 / ((k' : ℝ) + 1))
      (h := fun _ => (u : ℝ)) ?_ tendsto_const_nhds (fun k' => ?_) (fun k' => ?_)
    · simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · rcases hp k' with ⟨h1, -⟩ | h
      · exact (le_max_right _ _).trans h1.le
      · rw [h]; have : (0 : ℝ) < 1 / ((k' : ℝ) + 1) := by positivity
        linarith
    · rcases hp k' with ⟨-, h2⟩ | h
      · exact h2.le
      · exact h.le
  have hbound : ∀ k', ‖LP.traceAt ((p k' : ℚ≥0) : ℝ≥0) w - (y : ℂ)‖ ≤ 1 / ((k : ℝ) + 1) := by
    intro k'
    rcases hp k' with ⟨h1, h2⟩ | h
    · exact hm _ (lt_of_le_of_lt (le_max_left _ _) h1) (by exact_mod_cast h2.trans huS)
    · have hpu' : ((p k' : ℚ≥0) : ℝ≥0) = u := NNReal.coe_injective h
      have : (S : ℝ) - 1 / ((m : ℝ) + 1) < ((p k' : ℚ≥0) : ℝ≥0) := by rw [hpu']; exact hlo
      exact hm _ this (by rw [hpu']; exact huS)
  have hc' : Tendsto (fun k' => LP.traceAt ((p k' : ℚ≥0) : ℝ≥0) w) atTop (𝓝 (LP.traceAt u w)) :=
    (hc u huS).tendsto.comp hpu
  have hle : ‖LP.traceAt u w - (y : ℂ)‖ ≤ 1 / ((k : ℝ) + 1) :=
    le_of_tendsto ((continuous_norm.tendsto _).comp (hc'.sub tendsto_const_nhds))
      (Eventually.of_forall hbound)
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hle hk

/-- **Shifting a left limit**: `f(· − q)` converges at `q + S` from the left when `f` converges at `S`. -/
theorem tendsto_comp_tsub {q S : ℝ≥0} (hS : 0 < S) {f : ℝ≥0 → ℂ} {z : ℂ} (h : Tendsto f (𝓝[<] S) (𝓝 z)) :
    Tendsto (fun t => f (t - q)) (𝓝[<] (q + S)) (𝓝 z) := by
  refine h.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have hc : Continuous fun t : ℝ≥0 => t - q := continuous_id.sub continuous_const
    have := (hc.tendsto (q + S)).mono_left (nhdsWithin_le_nhds (s := Iio (q + S)))
    rwa [add_tsub_cancel_left] at this
  · have hq : ∀ᶠ t in 𝓝[<] (q + S), q < t :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (lt_add_of_pos_right q hS))
    filter_upwards [hq, self_mem_nhdsWithin] with t hqt ht
    show t - q < S
    rw [tsub_lt_iff_left hqt.le]
    exact ht

end Helpers

/-! ### The pathwise exit after a restart -/

section Pathwise

/-- **The pathwise left exit.** Let `γ` generate the chain of `w` (continuous before `T`, from `0`) before `T`, in
`ℍ` at positive times; let `c` (continuous before `ζ_c`, from `0`) agree with the restarted driver
`w(q + ·) − w(q)` before `T − q` (`0 < q < T`), and have a left strip end `(S, y)` with bound `e`; let `F̄_q`
send the real points left of `e` off `ℍ`. Then `T` is finite and `γ` converges at `T`, to a point of `ℍ` or to
`F̄_q(y′)` for a real `y′ < e`. -/
theorem leftExit_of_restart {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T → Sec7.IsGeneratingTraceIcc w s γ)
    (hγH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T → γ t ∈ H) {q : ℝ≥0} (hq0 : 0 < q) (hqT : (q : ℝ≥0∞) < T)
    {c : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} (hcc : ContinuousOn c {t | (t : ℝ≥0∞) < ζc}) (hc0 : c 0 = 0)
    (hagree : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T - q → c t = w (q + t) - w q)
    {e : ℝ} {S : ℝ≥0} {y : ℝ} (hend : EndCond e c ζc S y)
    (hgeo : ∀ y' : ℝ, y' < e → extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) y' ∉ H) :
    T ≠ ⊤ ∧ ∃ z : ℂ, Tendsto γ (𝓝[<] T.toNNReal) (𝓝 z) ∧
      (z ∈ H ∨ ∃ y' : ℝ, y' < e ∧ z = extendFrom H (fwdMapInv (fun s : ℝ => w s.toNNReal) q) y') := by
  obtain ⟨hS0, hSζ, hy0, hye, htr, hav, hlim⟩ := hend
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
    exact hgeo y hye hmem
  · -- `T = q + S`: convergence to `F̄_q(y)`
    have hT : T.toNNReal = q + S := by rw [← heq, ENNReal.toNNReal_coe]
    refine ⟨heq ▸ ENNReal.coe_ne_top, F y, ?_, Or.inr ⟨y, hye, rfl⟩⟩
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

/-! ### The killed word -/

section Killed

/-- **The left exit of a killed `SLE_κ(ρ)` word** (`0 < κ ≤ 4`; Aux. lemma 22 for the left span beyond the last left
mark, through the restart). Let the driver and the marks be adapted to `𝓘`, satisfy the integrated equations of
their random initial word before `T` driven by a Brownian motion `B` of `𝓘` with continuous paths (`T > 0`,
`{q < T} ∈ 𝓘_q`), be strictly separated from the driver and strictly ordered at positive times before `T`, start
below the continuation threshold, and let the weights satisfy Zhan's hypotheses for the reflected strip word. Assume
that at positive times `t < T` the inverse map `F̄_t` sends the real points left of the last left mark off `ℍ`. Then
almost surely every trace `γ` generating the chain in `ℍ` before `T` converges at `T < ∞`, to a point of `ℍ` or to
`F̄_q(y)` for some `0 < q < T` and a real `y` left of the last left mark at `q`. -/
theorem ae_leftExit_of_killed {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {n j : ℕ} {ρL : Fin (j + 1) → ℝ}
    {ρR : Fin n → ℝ} (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓘 : Filtration ℝ≥0 mΩ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓘 B P) (hBc : ∀ ω, Continuous (B · ω))
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ}
    (hWa : StronglyAdapted 𝓘 W) (hVLa : ∀ i, StronglyAdapted 𝓘 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓘 (VR j)) {T : Ω → ℝ≥0∞}
    (hTq : ∀ q : ℝ≥0, MeasurableSet[𝓘 q] {ω | (q : ℝ≥0∞) < T ω}) (hT0 : ∀ ω, 0 < T ω)
    (hE : ∀ᵐ ω ∂P, Sec7.Aux117.IsWordEntrance κ (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR
      (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (T ω))
    (hsepL : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ i, VL i t ω < W t ω)
    (hsepR : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ j, W t ω < VR j t ω)
    (hthr : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω))
    (hstrict : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω →
      StrictAnti (fun i => VL i t ω) ∧ StrictMono (fun j => VR j t ω))
    (hgeo : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → ∀ y : ℝ, y < VL (Fin.last j) t ω - W t ω →
      extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) t) y ∉ H) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, (∀ s : ℝ≥0, (s : ℝ≥0∞) < T ω → Sec7.IsGeneratingTraceIcc (W · ω) s γ) →
      (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < T ω → γ t ∈ H) →
      T ω ≠ ⊤ ∧ ∃ z : ℂ, Tendsto γ (𝓝[<] (T ω).toNNReal) (𝓝 z) ∧
        (z ∈ H ∨ ∃ (q : ℝ≥0) (y : ℝ), 0 < q ∧ (q : ℝ≥0∞) < T ω ∧ y < VL (Fin.last j) q ω - W q ω ∧
          z = extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal ω) q) y) := by
  have hS : ∀ s : (Fin (j + 1) → ℝ) × (Fin n → ℝ), SepStart s → IsOrderedForceWord s.1 s.2 →
      codeLaw κ ρL ρR (exitCode κ ρL ρR fun s => s.1 (Fin.last j))ᶜ s = 0 :=
    fun s hsep hF => codeLaw_compl_exitCode_eq_zero hκ hκ4 hpre hq s hsep hF
  have hR := ae_restart_code hκ hB hBc hWa hVLa hVRa hTq hT0
    (measurableSet_exitCode ((measurable_pi_apply (Fin.last j)).comp measurable_fst)) hS hE hsepL hsepR hthr
  filter_upwards [hR, hE] with ω hω hEω γ hγ hγH
  obtain ⟨q, -, hqpos, hqT⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (hT0 ω)
  have hq0 : 0 < q := by
    have h : (0 : ℝ≥0) < (q : ℝ).toNNReal := by exact_mod_cast hqpos
    exact_mod_cast Real.toNNReal_pos.1 h
  set q' : ℝ≥0 := (q : ℝ).toNNReal with hq'def
  have hqT' : (q' : ℝ≥0∞) < T ω := hqT
  obtain ⟨x, hxC, hxS, -, hagree⟩ := hω q hq0 hqT'
  have hq'0 : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  -- the restarted state is strictly ordered
  have hst : StrictStart (stAt W VL VR q' ω) := by
    obtain ⟨ha, hm⟩ := hstrict ω q' hq'0 hqT'
    refine ⟨fun i i' hii => ?_, fun i => ?_, fun j' j'' hjj => ?_, fun j' => ?_⟩
    · show VL i' q' ω - W q' ω < VL i q' ω - W q' ω
      linarith [ha hii]
    · show VL i q' ω - W q' ω < 0
      linarith [hsepL ω q' hq'0 hqT' i]
    · show VR j' q' ω - W q' ω < VR j'' q' ω - W q' ω
      linarith [hm hjj]
    · show 0 < VR j' q' ω - W q' ω
      linarith [hsepR ω q' hq'0 hqT' j']
  obtain ⟨S, y, hend⟩ := (mem_exitCode_iff hst hxC).1 hxS
  have hxp := hxC.1.2.2
  obtain ⟨hTne, z, hz, hzalt⟩ := leftExit_of_restart (w := fun t => W t ω) (T := T ω)
    hEω.continuousOn_w hEω.w_zero hγ hγH hq'0 hqT' hxp.isForcePath.continuousOn_w hxp.1
    (fun t ht => (hagree t ht).1) hend (fun y' hy' => hgeo ω q' hq'0 hqT' y' hy')
  refine ⟨hTne, z, hz, ?_⟩
  rcases hzalt with h | ⟨y', hy', rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨q', y', hq'0, hqT', hy', rfl⟩

end Killed

end InteractingSLE.Sec5.Prop49Exit
