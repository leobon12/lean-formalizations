/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Spec.Sec7.ContinuityProbInduction
import InteractingSLE.Spec.Supplement.LPProbInduction

/-!
# §7.3: Aux. lemma 99 — continuation of a separated one-force trace after its first swallow

Packet PROVE-SEC7-C3. Specification Aux. lemma 99 (p. 340, `source/spec/p337-384.md` L89–L140):

> Let `κ > 0` and let a chordal force-point evolution have one separated right mark at `x > 0` of weight `ρ`.
> Its trace is continuous up to and including the first swallow of that mark, or is transient if the mark is
> never swallowed. […] For `0 < κ < 4` and `ρ > −2`, the previously established admissible seed one-force
> theorem also supplies the continuation after a finite swallow; the resulting full trace is continuous and
> transient. […] Reflection gives the left-mark version.

and its last proof paragraph (p. 343–344): "restart the integrated equations at the finite swallow with the
sole admissible seed group. The seed theorem gives a continuous transient trace in the remaining half-plane
chart. A finite continuous Loewner prefix has a locally connected active boundary, so its inverse map extends
continuously to the real line; it joins this new trace to the terminal tip and fixes infinity." The same step
opens the proof of Aux. lemma 106 (p. 354), "under the present seed hypothesis", for every `κ`.

This file proves that continuation, for every `κ > 0`, from

* `Aux99StoppedStatement κ`: **named input**, the stopped assertion of Aux. lemma 99 (continuity up to and
  including the first swallow; transience if never swallowed), whose proof is the strip coordinate change
  (B2)–(B4) and Zhan's strip endpoint theorem (PROVE-ZHAN-A/B);
* the seed one-force theorem for the weight `ρ` (a hypothesis; for `0 < κ < 4` it is PROVE-SEC7-A4's
  `SeedOneForceTraceStatement`);

with the restart (`ae_restart_hasTransientTrace`, from PROVE-RESTART's `exists_restart`) at the first swallow
(`isStoppingTime_firstMeet_off`), and the join of traces (`IsGeneratingTraceIcc.join`).

* `isCompleteForceWord_oneRight_of_stopped`: one right mark `x > 0`, any weight, complete;
* `aux99Statement_of_stopped : Sec7.Aux99Statement` (the input of the κ < 4 induction);
* `oneForceStatement_of_stopped : LP.OneForceStatement κ` (the input of LP10, every `κ > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-- **Named input (§7.3): Aux. lemma 99, the stopped assertion** (Specification p. 340,
`source/spec/p337-384.md` L89: "Its trace is continuous up to and including the first swallow of that mark,
or is transient if the mark is never swallowed"; proof pp. 342–343: the strip coordinates (B2)–(B4) and
Zhan's actual-endpoint theorem for constant-drift strip SLE, PROVE-ZHAN-A/B). For `κ` and one right mark at
`x > 0` of any weight, every integrated evolution almost surely has a trace `η` which generates the chain on
`[0, τ]`, `τ` the first meeting of driver and mark before the lifetime (`firstMeet`, `= ζ` if there is none),
tends to infinity if `τ = ∞`, and, when the swallow happens before the lifetime, generates the chain on the
closed interval `[0, τ]` with its tip there ("up to and including the first swallow"). The endpoint table
(B1) of the source lemma is not needed downstream and is not included. -/
def Aux99StoppedStatement (κ : ℝ) : Prop :=
  ∀ (xL ρL : Fin 0 → ℝ) (xR ρR : Fin 1 → ℝ), 0 < xR 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (fun t => W t ω) (firstMeet W (VR 0) ζ ω) η ∧
        (firstMeet W (VR 0) ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) ∧
        ∀ σ : ℝ≥0, (σ : ℝ≥0∞) = firstMeet W (VR 0) ζ ω → (σ : ℝ≥0∞) < ζ ω →
          IsGeneratingTraceIcc (fun t => W t ω) σ η

/-- The one-mark seed word with an inadmissible weight `ρ ≤ −2` is complete (lifetime `0`). -/
theorem isCompleteForceWord_seed_of_le {κ : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ}
    (h : ρR 0 ≤ -2) : LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR := by
  apply isCompleteForceWord_of_thresholdCondition
  right
  simpa using h

/-- **Aux. lemma 99, the full one-force assertion, from the stopped assertion and the seed theorem**
(every `κ`). One right mark at `x > 0` with weight `ρ`: if the seed word with weight `ρ` is complete
whenever `ρ > −2` (the seed one-force theorem), every integrated evolution almost surely has a continuous
generating trace up to and including a finite lifetime, transient on infinite lifetime. Proof: restart at
`min(τ, n)` on `{τ < ζ, τ ≤ n}` (`τ` the first swallow; the word there is the seed word), apply the seed
theorem to the restarted evolution, and join the stopped trace with the restarted one. -/
theorem isCompleteForceWord_oneRight_of_stopped {κ : ℝ} (h99 : Aux99StoppedStatement.{u} κ)
    {xL ρL : Fin 0 → ℝ} {xR ρR : Fin 1 → ℝ} (hx : 0 < xR 0)
    (hseed : -2 < ρR 0 → LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hseed' : LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR := by
    rcases lt_or_ge (-2) (ρR 0) with h | h
    · exact hseed h
    · exact isCompleteForceWord_seed_of_le h
  have hstop := h99 xL ρL xR ρR hx P 𝓕 W VL VR B ζ hE
  set τ := firstMeet W (VR 0) ζ with hτdef
  have hE𝓖 := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hE.2.2.2.2)
  have hgood : ∀ ω ∉ N, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) := fun ω hω => by
    by_contra h
    exact hω (hNsub h)
  have hN𝓖 : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] N := fun t =>
    Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hc : ∀ ω ∉ N, ContinuousOn (fun t => VR 0 t ω - W t ω) {t | (t : ℝ≥0∞) < ζ ω} :=
    fun ω hω => ((hgood ω hω).isForcePath.continuousOn_vR 0).sub
      (hgood ω hω).isForcePath.continuousOn_w
  have hτN : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (zeroOn N τ ω : WithTop ℝ≥0) :=
    isStoppingTime_firstMeet_off hE𝓖.2.1 (hE𝓖.2.2.2.1 0) hN𝓖 hc
  have hζ𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ζ ω : WithTop ℝ≥0) :=
    Ito.isStoppingTime_lifetime hE𝓖.2.1
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- the restarts at `min τ n`, on `{τ < ζ, τ ≤ n}`
  have hrestart : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (zeroOn N τ ω < ζ ω ∧ zeroOn N τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)) →
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace
        (shiftNN (fun t => W t ω) (min (zeroOn N τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal)
        (ζ ω - (min (zeroOn N τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) η ∧
        (ζ ω - (min (zeroOn N τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal = ⊤ →
          Tendsto (fun t => ‖η t‖) atTop atTop) := by
    intro n
    set T : Ω → ℝ≥0 := fun ω => (min (zeroOn N τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal with hTdef
    have hpt : ∀ ω, ((T ω : ℝ≥0) : ℝ≥0∞) = min (zeroOn N τ ω) ((n : ℝ≥0) : ℝ≥0∞) := fun ω =>
      ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
    have hTn := IsStoppingTime.min_const hτN (n : ℝ≥0)
    have hT : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0) :=
      fun i => by
        have hs : {ω | ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
            {ω | min (zeroOn N τ ω : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0) ≤ i} := by
          ext ω
          exact iff_of_eq (congrArg (· ≤ (i : WithTop ℝ≥0)) (hpt ω))
        rw [hs]
        exact hTn i
    set A := {ω | zeroOn N τ ω < ζ ω ∧ zeroOn N τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞)} with hAdef
    have hA₁ : MeasurableSet[IsStoppingTime.measurableSpace hτN] A :=
      by
        have h1 : MeasurableSet[IsStoppingTime.measurableSpace hτN]
            {ω | (ζ ω : WithTop ℝ≥0) ≤ (zeroOn N τ ω : WithTop ℝ≥0)}ᶜ :=
          (IsStoppingTime.measurableSet_stopping_time_le hζ𝓖 hτN).compl
        have hs : {ω | (ζ ω : WithTop ℝ≥0) ≤ (zeroOn N τ ω : WithTop ℝ≥0)}ᶜ =
            {ω | zeroOn N τ ω < ζ ω} := by
          ext ω
          show ¬ (ζ ω ≤ zeroOn N τ ω) ↔ zeroOn N τ ω < ζ ω
          exact not_le
        rw [hs] at h1
        exact h1.inter (IsStoppingTime.measurableSet_le' hτN (n : ℝ≥0))
    have hA₂ : MeasurableSet[usualAugmentation 𝓕 P (n : ℝ≥0)] A := by
      have h2 : MeasurableSet[usualAugmentation 𝓕 P (n : ℝ≥0)]
          (A ∩ {ω | (zeroOn N τ ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) := hA₁.2 (n : ℝ≥0)
      have hs : A ∩ {ω | (zeroOn N τ ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} = A :=
        inter_eq_left.2 fun ω hω => hω.2
      rwa [hs] at h2
    have hAmin := (IsStoppingTime.measurableSet_min_const_iff hτN A).2 ⟨hA₁, hA₂⟩
    have hA : MeasurableSet[hT.measurableSpace] A := by
      refine ⟨hAmin.1, fun i => ?_⟩
      have hs : A ∩ {ω | ((T ω : ℝ≥0) : WithTop ℝ≥0) ≤ i} =
          A ∩ {ω | min (zeroOn N τ ω : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0) ≤ i} := by
        ext ω
        exact and_congr_right fun _ => iff_of_eq (congrArg (· ≤ (i : WithTop ℝ≥0)) (hpt ω))
      rw [hs]
      exact hAmin.2 i
    have hAζ : ∀ ω ∈ A, (T ω : ℝ≥0∞) < ζ ω := fun ω hω => by
      rw [hpt ω, min_eq_left hω.2]
      exact hω.1
    have hy : ∀ᵐ ω ∂P, ω ∈ A → (∀ i : Fin 0, VL i (T ω) ω - W (T ω) ω = xL i) ∧
        ∀ j : Fin 1, VR j (T ω) ω - W (T ω) ω = 0 := by
      filter_upwards [hNae] with ω hωN hωA
      refine ⟨fun i => i.elim0, fun j => ?_⟩
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have hτN' : zeroOn N τ ω = τ ω := zeroOn_of_notMem hωN
      obtain ⟨m, hm, hmζ, hmV⟩ := exists_eq_firstMeet (hc ω hωN) (hτN'.symm.trans_lt hωA.1)
      have hTm : T ω = m := by
        have h1 : ((T ω : ℝ≥0) : ℝ≥0∞) = m := by
          rw [hpt ω, min_eq_left hωA.2, hτN']
          exact hm
        exact_mod_cast h1
      rw [hTm]
      have := (hgood ω hωN).isForcePath.w_le_vR hmζ 0
      linarith
    exact ae_restart_hasTransientTrace hE𝓖 hT hA hAζ hy hseed'
  filter_upwards [hstop, ae_all_iff.2 hrestart, hNae] with ω hst hres hωN
  have hp := hgood ω hωN
  have hτN' : zeroOn N τ ω = τ ω := zeroOn_of_notMem hωN
  obtain ⟨η₁, hη₁, hη₁t, hη₁c⟩ := hst
  rcases (firstMeet_le_lifetime : τ ω ≤ ζ ω).lt_or_eq with hlt | heq
  · obtain ⟨m, hm, hmζ, -⟩ := exists_eq_firstMeet (hc ω hωN) hlt
    obtain ⟨n, hn⟩ := exists_nat_ge (m : ℝ)
    have hmn : (m : ℝ≥0∞) ≤ ((n : ℝ≥0) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe]; simpa using hn)
    have hm' : τ ω = m := hm
    have hTm : (min (zeroOn N τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal = m := by
      rw [hτN', hm', min_eq_left hmn, ENNReal.toNNReal_coe]
    obtain ⟨η₂, hη₂, hη₂t⟩ := hres n ⟨by rw [hτN', hm']; exact hmζ, by rw [hτN', hm']; exact hmn⟩
    rw [hTm] at hη₂ hη₂t
    have h₁ := hη₁c m hm.symm hmζ
    have hw : ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < m + (ζ ω - m)} := by
      rw [add_tsub_cancel_of_le hmζ.le]
      exact hp.isForcePath.continuousOn_w
    obtain ⟨hJ, hJt⟩ := h₁.join hw hp.isForcePath.w_zero hη₂
    rw [add_tsub_cancel_of_le hmζ.le] at hJ
    refine ⟨joinTrace (fun t => W t ω) m η₁ η₂, hJ, fun hζt => ?_⟩
    have htop : ζ ω - m = ⊤ := by rw [hζt]; exact ENNReal.top_sub_coe
    exact hJt htop (hη₂t htop)
  · exact ⟨η₁, heq ▸ hη₁, fun hζt => hη₁t (heq.trans hζt)⟩

/-- **`LP.OneForceStatement κ` from the stopped Aux. lemma 99 and the seed one-force theorem**, every `κ`
(LP10's one-group base, p. 486: "With one group use Aux. lemma 99 through its first swallow and the one-seed
theorem for every admissible continuation"). A mark at the seed is the seed theorem itself (or lifetime `0`
when inadmissible); a separated mark is `isCompleteForceWord_oneRight_of_stopped`. -/
theorem oneForceStatement_of_stopped {κ : ℝ} (h99 : Aux99StoppedStatement.{u} κ)
    (hseed : ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 →
      LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR) :
    LP.OneForceStatement.{u} κ := by
  intro xL ρL xR ρR hx
  rcases hx.lt_or_eq with hpos | hzero
  · exact isCompleteForceWord_oneRight_of_stopped h99 hpos (hseed xL ρL ρR)
  · have hxR : xR = fun _ => 0 := funext fun i => by
      rw [Subsingleton.elim i 0]
      exact hzero.symm
    subst hxR
    intro Ω mΩ
    rcases lt_or_ge (-2) (ρR 0) with h | h
    · exact hseed xL ρL ρR h
    · exact isCompleteForceWord_seed_of_le h

/-- **`Sec7.Aux99Statement`, the input of the κ < 4 induction, from the stopped Aux. lemma 99 and the seed
one-force theorem** (`SeedOneForceTraceStatement`, PROVE-SEC7-A4). The left-mark case is the reflection
(`LP.oneForce_left`). -/
theorem aux99Statement_of_stopped (h99 : ∀ κ : ℝ, 0 < κ → κ < 4 → Aux99StoppedStatement.{u} κ)
    (h1 : SeedOneForceTraceStatement.{u}) : Aux99Statement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hN hxL hxR
  have hseed : ∀ (xL' ρL' : Fin 0 → ℝ) (ρR' : Fin 1 → ℝ), -2 < ρR' 0 →
      LP.IsCompleteForceWord.{u} κ xL' (fun _ => 0) ρL' ρR' := fun xL' ρL' ρR' h =>
    h1 κ hκ hκ4 xL' (fun _ => 0) ρL' ρR' (by norm_num) (fun i => i.elim0) (fun _ => rfl)
      (fun i => i.elim0) (fun i => by rw [Subsingleton.elim i 0]; exact h)
  have hone := oneForceStatement_of_stopped (h99 κ hκ hκ4) hseed
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (nL = 0 ∧ nR = 1) ∨ (nL = 1 ∧ nR = 0) := by omega
  · intro Ω mΩ
    exact hone xL ρL xR ρR (hxR 0).le
  · intro Ω mΩ
    exact LP.oneForce_left hone xL ρL xR ρR (hxL 0).le

end Sec7

end InteractingSLE
