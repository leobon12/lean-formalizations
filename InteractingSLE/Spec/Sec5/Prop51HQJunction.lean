/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR6ProofCore
import InteractingSLE.Spec.Zhan.TransienceTrace
import InteractingSLE.Spec.Zhan.WordsEscape
import InteractingSLE.Spec.Zhan.Aux7
import InteractingSLE.Spec.Sec7.ContinuityProb3Random
import InteractingSLE.Spec.Sec5.Prop49QExitMainMerge

/-!
# Aux. lemma 22's empty-span case at a junction: an `SLE_κ(ρ)` word ends at a low-weight last left mark

Packet PROVE-PROP51H (`FwdNoContactQStatement`, the large-gap regime of Proposition 5.1's forward route in the chart
`Q`). Specification §4.1, Aux. lemma 22 and its use in the proof of Proposition 5.1 (p. 113 and (UC13), p. 115:
"In the remaining empty-span case, `a₀ ≤ −λ` and `a₁ ≥ λ`; Lemma 4.5 puts the endpoint at their common junction").
In half-plane coordinates: an integrated `SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, from a start with negative left and
positive right marks, whose left weights before the last one and whose right weights have prefix sums at least
`κ/2 − 2` and whose left total is at most `κ/2 − 4` (the junction `x_J`, the last left mark, is then a low barrier
for the span `(−∞, x_J)`), almost surely ends **at the junction**: its trace stays in `ℍ` and converges to `x_J` at
the (finite, positive) time at which the junction meets the driver.

Proof (the change of target of Lemma 4.5 and Theorem BR6's sufficiency, at `κ ≤ 4`): reflect, so that the junction
is the last right mark, and retarget at it (LP9, `Zhan.Retarget.retargetEvolutionStatement`). The transformed word has
every side prefix sum at least `κ/2 − 2` (the image of `∞` carries `κ − 6 − Σ ρ^L ≥ κ/2 − 2`), so Aux. lemma 7
(`Zhan.aux7Statement_of_separatedTransience`) and the simple-trace theorem
(`Zhan.IsIntegratedSLEEvolution.ae_simple_trace`) give a transient trace in `ℍ` of infinite lifetime; pulling it back
(`Zhan.Retarget.PullData.isGeneratingTrace_of_top`) gives a trace of the original driver that ends at the junction and
stays in `ℍ` before. This is PROVE-T14-BR3's `Theorem14.BR3Ref.visit_of_code` / `ae_visit_core` with Theorem 1.3's
trace replaced by Aux. lemma 7 (`κ ≤ 4`), and with the trace in `ℍ` recorded.

* `junction_of_code` (one path): the separation time is finite and positive, the pulled-back trace ends at the target
  and stays in `ℍ` before;
* `ImPos`, `imPosSet`: the code event "the trace is in `ℍ` with a positive margin on compact positive time ranges";
* **`ae_junction_core`**: the almost sure junction end for a distinct separated word (reflected form);
* **`ae_jEnd_of_integrated_strict`**, **`ae_jEnd_of_integrated_ord`**: the junction end of the original word in the
  countable form `JEnd` (`Prop49Exit.EndCond` with the end point the junction), strictly ordered and ordered starts.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or a `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Sec5.Prop51H

open Theorem14 Theorem14.BR3Ref Zhan Zhan.Retarget Sec7 Sec7.RandRestart

/-! ### One path -/

section OnePath

variable {κ : ℝ} {nL j m : ℕ}

/-- **The junction end along one path** (`Theorem14.BR3Ref.visit_of_code` without a given trace, with the trace in
`ℍ`). For a distinct word with target `z = x_k` (Lean index `j ≥ 1`), left partial sums `> −2` and right partial sums
before `k` `> −2`, Aux. lemma 3's threshold limit at a positive finite lifetime, and a continuous path `(w_c, v_c)`
agreeing with the transformed driver and old target before the new horizon of the separation time, with a transient
trace in `ℍ` and the gap `w_c − v_c` uniformly positive on compacts: the separation time `T′` is finite and positive,
and the driver has a generating trace on `[0, T′]` that ends at `z` and lies in `ℍ` at the times in `(0, T′)`. -/
theorem junction_of_code {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (hL : ∀ i : Fin nL, -2 < ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin (j + 1 + m), i < LP.retargetIdx j m → -2 < ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin (j + 1 + m) → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    {wc : ℝ≥0 → ℝ} {vLc : Fin (nL + (m + 1)) → ℝ≥0 → ℝ} (hwc : Continuous wc)
    (hvLc : Continuous (vLc (Fin.natAdd nL 0)))
    (htrc : ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace wc ⊤ η' ∧ Tendsto (fun t => ‖η' t‖) atTop atTop ∧
      ∀ t : ℝ≥0, 0 < t → η' t ∈ H)
    (hgap : GapPos (Fin.natAdd nL 0) wc vLc ⊤)
    (hag : ∀ t : ℝ≥0, (t : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
        (sepTime w (vR (LP.retargetIdx j m)) ζ) →
      newW xR w vR t = wc t ∧ newVL xR w vL vR (Fin.natAdd nL 0) t = vLc (Fin.natAdd nL 0) t)
 :
    ∃ T' : ℝ≥0, 0 < T' ∧ (T' : ℝ≥0∞) ≤ ζ ∧ ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace w (T' : ℝ≥0∞) γ ∧
      γ T' = (xR (LP.retargetIdx j m) : ℂ) ∧ ∀ t : ℝ≥0, 0 < t → t < T' → γ t ∈ H := by
  set xk := LP.retargetPos xR with hxk
  set vk := vR (LP.retargetIdx j m) with hvk
  set T := sepTime w vk ζ with hTdef
  have hTζ : T ≤ ζ := sepTime_le w vk ζ
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo hTζ) hD hj fun t ht => lt_of_lt_sepTime ht
  have hd : PullData w vk xk T := ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  have hxk0 := hd.pos
  have hfp := hp.isForcePath
  -- bounds of the code gap on compacts
  have hbd : ∀ N : ℕ, ∃ n : ℕ, ∀ u : ℝ≥0, u ≤ N → 1 / ((n : ℝ) + 1) ≤ wc u - vLc (Fin.natAdd nL 0) u ∧
      wc u - vLc (Fin.natAdd nL 0) u ≤ (n : ℝ) + 1 := by
    intro N
    obtain ⟨n₁, hn₁⟩ := hgap N
    have hc : ContinuousOn (fun t => wc t - vLc (Fin.natAdd nL 0) t) (Icc 0 (N : ℝ≥0)) :=
      (hwc.sub hvLc).continuousOn
    obtain ⟨t₂, -, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le⟩ hc
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge (wc t₂ - vLc (Fin.natAdd nL 0) t₂)
    refine ⟨max n₁ n₂, fun u hu => ⟨?_, ?_⟩⟩
    · exact (one_div_le_of_le (le_max_left _ _)).trans (le_of_forall_rat_le
        (f := fun t => wc t - vLc (Fin.natAdd nL 0) t) hc (fun q hq => hn₁ q ENNReal.coe_lt_top hq) hu)
    · have h1 : wc u - vLc (Fin.natAdd nL 0) u ≤ wc t₂ - vLc (Fin.natAdd nL 0) t₂ := hmax ⟨zero_le, hu⟩
      have h2 : (n₂ : ℝ) ≤ (max n₁ n₂ : ℕ) := by exact_mod_cast le_max_right _ _
      linarith
  have hceil : ∀ {Tn : ℝ≥0} {u : ℝ≥0}, u < Tn → u ≤ ((⌈(Tn : ℝ)⌉₊ : ℕ) : ℝ≥0) := by
    intro Tn u h1
    have h2 : (Tn : ℝ) ≤ ⌈(Tn : ℝ)⌉₊ := Nat.le_ceil _
    have h3 : (u : ℝ) ≤ ⌈(Tn : ℝ)⌉₊ := (le_of_lt (by exact_mod_cast h1)).trans h2
    exact_mod_cast h3
  -- Step 1: the separation time is finite
  have hTfin : T ≠ ⊤ := by
    intro hT
    have hd' : PullData w vk xk ⊤ := hT ▸ hd
    rw [hT] at hag
    by_cases hTn : newHorizon xk w vk ⊤ = ⊤
    · obtain ⟨η', hη', htr, -⟩ := htrc
      have hη'' : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk ⊤) η' := by
        rw [hTn]; exact IsGeneratingTrace.congr_lt hη' fun t ht => (hag t (by rw [hTn]; exact ht)).1
      exact PullData.false_of_newHorizon_top hd' hη'' htr hTn
    · set Tn := (newHorizon xk w vk ⊤).toNNReal with hTndef
      have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk ⊤ := ENNReal.coe_toNNReal hTn
      obtain ⟨n, hn⟩ := hbd ⌈(Tn : ℝ)⌉₊
      have hc : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      refine hTn (newHorizon_eq_top_of_gap hd'.sep hd'.pos hc fun s => ?_)
      obtain ⟨hu, he⟩ := newTime_gap (vL := vL) hd' (s := s) ENNReal.coe_lt_top
      rw [← he, (hag _ hu).1, (hag _ hu).2]
      exact (hn _ (hceil (by rw [← hTn'] at hu; exact_mod_cast hu))).1
  -- Step 2: the new horizon is infinite
  have hTn : newHorizon xk w vk T = ⊤ := by
    by_contra hTn
    set Tn := (newHorizon xk w vk T).toNNReal with hTndef
    have hTn' : ((Tn : ℝ≥0) : ℝ≥0∞) = newHorizon xk w vk T := ENNReal.coe_toNNReal hTn
    obtain ⟨n, hn⟩ := hbd ⌈(Tn : ℝ)⌉₊
    obtain ⟨δ, hδ, hgapδ⟩ := gap_pos_of_newTime_bounds (vL := vL) hd hTn (n := n) fun u hu => by
      rw [(hag u hu).1, (hag u hu).2]
      exact hn u (hceil (by rw [← hTn'] at hu; exact_mod_cast hu))
    rcases lt_or_eq_of_le hTζ with hTlt | hTeq
    · -- the driver meets the target at `T < ζ`
      have hc : ContinuousOn (fun t => vk t - w t) {t | (t : ℝ≥0∞) < ζ} :=
        (hfp.continuousOn_vR _).sub hfp.continuousOn_w
      have hTlt' := hTlt
      rw [hTdef, sepTime_eq_firstMeet] at hTlt'
      obtain ⟨t₀, ht₀, ht₀ζ, hle⟩ := exists_eq_firstMeet (W := fun t (_ : Unit) => w t)
        (V := fun t _ => vk t) (ζ := fun _ => ζ) (ω := ()) hc hTlt'
      have hTt₀ : T = (t₀ : ℝ≥0∞) := by rw [hTdef, sepTime_eq_firstMeet]; exact ht₀
      have hle' : vk t₀ ≤ w t₀ := hle
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
      · rw [← h0, hvk, hfp.vR_zero, hfp.w_zero] at hle'
        exact absurd hle' (not_le.2 hxk0)
      · have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
        have hcont := (hc.continuousAt (hopen.mem_nhds ht₀ζ)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t₀))
        have hne : (𝓝[<] t₀).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, h0⟩
        have hge : δ ≤ vk t₀ - w t₀ := ge_of_tendsto hcont (by
          filter_upwards [self_mem_nhdsWithin] with s (hs : s < t₀)
          exact hgapδ s (by rw [hTt₀]; exact_mod_cast hs))
        linarith
    · -- `T = ζ`: the threshold at `ζ` would have to sit at the target
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ ζ) with hζ0 | hζ0
      · have hth := hfp.threshold_of_eq_zero hζ0.symm
        have := vR_eq_of_thresholdCondition hD.1.1 hD.1.2.2.1 hD.1.2.1 hD.1.2.2.2 hL _ hR hth
        exact absurd this (ne_of_gt hxk0)
      · have hζfin : ζ ≠ ⊤ := by rw [← hTeq]; exact hTfin
        set T' := ζ.toNNReal with hT'def
        have hT' : (T' : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζfin
        have hT'0 : 0 < T' := by
          have : (0 : ℝ≥0∞) < (T' : ℝ≥0∞) := by rw [hT']; exact hζ0
          exact_mod_cast this
        obtain ⟨w₀, vL₀, vR₀, htend, hth⟩ := hlim T' hT'0 hT'
        have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T', (t : ℝ≥0∞) < ζ := by
          filter_upwards [self_mem_nhdsWithin] with t (ht : t < T')
          rw [← hT']; exact_mod_cast ht
        have hw := (continuous_fst.tendsto _).comp htend
        have hvL : ∀ i, Tendsto (fun t => vL i t) (𝓝[<] T') (𝓝 (vL₀ i)) := fun i =>
          ((continuous_apply i).tendsto _).comp ((continuous_fst.tendsto _).comp
            ((continuous_snd.tendsto _).comp htend))
        have hvR : ∀ i, Tendsto (fun t => vR i t) (𝓝[<] T') (𝓝 (vR₀ i)) := fun i =>
          ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp
            ((continuous_snd.tendsto _).comp htend))
        have hne : (𝓝[<] T').NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT'0⟩
        have hantiL : Antitone vL₀ := fun i i' h =>
          le_of_tendsto_of_tendsto (hvL i') (hvL i) (hev.mono fun t ht => hfp.antitone_vL ht h)
        have hmonoR : Monotone vR₀ := fun i i' h =>
          le_of_tendsto_of_tendsto (hvR i) (hvR i') (hev.mono fun t ht => hfp.monotone_vR ht h)
        have hLw : ∀ i, vL₀ i ≤ w₀ := fun i =>
          le_of_tendsto_of_tendsto (hvL i) hw (hev.mono fun t ht => hfp.vL_le_w ht i)
        have hwR : ∀ i, w₀ ≤ vR₀ i := fun i =>
          le_of_tendsto_of_tendsto hw (hvR i) (hev.mono fun t ht => hfp.w_le_vR ht i)
        have hkeq := vR_eq_of_thresholdCondition hantiL hmonoR hLw hwR hL _ hR hth
        have hge : δ ≤ vR₀ (LP.retargetIdx j m) - w₀ := ge_of_tendsto ((hvR _).sub hw) (by
          filter_upwards [self_mem_nhdsWithin] with s (hs : s < T')
          exact hgapδ s (by rw [hTeq, ← hT']; exact_mod_cast hs))
        rw [hkeq] at hge
        linarith
  -- Step 3: the pulled-back trace ends at `z` and stays in `ℍ` before
  obtain ⟨η', hη', htr, hH'⟩ := htrc
  have hη'' : IsGeneratingTrace (newDrv xk w vk) (newHorizon xk w vk T) η' := by
    rw [hTn]; exact IsGeneratingTrace.congr_lt hη' fun t ht => (hag t (by rw [hTn]; exact ht)).1
  have hpb := hd.isGeneratingTrace_of_top hη'' hTn htr
  set T' := T.toNNReal with hT'def
  have hT' : (T' : ℝ≥0∞) = T := ENNReal.coe_toNNReal hTfin
  have hT'0 : 0 < T' := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T') with h | h
    · exfalso
      have hT0 : T = 0 := by rw [← hT', ← h]; rfl
      rw [hT0, newHorizon_zero] at hTn
      exact ENNReal.zero_ne_top hTn
    · exact h
  refine ⟨T', hT'0, by rw [hT']; exact hTζ, _, by rw [hT']; exact hpb, ?_, fun t ht0 htT => ?_⟩
  · simp only [hT', lt_self_iff_false, ↓reduceIte]
    rfl
  · have htT' : (t : ℝ≥0∞) < T := by rw [← hT']; exact_mod_cast htT
    simp only [htT', ↓reduceIte, pullTrace]
    rw [targetChangeInv_mem_H_iff hxk0]
    refine hH' _ ?_
    have hc := (hd.isRate htT').clk_lt ⟨le_rfl, t.coe_nonneg⟩ ⟨t.coe_nonneg, le_rfl⟩ (by exact_mod_cast ht0)
    rw [clk_zero] at hc
    exact Real.toNNReal_pos.2 hc

end OnePath

/-! ### The code event "the trace is in `ℍ`" -/

section ImPos

open Sec2 Sec2.Assembly Sec2.Restart

variable {nL nR : ℕ}

/-- **The trace is in `ℍ`, with a margin on compact positive time ranges** (countable form, through the measurable
trace evaluation `LP.traceAt`). -/
def ImPos (w : ℝ≥0 → ℝ) : Prop :=
  ∀ n : ℕ, ∀ r : ℚ≥0, ∃ m : ℕ, ∀ p : ℚ≥0, 1 / ((n : ℝ) + 1) ≤ ((p : ℝ≥0) : ℝ) → (p : ℝ≥0) ≤ r →
    1 / ((m : ℝ) + 1) ≤ (LP.traceAt (p : ℝ≥0) w).im

/-- The codes whose driver satisfies `ImPos`. -/
def imPosSet : Set (XCode nL nR) := {x | ImPos (cw x)}

theorem measurableSet_imPosSet : MeasurableSet (imPosSet (nL := nL) (nR := nR)) := by
  have htr : ∀ s : ℝ≥0, Measurable fun x : XCode nL nR => LP.traceAt s (cw x) := fun s =>
    (LP.measurable_traceAt s).comp Exist.measurable_cw
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.forall fun r =>
    Measurable.exists fun m => Measurable.forall fun p => Measurable.imp measurable_const
      (Measurable.imp measurable_const ?_))
  exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (Complex.measurable_im.comp (htr _)))

/-- **A trace in `ℍ` at positive times gives `ImPos`** (compactness of `[1/(n+1), r]`). -/
theorem imPos_of_trace {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (hH : ∀ t : ℝ≥0, 0 < t → η t ∈ H) : ImPos w := by
  intro n r
  set K : Set ℝ≥0 := Icc (1 / ((n : ℝ) + 1)).toNNReal (r : ℝ≥0) with hK
  have hmemK : ∀ p : ℚ≥0, 1 / ((n : ℝ) + 1) ≤ ((p : ℝ≥0) : ℝ) → (p : ℝ≥0) ≤ r → (p : ℝ≥0) ∈ K :=
    fun p hp hpr => ⟨Real.toNNReal_le_iff_le_coe.2 hp, hpr⟩
  have htr : ∀ p : ℚ≥0, LP.traceAt (p : ℝ≥0) w = η p := fun p =>
    LP.traceAt_eq_of_isGeneratingTrace hη hwc.continuousOn hw0 ENNReal.coe_lt_top
  by_cases hne : K.Nonempty
  · have hc : ContinuousOn (fun t => (η t).im) K :=
      Complex.continuous_im.comp_continuousOn (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    obtain ⟨t₀, ht₀K, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
    have ht₀ : 0 < t₀ := by
      have h1 : (0 : ℝ≥0) < (1 / ((n : ℝ) + 1)).toNNReal := Real.toNNReal_pos.2 (by positivity)
      exact h1.trans_le ht₀K.1
    have hpos : 0 < (η t₀).im := hH t₀ ht₀
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    exact ⟨m, fun p hp hpr => by rw [htr]; exact hm.le.trans (hmin (hmemK p hp hpr))⟩
  · exact ⟨0, fun p hp hpr => absurd ⟨_, hmemK p hp hpr⟩ hne⟩

/-- **`ImPos` puts every generating trace in `ℍ` at positive times** (continuity, rational times). -/
theorem mem_H_of_imPos {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (hI : ImPos w) {t : ℝ≥0} (ht : 0 < t) : η t ∈ H := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t from ht)
  obtain ⟨r, hr1, -⟩ := Prop49Exit.exists_nnrat_btwn' t.coe_nonneg (lt_add_one (t : ℝ))
  obtain ⟨m, hm⟩ := hI n r
  have htr : ∀ p : ℚ≥0, LP.traceAt (p : ℝ≥0) w = η p := fun p =>
    LP.traceAt_eq_of_isGeneratingTrace hη hwc.continuousOn hw0 ENNReal.coe_lt_top
  have hc : ContinuousAt (fun s : ℝ => (η s.toNNReal).im) (t : ℝ) := by
    have h1 : ContinuousAt η t :=
      hη.2.1.continuousAt (Filter.univ_mem' fun s => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
    have h2 : ContinuousAt η (Real.toNNReal (t : ℝ)) := by rw [Real.toNNReal_coe]; exact h1
    exact Complex.continuous_im.continuousAt.comp (h2.comp continuous_real_toNNReal.continuousAt)
  have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  show 0 < (η t).im
  by_contra hle
  push Not at hle
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hc (1 / ((m : ℝ) + 1)) hm0
  obtain ⟨q, hq1, hq2⟩ := Prop49Exit.exists_nnrat_btwn' (le_max_left 0 _)
    (show max 0 (max (1 / ((n : ℝ) + 1)) ((t : ℝ) - δ)) < t from
      max_lt (by exact_mod_cast ht) (max_lt hn (by linarith)))
  have hq0 : (0 : ℝ) ≤ ((q : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hqn : 1 / ((n : ℝ) + 1) ≤ ((q : ℝ≥0) : ℝ) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hq1.le
  have hqr : (q : ℝ≥0) ≤ r := by
    have : ((q : ℝ≥0) : ℝ) ≤ ((r : ℝ≥0) : ℝ) := by linarith
    exact_mod_cast this
  have hd : dist ((q : ℝ≥0) : ℝ) (t : ℝ) < δ := by
    rw [Real.dist_eq, abs_lt]
    have h1 : (t : ℝ) - δ < ((q : ℝ≥0) : ℝ) :=
      lt_of_le_of_lt ((le_max_right (1 / ((n : ℝ) + 1)) ((t : ℝ) - δ)).trans (le_max_right 0 _)) hq1
    constructor <;> linarith
  have hbig := hm q hqn hqr
  rw [htr] at hbig
  have hclose := hδε hd
  simp only [Real.toNNReal_coe, Real.dist_eq] at hclose
  rw [abs_lt] at hclose
  linarith [hclose.2]

/-- `ImPos` sees the whole driver. -/
theorem imPos_congr {w w' : ℝ≥0 → ℝ} (h : ∀ t, w t = w' t) (hw : ImPos w) : ImPos w' := by
  have : w = w' := funext h
  rw [← this]; exact hw

end ImPos

/-! ### Admissible sums from index prefix sums -/

/-- **Admissible side partial sums from index prefix sums**, for an ordered word. -/
theorem hasAdmissible_of_prefix {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hL : ∀ i : Fin nL, k / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin nR, k / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), ρR l) :
    Sec4.HasAdmissiblePartialSums k ρL ρR xL xR := by
  have hpre : ∀ {n : ℕ} {ρ : Fin n → ℝ}, (∀ i : Fin n, k / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), ρ l) →
      ∀ j : ℕ, 1 ≤ j → j ≤ n → k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin n => i.val < j), ρ i := by
    intro n ρ h j hj1 hjn
    have h1 := h ⟨j - 1, by omega⟩
    rw [sum_filter_le_eq_pre] at h1
    have e : ((⟨j - 1, by omega⟩ : Fin n) : ℕ) + 1 = j := by simp only; omega
    rw [e] at h1
    exact h1
  refine ⟨fun x _ hne => Sec4.sum_filter_lt_xL_ge_of_cond44 hF.1 (hpre hL) hne, fun x _ ⟨i₀, hi₀⟩ => ?_⟩
  have hdown : ∀ i i' : Fin nR, i' ≤ i → xR i ≤ x → xR i' ≤ x := fun i i' hii' hi => (hF.2.2.1 hii').trans hi
  rw [Sec4.filter_eq_filter_val_lt_card hdown]
  exact hpre hR _ (card_pos.2 ⟨i₀, mem_filter.2 ⟨mem_univ _, hi₀⟩⟩) ((card_filter_le _ _).trans (by simp))

/-! ### The almost sure junction end (reflected form: the junction is a right mark) -/

section Core

open Sec2 Sec2.Assembly Sec2.Restart Sec7.Band

variable {κ : ℝ} {nL j m : ℕ}

/-- **The junction end, core** (Theorem BR6's sufficiency at `κ ≤ 4`, PROVE-T14-BR3's `ae_visit_core` with Aux.
lemma 7 in place of Theorem 1.3). For `0 < κ ≤ 4`, a distinct separated word with a left mark and target `z = x_k`
(Lean index `j ≥ 1` of a right list of length `j + 1 + m`), whose left partial sums and right partial sums before `k`
are at least `κ/2 − 2` and whose right partial sums at `k` and beyond are at most `κ/2 − 4`: almost surely the
driver has a generating trace on `[0, T′]`, `0 < T′ ≤ ζ`, that ends at `z` and lies in `ℍ` at the times in
`(0, T′)`. -/
theorem ae_junction_core (hκ : 0 < κ) (hκ4 : κ ≤ 4) {xL : Fin nL → ℝ}
    {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} (hD : LP.IsDistinctForceWord xL xR)
    (hsep : ∀ i i', xL i < xR i') (hj : 1 ≤ j) (hnL : 0 < nL)
    (hL : ∀ i : Fin nL, κ / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), ρL l)
    (hR : ∀ i : Fin (j + 1 + m), (i : ℕ) < j → κ / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), ρR l)
    (hlow : ∀ v : ℕ, j + 1 ≤ v → v ≤ j + 1 + m → pre ρR v ≤ κ / 2 - 4) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ T' : ℝ≥0, 0 < T' ∧ (T' : ℝ≥0∞) ≤ ζ ω ∧ ∃ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) (T' : ℝ≥0∞) γ ∧ γ T' = (xR (LP.retargetIdx j m) : ℂ) ∧
      ∀ t : ℝ≥0, 0 < t → t < T' → γ t ∈ H := by
  have hκ2 : -2 < κ / 2 - 2 := by linarith
  have hD' := LP.isDistinctForceWord_retarget hD hj
  have hsep' := retarget_sep hD hj hsep
  -- the transformed partial sums
  have hfar : ∀ k' : Fin (m + 1), κ / 2 - 2 ≤
      ∑ l ∈ univ.filter (· ≤ (Fin.natAdd nL k' : Fin (nL + (m + 1)))), LP.retargetρL κ ρL ρR l := by
    intro k'
    rw [retargetρL_partial_natAdd]
    have := hlow (j + 1 + m - k') (by have := k'.isLt; omega) (by omega)
    linarith
  have hL' : ∀ i : Fin (nL + (m + 1)), κ / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), LP.retargetρL κ ρL ρR l := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      rw [sum_filter_le_castAdd]
      simpa [LP.retargetρL] using hL i
    | right k' => exact hfar k'
  have hR' : ∀ i : Fin j, κ / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), LP.retargetρR ρR l := fun i => by
    rw [sum_filter_le_retargetρR]
    exact hR _ (by rw [val_castAdd_castSucc]; exact i.isLt)
  have hadm : Sec4.HasAdmissiblePartialSums κ (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR)
      (LP.retargetXL xL xR) (LP.retargetXR xR) := hasAdmissible_of_prefix hD'.1 hL' hR'
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled hκ hD'.1 (ρL := LP.retargetρL κ ρL ρR) (ρR := LP.retargetρR ρR)
  have h7 := aux7Statement_of_separatedTransience hκ hκ4 (separatedTransienceStatement hκ hκ4)
    (randomRestartTraceStatement hκ) _ _ _ _ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hD'.1 hadm hE₀
  have hsimp := IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4 hD'.1 hadm hE₀
  have hgb : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω → VL₀ (Fin.natAdd nL 0) t ω < W₀ t ω := by
    refine Supp8.GB5.gb5_left hκ hD'.1 (Fin.natAdd nL 0) (fun i _ _ => hκ2.trans_le (hL' i))
      (fun i hi _ => ?_) ?_ hE₀
    · induction i using Fin.addCases with
      | left i =>
        exfalso
        rw [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hi
        have := i.isLt; omega
      | right k' => exact hfar k'
    · obtain ⟨⟨-, hL0, -, hR0⟩, -, hmono⟩ := hD
      have hp := LP.retargetPos_pos hmono hR0 hj
      have e0 : (⟨0, Fin.pos (Fin.natAdd nL (0 : Fin (m + 1)))⟩ : Fin (nL + (m + 1))) =
          Fin.castAdd (m + 1) ⟨0, hnL⟩ := Fin.ext rfl
      rw [e0]
      simp only [LP.retargetXL, Fin.append_left, Fin.append_right, Fin.cons_zero]
      exact Sec7.neg_one_lt_targetChangeReal hp (lt_of_le_of_lt (hL0 _) hp)
  have hW := ae_mem_lawSetS_of_ae hκ hsep' hE₀
    (S := ((fullTraceSet ∩ {x : XCode (nL + (m + 1)) j | cζ x = ⊤}) ∩ gapPosSet (Fin.natAdd nL 0)) ∩ imPosSet)
    (Ψ := fun w vL _ τ => ((FullTrace w τ ∧ τ = ⊤) ∧ GapPos (Fin.natAdd nL 0) w vL τ) ∧ ImPos w)
    (((measurableSet_fullTraceSet.inter (measurableSet_eq_fun measurable_cζ measurable_const)).inter
      (measurableSet_gapPosSet _)).inter measurableSet_imPosSet)
    (fun x hx hl => by
      show ((x ∈ fullTraceSet ∧ cζ x = ⊤) ∧ GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x)) ∧ ImPos (cw x) ↔
        ((FullTrace (cw x) (cζ x) ∧ cζ x = ⊤) ∧ GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x)) ∧ ImPos (cw x)
      rw [mem_fullTraceSet_iff x hx hl])
    (fun w w' vL vL' vR vR' τ h hw => ⟨⟨⟨fullTrace_congr w w' τ (fun t ht => (h t ht).1) hw.1.1.1, hw.1.1.2⟩,
      gapPos_congr _ w w' vL vL' vR vR' τ h hw.1.2⟩,
      imPos_congr (fun t => (h t (by rw [hw.1.1.2]; exact ENNReal.coe_lt_top)).1) hw.2⟩)
    (by
      filter_upwards [h7, hsimp, hgb, hE₀.ae_isIntegratedSLEPath] with ω h7ω hsω hg hp
      obtain ⟨hl, -, h7t⟩ := h7ω
      obtain ⟨-, -, η, hη, -, hηH, -⟩ := hsω
      have hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₀ ω := fun t => by rw [hl]; exact ENNReal.coe_lt_top
      have hwc : Continuous fun t => W₀ t ω :=
        continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => hc t)
      refine ⟨⟨⟨fullTrace_of_traceEvent ⟨η, by rw [hl]; exact hη, fun _ => h7t η hη⟩, hl⟩, ?_⟩,
        imPos_of_trace hwc hp.1 hη hηH⟩
      rw [hl]
      exact gapPos_of_pos _ hwc
        (continuousOn_univ.1 ((hp.isForcePath.continuousOn_vL _).mono fun t _ => hc t)) fun t => hg t (hc t))
  obtain ⟨𝓘, β, τ, -, hτ, hloc⟩ := retargetEvolutionStatement.{u} P 𝓕 xL xR ρL ρR W VL VR B ζ hκ hD hj hE
  have hcode := ae_exists_code_of_upTo hloc hsep' hW
  have hcode' := Sec7.ae_of_ae_prod_fst (P := P) (Φ := fun ω => ∃ x ∈ CRel κ (LP.retargetXL xL xR)
      (LP.retargetXR xR) (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR),
      x ∈ ((fullTraceSet ∩ {x : XCode (nL + (m + 1)) j | cζ x = ⊤}) ∩ gapPosSet (Fin.natAdd nL 0)) ∩ imPosSet ∧
      τ ω ≤ cζ x ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → newW xR (fun t => W t ω) (fun i t => VR i t ω) t = cw x t ∧
        (∀ i, newVL xR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) i t = cvL x i t) ∧
        ∀ i, newVR xR (fun t => W t ω) (fun i t => VR i t ω) i t = cvR x i t) hcode
  filter_upwards [hcode', hτ, hE.ae_isIntegratedSLEPath, hE.ae_tendsto_threshold hκ] with ω hc hτω hp hlim
  obtain ⟨x, hxC, ⟨⟨⟨hxtr, hxζ⟩, hxgap⟩, hxI⟩, -, hag⟩ := hc
  have hxp : IsIntegratedSLEPath κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
      (LP.retargetρR ρR) (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hxζ' : cζ x = ⊤ := hxζ
  have hcx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x := fun t => by rw [hxζ']; exact ENNReal.coe_lt_top
  have hwc : Continuous (cw x) := continuousOn_univ.1 (hxp.isForcePath.continuousOn_w.mono fun t _ => hcx t)
  have hgap' : GapPos (Fin.natAdd nL 0) (cw x) (cvL x) ⊤ := by
    have h : GapPos (Fin.natAdd nL 0) (cw x) (cvL x) (cζ x) := hxgap
    rwa [hxζ'] at h
  have htrc : ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (cw x) ⊤ η' ∧ Tendsto (fun t => ‖η' t‖) atTop atTop ∧
      ∀ t : ℝ≥0, 0 < t → η' t ∈ H := by
    have hx1 : (cw x, cζ x) ∈ traceSet := hxtr.1
    have hx1' : ratVals (cw x) ∈ transientSet := by
      rcases hx1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd hxζ' h
    obtain ⟨η', hη', htr⟩ := (mem_transientSet_iff hwc hxp.1).1 hx1'
    exact ⟨η', hη', htr, fun t ht => mem_H_of_imPos hwc hxp.1 hη' hxI ht⟩
  exact junction_of_code hp hD hj (fun i => hκ2.trans_le (hL i)) (fun i hi => hκ2.trans_le (hR i (by
      rw [Fin.lt_def] at hi; simpa [LP.retargetIdx] using hi))) hlim hwc
    (continuousOn_univ.1 ((hxp.isForcePath.continuousOn_vL _).mono fun t _ => hcx t)) htrc hgap'
    (fun t ht => ⟨(hag t (by rw [hτω]; exact ht)).1, (hag t (by rw [hτω]; exact ht)).2.1 _⟩)

end Core

/-! ### The junction end of the original word -/

section Original

open Sec2 Sec2.Assembly Sec2.Restart Metric

/-- **The countable form of a strip end with the given end time and point** (`Prop49Exit.leftEnd_of_trace` with
explicit witnesses). -/
theorem endCond_of_trace {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    {S : ℝ≥0} (hS0 : 0 < S) (hSζ : (S : ℝ≥0∞) ≤ ζ) {η : ℝ≥0 → ℂ} (hgen : ∀ u : ℝ≥0, u < S → IsGeneratingTrace w u η)
    (havoid : ∀ u : ℝ≥0, u < S → ∀ z : ℝ, z ≠ 0 → η u ≠ z) {y e : ℝ} (hy0 : y < 0) (hye : y < e)
    (hconv : Tendsto η (𝓝[<] S) (𝓝 (y : ℂ))) : Prop49Exit.EndCond e w ζ S y := by
  have hlt : ∀ u : ℝ≥0, u < S → (u : ℝ≥0∞) < ζ := fun u hu => lt_of_lt_of_le (by exact_mod_cast hu) hSζ
  -- the measurable evaluation is the trace before `S`
  have htr : ∀ p : ℝ≥0, p < S → LP.traceAt p w = η p := by
    intro p hp
    obtain ⟨u, hpu, huS⟩ := exists_between hp
    exact Prop49Exit.traceAt_eq_of_trace (hgen u huS) hw hw0 (hlt u huS).le hpu
  refine ⟨hS0, hSζ, hy0, hye, fun r hr => Prop49Exit.mem_traceSet_of_trace hw hw0 (hlt _ hr) (hgen _ hr),
    fun n r hr => ?_, fun k => ?_⟩
  · -- a uniform margin on `[0, r]` by compactness
    obtain ⟨u, hru, huS⟩ := exists_between hr
    have hηc : ContinuousOn η (Icc 0 (r : ℝ≥0)) :=
      (hgen u huS).2.1.mono fun t ht => by exact_mod_cast ht.2.trans hru.le
    have hne : (GlueCond.farReal n).Nonempty := ⟨((((n : ℝ) + 1) : ℝ) : ℂ), by
      refine ⟨by simp, ?_⟩
      simp only [Complex.ofReal_re]
      rw [abs_of_pos (by positivity)]
      calc 1 / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        _ ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩
    have hpos : ∀ t ∈ Icc (0 : ℝ≥0) r, 0 < infDist (η t) (GlueCond.farReal n) := by
      intro t ht
      refine ((GlueCond.isClosed_farReal n).notMem_iff_infDist_pos hne).1 fun hmem => ?_
      have hre : η t = ((η t).re : ℂ) := Complex.ext rfl (by simp [hmem.1])
      have hne0 : (η t).re ≠ 0 := by
        intro h0
        have := hmem.2
        rw [h0, abs_zero] at this
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact havoid t (lt_of_le_of_lt (by exact_mod_cast ht.2) hr) _ hne0 hre
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (r : ℝ≥0))).exists_isMinOn
      ⟨0, le_rfl, zero_le⟩ ((continuous_infDist_pt _).comp_continuousOn hηc)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hpos t₀ ht₀)
    refine ⟨m, fun p hp => ?_⟩
    have hpI : ((p : ℝ≥0)) ∈ Icc (0 : ℝ≥0) r := ⟨zero_le, by exact_mod_cast hp⟩
    rw [htr p (lt_of_le_of_lt (by exact_mod_cast hp) hr)]
    exact hm.le.trans (hmin hpI)
  · -- the limit along rational times
    obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhdsWithin_nhds.1 hconv (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun p hp1 hp2 => ?_⟩
    rw [htr p hp2, ← dist_eq_norm]
    refine (hδε hp2 ?_).le
    rw [NNReal.dist_eq, abs_lt]
    have hp2' : ((p : ℝ≥0) : ℝ) < S := by exact_mod_cast hp2
    constructor <;> linarith

/-- `univ.filter (· ≤ i)` is `Iic i`. -/

theorem sum_filter_le_eq_Iic {N : ℕ} (f : Fin N → ℝ) (i : Fin N) :
    ∑ l ∈ univ.filter (· ≤ i), f l = ∑ l ∈ Finset.Iic i, f l := by
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext l; simp

variable {κ : ℝ}

/-- **The junction end from a strictly ordered start** (Aux. lemma 22's empty-span case, Lemma 4.5 at the junction).
For an integrated `SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, from a strictly ordered start (every left mark negative, at
least two left marks, at least one right mark, every right mark positive), whose left weights before the last one and
whose right weights have prefix sums at least `κ/2 − 2` and whose left total is at most `κ/2 − 4`: almost surely the
driver has a strip end, at a time `S`, at the last left mark itself (`Prop49Exit.EndCond` with bound the first left
mark and end point the last left mark). -/
theorem ae_jEnd_of_integrated_strict (hκ : 0 < κ) (hκ4 : κ ≤ 4) {n j : ℕ} {xL : Fin (j + 1) → ℝ}
    {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hj : 1 ≤ j) (hn : 0 < n)
    (hLa : StrictAnti xL) (hL0 : ∀ i, xL i < 0) (hRm : StrictMono xR) (hR0 : ∀ k, 0 < xR k)
    (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR) (hlow : ∑ i, ρL i ≤ κ / 2 - 4) :
    ∀ᵐ ω ∂P, ∃ S : ℝ≥0, Prop49Exit.EndCond (xL 0) (fun t => W t ω) (ζ ω) S (xL (Fin.last j)) := by
  have hR := InteractingSLE.IsIntegratedSLEEvolution.reflect hE
  have hD : LP.IsDistinctForceWord (-xR) (-xL) := LP.IsDistinctForceWord.reflect
    ⟨⟨hLa.antitone, fun i => (hL0 i).le, hRm.monotone, fun k => (hR0 k).le⟩, hLa, hRm⟩
  have hLp : ∀ i : Fin n, κ / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), ρR l := fun i => by
    rw [sum_filter_le_eq_Iic]; exact hpre.2 i
  have hRp : ∀ i : Fin (j + 1 + 0), (i : ℕ) < j → κ / 2 - 2 ≤ ∑ l ∈ univ.filter (· ≤ i), ρL l := by
    intro i hi
    have e : ∑ l ∈ univ.filter (· ≤ i), ρL l =
        ∑ l ∈ univ.filter (fun l : Fin (j + 1) => l.val ≤ (i : ℕ)), ρL l := by
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Fin.le_iff_val_le_val
    rw [e, Prop49Exit.sum_filter_le_eq_init ρL (i : ℕ) hi]
    exact hpre.1 _
  have hlow' : ∀ v : ℕ, j + 1 ≤ v → v ≤ j + 1 + 0 → pre ρL v ≤ κ / 2 - 4 := by
    intro v hv1 hv2
    have hv : v = j + 1 := by omega
    subst hv
    unfold pre
    rw [Finset.filter_true_of_mem fun l _ => l.isLt]
    exact hlow
  have hcore := ae_junction_core (m := 0) hκ hκ4 hD
    (fun i i' => by simp only [Pi.neg_apply]; linarith [hR0 i, hL0 i']) hj hn hLp hRp hlow' hR
  filter_upwards [hcore, hE.ae_isIntegratedSLEPath] with ω ⟨T', hT'0, hT'ζ, γ, hγ, hγT, hγH⟩ hp
  have hγT' : γ T' = ((-xL (Fin.last j) : ℝ) : ℂ) := hγT
  have hγr := LP.isGeneratingTrace_reflect hγ
  have e : (-fun t => (-W) t ω) = fun t => W t ω := by funext t; simp
  rw [e] at hγr
  refine ⟨T', endCond_of_trace hp.isForcePath.continuousOn_w hp.1 hT'0 hT'ζ
    (fun u hu => LP.isGeneratingTrace_mono hγr (by exact_mod_cast hu.le)) (fun u hu z hz => ?_)
    (hL0 _) (hLa (show (0 : Fin (j + 1)) < Fin.last j by
      rw [Fin.lt_def]; simp only [Fin.val_zero, Fin.val_last]; omega)) ?_⟩
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0 | h0
    · subst h0
      have h00 : LP.reflectC (γ 0) = 0 := hγr.1
      rw [h00]
      exact fun h => hz (by exact_mod_cast h.symm)
    · have hH := LP.reflectC_mem_H_iff.2 (hγH u h0 hu)
      intro h
      rw [h] at hH
      exact lt_irrefl _ (show (0 : ℝ) < ((z : ℝ) : ℂ).im from hH |>.trans_eq (by simp))
  · have hc := hγr.2.1 T' (show ((T' : ℝ≥0) : ℝ≥0∞) ≤ (T' : ℝ≥0∞) from le_rfl)
    have hval : LP.reflectC (γ T') = ((xL (Fin.last j) : ℝ) : ℂ) := by
      rw [hγT']; simp [LP.reflectC]
    rw [← hval]
    exact hc.tendsto.mono_left (nhdsWithin_mono _ fun s (hs : s < T') =>
      show ((s : ℝ≥0) : ℝ≥0∞) ≤ (T' : ℝ≥0∞) by exact_mod_cast hs.le)

/-- **The junction end from an ordered start** (coincident marks merged, as in
`Prop49Exit.ae_leftEnd_of_integrated_ord`). For an integrated `SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, from an ordered start
with negative left and positive right marks, at least one right mark, the last left mark strictly left of the first,
left weights before the last and right weights with prefix sums at least `κ/2 − 2`, and left total at most `κ/2 − 4`:
almost surely the driver has a strip end at the last left mark. -/
theorem ae_jEnd_of_integrated_ord (hκ : 0 < κ) (hκ4 : κ ≤ 4) (N : ℕ) :
    ∀ {n j : ℕ}, j + n ≤ N → ∀ {xL : Fin (j + 1) → ℝ} {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ}
      {ρR : Fin n → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
      {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ}
      {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞},
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → Antitone xL → (∀ i, xL i < 0) →
      xL (Fin.last j) < xL 0 → Monotone xR → (∀ k, 0 < xR k) → 0 < n →
      Strip.HasStripPrefixSums κ (Fin.init ρL) ρR → ∑ i, ρL i ≤ κ / 2 - 4 →
      ∀ᵐ ω ∂P, ∃ S : ℝ≥0, Prop49Exit.EndCond (xL 0) (fun t => W t ω) (ζ ω) S (xL (Fin.last j)) := by
  induction N with
  | zero =>
    intro n j hN xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hE hLa hL0 hfl hRm hR0 hn hpre hlow
    omega
  | succ N ih =>
    intro n j hN xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hE hLa hL0 hfl hRm hR0 hn hpre hlow
    have hj : 1 ≤ j := by
      by_contra hj
      obtain rfl : j = 0 := by omega
      exact lt_irrefl _ hfl
    by_cases hsL : StrictAnti xL
    · by_cases hsR : StrictMono xR
      · exact ae_jEnd_of_integrated_strict hκ hκ4 hE hj hn hsL hL0 hsR hR0 hpre hlow
      · -- merge two coincident right marks
        obtain ⟨n₁, rfl⟩ : ∃ n₁, n = n₁ + 2 := ⟨n - 2, by
          by_contra hn'
          exact hsR (Prop49Exit.strictMono_of_fin_le_one (by omega) xR)⟩
        obtain ⟨k, hk⟩ := exists_adj_eq_of_not_strictMono hRm hsR
        have hE' := Prop49Exit.mergeAdjR_evol k hk hE
        exact ih (by omega) hE' hLa hL0 hfl (hRm.comp (Fin.strictMono_succAbove _).monotone)
          (fun _ => hR0 _) (by omega) ⟨hpre.1, fun m => Prop49Exit.prefix_mergeAdj (fun m => hpre.2 m) k m⟩ hlow
    · -- merge two coincident left marks
      obtain ⟨j₁, rfl⟩ : ∃ j₁, j = j₁ + 1 := ⟨j - 1, by omega⟩
      obtain ⟨k, hk⟩ := exists_adj_eq_of_not_strictAnti hLa hsL
      have hE' := Prop49Exit.mergeAdjL_evol k hk hE
      have h0 : xL (k.succ.succAbove 0) = xL 0 := by rw [Fin.succ_succAbove_zero]
      have hlast := Prop49Exit.eq_last_of_mergeAdj hk
      have h := ih (by omega) hE' (hLa.comp_monotone (Fin.strictMono_succAbove _).monotone)
        (fun _ => hL0 _) (by rw [h0, hlast]; exact hfl) hRm hR0 hn
        ⟨fun m => Prop49Exit.prefix_init_mergeAdj (fun m => hpre.1 m) k m, hpre.2⟩
        (by rwa [sum_mergeAdj])
      simpa only [hlast, h0] using h

end Original

end InteractingSLE.Sec5.Prop51H
