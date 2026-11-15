/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessTraceLocal
import InteractingSLE.Spec.ZhanGT4.NoClusterRec

/-!
# BR3's bounded reference: code-law tools

Packet PROVE-T14-BR3. Tools for the proof of `GW0BadGroup.BR3ReferenceStatement` (supplement pp. 608–609): a local
evolution of a separated word (the retargeted process of LP9, defined only before its horizon) agrees with a maximal
solution of the word driven by the same Brownian path, and that solution can be chosen with any property that one
integrated evolution of the word has almost surely (pathwise uniqueness and uniqueness of the canonical law).

* `ae_mem_lawSetS_of_ae`: a coded state event that holds almost surely for one evolution from a separated start holds
  for the canonical solution of Wiener-almost every driving path (`measure_eventOf_eq_codeLaw_state`);
* **`ae_exists_code_of_upTo`**: a local evolution before `τ` of a separated word agrees, almost surely, before `τ`
  with a canonical solution code lying in any such event, and `τ` is at most its lifetime (the argument of
  `Sec2.IsSLEEvolutionUpTo.ae_trace_of_complete`, PROVE-SEC7-C10, with the trace event replaced by a general one);
* `GapPos`, `gapPosSet`: the gap `w − v^{L,i}` is bounded below by a positive constant at the rational times of every
  `[0, N]` before the lifetime; `GapBdd`, `gapBddSet`: the lifetime is finite and the gap is bounded above and below
  by positive constants at the rational times before it. Both are Borel code events.
* `le_of_forall_rat_le`: a rational-time bound of a function continuous on an interval extends to the interval.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace BR3Ref

open Sec2 Sec2.Assembly Sec2.Restart Sec7 Sec7.RandRestart Sec7.Band

variable {nL nR : ℕ}

/-! ### From one evolution to Wiener-almost every driving path -/

/-- **A coded state event that holds almost surely for one evolution** from a separated start holds for the canonical
solution of Wiener-almost every driving path. -/
theorem ae_mem_lawSetS_of_ae {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {S : Set (XCode nL nR)}
    {Ψ : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → ℝ≥0∞ → Prop} (hS : MeasurableSet S)
    (hSΨ : ∀ x ∈ CRelF κ ρL ρR, HasLimW x → (x ∈ S ↔ Ψ (cw x) (cvL x) (cvR x) (cζ x)))
    (hΨ : ∀ (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) →
      Ψ w vL vR τ → Ψ w' vL' vR' τ)
    (hae : ∀ᵐ ω ∂P, Ψ (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)) :
    ∀ᵐ f ∂wienerPath, ((xL, xR), enc f) ∈ lawSetS κ ρL ρR S := by
  have e := ZhanGT4.measure_eventOf_eq_codeLaw_state hκ hsep hE hS hSΨ hΨ
  have h1 : P {ω | Ψ (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)} = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := P)]
    exact measure_mono_ae (hae.mono fun ω h _ => h)
  rw [h1] at e
  have hm : MeasurableSet (Prod.mk (xL, xR) ⁻¹' restartSetS κ ρL ρR S) :=
    (measurableSet_restartSetS hS).preimage measurable_prodMk_left
  have h2 : wienerPath (Prod.mk (xL, xR) ⁻¹' restartSetS κ ρL ρR S) = 1 := e.symm
  rw [← measure_univ (μ := wienerPath)] at h2
  exact (ae_iff_measure_eq hm.nullMeasurableSet).2 h2

/-! ### A local evolution and a canonical code driven by the same path -/

/-- **A local evolution agrees with a canonical code in a given event.** Let `(W, V, B)` be a local integrated
evolution before `τ` of a separated ordered word, and `S` a set of codes containing the canonical solution of
Wiener-almost every driving path. Then almost surely there is a canonical solution code `x` of the word in `S`, driven
by the path of `B`, with `τ ≤ ζ(x)` and the same driver and force coordinates before `τ`. -/
theorem ae_exists_code_of_upTo {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓘 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {τ : Ω → ℝ≥0∞} (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR Q 𝓘 W VL VR B τ) (hsep : ∀ i j, xL i < xR j)
    {S : Set (XCode nL nR)} (hS : ∀ᵐ f ∂wienerPath, ((xL, xR), enc f) ∈ lawSetS κ ρL ρR S) :
    ∀ᵐ p ∂Q, ∃ x ∈ CRel κ xL xR ρL ρR, x ∈ S ∧ τ p ≤ cζ x ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ p → W t p = cw x t ∧ (∀ i, VL i t p = cvL x i t) ∧ ∀ j, VR j t p = cvR x j t := by
  obtain ⟨B', hm, hcB, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 hE.brownian.1
  have hpm : Measurable fun p (s : ℝ≥0) => B' s p := measurable_pi_iff.2 hm
  have hlaw : Q.map (fun p s => B' s p) = wienerPath := map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm
  rw [← hlaw] at hS
  have hgood := ae_of_ae_map hpm.aemeasurable hS
  filter_upwards [hgood, hae, hE.ae_path] with p hg hb hp
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxeq⟩ := hg
  simp only [Prod.mk.injEq] at hxeq
  have hxC : x ∈ CRel κ xL xR ρL ρR := mem_cRelF_iff.1 ⟨hxF, hxeq.1⟩
  have hxp : IsIntegratedSLEPath κ xL xR ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hcb : cb x = fun s => B' s p := by
    funext t
    show dec x.1 t = B' t p
    rw [hxeq.2]
    exact dec_enc (hcB p).continuousWithinAt
  rw [hcb] at hxp
  have hp' : IsSLEPathUpTo κ xL xR ρL ρR (fun t => W t p) (fun i t => VL i t p) (fun j t => VR j t p)
      (fun s => B' s p) (τ p) := hp.congr_b fun t _ => hb t
  obtain ⟨hle, hag⟩ := le_lifetime_of_upTo hsep hp' hxp
  exact ⟨x, hxC, hxS, hle, hag⟩

/-! ### Rational-time bounds -/

theorem cast_toNNRat' (r : ℚ) (h : 0 ≤ r) : ((r.toNNRat : ℚ≥0) : ℝ) = (r : ℝ) := by
  have e : ((r.toNNRat : ℚ) : ℝ) = (r : ℝ) := by rw [Rat.coe_toNNRat r h]
  rw [← e, Rat.cast_nnratCast]

/-- **A rational-time lower bound extends to the real times** of an interval `[0, T]` on which the function is
continuous (`T < ζ`-type intervals: the rational times are dense in `[0, T]`). -/
theorem le_of_forall_rat_le {f : ℝ≥0 → ℝ} {T : ℝ≥0} (hf : ContinuousOn f (Icc 0 T)) {c : ℝ}
    (h : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ T → c ≤ f q) {t : ℝ≥0} (ht : t ≤ T) : c ≤ f t := by
  have hcl : IsClosed (Icc (0 : ℝ≥0) T ∩ f ⁻¹' Ici c) := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsub : Icc (0 : ℝ≥0) T ⊆ closure (Icc (0 : ℝ≥0) T ∩ f ⁻¹' Ici c) := by
    intro s hs
    rw [mem_closure_iff_seq_limit]
    rcases eq_or_lt_of_le hs.2 with hsT | hsT
    · -- approach `T` from below by rationals (or take `s = T` itself when `T = 0`)
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT0 | hT0
      · refine ⟨fun _ => 0, fun _ => ⟨⟨le_rfl, zero_le⟩, ?_⟩, ?_⟩
        · have := h 0 (by simp); simpa using this
        · rw [hsT, ← hT0]; exact tendsto_const_nhds
      · have hd : ∀ n : ℕ, ∃ q : ℚ≥0, max 0 ((T : ℝ) - 1 / ((n : ℝ) + 1)) < (q : ℝ) ∧ (q : ℝ) < T := by
          intro n
          have hlt : max 0 ((T : ℝ) - 1 / ((n : ℝ) + 1)) < T := by
            refine max_lt (by exact_mod_cast hT0) ?_
            have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            linarith
          obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
          have hr0 : (0 : ℝ) ≤ r := (le_max_left _ _).trans hr1.le
          refine ⟨r.toNNRat, ?_, ?_⟩ <;> rw [cast_toNNRat' r (by exact_mod_cast hr0)] <;> assumption
        choose q hq1 hq2 using hd
        have hqT : ∀ n, (q n : ℝ≥0) ≤ T := fun n => by
          have := (hq2 n).le; exact_mod_cast this
        refine ⟨fun n => (q n : ℝ≥0), fun n => ⟨⟨zero_le, hqT n⟩, h (q n) (hqT n)⟩, ?_⟩
        rw [hsT]
        rw [← NNReal.tendsto_coe]
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => (T : ℝ) - 1 / ((n : ℝ) + 1))
          (h := fun _ => (T : ℝ)) ?_ tendsto_const_nhds (fun n => ?_) (fun n => (hq2 n).le)
        · have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
          simpa using tendsto_const_nhds.sub this
        · exact (le_max_right _ _).trans (hq1 n).le
    · -- approach `s < T` from above by rationals below `T`
      have hd : ∀ n : ℕ, ∃ q : ℚ≥0, (s : ℝ) < (q : ℝ) ∧ (q : ℝ) < min (T : ℝ) ((s : ℝ) + 1 / ((n : ℝ) + 1)) := by
        intro n
        have hlt : (s : ℝ) < min (T : ℝ) ((s : ℝ) + 1 / ((n : ℝ) + 1)) := by
          refine lt_min (by exact_mod_cast hsT) ?_
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
        have hr0 : (0 : ℝ) ≤ r := s.coe_nonneg.trans hr1.le
        refine ⟨r.toNNRat, ?_, ?_⟩ <;> rw [cast_toNNRat' r (by exact_mod_cast hr0)] <;> assumption
      choose q hq1 hq2 using hd
      have hqT : ∀ n, (q n : ℝ≥0) ≤ T := fun n => by
        have := ((hq2 n).trans_le (min_le_left _ _)).le; exact_mod_cast this
      refine ⟨fun n => (q n : ℝ≥0), fun n => ⟨⟨zero_le, hqT n⟩, h (q n) (hqT n)⟩, ?_⟩
      rw [← NNReal.tendsto_coe]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (s : ℝ))
        (h := fun n : ℕ => (s : ℝ) + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_ (fun n => (hq1 n).le)
        (fun n => (hq2 n).le.trans (min_le_right _ _))
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add this
  have := hsub ⟨zero_le, ht⟩
  rw [hcl.closure_eq] at this
  exact this.2

/-! ### The gap code events -/

/-- **The gap `w − v^{L,i}` is uniformly positive on compacts**: on every `[0, N]` before the lifetime, the gap at
rational times is at least `1/(n + 1)` for some `n`. -/
def GapPos (i : Fin nL) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) < ζ) → (q : ℝ≥0) ≤ N → 1 / ((n : ℝ) + 1) ≤ w q - vL i q

/-- **Finite lifetime, and the gap `w − v^{L,i}` bounded above and below** by positive constants at the rational
times before the lifetime. -/
def GapBdd (i : Fin nL) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ζ < ⊤ ∧ ∃ n : ℕ, ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) < ζ) →
    1 / ((n : ℝ) + 1) ≤ w q - vL i q ∧ w q - vL i q ≤ (n : ℝ) + 1

/-- The codes with `GapPos`. -/
def gapPosSet (i : Fin nL) : Set (XCode nL nR) := {x | GapPos i (cw x) (cvL x) (cζ x)}

/-- The codes with `GapBdd`. -/
def gapBddSet (i : Fin nL) : Set (XCode nL nR) := {x | GapBdd i (cw x) (cvL x) (cζ x)}

theorem measurable_gap_at (i : Fin nL) (q : ℚ≥0) :
    Measurable fun x : XCode nL nR => cw x q - cvL x i q :=
  (measurable_dec_at measurable_code_w q).sub (measurable_dec_at (measurable_code_vL i) q)

theorem measurableSet_gapPosSet (i : Fin nL) : MeasurableSet (gapPosSet (nR := nR) i) := by
  have e : gapPosSet (nR := nR) i = ⋂ N : ℕ, ⋃ n : ℕ, ⋂ q : ℚ≥0,
      ({x : XCode nL nR | ¬ (((q : ℝ≥0) : ℝ≥0∞) < cζ x)} ∪ {_x | ¬ ((q : ℝ≥0) ≤ N)} ∪
        {x | 1 / ((n : ℝ) + 1) ≤ cw x q - cvL x i q}) := by
    ext x
    simp only [gapPosSet, GapPos, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_union]
    refine forall_congr' fun N => exists_congr fun n => forall_congr' fun q => ?_
    tauto
  rw [e]
  refine MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q => ?_
  refine ((measurableSet_lt measurable_const measurable_cζ).compl.union (MeasurableSet.const _)).union ?_
  exact measurableSet_le measurable_const (measurable_gap_at i q)

theorem measurableSet_gapBddSet (i : Fin nL) : MeasurableSet (gapBddSet (nR := nR) i) := by
  have e : gapBddSet (nR := nR) i = {x : XCode nL nR | cζ x < ⊤} ∩ ⋃ n : ℕ, ⋂ q : ℚ≥0,
      ({x : XCode nL nR | ¬ (((q : ℝ≥0) : ℝ≥0∞) < cζ x)} ∪
        ({x | 1 / ((n : ℝ) + 1) ≤ cw x q - cvL x i q} ∩ {x | cw x q - cvL x i q ≤ (n : ℝ) + 1})) := by
    ext x
    simp only [gapBddSet, GapBdd, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion, mem_union]
    refine and_congr Iff.rfl (exists_congr fun n => forall_congr' fun q => ?_)
    tauto
  rw [e]
  refine (measurableSet_lt measurable_cζ measurable_const).inter
    (MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q => ?_)
  refine (measurableSet_lt measurable_const measurable_cζ).compl.union ?_
  exact (measurableSet_le measurable_const (measurable_gap_at i q)).inter
    (measurableSet_le (measurable_gap_at i q) measurable_const)

theorem gapPos_congr (i : Fin nL) (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ)
    (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hw : GapPos i w vL τ) : GapPos i w' vL' τ := by
  intro N
  obtain ⟨n, hn⟩ := hw N
  refine ⟨n, fun q hq hqN => ?_⟩
  rw [← (h q hq).1, ← (h q hq).2.1 i]
  exact hn q hq hqN

theorem gapBdd_congr (i : Fin nL) (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ)
    (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (hw : GapBdd i w vL τ) : GapBdd i w' vL' τ := by
  obtain ⟨hτ, n, hn⟩ := hw
  refine ⟨hτ, n, fun q hq => ?_⟩
  rw [← (h q hq).1, ← (h q hq).2.1 i]
  exact hn q hq

end BR3Ref

end Theorem14

end InteractingSLE
