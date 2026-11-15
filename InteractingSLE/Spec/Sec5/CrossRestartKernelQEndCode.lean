/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndMarks
import InteractingSLE.Spec.Sec5.Prop49QExitMainGlue
import InteractingSLE.Spec.Sec5.CfAvoidLeftQHit
import InteractingSLE.Spec.ZhanGT4.ClearanceWire

/-!
# Lemma 4.7 in the chart `Q`: the full image evolution as a Borel event of solution codes (item E, first part)

Packet PROVE-CFRESTART5, item E. To continue the counterflow's killed image word past its killing time it is
restarted at positive rational times (`Prop49Exit.ae_restart_code`). The code event used there is Lemma 4.5's
conclusion for the restarted word: infinite lifetime, a transient generating trace on `[0, ∞)`, and real values of
the trace only between the two seed marks (the images of `0⁻`, `0⁺`; beyond them the trace would leave the image
hull's base interval).

* `AvQ47 eL eR w`: the countable (margin) form of "the trace takes real values only in `[eL, eR]`";
  `avQ47_of_avoid` and `avoid_of_avQ47` (the equivalence for continuous traces);
* `AvEv47`, `avCode47 iL iR`: the event and its code set (seed indices `iL`, `iR`), **`measurableSet_avCode47`**;
* `hasAdmissiblePartialSums_of_prefix`, `prefixL_of_hasAdmissiblePartialSums`, `prefixR_of_hasAdmissiblePartialSums`,
  `prefix_snoc`: admissible partial sums from index prefix sums (marks ordered, possibly coincident) and back;
* **`codeLaw_compl_avCode47_eq_zero`**: given Zhan's Part A inputs at `16/κ` (clearance form) and prefix sums at
  least `8/κ − 2`, the event has full canonical law at every separated ordered start (Aux. lemmas 7 and 6).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

namespace Kill47

open Prop49Exit Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-! ### The countable avoidance condition -/

section Cond

/-- **The trace takes real values only in `[eL, eR]`**, countable margin form: for every `n` and rational horizon
`r`, there is a margin `1/(m+1)` such that at every rational time `p ≤ r` the trace evaluation is at height at least
the margin, or its real part is in `[eL − 1/(n+1) + margin, eR + 1/(n+1) − margin]`. -/
def AvQ47 (eL eR : ℝ) (w : ℝ≥0 → ℝ) : Prop :=
  ∀ n : ℕ, ∀ r : ℚ≥0, ∃ m : ℕ, ∀ p : ℚ≥0, p ≤ r →
    1 / ((m : ℝ) + 1) ≤ (LP.traceAt p w).im ∨
      (eL - 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ (LP.traceAt p w).re ∧
        (LP.traceAt p w).re ≤ eR + 1 / ((n : ℝ) + 1) - 1 / ((m : ℝ) + 1))

/-- **The full image evolution event**: infinite lifetime, a transient generating trace on `[0, ∞)` (through
`traceSet`), and real trace values only in `[eL, eR]`. -/
def AvEv47 (eL eR : ℝ) (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ζ = ⊤ ∧ (w, (⊤ : ℝ≥0∞)) ∈ traceSet ∧ AvQ47 eL eR w

/-- The event only sees the driver before the horizon (the horizon is `∞`). -/
theorem avEv47_congr {eL eR : ℝ} (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (hww' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (h : AvEv47 eL eR w τ) : AvEv47 eL eR w' τ := by
  obtain ⟨hτ, h2, h3⟩ := h
  have e : w = w' := funext fun t => hww' t (by rw [hτ]; exact ENNReal.coe_lt_top)
  subst e
  exact ⟨hτ, h2, h3⟩

/-- **Avoidance gives the margin condition** (a continuous trace in `ℍ̄` whose real values lie in `[eL, eR]`). -/
theorem avQ47_of_avoid {eL eR : ℝ} {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hηc : Continuous η)
    (hηH : ∀ t, 0 ≤ (η t).im) (hη : ∀ t, LP.traceAt t w = η t)
    (hav : ∀ t (x : ℝ), η t = x → eL ≤ x ∧ x ≤ eR) : AvQ47 eL eR w := by
  intro n r
  set c : ℝ := 1 / ((n : ℝ) + 1) with hc
  have hc0 : 0 < c := by positivity
  set f : ℝ≥0 → ℝ := fun t => max (η t).im (min ((η t).re - (eL - c)) (eR + c - (η t).re)) with hf
  have hfc : Continuous f :=
    (Complex.continuous_im.comp hηc).max (((Complex.continuous_re.comp hηc).sub continuous_const).min
      (continuous_const.sub (Complex.continuous_re.comp hηc)))
  have hfpos : ∀ t, 0 < f t := by
    intro t
    by_cases him : 0 < (η t).im
    · exact lt_of_lt_of_le him (le_max_left _ _)
    · have h0 : (η t).im = 0 := le_antisymm (not_lt.1 him) (hηH t)
      have hre : η t = (((η t).re : ℝ) : ℂ) := Complex.ext rfl (by simp [h0])
      obtain ⟨h1, h2⟩ := hav t _ hre
      refine lt_of_lt_of_le (lt_min (by linarith) (by linarith)) (le_max_right _ _)
  obtain ⟨t₀, -, ht₀⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (r : ℝ≥0))).exists_isMinOn
    (nonempty_Icc.2 zero_le) hfc.continuousOn
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hfpos t₀)
  refine ⟨m, fun p hp => ?_⟩
  have hfp : f t₀ ≤ f p := ht₀ ⟨zero_le, by exact_mod_cast hp⟩
  have hle : 1 / ((m : ℝ) + 1) ≤ f p := hm.le.trans hfp
  rw [hη]
  rcases le_max_iff.1 hle with h | h
  · exact Or.inl h
  · obtain ⟨h1, h2⟩ := le_min_iff.1 h
    exact Or.inr ⟨by linarith, by linarith⟩

/-- **The margin condition gives avoidance** for a continuous trace evaluation. -/
theorem avoid_of_avQ47 {eL eR : ℝ} {w : ℝ≥0 → ℝ} (hav : AvQ47 eL eR w)
    (hc : Continuous fun t => LP.traceAt t w) (t : ℝ≥0) (x : ℝ) (hx : LP.traceAt t w = x) :
    eL ≤ x ∧ x ≤ eR := by
  obtain ⟨r, hr⟩ : ∃ r : ℚ≥0, (t : ℝ≥0) + 1 ≤ (r : ℝ≥0) := by
    obtain ⟨r, hr⟩ := exists_nat_ge ((t : ℝ) + 1)
    exact ⟨r, by exact_mod_cast hr⟩
  -- a contradiction from a rational time near `t`
  have key : ∀ (n m : ℕ), (∀ p : ℚ≥0, p ≤ r →
      1 / ((m : ℝ) + 1) ≤ (LP.traceAt p w).im ∨
        (eL - 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ (LP.traceAt p w).re ∧
          (LP.traceAt p w).re ≤ eR + 1 / ((n : ℝ) + 1) - 1 / ((m : ℝ) + 1))) →
      eL - 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤ x ∧ x ≤ eR + 1 / ((n : ℝ) + 1) - 1 / ((m : ℝ) + 1) := by
    intro n m hnm
    set δm : ℝ := 1 / ((m : ℝ) + 1) with hδm
    have hδm0 : 0 < δm := by positivity
    by_contra hcon
    -- the bad closed condition is open around `t`; pick a nearby rational time
    obtain ⟨ε, hεpos, hεδ, hεcase⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ δm ∧
        (x + ε ≤ eL - 1 / ((n : ℝ) + 1) + δm ∨ eR + 1 / ((n : ℝ) + 1) - δm ≤ x - ε) := by
      rcases not_and_or.1 hcon with h | h
      · refine ⟨min δm ((eL - 1 / ((n : ℝ) + 1) + δm - x) / 2), lt_min hδm0 (by linarith [not_le.1 h]),
          min_le_left _ _, Or.inl ?_⟩
        have := min_le_right δm ((eL - 1 / ((n : ℝ) + 1) + δm - x) / 2)
        linarith [not_le.1 h]
      · refine ⟨min δm ((x - (eR + 1 / ((n : ℝ) + 1) - δm)) / 2), lt_min hδm0 (by linarith [not_le.1 h]),
          min_le_left _ _, Or.inr ?_⟩
        have := min_le_right δm ((x - (eR + 1 / ((n : ℝ) + 1) - δm)) / 2)
        linarith [not_le.1 h]
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 hc t ε hεpos
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show (t : ℝ) < (t : ℝ) + min δ 1 by
      have := lt_min hδ one_pos; linarith)
    have hp0 : (0 : ℚ) ≤ p := by
      have : (0 : ℝ) ≤ p := (NNReal.coe_nonneg t).trans hp1.le
      exact_mod_cast this
    set p' : ℚ≥0 := ⟨p, hp0⟩ with hp'
    have hp'c : ((p' : ℝ≥0) : ℝ) = p := rfl
    have hdist : dist (p' : ℝ≥0) t < δ := by
      rw [NNReal.dist_eq, hp'c, abs_lt]
      constructor <;> linarith [min_le_left δ 1]
    have hclose := hδc _ hdist
    rw [hx] at hclose
    have hpr : p' ≤ r := by
      have : ((p' : ℝ≥0) : ℝ) ≤ ((r : ℝ≥0) : ℝ) := by
        rw [hp'c]
        have := NNReal.coe_le_coe.2 hr
        push_cast at this
        linarith [min_le_right δ 1]
      exact_mod_cast this
    have him : |(LP.traceAt (p' : ℝ≥0) w).im| < ε := by
      have := (Complex.abs_im_le_norm (LP.traceAt (p' : ℝ≥0) w - (x : ℂ)))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      rw [dist_eq_norm] at hclose
      linarith
    have hre : |(LP.traceAt (p' : ℝ≥0) w).re - x| < ε := by
      have := (Complex.abs_re_le_norm (LP.traceAt (p' : ℝ≥0) w - (x : ℂ)))
      rw [Complex.sub_re, Complex.ofReal_re] at this
      rw [dist_eq_norm] at hclose
      linarith
    rcases hnm p' hpr with h | ⟨h1, h2⟩
    · have := (abs_lt.1 him).2
      linarith
    · rcases hεcase with hc1 | hc2
      · have := (abs_lt.1 hre).2
        linarith
      · have := (abs_lt.1 hre).1
        linarith
  constructor
  · by_contra h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < eL - x by linarith [not_le.1 h])
    obtain ⟨m, hm⟩ := hav n r
    have := (key n m hm).1
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  · by_contra h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < x - eR by linarith [not_le.1 h])
    obtain ⟨m, hm⟩ := hav n r
    have := (key n m hm).2
    have : 0 < 1 / ((m : ℝ) + 1) := by positivity
    linarith

end Cond

/-! ### The code set -/

section Meas

variable {nL nR : ℕ}

/-- **The codes of full image evolutions** (seed indices `iL`, `iR` of the start). -/
def avCode47 (iL : Fin nL) (iR : Fin nR) : Set (XCode nL nR) :=
  {x | AvEv47 ((startOf x).1 iL) ((startOf x).2 iR) (cw x) (cζ x)}

theorem measurableSet_avCode47 (iL : Fin nL) (iR : Fin nR) :
    MeasurableSet (avCode47 (nL := nL) (nR := nR) iL iR) := by
  have hw : Measurable fun x : XCode nL nR => cw x := Exist.measurable_cw
  have htr : ∀ s : ℝ≥0, Measurable fun x : XCode nL nR => LP.traceAt s (cw x) := fun s =>
    (LP.measurable_traceAt s).comp hw
  have hL : Measurable fun x : XCode nL nR => (startOf x).1 iL := measurable_startOf_fst iL
  have hR : Measurable fun x : XCode nL nR => (startOf x).2 iR := measurable_startOf_snd iR
  refine measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.and ?_ ?_))
  · exact measurableSet_setOfPred.1 (measurable_cζ (measurableSet_singleton ⊤))
  · exact measurableSet_setOfPred.1 ((hw.prodMk measurable_const) measurableSet_traceSet)
  · refine Measurable.forall fun n => Measurable.forall fun r => Measurable.exists fun m =>
      Measurable.forall fun p => Measurable.imp measurable_const ?_
    refine Measurable.or ?_ (Measurable.and ?_ ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (Complex.measurable_im.comp (htr _)))
    · exact measurableSet_setOfPred.1 (measurableSet_le ((hL.sub_const _).add_const _)
        (Complex.measurable_re.comp (htr _)))
    · exact measurableSet_setOfPred.1 (measurableSet_le (Complex.measurable_re.comp (htr _))
        ((hR.add_const _).sub_const _))

/-- The coding on canonical codes from a start. -/
theorem mem_avCode47_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}
    {s : (Fin nL → ℝ) × (Fin nR → ℝ)} {x : XCode nL nR} (hx : x ∈ CRel a s.1 s.2 ρL ρR) :
    x ∈ avCode47 iL iR ↔ AvEv47 (s.1 iL) (s.2 iR) (cw x) (cζ x) := by
  obtain ⟨-, hst⟩ := mem_cRelF_iff.2 hx
  show AvEv47 ((startOf x).1 iL) ((startOf x).2 iR) (cw x) (cζ x) ↔ _
  rw [hst]

end Meas

/-! ### Admissible partial sums from prefix sums -/

section Adm

open Finset in
/-- **Admissible partial sums from index prefix sums** (marks ordered, possibly coincident). -/
theorem hasAdmissiblePartialSums_of_prefix {k : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : Antitone xL) (hxR : Monotone xR)
    (hL : ∀ m : ℕ, 1 ≤ m → m ≤ nL → k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nL => i.val < m), ρL i)
    (hR : ∀ m : ℕ, 1 ≤ m → m ≤ nR → k / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i.val < m), ρR i) :
    Sec4.HasAdmissiblePartialSums k ρL ρR xL xR := by
  refine ⟨fun x _ ⟨i, hi⟩ => ?_, fun x _ ⟨i, hi⟩ => ?_⟩
  · rw [Sec4.filter_eq_filter_val_lt_card (p := fun i => x < xL i) (fun i i' hii h => lt_of_lt_of_le h (hxL hii))]
    refine hL _ (Nat.succ_le_of_lt (Finset.card_pos.2 ⟨i, by simp [hi]⟩)) ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [Sec4.filter_eq_filter_val_lt_card (p := fun i => xR i ≤ x) (fun i i' hii h => le_trans (hxR hii) h)]
    refine hR _ (Nat.succ_le_of_lt (Finset.card_pos.2 ⟨i, by simp [hi]⟩)) ?_
    exact (Finset.card_filter_le _ _).trans (by simp)

/-- Index prefix sums of the left side from admissible partial sums (strictly ordered left marks `≤ 0`). -/
theorem prefixL_of_hasAdmissiblePartialSums {k : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hadm : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR)
    (hxL : StrictAnti xL) (hxL0 : ∀ i, xL i ≤ 0) :
    ∀ m : ℕ, 1 ≤ m → m ≤ nL →
      k / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nL => i.val < m), ρL i := by
  intro m hm1 hmn
  have hjlt : m - 1 < nL := by omega
  obtain ⟨x, hx0, hxj, hfil⟩ : ∃ x : ℝ, x < 0 ∧ x < xL ⟨m - 1, hjlt⟩ ∧
      Finset.univ.filter (fun i : Fin nL => x < xL i) = Finset.univ.filter (fun i : Fin nL => i.val < m) := by
    by_cases hmn' : m = nL
    · refine ⟨xL ⟨m - 1, hjlt⟩ - 1, by linarith [hxL0 ⟨m - 1, hjlt⟩], by linarith, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _; omega
      · intro _
        have : i ≤ ⟨m - 1, hjlt⟩ := Fin.le_iff_val_le_val.2 (by simp only; omega)
        linarith [hxL.antitone this]
    · have hj'lt : m < nL := by omega
      have hjj' : (⟨m - 1, hjlt⟩ : Fin nL) < ⟨m, hj'lt⟩ := Fin.lt_def.2 (by simp only; omega)
      have hlt := hxL hjj'
      refine ⟨(xL ⟨m - 1, hjlt⟩ + xL ⟨m, hj'lt⟩) / 2, by linarith [hxL0 ⟨m - 1, hjlt⟩], by linarith, ?_⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hi
        have : (⟨m, hj'lt⟩ : Fin nL) ≤ i := Fin.le_iff_val_le_val.2 (by simp only; omega)
        linarith [hxL.antitone this]
      · intro h
        have : i ≤ ⟨m - 1, hjlt⟩ := Fin.le_iff_val_le_val.2 (by simp only; omega)
        linarith [hxL.antitone this]
  rw [← hfil]
  exact hadm.1 x hx0 ⟨⟨m - 1, hjlt⟩, hxj⟩

/-- Index prefix sums of the right side from admissible partial sums (strictly ordered right marks `≥ 0`). -/
theorem prefixR_of_hasAdmissiblePartialSums {k : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hadm : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR)
    (hxR : StrictMono xR) (hxR0 : ∀ i, 0 ≤ xR i) :
    ∀ m : ℕ, 1 ≤ m → m ≤ nR →
      k / 2 - 2 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin nR => i.val < m), ρR i := by
  intro m hm1 hmn
  have hjlt : m - 1 < nR := by omega
  have hfil : Finset.univ.filter (fun i : Fin nR => xR i ≤ xR ⟨m - 1, hjlt⟩) =
      Finset.univ.filter (fun i : Fin nR => i.val < m) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hi
      have : (⟨m - 1, hjlt⟩ : Fin nR) < i := Fin.lt_def.2 (by simp only; omega)
      linarith [hxR this]
    · intro h
      exact hxR.monotone (Fin.le_iff_val_le_val.2 (by simp only; omega))
  rw [← hfil]
  exact hadm.2 (xR ⟨m - 1, hjlt⟩) (hxR0 _) ⟨⟨m - 1, hjlt⟩, le_rfl⟩

open Finset in
/-- **Prefix sums of a word with one more (outermost) weight.** -/
theorem prefix_snoc {n : ℕ} {ρ : Fin n → ℝ} {c b : ℝ}
    (hpre : ∀ m : ℕ, 1 ≤ m → m ≤ n → b ≤ ∑ i ∈ univ.filter (fun i : Fin n => i.val < m), ρ i)
    (htot : b ≤ ∑ i, ρ i + c) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n + 1 →
      b ≤ ∑ i ∈ univ.filter (fun i : Fin (n + 1) => i.val < m), (Fin.snoc ρ c : Fin (n + 1) → ℝ) i := by
  intro m hm1 hmn
  rw [Finset.sum_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
  by_cases hm : m ≤ n
  · simp only [show ¬ (n < m) from by omega, ↓reduceIte, add_zero]
    rw [← Finset.sum_filter]
    exact hpre m hm1 hm
  · simp only [show n < m from by omega, ↓reduceIte]
    have : ∀ i : Fin n, i.val < m := fun i => by omega
    simp only [this, ↓reduceIte]
    exact htot

end Adm

/-! ### Full canonical law -/

section Law

open Finset in
/-- **The full image evolution event has full canonical law at every separated ordered start** (Aux. lemma 7 from
Zhan's Part A inputs at `16/κ`, clearance form; Aux. lemma 6's non-hitting beyond the seed marks), for weights whose
index prefix sums are at least `8/κ − 2`. -/
theorem codeLaw_compl_avCode47_eq_zero (hA : Sec5.PartAInputsSixteenDivOfClearance) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hpL : ∀ m : ℕ, 1 ≤ m → m ≤ nL → 16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nL => i.val < m), ρL i)
    (hpR : ∀ m : ℕ, 1 ≤ m → m ≤ nR → 16 / κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i.val < m), ρR i)
    (iL : Fin nL) (iR : Fin nR) (s : (Fin nL → ℝ) × (Fin nR → ℝ)) (hsep : SepStart s)
    (hF : IsOrderedForceWord s.1 s.2) :
    codeLaw (16 / κ) ρL ρR (avCode47 iL iR)ᶜ s = 0 := by
  have hk : 0 < 16 / κ := by positivity
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_assembled (a := 16 / κ) hk hF
  have hadm := hasAdmissiblePartialSums_of_prefix hF.1 hF.2.2.1 hpL hpR
  refine codeLaw_compl_eq_zero_of_ae hk hsep hE₀ (measurableSet_avCode47 iL iR)
    (fun x hx _ => mem_avCode47_iff hx) (fun w w' τ hww' h => avEv47_congr w w' τ hww' h) ?_
  have h7 := Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4 s.1 s.2 ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀
    hF hadm hE₀
  filter_upwards [h7, CfAvoidLeftQ.ae_trace_ne_pos hk hF hadm hE₀, CfAvoidLeftQ.ae_trace_ne_neg hk hF hadm hE₀,
    hE₀.2.2.2.2] with ω ⟨hζ, ⟨η, hη⟩, htr⟩ hpos hneg hp
  have hw : Continuous fun t => W₀ t ω := by
    have := hp.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  have hw0 : W₀ 0 ω = 0 := hp.1
  have heq : ∀ t, LP.traceAt t (fun t => W₀ t ω) = η t := fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨hζ, ?_, ?_⟩
  · exact (mem_traceSet_iff hw.continuousOn hw0 (fun _ h => absurd h (lt_irrefl _))).2
      ⟨η, hη, fun _ => htr η hη⟩
  · refine avQ47_of_avoid hηc (fun t => ?_) heq (fun t x hx => ⟨?_, ?_⟩)
    · exact Sec7.IsGeneratingTrace.mem_Hbar hη hw.continuousOn hw0 (le_top : ((t : ℝ≥0) : ℝ≥0∞) ≤ ⊤)
    · by_contra h
      exact hneg η hη t iL x (lt_of_lt_of_le (not_le.1 h) (hF.2.1 iL)) (not_le.1 h).le hx
    · by_contra h
      exact hpos η hη t iR x (lt_of_le_of_lt (hF.2.2.2 iR) (not_le.1 h)) (not_le.1 h).le hx

end Law

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
