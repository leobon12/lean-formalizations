/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418DetGlue
import InteractingSLE.WangWu.Prop418Range
import InteractingSLE.WangWu.MeanIdentArc
import InteractingSLE.Spec.Exist.DetField

/-!
# Wang–Wu Proposition 4.18: the range of the seed line determines its history, measurably

Packet PROVE-WW-B10. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), last paragraph of the
proof of Proposition 4.18 (text dump L1649–1653): "Lemma 4.1 makes the oriented forward range a function of `h`.
Half-plane capacity determines the parameter of a simple Loewner trace, so the complete hull history is determined."

PROVE-WW-B6 proved the deterministic core (`eqOn_of_arcRange_eq`: two simple proper Loewner traces with the same range
are equal, and so are their drivers). PROVE-WW-B9 reduced the determination to a glued identity in *history* form and
recorded that the *range* form (a hitting code of the range, `hitCode`) needs a Borel set of good histories on which the
range is injective, followed by Lusin–Souslin. This file supplies that step.

* `ImPosCond`, `SepCond`: countably many conditions on the values of a curve at rational times (imaginary part bounded
  below on rational windows `[a, b] ⊂ (0, ∞)`, positive distance between disjoint rational windows). For a curve
  continuous on `[0, ∞)` they give injectivity and `γ (0, ∞) ⊆ ℍ` (`injOn_of_sepCond`, `mem_H_of_imPosCond`); a simple
  proper arc satisfies them (`IsProperArc.sepCond`, `IsProperArc.imPosCond`).
* `arcRange_eq_of_hitCode_eq`: two proper arcs with the same hitting code have the same range.
* `RangeSet`: the Borel set of Theorem 2.2 history codes in `Exist.DetSet` with infinite lifetime, a transient
  generating trace on `[0, ∞)` (`Sec7.RandRestart.traceSet`) and the two window conditions on the trace.
  **`injOn_hitCode_codeLine`**: on `RangeSet`, the hitting code of the range of the trace determines the code
  (`eqOn_of_arcRange_eq`, then `Exist.injOn_traceOfCode`).
* **`isFieldDeterminedHistory_of_aeDeterminedBy_hitCode`**: for an integrated evolution whose seed line is almost surely
  a simple proper arc on an infinite lifetime, if the hitting code of the range of the seed line is almost surely a
  Borel function of the field, then the killed driving history is (Lusin–Souslin,
  `Exist.exists_measurable_leftInverse_of_injOn`). **`IsMarkedChain.isFieldDeterminedHistory_of_aeDeterminedBy_hitCode`**
  is the case of the nonnegative words at `κ = 4` (Proposition 4.18's words), where the trace hypotheses hold by
  `IsMarkedChain.ae_seedLine`.
* **`IsMarkedChain.isFieldDeterminedHistory_of_glue_hitCode`**: the range form of B9's glued identity suffices — if the
  hitting code of the forward range is almost surely a measurable function of a glued sample of `κ(h)`, the killed
  history is field-determined.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open QuantumZipper (H)

/-! ### Rational windows -/

section Windows

/-- The rational times of the window `[a, b]`, as a set of reals. -/
def ratWindow (a b : ℚ) : Set ℝ := {u | ∃ p : ℚ, (p : ℝ) = u ∧ a ≤ p ∧ p ≤ b}

/-- A point of `[a, b)` is a limit of rational times of the window `[a, b]`. -/
theorem mem_closure_ratWindow {a b : ℚ} {s : ℝ} (has : (a : ℝ) ≤ s) (hsb : s < b) :
    s ∈ closure (ratWindow a b) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_rat_btwn (show s < min (s + ε) b from lt_min (by linarith) hsb)
  refine ⟨p, ⟨p, rfl, ?_, ?_⟩, ?_⟩
  · exact_mod_cast has.trans hp.1.le
  · exact_mod_cast hp.2.le.trans (min_le_right _ _)
  · rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith [hp.1])]
    linarith [hp.2.trans_le (min_le_left _ _)]

/-- A lower bound at the rational times of a window `[a, b] ⊆ [0, ∞)` holds at every point of `[a, b)` (continuity of
the curve within `[0, ∞)`). -/
theorem le_of_ratWindow {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) {f : ℂ → ℝ} (hf : Continuous f) {c : ℝ}
    {a b : ℚ} (ha : 0 ≤ a) (hle : ∀ p : ℚ, a ≤ p → p ≤ b → c ≤ f (γ p)) {s : ℝ} (has : (a : ℝ) ≤ s)
    (hsb : s < b) : c ≤ f (γ s) := by
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hsub : ratWindow a b ⊆ Ici 0 := by
    rintro _ ⟨p, rfl, hap, -⟩
    exact mem_Ici.2 (ha'.trans (by exact_mod_cast hap))
  have hs0 : s ∈ Ici (0 : ℝ) := mem_Ici.2 (ha'.trans has)
  have hcw : ContinuousWithinAt (fun u => f (γ u)) (ratWindow a b) s :=
    hf.continuousAt.comp_continuousWithinAt ((hγ s hs0).mono hsub)
  refine ContinuousWithinAt.closure_le (mem_closure_ratWindow has hsb) continuousWithinAt_const hcw ?_
  rintro _ ⟨p, rfl, hap, hpb⟩
  exact hle p hap hpb

/-- **Positive imaginary part on rational windows**: on every rational window `[a, b]` with `0 < a`, the imaginary
part of the curve at rational times is bounded below by some `1/(m + 1)`. -/
def ImPosCond (γ : ℝ → ℂ) : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → ∃ m : ℕ, ∀ p : ℚ, a ≤ p → p ≤ b → (1 : ℝ) / (m + 1) ≤ (γ p).im

/-- **Separation of disjoint rational windows**: for rational `0 ≤ a < b < c < d`, the values of the curve at rational
times of `[a, b]` and of `[c, d]` are at distance at least some `1/(m + 1)`. -/
def SepCond (γ : ℝ → ℂ) : Prop :=
  ∀ a b c d : ℚ, 0 ≤ a → a < b → b < c → c < d → ∃ m : ℕ, ∀ p q : ℚ, a ≤ p → p ≤ b → c ≤ q → q ≤ d →
    (1 : ℝ) / (m + 1) ≤ ‖γ p - γ q‖

/-- A curve continuous on `[0, ∞)` with separated rational windows is injective on `[0, ∞)`. -/
theorem injOn_of_sepCond {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) (hsep : SepCond γ) : InjOn γ (Ici 0) := by
  have key : ∀ s t : ℝ, 0 ≤ s → s < t → γ s ≠ γ t := by
    intro s t hs hst heq
    obtain ⟨b, hb⟩ := exists_rat_btwn (show s < (s + t) / 2 by linarith)
    obtain ⟨c, hc⟩ := exists_rat_btwn (show (s + t) / 2 < t by linarith)
    obtain ⟨d, hd⟩ := exists_rat_btwn (show t < t + 1 by linarith)
    have hb0 : (0 : ℚ) < b := by exact_mod_cast hs.trans_lt hb.1
    have hbc : b < c := by exact_mod_cast hb.2.trans hc.1
    have hcd : c < d := by exact_mod_cast hc.2.trans hd.1
    obtain ⟨m, hm⟩ := hsep 0 b c d le_rfl hb0 hbc hcd
    have h1 : ∀ q : ℚ, c ≤ q → q ≤ d → (1 : ℝ) / (m + 1) ≤ ‖γ s - γ q‖ := fun q hcq hqd =>
      le_of_ratWindow hγ (f := fun z => ‖z - γ q‖) (by fun_prop) le_rfl
        (fun p hp hpb => hm p q hp hpb hcq hqd) (by exact_mod_cast hs) hb.1
    have h2 : (1 : ℝ) / (m + 1) ≤ ‖γ s - γ t‖ :=
      le_of_ratWindow hγ (f := fun z => ‖γ s - z‖) (by fun_prop) (hb0.le.trans hbc.le) h1 hc.2.le hd.1
    rw [heq, sub_self, norm_zero] at h2
    have : (0 : ℝ) < 1 / (m + 1) := by positivity
    linarith
  intro s hs t ht heq
  rcases lt_trichotomy s t with hst | rfl | hts
  · exact absurd heq (key s t (mem_Ici.1 hs) hst)
  · rfl
  · exact absurd heq.symm (key t s (mem_Ici.1 ht) hts)

/-- A curve continuous on `[0, ∞)` with imaginary parts bounded below on rational windows maps `(0, ∞)` into `ℍ`. -/
theorem mem_H_of_imPosCond {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) (him : ImPosCond γ) {t : ℝ} (ht : 0 < t) :
    γ t ∈ H := by
  obtain ⟨a, ha⟩ := exists_rat_btwn ht
  obtain ⟨b, hb⟩ := exists_rat_btwn (show t < t + 1 by linarith)
  have ha0 : (0 : ℚ) < a := by exact_mod_cast ha.1
  obtain ⟨m, hm⟩ := him a b ha0 (by exact_mod_cast ha.2.trans hb.1)
  have h := le_of_ratWindow hγ (f := Complex.im) Complex.continuous_im ha0.le hm ha.2.le hb.1
  show 0 < (γ t).im
  exact lt_of_lt_of_le (by positivity) h

/-- **The window conditions give a proper arc.** -/
theorem isProperArc_of_conds {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0)) (h0 : γ 0 = 0) (hsep : SepCond γ)
    (him : ImPosCond γ) (ht : Tendsto (fun t => ‖γ t‖) atTop atTop) : IsProperArc γ where
  cont := hc
  inj := injOn_of_sepCond hc hsep
  zero := h0
  mem_H := fun _ h => mem_H_of_imPosCond hc him h
  tendsto := ht

/-- A simple proper arc has separated rational windows. -/
theorem IsProperArc.sepCond {γ : ℝ → ℂ} (hγ : IsProperArc γ) : SepCond γ := by
  intro a b c d ha hab hbc hcd
  have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (b : ℝ) < c := by exact_mod_cast hbc
  set K : Set (ℝ × ℝ) := Icc (a : ℝ) b ×ˢ Icc (c : ℝ) d with hKdef
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKne : K.Nonempty :=
    ⟨((a : ℝ), (c : ℝ)), left_mem_Icc.2 (by exact_mod_cast hab.le), left_mem_Icc.2 (by exact_mod_cast hcd.le)⟩
  have hK1 : ∀ x ∈ K, x.1 ∈ Ici (0 : ℝ) := fun x hx => mem_Ici.2 (ha'.trans hx.1.1)
  have hK2 : ∀ x ∈ K, x.2 ∈ Ici (0 : ℝ) := fun x hx =>
    mem_Ici.2 (ha'.trans ((by exact_mod_cast hab.le : (a : ℝ) ≤ b).trans (hb'.le.trans hx.2.1)))
  have hcont : ContinuousOn (fun x : ℝ × ℝ => ‖γ x.1 - γ x.2‖) K :=
    ((hγ.cont.comp continuousOn_fst hK1).sub (hγ.cont.comp continuousOn_snd hK2)).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKne hcont
  have hpos : 0 < ‖γ x₀.1 - γ x₀.2‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    have e := hγ.inj (hK1 x₀ hx₀) (hK2 x₀ hx₀) h
    have h1 : x₀.1 ≤ b := hx₀.1.2
    have h2 : (c : ℝ) ≤ x₀.2 := hx₀.2.1
    linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  refine ⟨m, fun p q hap hpb hcq hqd => hm.le.trans (isMinOn_iff.1 hmin ((p : ℝ), (q : ℝ)) ?_)⟩
  show ((a : ℝ) ≤ p ∧ (p : ℝ) ≤ b) ∧ ((c : ℝ) ≤ q ∧ (q : ℝ) ≤ d)
  exact ⟨⟨by exact_mod_cast hap, by exact_mod_cast hpb⟩, ⟨by exact_mod_cast hcq, by exact_mod_cast hqd⟩⟩

/-- A simple proper arc has imaginary parts bounded below on rational windows. -/
theorem IsProperArc.imPosCond {γ : ℝ → ℂ} (hγ : IsProperArc γ) : ImPosCond γ := by
  intro a b ha hab
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hne : (Icc (a : ℝ) b).Nonempty := nonempty_Icc.2 (by exact_mod_cast hab.le)
  have hsub : Icc (a : ℝ) b ⊆ Ici 0 := fun u hu => mem_Ici.2 (ha'.le.trans hu.1)
  obtain ⟨u₀, hu₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn hne (Complex.continuous_im.comp_continuousOn (hγ.cont.mono hsub))
  have hpos : 0 < (γ u₀).im := hγ.mem_H u₀ (ha'.trans_le hu₀.1)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  exact ⟨m, fun p hap hpb =>
    hm.le.trans (isMinOn_iff.1 hmin (p : ℝ) ⟨by exact_mod_cast hap, by exact_mod_cast hpb⟩)⟩

/-- **Two proper arcs with the same hitting code have the same range** (the ranges are closed, and an open set meets
a range iff the hitting code is `1` at a rational disc inside it). -/
theorem arcRange_eq_of_hitCode_eq {γ₁ γ₂ : ℝ → ℂ} (h₁ : IsProperArc γ₁) (h₂ : IsProperArc γ₂)
    (he : hitCode γ₁ = hitCode γ₂) : arcRange γ₁ = arcRange γ₂ := by
  have hsub : ∀ {γ γ' : ℝ → ℂ}, IsProperArc γ → IsProperArc γ' → hitCode γ = hitCode γ' →
      arcRange γ ⊆ arcRange γ' := by
    intro γ γ' hγ hγ' he z hz
    by_contra hz'
    have hU : IsOpen (arcRange γ')ᶜ := (hγ'.isClosed_image isClosed_Ici subset_rfl).isOpen_compl
    obtain ⟨i, hiU, hi⟩ := (arcRange_inter_nonempty_iff_hitCode hγ.cont hU).1 ⟨z, hz, hz'⟩
    rw [he] at hi
    obtain ⟨w, hw, hwU⟩ := (arcRange_inter_nonempty_iff_hitCode hγ'.cont hU).2 ⟨i, hiU, hi⟩
    exact hwU hw
  exact (hsub h₁ h₂ he).antisymm (hsub h₂ h₁ he.symm)

end Windows

/-! ### Codes: the range of the trace determines the code -/

section Code

open Exist Sec2.Assembly

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The trace of a history code, read at every real time by the measurable trace evaluation `LP.traceAt`. -/
def codeLine (x : XCode nL nR) (s : ℝ) : ℂ := LP.traceAt s.toNNReal (cw x)

theorem measurable_codeLine (s : ℝ) : Measurable fun x : XCode nL nR => codeLine x s :=
  (LP.measurable_traceAt _).comp measurable_cw

theorem measurable_hitCode_codeLine : Measurable fun x : XCode nL nR => hitCode (codeLine x) :=
  measurable_hitCode.comp (measurable_pi_iff.2 measurable_codeLine)

theorem measurableSet_imPosCond : MeasurableSet {x : XCode nL nR | ImPosCond (codeLine x)} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b => ?_)
  refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.exists fun m => ?_))
  refine Measurable.forall fun p => Measurable.imp measurable_const (Measurable.imp measurable_const ?_)
  exact measurableSet_setOfPred.1
    (measurableSet_le measurable_const (Complex.measurable_im.comp (measurable_codeLine _)))

theorem measurableSet_sepCond : MeasurableSet {x : XCode nL nR | SepCond (codeLine x)} := by
  refine measurableSet_setOfPred.2 (Measurable.forall fun a => Measurable.forall fun b =>
    Measurable.forall fun c => Measurable.forall fun d => ?_)
  refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
    (Measurable.imp measurable_const (Measurable.exists fun m => ?_))))
  refine Measurable.forall fun p => Measurable.forall fun q => Measurable.imp measurable_const
    (Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const ?_)))
  exact measurableSet_setOfPred.1
    (measurableSet_le measurable_const ((measurable_codeLine _).sub (measurable_codeLine _)).norm)

/-- **The range set**: codes of `Exist.DetSet` with infinite lifetime, a transient generating trace on `[0, ∞)`, and
the two window conditions on the trace (so that the trace is a simple proper arc). -/
def RangeSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Set (XCode nL nR) :=
  DetSet a xL xR ρL ρR ∩ {x | cζ x = ⊤} ∩ {x | (cw x, (⊤ : ℝ≥0∞)) ∈ Sec7.RandRestart.traceSet} ∩
    {x | ImPosCond (codeLine x)} ∩ {x | SepCond (codeLine x)}

theorem measurableSet_rangeSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : MeasurableSet (RangeSet a xL xR ρL ρR) :=
  ((((measurableSet_detSet a xL xR ρL ρR).inter (measurable_cζ (measurableSet_singleton ⊤))).inter
    ((measurable_cw.prodMk measurable_const) Sec7.RandRestart.measurableSet_traceSet)).inter
    measurableSet_imPosCond).inter measurableSet_sepCond

/-- **On the range set, the trace is a simple proper Loewner trace of a continuous driver from `0`.** -/
theorem trace_of_mem_rangeSet {x : XCode nL nR} (hx : x ∈ RangeSet a xL xR ρL ρR) :
    Continuous (cw x) ∧ cw x 0 = 0 ∧ IsLoewnerTrace (Ito.rpath (cw x)) (codeLine x) ∧
      IsProperArc (codeLine x) := by
  obtain ⟨⟨⟨⟨hdet, hζ⟩, htr⟩, him⟩, hsep⟩ := hx
  have hζ' : cζ x = ⊤ := hζ
  have hcrel := hdet.1.1
  have hcw := hcrel.1.1.continuousOn_w
  have hw0 : cw x 0 = 0 := hcrel.1.2.2.1
  have hc : ContinuousOn (cw x) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} :=
    hcw.mono fun t _ => show (t : ℝ≥0∞) < cζ x by rw [hζ']; exact ENNReal.coe_lt_top
  have hcont : Continuous (cw x) := continuousOn_univ.1 (hc.mono fun t _ => ENNReal.coe_lt_top)
  obtain ⟨η, hη, htend⟩ := (Sec7.RandRestart.mem_traceSet_iff hc hw0
    (fun _ h => absurd h (lt_irrefl _))).1 htr
  have hline : codeLine x = fun s : ℝ => η s.toNNReal := by
    funext s
    exact LP.traceAt_eq_of_isGeneratingTrace hη hc hw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  refine ⟨hcont, hw0, ?_, ?_⟩
  · rw [hline]
    exact isLoewnerTrace_of_isGeneratingTrace hη
  · refine isProperArc_of_conds ?_ ?_ hsep him ?_
    · rw [hline]; exact (hηc.comp continuous_real_toNNReal).continuousOn
    · rw [hline]; simpa using hη.1
    · rw [hline]; exact (htend rfl).comp tendsto_real_toNNReal_atTop

/-- **On the range set, the hitting code of the range of the trace determines the code** (`a > 0`): equal hitting
codes give equal ranges (`arcRange_eq_of_hitCode_eq`), equal ranges of simple proper Loewner traces give equal drivers
(`eqOn_of_arcRange_eq`, Proposition 4.18's "half-plane capacity determines the parameter"), and the driver determines
the code (`Exist.injOn_traceOfCode`). -/
theorem injOn_hitCode_codeLine (ha : 0 < a) :
    InjOn (fun x : XCode nL nR => hitCode (codeLine x)) (RangeSet a xL xR ρL ρR) := by
  intro x hx x' hx' he
  obtain ⟨hc, h0, hL, hP⟩ := trace_of_mem_rangeSet hx
  obtain ⟨hc', h0', hL', hP'⟩ := trace_of_mem_rangeSet hx'
  have hr := arcRange_eq_of_hitCode_eq hP hP' he
  have hr0 : Ito.rpath (cw x) 0 = 0 := by rw [Ito.rpath, Real.toNNReal_zero, h0]
  have hr0' : Ito.rpath (cw x') 0 = 0 := by rw [Ito.rpath, Real.toNNReal_zero, h0']
  obtain ⟨-, hW⟩ := eqOn_of_arcRange_eq hL hL' hP hP' (hc.comp continuous_real_toNNReal)
    (hc'.comp continuous_real_toNNReal) hr0 hr0' hr
  have hw : cw x = cw x' := funext fun t => by
    have e := hW (mem_Ici.2 (NNReal.coe_nonneg t))
    rwa [Ito.rpath_coe, Ito.rpath_coe] at e
  have hζ : cζ x = cζ x' := by rw [hx.1.1.1.2, hx'.1.1.1.2]
  refine injOn_traceOfCode ha hx.1.1.1.1 hx'.1.1.1.1 ?_
  unfold traceOfCode
  rw [hw, hζ]

end Code

/-! ### The history is a Borel function of the field once the range is -/

section History

open Exist Sec2.Assembly
open LQGMetric (AEDeterminedBy)

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Range determination gives history determination.** For an integrated evolution (`a > 0`) whose seed line is
almost surely a simple proper arc on an infinite lifetime, given by a generating trace: if the hitting code of the
range of the seed line is almost surely a Borel function of the field `h`, then so is the killed driving history
(Lusin–Souslin on the range set). -/
theorem isFieldDeterminedHistory_of_aeDeterminedBy_hitCode {a : ℝ} (ha : 0 < a)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hline : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η ∧
      seedLine ζ W ω = fun s : ℝ => η s.toNNReal) ∧ IsProperArc (seedLine ζ W ω))
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hdet : AEDeterminedBy (fun ω => hitCode (seedLine ζ W ω)) h P) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  obtain ⟨F, hF, hDF⟩ := hdet
  obtain ⟨B', -, hB'c, -, -, hB'ae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  obtain ⟨G, hGm, hG⟩ := exists_measurable_leftInverse_of_injOn
    (measurable_hitCode_codeLine (nL := nL) (nR := nR)) (measurableSet_rangeSet a xL xR ρL ρR)
    (injOn_hitCode_codeLine ha)
  have hGF : Measurable fun f => G (F f) := hGm.comp hF
  refine ⟨fun f => (cζ (G (F f)), cw (G (F f)), fun i => cvL (G (F f)) i, fun j => cvR (G (F f)) j),
    (measurable_cζ.comp hGF).prodMk ((measurable_cw.comp hGF).prodMk
      ((measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun t => (measurable_cvL_at i t).comp hGF).prodMk
      (measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun t => (measurable_cvR_at j t).comp hGF))), ?_⟩
  filter_upwards [hDF, hline, ae_codeOf_mem ha hE hB'c hB'ae] with ω hDω hlω hcode
  obtain ⟨hζ, ⟨η, hη, hseed⟩, harc⟩ := hlω
  obtain ⟨hx₁, hdec⟩ := hcode
  set x₀ := frz (codeOf xL xR B' W VL VR ζ ω) with hx₀def
  have hζx : cζ x₀ = ζ ω := rfl
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω := fun t => by rw [hζ]; exact ENNReal.coe_lt_top
  have hcwx : cw x₀ = fun t => W t ω := funext fun t => (hdec t (hlt t)).1
  have hηx : IsGeneratingTrace (cw x₀) ⊤ η := by rw [hcwx]; exact hη
  have hcrel : x₀ ∈ CRel a xL xR ρL ρR := frz_mem_cRel hx₁
  have hk : (fun t => killedProc ζ W t ω) = fun t => W t ω := funext (killedProc_of_eq_top hζ)
  have hline : codeLine x₀ = seedLine ζ W ω := by
    funext s
    simp only [codeLine, seedLine, hk, hcwx]
  have hcw := hcrel.1.1.continuousOn_w
  have hc : ContinuousOn (cw x₀) {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} :=
    hcw.mono fun t _ => show (t : ℝ≥0∞) < cζ x₀ by rw [hζx]; exact hlt t
  have htend : Tendsto (fun t => ‖η t‖) atTop atTop := by
    have e : (fun t : ℝ≥0 => ‖η t‖) = (fun s : ℝ => ‖seedLine ζ W ω s‖) ∘ (fun t : ℝ≥0 => (t : ℝ)) := by
      funext t; simp [hseed]
    rw [e]
    exact harc.tendsto.comp (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hmem : x₀ ∈ RangeSet a xL xR ρL ρR := by
    refine ⟨⟨⟨⟨⟨⟨hcrel, frozenB_frz hx₁.1.1⟩, fun n k hT => mem_traceSet_of_isGeneratingTrace hcrel hT hηx le_top⟩,
      hζx.trans hζ⟩, ?_⟩, ?_⟩, ?_⟩
    · exact (Sec7.RandRestart.mem_traceSet_iff hc hcrel.1.2.2.1 (fun _ h => absurd h (lt_irrefl _))).2
        ⟨η, hηx, fun _ => htend⟩
    · show ImPosCond (codeLine x₀); rw [hline]; exact harc.imPosCond
    · show SepCond (codeLine x₀); rw [hline]; exact harc.sepCond
  have hΨ : G (F (h ω)) = x₀ := by
    have e : F (h ω) = hitCode (codeLine x₀) := by rw [hline]; exact hDω.symm
    rw [e]; exact hG x₀ hmem
  simp only [hΨ]
  refine ⟨hζx, fun t ht => ⟨(hdec t ht).1, fun i => (hdec t ht).2.1 i, fun j => (hdec t ht).2.2.1 j⟩⟩

/-- **Proposition 4.18's words: range determination gives history determination.** For a marked chain (`κ = 4`) of an
ordered word with nonnegative cumulative weights, if the hitting code of the range of the seed line is almost surely a
Borel function of the field, then so is the killed driving history. -/
theorem IsMarkedChain.isFieldDeterminedHistory_of_aeDeterminedBy_hitCode (hxF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hdet : AEDeterminedBy (fun ω => hitCode (seedLine ζ W ω)) h P) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  refine WangWu.isFieldDeterminedHistory_of_aeDeterminedBy_hitCode (a := 4) (by norm_num) hE ?_ hdet
  filter_upwards [IsMarkedChain.ae_seedLine hxF hcum hE] with ω hω
  exact ⟨hω.1, hω.2.1, hω.2.2.2.1⟩

/-- **Proposition 4.18, determination, from the range form of the glued identity.** For a marked chain of an ordered
word with nonnegative cumulative weights, if the hitting code of the range of the seed line is almost surely a
measurable function `L` of a glued sample of `κ(h)` (`κ` any Markov kernel from the field space), then the killed
history is field-determined (Lemma 4.1 for the glued sample, then `isFieldDeterminedHistory_of_aeDeterminedBy_hitCode`). -/
theorem IsMarkedChain.isFieldDeterminedHistory_of_glue_hitCode (hxF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR) (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : Measurable h) {β : Type*} [MeasurableSpace β]
    (κ : ProbabilityTheory.Kernel (LQGMetric.DistOn upperHalfPlaneOpens) β) [IsMarkovKernel κ]
    {L : β → ℚ × ℚ × ℚ → ℝ} (hL : Measurable L)
    (heq : ∀ᵐ p ∂(glueMeasure P κ h hh), hitCode (seedLine ζ W p.1) = L p.2) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  have hD : Measurable fun ω => hitCode (seedLine ζ W ω) :=
    measurable_hitCode.comp (measurable_pi_iff.2 (measurable_seedLine hE.2.1))
  exact hE.isFieldDeterminedHistory_of_aeDeterminedBy_hitCode hxF hcum
    (aeDeterminedBy_of_glue_ae_eq κ hh hD hL heq)

end History

end InteractingSLE.WangWu
