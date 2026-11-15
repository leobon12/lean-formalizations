/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part1Main
import InteractingSLE.Spec.Sec5.Prop49QExitRestart
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# The image endpoint, part 2: the Borel code event of a simple trace in `ℍ` before the lifetime

Packet PROVE-A2-IMGEND. Source: Astra, *Follow-up 5* §1.2 and Lemma 1.2 (L180–L196,
`source/external/AstraIG1/ig1_followup5.txt`, R73): "Let `c ↦ Q_c` be the Borel canonical one-curve kernel … If `E` is
the jointly measurable endpoint event and `Q_c(E_c) = 1` for every admissible deterministic `c` …". Here `E` is coded
on the canonical solution codes of PROVE-SEC2-PATCH2 (`XCode`), through countably many rational windows:

* `SimpPath w vL vR ζ`: the trace event on every rational horizon before `ζ`; on every rational window `[a, b]` with
  `0 < a` and `b < ζ`, a uniform lower bound for the imaginary part of the trace `LP.traceAt` and for all the gaps
  between the driver and the marks; on any two disjoint rational windows before `ζ`, a uniform separation of the
  trace values (WangWu's `ImPosCond`/`SepCond`, here below the lifetime and with the marks);
* `simpSet`: the codes whose decoded processes satisfy `SimpPath` — a Borel set (`measurableSet_simpSet`);
* `SimpPath.isGeneratingTrace`, `SimpPath.injOn`, `SimpPath.mem_H`, `SimpPath.noncoll`: the trace `LP.traceAt · w`
  generates the chain before `ζ`, is injective before `ζ`, in `ℍ` and with the marks strictly separated from the
  driver at positive times before `ζ` (continuity extends the rational bounds);
* `simpPath_of`: conversely these properties give `SimpPath` (compactness on the windows);
* `codeLaw_compl_eq_zero_of_ae'`: PROVE-GLUECOND9's `codeLaw_compl_eq_zero_of_ae` with an event that may depend on
  the marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2ImgEnd

open QuantumZipper (H)
open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {nL nR : ℕ}

/-! ### The path predicate and its code set -/

/-- **A simple trace in `ℍ` before `ζ`, with the marks off the driver, read on rational windows.** -/
def SimpPath (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  (∀ r : ℚ≥0, ((r : ℝ≥0) : ℝ≥0∞) < ζ → (w, ((r : ℝ≥0) : ℝ≥0∞)) ∈ traceSet) ∧
    (∀ a b : ℚ≥0, 0 < a → a < b → ((b : ℝ≥0) : ℝ≥0∞) < ζ → ∃ m : ℕ, ∀ p : ℚ≥0, a ≤ p → p ≤ b →
      (1 : ℝ) / (m + 1) ≤ (LP.traceAt (p : ℝ≥0) w).im ∧ (∀ i, (1 : ℝ) / (m + 1) ≤ w p - vL i p) ∧
        ∀ j, (1 : ℝ) / (m + 1) ≤ vR j p - w p) ∧
    ∀ a b c d : ℚ≥0, a < b → b < c → c < d → ((d : ℝ≥0) : ℝ≥0∞) < ζ → ∃ m : ℕ, ∀ p q : ℚ≥0, a ≤ p → p ≤ b →
      c ≤ q → q ≤ d → (1 : ℝ) / (m + 1) ≤ ‖LP.traceAt (p : ℝ≥0) w - LP.traceAt (q : ℝ≥0) w‖

/-- The codes whose decoded processes satisfy `SimpPath`. -/
def simpSet : Set (XCode nL nR) := {x | SimpPath (cw x) (cvL x) (cvR x) (cζ x)}

theorem measurableSet_simpSet : MeasurableSet (simpSet (nL := nL) (nR := nR)) := by
  have hlt : ∀ r : ℚ≥0, Measurable fun x : XCode nL nR => ((r : ℝ≥0) : ℝ≥0∞) < cζ x := fun r =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_cζ)
  have htr : ∀ p : ℚ≥0, Measurable fun x : XCode nL nR => LP.traceAt (p : ℝ≥0) (cw x) := fun p =>
    (LP.measurable_traceAt _).comp Exist.measurable_cw
  refine measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.and ?_ ?_))
  · refine Measurable.forall fun r => (hlt r).imp ?_
    exact measurableSet_setOfPred.1
      ((Exist.measurable_cw.prodMk measurable_const) measurableSet_traceSet)
  · refine Measurable.forall fun a => Measurable.forall fun b => measurable_const.imp
      (measurable_const.imp ((hlt b).imp (Measurable.exists fun m => Measurable.forall fun p =>
        measurable_const.imp (measurable_const.imp (Measurable.and ?_ (Measurable.and ?_ ?_))))))
    · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (Complex.measurable_im.comp (htr p)))
    · exact Measurable.forall fun i => measurableSet_setOfPred.1 (measurableSet_le measurable_const
        ((measurable_cw_at _).sub (measurable_cvL_at i _)))
    · exact Measurable.forall fun j => measurableSet_setOfPred.1 (measurableSet_le measurable_const
        ((measurable_cvR_at j _).sub (measurable_cw_at _)))
  · refine Measurable.forall fun a => Measurable.forall fun b => Measurable.forall fun c =>
      Measurable.forall fun d => measurable_const.imp (measurable_const.imp (measurable_const.imp
        ((hlt d).imp (Measurable.exists fun m => Measurable.forall fun p => Measurable.forall fun q =>
          measurable_const.imp (measurable_const.imp (measurable_const.imp (measurable_const.imp ?_)))))))
    exact measurableSet_setOfPred.1 (measurableSet_le measurable_const ((htr p).sub (htr q)).norm)

theorem mem_simpSet_iff {x : XCode nL nR} : x ∈ simpSet ↔ SimpPath (cw x) (cvL x) (cvR x) (cζ x) := Iff.rfl

/-! ### Rational approximation -/

/-- A rational time strictly between two times. -/
theorem exists_nnrat_btwn {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < q ∧ (q : ℝ≥0) < b := by
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := LocalExt.dense_range_coe_nnrat.exists_between h
  exact ⟨q, hq⟩

/-- A rational time strictly between a time and a horizon. -/
theorem exists_nnrat_btwn_top {s : ℝ≥0} {ζ : ℝ≥0∞} (h : (s : ℝ≥0∞) < ζ) :
    ∃ q : ℚ≥0, s < q ∧ (((q : ℝ≥0) : ℝ≥0∞)) < ζ := by
  obtain ⟨r, hsr, hrζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  obtain ⟨q, hsq, hqr⟩ := exists_nnrat_btwn (ENNReal.coe_lt_coe.1 hsr)
  exact ⟨q, hsq, lt_trans (ENNReal.coe_lt_coe.2 hqr) hrζ⟩

/-- A lower bound at the rational times of a window holds at an interior time of continuity. -/
theorem le_of_forall_nnrat {f : ℝ≥0 → ℝ} {a b : ℚ≥0} {t : ℝ≥0} (hat : (a : ℝ≥0) < t) (htb : t < b)
    (hf : ContinuousAt f t) {c : ℝ} (hc : ∀ p : ℚ≥0, a ≤ p → p ≤ b → c ≤ f p) : c ≤ f t := by
  by_contra hlt
  rw [not_le] at hlt
  have hev : ∀ᶠ u in 𝓝 t, f u < c := hf.eventually (gt_mem_nhds hlt)
  obtain ⟨l, u, ⟨hlt', htu⟩, hsub⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨_, hat⟩ ⟨_, htb⟩).1 hev
  obtain ⟨p, hp1, hp2⟩ := exists_nnrat_btwn ((max_lt hlt' hat).trans (lt_min htu htb) :
    max l (a : ℝ≥0) < min u (b : ℝ≥0))
  have hpl : l < p := lt_of_le_of_lt (le_max_left _ _) hp1
  have hpa : (a : ℝ≥0) < p := lt_of_le_of_lt (le_max_right _ _) hp1
  have hpu : (p : ℝ≥0) < u := lt_of_lt_of_le hp2 (min_le_left _ _)
  have hpb : (p : ℝ≥0) < b := lt_of_lt_of_le hp2 (min_le_right _ _)
  have h1 : f p < c := hsub ⟨hpl, hpu⟩
  have h2 := hc p (by exact_mod_cast hpa.le) (by exact_mod_cast hpb.le)
  linarith

/-- A continuous positive function on a compact set has a uniform lower bound `1/(m + 1)`. -/
theorem exists_nat_le_of_pos {α : Type*} [TopologicalSpace α] {K : Set α} (hK : IsCompact K) {f : α → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ u ∈ K, 0 < f u) : ∃ m : ℕ, ∀ u ∈ K, (1 : ℝ) / (m + 1) ≤ f u := by
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · exact ⟨0, fun u hu => by rw [hKe] at hu; exact absurd hu (Set.notMem_empty u)⟩
  obtain ⟨u₀, hu₀, hmin⟩ := hK.exists_isMinOn hKn hf
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hpos u₀ hu₀)
  exact ⟨m, fun u hu => hm.le.trans (hmin hu)⟩

/-- Finitely many such lower bounds combine. -/
theorem exists_nat_le_of_forall {ι : Type*} [Fintype ι] {P : ι → ℝ → Prop}
    (hP : ∀ k (m m' : ℕ), m ≤ m' → P k ((1 : ℝ) / (m + 1)) → P k ((1 : ℝ) / (m' + 1)))
    (h : ∀ k, ∃ m : ℕ, P k ((1 : ℝ) / (m + 1))) : ∃ m : ℕ, ∀ k, P k ((1 : ℝ) / (m + 1)) := by
  choose m hm using h
  exact ⟨Finset.univ.sup m, fun k => hP k _ _ (Finset.le_sup (Finset.mem_univ k)) (hm k)⟩

/-! ### Consequences of the path predicate -/

section Path

variable {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The trace `LP.traceAt · w` generates the chain before every `s < ζ`. -/
theorem SimpPath.isGeneratingTrace (h : SimpPath w vL vR ζ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) : IsGeneratingTrace w s (fun t => LP.traceAt t w) := by
  obtain ⟨r, hsr, hrζ⟩ := exists_nnrat_btwn_top hs
  have hwr : ContinuousOn w {t | (t : ℝ≥0∞) < ((r : ℝ≥0) : ℝ≥0∞)} := hw.mono fun t ht => lt_trans ht hrζ
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hlim : 0 < ((r : ℝ≥0) : ℝ≥0∞) → ((r : ℝ≥0) : ℝ≥0∞) < ⊤ →
      ∃ w₀ : ℝ, Tendsto w (𝓝[<] (((r : ℝ≥0) : ℝ≥0∞)).toNNReal) (𝓝 w₀) := fun _ _ => by
    rw [ENNReal.toNNReal_coe]
    exact ⟨w r, ((hw.continuousAt (hopen.mem_nhds hrζ)).tendsto).mono_left nhdsWithin_le_nhds⟩
  obtain ⟨η, hη, -⟩ := (mem_traceSet_iff hwr hw0 hlim).1 (h.1 r hrζ)
  have heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ s → LP.traceAt t w = η t := fun t ht =>
    LP.traceAt_eq_of_isGeneratingTrace hη hwr hw0 (lt_of_le_of_lt ht (by exact_mod_cast hsr))
  exact A2P1.isGeneratingTrace_congr (hη.mono_horizon (by exact_mod_cast hsr.le)) heq

/-- The trace is continuous before `ζ`. -/
theorem SimpPath.continuousAt (h : SimpPath w vL vR ζ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : ContinuousAt (fun s => LP.traceAt s w) t := by
  obtain ⟨r, htr, hrζ⟩ := exists_nnrat_btwn_top ht
  have hc := (h.isGeneratingTrace hw hw0 hrζ).2.1
  have hset : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ ((r : ℝ≥0) : ℝ≥0∞)} = Iic (r : ℝ≥0) := by
    ext s; simp only [mem_ofPred_eq, mem_Iic, ENNReal.coe_le_coe]
  rw [hset] at hc
  exact hc.continuousAt (Iic_mem_nhds htr)

/-- At positive times before `ζ` the trace is in `ℍ` and the marks are strictly separated from the driver. -/
theorem SimpPath.mem_H (h : SimpPath w vL vR ζ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < ζ) :
    LP.traceAt t w ∈ H ∧ (∀ i, vL i t < w t) ∧ ∀ j, w t < vR j t := by
  obtain ⟨a, ha0, hat⟩ := exists_nnrat_btwn ht0
  obtain ⟨b, htb, hbζ⟩ := exists_nnrat_btwn_top ht
  have ha0' : (0 : ℚ≥0) < a := by exact_mod_cast ha0
  have hab : a < b := by exact_mod_cast hat.trans htb
  obtain ⟨m, hm⟩ := h.2.1 a b ha0' hab hbζ
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {s | (s : ℝ≥0∞) < ζ} → ContinuousAt f t := fun hf =>
    hf.continuousAt (hopen.mem_nhds ht)
  have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
  refine ⟨?_, fun i => ?_, fun j => ?_⟩
  · have := le_of_forall_nnrat hat htb (Complex.continuous_im.continuousAt.comp (h.continuousAt hw hw0 ht))
      fun p hp1 hp2 => (hm p hp1 hp2).1
    exact lt_of_lt_of_le hpos this
  · have := le_of_forall_nnrat hat htb ((hca hw).sub (hca (hvL i))) fun p hp1 hp2 => (hm p hp1 hp2).2.1 i
    simp only [Pi.sub_apply] at this
    linarith
  · have := le_of_forall_nnrat hat htb ((hca (hvR j)).sub (hca hw)) fun p hp1 hp2 => (hm p hp1 hp2).2.2 j
    simp only [Pi.sub_apply] at this
    linarith

/-- The trace is injective before `ζ`. -/
theorem SimpPath.injOn (h : SimpPath w vL vR ζ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) :
    InjOn (fun t => LP.traceAt t w) {t | (t : ℝ≥0∞) < ζ} := by
  have key : ∀ s t : ℝ≥0, s < t → (t : ℝ≥0∞) < ζ → LP.traceAt s w ≠ LP.traceAt t w := by
    intro s t hst htζ heq
    obtain ⟨b, hsb, hbt⟩ := exists_nnrat_btwn hst
    obtain ⟨c, hbc, hct⟩ := exists_nnrat_btwn hbt
    obtain ⟨d, htd, hdζ⟩ := exists_nnrat_btwn_top htζ
    have hb : (0 : ℚ≥0) < b := by exact_mod_cast lt_of_le_of_lt zero_le hsb
    have hbc' : b < c := by exact_mod_cast hbc
    have hcd : c < d := by exact_mod_cast hct.trans htd
    obtain ⟨m, hm⟩ := h.2.2 0 b c d hb hbc' hcd hdζ
    have hsζ : (s : ℝ≥0∞) < ζ := lt_trans (ENNReal.coe_lt_coe.2 hst) htζ
    have hcs := h.continuousAt hw hw0 hsζ
    have hct' := h.continuousAt hw hw0 htζ
    -- the bound at `(s, q)` for every rational `q` of the second window
    have h1 : ∀ q : ℚ≥0, c ≤ q → q ≤ d →
        (1 : ℝ) / (m + 1) ≤ ‖LP.traceAt s w - LP.traceAt (q : ℝ≥0) w‖ := by
      intro q hcq hqd
      rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs0 | hs0
      · have := hm 0 q le_rfl (zero_le) hcq hqd
        rw [← hs0]; simpa using this
      · exact le_of_forall_nnrat (a := 0) (b := b) (by simpa using hs0) hsb
          ((hcs.sub continuousAt_const).norm) fun p hp1 hp2 => hm p q hp1 hp2 hcq hqd
    have h2 : (1 : ℝ) / (m + 1) ≤ ‖LP.traceAt s w - LP.traceAt t w‖ :=
      le_of_forall_nnrat hct htd ((continuousAt_const.sub hct').norm) h1
    rw [heq, sub_self, norm_zero] at h2
    have : (0 : ℝ) < 1 / (m + 1) := by positivity
    linarith
  intro s hs t ht heq
  rcases lt_trichotomy s t with hlt | heq' | hgt
  · exact absurd heq (key s t hlt ht)
  · exact heq'
  · exact absurd heq.symm (key t s hgt hs)

/-- **The converse coding**: a generating trace before `ζ` that is simple, in `ℍ` and with the marks strictly
separated from the driver at positive times satisfies the rational window conditions (compactness). -/
theorem simpPath_of (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ})
    (hgen : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → IsGeneratingTrace w s (fun t => LP.traceAt t w))
    (hinj : InjOn (fun t => LP.traceAt t w) {t | (t : ℝ≥0∞) < ζ})
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → LP.traceAt t w ∈ H)
    (hnc : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → (∀ i, vL i t < w t) ∧ ∀ j, w t < vR j t) :
    SimpPath w vL vR ζ := by
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hγc : ∀ b : ℝ≥0, (b : ℝ≥0∞) < ζ → ContinuousOn (fun t => LP.traceAt t w) (Icc 0 b) := fun b hb =>
    (hgen b hb).2.1.mono fun t ht => ENNReal.coe_le_coe.2 ht.2
  have hsub : ∀ {a b : ℝ≥0}, (b : ℝ≥0∞) < ζ → Icc a b ⊆ {t | (t : ℝ≥0∞) < ζ} := fun hb t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hb
  refine ⟨fun r hr => ?_, fun a b ha hab hb => ?_, fun a b c d hab hbc hcd hd => ?_⟩
  · have hwr : ContinuousOn w {t | (t : ℝ≥0∞) < ((r : ℝ≥0) : ℝ≥0∞)} := hw.mono fun t ht => lt_trans ht hr
    have hlim : 0 < ((r : ℝ≥0) : ℝ≥0∞) → ((r : ℝ≥0) : ℝ≥0∞) < ⊤ →
        ∃ w₀ : ℝ, Tendsto w (𝓝[<] (((r : ℝ≥0) : ℝ≥0∞)).toNNReal) (𝓝 w₀) := fun _ _ => by
      rw [ENNReal.toNNReal_coe]
      exact ⟨w r, ((hw.continuousAt (hopen.mem_nhds hr)).tendsto).mono_left nhdsWithin_le_nhds⟩
    exact (mem_traceSet_iff hwr hw0 hlim).2 ⟨_, hgen r hr, fun h => absurd h ENNReal.coe_ne_top⟩
  · set K : Set ℝ≥0 := Icc (a : ℝ≥0) b with hK
    have hKc : IsCompact K := isCompact_Icc
    have hpos : ∀ u ∈ K, 0 < u := fun u hu => lt_of_lt_of_le (by exact_mod_cast ha) hu.1
    have hKζ := hsub (a := (a : ℝ≥0)) hb
    obtain ⟨m, hm⟩ := exists_nat_le_of_forall (ι := Option (Fin nL ⊕ Fin nR))
      (P := fun k c => ∀ u ∈ K, c ≤ (match k with
        | none => (LP.traceAt u w).im
        | some (Sum.inl i) => w u - vL i u
        | some (Sum.inr j) => vR j u - w u))
      (fun k m m' hmm' h u hu => le_trans (one_div_le_one_div_of_le (by positivity)
        (by have : (m : ℝ) ≤ m' := by exact_mod_cast hmm'
            linarith)) (h u hu)) fun k => by
        rcases k with _ | i | j
        · exact exists_nat_le_of_pos hKc (Complex.continuous_im.comp_continuousOn
            ((hγc b hb).mono (Icc_subset_Icc_left zero_le))) fun u hu =>
              (show (0 : ℝ) < (LP.traceAt u w).im from hH u (hpos u hu) (hKζ hu))
        · exact exists_nat_le_of_pos hKc ((hw.mono hKζ).sub ((hvL i).mono hKζ)) fun u hu =>
            sub_pos.2 ((hnc u (hpos u hu) (hKζ hu)).1 i)
        · exact exists_nat_le_of_pos hKc (((hvR j).mono hKζ).sub (hw.mono hKζ)) fun u hu =>
            sub_pos.2 ((hnc u (hpos u hu) (hKζ hu)).2 j)
    refine ⟨m, fun p hp1 hp2 => ?_⟩
    have hpK : ((p : ℝ≥0)) ∈ K := ⟨by exact_mod_cast hp1, by exact_mod_cast hp2⟩
    exact ⟨hm none _ hpK, fun i => hm (some (Sum.inl i)) _ hpK, fun j => hm (some (Sum.inr j)) _ hpK⟩
  · set K : Set (ℝ≥0 × ℝ≥0) := Icc (a : ℝ≥0) b ×ˢ Icc (c : ℝ≥0) d with hK
    have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
    have hdζ := hd
    have hcont : ContinuousOn (fun z : ℝ≥0 × ℝ≥0 => ‖LP.traceAt z.1 w - LP.traceAt z.2 w‖) K := by
      have h1 := hγc d hdζ
      refine (((h1.comp continuousOn_fst fun z hz => ⟨zero_le, ?_⟩).sub
        (h1.comp continuousOn_snd fun z hz => ⟨zero_le, hz.2.2⟩))).norm
      exact hz.1.2.trans (by exact_mod_cast (hbc.trans hcd).le)
    obtain ⟨m, hm⟩ := exists_nat_le_of_pos hKc hcont fun z hz => by
      refine norm_pos_iff.2 (sub_ne_zero.2 fun he => ?_)
      have hz1 : ((z.1 : ℝ≥0) : ℝ≥0∞) < ζ :=
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hz.1.2.trans (by exact_mod_cast (hbc.trans hcd).le))) hd
      have hz2 : ((z.2 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hz.2.2) hd
      have := hinj hz1 hz2 he
      have hlt : z.1 < z.2 := lt_of_le_of_lt hz.1.2 (lt_of_lt_of_le (by exact_mod_cast hbc) hz.2.1)
      exact absurd this hlt.ne
    refine ⟨m, fun p q hp1 hp2 hq1 hq2 => hm ((p : ℝ≥0), (q : ℝ≥0)) ?_⟩
    have h1 : (a : ℝ≥0) ≤ p := by exact_mod_cast hp1
    have h2 : (p : ℝ≥0) ≤ b := by exact_mod_cast hp2
    have h3 : (c : ℝ≥0) ≤ q := by exact_mod_cast hq1
    have h4 : (q : ℝ≥0) ≤ d := by exact_mod_cast hq2
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

end Path

/-! ### The semantic predicate and its congruence -/

section Sem

/-- **The semantic form of `SimpPath`**: the trace generates the chain before `ζ`, is injective before `ζ`, in `ℍ`
at positive times, and the marks are strictly separated from the driver at positive times. -/
def SimpSem (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  (∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → IsGeneratingTrace w s (fun t => LP.traceAt t w)) ∧
    InjOn (fun t => LP.traceAt t w) {t | (t : ℝ≥0∞) < ζ} ∧
    (∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → LP.traceAt t w ∈ H) ∧
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → (∀ i, vL i t < w t) ∧ ∀ j, w t < vR j t

theorem SimpSem.congr {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (he : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t)
    (h : SimpSem w vL vR ζ) : SimpSem w' vL' vR' ζ := by
  have htr : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → LP.traceAt t w' = LP.traceAt t w := fun t ht =>
    (LP.traceAt_congr fun r hr => (he r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht)).1).symm
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun s hs => ?_, fun t ht t' ht' heq => h2 ht ht' ?_, fun t ht0 ht => ?_, fun t ht0 ht => ?_⟩
  · have hg := Sec7.IsGeneratingTrace.congr_lt (h1 s hs) fun t ht => (he t (lt_trans ht hs)).1.symm
    exact A2P1.isGeneratingTrace_congr hg fun t ht => htr t (lt_of_le_of_lt ht hs)
  · simpa only [htr t ht, htr t' ht'] using heq
  · rw [htr t ht]; exact h3 t ht0 ht
  · obtain ⟨e1, e2, e3⟩ := he t ht
    obtain ⟨hL, hR⟩ := h4 t ht0 ht
    exact ⟨fun i => by rw [← e1, ← e2 i]; exact hL i, fun j => by rw [← e1, ← e3 j]; exact hR j⟩

/-- `SimpSem` gives `SimpPath` (the converse coding). -/
theorem SimpSem.simpPath {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : SimpSem w vL vR ζ) (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}) (hvR : ∀ j, ContinuousOn (vR j) {t | (t : ℝ≥0∞) < ζ}) :
    SimpPath w vL vR ζ :=
  simpPath_of hw hw0 hvL hvR h.1 h.2.1 h.2.2.1 h.2.2.2

end Sem

/-! ### Canonical laws -/

section Law

/-- **`codeLaw_compl_eq_zero_of_ae` with an event that may depend on the marks.** If one integrated evolution from a
separated start satisfies `Φ` almost surely, `Φ` only sees the processes before the lifetime, and every canonical
solution code from the start satisfying `Φ` lies in `S`, then `Sᶜ` has canonical law `0` at the start. -/
theorem codeLaw_compl_eq_zero_of_ae' {a : ℝ} (ha : 0 < a) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {S : Set (XCode nL nR)} (hS : MeasurableSet S)
    {Φ : (ℝ≥0 → ℝ) → (Fin nL → ℝ≥0 → ℝ) → (Fin nR → ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (hSΦ : ∀ x ∈ CRel a xL xR ρL ρR, Φ (cw x) (cvL x) (cvR x) (cζ x) → x ∈ S)
    (hΦ : ∀ (w w' : ℝ≥0 → ℝ) (vL vL' : Fin nL → ℝ≥0 → ℝ) (vR vR' : Fin nR → ℝ≥0 → ℝ) (τ : ℝ≥0∞),
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) →
      Φ w vL vR τ → Φ w' vL' vR' τ)
    (hae : ∀ᵐ ω ∂P, Φ (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)) :
    codeLaw a ρL ρR Sᶜ (xL, xR) = 0 := by
  obtain ⟨B', hm, hc, -, hbm, hae'⟩ := QuantumZipper.RS.exists_good_version0 h.1.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  rw [codeLaw, ← map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm,
    Measure.map_apply hpm ((measurableSet_restartSetS hS.compl).preimage measurable_prodMk_left)]
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [ae_codeOf_mem ha h hc hae', hae] with ω ⟨hmem, hdec⟩ hΦω hω
  set x := codeOf xL xR B' W VL VR ζ ω with hx
  have hx1 : x.1 = enc (B' · ω) := rfl
  have hxζ : cζ x = ζ ω := rfl
  have hω' : ((xL, xR), x.1) ∈ lawSetS a ρL ρR Sᶜ := by rw [hx1]; exact hω
  refine (mem_lawSetS_iff hsep hmem).1 hω' (hSΦ x hmem ?_)
  rw [hxζ]
  exact hΦ _ _ _ _ _ _ _ (fun t ht => ⟨((hdec t ht).1).symm, fun i => ((hdec t ht).2.1 i).symm,
    fun j => ((hdec t ht).2.2.1 j).symm⟩) hΦω

theorem lawSetS_union {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (S S' : Set (XCode nL nR)) :
    lawSetS a ρL ρR (S ∪ S') = lawSetS a ρL ρR S ∪ lawSetS a ρL ρR S' := by
  unfold lawSetS
  rw [inter_union_distrib_left, image_union]

theorem codeLaw_union_le {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (S S' : Set (XCode nL nR))
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    codeLaw a ρL ρR (S ∪ S') s ≤ codeLaw a ρL ρR S s + codeLaw a ρL ρR S' s := by
  unfold codeLaw restartSetS
  rw [lawSetS_union]
  exact measure_union_le _ _

theorem codeLaw_mono {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {S S' : Set (XCode nL nR)} (h : S ⊆ S')
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) : codeLaw a ρL ρR S s ≤ codeLaw a ρL ρR S' s := by
  unfold codeLaw restartSetS lawSetS
  exact measure_mono fun f hf => image_mono (inter_subset_inter_right _ h) hf

end Law

/-! ### The code event of the restarts and its full canonical law -/

section Good

variable {k : ℝ} {j n : ℕ} {ρL ρL' : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ}

/-- **The code event of the restarts**: a simple trace in `ℍ` before the lifetime with the marks off the driver (when
the last left mark is off the source), and the left strip end of PROVE-GLUECOND9's `exitCode` (when the start is
strictly separated). -/
def goodSet (k : ℝ) (ρL : Fin (j + 1) → ℝ) (ρR : Fin n → ℝ) : Set (XCode (j + 1) n) :=
  ({x | ¬ (startOf x).1 (Fin.last j) < 0} ∪ simpSet) ∩
    Sec5.Prop49Exit.exitCode k ρL ρR fun s => s.1 (Fin.last j)

theorem measurableSet_goodSet : MeasurableSet (goodSet k ρL ρR) :=
  ((measurableSet_lt (measurable_startOf_fst (Fin.last j)) measurable_const).compl.union
    measurableSet_simpSet).inter (Sec5.Prop49Exit.measurableSet_exitCode (by fun_prop))

/-- **The full canonical law of the code event** at every separated ordered start (A.2 part 1's simple trace and
noncollision, `A2P1.ae_noncollision_simpleTrace`, for the start's evolution; PROVE-GLUECOND9's strip endpoint). The
hypotheses are those of `A2P1.ae_exit_trace`, with the admissibility (by positions) asked for every ordered start. -/
theorem codeLaw_compl_goodSet_eq_zero (hk : 0 < k) (hk4 : k ≤ 4) (hρ' : ∀ i, i ≠ Fin.last j → ρL' i = ρL i)
    (hadm : ∀ s : (Fin (j + 1) → ℝ) × (Fin n → ℝ), IsOrderedForceWord s.1 s.2 →
      Sec4.HasAdmissiblePartialSums k ρL' ρR s.1 s.2)
    (hsum : ∑ i, ρL i ≤ -2) (hpreL : ∀ m : Fin (j + 1), m ≠ Fin.last j → -2 < ∑ i ∈ Finset.Iic m, ρL i)
    (hpreR : ∀ m : Fin n, -2 < ∑ i ∈ Finset.Iic m, ρR i) (hpre : Strip.HasStripPrefixSums k (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus k (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2)
    (s : (Fin (j + 1) → ℝ) × (Fin n → ℝ)) (hsep : SepStart s) (hF : IsOrderedForceWord s.1 s.2) :
    codeLaw k ρL ρR (goodSet k ρL ρR)ᶜ s = 0 := by
  rw [goodSet, compl_inter]
  refine le_antisymm ((codeLaw_union_le _ _ s).trans ?_) bot_le
  rw [Sec5.Prop49Exit.codeLaw_compl_exitCode_eq_zero hk hk4 hpre hq s hsep hF, add_zero]
  refine le_of_eq ?_
  by_cases hl : s.1 (Fin.last j) < 0
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
      exists_isIntegratedSLEEvolution_assembled (a := k) (xL := s.1) (xR := s.2) (ρL := ρL) (ρR := ρR) hk hF
    refine le_antisymm ((codeLaw_mono (compl_subset_compl.2 subset_union_right) s).trans
      (le_of_eq ?_)) bot_le
    refine codeLaw_compl_eq_zero_of_ae' hk hsep hE₀ measurableSet_simpSet (Φ := SimpSem)
      (fun x hx hΦ => ?_) (fun w w' vL vL' vR vR' τ he h => h.congr he) ?_
    · have hfp := hx.1.2.2.isForcePath
      exact hΦ.simpPath hfp.continuousOn_w hfp.w_zero hfp.continuousOn_vL hfp.continuousOn_vR
    · filter_upwards [A2P1.ae_noncollision_simpleTrace hk hk4 hF hl hρ' (hadm s hF) hsum hpreL hpreR hE₀]
        with ω ⟨_, hnc, hgen, hinj, hH⟩
      exact ⟨hgen, hinj, hH, hnc⟩
  · unfold codeLaw restartSetS lawSetS
    refine measure_mono_null (fun f hf => ?_) measure_empty
    obtain ⟨y, ⟨-, hy⟩, hye⟩ := hf
    simp only [Prod.mk.injEq] at hye
    exact hy (Or.inl (show ¬ (startOf y).1 (Fin.last j) < 0 by rw [hye.1]; exact hl))

end Good

end InteractingSLE.ZhanGT4.A2ImgEnd
