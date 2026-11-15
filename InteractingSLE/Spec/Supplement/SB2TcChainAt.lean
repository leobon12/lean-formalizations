/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineIface

/-!
# SB2(1)'s chain record: one physical horizon forces a finite lifetime; the per-time record

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s version half; interface `Lv.SB2LineVersion` of PROVE-T14-SB2DRV).

**Finding.** The interface's chain record `Lv.IsSB2LineChain A u m c η ζ W a V` has ONE physical horizon `t_L + S`
(`S : ℝ`) and the clause `∀ t, a t < V → t < t_L + S`. Below the horizon the clock is `0` or the capacity clock of
the lift `γ`, which is bounded by its value at `S` (`capClock_mono_of_continuous`). Past the horizon the clock must be
at least `V`. So a continuous clock forces `V < ∞` (**`ne_top_of_le_before`**, **`IsSB2LineChain.ne_top`**). In
`SB2LineVersion`, the fields `link` and `life` give `Vg = thr = ∞` whenever the upper flow lives forever. Hence every
`SB2LineVersion` has a finite lifetime `ζ` almost surely on every seed cell (**`SB2LineVersion.ae_lifetime_ne_top`**).
A flow line that runs to `∞` with positive probability after its entrance therefore admits no `SB2LineVersion`, and
the named input `SB2LineVersionStatement` is false as stated.

**Proposed repair.** Use the record at one physical time: **`IsSB2LineChainAt … t`** keeps the clauses of
`IsSB2LineChain`, asks `t < t_L + S`, and drops the lifetime clause. The `chain` field would read
`∀ w ∈ I.types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell … → a t ω < thr … → IsSB2LineChainAt … t`. This is a weakening
(**`IsSB2LineChain.chainAt`**). The kernel half's `sb2LineGeomStatement` uses the record at one time `t` on the live
cell `{a t < thr}` only, so it goes through unchanged up to the position of the quantifier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Tc

open Lv Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 WalkInf
  Sec7.PocketTraversal Supp8.Q3Stop

/-! ### The capacity clock of a continuous curve is monotone -/

/-- **The capacity clock of a continuous curve from a real point is monotone.** -/
theorem capClock_mono_of_continuous {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (h0 : (γ 0).im = 0) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s ≤
      Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) t := by
  have hc : Continuous fun r : ℝ => γ r.toNNReal := hγ.comp continuous_real_toNNReal
  have h0' : ((fun r : ℝ => γ r.toNNReal) 0).im = 0 := by simpa using h0
  have hKs := YuanCharacterisation.isHPHull_fillH_image_of_im hc.continuousOn hs h0'
  have hKt := YuanCharacterisation.isHPHull_fillH_image_of_im hc.continuousOn (hs.trans hst) h0'
  unfold Sec7.Lemma71C.capClock
  rw [ConformalImage.hcapSet_eq hKs, ConformalImage.hcapSet_eq hKt]
  have := HPHull.hcap_mono (A := ⟨_, hKs⟩) (B := ⟨_, hKt⟩) (fillH_mono (image_mono (Icc_subset_Icc_right hst)))
  linarith

/-! ### One horizon forces a finite lifetime -/

/-- **A continuous clock bounded before a horizon cannot have an infinite lifetime reached only before it**
(generic): if `a` is continuous, `a t ≤ M < ∞` for `t < T₀` (`T₀ > 0`), and `a t < V → t < T₀`, then `V ≠ ∞`. -/
theorem ne_top_of_le_before {a : ℝ≥0 → ℝ≥0∞} (ha : Continuous a) {V : ℝ≥0∞} {T₀ : ℝ} (hT₀ : 0 < T₀) {M : ℝ≥0}
    (hle : ∀ t : ℝ≥0, (t : ℝ) < T₀ → a t ≤ M) (hV : ∀ t : ℝ≥0, a t < V → (t : ℝ) < T₀) : V ≠ ⊤ := by
  intro hVt
  set t₀ : ℝ≥0 := T₀.toNNReal with ht₀def
  have ht₀ : (t₀ : ℝ) = T₀ := Real.coe_toNNReal _ hT₀.le
  have htop : a t₀ = ⊤ := by
    by_contra hne
    have h1 := hV t₀ (hVt ▸ lt_top_iff_ne_top.2 hne)
    rw [ht₀] at h1
    exact lt_irrefl _ h1
  have hcl : IsClosed {t | a t ≤ M} := isClosed_le ha continuous_const
  have hsub : Iio t₀ ⊆ {t | a t ≤ M} := fun t ht => hle t (by rw [← ht₀]; exact_mod_cast ht)
  have hne : (Iio t₀).Nonempty := ⟨0, Real.toNNReal_pos.2 hT₀⟩
  have hmem : t₀ ∈ closure (Iio t₀) := by
    rw [closure_Iio' hne]
    exact Set.self_mem_Iic
  have h2 : a t₀ ≤ M := hcl.closure_subset_iff.2 hsub hmem
  rw [htop] at h2
  exact ENNReal.coe_ne_top (top_le_iff.1 h2)

/-- **One physical horizon forces a finite lifetime.** If the chain record holds with a continuous clock, the
lifetime `V` is finite. -/
theorem IsSB2LineChain.ne_top {A : Set ℂ} {u m : ℝ} {c : Chart} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {W : ℝ≥0 → ℝ}
    {a : ℝ≥0 → ℝ≥0∞} {V : ℝ≥0∞} (h : IsSB2LineChain A u m c η ζ W a V) (ha : Continuous a) : V ≠ ⊤ := by
  obtain ⟨p, g, β', γ, tL, S, Wr, ηr, w, ηw, -, -, ⟨-, -, -, -, -, hγ, hγ0, -⟩, -, ⟨hS, -, -⟩, -,
    ⟨-, ha0, hacap, haS⟩⟩ := h
  refine ne_top_of_le_before ha (by positivity) (M := (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) S).toNNReal)
    (fun t ht => ?_) haS
  rcases le_or_gt (t : ℝ) tL with htL | htL
  · rw [ha0 t htL]
    exact zero_le
  · rw [hacap t htL.le ht]
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal
      (capClock_mono_of_continuous hγ.1 (by rw [hγ0]; simp) (by linarith) (by linarith)))

/-- **The interface forces a finite lifetime on the seed cells**: for every `SB2LineVersion`, almost surely on every
seed cell, the upper flow's lifetime `ζ` is finite (`link` and `life` give `Vg = thr = ∞` when `ζ = ∞`;
`chain` with the continuous clock gives `thr < ∞`). -/
theorem SB2LineVersion.ae_lifetime_ne_top {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ}
    {I : K2LaunchInputs κ b jumps P h E k u ψ} {u₀ : ℂ → ℝ} {D : EntranceUnion κ b jumps P h E k u η ζ u₀}
    (Vd : SB2LineVersion HP I D) (w : WordType) (hw : w ∈ I.types) :
    ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w → ζ ω ≠ ⊤ := by
  filter_upwards [Vd.chain w hw, Vd.life w hw, Vd.link, D.ae_mem_event_iff] with ω hch hlife hlink hev hcell hζ
  have hevω : ω ∈ D.event := hcell.1.1
  have hl : ω ∈ launchSet κ b jumps E (k + 1) := D.event_subset hevω
  have hT := (hev hl).1 hevω
  have hthr := IsSB2LineChain.ne_top (hch hcell) (Vd.clock_cont ω)
  have hVg := hlife hl hT hcell.1
  obtain ⟨-, hrem⟩ := hlink hl hT
  obtain ⟨σ, -, -, -, hσ⟩ := hrem hT
  have htop : Vd.Vg ω = ⊤ := ENNReal.eq_top_of_forall_nnreal_le fun r =>
    ((hσ r).1.2 (by rw [hζ]; exact ENNReal.coe_lt_top)).le
  exact hthr (hVg ▸ htop)

/-! ### The per-time record (proposed repair) -/

/-- **The S2 chain record at one absolute physical time `t`** (the proposed repair of `IsSB2LineChain`): the same
clauses, with the physical horizon `t_L + S` beyond `t`, the driver and clock identifications below `V` and the
horizon, and no clause tying the lifetime to the horizon. -/
def IsSB2LineChainAt (A : Set ℂ) (u m : ℝ) (c : Chart) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (W : ℝ≥0 → ℝ)
    (a : ℝ≥0 → ℝ≥0∞) (V : ℝ≥0∞) (t : ℝ≥0) : Prop :=
  ∃ (p : ℝ → ℂ) (g : ℂ → ℂ) (β' γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (S : ℝ) (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (w : ℝ → ℝ)
    (ηw : ℝ → ℂ),
    (t : ℝ) < (tL : ℝ) + S ∧
    (ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
      (∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite) ∧ p '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A) ∧
    (IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) (Lw.shiftChart c u m) ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (Lw.shiftChart c u m).2.1 H ∧
      (∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) ∧ FinRel.LiftRealOn (Lw.shiftChart c u m)) ∧
    (Supp9B.IsProperCurve β' ∧ β' 0 = 0 ∧ p '' Icc 0 1 ⊆ Supp9B.closedRightSide β' ∧
      β' tL = realMin (p '' Icc 0 1) ∧ ((tL : ℝ≥0) : ℝ≥0∞) = firstVisit η ζ (realMin A) ∧
      Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ ∀ s, g (γ s) = β' (tL + s)) ∧
    (∀ t' : ℝ≥0, (t' : ℝ) < (tL : ℝ) + S → β' t' = η t' - u) ∧
    (0 < S ∧ (∀ S₀ : ℝ, 0 ≤ S₀ → S₀ < S → FinRel.IsSB2RelChain (p '' Icc 0 1) (Lw.shiftChart c u m) β' γ tL S₀ Wr ηr) ∧
      interior {r ∈ Ioo (0 : ℝ) S | β' (tL + r.toNNReal) ∈ {z : ℂ | z.im = 0}} = ∅) ∧
    (Continuous w ∧ w 0 = 0 ∧ IsLoewnerTrace w ηw ∧
      (∀ s : ℝ, 0 < s → s < S → fwdHull w ((tL : ℝ) + s) = fillH (β' '' Icc 0 (tL + s.toNNReal))) ∧
      ∀ r : ℝ, 0 ≤ r → r < (tL : ℝ) + S → ηw r = β' r.toNNReal) ∧
    ((∀ q : ℝ≥0, (q : ℝ≥0∞) < V → W q = Wr q) ∧
      (∀ t' : ℝ≥0, (t' : ℝ) ≤ tL → a t' = 0) ∧
      ∀ t' : ℝ≥0, (tL : ℝ) ≤ t' → (t' : ℝ) < tL + S →
        a t' = ((Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (t' - tL)).toNNReal : ℝ≥0∞))

/-- **The per-time record is a weakening**: the interface's record gives the per-time record at every live time. -/
theorem IsSB2LineChain.chainAt {A : Set ℂ} {u m : ℝ} {c : Chart} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {W : ℝ≥0 → ℝ}
    {a : ℝ≥0 → ℝ≥0∞} {V : ℝ≥0∞} (h : IsSB2LineChain A u m c η ζ W a V) {t : ℝ≥0} (ht : a t < V) :
    IsSB2LineChainAt A u m c η ζ W a V t := by
  obtain ⟨p, g, β', γ, tL, S, Wr, ηr, w, ηw, h1, h2, h3, h4, h5, h6, ⟨hW, ha0, ha, haS⟩⟩ := h
  exact ⟨p, g, β', γ, tL, S, Wr, ηr, w, ηw, haS t ht, h1, h2, h3, h4, h5, h6, hW, ha0, ha⟩

end InteractingSLE.Theorem14.SB.Tc
