/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.KernelFlow
import InteractingSLE.Frozen.Spec.IsFlowLineDriver

/-!
# The general restart kernel: driven continuations (counterflows and other drivers)

Packet PROVE-RESTARTKERNEL. The companion of `KernelFlow.lean` for restart carriers whose continuation coordinate is
a **driving process** rather than a trace: GB6's conditional counterflow (`Supp8.GB6.IsGB6ConditionalCounterflow`,
the frozen `IsFlowLineDriver` at `16/κ`), the counterflow restarts of §5, and any carrier stated with
`IsFlowLineDriver`.

* `IsDriverCodeMatch p W L`: the driver `W` with lifetime `L` agrees with the code `p` (a value at every dyadic time
  and a lifetime) at time `0` and at every dyadic time before `L`; with continuity of `W` on `[0, L)` this
  determines `W` there.
  (No left limit at the lifetime is needed: drivers are matched only before it.)
* **`IsDriverCode κ θ F`**: `F` is a Borel *canonical driver code*: from a word `c` and a field `f` it returns a driver
  code such that, on every probability space, for every GFF `h` with the data of `c`, every measurable driver `W`
  continuous before its lifetime `L` and almost surely matching the code of `F (c, h)` drives the angle-`θ` flow line
  from `0` of `h` (frozen `IsFlowLineDriver`, any `κ > 0`). `DriverCodeStatement`: such codes exist (Theorem 1.2 —
  the driving history is a Borel function of the field, `Exist.exists_fieldDetermination` — realized on any space).
* **`ae_isFlowLineDriver_of_codeMatch`**: for every kernel `K` disintegrating `(β, X)` on `M`, (R1) under `K` and
  the almost sure match (Det) of the driver coordinate of `X` with the canonical driver code of the chart field give,
  for almost every datum `c`, that the driver coordinate drives the flow line of the chart field under `K c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open LQGMetric Sec2.Assembly

/-! ### Matching a driver code -/

/-- The driver `W` with lifetime `L` matches the code `p`: the lifetimes agree, `W` takes the coded value `p.1 0 0`
at time `0` (also when `L = 0`), and the coded values at the dyadic times before `L`. -/
def IsDriverCodeMatch (p : PCode × ℝ≥0∞) (W : ℝ≥0 → ℝ) (L : ℝ≥0∞) : Prop :=
  L = p.2 ∧ W 0 = p.1 0 0 ∧ ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < L → W (dyad n k) = p.1 n k

theorem measurableSet_driverCodeMatch {C S : Type*} [MeasurableSpace C] [MeasurableSpace S]
    {G : C × S → PCode × ℝ≥0∞} (hG : Measurable G) {WC : ℝ≥0 → S → ℝ} (hWC : ∀ t, Measurable (WC t))
    {L : S → ℝ≥0∞} (hL : Measurable L) :
    MeasurableSet {p : C × S | IsDriverCodeMatch (G p) (fun t => WC t p.2) (L p.2)} := by
  have hL' : Measurable fun p : C × S => L p.2 := hL.comp measurable_snd
  have hl : MeasurableSet {p : C × S | L p.2 = (G p).2} :=
    measurableSet_eq_fun hL' (measurable_snd.comp hG)
  have hcode : ∀ n k : ℕ, Measurable fun p : C × S => (G p).1 n k := fun n k =>
    (measurable_pi_apply k).comp ((measurable_pi_apply n).comp (measurable_fst.comp hG))
  have h0 : MeasurableSet {p : C × S | WC 0 p.2 = (G p).1 0 0} :=
    measurableSet_eq_fun ((hWC 0).comp measurable_snd) (hcode 0 0)
  have hd : ∀ n k : ℕ, MeasurableSet {p : C × S | (dyad n k : ℝ≥0∞) < L p.2 →
      WC (dyad n k) p.2 = (G p).1 n k} := fun n k => by
    have h1 : MeasurableSet {p : C × S | (dyad n k : ℝ≥0∞) < L p.2} := measurableSet_lt measurable_const hL'
    have h2 : MeasurableSet {p : C × S | WC (dyad n k) p.2 = (G p).1 n k} :=
      measurableSet_eq_fun ((hWC _).comp measurable_snd) (hcode n k)
    have e : {p : C × S | (dyad n k : ℝ≥0∞) < L p.2 → WC (dyad n k) p.2 = (G p).1 n k} =
        {p : C × S | (dyad n k : ℝ≥0∞) < L p.2}ᶜ ∪ {p : C × S | WC (dyad n k) p.2 = (G p).1 n k} := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    exact h1.compl.union h2
  have e : {p : C × S | IsDriverCodeMatch (G p) (fun t => WC t p.2) (L p.2)} =
      {p : C × S | L p.2 = (G p).2} ∩ {p : C × S | WC 0 p.2 = (G p).1 0 0} ∩ ⋂ n : ℕ, ⋂ k : ℕ,
        {p : C × S | (dyad n k : ℝ≥0∞) < L p.2 → WC (dyad n k) p.2 = (G p).1 n k} := by
    ext p
    simp only [IsDriverCodeMatch, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [e]
  exact (hl.inter h0).inter (MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => hd n k)

/-! ### Canonical driver codes -/

/-- **A Borel canonical driver code for the angle `θ`** (determination of the driving process by the field,
Theorem 1.2, realized on every space). `F` is jointly measurable in the word `c` and the field, and for every sorted
word `c`, on every probability space, every GFF `h` with the data of `c` and every measurable driver `W`, continuous
before its lifetime `L`, that almost surely matches the code `F (c, h)`: `W` with lifetime `L` drives the angle-`θ`
flow line from `0` of `h` (frozen `IsFlowLineDriver`). -/
def IsDriverCode (κ θ : ℝ) (F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞) : Prop :=
  Measurable F ∧ ∀ c : BoundaryWord, c.IsSorted →
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞),
      IsGFFWithBoundaryData Q h c.fn c.jumps → (∀ t, Measurable (W t)) →
      (∀ ω, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < L ω}) →
      (∀ᵐ ω ∂Q, IsDriverCodeMatch (F (c, h ω)) (fun t => W t ω) (L ω)) →
      IsFlowLineDriver κ c.fn c.jumps θ Q h W L

/-- **Named input: canonical driver codes exist** for every angle and every `κ > 0` (Theorem 1.2: the driving history
of every optional hull coupling is a Borel function of the field, jointly in the word —
`Exist.Staged.Theorem12ParamStatement`, `Exist.exists_fieldDetermination`; realized on any space carrying a GFF
with the same data, as in `Exist.exists_isFlowLine_of_thm12_thm13`; null modifications of the driver and lifetime
by `IsOptionalHullCoupling.congr_ae`). **Not proved in Lean.** -/
def DriverCodeStatement : Prop :=
  ∀ κ θ : ℝ, 0 < κ → ∃ F, IsDriverCode κ θ F

/-! ### The driver under a disintegrating kernel -/

/-- **The driver coordinate drives the flow line of the chart field under almost every kernel measure.** Let `K`
disintegrate the restart variable `X` over the datum `β` on `M`; suppose (R1) under `K` (for almost every `c` the word
`w c` is sorted and `H` is a GFF with it under `K c`) and that almost surely on `M` the driver coordinate `WC` of `X`,
continuous before the lifetime coordinate `L` at every point of `S`, matches the canonical driver code of the chart
field ((Det)). Then for almost every datum `c`, under `K c`, `WC` with lifetime `L` drives the angle-`θ` flow line
from `0` of `H` with the word `w c`. -/
theorem ae_isFlowLineDriver_of_codeMatch {Ω : Type*} {C S : Type} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSpace S] {P : Measure Ω} [IsFiniteMeasure P] {M : Set Ω} (hM : MeasurableSet M) {β : Ω → C}
    {X : Ω → S} (hβ : Measurable β) (hX : Measurable X) {K : Kernel C S} [IsMarkovKernel K]
    (hlaw : (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K)
    {w : C → BoundaryWord} (hw : Measurable w) {H : S → DistOn upperHalfPlaneOpens} (hH : Measurable H)
    {WC : ℝ≥0 → S → ℝ} (hWC : ∀ t, Measurable (WC t)) {L : S → ℝ≥0∞} (hL : Measurable L)
    (hWCc : ∀ s, ContinuousOn (fun t => WC t s) {t | (t : ℝ≥0∞) < L s}) {κ θ : ℝ}
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsDriverCode κ θ F)
    (hgff : ∀ᵐ c ∂(P.restrict M).map β,
      (w c).IsSorted ∧ IsGFFWithBoundaryData (K c) H (w c).fn (w c).jumps)
    (hdet : ∀ᵐ ω ∂P, ω ∈ M → IsDriverCodeMatch (F (w (β ω), H (X ω))) (fun t => WC t (X ω)) (L (X ω))) :
    ∀ᵐ c ∂(P.restrict M).map β, IsFlowLineDriver κ (w c).fn (w c).jumps θ (K c) H WC L := by
  set G : C × S → PCode × ℝ≥0∞ := fun p => F (w p.1, H p.2) with hGdef
  have hGm : Measurable G := hF.1.comp ((hw.comp measurable_fst).prodMk (hH.comp measurable_snd))
  have hE := measurableSet_driverCodeMatch hGm hWC hL
  have hK := ae_ae_of_map_eq_compProd hM hβ hX hlaw hE (by
    filter_upwards [hdet] with ω hω hωM
    exact hω hωM)
  filter_upwards [hK, hgff] with c hc ⟨hcs, hcg⟩
  exact hF.2 (w c) hcs (K c) H WC L hcg hWC hWCc hc

end Restart

end InteractingSLE
