/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.RestartLaw
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution_measure_killedState_eq
import InteractingSLE.Frozen.Spec.exists_isIntegratedSLEEvolution

/-!
# Theorem 2.2, the Markov sentence: the transition kernel of the full state

Packet PROVE-AF-MARKOV (external audit, item "Markov interface", priority 3). The landed restart law
`Sec2.Restart.measure_restart_killedState` gives, at a stopping time `T`, the conditional law of the
*increments* `(W_{T+·} − W_T, V_{T+·} − W_T, B_{T+·} − B_T)` as the canonical kernel `restartLaw` at the relative
word `V_T − W_T`. The paper's sentence is about the state `X = (W, V^L, V^R, B)` itself. This file builds the
kernel of that state.

* `relWord x = V − W` (the relative word of a state), `shiftState c y` (the translate of a state by
  `c = (w, b)`: the driver and the force points by `w`, the Brownian coordinate by `b`), `shiftSet`.
* `lawSetP`, `kerP`: the canonical killed-state law from a separated relative word, translated by a shift. The
  set is Borel by Lusin–Souslin, exactly as the landed `Sec2.Assembly.lawSetF` but with the shift as an extra
  parameter (the code is still determined by the start and the driving code, `injOn_startOf_fst`), so the kernel
  is measurable jointly in the shift and the word (`measurable_kerP`); `kerP_eq_restartLaw`: for a fixed shift it
  is the landed `restartLaw` of the translated sets.
* `shiftKer_eq`: on separated states it is the translated killed-state law of every evolution from the relative
  word (the landed `measure_killedState_eq_restartLaw`).
* `refLaw`, `refLaw_eq`: for an ordered relative word (separated or not, e.g. the entrance word `0⁻, 0⁺`) the
  translated killed-state law of a reference evolution (frozen Theorem 2.2 existence) is that of every evolution
  (frozen Theorem 2.2 uniqueness in law).
* `markovKer`: **the kernel `Q`** (`shiftKer` on separated states, `refLaw` elsewhere), with `markovKer_eq` (the law
  of every evolution started from the state, for every ordered relative word) and `measurable_markovKer_sep`
  (measurable on the separated states).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace AuditFix

namespace Markov

open Sec2 Sec2.Assembly Sec2.Restart

variable {nL nR : ℕ}

/-! ### States, relative words and translations -/

/-- The state `(W, V^L, V^R, B)` of an integrated evolution. -/
abbrev State (nL nR : ℕ) : Type := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ

/-- The relative force word of a state, seen from its driver: `V − W`. -/
def relWord (x : State nL nR) : (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (fun i => x.2.1 i - x.1, fun j => x.2.2.1 j - x.1)

theorem measurable_relWord : Measurable (relWord : State nL nR → (Fin nL → ℝ) × (Fin nR → ℝ)) :=
  (measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp measurable_snd.fst).sub measurable_fst).prodMk
    (measurable_pi_iff.2 fun j =>
      ((measurable_pi_apply j).comp measurable_snd.snd.fst).sub measurable_fst)

theorem relWord_shift (w b : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    relWord ((w, (fun i => w + xL i), (fun j => w + xR j), b) : State nL nR) = (xL, xR) :=
  Prod.ext (funext fun i => add_sub_cancel_left w (xL i))
    (funext fun j => add_sub_cancel_left w (xR j))

theorem relWord_zero (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    relWord (((0 : ℝ), xL, xR, (0 : ℝ)) : State nL nR) = (xL, xR) :=
  Prod.ext (funext fun i => sub_zero (xL i)) (funext fun j => sub_zero (xR j))

theorem sepStart_relWord_iff {x : State nL nR} : SepStart (relWord x) ↔ ∀ i j, x.2.1 i < x.2.2.1 j := by
  simp only [SepStart, relWord, sub_lt_sub_iff_right]

/-- The translate of a state `y` by `c = (w, b)`: the driver and the force points by `w`, the Brownian
coordinate by `b`. -/
def shiftState (c : ℝ × ℝ) (y : State nL nR) : State nL nR :=
  (c.1 + y.1, fun i => c.1 + y.2.1 i, fun j => c.1 + y.2.2.1 j, c.2 + y.2.2.2)

theorem measurable_shiftState :
    Measurable fun p : (ℝ × ℝ) × State nL nR => shiftState p.1 p.2 :=
  (measurable_fst.fst.add measurable_snd.fst).prodMk
    ((measurable_pi_iff.2 fun i =>
      measurable_fst.fst.add ((measurable_pi_apply i).comp measurable_snd.snd.fst)).prodMk
      ((measurable_pi_iff.2 fun j =>
        measurable_fst.fst.add ((measurable_pi_apply j).comp measurable_snd.snd.snd.fst)).prodMk
        (measurable_fst.snd.add measurable_snd.snd.snd.snd)))

/-- The states whose translate by `c` lies in `K`. -/
def shiftSet (c : ℝ × ℝ) (K : Set (State nL nR)) : Set (State nL nR) := shiftState c ⁻¹' K

theorem measurableSet_shiftSet (c : ℝ × ℝ) {K : Set (State nL nR)} (hK : MeasurableSet K) :
    MeasurableSet (shiftSet c K) :=
  (measurable_shiftState.comp (measurable_const.prodMk measurable_id)) hK

/-- The decoded full state of a solution code at time `t`. -/
def fullCodeState (y : XCode nL nR) (t : ℝ≥0) : State nL nR :=
  (cw y t, (fun i => cvL y i t), (fun j => cvR y j t), cb y t)

theorem measurable_fullCodeState (t : ℝ≥0) : Measurable fun y : XCode nL nR => fullCodeState y t :=
  (measurable_cw_at t).prodMk ((measurable_pi_iff.2 fun i => measurable_cvL_at i t).prodMk
    ((measurable_pi_iff.2 fun j => measurable_cvR_at j t).prodMk (measurable_cb_at t)))

/-! ### The translated canonical kernel -/

/-- Triples (shift `c`, separated start, driving code) whose canonical solution from the start, translated by
`c`, has its killed state at the times `ts` in the sets `K`. -/
def lawSetP (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (State nL nR)) :
    Set (((ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ))) × PCode) :=
  (fun p : (ℝ × ℝ) × XCode nL nR => ((p.1, startOf p.2), p.2.1)) ''
    {p | (p.2 ∈ CRelF a ρL ρR ∧ SepStart (startOf p.2)) ∧
      ∀ j, (ts j : ℝ≥0∞) < cζ p.2 ∧ shiftState p.1 (fullCodeState p.2 (ts j)) ∈ K j}

/-- **Lusin–Souslin**: the translated law set is Borel. -/
theorem measurableSet_lawSetP {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ}
    (ts : Fin n → ℝ≥0) {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    MeasurableSet (lawSetP a ρL ρR ts K) := by
  have : StandardBorelSpace ((ℝ × ℝ) × XCode nL nR) := StandardBorelSpace.prod
  -- the codomain is countably separated (the direct instance search times out)
  have : MeasurableSpace.CountablyGenerated
      (((ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ))) × PCode) := inferInstance
  have : MeasurableSpace.SeparatesPoints
      (((ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ))) × PCode) := inferInstance
  have : MeasurableSpace.CountablySeparated
      (((ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ))) × PCode) :=
    MeasurableSpace.countablySeparated_of_separatesPoints
  refine MeasurableSet.image_of_measurable_injOn ?_
    ((measurable_fst.prodMk (measurable_startOf.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)) ?_
  · refine (((measurableSet_cRelF a ρL ρR).preimage measurable_snd).inter
      ((measurable_startOf measurableSet_sepStart).preimage measurable_snd)).inter ?_
    refine measurableSet_setOfPred.2 (Measurable.forall fun j =>
      (measurable_coe_lt _ (measurable_cζ.comp measurable_snd)).and ?_)
    exact measurableSet_setOfPred.1 ((measurable_shiftState.comp (measurable_fst.prodMk
      ((measurable_fullCodeState (ts j)).comp measurable_snd))) (hK j))
  · rintro ⟨c, x⟩ ⟨⟨hx, hsx⟩, -⟩ ⟨c', x'⟩ ⟨⟨hx', -⟩, -⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨hc, hs⟩, h1⟩ := h
    have hsx' : SepStart (startOf x') := by
      have : SepStart (startOf x) := hsx
      rwa [hs] at this
    have := injOn_startOf_fst a ρL ρR ⟨hx, hsx⟩ ⟨hx', hsx'⟩ (Prod.ext hs h1)
    simp only at hc this
    rw [hc, this]

/-- **The translated canonical kernel**: the Wiener probability that the canonical solution from the separated
relative start `s`, translated by `c = (w, b)`, has its killed state at the times `ts` in `K`. -/
def kerP (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (State nL nR)) (p : (ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ))) : ℝ≥0∞ :=
  wienerPath {β | (p, enc β) ∈ lawSetP a ρL ρR ts K}

/-- The translated kernel is measurable jointly in the shift and the start. -/
theorem measurable_kerP {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ} (ts : Fin n → ℝ≥0)
    {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    Measurable (kerP a ρL ρR ts K) := by
  have hS : MeasurableSet {q : ((ℝ × ℝ) × ((Fin nL → ℝ) × (Fin nR → ℝ))) × (ℝ≥0 → ℝ) |
      (q.1, enc q.2) ∈ lawSetP a ρL ρR ts K} :=
    (measurable_fst.prodMk (measurable_enc.comp measurable_snd)) (measurableSet_lawSetP ts hK)
  exact measurable_measure_prodMk_left hS

/-- The sections of the translated law set are the landed law sets of the translated cylinders. -/
theorem mem_lawSetP_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (State nL nR)) (c : ℝ × ℝ) (s : (Fin nL → ℝ) × (Fin nR → ℝ)) (p : PCode) :
    ((c, s), p) ∈ lawSetP a ρL ρR ts K ↔
      (s, p) ∈ lawSetF a ρL ρR ts (fun j => shiftSet c (K j)) := by
  constructor
  · rintro ⟨⟨c', y⟩, ⟨⟨hy, hsy⟩, hyK⟩, hyx⟩
    simp only [Prod.mk.injEq] at hyx
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hyx
    exact ⟨y, ⟨⟨hy, hsy⟩, fun j => hyK j⟩, rfl⟩
  · rintro ⟨y, ⟨⟨hy, hsy⟩, hyK⟩, hyx⟩
    simp only [Prod.mk.injEq] at hyx
    obtain ⟨rfl, rfl⟩ := hyx
    exact ⟨(c, y), ⟨⟨hy, hsy⟩, fun j => hyK j⟩, rfl⟩

/-- For a fixed shift the translated kernel is the landed `restartLaw` of the translated cylinders. -/
theorem kerP_eq_restartLaw {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ}
    (ts : Fin n → ℝ≥0) (K : Fin n → Set (State nL nR)) (c : ℝ × ℝ)
    (s : (Fin nL → ℝ) × (Fin nR → ℝ)) :
    kerP a ρL ρR ts K (c, s) = restartLaw a ρL ρR ts (fun j => shiftSet c (K j)) s := by
  rw [kerP, restartLaw]
  congr 1
  ext β
  exact mem_lawSetP_iff ts K c s (enc β)

/-- The kernel of the full state on separated states: `kerP` at the shift `(W, B)` and the relative word of the
state. -/
def shiftKer (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (State nL nR)) (x : State nL nR) : ℝ≥0∞ :=
  kerP a ρL ρR ts K ((x.1, x.2.2.2), relWord x)

theorem measurable_shiftKer {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ}
    (ts : Fin n → ℝ≥0) {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    Measurable (shiftKer a ρL ρR ts K) :=
  (measurable_kerP ts hK).comp ((measurable_fst.prodMk measurable_snd.snd.snd).prodMk measurable_relWord)

/-- **On separated states the kernel is the translated killed-state law of every evolution** from the relative
word (the landed `measure_killedState_eq_restartLaw`). -/
theorem shiftKer_eq {a : ℝ} (ha : 0 < a) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {x : State nL nR}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hc : relWord x = (xL, xR)) (hsep : ∀ i j, xL i < xR j)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    shiftKer a ρL ρR ts K x = P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      shiftState (x.1, x.2.2.2) (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω),
        B (ts j) ω) ∈ K j} := by
  have := hE.1.isProbabilityMeasure'
  rw [shiftKer, hc, kerP_eq_restartLaw]
  exact (measure_killedState_eq_restartLaw ha hsep hE ts
    (fun j => measurableSet_shiftSet _ (hK j))).symm

/-! ### The law from an ordered word that is not separated -/

open Classical in
/-- The translated killed-state law of a reference evolution from the relative word of `x` (Theorem 2.2 gives
one for every ordered word, and its killed-state law is unique); `0` if there is none. -/
def refLaw (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (State nL nR)) (x : State nL nR) : ℝ≥0∞ :=
  if h : ∃ v : ℝ≥0∞, ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a (relWord x).1 (relWord x).2 ρL ρR P 𝓕 W VL VR B ζ ∧
      P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧ (W (ts j) ω, (fun i => VL i (ts j) ω),
        (fun i => VR i (ts j) ω), B (ts j) ω) ∈ shiftSet (x.1, x.2.2.2) (K j)} = v
  then Classical.choose h else 0

/-- **For an ordered relative word the reference law is the translated killed-state law of every evolution**
(frozen Theorem 2.2: existence and uniqueness in law). -/
theorem refLaw_eq {a : ℝ} (ha : 0 < a) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {x : State nL nR}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hc : relWord x = (xL, xR)) (hF : IsOrderedForceWord xL xR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    refLaw a ρL ρR ts K x = P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      shiftState (x.1, x.2.2.2) (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω),
        B (ts j) ω) ∈ K j} := by
  have := hE.1.isProbabilityMeasure'
  unfold refLaw
  split_ifs with h
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀, hv⟩ := Classical.choose_spec h
    rw [← hv]
    rw [hc] at hE₀
    exact IsIntegratedSLEEvolution.measure_killedState_eq ha hF hE₀ hE n ts _
      (fun j => measurableSet_shiftSet _ (hK j))
  · exfalso
    obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
      exists_isIntegratedSLEEvolution ha xL xR ρL ρR hF
    exact h ⟨_, Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, by rw [hc]; exact hE₀, rfl⟩

/-! ### The kernel `Q` of the full state -/

open Classical in
/-- **The kernel `Q` of the full state** `(W, V^L, V^R, B)`: at a state with separated force points the
measurable translated Wiener functional `shiftKer`, at the other states the reference law `refLaw`. -/
def markovKer (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (n : ℕ) (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (State nL nR)) (x : State nL nR) : ℝ≥0∞ :=
  if SepStart (relWord x) then shiftKer a ρL ρR ts K x else refLaw a ρL ρR ts K x

/-- **`Q` is the law of the process started from the state**: for a state `x` with ordered relative word
`(xL, xR)` and every integrated evolution from `(xL, xR)`, `Q(x)` is the probability that the evolution, translated
by the driver and Brownian coordinates of `x`, has its killed state at the times `ts` in `K`. -/
theorem markovKer_eq {a : ℝ} (ha : 0 < a) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {x : State nL nR}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hc : relWord x = (xL, xR)) (hF : IsOrderedForceWord xL xR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {n : ℕ} (ts : Fin n → ℝ≥0)
    {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    markovKer a ρL ρR n ts K x = P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
      shiftState (x.1, x.2.2.2) (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω),
        B (ts j) ω) ∈ K j} := by
  unfold markovKer
  split_ifs with hs
  · have hsep : ∀ i j, xL i < xR j := by
      intro i j
      have := hs i j
      rw [hc] at this
      exact this
    exact shiftKer_eq ha hc hsep hE ts hK
  · exact refLaw_eq ha hc hF hE ts hK

/-- On separated states `Q` is the translated canonical kernel. -/
theorem markovKer_of_sep {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ} (ts : Fin n → ℝ≥0)
    (K : Fin n → Set (State nL nR)) {x : State nL nR} (hx : SepStart (relWord x)) :
    markovKer a ρL ρR n ts K x = shiftKer a ρL ρR ts K x := by
  rw [markovKer, ite_eq_left hx]

/-- **`Q` is measurable on the states with separated force points.** -/
theorem measurable_markovKer_sep {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {n : ℕ}
    (ts : Fin n → ℝ≥0) {K : Fin n → Set (State nL nR)} (hK : ∀ j, MeasurableSet (K j)) :
    Measurable fun x : {x : State nL nR // ∀ i j, x.2.1 i < x.2.2.1 j} =>
      markovKer a ρL ρR n ts K x.1 := by
  have e : (fun x : {x : State nL nR // ∀ i j, x.2.1 i < x.2.2.1 j} =>
      markovKer a ρL ρR n ts K x.1) = fun x => shiftKer a ρL ρR ts K x.1 := by
    funext x
    exact markovKer_of_sep ts K (sepStart_relWord_iff.2 x.2)
  rw [e]
  exact (measurable_shiftKer ts hK).comp measurable_subtype_coe

end Markov

end AuditFix

end InteractingSLE
