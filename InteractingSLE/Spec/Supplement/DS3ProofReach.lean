/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS3

/-!
# DS2–DS3 in the inner-buffer (reach) form used by the near-extreme stages

Packet PROVE-T14-TIP7, ruling R53 (Astra's follow-up note A–E, `source/external/AstraIG1/ig1_followup_a_e_audited.txt`,
Part A.3, lines 118–173). The near-extreme stage compares the coordinate laws of the angle `θ` and of the exact
extreme angle `θ*` on the open event

  `U_{T,R,g} = {∃ t < T, e W_t > 17/8, sup_{u ≤ t} |W_u| ∨ max_i |V_i(u)| < R,`
  `             min_{i ∈ Far} inf_{u ≤ t} |V_i(u) − W_u| > g}`

("It is an open event in the uniform path topology: each witness `t` has strict positive margins on a compact
interval. Use the laws only before an outer buffer with bounds `T + 1, R + 1, g/2`. Every witness to `U_{T,R,g}` lies
strictly inside that buffer. This is the inner-buffer interpretation of DS2 on p. 553"). It is exactly the application
the proof of DS2 names (`source/spec/p529-576.md` L594: "For applications to a crossing event, select strict time,
driver and gap margins first; only the open event that the desired driver level is exceeded before those margins fail
is used").

The landed `DS2.DS2Statement`, `DS3.DS3Statement` (PROVE-T14-TIP2) concern sets of whole state paths on `[0, T]` that
stay in the far buffer and are alive through `T`; an event with a random witness time `t < T` after which the path may
leave the buffer or die is not of that form (it is a union over witness times, and a `liminf` inequality does not pass
to unions). This file states DS2 and DS3 for such **reach events**:

* `InBox R p`: every coordinate of the state `p = (W, V^L, V^R)` has absolute value `< R`;
* `reachEvent T O B`: some time `t < T` before the lifetime has its state in `O`, and every state on `[0, t]` is in `B`;
* `DS2ReachStatement`, `DS3ReachStatement`: DS2 and DS3 (same hypotheses as `DS2Statement`, `DS3Statement`) with the
  conclusion `P₀(reach) ≤ liminf P_m(reach)` for every open target `O` and every open inner buffer `B` (bounded
  coordinates and far gaps `> g`).

Proved here (the consumer side, A.3):

* `reachEvent_mono`: the event grows with the horizon, the target and the buffer;
* `eventually_lt_measure_reachEvent`: from the `liminf` inequality, a strict lower bound at the limiting word holds
  eventually along the sequence ("In particular a `θ ∈ Θ` sufficiently close to `θ*` has probability greater than
  `1 − ε/2`");
* `exists_seq_tendsto_half_pi`, `exists_seq_tendsto_neg_half_pi`: a dense `Θ ⊆ (−π/2, π/2)` contains sequences tending
  to the two extreme angles.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Finset Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2

section Events

variable {nL nR : ℕ}

/-- Every coordinate of the state `p = (W, V^L, V^R)` has absolute value `< R`. -/
def InBox (R : ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  |p.1| < R ∧ (∀ i, |p.2.1 i| < R) ∧ ∀ j, |p.2.2 j| < R

/-- The **inner buffer**: coordinates bounded by `R` and every far gap greater than `g`. -/
def InBuffer (mL mR : ℕ) (R g : ℝ) (p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  InBox R p ∧ InFarBuffer mL mR g p

/-- The **reach event** of a target `O` before the horizon `T` inside the buffer `B`: some time `t < T` before the
lifetime has its state in `O`, and every state on `[0, t]` lies in `B`. -/
def reachEvent {Ω : Type*} (T : ℝ≥0) (O B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Set Ω :=
  {ω | ∃ t : ℝ≥0, t < T ∧ (t : ℝ≥0∞) < ζ ω ∧ Coupling.stateAt W VL VR t ω ∈ O ∧
    ∀ u ≤ t, Coupling.stateAt W VL VR u ω ∈ B}

theorem reachEvent_mono {Ω : Type*} {T T' : ℝ≥0} {O O' B B' : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    (hT : T ≤ T') (hO : O ⊆ O') (hB : B ⊆ B') (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) :
    reachEvent T O B W VL VR ζ ⊆ reachEvent T' O' B' W VL VR ζ := by
  rintro ω ⟨t, htT, htζ, hO', hB'⟩
  exact ⟨t, htT.trans_le hT, htζ, hO hO', fun u hu => hB (hB' u hu)⟩

theorem inBox_mono {R R' : ℝ} (h : R ≤ R') {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hp : InBox R p) :
    InBox R' p :=
  ⟨hp.1.trans_le h, fun i => (hp.2.1 i).trans_le h, fun j => (hp.2.2 j).trans_le h⟩

theorem inFarBuffer_anti {mL mR : ℕ} {g g' : ℝ} (h : g' ≤ g) {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hp : InFarBuffer mL mR g p) : InFarBuffer mL mR g' p :=
  ⟨fun j hj => h.trans_lt (hp.1 j hj), fun i hi => h.trans_lt (hp.2 i hi)⟩

theorem inBuffer_mono {mL mR : ℕ} {R R' g g' : ℝ} (hR : R ≤ R') (hg : g' ≤ g)
    {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hp : InBuffer mL mR R g p) : InBuffer mL mR R' g' p :=
  ⟨inBox_mono hR hp.1, inFarBuffer_anti hg hp.2⟩

/-- The inner buffer is open. -/
theorem isOpen_setOf_inBuffer (mL mR : ℕ) (R g : ℝ) :
    IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR R g p} := by
  have h1 : IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | |p.1| < R} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have h2 : ∀ i, IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | |p.2.1 i| < R} := fun i =>
    isOpen_lt (continuous_abs.comp ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))
      continuous_const
  have h3 : ∀ j, IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | |p.2.2 j| < R} := fun j =>
    isOpen_lt (continuous_abs.comp ((continuous_apply j).comp (continuous_snd.comp continuous_snd)))
      continuous_const
  have h4 : ∀ j : Fin nR, IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | mR ≤ (j : ℕ) → g < p.2.2 j - p.1} :=
    fun j => by
      by_cases hj : mR ≤ (j : ℕ)
      · simp only [hj, true_implies]
        exact isOpen_lt continuous_const
          (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).sub continuous_fst)
      · simp only [hj, false_implies, ofPred_true, isOpen_univ]
  have h5 : ∀ i : Fin nL, IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | mL ≤ (i : ℕ) → g < p.1 - p.2.1 i} :=
    fun i => by
      by_cases hi : mL ≤ (i : ℕ)
      · simp only [hi, true_implies]
        exact isOpen_lt continuous_const
          (continuous_fst.sub ((continuous_apply i).comp (continuous_fst.comp continuous_snd)))
      · simp only [hi, false_implies, ofPred_true, isOpen_univ]
  have e : {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR R g p} =
      {p | |p.1| < R} ∩ (⋂ i, {p | |p.2.1 i| < R}) ∩ (⋂ j, {p | |p.2.2 j| < R}) ∩
        (⋂ j : Fin nR, {p | mR ≤ (j : ℕ) → g < p.2.2 j - p.1}) ∩
          ⋂ i : Fin nL, {p | mL ≤ (i : ℕ) → g < p.1 - p.2.1 i} := by
    ext p
    simp only [InBuffer, InBox, InFarBuffer, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    tauto
  rw [e]
  exact ((((h1.inter (isOpen_iInter_of_finite h2)).inter (isOpen_iInter_of_finite h3)).inter
    (isOpen_iInter_of_finite h4)).inter (isOpen_iInter_of_finite h5))

end Events

/-! ### The statements -/

/-- **Named statement: Lemma DS2, reach form** (p. 553, the inner-buffer interpretation; follow-up note A.3). The
hypotheses of `DS2Statement`; the conclusion: for every horizon `T`, every open target `O` of states and every open
inner buffer `B` (coordinates bounded by some `R`, far gaps `> g`),
`P₀(reach O before T inside B) ≤ liminf_m P_m(reach O before T inside B)`. -/
def DS2ReachStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) (mL mR : ℕ) (Rw ε a g η : ℝ),
    0 < ε → 0 < a → 0 < g → 0 < η →
    ∀ (xL : ℕ → Fin nL → ℝ) (xR : ℕ → Fin nR → ℝ) (ρL : ℕ → Fin nL → ℝ) (ρR : ℕ → Fin nR → ℝ)
      (xL₀ : Fin nL → ℝ) (xR₀ : Fin nR → ℝ) (ρL₀ : Fin nL → ℝ) (ρR₀ : Fin nR → ℝ),
      (∀ m, IsDS1Word mL mR Rw ε (xL m) (xR m) (ρL m) (ρR m)) → IsDS1Word mL mR Rw ε xL₀ xR₀ ρL₀ ρR₀ →
      (∀ m, a ≤ xR m ⟨0, hnR⟩ - xL m ⟨0, hnL⟩) → a ≤ xR₀ ⟨0, hnR⟩ - xL₀ ⟨0, hnL⟩ →
      Tendsto xL atTop (𝓝 xL₀) → Tendsto xR atTop (𝓝 xR₀) → Tendsto ρL atTop (𝓝 ρL₀) →
      Tendsto ρR atTop (𝓝 ρR₀) →
      (∀ m, SameGrouping (xL m) xL₀) → (∀ m, SameGrouping (xR m) xR₀) →
      (∀ m i i', xL m i ≠ xL m i' → η ≤ |xL m i - xL m i'|) →
      (∀ m j j', xR m j ≠ xR m j' → η ≤ |xR m j - xR m j'|) →
      ∀ (Ω : ℕ → Type u) [mΩ : ∀ m, MeasurableSpace (Ω m)] (P : ∀ m, Measure (Ω m))
        (𝓕 : ∀ m, Filtration ℝ≥0 (mΩ m)) (W : ∀ m, ℝ≥0 → Ω m → ℝ) (VL : ∀ m, Fin nL → ℝ≥0 → Ω m → ℝ)
        (VR : ∀ m, Fin nR → ℝ≥0 → Ω m → ℝ) (B : ∀ m, ℝ≥0 → Ω m → ℝ) (ζ : ∀ m, Ω m → ℝ≥0∞),
        (∀ m, IsIntegratedSLEEvolution κ (xL m) (xR m) (ρL m) (ρR m) (P m) (𝓕 m) (W m) (VL m) (VR m) (B m)
          (ζ m)) →
      ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀)
        (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ)
        (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL₀ xR₀ ρL₀ ρR₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ →
      ∀ (T : ℝ≥0) (R : ℝ) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))), IsOpen O → IsOpen Bf →
        (∀ p ∈ Bf, InBuffer mL mR R g p) →
        P₀ (reachEvent T O Bf W₀ VL₀ VR₀ ζ₀) ≤
          liminf (fun m => P m (reachEvent T O Bf (W m) (VL m) (VR m) (ζ m))) atTop

/-- **Named statement: Lemma DS3, reach form** (p. 554, with the inner-buffer interpretation of DS2; follow-up note
A.3: "These are exactly DS3's hypotheses with the prescribed far-gap cutoffs … DS3 and Portmanteau give
`lim inf_{θ → θ*} P_θ(U_{T,R,g}) ≥ P_{θ*}(U_{T,R,g})`"). The hypotheses of `DS3Statement` (fixed initial positions
with both nearest labels at the driver, the other labels `η`-separated from it, (DS1.1) uniform, weights converging);
the conclusion: for every horizon `T`, open target `O` and open inner buffer `B`,
`P₀(reach O before T inside B) ≤ liminf_m P_m(reach O before T inside B)`. -/
def DS3ReachStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) (mL mR : ℕ) (Rw ε g η : ℝ),
    0 < ε → 0 < g → 0 < η →
    ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : ℕ → Fin nL → ℝ) (ρR : ℕ → Fin nR → ℝ) (ρL₀ : Fin nL → ℝ)
      (ρR₀ : Fin nR → ℝ),
      xL ⟨0, hnL⟩ = 0 → xR ⟨0, hnR⟩ = 0 → (∀ i, xL i ≠ 0 → xL i ≤ -η) → (∀ j, xR j ≠ 0 → η ≤ xR j) →
      (∀ m, IsDS1Word mL mR Rw ε xL xR (ρL m) (ρR m)) → IsDS1Word mL mR Rw ε xL xR ρL₀ ρR₀ →
      Tendsto ρL atTop (𝓝 ρL₀) → Tendsto ρR atTop (𝓝 ρR₀) →
      ∀ (Ω : ℕ → Type u) [mΩ : ∀ m, MeasurableSpace (Ω m)] (P : ∀ m, Measure (Ω m))
        (𝓕 : ∀ m, Filtration ℝ≥0 (mΩ m)) (W : ∀ m, ℝ≥0 → Ω m → ℝ) (VL : ∀ m, Fin nL → ℝ≥0 → Ω m → ℝ)
        (VR : ∀ m, Fin nR → ℝ≥0 → Ω m → ℝ) (B : ∀ m, ℝ≥0 → Ω m → ℝ) (ζ : ∀ m, Ω m → ℝ≥0∞),
        (∀ m, IsIntegratedSLEEvolution κ xL xR (ρL m) (ρR m) (P m) (𝓕 m) (W m) (VL m) (VR m) (B m) (ζ m)) →
      ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀)
        (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ)
        (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL xR ρL₀ ρR₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ →
      ∀ (T : ℝ≥0) (R : ℝ) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))), IsOpen O → IsOpen Bf →
        (∀ p ∈ Bf, InBuffer mL mR R g p) →
        P₀ (reachEvent T O Bf W₀ VL₀ VR₀ ζ₀) ≤
          liminf (fun m => P m (reachEvent T O Bf (W m) (VL m) (VR m) (ζ m))) atTop

/-! ### The consumer side -/

/-- **A strict lower bound at the limit holds eventually** (the last step of A.3): if `p₀ ≤ liminf pₘ` and
`c < p₀`, then `c < pₘ` for all large `m`. -/
theorem eventually_lt_of_le_liminf {p : ℕ → ℝ≥0∞} {p₀ c : ℝ≥0∞} (h : p₀ ≤ liminf p atTop) (hc : c < p₀) :
    ∀ᶠ m in atTop, c < p m :=
  eventually_lt_of_lt_liminf (hc.trans_le h)

/-- **DS3 at a near-extreme word** (A.3): under the hypotheses of `DS3ReachStatement`, if the reach event has
probability `> c` at the limiting word, it has probability `> c` for all large `m`. -/
theorem eventually_lt_measure_reachEvent (hDS3 : DS3ReachStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    (hnL : 0 < nL) (hnR : 0 < nR) {mL mR : ℕ} {Rw ε g η : ℝ} (hε : 0 < ε) (hg : 0 < g) (hη : 0 < η)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : ℕ → Fin nL → ℝ} {ρR : ℕ → Fin nR → ℝ} {ρL₀ : Fin nL → ℝ}
    {ρR₀ : Fin nR → ℝ} (hxL0 : xL ⟨0, hnL⟩ = 0) (hxR0 : xR ⟨0, hnR⟩ = 0) (hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η)
    (hxR : ∀ j, xR j ≠ 0 → η ≤ xR j) (hw : ∀ m, IsDS1Word mL mR Rw ε xL xR (ρL m) (ρR m))
    (hw₀ : IsDS1Word mL mR Rw ε xL xR ρL₀ ρR₀) (hρL : Tendsto ρL atTop (𝓝 ρL₀))
    (hρR : Tendsto ρR atTop (𝓝 ρR₀)) {Ω : ℕ → Type u} [mΩ : ∀ m, MeasurableSpace (Ω m)]
    {P : ∀ m, Measure (Ω m)} {𝓕 : ∀ m, Filtration ℝ≥0 (mΩ m)} {W : ∀ m, ℝ≥0 → Ω m → ℝ}
    {VL : ∀ m, Fin nL → ℝ≥0 → Ω m → ℝ} {VR : ∀ m, Fin nR → ℝ≥0 → Ω m → ℝ} {B : ∀ m, ℝ≥0 → Ω m → ℝ}
    {ζ : ∀ m, Ω m → ℝ≥0∞}
    (hE : ∀ m, IsIntegratedSLEEvolution κ xL xR (ρL m) (ρR m) (P m) (𝓕 m) (W m) (VL m) (VR m) (B m) (ζ m))
    {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞} (hE₀ : IsIntegratedSLEEvolution κ xL xR ρL₀ ρR₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀)
    {T : ℝ≥0} {R : ℝ} {O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hO : IsOpen O) (hB : IsOpen Bf)
    (hBR : ∀ p ∈ Bf, InBuffer mL mR R g p) {c : ℝ≥0∞} (hc : c < P₀ (reachEvent T O Bf W₀ VL₀ VR₀ ζ₀)) :
    ∀ᶠ m in atTop, c < P m (reachEvent T O Bf (W m) (VL m) (VR m) (ζ m)) :=
  eventually_lt_of_le_liminf
    (hDS3 κ hκ hnL hnR mL mR Rw ε g η hε hg hη xL xR ρL ρR ρL₀ ρR₀ hxL0 hxR0 hxL hxR hw hw₀ hρL hρR Ω P 𝓕 W
      VL VR B ζ hE P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hE₀ T R O Bf hO hB hBR) hc

/-! ### Angles approaching the extremes -/

/-- A set dense in `(−π/2, π/2)` contains a sequence tending to `π/2`. -/
theorem exists_seq_tendsto_half_pi {Θ : Set ℝ} (hΘ : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ) :
    ∃ θ : ℕ → ℝ, (∀ n, θ n ∈ Θ) ∧ Tendsto θ atTop (𝓝 (Real.pi / 2)) := by
  have hcl : Real.pi / 2 ∈ closure Θ := by
    have h1 : Real.pi / 2 ∈ closure (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
      rw [closure_Ioo (by linarith [Real.pi_pos])]
      exact ⟨by linarith [Real.pi_pos], le_rfl⟩
    have h2 := closure_mono hΘ h1
    rwa [closure_closure] at h2
  obtain ⟨θ, hθ, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  exact ⟨θ, hθ, hlim⟩

/-- A set dense in `(−π/2, π/2)` contains a sequence tending to `−π/2`. -/
theorem exists_seq_tendsto_neg_half_pi {Θ : Set ℝ} (hΘ : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ) :
    ∃ θ : ℕ → ℝ, (∀ n, θ n ∈ Θ) ∧ Tendsto θ atTop (𝓝 (-(Real.pi / 2))) := by
  have hcl : -(Real.pi / 2) ∈ closure Θ := by
    have h1 : -(Real.pi / 2) ∈ closure (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
      rw [closure_Ioo (by linarith [Real.pi_pos])]
      exact ⟨le_rfl, by linarith [Real.pi_pos]⟩
    have h2 := closure_mono hΘ h1
    rwa [closure_closure] at h2
  obtain ⟨θ, hθ, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  exact ⟨θ, hθ, hlim⟩

end DSReach

end Supp12

end InteractingSLE
