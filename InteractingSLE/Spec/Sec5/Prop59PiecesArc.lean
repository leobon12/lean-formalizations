/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesMeas
import InteractingSLE.Spec.Sec5.Prop59SystemStage

/-!
# The piece of a killed arc after its start, and its regularity

Packet PROVE-PROP59-PIECES. Specification §5.2, proof of Proposition 5.9 (p. 144): "The trajectory is used only
before its first new contact with the conditional domain boundary"; Astra's follow-up 4, §3.4 (ruling R71): the
conditional word is identified at own stopping times "strictly before the continuation threshold and the first new
boundary contact".

A candidate piece of the alternating construction (PROVE-PROP59T4's `Piece`) is read through a killed arc `γ ω` on
its pre-contact times `P ω`, in the joint chart, from the chart capacity `S₀ ω` of its start (the last switch) on,
on the event `A` that the candidate is alive:

* `arcW`: the relative driver `W(S₀ + u) − W(S₀)` of the killed chain (`kW`), before the terminal capacity;
* `arcζ`: the lifetime `kLife − S₀` (the first new contact), `0` off `A`;
* `arcVL`, `arcVR`: the geometric images (`MartChar.RealFlow.rightImg`, reflected on the left) of the initial
  relative marks `xL`, `xR` under the relative driver, killed at the lifetime;
* `arcClk`: the compressed original clock `absClock (S₀ + ·)` (`Prop59PiecesClock`), the identity off `A`;
* `arcPiece`: the candidate piece, with a given noise `B`.

## Main results

* `isLocCont_realPath`, `continuousOn_rightImg_realPath`: images under a driver continuous before a lifetime are
  continuous before it;
* **`isRegPiece_arcPiece`**: the piece of a measurable family of killed arcs with a measurable start, alive event and
  initial marks is regular (`Prop59System.IsRegPiece`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

open WangWu WangWu.ImgWord CrossRestart MartChar.RealFlow Prop59System Prop59Stage
open Sec7.Lemma71C (capClock)

/-! ### Images under a driver continuous before a lifetime -/

section Images

variable {Ω : Type*}

/-- A driver continuous before `L` is locally continuous before `L`. -/
theorem isLocCont_realPath {X : ℝ≥0 → Ω → ℝ} {L : ℝ≥0∞} {ω : Ω}
    (hc : ContinuousOn (X · ω) {u | (u : ℝ≥0∞) < L}) : IsLocCont (Bessel.realPath X ω) L := by
  intro t ht
  have ht' : (t : ℝ≥0∞) < L := ht
  obtain ⟨c, htc, hcL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht'
  refine ⟨c, NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 htc), fun r => X (min r.toNNReal c) ω, ?_, ?_⟩
  · refine (hc.comp_continuous ((continuous_real_toNNReal).min continuous_const) fun r => ?_)
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hcL
  · intro r hr
    have hrc : r.toNNReal ≤ c := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp only [Bessel.realPath, min_eq_left hrc]

/-- The image of a right mark under a driver continuous before `L` is continuous before `L`. -/
theorem continuousOn_rightImg_realPath {X : ℝ≥0 → Ω → ℝ} {L : ℝ≥0∞} {ω : Ω}
    (hc : ContinuousOn (X · ω) {u | (u : ℝ≥0∞) < L}) (x : ℝ) :
    ContinuousOn (fun u : ℝ≥0 => rightImg (Bessel.realPath X ω) x u) {u | (u : ℝ≥0∞) < L} :=
  (isLocCont_realPath hc).continuousOn_kImg x

end Images

/-! ### The piece of a killed arc after its start -/

section Piece

variable {Ω : Type*} {nL nR : ℕ}

/-- The relative driver after the start `S₀` (before the terminal capacity, on the alive event). -/
def arcW (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) (A : Set Ω) : ℝ≥0 → Ω → ℝ :=
  open scoped Classical in
  fun u ω => if ω ∈ A ∧ ((S₀ ω + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) then
    kW (γ ω) (P ω) (S₀ ω + u) - kW (γ ω) (P ω) (S₀ ω) else 0

/-- The lifetime of the piece: the terminal capacity after the start (the first new contact), `0` off `A`. -/
def arcζ (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) (A : Set Ω) : Ω → ℝ≥0∞ :=
  open scoped Classical in
  fun ω => if ω ∈ A then lifeE (γ ω) (P ω) - S₀ ω else 0

/-- The right marks: the images of `xR` under the relative driver, killed at the lifetime. -/
def arcVR (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) (A : Set Ω) (xR : Ω → Fin nR → ℝ) :
    Fin nR → ℝ≥0 → Ω → ℝ :=
  fun k u ω => if (u : ℝ≥0∞) < arcζ γ P S₀ A ω then
    rightImg (Bessel.realPath (arcW γ P S₀ A) ω) (xR ω k) u else 0

/-- The left marks: the reflected images of `xL` under the relative driver, killed at the lifetime. -/
def arcVL (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) (A : Set Ω) (xL : Ω → Fin nL → ℝ) :
    Fin nL → ℝ≥0 → Ω → ℝ :=
  fun i u ω => if (u : ℝ≥0∞) < arcζ γ P S₀ A ω then
    -rightImg (Bessel.realPath (fun u ω => -arcW γ P S₀ A u ω) ω) (-xL ω i) u else 0

/-- The compressed original clock after the start (the identity off `A`). -/
def arcClk (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) (A : Set Ω) : Ω → ℝ≥0 → ℝ≥0 :=
  open scoped Classical in
  fun ω s => if ω ∈ A then absClock (γ ω) (P ω) (S₀ ω + s) else s

/-- **The candidate piece of a killed arc after its start.** -/
def arcPiece (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) (A : Set Ω) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (B : ℝ≥0 → Ω → ℝ) : Piece Ω nL nR where
  W := arcW γ P S₀ A
  VL := arcVL γ P S₀ A xL
  VR := arcVR γ P S₀ A xR
  B := B
  ζ := arcζ γ P S₀ A
  clk := arcClk γ P S₀ A

variable {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0} {A : Set Ω}

theorem lt_arcζ_iff {u : ℝ≥0} {ω : Ω} :
    (u : ℝ≥0∞) < arcζ γ P S₀ A ω ↔ ω ∈ A ∧ ((S₀ ω + u : ℝ≥0) : WithTop ℝ≥0) < kLife (γ ω) (P ω) := by
  classical
  by_cases hA : ω ∈ A
  · simp only [arcζ, hA, ↓reduceIte, true_and]
    rw [lt_tsub_iff_left]
    exact Iff.rfl
  · simp only [arcζ, hA, ↓reduceIte, false_and, iff_false, not_lt]
    exact zero_le

theorem arcW_of_lt {u : ℝ≥0} {ω : Ω} (h : (u : ℝ≥0∞) < arcζ γ P S₀ A ω) :
    arcW γ P S₀ A u ω = kW (γ ω) (P ω) (S₀ ω + u) - kW (γ ω) (P ω) (S₀ ω) := by
  classical
  simp only [arcW, lt_arcζ_iff.1 h, and_self, ↓reduceIte]

theorem continuousOn_arcW (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (ω : Ω) :
    ContinuousOn (arcW γ P S₀ A · ω) {u | (u : ℝ≥0∞) < arcζ γ P S₀ A ω} := by
  have hk := (hγ ω).continuousOn_kW
  have h1 : ContinuousOn (fun u : ℝ≥0 => kW (γ ω) (P ω) (S₀ ω + u) - kW (γ ω) (P ω) (S₀ ω))
      {u | (u : ℝ≥0∞) < arcζ γ P S₀ A ω} :=
    (hk.comp (continuous_const.add continuous_id : Continuous fun u : ℝ≥0 => S₀ ω + u).continuousOn
      fun u hu => (lt_arcζ_iff.1 hu).2).sub continuousOn_const
  exact h1.congr fun u hu => arcW_of_lt hu

section Meas

variable [MeasurableSpace Ω]

theorem measurable_arcζ (hF : IsKilledFamily γ P) (hS₀ : Measurable S₀) (hA : MeasurableSet A) :
    Measurable (arcζ γ P S₀ A) := by
  classical
  exact Measurable.ite hA (hF.measurable_kLife.sub (measurable_coe_nnreal_ennreal.comp hS₀)) measurable_const

theorem measurable_uncurry_arcW (hF : IsKilledFamily γ P) (hS₀ : Measurable S₀) (hA : MeasurableSet A) :
    Measurable (Function.uncurry (arcW γ P S₀ A)) := by
  classical
  have hK := hF.measurable_uncurry_kW
  have h1 : Measurable fun p : ℝ≥0 × Ω => kW (γ p.2) (P p.2) (S₀ p.2 + p.1) :=
    hK.comp ((hS₀.comp measurable_snd).add measurable_fst |>.prodMk measurable_snd)
  have h2 : Measurable fun p : ℝ≥0 × Ω => kW (γ p.2) (P p.2) (S₀ p.2) :=
    hK.comp ((hS₀.comp measurable_snd).prodMk measurable_snd)
  have hset : MeasurableSet {p : ℝ≥0 × Ω | p.2 ∈ A ∧
      ((S₀ p.2 + p.1 : ℝ≥0) : WithTop ℝ≥0) < kLife (γ p.2) (P p.2)} := by
    refine (measurable_snd hA).inter ?_
    have : Measurable fun p : ℝ≥0 × Ω => ((S₀ p.2 + p.1 : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp ((hS₀.comp measurable_snd).add measurable_fst)
    exact measurableSet_lt this (hF.measurable_kLife.comp measurable_snd)
  exact Measurable.ite hset (h1.sub h2) measurable_const

theorem measurable_arcW (hF : IsKilledFamily γ P) (hS₀ : Measurable S₀) (hA : MeasurableSet A) (u : ℝ≥0) :
    Measurable (arcW γ P S₀ A u) :=
  (measurable_uncurry_arcW hF hS₀ hA).comp (measurable_const.prodMk measurable_id)

theorem measurable_uncurry_arcVR (hF : IsKilledFamily γ P) (hS₀ : Measurable S₀) (hA : MeasurableSet A)
    {xR : Ω → Fin nR → ℝ} (hx : Measurable xR) (k : Fin nR) :
    Measurable (Function.uncurry (arcVR γ P S₀ A xR k)) := by
  refine measurable_uncurry_killed (f := fun u ω => rightImg (Bessel.realPath (arcW γ P S₀ A) ω) (xR ω k) u)
    (L := arcζ γ P S₀ A) (fun u => ?_) fun ω => continuousOn_rightImg_realPath (continuousOn_arcW hF.arc ω) _
  exact measurable_killedRightImg (measurable_arcW hF hS₀ hA) (fun ω => continuousOn_arcW hF.arc ω)
    (measurable_arcζ hF hS₀ hA) ((measurable_pi_apply k).comp hx) u

theorem measurable_uncurry_arcVL (hF : IsKilledFamily γ P) (hS₀ : Measurable S₀) (hA : MeasurableSet A)
    {xL : Ω → Fin nL → ℝ} (hx : Measurable xL) (i : Fin nL) :
    Measurable (Function.uncurry (arcVL γ P S₀ A xL i)) := by
  have hcn : ∀ ω, ContinuousOn ((fun u ω => -arcW γ P S₀ A u ω) · ω) {u | (u : ℝ≥0∞) < arcζ γ P S₀ A ω} :=
    fun ω => (continuousOn_arcW hF.arc ω).neg
  have h := measurable_uncurry_killed
    (f := fun u ω => rightImg (Bessel.realPath (fun u ω => -arcW γ P S₀ A u ω) ω) (-xL ω i) u)
    (L := arcζ γ P S₀ A) (fun u => measurable_killedRightImg (X := fun u ω => -arcW γ P S₀ A u ω)
      (fun u => (measurable_arcW hF hS₀ hA u).neg) hcn
      (measurable_arcζ hF hS₀ hA) ((measurable_pi_apply i).comp hx).neg u)
    fun ω => continuousOn_rightImg_realPath (X := fun u ω => -arcW γ P S₀ A u ω) (ω := ω) (hcn ω) _
  have e : Function.uncurry (arcVL γ P S₀ A xL i) = fun p => -(Function.uncurry fun (u : ℝ≥0) ω =>
      if (u : ℝ≥0∞) < arcζ γ P S₀ A ω then
        rightImg (Bessel.realPath (fun u ω => -arcW γ P S₀ A u ω) ω) (-xL ω i) u else 0) p := by
    funext p
    simp only [Function.uncurry, arcVL]
    split_ifs <;> simp
  rw [e]
  exact h.neg

theorem measurable_arcClk (hF : IsKilledFamily γ P) (hS₀ : Measurable S₀) (hA : MeasurableSet A) (s : ℝ≥0) :
    Measurable fun ω => arcClk γ P S₀ A ω s := by
  classical
  exact Measurable.ite hA (hF.measurable_uncurry_absClock.comp ((hS₀.add measurable_const).prodMk measurable_id))
    measurable_const

end Meas

theorem arcClk_of_mem {ω : Ω} (hA : ω ∈ A) :
    arcClk γ P S₀ A ω = fun s => absClock (γ ω) (P ω) (S₀ ω + s) := by
  unfold arcClk
  split_ifs
  rfl

theorem arcClk_of_notMem {ω : Ω} (hA : ω ∉ A) : arcClk γ P S₀ A ω = fun s => s := by
  unfold arcClk
  split_ifs
  rfl

theorem continuous_arcClk (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (ω : Ω) : Continuous (arcClk γ P S₀ A ω) := by
  by_cases hA : ω ∈ A
  · rw [arcClk_of_mem hA]
    exact (continuous_absClock (hγ ω)).comp (continuous_const.add continuous_id)
  · rw [arcClk_of_notMem hA]
    exact continuous_id

theorem strictMono_arcClk (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (ω : Ω) : StrictMono (arcClk γ P S₀ A ω) := by
  by_cases hA : ω ∈ A
  · rw [arcClk_of_mem hA]
    exact (strictMono_absClock (hγ ω)).comp fun a b hab => add_lt_add_right hab _
  · rw [arcClk_of_notMem hA]
    exact strictMono_id

/-- **The piece of a measurable family of killed arcs is regular.** -/
theorem isRegPiece_arcPiece [MeasurableSpace Ω] (hF : IsKilledFamily γ P) (hS₀ : Measurable S₀)
    (hA : MeasurableSet A) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable xL)
    (hxR : Measurable xR) (B : ℝ≥0 → Ω → ℝ) : IsRegPiece (arcPiece γ P S₀ A xL xR B) where
  W := measurable_uncurry_arcW hF hS₀ hA
  VL i := measurable_uncurry_arcVL hF hS₀ hA hxL i
  VR k := measurable_uncurry_arcVR hF hS₀ hA hxR k
  ζ := measurable_arcζ hF hS₀ hA
  clk s := measurable_arcClk hF hS₀ hA s
  clk_cont ω := continuous_arcClk hF.arc ω
  clk_mono ω := strictMono_arcClk hF.arc ω
  W_cont ω := continuousOn_arcW hF.arc ω
  VL_cont ω i := by
    show ContinuousOn (fun u => arcVL γ P S₀ A xL i u ω) {u | (u : ℝ≥0∞) < arcζ γ P S₀ A ω}
    have hcn : ContinuousOn ((fun u ω => -arcW γ P S₀ A u ω) · ω) {u | (u : ℝ≥0∞) < arcζ γ P S₀ A ω} :=
      (continuousOn_arcW hF.arc ω).neg
    refine ((continuousOn_rightImg_realPath (X := fun u ω => -arcW γ P S₀ A u ω) (ω := ω) hcn
      (-xL ω i)).neg).congr fun u hu => ?_
    have hu' : (u : ℝ≥0∞) < arcζ γ P S₀ A ω := hu
    simp only [arcVL, hu', ↓reduceIte, Pi.neg_apply]
  VR_cont ω k := by
    show ContinuousOn (fun u => arcVR γ P S₀ A xR k u ω) {u | (u : ℝ≥0∞) < arcζ γ P S₀ A ω}
    refine (continuousOn_rightImg_realPath (continuousOn_arcW hF.arc ω) (xR ω k)).congr fun u hu => ?_
    have hu' : (u : ℝ≥0∞) < arcζ γ P S₀ A ω := hu
    simp only [arcVR, hu', ↓reduceIte]

end Piece

end InteractingSLE.Sec5.Prop59Pieces
