/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowNoReturnCmp
import InteractingSLE.Spec.Supplement.GW4Completion
import InteractingSLE.Spec.Theorem15Inputs

/-!
# A centred counterflow does not return to its start, from the germ of its seeds

Packet PROVE-CFNORETURN (ruling R59). `Theorem14.GW4Ident.CounterflowNoReturnStatement` (PROVE-T14-GW4S) asks that a
centred counterflow with infinite lifetime never returns to its start at a positive time. In the chart `R` the
counterflow is an integrated `SLE_{κ'}(ρ)` evolution, `κ' = 16/κ`, of the flow-line word of a piecewise constant
boundary datum: a seed mark at `0⁻` and one at `0⁺` (kept even with weight `0`) and finitely many marks at nonzero
positions.

## The argument

Let `γ` be a continuous generating trace on `[0, ∞)` that vanishes at some positive time. If the returns do not
accumulate at `0` there is a first return `u > 0` (`γ` is continuous). At a first return one seed gap closes and the
corresponding side of `0` has not been visited (`first_return`, deterministic: `CounterflowNoReturnBack.lean`,
`CounterflowNoReturnFirst.lean`). Two cases for that side (say the right one, the left one is the reflection):

* **barrier seed** (total weight at `0⁺` at least `κ'/2 − 2`): at the first collision of the seed with the driver,
  every other mark is off the driver, so PROVE-CFBARRIER3's zero-side comparison picture holds at a rational restart
  time (`exists_genCmpPath_of_return_right`); it is null (`ae_forall_not_genCmpPath_right`) — R59's "the landed junction
  barrier applies";
* **hittable seed** (weight below `κ'/2 − 2`): the trace visits `(0, ∞)` at arbitrarily small times, so this side has
  been visited before `u` — R59's "0 is swallowed as soon as the counterflow touches" that side.

What remains probabilistic is the behaviour at time `0` only, recorded as the named input **`SeedGermStatement κ'`**
(the trace's germ: no returns at small positive times, and every hittable seed side visited at small times); the
reduction is `ae_trace_ne_zero_of_germ`, and `counterflowNoReturnStatement_of_seedGerm` gives the frozen-setting
statement. Both properties of the germ are those of the seed-only two-seed law (`SLE_{κ'}(ρ⁰_L; ρ⁰_R)`, the far marks are
at positive distance at time `0`), see PROVE-T14-GW4T4 §5.2 steps 1–2 and the handoff of this packet.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace CfNoReturn

open Sec5.CfJunction Sec5.CfLocalCmp

/-- The total weight of the right marks at the seed `0⁺`. -/
def seedWeightR {nR : ℕ} (xR ρR : Fin nR → ℝ) : ℝ := ∑ i ∈ univ.filter (fun i => xR i = 0), ρR i

/-- The total weight of the left marks at the seed `0⁻`. -/
def seedWeightL {nL : ℕ} (xL ρL : Fin nL → ℝ) : ℝ := ∑ i ∈ univ.filter (fun i => xL i = 0), ρL i

/-- **The germ property of a trace at its start** (parameter `κ`, seed weights `SL`, `SR`): for some `T > 0`, `γ` does
not vanish on `(0, T]`, and if the right (left) seed weight is below `κ/2 − 2`, the trace visits `(0, ∞)`
(`(−∞, 0)`) at some time `≤ T`. -/
def HasSeedGerm (κ SL SR : ℝ) (γ : ℝ≥0 → ℂ) : Prop :=
  ∃ T : ℝ≥0, 0 < T ∧ (∀ t : ℝ≥0, 0 < t → t ≤ T → γ t ≠ 0) ∧
    (SR < κ / 2 - 2 → ∃ s : ℝ≥0, s ≤ T ∧ ∃ x : ℝ, 0 < x ∧ γ s = x) ∧
    (SL < κ / 2 - 2 → ∃ s : ℝ≥0, s ≤ T ∧ ∃ x : ℝ, x < 0 ∧ γ s = x)

/-- **Named input: the germ of a seeded evolution at its start.** For every integrated `SLE_κ(ρ)` evolution of an
ordered word with infinite lifetime, almost surely every continuous generating trace on `[0, ∞)` has the germ property
`HasSeedGerm` for the seed weights of the word: no return to `0` at small positive times, and every side of `0` whose
seed weight is below `κ/2 − 2` is visited at small times. -/
def SeedGermStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞),
    IsOrderedForceWord xL xR → IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      (∀ᵐ ω ∂P, ζ ω = ⊤) →
        ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ →
          HasSeedGerm κ (seedWeightL xL ρL) (seedWeightR xR ρR) γ

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **No return to the start, from the germ** (every `κ > 0`): for an ordered word with a left and a right mark at
the seed and infinite lifetime, if almost surely every trace has the germ property, then almost surely no continuous
generating trace on `[0, ∞)` vanishes at a positive time. -/
theorem ae_trace_ne_zero_of_germ (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {k : Fin nR} (hk : xR k = 0) {l : Fin nL} (hl : xL l = 0)
    (hgerm : ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ →
      HasSeedGerm κ (seedWeightL xL ρL) (seedWeightR xR ρR) γ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  have hSRk : seedWeightR xR ρR = ∑ i ∈ univ.filter (fun i => xR i = xR k), ρR i := by
    rw [hk]; rfl
  have hSLl : seedWeightL xL ρL = ∑ i ∈ univ.filter (fun i => (-xL) i = (-xL) l), ρL i := by
    simp only [seedWeightL, Pi.neg_apply, neg_inj, hl]
  have hNR : ∀ᵐ ω ∂P, κ / 2 - 2 ≤ seedWeightR xR ρR → ∀ q : ℚ, ¬ GenCmpPath ρL ρR (zeroSideWeight xR ρR k)
      (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω) k (q : ℝ).toNNReal := by
    by_cases hS : κ / 2 - 2 ≤ seedWeightR xR ρR
    · filter_upwards [ae_forall_not_genCmpPath_right hκ hord hE hk (hSRk ▸ hS)] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hS
  have hNL : ∀ᵐ ω ∂P, κ / 2 - 2 ≤ seedWeightL xL ρL → ∀ q : ℚ, ¬ GenCmpPath ρR ρL (zeroSideWeight (-xL) ρL l)
      ((-W) · ω) (fun i t => (fun i => -VR i) i t ω) (fun j t => (fun i => -VL i) j t ω) (ζ ω) l
        (q : ℝ).toNNReal := by
    by_cases hS : κ / 2 - 2 ≤ seedWeightL xL ρL
    · filter_upwards [ae_forall_not_genCmpPath_right hκ (GB7a.isOrderedForceWord_reflect hord)
        (IsIntegratedSLEEvolution.reflect hE) (k := l) (by simp [hl]) (hSLl ▸ hS)] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hS
  filter_upwards [hgerm, hζ, hE.2.2.2.2, hNR, hNL] with ω hg hζω hp hNRω hNLω γ hγ t ht hγt
  rw [hζω] at hp hNRω hNLω
  obtain ⟨T, hT0, hnoret, hhitR, hhitL⟩ := hg γ hγ
  have hγc : Continuous γ :=
    continuousOn_univ.1 (hγ.2.1.mono fun s _ => show (s : ℝ≥0∞) ≤ ⊤ from le_top)
  set R : Set ℝ≥0 := {s | T ≤ s ∧ γ s = 0} with hRdef
  have hRc : IsClosed R := (isClosed_le continuous_const continuous_id).inter (isClosed_eq hγc continuous_const)
  have htR : t ∈ R := ⟨le_of_lt (lt_of_not_ge fun h => hnoret t ht h hγt), hγt⟩
  have huR : sInf R ∈ R := hRc.csInf_mem ⟨t, htR⟩ (OrderBot.bddBelow R)
  set u := sInf R with hudef
  have huT : T < u := lt_of_le_of_ne huR.1 fun h => hnoret T hT0 le_rfl (by rw [h]; exact huR.2)
  have hu0 : 0 < u := hT0.trans huT
  have hfirst : ∀ s : ℝ≥0, 0 < s → s < u → γ s ≠ 0 := fun s hs hsu hγs => by
    rcases le_or_gt s T with hsT | hsT
    · exact hnoret s hs hsT hγs
    · exact absurd (csInf_le (OrderBot.bddBelow R) ⟨hsT.le, hγs⟩) (not_le.2 hsu)
  rcases first_return hp hord hγ hk hl hu0 huR.2 hfirst with ⟨hvR, hoffR⟩ | ⟨hvL, hoffL⟩
  · by_cases hS : seedWeightR xR ρR < κ / 2 - 2
    · obtain ⟨s, hsT, x, hx, hsx⟩ := hhitR hS
      exact hoffR s (hsT.trans_lt huT) x hx hsx
    · obtain ⟨q, hq⟩ := exists_genCmpPath_of_return_right hp hord hγ hk hu0 huR.2 hfirst hvR hoffR
      exact hNRω (not_lt.1 hS) q hq
  · by_cases hS : seedWeightL xL ρL < κ / 2 - 2
    · obtain ⟨s, hsT, x, hx, hsx⟩ := hhitL hS
      exact hoffL s (hsT.trans_lt huT) x hx hsx
    · have hγR := LP.isGeneratingTrace_reflect hγ
      have hfirstR : ∀ s : ℝ≥0, 0 < s → s < u → LP.reflectC (γ s) ≠ 0 := fun s hs hsu he => by
        refine hfirst s hs hsu ?_
        have := congrArg LP.reflectC he
        rwa [LP.reflectC_reflectC, LP.reflectC_zero] at this
      have hoffR' : ∀ s : ℝ≥0, s < u → ∀ x : ℝ, 0 < x → LP.reflectC (γ s) ≠ x := fun s hs x hx he => by
        refine hoffL s hs (-x) (by linarith) ?_
        have := congrArg LP.reflectC he
        rwa [LP.reflectC_reflectC, LP.reflectC_ofReal] at this
      obtain ⟨q, hq⟩ := exists_genCmpPath_of_return_right hp.reflect (GB7a.isOrderedForceWord_reflect hord) hγR
        (k := l) (by simp [hl]) hu0 (by simp [huR.2]) hfirstR (by simp [hvL]) hoffR'
      exact hNLω (not_lt.1 hS) q hq

end Main

/-- **`CounterflowNoReturnStatement` from the germ input** at the counterflow parameters `κ' = 16/κ`, `0 < κ < 4`.
The flow-line word of the counterflow is ordered and has its seed marks `0⁻`, `0⁺` at index `0`. -/
theorem counterflowNoReturnStatement_of_seedGerm
    (hG : ∀ κ : ℝ, 0 < κ → κ < 4 → SeedGermStatement.{u} (16 / κ)) :
    Theorem14.GW4Ident.CounterflowNoReturnStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ Q _ h hh W ζ hcf hζ
  obtain ⟨b', J', h', -, -, h'', 𝓕, VL, VR, B, -, hC⟩ := hcf
  have hE := hC.1
  have hord := Theorem15.isOrderedForceWord_flowLine b' J' 0
  have hκ' : 0 < 16 / κ := by positivity
  exact ae_trace_ne_zero_of_germ hκ' hord hE hζ (k := ⟨0, by unfold flowLineNR; omega⟩) rfl
    (l := ⟨0, by unfold flowLineNL; omega⟩) rfl (hG κ hκ hκ4 _ _ _ _ Q 𝓕 W VL VR B ζ hord hE hζ)

end CfNoReturn

end InteractingSLE
