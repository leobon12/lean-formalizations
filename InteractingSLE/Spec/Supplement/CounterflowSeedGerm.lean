/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowSeedGermTwoSeed
import InteractingSLE.Spec.Supplement.CounterflowSeedGermLocal
import InteractingSLE.Spec.Supplement.CounterflowNoReturn
import InteractingSLE.Spec.Sec7.FanTipFiber
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.WangWu.SideValues

/-!
# The counterflow's seed germ, and the counterflow does not return to its start

Packet PROVE-CFNORETURN2 (ruling R59; PROVE-CFNORETURN §5). PROVE-CFNORETURN reduced
`Theorem14.GW4Ident.CounterflowNoReturnStatement` to the germ of the trace at time `0`
(`CfNoReturn.HasSeedGerm`: no return to `0` at small positive times, and every seed side of weight below `κ'/2 − 2`
visited at small times). This file proves that germ for every ordered word with a mark at `0⁻` and a mark at `0⁺`
and infinite lifetime (`ae_hasSeedGerm_of_twoSeedComplete`, `κ' > 4`), from one input: **two-seed completeness**
(`LP.TwoSeedComplete κ'`: every two-seed word `SLE_{κ'}(r_L; r_R)`, `r_L, r_R > −2`, has a continuous transient trace),
which LP11's assembly takes from Theorem R.7, Lemma 7.25 and Proposition LP4 (`LP.isCompleteForceWord_twoSeed`). It
gives `CounterflowNoReturnStatement` for every admissible word (`counterflowNoReturnStatement_of_twoSeedComplete`,
`counterflowNoReturnStatement_of_inputs`).

## Route

1. **A germ property of the driving path** (`DriverGerm`): the Loewner tip `F̄_t(0)` does not vanish on `(0, T]`
   for some `T > 0`; for a hittable seed side, a point of that side is swallowed by every time `T > 0`. It only depends
   on the germ of the driving path at `0` (`driverGerm_congr`: `Sec7.loewnerTip_congr`, `LP4HB.isSwallowedBy_congr`),
   and it implies `HasSeedGerm` for every trace on `[0, ∞)` (`hasSeedGerm_of_driverGerm`: the tip is the trace; a
   swallowed `x > 0` gives a visit of `[x, ∞)` by `Sec7.Lemma76E.alive_of_trace_off`).
2. **The two-seed word** (`ae_driverGerm_twoSeed`, `CounterflowSeedGermTwoSeed.lean`): the swallowing clauses by
   LP18's positivity, scaling and Aux. lemma 128 (no input); the tip clause from two-seed completeness by scaling.
3. **Localization** (`Germ.ae_of_twoSeed`, `CounterflowSeedGermLocal.lean`): Theorem 2.2's Girsanov cover of the seed
   groups by the two-seed word transfers the germ property to every seeded word.
4. **Wiring**: `CfNoReturn.ae_trace_ne_zero_of_germ` (PROVE-CFNORETURN) and the frozen counterflow setting.

R48: nothing used takes Theorem 1.2/1.3, `Theorem12ParamStatement` or `Theorem13Statement` as a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace CfNoReturn

/-! ### The germ property of a driving path -/

/-- **The germ property of a driving path** (parameter `κ`, seed weights `SL`, `SR`): for some `T > 0` the Loewner tip
does not vanish on `(0, T]`, and if the right (left) seed weight is below `κ/2 − 2`, then for every `T > 0` some point
`x > 0` is swallowed by time `T` under the driver (under the reflected driver `−w`, i.e. the point `−x`). -/
def DriverGerm (κ SL SR : ℝ) (w : ℝ≥0 → ℝ) : Prop :=
  (∃ T : ℝ≥0, 0 < T ∧ ∀ t : ℝ≥0, 0 < t → t ≤ T → loewnerTip (fun s : ℝ => w s.toNNReal) t ≠ 0) ∧
    (SR < κ / 2 - 2 → ∀ T : ℝ≥0, 0 < T → ∃ x : ℝ, 0 < x ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T) ∧
    (SL < κ / 2 - 2 → ∀ T : ℝ≥0, 0 < T → ∃ x : ℝ, 0 < x ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => -w s.toNNReal) x T)

/-- **The germ property only depends on the germ of the driving path**: two continuous driving paths from `0` that
agree on an initial interval `[0, ε)` have the same germ property. -/
theorem driverGerm_congr {κ SL SR : ℝ} {w w' : ℝ≥0 → ℝ} (hw : Continuous w) (hw' : Continuous w')
    (hw0 : w 0 = 0) (hw'0 : w' 0 = 0) (hag : ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s : ℝ≥0, s < ε → w s = w' s)
    (h : DriverGerm κ SL SR w) : DriverGerm κ SL SR w' := by
  obtain ⟨ε, hε, hag⟩ := hag
  obtain ⟨⟨T, hT, hne⟩, hR, hL⟩ := h
  have hWc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hW'c : Continuous fun s : ℝ => w' s.toNNReal := hw'.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa using hw0
  have hW'0 : (fun s : ℝ => w' s.toNNReal) 0 = 0 := by simpa using hw'0
  -- agreement on `[0, t]` for `t < ε`
  have hEq : ∀ t : ℝ, t < ε → ∀ r ∈ Icc (0 : ℝ) t, w r.toNNReal = w' r.toNNReal := fun t ht r hr =>
    hag _ (by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr.1]; exact hr.2.trans_lt ht)
  set ε' : ℝ≥0 := ε / 2 with hε'def
  have hε' : 0 < ε' := by positivity
  have hε'ε : (ε' : ℝ) < ε := by
    rw [hε'def, NNReal.coe_div]
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    push_cast
    linarith
  have hlt : ∀ t : ℝ≥0, t ≤ ε' → (t : ℝ) < ε := fun t ht => lt_of_le_of_lt (by exact_mod_cast ht) hε'ε
  refine ⟨⟨min T ε', lt_min hT hε', fun t ht htT => ?_⟩, fun hS T' hT' => ?_, fun hS T' hT' => ?_⟩
  · rw [← Sec7.loewnerTip_congr hWc hW0 hW'c hW'0 t.coe_nonneg
      (fun r hr => hEq t (hlt t (htT.trans (min_le_right _ _))) r hr)]
    exact hne t ht (htT.trans (min_le_left _ _))
  · obtain ⟨x, hx, hs⟩ := hR hS (min T' ε') (lt_min hT' hε')
    refine ⟨x, hx, LP.LP4HB.isSwallowedBy_mono (min T' ε').coe_nonneg
      (by exact_mod_cast min_le_left T' ε') (LP.LP4HB.isSwallowedBy_congr (fun r hr => ?_) hs)⟩
    exact hEq _ (hlt _ (min_le_right _ _)) r hr
  · obtain ⟨x, hx, hs⟩ := hL hS (min T' ε') (lt_min hT' hε')
    refine ⟨x, hx, LP.LP4HB.isSwallowedBy_mono (min T' ε').coe_nonneg
      (by exact_mod_cast min_le_left T' ε') (LP.LP4HB.isSwallowedBy_congr (fun r hr => ?_) hs)⟩
    show -w r.toNNReal = -w' r.toNNReal
    rw [hEq _ (hlt _ (min_le_right _ _)) r hr]

/-- **A swallowed positive point is visited beyond**: if `x > 0` is swallowed by time `T`, a generating trace on
`[0, ∞)` visits `[x, ∞)` by time `T` (contrapositive of `Sec7.Lemma76E.alive_of_trace_off`). -/
theorem exists_visit_of_isSwallowedBy {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
    (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : 0 < x) {T : ℝ≥0}
    (hs : ZhanGT4.IsSwallowedBy (fun s : ℝ => w s.toNNReal) x T) :
    ∃ s : ℝ≥0, s ≤ T ∧ ∃ r : ℝ, x ≤ r ∧ γ s = r := by
  by_contra hno
  push Not at hno
  have ht₂ : ENNReal.ofReal ((T : ℝ) + 1) < ⊤ := ENNReal.ofReal_lt_top
  have hal := Sec7.Lemma76E.alive_of_trace_off hγ hw.continuousOn hw0 ht₂ (t := T) (by linarith) hx hno
  have hfc : Continuous (frozenDrive w ((T : ℝ) + 1)) := continuous_frozenDrive_of_lt hw.continuousOn ht₂
  have hs' : ZhanGT4.IsSwallowedBy (frozenDrive w ((T : ℝ) + 1)) x T :=
    LP.LP4HB.isSwallowedBy_congr (fun r hr => (frozenDrive_eq ⟨hr.1, hr.2.trans (by linarith)⟩).symm) hs
  exact hs' ⟨_, WangWu.isForwardSol_of_alive hfc hal⟩

/-- **The germ property of the driver gives the germ property of every trace** (`HasSeedGerm`). -/
theorem hasSeedGerm_of_driverGerm {κ SL SR : ℝ} {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
    (hw : Continuous w) (hw0 : w 0 = 0) (h : DriverGerm κ SL SR w) : HasSeedGerm κ SL SR γ := by
  obtain ⟨⟨T, hT, hne⟩, hR, hL⟩ := h
  refine ⟨T, hT, fun t ht htT => ?_, fun hS => ?_, fun hS => ?_⟩
  · rw [← Germ.loewnerTip_eq_trace hγ hw hw0 t]
    exact hne t ht htT
  · obtain ⟨x, hx, hs⟩ := hR hS T hT
    obtain ⟨s, hsT, r, hxr, hγs⟩ := exists_visit_of_isSwallowedBy hγ hw hw0 hx hs
    exact ⟨s, hsT, r, hx.trans_le hxr, hγs⟩
  · obtain ⟨x, hx, hs⟩ := hL hS T hT
    have hγR := LP.isGeneratingTrace_reflect hγ
    have hs' : ZhanGT4.IsSwallowedBy (fun s : ℝ => (-w) s.toNNReal) x T := hs
    obtain ⟨s, hsT, r, hxr, hγs⟩ := exists_visit_of_isSwallowedBy hγR hw.neg (by simp [hw0]) hx hs'
    refine ⟨s, hsT, -r, by linarith, ?_⟩
    have := congrArg LP.reflectC hγs
    rwa [LP.reflectC_reflectC, LP.reflectC_ofReal] at this

/-! ### The two-seed word -/

section TwoSeed

variable {κ rL rR : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The germ property of the two-seed word** (`κ > 4`, `r_L, r_R > −2`, the word complete). -/
theorem ae_driverGerm_twoSeed [IsProbabilityMeasure P] (hκ4 : 4 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hc : LP.IsCompleteForceWord.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, DriverGerm κ rL rR (fun t => W t ω) := by
  have hκ : 0 < κ := by linarith
  have hR' : ∀ᵐ ω ∂P, rR < κ / 2 - 2 → ∀ T : ℝ≥0, 0 < T → ∃ x : ℝ, 0 < x ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => W s.toNNReal ω) x T := by
    by_cases h : rR < κ / 2 - 2
    · filter_upwards [Germ.ae_swallowed_right hκ4 hL hR h hE] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h' => absurd h' h
  have hL' : ∀ᵐ ω ∂P, rL < κ / 2 - 2 → ∀ T : ℝ≥0, 0 < T → ∃ x : ℝ, 0 < x ∧
      ZhanGT4.IsSwallowedBy (fun s : ℝ => -W s.toNNReal ω) x T := by
    by_cases h : rL < κ / 2 - 2
    · filter_upwards [Germ.ae_swallowed_left hκ4 hL hR h hE] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h' => absurd h' h
  filter_upwards [Germ.ae_tip_ne_zero_twoSeed hκ hL hR hc hE, hR', hL'] with ω h0 hr hl
  exact ⟨⟨1, one_pos, fun t ht _ => h0 t ht⟩, hr, hl⟩

end TwoSeed

/-- The two-seed word with both weights at least `κ/2 − 2` has admissible partial sums. -/
theorem hasAdmissiblePartialSums_twoSeed {κ rL rR : ℝ} (hL : κ / 2 - 2 ≤ rL) (hR : κ / 2 - 2 ≤ rR) :
    Sec4.HasAdmissiblePartialSums κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL LP.twoSeedXR := by
  refine ⟨fun x hx _ => ?_, fun x hx _ => ?_⟩
  · have e : Finset.univ.filter (fun i : Fin 1 => x < LP.twoSeedXL i) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => by simpa [LP.twoSeedXL] using hx
    rw [e, Fin.sum_univ_one]
    exact hL
  · have e : Finset.univ.filter (fun i : Fin 1 => LP.twoSeedXR i ≤ x) = Finset.univ :=
      Finset.filter_true_of_mem fun i _ => by simpa [LP.twoSeedXR] using hx
    rw [e, Fin.sum_univ_one]
    exact hR

/-- **The two-seed word with barrier weights is complete, from Aux. lemma 7** (`Sec4.Aux7Statement κ`). -/
theorem isCompleteForceWord_twoSeed_of_aux7 {κ rL rR : ℝ} (haux7 : Sec4.Aux7Statement.{u} κ)
    (hL : κ / 2 - 2 ≤ rL) (hR : κ / 2 - 2 ≤ rR) :
    LP.IsCompleteForceWord.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hF : IsOrderedForceWord LP.twoSeedXL LP.twoSeedXR :=
    ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩
  filter_upwards [haux7 _ _ _ _ P 𝓕 W VL VR B ζ hF (hasAdmissiblePartialSums_twoSeed hL hR) hE] with ω
    ⟨hζ, ⟨η, hη⟩, htr⟩
  exact ⟨η, by rw [hζ]; exact hη, fun _ => htr η hη⟩

/-! ### Every seeded word -/

section Seeded

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The seed germ of a seeded word** (`κ > 4`): for an ordered word with a mark at `0⁻` and a mark at `0⁺` and
infinite lifetime, if the two-seed word with the word's seed weights is complete (a continuous transient trace,
`LP.IsCompleteForceWord`), then almost surely every continuous generating trace on `[0, ∞)` has the germ property
`HasSeedGerm` for the seed weights of the word. -/
theorem ae_hasSeedGerm_of_complete [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hc : LP.IsCompleteForceWord.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedWeightL xL ρL)
      (fun _ => seedWeightR xR ρR))
    (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {k : Fin nR} (hk : xR k = 0) {l : Fin nL} (hl : xL l = 0) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ →
      HasSeedGerm κ (seedWeightL xL ρL) (seedWeightR xR ρR) γ := by
  have hκ : 0 < κ := by linarith
  obtain ⟨hsL, hsR⟩ := (Sec2.not_thr_iff_seedSum xL xR ρL ρR).1
    (Germ.not_thresholdCondition_of_ae_top hE hζ)
  have hD : ∀ᵐ ω ∂P, DriverGerm κ (seedWeightL xL ρL) (seedWeightR xR ρR) (fun t => W t ω) :=
    Germ.ae_of_twoSeed hκ hord hl hk hE hζ
      (fun _ _ hw hw' hw0 hw'0 hag h => driverGerm_congr hw hw' hw0 hw'0 hag h)
      (fun _ _ _ _ _ _ _ _ hG => ae_driverGerm_twoSeed (rL := seedWeightL xL ρL) (rR := seedWeightR xR ρR)
        hκ4 hsL hsR hc hG)
  filter_upwards [hD, hζ, hE.2.2.2.2] with ω hd hζω hp γ hγ
  rw [hζω] at hp
  exact hasSeedGerm_of_driverGerm hγ (continuousOn_univ.1 (by simpa using hp.2.2.2.1)) hp.1 hd

/-- **No return to the start for a seeded word** (`κ > 4`), from the completeness of the two-seed word with the word's
seed weights: almost surely no continuous generating trace on `[0, ∞)` vanishes at a positive time. -/
theorem ae_trace_ne_zero_of_complete [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hc : LP.IsCompleteForceWord.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => seedWeightL xL ρL)
      (fun _ => seedWeightR xR ρR))
    (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {k : Fin nR} (hk : xR k = 0) {l : Fin nL} (hl : xL l = 0) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 :=
  ae_trace_ne_zero_of_germ (by linarith) hord hE hζ hk hl (ae_hasSeedGerm_of_complete hκ4 hc hord hE hζ hk hl)

/-- **The seed germ of a seeded word from two-seed completeness** (`LP.TwoSeedComplete κ`, `κ > 4`). -/
theorem ae_hasSeedGerm_of_twoSeedComplete [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hc : LP.TwoSeedComplete.{u} κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {k : Fin nR} (hk : xR k = 0) {l : Fin nL} (hl : xL l = 0) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ →
      HasSeedGerm κ (seedWeightL xL ρL) (seedWeightR xR ρR) γ := by
  obtain ⟨hsL, hsR⟩ := (Sec2.not_thr_iff_seedSum xL xR ρL ρR).1
    (Germ.not_thresholdCondition_of_ae_top hE hζ)
  exact ae_hasSeedGerm_of_complete hκ4 (hc _ _ hsL hsR) hord hE hζ hk hl

/-- **No return to the start for a seeded word** (`κ > 4`, from two-seed completeness). -/
theorem ae_trace_ne_zero_of_twoSeedComplete [IsProbabilityMeasure P] (hκ4 : 4 < κ)
    (hc : LP.TwoSeedComplete.{u} κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {k : Fin nR} (hk : xR k = 0) {l : Fin nL} (hl : xL l = 0) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 :=
  ae_trace_ne_zero_of_germ (by linarith) hord hE hζ hk hl
    (ae_hasSeedGerm_of_twoSeedComplete hκ4 hc hord hE hζ hk hl)

/-- **Barrier seeds: no return from Aux. lemma 7 alone** (`κ > 4`). For a seeded word whose two seed groups both have
weight at least `κ/2 − 2`, the two-seed word has admissible partial sums, so Aux. lemma 7 at `κ`
(`Sec4.Aux7Statement κ`: a continuous transient trace for words with admissible partial sums) makes it complete, and
almost surely no continuous generating trace on `[0, ∞)` vanishes at a positive time. -/
theorem ae_trace_ne_zero_of_aux7 [IsProbabilityMeasure P] (hκ4 : 4 < κ) (haux7 : Sec4.Aux7Statement.{u} κ)
    (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {k : Fin nR} (hk : xR k = 0) {l : Fin nL} (hl : xL l = 0) (hbL : κ / 2 - 2 ≤ seedWeightL xL ρL)
    (hbR : κ / 2 - 2 ≤ seedWeightR xR ρR) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 :=
  ae_trace_ne_zero_of_complete hκ4 (isCompleteForceWord_twoSeed_of_aux7 haux7 hbL hbR) hord hE hζ hk hl

end Seeded

/-- **`SeedGermStatement` for the seeded words**: the named input `SeedGermStatement κ` of PROVE-CFNORETURN, for the
ordered words with a mark at `0⁻` and a mark at `0⁺` (all the words of the counterflow). -/
def SeedGermBothStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞),
    IsOrderedForceWord xL xR → (∃ l, xL l = 0) → (∃ k, xR k = 0) →
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ → (∀ᵐ ω ∂P, ζ ω = ⊤) →
        ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ →
          HasSeedGerm κ (seedWeightL xL ρL) (seedWeightR xR ρR) γ

/-- **The seed germ of every seeded word from two-seed completeness** (`κ > 4`). -/
theorem seedGermBothStatement_of_twoSeedComplete {κ : ℝ} (hκ4 : 4 < κ) (hc : LP.TwoSeedComplete.{u} κ) :
    SeedGermBothStatement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hord ⟨l, hl⟩ ⟨k, hk⟩ hE hζ
  exact ae_hasSeedGerm_of_twoSeedComplete hκ4 hc hord hE hζ hk hl

/-- **Two-seed completeness for `κ > 4` from LP11's two-seed inputs** (Theorem R.7, Lemma 7.25, Proposition LP4;
`LP.isCompleteForceWord_twoSeed`). -/
theorem twoSeedComplete_of_inputs (hR7 : LP.TheoremR7TraceStatement.{u}) (h725 : LP.Lemma725TraceStatement.{u})
    (hLP4 : LP.LP4Statement.{u}) {κ : ℝ} (hκ4 : 4 < κ) : LP.TwoSeedComplete.{u} κ :=
  fun _ _ hL hR => LP.isCompleteForceWord_twoSeed hR7 h725 hLP4 hκ4 hL hR

/-- **PROVE-CFNORETURN's reduction with the seeded input**: `CounterflowNoReturnStatement` (ruling R59) from
`SeedGermBothStatement (16/κ)`, `0 < κ < 4` (the counterflow's flow-line word has its seed marks `0⁻`, `0⁺` at
index `0`). -/
theorem counterflowNoReturnStatement_of_seedGermBoth
    (hG : ∀ κ : ℝ, 0 < κ → κ < 4 → SeedGermBothStatement.{u} (16 / κ)) :
    Theorem14.GW4Ident.CounterflowNoReturnStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ Q _ h hh W ζ hcf hζ
  obtain ⟨b', J', h', -, -, h'', 𝓕, VL, VR, B, -, hC⟩ := hcf
  have hE := hC.1
  have hord := Theorem15.isOrderedForceWord_flowLine b' J' 0
  have hκ' : 0 < 16 / κ := by positivity
  exact ae_trace_ne_zero_of_germ hκ' hord hE hζ (k := ⟨0, by unfold flowLineNR; omega⟩) rfl
    (l := ⟨0, by unfold flowLineNL; omega⟩) rfl
    (hG κ hκ hκ4 _ _ _ _ Q 𝓕 W VL VR B ζ hord ⟨⟨0, by unfold flowLineNL; omega⟩, rfl⟩
      ⟨⟨0, by unfold flowLineNR; omega⟩, rfl⟩ hE hζ)

/-- **The counterflow does not return to its start** (`CounterflowNoReturnStatement`, ruling R59), for every
admissible word, from two-seed completeness at the counterflow parameters `κ' = 16/κ > 4`. -/
theorem counterflowNoReturnStatement_of_twoSeedComplete
    (hc : ∀ κ' : ℝ, 4 < κ' → LP.TwoSeedComplete.{u} κ') :
    Theorem14.GW4Ident.CounterflowNoReturnStatement.{u} :=
  counterflowNoReturnStatement_of_seedGermBoth fun κ hκ hκ4 =>
    have hκ' : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
    seedGermBothStatement_of_twoSeedComplete hκ' (hc _ hκ')

/-- **The counterflow does not return to its start** (`CounterflowNoReturnStatement`), from LP11's two-seed inputs for
`κ' > 4`: Theorem R.7 (`LP.TheoremR7TraceStatement`), Lemma 7.25 (`LP.Lemma725TraceStatement`) and Proposition LP4
(`LP.LP4Statement`). Conditional helper. -/
theorem counterflowNoReturnStatement_of_inputs (hR7 : LP.TheoremR7TraceStatement.{u})
    (h725 : LP.Lemma725TraceStatement.{u}) (hLP4 : LP.LP4Statement.{u}) :
    Theorem14.GW4Ident.CounterflowNoReturnStatement.{u} :=
  counterflowNoReturnStatement_of_twoSeedComplete fun _ hκ' => twoSeedComplete_of_inputs hR7 h725 hLP4 hκ'

end CfNoReturn

end InteractingSLE
