/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB5Path
import InteractingSLE.Spec.Coupling.AnnounceLifetime
import InteractingSLE.Spec.Sec2.TwoSeedLawBridge
import InteractingSLE.Spec.Ito.Localize
import InteractingSLE.Spec.Ito.Measurability

/-!
# Lemma GB5: localization and the Lyapunov estimate

Packet PROVE-T14-GB. For an integrated `SLE_k(ρ)` evolution with the hypotheses of Lemma GB5 (supplement §8.5), the
Lyapunov observable of `GB5Lyap.lean` is localized at

  `σ = T_n ∧ (first failure of the outer constraints) ∧ (first time X_j < ε) ∧ (exit of |B| from (−n, n))`

(`gbLoc`), where `T_n < ζ` is an announcing sequence of the lifetime (`Coupling.exists_isAnnouncingSeq_le`) and the
outer constraints are: all marks in `[−n, n]`, `V^j − V^{i₀} ≥ 1/(R+1)`, and, if there are left marks,
`W − V^{L,0} ≥ γ` or `X_j ≥ γ'` (the localization of the opposite group). Off a full-measure event `G` of good paths
the localizing time is `0`.

* `martingale_gbLyap`: the localized Itô formula (`Ito.martingale_itoLocalized`) for the observable;
* `measure_gbEvent_le`: **the Lyapunov estimate**. On the event that `X_j` reaches `ε` before the outer constraints
  fail, before `T_n` and before `|B|` reaches `n` (`gbEvent`), the observable is at least `log(1/ε)`; it has
  expectation at most `F(0) + gbCst` (the opposite-group drift, `integral_itoGen_le`). Markov's inequality gives
  `P(gbEvent) ≤ (F(0) + log C + gbCst)/log(C/ε)`, uniformly in the level `R` of the `V^j − V^{i₀}` constraint.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB5

variable {nL nR : ℕ}

/-! ### Functionals of the state -/

/-- `X_j = V^j − W`. -/
def xFun (j : Fin nR) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ := st.2.2 j - st.1

/-- `d = V^j − V^{i₀}`. -/
def dFun (j i₀ : Fin nR) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ := st.2.2 j - st.2.2 i₀

/-- The localization of the opposite group: `max(W − V^{L,0} − γ, X_j − γ')` (`1` without left marks). -/
def leftFun (j : Fin nR) (γ γ' : ℝ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  if h : 0 < nL then max (st.1 - st.2.1 ⟨0, h⟩ - γ) (xFun j st - γ') else 1

/-- The outer constraints: `‖state‖ ≤ n`, `d ≥ 1/(R+1)`, and the opposite-group localization. -/
def levO (j i₀ : Fin nR) (n R : ℕ) (γ γ' : ℝ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  min (min ((n : ℝ) - ‖st‖) (dFun j i₀ st - 1 / ((R : ℝ) + 1))) (leftFun j γ γ' st)

/-- The constraint `X_j ≥ ε`. -/
def levX (j : Fin nR) (ε : ℝ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ := xFun j st - ε

theorem continuous_xFun (j : Fin nR) : Continuous (xFun (nL := nL) j) := by
  unfold xFun
  exact ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).sub continuous_fst

theorem continuous_dFun (j i₀ : Fin nR) : Continuous (dFun (nL := nL) j i₀) := by
  unfold dFun
  exact ((continuous_apply j).comp (continuous_snd.comp continuous_snd)).sub
    ((continuous_apply i₀).comp (continuous_snd.comp continuous_snd))

theorem continuous_leftFun (j : Fin nR) (γ γ' : ℝ) : Continuous (leftFun (nL := nL) j γ γ') := by
  unfold leftFun
  by_cases h : 0 < nL
  · simp only [h, ↓reduceDIte]
    have h1 : Continuous fun st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => st.1 - st.2.1 ⟨0, h⟩ - γ := by
      fun_prop
    have h2 : Continuous fun st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => xFun j st - γ' :=
      (continuous_xFun j).sub continuous_const
    exact h1.max h2
  · simp only [h, ↓reduceDIte]; exact continuous_const

theorem continuous_levO (j i₀ : Fin nR) (n R : ℕ) (γ γ' : ℝ) :
    Continuous (levO (nL := nL) j i₀ n R γ γ') := by
  unfold levO
  exact ((continuous_const.sub continuous_norm).min ((continuous_dFun j i₀).sub continuous_const)).min
    (continuous_leftFun j γ γ')

theorem continuous_levX (j : Fin nR) (ε : ℝ) : Continuous (levX (nL := nL) j ε) :=
  (continuous_xFun j).sub continuous_const

theorem levO_mono {j i₀ : Fin nR} {n R R' : ℕ} {γ γ' : ℝ} (hR : R ≤ R')
    (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : levO j i₀ n R γ γ' st ≤ levO j i₀ n R' γ γ' st := by
  unfold levO
  refine min_le_min (min_le_min le_rfl ?_) le_rfl
  have h : 1 / ((R' : ℝ) + 1) ≤ 1 / ((R : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hR 1)
  linarith

/-! ### Hitting times along one path -/

section PathHit

variable {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- Before a time `σ < ζ` that is at most the hitting time of `{f < 0}`, `f ≥ 0`; at `σ` itself too if `σ > 0`
(by continuity from the left). -/
theorem nonneg_of_le_hitBelow (hf : ContinuousOn f {s : ℝ≥0 | (s : ℝ≥0∞) < ζ}) {σ : ℝ≥0}
    (hσζ : (σ : ℝ≥0∞) < ζ) (hσ : (σ : WithTop ℝ≥0) ≤ Coupling.hitBelow f ζ 0) (hσ0 : 0 < σ)
    {r : ℝ≥0} (hr : r ≤ σ) : 0 ≤ f r := by
  have hlt : ∀ r' < σ, 0 ≤ f r' := fun r' hr' => by
    by_contra hneg
    push Not at hneg
    have h1 := Coupling.hitBelow_le (f := f) (lt_of_le_of_lt (by exact_mod_cast hr'.le) hσζ) hneg
    exact absurd (WithTop.coe_le_coe.1 (hσ.trans h1)) (not_le.2 hr')
  rcases hr.lt_or_eq with h | rfl
  · exact hlt r h
  · have hat := hf.continuousAt ((Coupling.isOpen_setOf_coe_lt ζ).mem_nhds hσζ)
    have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
    refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio r))) ?_
    filter_upwards [self_mem_nhdsWithin] with r' hr'
    exact hlt r' hr'

theorem hitBelow_mono_fun' {g : ℝ≥0 → ℝ} (hfg : ∀ s, f s ≤ g s) :
    Coupling.hitBelow f ζ 0 ≤ Coupling.hitBelow g ζ 0 := by
  by_cases hne : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ f s < 0}.Nonempty
  · rw [Coupling.hitBelow_of_nonempty hne]
    exact Coupling.le_hitBelow fun s hs hgs => csInf_le (OrderBot.bddBelow _)
      ⟨hs, lt_of_le_of_lt (hfg s) hgs⟩
  · have hne' : ¬ {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ∧ g s < 0}.Nonempty := fun ⟨s, hs, hgs⟩ =>
      hne ⟨s, hs, lt_of_le_of_lt (hfg s) hgs⟩
    rw [Coupling.hitBelow_of_not_nonempty hne, Coupling.hitBelow_of_not_nonempty hne']

end PathHit

/-! ### Good paths and the localizing times -/

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Good paths**: the frozen pathwise conditions, a continuous Brownian path from `0`, and the announcing
property of the times `T n` (`T n < ζ`, every `t < ζ` below some `T n`). -/
def IsGBGood (k : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (ω : Ω) : Prop :=
  IsIntegratedSLEPath k xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (ζ ω) ∧
    Continuous (B · ω) ∧ B 0 ω = 0 ∧ (∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω

open scoped Classical in
/-- The first failure of the outer constraints, on the good event (`0` off it). -/
def hitO (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (j i₀ : Fin nR) (n R : ℕ) (γ γ' : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => levO j i₀ n R γ γ' (Coupling.stateAt W VL VR s ω)) (ζ ω) 0
  else 0

open scoped Classical in
/-- The first time `X_j < ε`, on the good event (`0` off it). -/
def hitX (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (j : Fin nR) (ε : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => levX j ε (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0

/-- **The localizing time** `σ = T_n ∧ hitO ∧ hitX ∧ (exit of |B| from (−n, n))`. -/
def gbLoc (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (j i₀ : Fin nR) (n R : ℕ) (γ γ' ε : ℝ)
    (ω : Ω) : ℝ≥0 :=
  Sec2.TwoSeed.capTime (T n) (fun ω => min (min (hitO G W VL VR ζ j i₀ n R γ γ' ω)
    (hitX G W VL VR ζ j ε ω)) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω

/-- **The event of a hit**: `X_j` drops below `ε` no later than the outer constraints fail, `|B|` reaches `n`,
and `T_n`. -/
def gbEvent (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (j i₀ : Fin nR) (n R : ℕ) (γ γ' ε : ℝ) :
    Set Ω :=
  {ω | ω ∈ G ∧ hitX G W VL VR ζ j ε ω ≤ min (min (hitO G W VL VR ζ j i₀ n R γ γ' ω)
    (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) (T n ω : WithTop ℝ≥0)}

variable {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {j i₀ : Fin nR} {n R : ℕ} {γ γ' ε : ℝ}

theorem gbLoc_le_T (ω : Ω) : gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω ≤ T n ω :=
  Sec2.TwoSeed.capTime_le _ _ ω

theorem gbLoc_le_hitO (ω : Ω) :
    (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω : WithTop ℝ≥0) ≤ hitO G W VL VR ζ j i₀ n R γ γ' ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans ((min_le_left _ _).trans (min_le_left _ _))

theorem gbLoc_le_hitX (ω : Ω) :
    (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω : WithTop ℝ≥0) ≤ hitX G W VL VR ζ j ε ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans ((min_le_left _ _).trans (min_le_right _ _))

theorem gbLoc_le_exitTime (ω : Ω) :
    (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω : WithTop ℝ≥0) ≤
      MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_right _ _)

theorem gbLoc_of_not_mem {ω : Ω} (hω : ω ∉ G) : gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω = 0 := by
  have h := gbLoc_le_hitO (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (j := j)
    (i₀ := i₀) (n := n) (R := R) (γ := γ) (γ' := γ') (ε := ε) ω
  simp only [hitO, hω, ↓reduceIte] at h
  exact le_antisymm (by exact_mod_cast h) bot_le

/-- On the event of a hit, the localizing time is the hitting time of `{X_j < ε}`. -/
theorem gbLoc_eq_hitX {ω : Ω} (hω : ω ∈ gbEvent G W VL VR B ζ T j i₀ n R γ γ' ε) :
    (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω : WithTop ℝ≥0) = hitX G W VL VR ζ j ε ω := by
  refine le_antisymm (gbLoc_le_hitX ω) ?_
  rw [gbLoc, Sec2.TwoSeed.coe_capTime]
  refine le_min (hω.2.trans (min_le_right _ _)) (le_min (le_min ?_ le_rfl) ?_)
  · exact hω.2.trans ((min_le_left _ _).trans (min_le_left _ _))
  · exact hω.2.trans ((min_le_left _ _).trans (min_le_right _ _))

theorem gbEvent_mono {R R' : ℕ} (hR : R ≤ R') :
    gbEvent G W VL VR B ζ T j i₀ n R γ γ' ε ⊆ gbEvent G W VL VR B ζ T j i₀ n R' γ γ' ε := by
  rintro ω ⟨hωG, h⟩
  refine ⟨hωG, h.trans (min_le_min (min_le_min ?_ le_rfl) le_rfl)⟩
  simp only [hitO, hωG, ↓reduceIte]
  exact hitBelow_mono_fun' fun s => levO_mono hR _

end Loc

section StoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {j i₀ : Fin nR} {n R : ℕ} {γ γ' ε : ℝ}

theorem measurableSet_good_usual' (hGm : MeasurableSet G) (hGc : P Gᶜ = 0) (t : ℝ≥0) :
    MeasurableSet[usualAugmentation 𝓕 P t] G := by
  have := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
  rwa [compl_compl] at this

theorem continuous_brownG_gb (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) (ω : Ω) :
    Continuous (Sec2.TwoSeed.brownG G B · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using (hgood ω hω).2.1
  · simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]; exact continuous_const

theorem isFilteredBrownianReal_brownG_gb (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) :
    IsFilteredBrownianReal (usualAugmentation 𝓕 P) (Sec2.TwoSeed.brownG G B) P := by
  have := (Ito.isFilteredBrownianReal_modify (Ito.isFilteredBrownianReal_usualAugmentation hE.1) hGm hGc
    fun ω hω => (hgood ω hω).2.1).1
  rwa [Ito.nullAugmented_usualAugmentation] at this

theorem continuousOn_stateAt_gb (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) {ω : Ω}
    (hω : ω ∈ G) :
    ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := by
  have hF := (hgood ω hω).1.isForcePath
  exact hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
    (continuousOn_pi.2 hF.continuousOn_vR))

open scoped Classical in
theorem isStoppingTime_hit_gb (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    {Φ : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) → ℝ} (hΦ : Continuous Φ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω =>
      if ω ∈ G then Coupling.hitBelow (fun s => Φ (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0 := by
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hτ := Coupling.isStoppingTime_hitBelow_state hWa hVLa hVRa hG0
    (fun ω hω => continuousOn_stateAt_gb hgood hω) hΦ 0
  intro t
  have e : {ω | (if ω ∈ G then Coupling.hitBelow (fun s => Φ (Coupling.stateAt W VL VR s ω)) (ζ ω) 0
      else 0) ≤ (t : WithTop ℝ≥0)} = Gᶜ ∪ {ω | (if ω ∈ G then Coupling.hitBelow
      (fun s => Φ (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else ⊤) ≤ t} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp [hω]
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff, not_false_eq_true, true_or,
        iff_true]
      exact_mod_cast (zero_le (a := t))
  rw [e]
  exact ((usualAugmentation 𝓕 P).mono (zero_le (a := t)) _ hG0).compl.union (hτ t)

/-- **The localizing times are stopping times of the usual augmentation.** -/
theorem isStoppingTime_gbLoc (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0)) :
    IsStoppingTime (usualAugmentation 𝓕 P)
      fun ω => (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω : WithTop ℝ≥0) :=
  Sec2.TwoSeed.isStoppingTime_capTime (hT n)
    (((isStoppingTime_hit_gb hE hGm hGc hgood (continuous_levO j i₀ n R γ γ')).min
      (isStoppingTime_hit_gb hE hGm hGc hgood (continuous_levX j ε))).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG_gb hE hGm hGc hgood).2.1 (continuous_brownG_gb hgood) n))

end StoppingTime

/-! ### Pathwise facts on good paths -/

section GoodFacts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {j i₀ : Fin nR} {n R : ℕ} {γ γ' ε : ℝ}
  {ω : Ω} (hω : IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) (hωG : ω ∈ G)
include hω

theorem gbLoc_lt_lifetime : (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω : ℝ≥0∞) < ζ ω :=
  lt_of_le_of_lt (by exact_mod_cast gbLoc_le_T ω) (hω.2.2.2.1 n)

include hωG in
theorem levO_nonneg_of_le_gbLoc (hσ0 : 0 < gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) {r : ℝ≥0}
    (hr : r ≤ gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) :
    0 ≤ levO j i₀ n R γ γ' (Coupling.stateAt W VL VR r ω) := by
  have h := gbLoc_le_hitO (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (j := j)
    (i₀ := i₀) (n := n) (R := R) (γ := γ) (γ' := γ') (ε := ε) ω
  simp only [hitO, hωG, ↓reduceIte] at h
  have hF := hω.1.isForcePath
  exact nonneg_of_le_hitBelow ((continuous_levO j i₀ n R γ γ').comp_continuousOn
    (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR)))) (gbLoc_lt_lifetime hω) h hσ0 hr

include hωG in
theorem levX_nonneg_of_le_gbLoc (hσ0 : 0 < gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) {r : ℝ≥0}
    (hr : r ≤ gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) :
    0 ≤ levX j ε (Coupling.stateAt W VL VR r ω) := by
  have h := gbLoc_le_hitX (G := G) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (T := T) (j := j)
    (i₀ := i₀) (n := n) (R := R) (γ := γ) (γ' := γ') (ε := ε) ω
  simp only [hitX, hωG, ↓reduceIte] at h
  have hF := hω.1.isForcePath
  exact nonneg_of_le_hitBelow ((continuous_levX j ε).comp_continuousOn
    (hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
      (continuousOn_pi.2 hF.continuousOn_vR)))) (gbLoc_lt_lifetime hω) h hσ0 hr

include hωG in
theorem abs_B_le_of_le_gbLoc (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) {r : ℝ≥0}
    (hr : r ≤ gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) : |B r ω| ≤ n := by
  rcases (zero_le (a := r)).eq_or_lt with h0 | h0
  · rw [← h0, hω.2.2.1, abs_zero]; exact Nat.cast_nonneg n
  have h := MathFin.abs_le_N_of_le_exitTime (continuous_brownG_gb hgood) h0
    ((WithTop.coe_le_coe.2 hr).trans (gbLoc_le_exitTime ω))
  simpa only [Sec2.TwoSeed.brownG, hωG, ↓reduceIte] using h

end GoodFacts

/-! ### The compact set and the coordinate processes -/

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem abs_le_norm_state (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) :
    |st.1| ≤ ‖st‖ ∧ (∀ i, |st.2.1 i| ≤ ‖st‖) ∧ ∀ i, |st.2.2 i| ≤ ‖st‖ := by
  refine ⟨(le_of_eq (Real.norm_eq_abs _).symm).trans (norm_fst_le st), fun i => ?_, fun i => ?_⟩
  · calc |st.2.1 i| = ‖st.2.1 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖st.2.1‖ := norm_le_pi_norm _ i
      _ ≤ ‖st.2‖ := norm_fst_le _
      _ ≤ ‖st‖ := norm_snd_le _
  · calc |st.2.2 i| = ‖st.2.2 i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖st.2.2‖ := norm_le_pi_norm _ i
      _ ≤ ‖st.2‖ := norm_snd_le _
      _ ≤ ‖st‖ := norm_snd_le _

open scoped Classical in
/-- The Itô coordinates on the good event (their initial value off it). -/
def coordG (k : ℝ) (xR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (j i₀ : Fin nR) (t : ℝ≥0) (ω : Ω) : ℝ × ℝ :=
  if ω ∈ G then coordAt k j i₀ (W · ω) (fun i t => VR i t ω) (B · ω) t else (xR j, xR j - xR i₀)

open scoped Classical in
/-- Their density on the good event (`0` off it). -/
def densG (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (j i₀ : Fin nR) (s : ℝ) (ω : Ω) : ℝ × ℝ :=
  if ω ∈ G then densAt ρL ρR j i₀ (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s else 0

/-- The initial point of the coordinates and of the Brownian motion. -/
def initPt (xR : Fin nR → ℝ) (j i₀ : Fin nR) : (ℝ × ℝ) × ℝ := ((xR j, xR j - xR i₀), 0)

/-- The box `X_j ≥ ε`, `d ≥ 1/(R+1)`, `‖·‖ ≤ (2 + √k) n`. -/
def gbBox (k : ℝ) (n R : ℕ) (ε : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {q | ε ≤ lyapX k q ∧ 1 / ((R : ℝ) + 1) ≤ q.1.2 ∧ ‖q‖ ≤ (2 + Real.sqrt k) * n}

/-- The compact set of the localization: the box and the initial point. -/
def gbKc (k : ℝ) (xR : Fin nR → ℝ) (j i₀ : Fin nR) (n R : ℕ) (ε : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  insert (initPt xR j i₀) (gbBox k n R ε)

variable {k : ℝ} {xR : Fin nR → ℝ} {j i₀ : Fin nR} {n R : ℕ} {ε : ℝ}

theorem isCompact_gbKc : IsCompact (gbKc k xR j i₀ n R ε) := by
  refine IsCompact.insert ?_ _
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {q : (ℝ × ℝ) × ℝ | ε ≤ lyapX k q} := isClosed_le continuous_const continuous_lyapX
    have h2 : IsClosed {q : (ℝ × ℝ) × ℝ | 1 / ((R : ℝ) + 1) ≤ q.1.2} :=
      isClosed_le continuous_const (continuous_snd.comp continuous_fst)
    have h3 : IsClosed {q : (ℝ × ℝ) × ℝ | ‖q‖ ≤ (2 + Real.sqrt k) * n} :=
      isClosed_le continuous_norm continuous_const
    exact h1.inter (h2.inter h3)
  · refine (Metric.isBounded_closedBall (x := (0 : (ℝ × ℝ) × ℝ)) (r := (2 + Real.sqrt k) * n)).subset
      fun q hq => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hq.2.2

theorem gbKc_subset_region (hε : 0 < ε) (hxj : 0 < xR j) (hxd : xR i₀ < xR j) :
    gbKc k xR j i₀ n R ε ⊆ lyapRegion k := by
  intro q hq
  rcases hq with rfl | hq
  · refine ⟨?_, ?_⟩
    · simp only [lyapX, initPt, mul_zero, sub_zero]; exact hxj
    · simp only [initPt]; linarith
  · exact ⟨hε.trans_le hq.1, lt_of_lt_of_le (by positivity) hq.2.1⟩

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {γ γ' : ℝ}

/-- **Up to `σ` the coordinates and the Brownian motion stay in the compact set.** -/
theorem mem_gbKc_of_le_gbLoc (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω) {ω : Ω}
    (hωG : ω ∈ G) {r : ℝ≥0} (hr : r ≤ gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) :
    (coordG k xR G W VR B j i₀ r ω, Sec2.TwoSeed.brownG G B r ω) ∈ gbKc k xR j i₀ n R ε := by
  have hω := hgood ω hωG
  have hF := hω.1.isForcePath
  simp only [coordG, Sec2.TwoSeed.brownG, hωG, ↓reduceIte]
  rcases (zero_le (a := gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω)).eq_or_lt with h0 | h0
  · have hr0 : r = 0 := le_antisymm (h0 ▸ hr) bot_le
    subst hr0
    refine Set.mem_insert_iff.2 (Or.inl ?_)
    have hw : W 0 ω = 0 := hF.w_zero
    have hj : VR j 0 ω = xR j := hF.vR_zero j
    have hi : VR i₀ 0 ω = xR i₀ := hF.vR_zero i₀
    simp only [coordAt, initPt, hw, hj, hi, hω.2.2.1, mul_zero, add_zero, sub_zero]
  refine mem_insert_of_mem _ ⟨?_, ?_, ?_⟩
  · rw [lyapX_coordAt]
    have := levX_nonneg_of_le_gbLoc hω hωG h0 hr
    simp only [levX, xFun, Coupling.stateAt] at this
    linarith
  · have := levO_nonneg_of_le_gbLoc hω hωG h0 hr
    simp only [levO, dFun, Coupling.stateAt, le_min_iff] at this
    simp only [coordAt]
    linarith [this.1.2]
  · have hO := levO_nonneg_of_le_gbLoc hω hωG h0 hr
    simp only [levO, le_min_iff] at hO
    have hn : ‖Coupling.stateAt W VL VR r ω‖ ≤ n := by linarith [hO.1.1]
    obtain ⟨hw, -, hv⟩ := abs_le_norm_state (Coupling.stateAt W VL VR r ω)
    simp only [Coupling.stateAt] at hw hv
    have hB := abs_B_le_of_le_gbLoc hω hωG hgood hr
    have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg k
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have ha : |VR j r ω - W r ω + Real.sqrt k * B r ω| ≤ (2 + Real.sqrt k) * n := by
      have h1 := abs_add_le (VR j r ω - W r ω) (Real.sqrt k * B r ω)
      have h2 := abs_sub (VR j r ω) (W r ω)
      rw [abs_mul, abs_of_nonneg hsk] at h1
      have h3 : Real.sqrt k * |B r ω| ≤ Real.sqrt k * n := mul_le_mul_of_nonneg_left hB hsk
      linarith [(hv j).trans hn, hw.trans hn]
    have hd : |VR j r ω - VR i₀ r ω| ≤ (2 + Real.sqrt k) * n := by
      calc |VR j r ω - VR i₀ r ω| ≤ |VR j r ω| + |VR i₀ r ω| := abs_sub _ _
        _ ≤ n + n := add_le_add ((hv j).trans hn) ((hv i₀).trans hn)
        _ ≤ (2 + Real.sqrt k) * n := by nlinarith
    have hb : |B r ω| ≤ (2 + Real.sqrt k) * n := hB.trans (by nlinarith)
    simp only [coordAt, Prod.norm_def, Real.norm_eq_abs]
    exact max_le (max_le ha hd) hb

end Martingale

section Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {j i₀ : Fin nR} {n R : ℕ} {γ γ' ε : ℝ}
  (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
  (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))

include hE hGm hGc hgood hT in
/-- **The stopped coordinates are adapted.** -/
theorem measurable_coordG_gbLoc (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      coordG k xR G W VR B j i₀ (min t (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω)) ω := by
  obtain ⟨-, hWa, -, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P
  have hG0 := measurableSet_good_usual' (𝓕 := 𝓕) hGm hGc 0
  have hσ := isStoppingTime_gbLoc (j := j) (i₀ := i₀) (n := n) (R := R) (γ := γ) (γ' := γ') (ε := ε)
    hE hGm hGc hgood hT
  have hB' := isFilteredBrownianReal_brownG_gb hE hGm hGc hgood
  set Kp : ℝ≥0 → Ω → ℝ × ℝ := fun s ω =>
    ((if (s : ℝ≥0∞) < ζ ω then VR j s ω else 0) - (if (s : ℝ≥0∞) < ζ ω then W s ω else 0) +
        Real.sqrt k * Sec2.TwoSeed.brownG G B s ω,
      (if (s : ℝ≥0∞) < ζ ω then VR j s ω else 0) - (if (s : ℝ≥0∞) < ζ ω then VR i₀ s ω else 0))
    with hKp
  have hK : ∀ s, Measurable[𝓖 s] (Kp s) := fun s =>
    (((Sec2.TwoSeed.measurable_killed (hVRa j) s).sub (Sec2.TwoSeed.measurable_killed hWa s)).add
      (measurable_const.mul (hB'.2.1 s))).prodMk
      ((Sec2.TwoSeed.measurable_killed (hVRa j) s).sub (Sec2.TwoSeed.measurable_killed (hVRa i₀) s))
  have h := Ito.measurable_stopped_of_agree
    (X := fun s ω => coordAt k j i₀ (W · ω) (fun i t => VR i t ω) (B · ω) s) hσ hK hG0
    ((xR j, xR j - xR i₀) : ℝ × ℝ) (fun ω hω s hs => ?_) (fun ω hω => ?_) t
  · convert h using 2 with ω
    by_cases hω : ω ∈ G <;> simp [coordG, hω]
  · have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) (gbLoc_lt_lifetime (hgood ω hω))
    simp only [hKp, hsζ, ↓reduceIte, Sec2.TwoSeed.brownG, hω, coordAt]
  · have hF := (hgood ω hω).1.isForcePath
    have hsub : Iic (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
      fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (gbLoc_lt_lifetime (hgood ω hω))
    have hBc : ContinuousOn (B · ω) (Iic (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω)) :=
      (hgood ω hω).2.1.continuousOn
    exact ((((hF.continuousOn_vR j).mono hsub).sub (hF.continuousOn_w.mono hsub)).add
      (continuousOn_const.mul hBc)).prodMk (((hF.continuousOn_vR j).mono hsub).sub
        ((hF.continuousOn_vR i₀).mono hsub))

include hE hGm hGc hgood hT in
/-- **The localized Itô formula for the Lyapunov observable**: with `σ = gbLoc`,
`F(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen F` is a martingale of the usual augmentation. -/
theorem martingale_gbLyap (hε : 0 < ε) (hxj : 0 < xR j) (hxd : xR i₀ < xR j) (εH : ℝ) :
    Martingale (fun t ω =>
      lyapObs k εH (coordG k xR G W VR B j i₀ (min t (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε ω) : ℝ≥0),
          Ito.itoGen (lyapObs k εH) (coordG k xR G W VR B j i₀ s.toNNReal ω,
            Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR j i₀ s ω))
      (usualAugmentation 𝓕 P) P := by
  set σ := gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε with hσdef
  have hB' := isFilteredBrownianReal_brownG_gb hE hGm hGc hgood
  have hlam : ∀ ω, IntervalIntegrable (densG ρL ρR G W VL VR j i₀ · ω) volume 0 (σ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [densG, hω, ↓reduceIte] using
        intervalIntegrable_densAt (hgood ω hω).1 (gbLoc_lt_lifetime (hgood ω hω))
    · simp only [densG, hω, ↓reduceIte]; exact intervalIntegrable_const
  have hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → coordG k xR G W VR B j i₀ t ω =
      coordG k xR G W VR B j i₀ 0 ω + ∫ s in (0 : ℝ)..t, densG ρL ρR G W VL VR j i₀ s ω := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · simp only [coordG, densG, hω, ↓reduceIte]
      exact coordAt_eq_add_integral (hgood ω hω).1 (hgood ω hω).2.2.1
        (lt_of_le_of_lt (by exact_mod_cast ht) (gbLoc_lt_lifetime (hgood ω hω)))
    · simp only [coordG, densG, hω, ↓reduceIte, intervalIntegral.integral_zero, add_zero]
  have hKb0 : 0 ≤ gbKb xL xR ρL ρR j i₀ n := by
    unfold gbKb
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 0 ≤ ∑ i, |ρL i| * ((|xL i| + n) / 2) :=
      sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by positivity)
    have h2 : 0 ≤ ∑ i, |ρR i| * ((n + |xR i|) / 2) :=
      sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by positivity)
    have := abs_nonneg (xR j); have := abs_nonneg (xR i₀)
    linarith
  have hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖densG ρL ρR G W VL VR j i₀ s ω‖ ≤
      gbKb xL xR ρL ρR j i₀ n := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [densG, hω, ↓reduceIte]
      rcases (zero_le (a := σ ω)).eq_or_lt with h0 | h0
      · rw [← h0, NNReal.coe_zero, intervalIntegral.integral_same]; exact hKb0
      have hO := levO_nonneg_of_le_gbLoc (hgood ω hω) hω h0 le_rfl
      simp only [levO, le_min_iff] at hO
      have hn : ‖Coupling.stateAt W VL VR (σ ω) ω‖ ≤ n := by linarith [hO.1.1]
      obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (Coupling.stateAt W VL VR (σ ω) ω)
      exact integral_norm_densAt_le (hgood ω hω).1 (gbLoc_lt_lifetime (hgood ω hω))
        (fun i => (hvL i).trans hn) (fun i => (hvR i).trans hn)
    · simp only [densG, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
      exact hKb0
  have hK : ∀ ω (t : ℝ≥0), t ≤ σ ω →
      (coordG k xR G W VR B j i₀ t ω, Sec2.TwoSeed.brownG G B t ω) ∈ gbKc k xR j i₀ n R ε := by
    intro ω t ht
    by_cases hω : ω ∈ G
    · exact mem_gbKc_of_le_gbLoc hgood hω ht
    · simp only [coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      exact mem_insert _ _
  exact Ito.martingale_itoLocalized hB' (continuous_brownG_gb hgood) isOpen_lyapRegion
    contDiffOn_lyapObs isCompact_gbKc (gbKc_subset_region hε hxj hxd)
    (isStoppingTime_gbLoc hE hGm hGc hgood hT) (measurable_coordG_gbLoc hE hGm hGc hgood hT)
    hlam hΛ hKb hK

end Ito

/-! ### The Lyapunov estimate -/

section Estimate

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {G : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {j : Fin nR} {n R : ℕ} {γ γ' ε : ℝ}

/-- The bound `|x_j| + 2n + 1` on `X_j` up to `σ`. -/
def gbCx (xR : Fin nR → ℝ) (j : Fin nR) (n : ℕ) : ℝ := |xR j| + 2 * n + 1

theorem gbCx_pos (xR : Fin nR → ℝ) (j : Fin nR) (n : ℕ) : 0 < gbCx xR j n := by
  unfold gbCx; positivity

theorem gbCst_nonneg (hk : 0 < k) {εH : ℝ} (hεH : 0 < εH) (hγ : 0 < γ) (hγ' : 0 < γ') :
    0 ≤ gbCst k εH γ γ' xL xR ρL j n := by
  unfold gbCst
  have := alphaC_pos hεH; have := expoC_pos hk; have := lamC_pos hk hεH
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine mul_nonneg (by positivity) (add_nonneg (mul_nonneg ?_ ?_) (mul_nonneg (by positivity) ?_))
  · exact div_nonneg (sum_nonneg fun i _ => abs_nonneg _) hγ.le
  · have := abs_nonneg (xR j); positivity
  · exact sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (by have := abs_nonneg (xL i); positivity)

/-- **The Lyapunov estimate.** Under the hypotheses of Lemma GB5 (`ε_H ≤ S_i + 2` for `i < j`, `S_i ≥ c` for
`i ≥ j`, `0 ≤ x_{i₀} < x_j`) and `0 < ε < C = gbCx`, the probability that `X_j` reaches `ε` before the outer
constraints fail, before `T_n` and before `|B|` reaches `n`, is at most `(F(0) + log C + gbCst)/log(C/ε)`; the bound
does not depend on `R`. -/
theorem measureReal_gbEvent_le (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsGBGood k xL xR ρL ρR W VL VR B ζ T ω)
    (hT : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (T n ω : WithTop ℝ≥0))
    (hTn : ∀ n ω, T n ω ≤ n) (hk : 0 < k) {εH : ℝ} (hεH : 0 < εH) (hnR : 0 < nR) (hxm : Monotone xR)
    (hin : ∀ i : Fin nR, i < j → (∀ i', i < i' → xR i < xR i') →
      εH ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l + 2)
    (hout : ∀ i : Fin nR, j ≤ i → (∀ i', i < i' → xR i < xR i') →
      k / 2 - 2 ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l)
    (hx0 : 0 ≤ xR ⟨0, hnR⟩) (hxd : xR ⟨0, hnR⟩ < xR j) (hγ : 0 < γ) (hγ' : 0 < γ') (hε : 0 < ε)
    (hεC : ε < gbCx xR j n) :
    P.real (gbEvent G W VL VR B ζ T j ⟨0, hnR⟩ n R γ γ' ε) ≤
      (lyapObs k εH (initPt xR j ⟨0, hnR⟩) + Real.log (gbCx xR j n) + gbCst k εH γ γ' xL xR ρL j n) /
        Real.log (gbCx xR j n / ε) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hxj : 0 < xR j := lt_of_le_of_lt hx0 hxd
  set i₀ : Fin nR := ⟨0, hnR⟩ with hi₀
  set σ := gbLoc G W VL VR B ζ T j i₀ n R γ γ' ε with hσdef
  set M : ℝ≥0 → Ω → ℝ := fun t ω =>
    lyapObs k εH (coordG k xR G W VR B j i₀ (min t (σ ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
        Ito.itoGen (lyapObs k εH) (coordG k xR G W VR B j i₀ s.toNNReal ω,
          Sec2.TwoSeed.brownG G B s.toNNReal ω) (densG ρL ρR G W VL VR j i₀ s ω) with hMdef
  have hM : Martingale M (usualAugmentation 𝓕 P) P :=
    martingale_gbLyap hE hGm hGc hgood hT hε hxj hxd εH
  set Φ0 := lyapObs k εH (initPt xR j i₀) with hΦ0
  set C := gbCst k εH γ γ' xL xR ρL j n with hC
  set Cx := gbCx xR j n with hCx
  have hC0 : 0 ≤ C := gbCst_nonneg hk hεH hγ hγ'
  have hCx0 : 0 < Cx := gbCx_pos xR j n
  -- the initial value
  have hM0 : ∀ ω, M 0 ω = Φ0 := by
    intro ω
    simp only [hMdef, zero_min, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    by_cases hω : ω ∈ G
    · have hF := (hgood ω hω).1.isForcePath
      have hw : W 0 ω = 0 := hF.w_zero
      have hj : VR j 0 ω = xR j := hF.vR_zero j
      have hi : VR i₀ 0 ω = xR i₀ := hF.vR_zero i₀
      simp only [coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte, coordAt, hw, hj, hi, (hgood ω hω).2.2.1,
        mul_zero, add_zero, sub_zero, hΦ0, initPt]
    · simp only [coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte, hΦ0, initPt]
  have hint : ∫ ω, M (n : ℝ≥0) ω ∂P = Φ0 := by
    have h := hM.setIntegral_eq (zero_le (a := (n : ℝ≥0))) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [← h]
    simp only [hM0, integral_const, probReal_univ, one_smul]
  -- pathwise bounds on good paths
  have hlow : ∀ ω ∈ G, -Real.log Cx - C ≤ M n ω ∧
      (ω ∈ gbEvent G W VL VR B ζ T j i₀ n R γ γ' ε → -Real.log ε - C ≤ M n ω) := by
    intro ω hω
    have hgω := hgood ω hω
    have hF := hgω.1.isForcePath
    have hσn : min (n : ℝ≥0) (σ ω) = σ ω := min_eq_right ((gbLoc_le_T ω).trans (hTn n ω))
    have hσζ := gbLoc_lt_lifetime (G := G) (j := j) (i₀ := i₀) (n := n) (R := R) (γ := γ) (γ' := γ')
      (ε := ε) hgω
    have hq := gbKc_subset_region hε hxj hxd (mem_gbKc_of_le_gbLoc hgood hω (le_refl (σ ω)))
    simp only [coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte] at hq
    -- the integrated generator
    have hgen : ∫ s in (0 : ℝ)..(σ ω), Ito.itoGen (lyapObs k εH)
        (coordG k xR G W VR B j i₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densG ρL ρR G W VL VR j i₀ s ω) ≤ C := by
      simp only [coordG, Sec2.TwoSeed.brownG, densG, hω, ↓reduceIte]
      rcases (zero_le (a := σ ω)).eq_or_lt with h0 | h0
      · rw [← h0, NNReal.coe_zero, intervalIntegral.integral_same]; exact hC0
      have hO : ∀ r ≤ σ ω, 0 ≤ levO j i₀ n R γ γ' (Coupling.stateAt W VL VR r ω) := fun r hr =>
        levO_nonneg_of_le_gbLoc hgω hω h0 hr
      have hOσ := hO (σ ω) le_rfl
      simp only [levO, le_min_iff] at hOσ
      have hn : ‖Coupling.stateAt W VL VR (σ ω) ω‖ ≤ n := by linarith [hOσ.1.1]
      obtain ⟨-, hvL, hvR⟩ := abs_le_norm_state (Coupling.stateAt W VL VR (σ ω) ω)
      refine integral_itoGen_le hgω.1 hk hεH hnR hxm hin hout hσζ (fun s hs => ?_) hγ hγ' (fun s hs h => ?_)
        (fun i => (hvL i).trans hn) ((hvR j).trans hn)
      · have := hO s hs
        simp only [levO, le_min_iff, dFun, Coupling.stateAt] at this
        have hR0 : (0 : ℝ) < 1 / ((R : ℝ) + 1) := by positivity
        linarith [this.1.2]
      · have := (hO s hs)
        simp only [levO, le_min_iff, leftFun, h, ↓reduceDIte, le_max_iff, xFun,
          Coupling.stateAt] at this
        rcases this.2 with h1 | h1
        · left; linarith
        · right; linarith
    -- `F ≥ −log x` and `x ≤ C_x`
    have hxσ : lyapX k (coordAt k j i₀ (W · ω) (fun i t => VR i t ω) (B · ω) (σ ω), B (σ ω) ω) =
        VR j (σ ω) ω - W (σ ω) ω := lyapX_coordAt k j i₀ _ _ _ _
    have hF0 : -Real.log (VR j (σ ω) ω - W (σ ω) ω) ≤ lyapObs k εH
        (coordAt k j i₀ (W · ω) (fun i t => VR i t ω) (B · ω) (σ ω), B (σ ω) ω) := by
      rw [← hxσ]; exact lyapF_ge hk hεH hq.1 hq.2
    have hxpos : 0 < VR j (σ ω) ω - W (σ ω) ω := hxσ ▸ hq.1
    have hxC : VR j (σ ω) ω - W (σ ω) ω ≤ Cx := by
      rcases (zero_le (a := σ ω)).eq_or_lt with h0 | h0
      · rw [← h0, hF.w_zero, hF.vR_zero j, sub_zero, hCx, gbCx]
        have := le_abs_self (xR j); have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      · have hOσ := levO_nonneg_of_le_gbLoc hgω hω h0 le_rfl
        simp only [levO, le_min_iff] at hOσ
        have hn : ‖Coupling.stateAt W VL VR (σ ω) ω‖ ≤ n := by linarith [hOσ.1.1]
        obtain ⟨hw, -, hvR⟩ := abs_le_norm_state (Coupling.stateAt W VL VR (σ ω) ω)
        simp only [Coupling.stateAt] at hw hvR
        have := le_abs_self (VR j (σ ω) ω); have := neg_abs_le (W (σ ω) ω)
        have := abs_nonneg (xR j)
        rw [hCx, gbCx]
        linarith [(hvR j).trans hn, hw.trans hn]
    have hMn : M n ω = lyapObs k εH
        (coordAt k j i₀ (W · ω) (fun i t => VR i t ω) (B · ω) (σ ω), B (σ ω) ω) -
        ∫ s in (0 : ℝ)..(σ ω), Ito.itoGen (lyapObs k εH)
          (coordG k xR G W VR B j i₀ s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
          (densG ρL ρR G W VL VR j i₀ s ω) := by
      simp only [hMdef, hσn, coordG, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    refine ⟨?_, fun hev => ?_⟩
    · have : -Real.log Cx ≤ -Real.log (VR j (σ ω) ω - W (σ ω) ω) :=
        neg_le_neg (Real.log_le_log hxpos hxC)
      rw [hMn]; linarith
    · -- on the event, `σ` is the hitting time of `{X_j < ε}`
      have heq := gbLoc_eq_hitX hev
      simp only [hitX, hω, ↓reduceIte] at heq
      have hle := Coupling.le_of_hitBelow_eq ((continuous_levX j ε).comp_continuousOn
        (continuousOn_stateAt_gb hgood hω)) heq.symm
      simp only [Function.comp_apply, levX, xFun, Coupling.stateAt] at hle
      have : -Real.log ε ≤ -Real.log (VR j (σ ω) ω - W (σ ω) ω) :=
        neg_le_neg (Real.log_le_log hxpos (by linarith))
      rw [hMn]; linarith
  -- Markov's inequality
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set f : Ω → ℝ := fun ω => M n ω + (Real.log Cx + C) with hf
  have hf0 : 0 ≤ᵐ[P] f := by
    filter_upwards [hGae] with ω hω
    have := (hlow ω hω).1
    simp only [hf, Pi.zero_apply]; linarith
  have hfi : Integrable f P := (hM.integrable n).add (integrable_const _)
  have hfint : ∫ ω, f ω ∂P = Φ0 + Real.log Cx + C := by
    simp only [hf]
    rw [integral_add (hM.integrable n) (integrable_const _), hint, integral_const, probReal_univ,
      one_smul]
    ring
  set c := Real.log (Cx / ε) with hc
  have hc0 : 0 < c := Real.log_pos ((one_lt_div hε).2 hεC)
  have hcl : c = Real.log Cx - Real.log ε := Real.log_div hCx0.ne' hε.ne'
  have hsub : gbEvent G W VL VR B ζ T j i₀ n R γ γ' ε ⊆ {ω | c ≤ f ω} := by
    intro ω hev
    have := (hlow ω hev.1).2 hev
    simp only [mem_ofPred_eq, hf, hcl]
    linarith
  have hmark := mul_meas_ge_le_integral_of_nonneg hf0 hfi c
  rw [hfint] at hmark
  have hmono : P.real (gbEvent G W VL VR B ζ T j i₀ n R γ γ' ε) ≤ P.real {ω | c ≤ f ω} :=
    measureReal_mono hsub
  rw [le_div_iff₀ hc0]
  nlinarith

end Estimate

end GB5

end Supp8

end InteractingSLE
