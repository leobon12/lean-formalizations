/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualObserved
import InteractingSLE.Spec.Restart.FlowStopIdentLLCont
import InteractingSLE.Spec.Sec7.LocalExtJCont

/-!
# A continuous adapted retained driver from its killed observations

Packet PROVE-RETPLUMB. The measurable stopped reader removes arbitrary choices
of extension after the lifetime. Killed-driver observability is stated separately
as an exact named mathematical input; it is not inferred from pointwise choice.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7 MartChar.RealFlow
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Stopping a continuous process from zero gives a globally continuous adapted
version as soon as its killed observations are adapted. -/
theorem exists_continuous_adapted_stopped {𝓗 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun q => X q ω) (h0 : ∀ ω, X 0 ω = 0)
    (ha : AdaptedBefore 𝓗 V X) :
    ∃ W : ℝ≥0 → Ω → ℝ, (∀ ω, W 0 ω = 0) ∧
      (∀ ω, Continuous fun q => W q ω) ∧ StronglyAdapted 𝓗 W ∧
      ∀ ω (q : ℝ≥0), (q : ℝ≥0∞) < V ω → W q ω = X q ω := by
  classical
  let S : Ω → WithTop ℝ≥0 := fun ω => (V ω : WithTop ℝ≥0)
  let W := LocalExt.stopVal X S
  have hz : ∀ ω, V ω = 0 → ∀ q, W q ω = 0 := by
    intro ω hω q
    have hzq (q : ℝ≥0) : ¬ (q : WithTop ℝ≥0) < 0 := by
      exact_mod_cast (not_lt_zero : ¬ q < 0)
    have hS : S ω = 0 := hω
    have hl : (fun n => LocalExt.lowVal X S n ω) = fun _ => 0 := by
      funext n
      rw [LocalExt.lowVal, hS, ite_eq_right (hzq _)]
    rw [show W q ω = LocalExt.stopVal X S q ω from rfl,
      LocalExt.stopVal, hS, ite_eq_right (hzq q), hl]
    exact (tendsto_const_nhds (x := (0 : ℝ))).limUnder_eq
  have hcW : ∀ ω, Continuous fun q => W q ω := by
    intro ω
    rcases eq_or_lt_of_le (zero_le : 0 ≤ V ω) with hV | hV
    · have he : (fun q => W q ω) = fun _ => 0 := funext (hz ω hV.symm)
      rw [he]
      exact continuous_const
    by_cases htop : V ω = ⊤
    · have he : (fun q => W q ω) = fun q => X q ω := by
        funext q
        simp only [W, LocalExt.stopVal, S, htop]
        split_ifs with hq
        · rfl
        · exact False.elim (hq (WithTop.coe_lt_top q))
      rw [he]
      exact hc ω
    · let T := (V ω).toNNReal
      have he : (T : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal htop
      have hT : 0 < T := ENNReal.coe_pos.1 (he.symm ▸ hV)
      have hS : S ω = T := by
        change (V ω : WithTop ℝ≥0) = _
        rw [← he]
        rfl
      exact FlowStopIdentLL.continuous_stopVal_of_tendsto hT hS (hc ω).continuousOn
        (((hc ω).tendsto T).mono_left nhdsWithin_le_nhds)
  refine ⟨W, ?_, hcW, ?_, ?_⟩
  · intro ω
    by_cases hV : V ω = 0
    · exact hz ω hV 0
    · have hVpos : 0 < V ω := pos_iff_ne_zero.2 hV
      simpa only [W, LocalExt.stopVal, S, show ((0 : ℝ≥0) : WithTop ℝ≥0) <
        (V ω : WithTop ℝ≥0) from hVpos, ↓reduceIte] using h0 ω
  · intro q
    exact (LocalExt.measurable_stopVal_le (Ito.isStoppingTime_lifetime ha) ha q).stronglyMeasurable
  · intro ω q hq
    exact ite_eq_left hq

/-- Later-line identities depend only on the driver through their capacity. -/
theorem IsRetLineFacts.congr {d d' : RetData Ω} {ω : Ω} {W W' : ℝ≥0 → ℝ}
    {Q : ℝ≥0} {κ θ : ℝ} {B₀ Bt : BoundaryWord}
    (h : IsRetLineFacts d d' ω W Q κ θ B₀ Bt) (hc : Continuous W) (hc' : Continuous W')
    (he : ∀ s ≤ Q, W s = W' s) : IsRetLineFacts d d' ω W' Q κ θ B₀ Bt := by
  have hcR := hc.comp continuous_real_toNNReal
  have hcR' := hc'.comp continuous_real_toNNReal
  have heR : EqOn (fun s : ℝ => W s.toNNReal) (fun s : ℝ => W' s.toNNReal) (Icc 0 (Q : ℝ)) := by
    intro s hs
    exact he s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hinv (z : ℂ) : QuantumZipper.fwdMapInv (fun s : ℝ => W s.toNNReal) Q z =
      QuantumZipper.fwdMapInv (fun s : ℝ => W' s.toNNReal) Q z :=
    LocalExt.fwdMapInv_congr_of_continuousOn (t' := (Q : ℝ) + 1) hcR.continuousOn hcR'.continuousOn
      Q.coe_nonneg (lt_add_one _) heR z
  have hlog (z : ℂ) : QuantumZipper.logDerivFwd (fun s : ℝ => W s.toNNReal) Q z =
      QuantumZipper.logDerivFwd (fun s : ℝ => W' s.toNNReal) Q z :=
    Ito.logDerivFwd_congr_of_eqOn heR Q.coe_nonneg le_rfl
  have hright (x : ℝ) : rightImg (fun s : ℝ => W s.toNNReal) x Q =
      rightImg (fun s : ℝ => W' s.toNNReal) x Q :=
    Sec7.Lemma71B.rightImg_congr hcR' Q.coe_nonneg heR x
  have hleft (x : ℝ) : rightImg (fun s : ℝ => -W s.toNNReal) x Q =
      rightImg (fun s : ℝ => -W' s.toNNReal) x Q :=
    Sec7.Lemma71B.rightImg_congr hcR'.neg Q.coe_nonneg (fun s hs => congrArg Neg.neg (heR hs)) x
  rcases h with ⟨hi, hl, S, hS, hB⟩
  refine ⟨?_, ?_, S, hS, ?_⟩
  · intro z hz
    rw [← hinv]
    exact hi z hz
  · intro z hz
    rw [← hinv, ← hlog]
    exact hl z hz
  · intro y hy
    simpa only [hright, hleft, he Q le_rfl] using hB y hy

/-- Changing only the post-lifetime extension preserves the retained driver. -/
theorem IsRetDriver.congr {G : ℝ≥0 → Set Ω} {η₁' η₂' : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {κ θ : ℝ} {c₀ : BoundaryWord}
    {g₃ g₄ : ℝ} {ω : Ω} {W W' : ℝ≥0 → ℝ} {x₂ : ℝ}
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : ω ∈ G r)
    (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (h : IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω W)
    (hc' : Continuous W') (h0' : W' 0 = 0)
    (he : ∀ q : ℝ≥0, (q : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω → W q = W' q) :
    IsRetDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ ω W' := by
  refine ⟨hc', h0', StoppedK2.isGeneratingTrace_congr he h.2.2.1, ?_⟩
  intro t ht htV hGt
  obtain ⟨hp, hE, hf⟩ := h.2.2.2 t ht htV hGt
  refine ⟨hp, hE, hf.congr h.1 hc' fun s hs => he s ?_⟩
  have hQ : (((chartClock (retChartPath G η₁' η₂' ζ₂ u r ω) t).toNNReal : ℝ≥0) : ℝ≥0∞) <
      retLife G η₁' η₂' ζ₂ u r ω := by
    rw [← retClock_eq hd hG hp₂ hpair t]
    exact (retClock_lt_retLife_iff hd hG hp₂ hpair).2 htV
  exact (ENNReal.coe_le_coe.2 hs).trans_lt hQ

/-- Exact remaining Borel reconstruction input. It observes the driver only
strictly before the supported lifetime, and places no condition on the arbitrary
post-lifetime extension chosen by `retDriver`. -/
def RetKilledDriverObservable (𝓗 : Filtration ℝ≥0 mΩ) (F : Set Ω)
    (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (u r : ℝ≥0) (κ θ : ℝ) (c₀ : BoundaryWord) (g₃ g₄ : ℝ) : Prop :=
  AdaptedBefore 𝓗 (F.indicator (retLife G η₁' η₂' ζ₂ u r))
    (retDriver G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄)

/-- Construct the globally continuous adapted retained driver by stopping its
killed observable version. Pointwise driver existence is the landed geometry. -/
theorem retAdaptedDriverExists_of_killedObservations
    {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω} {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {κ θ : ℝ} {c₀ : BoundaryWord} {g₃ g₄ x₁ x₂ : ℝ}
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood) (hG : F ⊆ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂) (hx : x₂ < x₁)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hκ : 0 < κ)
    (ho : RetKilledDriverObservable 𝓗 F G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄) :
    RetAdaptedDriverExists 𝓗 F G η₁' η₂' ζ₁ ζ₂ u r κ θ c₀ g₃ g₄ := by
  obtain ⟨W, hW0, hWc, hWa, he⟩ := exists_continuous_adapted_stopped
    (continuous_retDriver (G := G) (η₁' := η₁') (η₂' := η₂') (ζ₁ := ζ₁) (ζ₂ := ζ₂)
      (u := u) (r := r) (κ := κ) (θ := θ) (c₀ := c₀) (g₃ := g₃) (g₄ := g₄))
    retDriver_zero ho
  refine ⟨W, hW0, hWc, hWa, fun ω hω => ?_⟩
  have hdW := isRetDriver_retDriver (exists_isRetDriver hd (hG hω) (hp₁ ω hω)
    (hp₂ ω hω) hx (hpair ω hω) hc₀ hκ θ g₃ g₄)
  apply hdW.congr (hd r) (hG hω) (hp₂ ω hω) (hpair ω hω) (hWc ω) (hW0 ω)
  intro q hq
  exact (he ω q (by simpa only [indicator_of_mem hω] using hq)).symm

end InteractingSLE.Restart.RetAux79
