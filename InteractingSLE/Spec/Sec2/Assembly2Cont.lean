/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Exist

/-!
# Theorem 2.2: continuing a local evolution by the maximal solution after a stopping time

Packet PROVE-SEC2-PATCH3. Let `B` be a Brownian motion of a right-continuous filtration with every
path continuous, and `(W, V)` continuous adapted processes that almost surely form a local solution
of an ordered word up to `τ'`. Let `T < τ'` be a positive finite stopping time at which the word seen
from the driver is good (separated, ordered, non-threshold). After `T`, run the maximal local
solution from that word driven by the increments of `B` after `T`
(`Assembly2Max`). The concatenation is an integrated `SLE_a(ρ)` evolution
(`isIntegratedSLEEvolution_cont`):

* `isIntegratedSLEPath_maxCode_of_good`: the maximal solution is a solution of Definition 2.1 when
  its horizon is positive and it is not in a `BadSet`;
* `IsIntegratedSLEPath.concat_of_upTo`: a local solution followed by a solution of Definition 2.1
  from the state at `σ > 0` is a solution of Definition 2.1;
* almost surely the maximal solution after `T` is a solution (strong Markov property with a
  parameter, `ae_mem_of_strongMarkov`, and `Assembly2Life`);
* adaptedness: the state at time `t` after `T` is a measurable function of the state at `T`, of `T`
  and of the path of `B` on `[T, u]` for every `u > t` (locality of the maximal solution), so it is
  `𝓕_u`-measurable for every `u > t`, hence `𝓕_t`-measurable (right continuity).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace Assembly2

open Assembly QuantumZipper.StrongMarkov

variable {a : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The maximal solution is a solution of Definition 2.1** when its horizon is positive and its
state code is in no `BadSet` (deterministic). -/
theorem isIntegratedSLEPath_maxCode_of_good {s : MWord nL nR} (hs : GoodWord ρL ρR s)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) (h0 : 0 < lifeMax a ρL ρR s (enc g))
    (hN : ∀ N : ℕ, (maxCode a ρL ρR s (enc g)).2 ∉ BadSet ρL ρR N) :
    IsIntegratedSLEPath a s.1 s.2 ρL ρR (cw (maxCode a ρL ρR s (enc g)))
      (cvL (maxCode a ρL ρR s (enc g))) (cvR (maxCode a ρL ρR s (enc g))) g
      (lifeMax a ρL ρR s (enc g)) := by
  obtain ⟨hx, hproj⟩ := maxCode_mem (a := a) (ρL := ρL) (ρR := ρR) hs.1 (uc_enc_of_continuous hg)
  simp only [lProj, Prod.mk.injEq] at hproj
  obtain ⟨hw, hb, hζ⟩ := hproj
  have key := isIntegratedSLEPath_of_lRel hx (fun h => absurd (hζ.symm.trans h) h0.ne')
    fun h1 h2 hc => by
      by_contra hthr
      obtain ⟨N, hN'⟩ := ENNReal.exists_nat_gt h2.ne
      exact hN N ⟨h1, hN', hc, hthr⟩
  have hwL : wordL (maxCode a ρL ρR s (enc g)) = s.1 := congrArg Prod.fst hw
  have hwR : wordR (maxCode a ρL ρR s (enc g)) = s.2 := congrArg Prod.snd hw
  have hcb : cb (maxCode a ρL ρR s (enc g)) = g := by
    unfold cb
    rw [hb, dec_enc_of_continuous hg]
  rw [hwL, hwR, hcb, hζ] at key
  exact key

/-- The pairs (word, path) along which the maximal solution from a good word is good. -/
def GoodPair (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Set (MWord nL nR × (ℝ≥0 → ℝ)) :=
  {p | GoodWord ρL ρR p.1 → 0 < lifeMax a ρL ρR p.1 (enc p.2) ∧
    ∀ N : ℕ, (maxCode a ρL ρR p.1 (enc p.2)).2 ∉ BadSet ρL ρR N}

theorem measurableSet_goodPair : MeasurableSet (GoodPair (nL := nL) (nR := nR) a ρL ρR) := by
  have hf : Measurable fun p : MWord nL nR × (ℝ≥0 → ℝ) => (p.1, enc p.2) :=
    measurable_fst.prodMk (measurable_enc.comp measurable_snd)
  have hl : Measurable fun p : MWord nL nR × (ℝ≥0 → ℝ) => lifeMax a ρL ρR p.1 (enc p.2) := by
    have h := (measurable_lifeMax (a := a) (ρL := ρL) (ρR := ρR)).comp hf
    simpa only [Function.comp_def] using h
  have hm : Measurable fun p : MWord nL nR × (ℝ≥0 → ℝ) => maxCode a ρL ρR p.1 (enc p.2) := by
    have h := (measurable_maxCode (a := a) (ρL := ρL) (ρR := ρR)).comp hf
    simpa only [Function.comp_def] using h
  have e : GoodPair (nL := nL) (nR := nR) a ρL ρR =
      (Prod.fst ⁻¹' {s | GoodWord ρL ρR s})ᶜ ∪
        ({p | 0 < lifeMax a ρL ρR p.1 (enc p.2)} ∩
          ⋂ N : ℕ, (fun p : MWord nL nR × (ℝ≥0 → ℝ) =>
            (maxCode a ρL ρR p.1 (enc p.2)).2) ⁻¹' (BadSet ρL ρR N)ᶜ) := by
    ext p
    simp only [GoodPair, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage, mem_inter_iff,
      mem_iInter]
    tauto
  rw [e]
  exact (measurableSet_goodWord.preimage measurable_fst).compl.union
    ((measurableSet_lt measurable_const hl).inter (MeasurableSet.iInter fun N =>
      (measurable_snd.comp hm) (measurableSet_badSet N).compl))

/-- Along almost every path of `B`, the maximal solution from a fixed good word is good. -/
theorem ae_mem_goodPair {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] {B : ℝ≥0 → Ω → ℝ}
    (ha : 0 < a) (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (e : MWord nL nR) : ∀ᵐ ω ∂P, (e, fun t => B t ω) ∈ GoodPair a ρL ρR := by
  by_cases he : GoodWord ρL ρR e
  · have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕.le t) le_rfl
    have hpos : HasPosLife a ρL ρR P B :=
      hasPosLife ha hB.1.toIsPreBrownianReal (measurable_pi_iff.2 hBm)
    have hnot : ∀ᵐ ω ∂P, ∀ N : ℕ, (codeProc a ρL ρR e B ω).2 ∉ BadSet ρL ρR N := by
      rw [ae_all_iff]
      intro N
      exact measure_eq_zero_iff_ae_notMem.1 (measure_badSet_eq_zero hpos he hB hBc N)
    filter_upwards [hpos e he, hnot] with ω h0 hN
    exact fun _ => ⟨h0, hN⟩
  · exact ae_of_all _ fun ω h => absurd h he

theorem thr_sub_iff (w c : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR (w - c) (fun i => vL i - c) (fun j => vR j - c) ↔
      ForceWord.ThresholdCondition ρL ρR w vL vR := by
  unfold ForceWord.ThresholdCondition
  simp only [sub_left_inj]

/-- **A local solution followed by a solution of Definition 2.1** from the state at `0 < σ < τ₁`
(driven by the increments after `σ`) **is a solution of Definition 2.1** with lifetime `σ + ζ₂`. -/
theorem isIntegratedSLEPath_concat {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ}
    {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {b b' : ℝ≥0 → ℝ} {τ₁ ζ₂ : ℝ≥0∞}
    {σ : ℝ≥0} (h₁ : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ₁) (hσ : (σ : ℝ≥0∞) < τ₁)
    (hσ0 : 0 < σ)
    (h₂ : IsIntegratedSLEPath a (fun i => vL i σ - w σ) (fun j => vR j σ - w σ) ρL ρR w' vL' vR'
      b' ζ₂) (hb' : ∀ t, b' t = b (σ + t) - b σ) :
    IsIntegratedSLEPath a xL xR ρL ρR (concatAt σ w (w σ) w')
      (fun i => concatAt σ (vL i) (w σ) (vL' i)) (fun j => concatAt σ (vR j) (w σ) (vR' j)) b
      ((σ : ℝ≥0∞) + ζ₂) := by
  have hU := h₁.concat hσ (h₂.isSLEPathUpTo le_rfl) hb'
  have hp₂ := h₂.isForcePath
  refine ⟨hU.w_zero, hU.vL_zero, hU.vR_zero, hU.continuousOn_w, hU.continuousOn_vL,
    hU.continuousOn_vR, fun t ht => hU.antitone_vL ht, fun t ht => hU.vL_le_w ht,
    fun t ht => hU.w_le_vR ht, fun t ht => hU.monotone_vR ht, fun t ht => hU.integrable_gapL ht,
    fun t ht => hU.integrable_gapR ht, fun t ht => hU.w_eq ht, fun t ht => hU.vL_eq ht,
    fun t ht => hU.vR_eq ht, hU.volume_collisionL, hU.volume_collisionR,
    fun t ht => hU.not_threshold ht, fun h0 => ?_, fun T hT0 hT w₀ vL₀ vR₀ hlim => ?_⟩
  · have : (σ : ℝ≥0∞) = 0 := le_antisymm (h0 ▸ le_self_add) bot_le
    exact absurd (show σ = 0 by exact_mod_cast this) hσ0.ne'
  · have hσT : σ ≤ T := by
      have : (σ : ℝ≥0∞) ≤ T := by rw [hT]; exact le_self_add
      exact_mod_cast this
    have hζ₂ : ζ₂ = ((T - σ : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_sub, hT, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
    rcases eq_or_lt_of_le hσT with hTσ | hTσ
    · -- the second piece has lifetime `0`: the limit is the state at `σ`
      subst hTσ
      have hz : ζ₂ = 0 := by rw [hζ₂, tsub_self]; rfl
      have hthr := hp₂.threshold_of_eq_zero hz
      have hcont : ContinuousAt (fun t => (w t, fun i => vL i t, fun j => vR j t)) σ :=
        ((h₁.continuousOn_w.continuousAt ((isOpen_lt ENNReal.continuous_coe
          continuous_const).mem_nhds hσ)).prodMk ((continuousAt_pi.2 fun i =>
          (h₁.continuousOn_vL i).continuousAt ((isOpen_lt ENNReal.continuous_coe
          continuous_const).mem_nhds hσ)).prodMk (continuousAt_pi.2 fun j =>
          (h₁.continuousOn_vR j).continuousAt ((isOpen_lt ENNReal.continuous_coe
          continuous_const).mem_nhds hσ))))
      have : NeBot (𝓝[<] σ) := nhdsLT_neBot_of_exists_lt ⟨0, hσ0⟩
      have hlim' : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] σ)
          (𝓝 (w₀, vL₀, vR₀)) := by
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : t < σ := ht
        simp only [concatAt_of_lt ht']
      have e := tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) hlim'
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1, e2, e3⟩ := e
      rw [← e1, ← e2, ← e3]
      have := (thr_sub_iff (ρL := ρL) (ρR := ρR) (w σ) (w σ) (fun i => vL i σ)
        (fun j => vR j σ)).1
      rw [sub_self] at this
      exact this hthr
    · -- the limit at the end of the second piece
      set T₂ := T - σ with hT₂
      have hT₂0 : 0 < T₂ := tsub_pos_of_lt hTσ
      have hshift : Tendsto (fun s : ℝ≥0 => σ + s) (𝓝[<] T₂) (𝓝[<] T) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have : T = σ + T₂ := by rw [hT₂, add_tsub_cancel_of_le hσT]
          rw [this]
          exact (((continuous_const (y := σ)).add continuous_id).tendsto T₂).mono_left
            nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with s hs
          have hs' : s < T₂ := hs
          show σ + s < T
          calc σ + s < σ + T₂ := add_lt_add_right hs' σ
            _ = T := by rw [hT₂, add_tsub_cancel_of_le hσT]
      set c : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) := (w σ, fun _ => w σ, fun _ => w σ) with hcdef
      have hc := ((continuous_id.sub (continuous_const (y := c))).tendsto
        ((w₀, vL₀, vR₀) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))).comp (hlim.comp hshift)
      have h1 : ∀ (f g : ℝ≥0 → ℝ) (s : ℝ≥0), concatAt σ f (w σ) g (σ + s) = w σ + g s :=
        fun f g s => by rw [concatAt_of_le le_self_add, add_tsub_cancel_left]
      have hlim₂ : Tendsto (fun s => (w' s, fun i => vL' i s, fun j => vR' j s)) (𝓝[<] T₂)
          (𝓝 ((w₀, vL₀, vR₀) - c)) := by
        refine hc.congr fun s => ?_
        simp only [Function.comp_apply, id, Pi.sub_apply, h1, hcdef, Prod.mk_sub_mk]
        refine Prod.ext (by ring) (Prod.ext (funext fun i => by simp) (funext fun j => by simp))
      have := hp₂.threshold_of_tendsto hT₂0 hζ₂.symm hlim₂
      exact (thr_sub_iff (ρL := ρL) (ρR := ρR) w₀ (w σ) vL₀ vR₀).1 this
/-- The maximal horizon vanishes for a word that is not separated. -/
theorem lifeMax_eq_zero_of_not_sep {s : MWord nL nR} (hs : ¬ ∀ i j, s.1 i < s.2 j) (c : PCode) :
    lifeMax a ρL ρR s c = 0 := by
  classical
  unfold lifeMax
  refine le_antisymm (iSup₂_le fun n k => ?_) bot_le
  have : (s, c, (dyad n k : ℝ≥0∞)) ∉ LSet a ρL ρR := fun h => hs (sep_of_mem_lSet h)
  simp only [this, ↓reduceIte, le_refl]

/-! ### Continuation after a stopping time -/

section Cont

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The value of a continuous adapted process at a stopping time `≤ u` is `𝓕 u`-measurable. -/
theorem measurable_eval_le {X : ℝ≥0 → Ω → ℝ} (hXa : ∀ t, Measurable[𝓕 t] (X t))
    (hXc : ∀ ω, Continuous (X · ω)) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)) {u : ℝ≥0} (hρu : ∀ ω, ρ ω ≤ u) :
    Measurable[𝓕 u] fun ω => X (ρ ω) ω := by
  have hX : IsStronglyProgressive 𝓕 X := isStronglyProgressive_of_rightContinuous
    (fun t => (hXa t).stronglyMeasurable) fun ω _ => (hXc ω).continuousWithinAt
  have h := measurable_stoppedValue hX hρ
  have e : (fun ω => X (ρ ω) ω) = stoppedValue X fun ω => (ρ ω : WithTop ℝ≥0) := by
    funext ω; rfl
  rw [e]
  exact h.mono (hρ.measurableSpace_le_of_le_const fun ω => WithTop.coe_le_coe.2 (hρu ω)) le_rfl

theorem isStoppingTime_min_const {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (u : ℝ≥0) : IsStoppingTime 𝓕 fun ω => ((min (T ω) u : ℝ≥0) : WithTop ℝ≥0) := by
  have h := hT.min_const u
  have e : (fun ω => min ((T ω : WithTop ℝ≥0)) (u : WithTop ℝ≥0)) =
      fun ω => ((min (T ω) u : ℝ≥0) : WithTop ℝ≥0) := funext fun ω => (WithTop.coe_min _ _).symm
  rw [e] at h
  exact h

variable {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}

/-- The word at time `T` seen from the driver. -/
def contWord (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0) (ω : Ω) : MWord nL nR :=
  (fun i => VL i (T ω) ω - W (T ω) ω, fun j => VR j (T ω) ω - W (T ω) ω)

variable (a ρL ρR) in
/-- The maximal solution after `T`, driven by the increments of `B` after `T`. -/
def contCode (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) : XCode nL nR :=
  maxCode a ρL ρR (contWord W VL VR T ω) (enc (smPath B T ω))

variable (a ρL ρR) in
/-- The maximal horizon after `T`. -/
def contLife (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  lifeMax a ρL ρR (contWord W VL VR T ω) (enc (smPath B T ω))

theorem measurable_contWord_le (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hVLa : ∀ i t, Measurable[𝓕 t] (VL i t)) (hVRa : ∀ j t, Measurable[𝓕 t] (VR j t))
    (hWc : ∀ ω, Continuous (W · ω)) (hVLc : ∀ i ω, Continuous (VL i · ω))
    (hVRc : ∀ j ω, Continuous (VR j · ω)) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓕 fun ω => (ρ ω : WithTop ℝ≥0)) {u : ℝ≥0} (hρu : ∀ ω, ρ ω ≤ u) :
    Measurable[𝓕 u] (contWord W VL VR ρ) := by
  let _ : MeasurableSpace Ω := 𝓕 u
  have hw := measurable_eval_le hWa hWc hρ hρu
  exact (measurable_pi_iff.2 fun i => (measurable_eval_le (hVLa i) (hVLc i) hρ hρu).sub hw).prodMk
    (measurable_pi_iff.2 fun j => (measurable_eval_le (hVRa j) (hVRc j) hρ hρu).sub hw)

/-- The word at `T` is `𝓕_T`-measurable. -/
theorem measurable_contWord (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hVLa : ∀ i t, Measurable[𝓕 t] (VL i t)) (hVRa : ∀ j t, Measurable[𝓕 t] (VR j t))
    (hWc : ∀ ω, Continuous (W · ω)) (hVLc : ∀ i ω, Continuous (VL i · ω))
    (hVRc : ∀ j ω, Continuous (VR j · ω))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) :
    Measurable[hT.measurableSpace] (contWord W VL VR T) := by
  have hprog : ∀ {X : ℝ≥0 → Ω → ℝ}, (∀ t, Measurable[𝓕 t] (X t)) → (∀ ω, Continuous (X · ω)) →
      Measurable[hT.measurableSpace] fun ω => X (T ω) ω := fun {X} hXa hXc => by
    have hX : IsStronglyProgressive 𝓕 X := isStronglyProgressive_of_rightContinuous
      (fun t => (hXa t).stronglyMeasurable) fun ω _ => (hXc ω).continuousWithinAt
    have e : (fun ω => X (T ω) ω) = stoppedValue X fun ω => (T ω : WithTop ℝ≥0) := by
      funext ω; rfl
    rw [e]
    exact measurable_stoppedValue hX hT
  let _ : MeasurableSpace Ω := hT.measurableSpace
  have hw := hprog hWa hWc
  exact (measurable_pi_iff.2 fun i => (hprog (hVLa i) (hVLc i)).sub hw).prodMk
    (measurable_pi_iff.2 fun j => (hprog (hVRa j) (hVRc j)).sub hw)

end Cont

/-- The state code of a code read at a time depending measurably on a parameter. -/
theorem measurable_stateAt_comp {α : Type*} [MeasurableSpace α] {f : α → XCode nL nR}
    {r : α → ℝ≥0} (hf : Measurable f) (hr : Measurable r) :
    Measurable fun p => stateAt (f p) (r p) := by
  have hd : ∀ {g : α → PCode}, Measurable g → Measurable fun p => dec (g p) (r p) := fun hg =>
    measurable_dec.comp (hg.prodMk hr)
  exact (hd (measurable_code_w.comp hf)).prodMk ((measurable_pi_iff.2 fun i =>
    hd ((measurable_code_vL i).comp hf)).prodMk (measurable_pi_iff.2 fun j =>
      hd ((measurable_code_vR j).comp hf)))

/-- A state shifted by `c`. -/
def shiftState (c : ℝ) (q : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (c + q.1, fun i => c + q.2.1 i, fun j => c + q.2.2 j)

theorem measurable_shiftState :
    Measurable fun p : ℝ × (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) => shiftState p.1 p.2 :=
  (measurable_fst.add (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_pi_iff.2 fun i => measurable_fst.add ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
    (measurable_pi_iff.2 fun j => measurable_fst.add ((measurable_pi_apply j).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

theorem coe_lt_add_iff {T t : ℝ≥0} (h : T ≤ t) {ℓ : ℝ≥0∞} :
    (t : ℝ≥0∞) < (T : ℝ≥0∞) + ℓ ↔ ((t - T : ℝ≥0) : ℝ≥0∞) < ℓ := by
  have e : (t : ℝ≥0∞) = (T : ℝ≥0∞) + ((t - T : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le h]
  rw [e, ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top]

section ContMain

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}

/-- The increments of `B` after `min T u`, stopped at `u`. -/
def stopIncr (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ≥0 → ℝ :=
  fun r => B (min (T ω + r) u) ω - B (min (T ω) u) ω

theorem measurable_enc_stopIncr (hBa : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (u : ℝ≥0) : Measurable[𝓕 u] fun ω => enc (stopIncr B T u ω) := by
  let _ : MeasurableSpace Ω := 𝓕 u
  refine measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_
  show Measurable fun ω => B (min (T ω + dyad n k) u) ω - B (min (T ω) u) ω
  exact (measurable_eval_le hBa hBc (isStoppingTime_min_const
    (Restart.isStoppingTime_add_const hT _) u) fun _ => min_le_right _ _).sub
    (measurable_eval_le hBa hBc (isStoppingTime_min_const hT u) fun _ => min_le_right _ _)

/-- The state after `T` at time `t`, as a measurable predicate of (word, shift, start, code). -/
def AfterPred (a : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (t : ℝ≥0)
    (D : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (p : MWord nL nR × ℝ × ℝ≥0 × PCode) : Prop :=
  p.2.2.1 ≤ t ∧ (((t - p.2.2.1 : ℝ≥0)) : ℝ≥0∞) < lifeMax a ρL ρR p.1 p.2.2.2 ∧
    shiftState p.2.1 (stateAt (maxCode a ρL ρR p.1 p.2.2.2) (t - p.2.2.1)) ∈ D

theorem measurableSet_afterPred (t : ℝ≥0) {D : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    (hD : MeasurableSet D) : MeasurableSet {p | AfterPred (nL := nL) (nR := nR) a ρL ρR t D p} := by
  have hσ : Measurable fun p : MWord nL nR × ℝ × ℝ≥0 × PCode => p.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hc : Measurable fun p : MWord nL nR × ℝ × ℝ≥0 × PCode => p.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hf : Measurable fun p : MWord nL nR × ℝ × ℝ≥0 × PCode => (p.1, p.2.2.2) :=
    measurable_fst.prodMk hc
  have hl : Measurable fun p : MWord nL nR × ℝ × ℝ≥0 × PCode => lifeMax a ρL ρR p.1 p.2.2.2 := by
    have h := (measurable_lifeMax (a := a) (ρL := ρL) (ρR := ρR)).comp hf
    simpa only [Function.comp_def] using h
  have hm : Measurable fun p : MWord nL nR × ℝ × ℝ≥0 × PCode => maxCode a ρL ρR p.1 p.2.2.2 := by
    have h := (measurable_maxCode (a := a) (ρL := ρL) (ρR := ρR)).comp hf
    simpa only [Function.comp_def] using h
  have hr : Measurable fun p : MWord nL nR × ℝ × ℝ≥0 × PCode => t - p.2.2.1 :=
    measurable_const.sub hσ
  refine (measurableSet_le hσ measurable_const).inter ((measurableSet_lt
    (measurable_coe_nnreal_ennreal.comp hr) hl).inter ?_)
  exact (measurable_shiftState.comp ((measurable_fst.comp measurable_snd).prodMk
    (measurable_stateAt_comp hm hr))) hD

end ContMain

section ContThm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0}

variable (a ρL ρR) in
/-- The continued state at time `t`: the local solution before `T`, the maximal solution after. -/
def contState (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (concatAt (T ω) (W · ω) (W (T ω) ω) (cw (contCode a ρL ρR W VL VR B T ω)) t,
    fun i => concatAt (T ω) (VL i · ω) (W (T ω) ω) (cvL (contCode a ρL ρR W VL VR B T ω) i) t,
    fun j => concatAt (T ω) (VR j · ω) (W (T ω) ω) (cvR (contCode a ρL ρR W VL VR B T ω) j) t)

/-- The predicate after `T` does not change when the path of `B` after `T` is stopped at `u > t`. -/
theorem afterPred_stopIncr (hBc : ∀ ω, Continuous (B · ω)) {t u : ℝ≥0} (htu : t < u)
    {D : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (ω : Ω) :
    AfterPred a ρL ρR t D (contWord W VL VR (fun ω => min (T ω) u) ω, W (min (T ω) u) ω,
        min (T ω) u, enc (stopIncr B T u ω)) ↔
      AfterPred a ρL ρR t D (contWord W VL VR T ω, W (T ω) ω, T ω, enc (smPath B T ω)) := by
  by_cases hTt : T ω ≤ t
  · have hmin : min (T ω) u = T ω := min_eq_left (hTt.trans htu.le)
    have hw : contWord W VL VR (fun ω => min (T ω) u) ω = contWord W VL VR T ω := by
      simp only [contWord, hmin]
    rw [hw, hmin]
    have hg : Continuous (smPath B T ω) :=
      ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    have hg' : Continuous (stopIncr B T u ω) :=
      ((hBc ω).comp ((continuous_const.add continuous_id).min continuous_const)).sub
        continuous_const
    have heq : ∀ r ≤ u - T ω, dec (enc (stopIncr B T u ω)) r = dec (enc (smPath B T ω)) r :=
      fun r hr => by
        rw [dec_enc_of_continuous hg, dec_enc_of_continuous hg']
        have : T ω + r ≤ u := by
          calc T ω + r ≤ T ω + (u - T ω) := add_le_add_right hr _
            _ = u := add_tsub_cancel_of_le (hTt.trans htu.le)
        simp only [stopIncr, smPath, smShift, min_eq_left this, hmin]
    have htr : t - T ω < u - T ω := tsub_lt_tsub_right_of_le hTt htu
    by_cases hs : ∀ i j, (contWord W VL VR T ω).1 i < (contWord W VL VR T ω).2 j
    · obtain ⟨hiff, hk⟩ := lt_lifeMax_iff_of_eqOn (a := a) (ρL := ρL) (ρR := ρR) hs
        (uc_enc_of_continuous hg) (uc_enc_of_continuous hg') heq htr
      unfold AfterPred
      simp only
      refine and_congr_right fun _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hiff.1 h1, by rw [← hk (hiff.1 h1)]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨hiff.2 h1, by rw [hk h1]; exact h2⟩
    · unfold AfterPred
      simp only [lifeMax_eq_zero_of_not_sep hs, ENNReal.not_lt_zero, false_and, and_false]
  · have h1 : ¬ min (T ω) u ≤ t := fun h => by
      rcases min_le_iff.1 h with h' | h'
      · exact hTt h'
      · exact absurd htu (not_lt.2 h')
    unfold AfterPred
    simp only [h1, hTt, false_and]

/-- **The continued state is adapted.** -/
theorem measurableSet_contState (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hVLa : ∀ i t, Measurable[𝓕 t] (VL i t)) (hVRa : ∀ j t, Measurable[𝓕 t] (VR j t))
    (hWc : ∀ ω, Continuous (W · ω)) (hVLc : ∀ i ω, Continuous (VL i · ω))
    (hVRc : ∀ j ω, Continuous (VR j · ω)) (hBa : ∀ t, Measurable[𝓕 t] (B t))
    (hBc : ∀ ω, Continuous (B · ω)) (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (t : ℝ≥0) {D : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hD : MeasurableSet D) :
    MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < (T ω : ℝ≥0∞) + contLife a ρL ρR W VL VR B T ω ∧
      contState a ρL ρR W VL VR B T t ω ∈ D} := by
  have hTle : MeasurableSet[𝓕 t] {ω | T ω ≤ t} := by
    have := hT.measurableSet_le t
    simp only [WithTop.coe_le_coe] at this
    exact this
  have e : {ω | (t : ℝ≥0∞) < (T ω : ℝ≥0∞) + contLife a ρL ρR W VL VR B T ω ∧
      contState a ρL ρR W VL VR B T t ω ∈ D} =
      ({ω | T ω ≤ t}ᶜ ∩ {ω | (W t ω, fun i => VL i t ω, fun j => VR j t ω) ∈ D}) ∪
        {ω | AfterPred a ρL ρR t D (contWord W VL VR T ω, W (T ω) ω, T ω, enc (smPath B T ω))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    by_cases hTt : T ω ≤ t
    · have hc : ∀ (f g : ℝ≥0 → ℝ), concatAt (T ω) f (W (T ω) ω) g t =
          W (T ω) ω + g (t - T ω) := fun f g => concatAt_of_le hTt
      simp only [contState, hc, coe_lt_add_iff hTt, AfterPred, hTt, true_and, not_true_eq_false,
        false_and, false_or, contLife, contCode, shiftState, stateAt]
    · have hlt : t < T ω := not_le.1 hTt
      have hc : ∀ (f g : ℝ≥0 → ℝ), concatAt (T ω) f (W (T ω) ω) g t = f t := fun f g =>
        concatAt_of_lt hlt
      have hζ : (t : ℝ≥0∞) < (T ω : ℝ≥0∞) + contLife a ρL ρR W VL VR B T ω :=
        lt_of_lt_of_le (by exact_mod_cast hlt) le_self_add
      simp only [contState, hc, hζ, true_and, AfterPred, hTt, not_false_eq_true, false_and,
        or_false]
  rw [e]
  refine (hTle.compl.inter ?_).union ?_
  · let _ : MeasurableSpace Ω := 𝓕 t
    exact ((hWa t).prodMk ((measurable_pi_iff.2 fun i => hVLa i t).prodMk
      (measurable_pi_iff.2 fun j => hVRa j t))) hD
  · refine measurableSet_of_forall_gt fun u htu => ?_
    have e2 : {ω | AfterPred a ρL ρR t D (contWord W VL VR T ω, W (T ω) ω, T ω,
        enc (smPath B T ω))} = (fun ω => (contWord W VL VR (fun ω => min (T ω) u) ω,
          W (min (T ω) u) ω, min (T ω) u, enc (stopIncr B T u ω))) ⁻¹'
          {p | AfterPred a ρL ρR t D p} := by
      ext ω
      exact (afterPred_stopIncr hBc htu ω).symm
    rw [e2]
    have hTu := isStoppingTime_min_const hT u
    let _ : MeasurableSpace Ω := 𝓕 u
    have hm : Measurable fun ω => (contWord W VL VR (fun ω => min (T ω) u) ω,
        W (min (T ω) u) ω, min (T ω) u, enc (stopIncr B T u ω)) :=
      (measurable_contWord_le hWa hVLa hVRa hWc hVLc hVRc hTu fun _ => min_le_right _ _).prodMk
        ((measurable_eval_le hWa hWc hTu fun _ => min_le_right _ _).prodMk
          ((measurable_coe_nnreal_ennreal_iff.1 (hTu.measurable_of_le fun _ =>
            WithTop.coe_le_coe.2 (min_le_right _ _))).prodMk (measurable_enc_stopIncr hBa hBc hT u)))
    exact hm (measurableSet_afterPred t hD)

/-- **Continuation by the maximal solution after a stopping time.** Let `B` be a Brownian motion of
the right-continuous filtration `𝓕` with every path continuous, `(W, V)` continuous adapted processes
that almost surely form a local solution of the ordered word `(xL; xR)` up to `τ'`, and `T < τ'` a
positive finite stopping time at which the word seen from the driver is almost surely good. Then
the local solution before `T`, followed by the maximal local solution driven by the increments of
`B` after `T`, is an integrated `SLE_a(ρ)` evolution. -/
theorem isIntegratedSLEEvolution_cont (ha : 0 < a) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hVLa : ∀ i t, Measurable[𝓕 t] (VL i t)) (hVRa : ∀ j t, Measurable[𝓕 t] (VR j t))
    (hWc : ∀ ω, Continuous (W · ω)) (hVLc : ∀ i ω, Continuous (VL i · ω))
    (hVRc : ∀ j ω, Continuous (VR j · ω)) {τ' : Ω → ℝ≥0∞}
    (hpath : ∀ᵐ ω ∂P, IsSLEPathUpTo a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (τ' ω))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hTτ' : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < τ' ω) (hT0 : ∀ ω, 0 < T ω)
    (hgood : ∀ᵐ ω ∂P, GoodWord ρL ρR (contWord W VL VR T ω)) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕
      (fun t ω => (contState a ρL ρR W VL VR B T t ω).1)
      (fun i t ω => (contState a ρL ρR W VL VR B T t ω).2.1 i)
      (fun j t ω => (contState a ρL ρR W VL VR B T t ω).2.2 j) B
      (fun ω => (T ω : ℝ≥0∞) + contLife a ρL ρR W VL VR B T ω) := by
  have hBa : ∀ t, Measurable[𝓕 t] (B t) := hB.2.1
  have hξ := measurable_contWord hWa hVLa hVRa hWc hVLc hVRc hT
  have hgp := ae_mem_of_strongMarkov hB hBc hT hξ (measurableSet_goodPair (a := a) (ρL := ρL)
    (ρR := ρR)) (ae_mem_goodPair ha hB hBc)
  refine ⟨hB, fun t A hA => ?_, fun i t A hA => ?_, fun j t A hA => ?_, ?_⟩
  · exact measurableSet_contState hWa hVLa hVRa hWc hVLc hVRc hBa hBc hT t (measurable_fst hA)
  · exact measurableSet_contState hWa hVLa hVRa hWc hVLc hVRc hBa hBc hT t
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) hA)
  · exact measurableSet_contState hWa hVLa hVRa hWc hVLc hVRc hBa hBc hT t
      (((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)) hA)
  · filter_upwards [hpath, hTτ', hgood, hgp] with ω hp hTτ hg hgp'
    obtain ⟨h0, hN⟩ := hgp' hg
    have hgc : Continuous (smPath B T ω) :=
      ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
    have h₂ := isIntegratedSLEPath_maxCode_of_good (a := a) hg hgc h0 hN
    exact isIntegratedSLEPath_concat hp hTτ (hT0 ω) h₂ fun t => rfl

end ContThm

end Assembly2

end Sec2

end InteractingSLE
