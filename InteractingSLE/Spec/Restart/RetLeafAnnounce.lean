/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RelClockAnnounce
import InteractingSLE.Spec.Coupling.SafeFamily

/-!
# Announcing a lifetime from a process that blows up before it, continuous only at positive times

Packet PROVE-T15-RET. PROVE-RETPLUMB's announcement input `RetBoundaryApproachObservable` asks for an
observable process that is continuous on the whole of `[0, ζ)` and unbounded before every finite `ζ`.
For the retained continuation this cannot be supplied by a natural geometric quantity: the continuation
starts on the boundary, so any reciprocal of a boundary distance is infinite at time `0`, and any
scale-invariant ratio oscillates near time `0`. This file removes the requirement at time `0`.

**Statement** (`exists_isAnnouncingSeq_of_blowup`). In a right-continuous filtration, let `ζ` be a stopping
time that is almost surely positive, and `X` a process that is observable before `ζ`, continuous at the
positive times before `ζ` (no condition at `t = 0`) and almost surely tends to `+∞` as `t ↑ ζ` when `ζ` is
finite. Then `ζ` has an announcing sequence.

**Proof.** For `k ∈ ℕ` restart at `s_k = 1/(k+1)`: on `{s_k < ζ}` the increment `X(t ∨ s_k) − X(s_k)` is
continuous on all of `[0, ζ)`, and the landed entrance-time announcement `RelClock.announce` of this
restarted process announces `ζ_k = ζ` on `{s_k < ζ}`, `ζ_k = ⊤` off it. As `k` grows, `ζ_k` decreases and
is eventually equal to `ζ` (`ζ > 0`). For each `k` choose an index `c_k` with
`P(a_{k,c_k} + s_k < ζ, a_{k,c_k} < k) ≤ 2^{-k}` (each restarted announcement converges pathwise). Put
`T_n = inf_k a_{k, n + c_k}`. It is a stopping time (countable infimum, right continuity), nondecreasing
in `n`, strictly below `ζ` (the restart with `s_k < ζ` is strictly below `ζ`), and by Borel–Cantelli almost
surely all but finitely many restarts are within `s_k` of `ζ` (or above `k`) already at `c_k`, while the
finitely many others converge; so `T_n ↑ ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetLeaf

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-! ### Restart times -/

/-- The restart times `1/(k+1)`. -/
def restartTime (k : ℕ) : ℝ≥0 := ((k : ℝ≥0) + 1)⁻¹

theorem restartTime_pos (k : ℕ) : 0 < restartTime k := by
  unfold restartTime
  positivity

theorem coe_restartTime (k : ℕ) : ((restartTime k : ℝ≥0) : ℝ≥0∞) = ((k : ℝ≥0∞) + 1)⁻¹ := by
  unfold restartTime
  rw [ENNReal.coe_inv (by positivity), ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]

theorem coe_restartTime_le (k : ℕ) : ((restartTime k : ℝ≥0) : ℝ≥0∞) ≤ (k : ℝ≥0∞)⁻¹ := by
  rw [coe_restartTime]
  exact ENNReal.inv_le_inv.2 le_self_add

theorem restartTime_anti {k k' : ℕ} (h : k ≤ k') :
    ((restartTime k' : ℝ≥0) : ℝ≥0∞) ≤ ((restartTime k : ℝ≥0) : ℝ≥0∞) := by
  rw [coe_restartTime, coe_restartTime]
  exact ENNReal.inv_le_inv.2 (add_le_add (by exact_mod_cast h) le_rfl)

/-- Some restart time lies before a positive time. -/
theorem exists_restartTime_lt {a : ℝ≥0∞} (ha : 0 < a) : ∃ k, ((restartTime k : ℝ≥0) : ℝ≥0∞) < a := by
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt ha.ne'
  exact ⟨n, lt_of_le_of_lt (coe_restartTime_le n) hn⟩

/-- All late restart times lie before a positive time. -/
theorem eventually_restartTime_lt {a : ℝ≥0∞} (ha : 0 < a) :
    ∃ K, ∀ k, K ≤ k → ((restartTime k : ℝ≥0) : ℝ≥0∞) < a := by
  obtain ⟨K, hK⟩ := exists_restartTime_lt ha
  exact ⟨K, fun k hk => lt_of_le_of_lt (restartTime_anti hk) hK⟩

/-! ### The restarted process and lifetime -/

/-- The lifetime restarted at `1/(k+1)`: `ζ` if alive then, `⊤` otherwise. -/
def restartLife (ζ : Ω → ℝ≥0∞) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  if ((restartTime k : ℝ≥0) : ℝ≥0∞) < ζ ω then ζ ω else ⊤

/-- The process restarted at `1/(k+1)`: its increment since then if alive then, `0` otherwise. -/
def restartProc (X : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (k : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ((restartTime k : ℝ≥0) : ℝ≥0∞) < ζ ω then X (max t (restartTime k)) ω - X (restartTime k) ω else 0

variable {X : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem le_restartLife (k : ℕ) (ω : Ω) : ζ ω ≤ restartLife ζ k ω := by
  unfold restartLife
  split_ifs
  · exact le_rfl
  · exact le_top

theorem restartLife_of_lt {k : ℕ} {ω : Ω} (h : ((restartTime k : ℝ≥0) : ℝ≥0∞) < ζ ω) :
    restartLife ζ k ω = ζ ω := by
  unfold restartLife
  rw [ite_eq_left h]

/-- The restarted process is continuous before the restarted lifetime. -/
theorem continuousOn_restartProc
    (hXc : ∀ ω, ContinuousOn (X · ω) {t | 0 < t ∧ (t : ℝ≥0∞) < ζ ω}) (k : ℕ) (ω : Ω) :
    ContinuousOn (restartProc X ζ k · ω) {t | (t : ℝ≥0∞) < restartLife ζ k ω} := by
  unfold restartProc restartLife
  split_ifs with h
  · have hmap : MapsTo (fun t : ℝ≥0 => max t (restartTime k)) {t | (t : ℝ≥0∞) < ζ ω}
        {t | 0 < t ∧ (t : ℝ≥0∞) < ζ ω} := fun t ht =>
      ⟨lt_of_lt_of_le (restartTime_pos k) (le_max_right _ _), by
        show ((max t (restartTime k) : ℝ≥0) : ℝ≥0∞) < ζ ω
        rw [ENNReal.coe_max]
        exact max_lt ht h⟩
    exact ((hXc ω).comp (continuous_id.max continuous_const).continuousOn hmap).sub continuousOn_const
  · exact continuousOn_const

/-- The restarted process is unbounded before every finite restarted lifetime. -/
theorem restartProc_unbounded {ω : Ω}
    (hblow : ζ ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω ∧
      ∀ t : ℝ≥0, s ≤ t → (t : ℝ≥0∞) < ζ ω → M < X t ω) (k : ℕ) :
    restartLife ζ k ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < restartLife ζ k ω ∧
      M < restartProc X ζ k s ω := by
  intro hne M
  by_cases h : ((restartTime k : ℝ≥0) : ℝ≥0∞) < ζ ω
  · rw [restartLife_of_lt h] at hne ⊢
    obtain ⟨s₀, hs₀, hM⟩ := hblow hne (M + X (restartTime k) ω)
    refine ⟨max s₀ (restartTime k), ?_, ?_⟩
    · rw [ENNReal.coe_max]
      exact max_lt hs₀ h
    · have hlt : ((max s₀ (restartTime k) : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        rw [ENNReal.coe_max]
        exact max_lt hs₀ h
      have h1 := hM (max s₀ (restartTime k)) (le_max_left _ _) hlt
      unfold restartProc
      rw [ite_eq_left h, max_eq_left (le_max_right s₀ (restartTime k))]
      linarith
  · exact absurd (by unfold restartLife; rw [ite_eq_right h]) hne

/-! ### Measurability -/

/-- The truncation of an observable process at its lifetime is measurable at each time. -/
theorem measurable_trunc (hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | ζ ω ≤ t})
    (hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ c < X t ω}) (t : ℝ≥0) :
    Measurable[𝓖 t] fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0 := by
  let _ : MeasurableSpace Ω := 𝓖 t
  refine measurable_of_Ioi fun c => ?_
  have e : (fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0) ⁻¹' Ioi c =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ c < X t ω} ∪ ({ω | ζ ω ≤ t} ∩ {_ω | c < 0}) := by
    ext ω
    simp only [mem_preimage, mem_Ioi, mem_union, mem_inter_iff, mem_ofPred_eq]
    by_cases h : (t : ℝ≥0∞) < ζ ω
    · rw [ite_eq_left h]
      exact ⟨fun hc => Or.inl ⟨h, hc⟩, fun hc => hc.elim (fun hc => hc.2) fun hc => absurd hc.1 (not_le.2 h)⟩
    · rw [ite_eq_right h]
      exact ⟨fun hc => Or.inr ⟨not_lt.1 h, hc⟩, fun hc => hc.elim (fun hc => absurd hc.1 h) fun hc => hc.2⟩
  rw [e]
  exact (hXa t c).union ((hζ t).inter (MeasurableSet.const _))

/-- The restarted process is observable before the restarted lifetime. -/
theorem measurableSet_restartProc (hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | ζ ω ≤ t})
    (hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ c < X t ω}) (k : ℕ)
    (t : ℝ≥0) (c : ℝ) :
    MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < restartLife ζ k ω ∧ c < restartProc X ζ k t ω} := by
  set s := restartTime k with hs
  rcases lt_or_ge t s with hts | hst
  · have e : {ω | (t : ℝ≥0∞) < restartLife ζ k ω ∧ c < restartProc X ζ k t ω} = {_ω | c < 0} := by
      ext ω
      simp only [mem_ofPred_eq, restartLife, restartProc, ← hs]
      by_cases h : (s : ℝ≥0∞) < ζ ω
      · rw [ite_eq_left h, ite_eq_left h, max_eq_right hts.le, sub_self]
        exact and_iff_right (lt_trans (by exact_mod_cast hts) h)
      · rw [ite_eq_right h, ite_eq_right h]
        exact and_iff_right ENNReal.coe_lt_top
    rw [e]
    exact MeasurableSet.const _
  · set f₁ : Ω → ℝ := fun ω => if (t : ℝ≥0∞) < ζ ω then X t ω else 0 with hf₁
    set f₂ : Ω → ℝ := fun ω => if (s : ℝ≥0∞) < ζ ω then X s ω else 0 with hf₂
    have hm₁ : Measurable[𝓖 t] f₁ := measurable_trunc hζ hXa t
    have hm₂ : Measurable[𝓖 t] f₂ := (measurable_trunc hζ hXa s).mono (𝓖.mono hst) le_rfl
    have hlive : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
      have : {ω | (t : ℝ≥0∞) < ζ ω} = {ω | ζ ω ≤ t}ᶜ := by
        ext ω
        simp only [mem_ofPred_eq, mem_compl_iff, not_le]
      rw [this]
      exact (hζ t).compl
    have hdead : MeasurableSet[𝓖 t] {ω | ζ ω ≤ s} := 𝓖.mono hst _ (hζ s)
    have e : {ω | (t : ℝ≥0∞) < restartLife ζ k ω ∧ c < restartProc X ζ k t ω} =
        ({ω | (t : ℝ≥0∞) < ζ ω} ∩ {ω | c < f₁ ω - f₂ ω}) ∪ ({ω | ζ ω ≤ s} ∩ {_ω | c < 0}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, restartLife, restartProc, ← hs, hf₁, hf₂]
      by_cases h : (s : ℝ≥0∞) < ζ ω
      · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, max_eq_left hst]
        constructor
        · rintro ⟨ht, hc⟩
          rw [ite_eq_left ht]
          exact Or.inl ⟨ht, hc⟩
        · rintro (⟨ht, hc⟩ | ⟨hd, -⟩)
          · rw [ite_eq_left ht] at hc
            exact ⟨ht, hc⟩
          · exact absurd hd (not_le.2 h)
      · rw [ite_eq_right h, ite_eq_right h]
        have ht : ¬ (t : ℝ≥0∞) < ζ ω := fun ht =>
          h (lt_of_le_of_lt (by exact_mod_cast hst) ht)
        constructor
        · rintro ⟨-, hc⟩
          exact Or.inr ⟨not_lt.1 h, hc⟩
        · rintro (⟨ht', -⟩ | ⟨-, hc⟩)
          · exact absurd ht' ht
          · exact ⟨ENNReal.coe_lt_top, hc⟩
    rw [e]
    refine (hlive.inter ?_).union (hdead.inter (MeasurableSet.const _))
    let _ : MeasurableSpace Ω := 𝓖 t
    exact measurableSet_lt measurable_const (hm₁.sub hm₂)

/-! ### The announcement -/

/-- **An almost surely positive lifetime with an observable process that blows up before it and is
continuous at positive times is announced** in a right-continuous filtration. -/
theorem exists_isAnnouncingSeq_of_blowup {P : Measure Ω} [IsFiniteMeasure P] [𝓖.IsRightContinuous]
    (hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | ζ ω ≤ t})
    (hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ c < X t ω})
    (hXc : ∀ ω, ContinuousOn (X · ω) {t | 0 < t ∧ (t : ℝ≥0∞) < ζ ω})
    (hpos : ∀ᵐ ω ∂P, 0 < ζ ω)
    (hblow : ∀ᵐ ω ∂P, ζ ω ≠ ⊤ → ∀ M : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω ∧
      ∀ t : ℝ≥0, s ≤ t → (t : ℝ≥0∞) < ζ ω → M < X t ω) :
    ∃ T : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq 𝓖 P ζ T := by
  set a : ℕ → ℕ → Ω → ℝ≥0 := fun k n => Sec7.RelClock.announce (restartProc X ζ k) (restartLife ζ k) n
    with ha
  have hst : ∀ k n, IsStoppingTime 𝓖 fun ω => ((a k n ω : ℝ≥0) : WithTop ℝ≥0) := fun k n =>
    Sec7.RelClock.isStoppingTime_announce (measurableSet_restartProc hζ hXa k)
      (continuousOn_restartProc hXc k) n
  have hmono : ∀ k ω, Monotone fun n => a k n ω := fun k ω => Sec7.RelClock.monotone_announce ω
  have hle : ∀ k ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ a k n ω := fun k ω t ht =>
    Sec7.RelClock.exists_le_announce (continuousOn_restartProc hXc k)
      (lt_of_lt_of_le ht (le_restartLife k ω))
  have hmeas : ∀ k n, Measurable (a k n) := fun k n => by
    refine measurable_of_Iic fun x => ?_
    have e : a k n ⁻¹' Iic x = {ω | ((a k n ω : ℝ≥0) : WithTop ℝ≥0) ≤ (x : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_ofPred_eq, WithTop.coe_le_coe]
    rw [e]
    exact 𝓖.le x _ ((hst k n).measurableSet_le x)
  have hζm : Measurable ζ := by
    refine measurable_of_Iic fun t => ?_
    induction t using ENNReal.recTopCoe with
    | top => simp only [Iic_top, preimage_univ, MeasurableSet.univ]
    | coe t => exact 𝓖.le t _ (hζ t)
  -- the bad events of the `k`-th restart at index `m`
  set B : ℕ → ℕ → Set Ω := fun k m =>
    {ω | ((a k m ω + restartTime k : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ ((a k m ω : ℝ≥0) : ℝ≥0∞) < k} with hB
  have hBm : ∀ k m, MeasurableSet (B k m) := fun k m =>
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp ((hmeas k m).add_const _)) hζm).inter
      (measurableSet_lt (measurable_coe_nnreal_ennreal.comp (hmeas k m)) measurable_const)
  have hBanti : ∀ k, Antitone (B k) := fun k m m' hmm' ω hω => by
    have h1 : ((a k m ω : ℝ≥0) : ℝ≥0∞) ≤ ((a k m' ω : ℝ≥0) : ℝ≥0∞) := by
      exact_mod_cast hmono k ω hmm'
    refine ⟨lt_of_le_of_lt ?_ hω.1, lt_of_le_of_lt h1 hω.2⟩
    exact_mod_cast add_le_add (hmono k ω hmm') le_rfl
  have hBinter : ∀ k, ⋂ m, B k m = ∅ := by
    intro k
    refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    rw [mem_iInter] at hω
    by_cases htop : ζ ω = ⊤
    · obtain ⟨m, hm⟩ := hle k ω (k : ℝ≥0) (by rw [htop]; exact ENNReal.coe_lt_top)
      have h2 := (hω m).2
      have : (k : ℝ≥0∞) ≤ ((a k m ω : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hm
      exact absurd h2 (not_lt.2 this)
    · have h0 := (hω 0).1
      set z : ℝ≥0 := (ζ ω).toNNReal with hz
      have hζz : ζ ω = (z : ℝ≥0∞) := (ENNReal.coe_toNNReal htop).symm
      have hlt0 : a k 0 ω + restartTime k < z := by
        rw [hζz] at h0
        exact_mod_cast h0
      have hrz : restartTime k ≤ z := le_trans le_add_self hlt0.le
      have htz : z - restartTime k < z := tsub_lt_self (lt_of_lt_of_le (restartTime_pos k) hrz)
        (restartTime_pos k)
      obtain ⟨m, hm⟩ := hle k ω (z - restartTime k) (by rw [hζz]; exact_mod_cast htz)
      have h1 := (hω m).1
      rw [hζz] at h1
      have h1' : a k m ω + restartTime k < z := by exact_mod_cast h1
      have h3 : z ≤ a k m ω + restartTime k := by
        calc z = z - restartTime k + restartTime k := (tsub_add_cancel_of_le hrz).symm
          _ ≤ a k m ω + restartTime k := add_le_add hm le_rfl
      exact absurd h1' (not_lt.2 h3)
  have hBlim : ∀ k, Tendsto (fun m => P (B k m)) atTop (𝓝 0) := fun k => by
    have h := tendsto_measure_iInter_atTop (μ := P) (fun m => (hBm k m).nullMeasurableSet) (hBanti k)
      ⟨0, measure_ne_top P _⟩
    rwa [hBinter k, measure_empty] at h
  have hc : ∀ k, ∃ m, P (B k m) ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    ((hBlim k).eventually (Iic_mem_nhds (ENNReal.pow_pos (by norm_num) k))).exists
  choose c hc using hc
  have hsum : ∑' k, P (B k (c k)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hc)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hBC := ae_eventually_notMem (μ := P) hsum
  -- the announcing sequence
  set T : ℕ → Ω → ℝ≥0 := fun n ω => ⨅ k, a k (n + c k) ω with hT
  have hTle : ∀ n ω k, T n ω ≤ a k (n + c k) ω := fun n ω k => ciInf_le (OrderBot.bddBelow _) k
  refine ⟨T, fun n => ?_, fun ω n n' hnn' => ?_, fun n => ?_, ?_⟩
  · -- stopping times
    refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
    have e : {ω | ((T n ω : ℝ≥0) : WithTop ℝ≥0) < (i : WithTop ℝ≥0)} =
        ⋃ k, {ω | ((a k (n + c k) ω : ℝ≥0) : WithTop ℝ≥0) < (i : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, WithTop.coe_lt_coe, hT]
      exact ciInf_lt_iff (OrderBot.bddBelow _)
    rw [e]
    exact MeasurableSet.iUnion fun k => (hst k (n + c k)).measurableSet_lt i
  · -- monotone
    exact ciInf_mono (OrderBot.bddBelow _) fun k => hmono k ω (by omega)
  · -- strictly before the lifetime
    filter_upwards [hpos, hblow] with ω hp hb
    obtain ⟨k, hk⟩ := exists_restartTime_lt hp
    have h1 := Sec7.RelClock.announce_lt (X := restartProc X ζ k) (ζ := restartLife ζ k)
      (restartProc_unbounded hb k) (n + c k)
    have h2 : ((a k (n + c k) ω : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      have h1' : ((a k (n + c k) ω : ℝ≥0) : ℝ≥0∞) < restartLife ζ k ω := h1
      rwa [restartLife_of_lt hk] at h1'
    exact lt_of_le_of_lt (by exact_mod_cast hTle n ω k) h2
  · -- every time before the lifetime is eventually passed
    filter_upwards [hBC] with ω hω t ht
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hω
    -- late restarts are within their restart time of `ζ`, or above `k`
    have hgap : ∃ K₁, ∀ k, K₁ ≤ k → ((t + restartTime k : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      by_cases htop : ζ ω = ⊤
      · exact ⟨0, fun k _ => by rw [htop]; exact ENNReal.coe_lt_top⟩
      · have hpos' : 0 < ζ ω - t := tsub_pos_of_lt ht
        obtain ⟨K₁, hK₁⟩ := eventually_restartTime_lt hpos'
        refine ⟨K₁, fun k hk => ?_⟩
        have h := hK₁ k hk
        rw [ENNReal.coe_add]
        exact lt_tsub_iff_left.1 h
    obtain ⟨K₁, hK₁⟩ := hgap
    obtain ⟨K₂, hK₂⟩ := exists_nat_ge (t : ℝ≥0)
    set K := max K₀ (max K₁ K₂) with hK
    have hlate : ∀ k, K ≤ k → t ≤ a k (c k) ω := by
      intro k hk
      have hnot := hK₀ k (le_trans (le_max_left _ _) hk)
      simp only [hB, mem_ofPred_eq, not_and_or, not_lt] at hnot
      rcases hnot with h | h
      · have hg := hK₁ k (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk)
        have h' := lt_of_lt_of_le hg h
        have h'' : t + restartTime k < a k (c k) ω + restartTime k := by exact_mod_cast h'
        exact (lt_of_add_lt_add_right h'').le
      · have hkK : (K₂ : ℝ≥0) ≤ (k : ℝ≥0) := by
          exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
        have h' : (k : ℝ≥0) ≤ a k (c k) ω := by exact_mod_cast h
        exact le_trans hK₂ (le_trans hkK h')
    choose m hm using fun k => hle k ω t ht
    refine ⟨(Finset.range K).sup m, le_ciInf fun k => ?_⟩
    by_cases hk : K ≤ k
    · exact le_trans (hlate k hk) (hmono k ω (by omega))
    · have hmk : m k ≤ (Finset.range K).sup m := Finset.le_sup (Finset.mem_range.2 (not_le.1 hk))
      exact le_trans (hm k) (hmono k ω (by omega))

end InteractingSLE.Restart.RetLeaf
