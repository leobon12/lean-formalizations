/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetLeafAnnounce

/-!
# Announcing the A-stop: a blowup before a contact, or an announced threshold

Packet PROVE-T15-ASTOP. The A-stop `V` of a retained continuation (first new contact with the retained union `A`
only, Lemma G7) is, in the continuation's chart, the first positive time the chart trace meets the closed chart image
`I_A` of `A`, or the continuation's threshold (its original terminal rule), whichever comes first. A natural blowup
process is `1/dist(γ(t), I_A)`: it is infinite at `t = 0` (the chart trace starts at `0 ∈ I_A`) and stays bounded near
a threshold end off `I_A`. PROVE-T15-RET's `Restart.RetLeaf.exists_isAnnouncingSeq_of_blowup` handles time `0` by
restarting at `1/(k+1)`, but needs the blowup at every finite lifetime. Here:

* **`exists_isAnnouncingSeq_of_restarts`**: the Borel–Cantelli selection of `exists_isAnnouncingSeq_of_blowup`,
  abstracted: from any doubly indexed family `a k n` of stopping times, nondecreasing in `n`, eventually above every
  time before `ζ` (almost surely), and strictly below `ζ` whenever the restart time `1/(k+1)` is (almost surely);
* **`exists_isAnnouncingSeq_of_blowup_or`**: a lifetime `ζ` is announced as soon as, almost surely at a finite `ζ`,
  either an observable process continuous at positive times blows up before `ζ`, or `ζ` equals an announced stopping
  time `ζ₂ ≥ ζ` (the candidates are `min (announce of the restarted process, n-th announcing time of ζ₂)`).

Provenance: the proof of `exists_isAnnouncingSeq_of_restarts` is the proof of
`Restart.RetLeaf.exists_isAnnouncingSeq_of_blowup` (`Spec/Restart/RetLeafAnnounce.lean`, PROVE-T15-RET) from its
measurability step on, with the announcing family a hypothesis, the property "eventually above every time before `ζ`"
only almost surely (so the bad events of a restart have null rather than empty intersection), and the strict
inequality taken from the hypothesis `hlt` instead of `announce_lt`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdAStop

open Restart.RetLeaf

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

/-- **An announcing sequence from restarted candidate sequences** (the selection step of
`Restart.RetLeaf.exists_isAnnouncingSeq_of_blowup`, abstracted). -/
theorem exists_isAnnouncingSeq_of_restarts {P : Measure Ω} [IsFiniteMeasure P] [𝓖.IsRightContinuous]
    {ζ : Ω → ℝ≥0∞} (hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | ζ ω ≤ t}) {a : ℕ → ℕ → Ω → ℝ≥0}
    (hst : ∀ k n, IsStoppingTime 𝓖 fun ω => ((a k n ω : ℝ≥0) : WithTop ℝ≥0))
    (hmono : ∀ k ω, Monotone fun n => a k n ω)
    (hle : ∀ᵐ ω ∂P, ∀ k (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ a k n ω)
    (hpos : ∀ᵐ ω ∂P, 0 < ζ ω)
    (hlt : ∀ᵐ ω ∂P, ∀ k n, ((restartTime k : ℝ≥0) : ℝ≥0∞) < ζ ω → ((a k n ω : ℝ≥0) : ℝ≥0∞) < ζ ω) :
    ∃ T : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq 𝓖 P ζ T := by
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
  have hBinter : ∀ k, P (⋂ m, B k m) = 0 := by
    intro k
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hle)
    show ¬ _
    intro hleω
    rw [mem_iInter] at hω
    by_cases htop : ζ ω = ⊤
    · obtain ⟨m, hm⟩ := hleω k (k : ℝ≥0) (by rw [htop]; exact ENNReal.coe_lt_top)
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
      obtain ⟨m, hm⟩ := hleω k (z - restartTime k) (by rw [hζz]; exact_mod_cast htz)
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
    rwa [hBinter k] at h
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
    filter_upwards [hpos, hlt] with ω hp hb
    obtain ⟨k, hk⟩ := exists_restartTime_lt hp
    exact lt_of_le_of_lt (by exact_mod_cast hTle n ω k) (hb k (n + c k) hk)
  · -- every time before the lifetime is eventually passed
    filter_upwards [hBC, hle] with ω hω hleω t ht
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
    choose m hm using fun k => hleω k t ht
    refine ⟨(Finset.range K).sup m, le_ciInf fun k => ?_⟩
    by_cases hk : K ≤ k
    · exact le_trans (hlate k hk) (hmono k ω (by omega))
    · have hmk : m k ≤ (Finset.range K).sup m := Finset.le_sup (Finset.mem_range.2 (not_le.1 hk))
      exact le_trans (hm k) (hmono k ω (by omega))

/-- **A lifetime is announced if, at a finite lifetime, either an observable process continuous at positive times
blows up before it, or it equals an announced stopping time `ζ₂ ≥ ζ`.** The candidates of
`exists_isAnnouncingSeq_of_restarts` are `min (announce of the process restarted at 1/(k+1), n) (b n)`. -/
theorem exists_isAnnouncingSeq_of_blowup_or {P : Measure Ω} [IsFiniteMeasure P] [𝓖.IsRightContinuous]
    {ζ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ} (hζ : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | ζ ω ≤ t})
    (hXa : ∀ (t : ℝ≥0) (c : ℝ), MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ c < X t ω})
    (hXc : ∀ ω, ContinuousOn (X · ω) {t | 0 < t ∧ (t : ℝ≥0∞) < ζ ω})
    (hpos : ∀ᵐ ω ∂P, 0 < ζ ω) {ζ₂ : Ω → ℝ≥0∞} {b : ℕ → Ω → ℝ≥0}
    (hb : Coupling.IsAnnouncingSeq 𝓖 P ζ₂ b) (hζ₂ : ∀ᵐ ω ∂P, ζ ω ≤ ζ₂ ω)
    (hblow : ∀ᵐ ω ∂P, ζ ω ≠ ⊤ → ζ ω = ζ₂ ω ∨ ∀ M : ℝ, ∃ s : ℝ≥0, (s : ℝ≥0∞) < ζ ω ∧
      ∀ t : ℝ≥0, s ≤ t → (t : ℝ≥0∞) < ζ ω → M < X t ω) :
    ∃ T : ℕ → Ω → ℝ≥0, Coupling.IsAnnouncingSeq 𝓖 P ζ T := by
  set a₀ : ℕ → ℕ → Ω → ℝ≥0 := fun k n => Sec7.RelClock.announce (restartProc X ζ k) (restartLife ζ k) n
    with ha₀
  refine exists_isAnnouncingSeq_of_restarts (a := fun k n ω => min (a₀ k n ω) (b n ω)) hζ (fun k n => ?_)
    (fun k ω n n' hnn' => ?_) ?_ hpos ?_
  · have h1 : IsStoppingTime 𝓖 fun ω => ((a₀ k n ω : ℝ≥0) : WithTop ℝ≥0) :=
      Sec7.RelClock.isStoppingTime_announce (measurableSet_restartProc hζ hXa k) (continuousOn_restartProc hXc k) n
    have h2 := h1.min (hb.1 n)
    have e : (fun ω => ((min (a₀ k n ω) (b n ω) : ℝ≥0) : WithTop ℝ≥0)) =
        fun ω => min ((a₀ k n ω : ℝ≥0) : WithTop ℝ≥0) ((b n ω : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun ω => WithTop.coe_min _ _
    rw [e]
    exact h2
  · exact min_le_min (Sec7.RelClock.monotone_announce ω hnn') (hb.2.1 ω hnn')
  · filter_upwards [hb.2.2.2, hζ₂] with ω hbω hζω k t ht
    obtain ⟨n₁, hn₁⟩ := Sec7.RelClock.exists_le_announce (continuousOn_restartProc hXc k)
      (lt_of_lt_of_le ht (le_restartLife k ω))
    obtain ⟨n₂, hn₂⟩ := hbω t (lt_of_lt_of_le ht hζω)
    exact ⟨max n₁ n₂, le_min (hn₁.trans (Sec7.RelClock.monotone_announce ω (le_max_left _ _)))
      (hn₂.trans (hb.2.1 ω (le_max_right _ _)))⟩
  · filter_upwards [hblow, ae_all_iff.2 hb.2.2.1] with ω hbl hbn k n hk
    by_cases htop : ζ ω = ⊤
    · rw [htop]
      exact ENNReal.coe_lt_top
    · rcases hbl htop with heq | hM
      · exact lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) ((hbn n).trans_eq heq.symm)
      · have h1 := Sec7.RelClock.announce_lt (X := restartProc X ζ k) (ζ := restartLife ζ k)
          (restartProc_unbounded (fun _ => hM) k) n
        have h2 : ((a₀ k n ω : ℝ≥0) : ℝ≥0∞) < ζ ω := by
          have h1' : ((a₀ k n ω : ℝ≥0) : ℝ≥0∞) < restartLife ζ k ω := h1
          rwa [restartLife_of_lt hk] at h1'
        exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) h2

end InteractingSLE.RLC.OrdAStop
