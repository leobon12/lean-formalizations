import InteractingSLE.Spec.Coupling.SafeEnergy
import InteractingSLE.Spec.Ito.Exhaust
import InteractingSLE.Spec.Ito.ExhaustMart

/-!
# Safe stops for a compact set

Packet PROVE-T11-L312 (Specification §3.3, L559–L565, graph node `SPEC.thm-1.1#safe-stops`): the safe stops
`s_{U,n} = T_n ∧ inf{t : inf_{z ∈ Ū} Im g_t(z) ≤ n⁻¹}`. Here a compact set `K ⊆ ℍ` (for instance `Ū` or the
support of a test function) is kept at height `≥ m/(n+1)` up to the stop, below a given nondecreasing sequence of
stopping times `σ₀ n < ζ` (`T_n` in the source; for one stopping time `τ < ζ`, the truncations `τ ∧ n`).

For one path, `IsSafeAt K δ N σ₀ ζ w t` says: `t < ζ`, `t ≤ σ₀`, `t ≤ N`, and every `z ∈ K` is alive at `t` with
`Im f_t(z) ≥ δ`. It is antitone in `t` (`IsSafeAt.anti`), so its failure set is an up-set and the exit time
`safeExitTime` is a stopping time of a right-continuous filtration as soon as the condition at a fixed time is
measurable. That is checked on a countable dense subset `D ⊆ K` (`isSafeAt_iff_of_dense`: a point of `K` whose
nearby points of `D` stay at height `≥ δ` is alive, by the hull criterion `FwdClock.mem_fwdHull_iff_inf_im` and the
continuity of `f_s` off the hull).

## Main results

* `IsSafeAt.anti`, `isSafeAt_iff_of_dense`, `isSafeAt_safeExitTime` (the condition holds at the exit time),
  `eventually_le_safeExitTime` (exhaustion: every horizon at which `K` is alive lies below the exit times of all
  large levels);
* `exists_safeSeq_of_seq`: the safe stops as stopping times of the usual augmentation.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

/-! ### The safe condition along one path -/

section Path

variable {K D : Set ℂ} {δ N : ℝ} {σ₀ : ℝ≥0} {ζ : ℝ≥0∞} {w : ℝ≥0 → ℝ}

/-- **The safe condition** for a set `K` at time `t` along the driving path `w`: `t < ζ`, `t ≤ σ₀`, `t ≤ N`, and every
`z ∈ K` is alive at `t` with `δ ≤ Im f_t(z)`. -/
def IsSafeAt (K : Set ℂ) (δ N : ℝ) (σ₀ : ℝ≥0) (ζ : ℝ≥0∞) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  (t : ℝ≥0∞) < ζ ∧ t ≤ σ₀ ∧ (t : ℝ) ≤ N ∧
    ∀ z ∈ K, (∃ u, IsForwardSol (rpath w) z t u) ∧ δ ≤ (fwdMap (rpath w) t z).im

/-- **The safe exit time**: the infimum of the times at which the safe condition fails. -/
def safeExitTime (K : Set ℂ) (δ N : ℝ) (σ₀ : ℝ≥0) (ζ : ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℝ≥0 :=
  sInf {t | ¬ IsSafeAt K δ N σ₀ ζ w t}

theorem IsSafeAt.lt_zeta {t : ℝ≥0} (h : IsSafeAt K δ N σ₀ ζ w t) : (t : ℝ≥0∞) < ζ := h.1

theorem IsSafeAt.le_sigma {t : ℝ≥0} (h : IsSafeAt K δ N σ₀ ζ w t) : t ≤ σ₀ := h.2.1

/-- The safe condition is antitone in time. -/
theorem IsSafeAt.anti (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H) {s t : ℝ≥0}
    (h : IsSafeAt K δ N σ₀ ζ w t) (hst : s ≤ t) : IsSafeAt K δ N σ₀ ζ w s := by
  obtain ⟨hζ, hσ, hN, hK⟩ := h
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  refine ⟨lt_of_le_of_lt (by exact_mod_cast hst) hζ, hst.trans hσ, hst'.trans hN, fun z hz => ?_⟩
  obtain ⟨⟨u, hu⟩, hδ⟩ := hK z hz
  refine ⟨⟨u, isForwardSol_of_le hu s.coe_nonneg hst'⟩, hδ.trans ?_⟩
  exact antitoneOn_im_fwdMap_of_continuousOn t.coe_nonneg (continuousOn_rpath hw hζ) (hKH hz)
    ⟨u, hu⟩ ⟨s.coe_nonneg, hst'⟩ ⟨t.coe_nonneg, le_rfl⟩ hst'

theorem IsSafeAt.mono {t : ℝ≥0} (h : IsSafeAt K δ N σ₀ ζ w t) {δ' N' : ℝ} {σ₀' : ℝ≥0}
    (hδ : δ' ≤ δ) (hN : N ≤ N') (hσ : σ₀ ≤ σ₀') : IsSafeAt K δ' N' σ₀' ζ w t :=
  ⟨h.1, h.2.1.trans hσ, h.2.2.1.trans hN, fun z hz => ⟨(h.2.2.2 z hz).1, hδ.trans (h.2.2.2 z hz).2⟩⟩

theorem IsSafeAt.subset {t : ℝ≥0} (h : IsSafeAt K δ N σ₀ ζ w t) {K' : Set ℂ} (hK : K' ⊆ K) :
    IsSafeAt K' δ N σ₀ ζ w t :=
  ⟨h.1, h.2.1, h.2.2.1, fun z hz => h.2.2.2 z (hK hz)⟩

theorem not_isSafeAt_of_lt {t : ℝ≥0} (h : σ₀ < t) : ¬ IsSafeAt K δ N σ₀ ζ w t :=
  fun hs => not_le.2 h hs.2.1

theorem nonempty_not_isSafeAt : {t | ¬ IsSafeAt K δ N σ₀ ζ w t}.Nonempty :=
  ⟨σ₀ + 1, not_isSafeAt_of_lt (lt_add_one σ₀)⟩

theorem safeExitTime_le_of_not {t : ℝ≥0} (h : ¬ IsSafeAt K δ N σ₀ ζ w t) :
    safeExitTime K δ N σ₀ ζ w ≤ t :=
  csInf_le (OrderBot.bddBelow _) h

theorem isSafeAt_of_lt_safeExitTime {t : ℝ≥0} (h : t < safeExitTime K δ N σ₀ ζ w) :
    IsSafeAt K δ N σ₀ ζ w t := by
  by_contra hn
  exact absurd (safeExitTime_le_of_not hn) (not_le.2 h)

theorem safeExitTime_le_sigma : safeExitTime K δ N σ₀ ζ w ≤ σ₀ :=
  le_of_forall_gt_imp_ge_of_dense fun _ hc => safeExitTime_le_of_not (not_isSafeAt_of_lt hc)

theorem le_safeExitTime_of_forall {t : ℝ≥0} (h : ∀ s ≤ t, IsSafeAt K δ N σ₀ ζ w s) :
    t ≤ safeExitTime K δ N σ₀ ζ w := by
  refine le_csInf nonempty_not_isSafeAt fun s hs => ?_
  by_contra hlt
  exact hs (h s (not_le.1 hlt).le)

theorem safeExitTime_mono {δ' N' : ℝ} {σ₀' : ℝ≥0} (hδ : δ' ≤ δ) (hN : N ≤ N') (hσ : σ₀ ≤ σ₀') :
    safeExitTime K δ N σ₀ ζ w ≤ safeExitTime K δ' N' σ₀' ζ w :=
  csInf_le_csInf (OrderBot.bddBelow _) nonempty_not_isSafeAt fun _ ht hp =>
    ht (hp.mono hδ hN hσ)

/-- **The exit time through a dense set of times**: `safeExitTime < t` iff the condition fails at a time of `T`
before `t`, for any dense `T ⊆ ℝ≥0`. -/
theorem safeExitTime_lt_iff (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H) {T : Set ℝ≥0}
    (hT : Dense T) {t : ℝ≥0} :
    safeExitTime K δ N σ₀ ζ w < t ↔ ∃ d ∈ T, d < t ∧ ¬ IsSafeAt K δ N σ₀ ζ w d := by
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt nonempty_not_isSafeAt h
    obtain ⟨d, hdT, hsd, hdt⟩ := hT.exists_between hst
    exact ⟨d, hdT, hdt, fun hd => hs (hd.anti hw hKH hsd.le)⟩
  · rintro ⟨d, -, hdt, hd⟩
    exact lt_of_le_of_lt (safeExitTime_le_of_not hd) hdt

/-- **The condition holds at the exit time**, if it holds at time `0` and `σ₀ < ζ` (a positive lower bound for
`Im f_s(z)` on `[0, T)` keeps `z` alive at `T`). -/
theorem isSafeAt_safeExitTime (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H) (hδ : 0 < δ)
    (hσζ : (σ₀ : ℝ≥0∞) < ζ) (h0 : IsSafeAt K δ N σ₀ ζ w 0) :
    IsSafeAt K δ N σ₀ ζ w (safeExitTime K δ N σ₀ ζ w) := by
  set T := safeExitTime K δ N σ₀ ζ w with hTdef
  rcases eq_or_lt_of_le (zero_le (a := T)) with hT0 | hTpos
  · rw [← hT0]; exact h0
  have hlt : ∀ s < T, IsSafeAt K δ N σ₀ ζ w s := fun s hs => isSafeAt_of_lt_safeExitTime hs
  have hTσ : T ≤ σ₀ := safeExitTime_le_sigma
  have hTζ : (T : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hTσ) hσζ
  have hwT := continuousOn_rpath hw hTζ
  have hTN : (T : ℝ) ≤ N := by
    refine le_of_forall_lt fun c hc => ?_
    by_cases hc0 : c < 0
    · exact lt_of_lt_of_le hc0 ((hlt 0 hTpos).2.2.1.trans' (by simp))
    · obtain ⟨s, hcs, hsT⟩ := exists_between hc
      have hs0 : 0 ≤ s := le_trans (not_lt.1 hc0) hcs.le
      have h := (hlt s.toNNReal (by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hsT)).2.2.1
      rw [Real.coe_toNNReal _ hs0] at h
      linarith
  refine ⟨hTζ, hTσ, hTN, fun z hz => ?_⟩
  have hzH := hKH hz
  have hlow : ∀ s, 0 ≤ s → s < (T : ℝ) → δ ≤ (fwdMap (rpath w) s z).im := fun s hs0 hsT => by
    have h := (hlt s.toNNReal (by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hsT)).2.2.2 z hz
    rw [Real.coe_toNNReal _ hs0] at h
    exact h.2
  have hsol := exists_isForwardSol_of_forall_lt T.coe_nonneg hwT hzH hδ hlow
  refine ⟨hsol, ?_⟩
  have hc := (Complex.continuous_im.comp_continuousOn
    (continuousOn_fwdMap_of_continuousOn T.coe_nonneg hwT hzH hsol)) (T : ℝ)
    ⟨T.coe_nonneg, le_rfl⟩
  have hTpos' : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hcl : (T : ℝ) ∈ closure (Ico 0 (T : ℝ)) := by
    rw [closure_Ico hTpos'.ne]; exact ⟨T.coe_nonneg, le_rfl⟩
  exact ContinuousWithinAt.closure_le hcl continuousWithinAt_const (hc.mono Ico_subset_Icc_self)
    fun s hs => hlow s hs.1 hs.2

/-- **The safe condition on a dense subset**: for `D ⊆ K ⊆ closure D`, `K ⊆ ℍ` and `δ > 0`, the condition for `D`
implies the condition for `K`. A point `z ∈ K` swallowed by time `t` has `Im f_s(z) < δ` at some time `s` before
its swallowing time (`FwdClock.mem_fwdHull_iff_inf_im`); by continuity of `f_s` at `z` the same holds at points of
`D` near `z`, which contradicts `Im f_s ≥ Im f_t ≥ δ` on `D`. -/
theorem IsSafeAt.of_dense (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hKH : K ⊆ H)
    (hKD : K ⊆ closure D) (hDK : D ⊆ K) (hδ : 0 < δ) {t : ℝ≥0} (h : IsSafeAt D δ N σ₀ ζ w t) :
    IsSafeAt K δ N σ₀ ζ w t := by
  obtain ⟨hζ, hσ, hN, hD⟩ := h
  refine ⟨hζ, hσ, hN, fun z hz => ?_⟩
  have hwt := continuousOn_rpath hw hζ
  have hW' : Continuous (clampDrv (rpath w) t) := continuous_clampDrv t.coe_nonneg hwt
  have hDim : ∀ y ∈ D, ∀ s ∈ Icc (0 : ℝ) t, δ ≤ (fwdMap (clampDrv (rpath w) t) s y).im :=
    fun y hy s hs => by
      rw [fwdMap_clampDrv_of_le hs.2]
      exact (hD y hy).2.trans (antitoneOn_im_fwdMap_of_continuousOn t.coe_nonneg hwt (hKH (hDK hy))
        (hD y hy).1 hs ⟨t.coe_nonneg, le_rfl⟩ hs.2)
  have key : ∀ s : ℝ, 0 ≤ s → s ≤ t → z ∈ H \ fwdHull (clampDrv (rpath w) t) s →
      δ ≤ (fwdMap (clampDrv (rpath w) t) s z).im := by
    intro s hs0 hst hzs
    by_contra hlt
    rw [not_le] at hlt
    have hca : ContinuousAt (fun y => (fwdMap (clampDrv (rpath w) t) s y).im) z :=
      Complex.continuous_im.continuousAt.comp (FwdHolo.hasDerivAt_fwdMap hW' hs0 hzs).continuousAt
    have hev : ∀ᶠ y in 𝓝 z, (fwdMap (clampDrv (rpath w) t) s y).im < δ :=
      hca.eventually (gt_mem_nhds hlt)
    obtain ⟨y, hy, hyD⟩ := mem_closure_iff_nhds.1 (hKD hz) _ hev
    exact absurd (hDim y hyD s ⟨hs0, hst⟩) (not_le.2 hy)
  have hzt : z ∈ H \ fwdHull (clampDrv (rpath w) t) t := by
    refine ⟨hKH hz, fun hmem => ?_⟩
    obtain ⟨-, σ, hσt, hsw, hc⟩ := (FwdClock.mem_fwdHull_iff_inf_im hW').1 hmem
    obtain ⟨s, hs0, hsσ, hs⟩ := hc δ hδ
    have hzs : z ∈ H \ fwdHull (clampDrv (rpath w) t) s := by
      refine ⟨hKH hz, fun h' => ?_⟩
      have h2 : swallowTime (clampDrv (rpath w) t) z ≤ ENNReal.ofReal s := h'.2
      rw [hsw, ENNReal.ofReal_le_ofReal_iff hs0] at h2
      exact absurd h2 (not_le.2 hsσ)
    exact absurd (key s hs0 (hsσ.le.trans hσt) hzs) (not_le.2 hs)
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem t.coe_nonneg hzt
  refine ⟨⟨u, (isForwardSol_iff_of_eqOn (clampDrv_eqOn (W := rpath w)) u).1 hu⟩, ?_⟩
  have := key t t.coe_nonneg le_rfl hzt
  rwa [fwdMap_clampDrv_of_le le_rfl] at this

/-- The safe condition at time `0`. -/
theorem isSafeAt_zero (hKH : K ⊆ H) (hKδ : ∀ z ∈ K, δ ≤ z.im) (hw0 : w 0 = 0) (hζ : 0 < ζ)
    (hN : 0 ≤ N) : IsSafeAt K δ N σ₀ ζ w 0 := by
  refine ⟨by simpa using hζ, zero_le, by simpa using hN, fun z hz => ⟨?_, ?_⟩⟩
  · simpa using exists_isForwardSol_zero (rpath w) (hKH hz)
  · rw [NNReal.coe_zero, fwdMap_zero_eq_sub _ (hKH hz)]
    simpa [rpath, hw0] using hKδ z hz

/-- **Exhaustion**: if `t ≤ σ₀`, `t < ζ` and the compact set `K ⊆ ℍ` is alive at `t`, then `t` lies below the exit
times of all large levels `δ = m/(n+1)`, `N = n` (`Im f_s ≥ Im f_t ≥ δ₀ > 0` on `K` for `s ≤ t`, by compactness). -/
theorem eventually_le_safeExitTime (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hK : IsCompact K)
    (hKH : K ⊆ H) (m : ℝ) {t : ℝ≥0} (htσ : t ≤ σ₀) (htζ : (t : ℝ≥0∞) < ζ)
    (halive : ∀ z ∈ K, ∃ u, IsForwardSol (rpath w) z t u) :
    ∀ᶠ n : ℕ in atTop, t ≤ safeExitTime K (m / ((n : ℝ) + 1)) n σ₀ ζ w := by
  have hwt := continuousOn_rpath hw htζ
  have hW' := continuous_clampDrv t.coe_nonneg hwt
  have hKt : K ⊆ H \ fwdHull (clampDrv (rpath w) t) t := fun z hz =>
    mem_diff_fwdHull_clampDrv t.coe_nonneg hwt (hKH hz) (halive z hz)
  obtain ⟨δ₀, hδ₀, hprot⟩ := exists_isProtected_of_isCompact hW' t.coe_nonneg hK hKt
  filter_upwards [eventually_div_succ_le m hδ₀, eventually_le_natCast_add (t : ℝ) 0] with n hn hnt
  refine le_safeExitTime_of_forall fun s hs => IsSafeAt.anti hw hKH ?_ hs
  refine ⟨htζ, htσ, by simpa using hnt, fun z hz => ⟨halive z hz, hn.trans ?_⟩⟩
  have := (hprot z hz).2
  rwa [fwdMap_clampDrv_of_le le_rfl] at this

end Path

/-! ### The safe stops as stopping times -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The safe event is adapted**: for a countable set `D ⊆ ℍ`, `{ω ∈ G : the safe condition for D holds at d}` is
`𝓖_d`-measurable. -/
theorem measurableSet_isSafeAt {𝓖 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {G : Set Ω} (hW : AdaptedBefore 𝓖 ζ W)
    (hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hG : MeasurableSet[𝓖 0] G) {D : Set ℂ} (hDc : D.Countable) (hDH : D ⊆ H) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime 𝓖 fun ω => (σ₀ ω : WithTop ℝ≥0)) (δ N : ℝ) (d : ℝ≥0) :
    MeasurableSet[𝓖 d] {ω | ω ∈ G ∧ IsSafeAt D δ N (σ₀ ω) (ζ ω) (W · ω) d} := by
  have hσm : MeasurableSet[𝓖 d] {ω | d ≤ σ₀ ω} := by
    have := (hσ₀.measurableSet_lt d).compl
    convert this using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_lt_coe, not_lt]
  have hS : MeasurableSet[𝓖 d] {ω | ω ∈ G ∧ (d : ℝ≥0∞) < ζ ω} := by
    have h1 := hW d univ MeasurableSet.univ
    simp only [mem_univ, and_true] at h1
    exact (𝓖.mono (zero_le : (0 : ℝ≥0) ≤ d) _ hG).inter h1
  have hz : ∀ z ∈ D, MeasurableSet[𝓖 d] (aliveSet W ζ G z d ∩ {ω | δ ≤
      (if ω ∈ aliveSet W ζ G z d then fwdMap (rpath (W · ω)) d z else 0).im}) := fun z hzD =>
    (measurableSet_aliveSet hW hGc hG (hDH hzD) d).inter
      (measurableSet_le measurable_const
        (Complex.measurable_im.comp (measurable_fwdMap_alive hW hGc hG (hDH hzD) d)))
  have heq : {ω | ω ∈ G ∧ IsSafeAt D δ N (σ₀ ω) (ζ ω) (W · ω) d} =
      {ω | ω ∈ G ∧ (d : ℝ≥0∞) < ζ ω} ∩ {ω | d ≤ σ₀ ω} ∩ {_ω | (d : ℝ) ≤ N} ∩
        ⋂ z ∈ D, (aliveSet W ζ G z d ∩ {ω | δ ≤
          (if ω ∈ aliveSet W ζ G z d then fwdMap (rpath (W · ω)) d z else 0).im}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, IsSafeAt]
    constructor
    · rintro ⟨hω, h1, h2, h3, h4⟩
      refine ⟨⟨⟨⟨hω, h1⟩, h2⟩, h3⟩, fun z hz => ⟨⟨hω, h1, (h4 z hz).1⟩, ?_⟩⟩
      have hal : ω ∈ aliveSet W ζ G z d := ⟨hω, h1, (h4 z hz).1⟩
      simp only [hal, ↓reduceIte]
      exact (h4 z hz).2
    · rintro ⟨⟨⟨⟨hω, h1⟩, h2⟩, h3⟩, h4⟩
      refine ⟨hω, h1, h2, h3, fun z' hz' => ?_⟩
      obtain ⟨hal', hle'⟩ := h4 z' hz'
      simp only [hal', ↓reduceIte] at hle'
      obtain ⟨-, -, hsol'⟩ := hal'
      exact ⟨hsol', hle'⟩
  rw [heq]
  exact ((hS.inter hσm).inter (MeasurableSet.const _)).inter
    (MeasurableSet.biInter hDc fun z hzD => hz z hzD)

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ}
  {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The safe stops** (Specification L559–L565, node `SPEC.thm-1.1#safe-stops`). For a compact `K ⊆ ℍ` with
`Im ≥ m > 0` on `K`, below a nondecreasing sequence of stopping times `σ₀ n < ζ` of the usual augmentation, the
level-`n` safe exit times `ρ_n` (threshold `Im f ≥ m/(n+1)` on `K`, `t ≤ n`, `t ≤ σ₀ n`) are stopping times of the
usual augmentation, `ρ_n ≤ σ₀ n`, nondecreasing in `n`, safe (the condition holds at `ρ_n`), and they exhaust every
horizon `t ≤ σ₀ j` at which `K` is alive. -/
theorem exists_safeSeq_of_seq (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {m : ℝ} (hm : 0 < m) (hKm : ∀ z ∈ K, m ≤ z.im)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
      ∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
        (∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω := by
  obtain ⟨-, hWa, -, -, hpath⟩ := isIntegratedSLEEvolution_usualAugmentation hE
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  set good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧
      ∀ n, (σ₀ n ω : ℝ≥0∞) < ζ ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, ae_all_iff.2 hσ₀ζ] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG : ∀ t, MeasurableSet[𝓖 t] G := fun t => by
    have := (measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc t).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hwc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hGgood ω hω).1.2.2.2.1
  obtain ⟨D, hDK, hDc, hKD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  have hδ : ∀ n : ℕ, 0 < m / ((n : ℝ) + 1) := fun n => by positivity
  set ρ : ℕ → Ω → ℝ≥0 := fun n ω => if ω ∈ G then
    safeExitTime K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) else 0 with hρ
  have hDiff : ∀ ω ∈ G, ∀ n : ℕ, ∀ d : ℝ≥0,
      IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) d ↔
        IsSafeAt D (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) d := fun ω hω n d =>
    ⟨fun h => h.subset hDK, fun h => h.of_dense (hwc ω hω) hKH hKD hDK (hδ n)⟩
  refine ⟨ρ, fun n => ?_, fun n ω => ?_, fun ω => ?_, fun n => ?_, ?_⟩
  · -- stopping times
    obtain ⟨T, hTc, hTd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
    have heq : {ω | ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0)} =
        (⋃ d ∈ T ∩ Iio t, G \ {ω | ω ∈ G ∧
          IsSafeAt D (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) d}) ∪
          (Gᶜ ∩ {_ω | (0 : ℝ≥0) < t}) := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_lt_coe, mem_union, mem_iUnion, mem_inter_iff,
        Set.mem_sdiff, mem_Iio, exists_prop, mem_compl_iff]
      by_cases hω : ω ∈ G
      · simp only [hρ, hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
        rw [safeExitTime_lt_iff (hwc ω hω) hKH hTd]
        constructor
        · rintro ⟨d, hd, hdt, hnp⟩; exact ⟨d, ⟨hd, hdt⟩, fun h => hnp ((hDiff ω hω n d).2 h)⟩
        · rintro ⟨d, ⟨hd, hdt⟩, hnp⟩; exact ⟨d, hd, hdt, fun h => hnp ((hDiff ω hω n d).1 h)⟩
      · simp only [hρ, hω, ↓reduceIte, false_and, and_false, exists_false, false_or,
          not_false_eq_true, true_and]
    rw [heq]
    refine MeasurableSet.union (MeasurableSet.biUnion (hTc.mono inter_subset_left) fun d hd => ?_)
      ((hG t).compl.inter (MeasurableSet.const _))
    exact 𝓖.mono hd.2.le _ ((hG d).diff (measurableSet_isSafeAt hWa hwc (hG 0) hDc
      (hDK.trans hKH) (hσ₀ n) _ _ d))
  · -- below σ₀
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]; exact safeExitTime_le_sigma
    · simp only [hρ, hω, ↓reduceIte]; exact zero_le
  · -- monotone
    intro n n' hnn'
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]
      have hn : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
      exact safeExitTime_mono (div_le_div_of_nonneg_left hm.le (by positivity) (by linarith)) hn
        (hσ₀m ω hnn')
    · simp only [hρ, hω, ↓reduceIte]; exact le_rfl
  · -- safety at the stop
    filter_upwards [hGae] with ω hω
    simp only [hρ, hω, ↓reduceIte]
    obtain ⟨hP, hσζ⟩ := hGgood ω hω
    have hζ0 : 0 < ζ ω := lt_of_le_of_lt (by exact_mod_cast zero_le) (hσζ n)
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    exact isSafeAt_safeExitTime (hwc ω hω) hKH (hδ n) (hσζ n)
      (isSafeAt_zero hKH (fun z hz => (div_le_self hm.le hn1).trans (hKm z hz)) hP.1 hζ0
        n.cast_nonneg)
  · -- exhaustion
    filter_upwards [hGae] with ω hω j t htσ halive
    have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast htσ) ((hGgood ω hω).2 j)
    have hev := eventually_le_safeExitTime (hwc ω hω) hK hKH m htσ htζ halive
    filter_upwards [hev, eventually_ge_atTop j] with n hn hjn
    simp only [hρ, hω, ↓reduceIte]
    exact hn.trans (safeExitTime_mono le_rfl le_rfl (hσ₀m ω hjn))

end Random

end Coupling

end InteractingSLE
