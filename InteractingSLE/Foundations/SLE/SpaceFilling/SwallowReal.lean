import QuantumZipper.Proofs.RS.RealAlive
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Swallowing times of real points under the chordal Loewner flow

Packet `planning/packets/PROVE-RS05-74b.md`. Deterministic facts about the centered real flow
`X_t(x) = g_t(x) − W_t` (QuantumZipper's `IsForwardSol W x T v` from a real starting point `x`),
used for [RS05, Lemma 7.3] when `4 < κ < 8`.

* `RealSwallowAt W x σ`: the real point `x` is alive on `[0, s]` for every `s < σ` and not alive on
  `[0, σ]` (the swallowing time `T_x = σ` of [Law] §6.2).
* `tendsto_fwdMap_of_realSwallowAt`: at the swallowing time the flow tends to `0`
  ([Law] p. 127, "`lim_{t → T_x−} ĝ_t(x) = 0`"). Proof: the uncentered flow `g_t(x)` is increasing
  and never exceeds `W_σ` (otherwise the tamed flow continues the solution past `σ`).
* `exists_realSwallowAt`: a point that is not alive on `[0, T]` is swallowed at some `σ ≤ T`.
* `re_fwdMap_lt_of_lt`: the real flow preserves the order of positive starting points (backward
  uniqueness of the Loewner ODE).
* `realSwallowAt_of_le_of_le`: if `x < y` are swallowed at the same time, so is every point between
  them ("the interval is swallowed at once").
* Reflection `x ↦ −x`, `W ↦ −W`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE

variable {W : ℝ → ℝ}

/-- **The real point `x` is swallowed at time `σ`**: it is alive (a solution of the centered
forward flow exists) on `[0, s]` for every `0 ≤ s < σ`, and not on `[0, σ]`. -/
def RealSwallowAt (W : ℝ → ℝ) (x σ : ℝ) : Prop :=
  0 < σ ∧ (∀ s ∈ Ico (0 : ℝ) σ, ∃ v, IsForwardSol W (x : ℂ) s v) ∧
    ¬ ∃ v, IsForwardSol W (x : ℂ) σ v

/-- `fwdMap` is the value of any solution, for any starting point (uniqueness of solutions,
`eqOn_of_isForwardSol`). -/
theorem fwdMap_eq_of_isForwardSol (hW : Continuous W) {p : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W p T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : fwdMap W t p = u t := by
  have hut : IsForwardSol W p t u := isForwardSol_restrict hu ht.1 ht.2
  have hex : ∃ u', IsForwardSol W p t u' := ⟨u, hut⟩
  simp only [fwdMap, hex, ↓reduceDIte]
  exact eqOn_of_isForwardSol hW hex.choose_spec hut ⟨ht.1, le_rfl⟩

/-- The real part of the uncentered flow solves the tamed real ODE while the solution stays
`≥ c`. -/
theorem hasDerivWithinAt_re_add_of_isForwardSol (hW : Continuous W) {x c T : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) (hc : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (v t).re) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => (v s).re + W s) (realVf W c t ((v t).re + W t)) (Icc 0 T) t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have him := im_isForwardSol_real hW hT hv
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (FwdHolo.hasDerivWithinAt_shift hv ht)
  have hval : realVf W c t ((v t).re + W t) = (2 / v t).re := by
    rw [realVf, add_sub_cancel_right, realDrift_of_le (hc t ht)]
    have : v t = ((v t).re : ℂ) := Complex.ext (by simp) (by simp [him t ht])
    rw [this, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]
  rw [hval]
  have e : (fun s => (v s).re + W s) = fun s => (v s + (W s : ℂ)).re := by
    funext s; simp
  rw [e]
  exact h

/-- **The tamed real flow is the true flow** while the latter stays `≥ c`. -/
theorem realTamed_eq_re_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x c T : ℝ}
    (hc0 : 0 < c) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (v t).re) :
    ∀ t ∈ Icc (0 : ℝ) T, realTamed W c x t = (v t).re := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (v 0).re + W 0 = x := by
    rw [FwdHolo.sol_zero hv hT, hW0]; simp
  have := realTamedUnc_eq_of_sol hW hc0 h0
    (fun s hs => hasDerivWithinAt_re_add_of_isForwardSol hW hv hc hs) t ht
  rw [realTamed, this]; ring

/-- A real solution has real values. -/
theorem fwdMap_eq_ofReal_re (hW : Continuous W) {x T : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap W t x = ((fwdMap W t x).re : ℂ) := by
  rw [fwdMap_eq_of_isForwardSol hW hv ht]
  exact Complex.ext (by simp) (by simp [im_isForwardSol_real hW (ht.1.trans ht.2) hv t ht])

/-- A real point is alive on `[0, 0]`. -/
theorem exists_isForwardSol_zero (hW0 : W 0 = 0) {x : ℝ} (hx : x ≠ 0) :
    ∃ v, IsForwardSol W (x : ℂ) 0 v := by
  refine ⟨fun _ => (x : ℂ), continuousOn_const, fun t ht => ?_⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst ht0
  refine ⟨show (x : ℂ) ≠ 0 by exact_mod_cast hx, ?_⟩
  simp [hW0]

/-- **Continuation of the real flow.** If `x > 0` is alive on `[0, s]` for every `s < σ` and the
flow stays `≥ c > 0` there, then `x` is alive on `[0, σ]` (the tamed flow at level `c/2` is the
true flow on `[0, σ)` and stays `≥ c` at `σ` by continuity). -/
theorem exists_isForwardSol_of_forall_lt (hW : Continuous W) (hW0 : W 0 = 0) {x σ : ℝ}
    (hσ : 0 < σ) (halive : ∀ s ∈ Ico (0 : ℝ) σ, ∃ v, IsForwardSol W (x : ℂ) s v) {c : ℝ}
    (hc : 0 < c) (hge : ∀ s ∈ Ico (0 : ℝ) σ, c ≤ (fwdMap W s x).re) :
    ∃ v, IsForwardSol W (x : ℂ) σ v := by
  have hc2 : 0 < c / 2 := half_pos hc
  have hagree : ∀ t ∈ Ico (0 : ℝ) σ, c ≤ realTamed W (c / 2) x t := by
    intro t ht
    obtain ⟨v, hv⟩ := halive t ht
    have hvc : ∀ r ∈ Icc (0 : ℝ) t, c / 2 ≤ (v r).re := fun r hr => by
      have h1 := hge r ⟨hr.1, hr.2.trans_lt ht.2⟩
      rw [fwdMap_eq_of_isForwardSol hW hv hr] at h1
      linarith
    rw [realTamed_eq_re_of_isForwardSol hW hW0 hc2 hv hvc t ⟨ht.1, le_rfl⟩,
      ← fwdMap_eq_of_isForwardSol hW hv ⟨ht.1, le_rfl⟩]
    exact hge t ht
  have hcont : ContinuousOn (realTamed W (c / 2) x) (Icc 0 σ) :=
    continuousOn_realTamed hW hc2 hσ.le x
  have hσmem : σ ∈ closure (Ico (0 : ℝ) σ) := by
    rw [closure_Ico hσ.ne]; exact ⟨hσ.le, le_rfl⟩
  have hnb : (𝓝[Ico (0 : ℝ) σ] σ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hσmem
  have hlim : Tendsto (realTamed W (c / 2) x) (𝓝[Ico (0 : ℝ) σ] σ)
      (𝓝 (realTamed W (c / 2) x σ)) :=
    (hcont.continuousWithinAt ⟨hσ.le, le_rfl⟩).mono Ico_subset_Icc_self
  have hclosed : c ≤ realTamed W (c / 2) x σ :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hagree)
  refine ⟨_, isForwardSol_realTamed hW hc2 hσ.le fun t ht => ?_⟩
  rcases ht.2.lt_or_eq with h | h
  · linarith [hagree t ⟨ht.1, h⟩]
  · rw [h]; linarith

/-- A positive real point has a positive flow while alive. -/
theorem re_fwdMap_pos (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : 0 < x) {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    0 < (fwdMap W t x).re := by
  rw [fwdMap_eq_of_isForwardSol hW hv ht]
  exact re_pos_isForwardSol_real hW (ht.1.trans ht.2) hv (by rw [hW0]; exact hx) t ht

/-- A solution from `x > 0` stays above a positive constant on `[0, T]`. -/
theorem exists_pos_le_re_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ}
    (hx : 0 < x) (hT : 0 ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) :
    ∃ c > 0, ∀ t ∈ Icc (0 : ℝ) T, c ≤ (v t).re := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (Complex.continuous_re.comp_continuousOn hv.1)
  exact ⟨(v t₀).re, re_pos_isForwardSol_real hW hT hv (by rw [hW0]; exact hx) t₀ ht₀,
    fun t ht => hmin ht⟩

/-- The uncentered real flow `g_t(x) = X_t + W_t` is nondecreasing while `x > 0` is alive. -/
theorem re_add_monotoneOn (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : 0 < x)
    (hT : 0 ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) :
    MonotoneOn (fun s => (v s).re + W s) (Icc 0 T) := by
  obtain ⟨c, hc, hcle⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx hT hv
  have hd := fun t (ht : t ∈ Icc (0 : ℝ) T) => hasDerivWithinAt_re_add_of_isForwardSol hW hv hcle ht
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
    (f' := fun t => realVf W c t ((v t).re + W t))
    (fun t ht => (hd t ht).continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · exact (hd t (interior_subset ht)).mono interior_subset
  · have h1 := hcle t (interior_subset ht)
    show 0 ≤ realDrift c ((v t).re + W t - W t)
    rw [add_sub_cancel_right, realDrift_of_le h1]
    exact div_nonneg zero_le_two (hc.le.trans h1)

/-- **At its swallowing time the real flow tends to `0`** ([Law] §6.2, p. 127). The uncentered
flow `g_s(x) = X_s + W_s` is nondecreasing; `X` comes arbitrarily close to `0` near `σ`
(otherwise `exists_isForwardSol_of_forall_lt` continues the solution to `σ`), so `g_s(x) ≤ W_σ`
for all `s < σ`, whence `0 < X_s ≤ W_σ − W_s → 0`. -/
theorem tendsto_fwdMap_of_realSwallowAt (hW : Continuous W) (hW0 : W 0 = 0) {x σ : ℝ}
    (hx : 0 < x) (h : RealSwallowAt W x σ) :
    Tendsto (fun s => fwdMap W s x) (𝓝[<] σ) (𝓝 0) := by
  obtain ⟨hσ, halive, hdead⟩ := h
  set X : ℝ → ℝ := fun s => (fwdMap W s x).re with hXdef
  have hXpos : ∀ s ∈ Ico (0 : ℝ) σ, 0 < X s := fun s hs => by
    obtain ⟨v, hv⟩ := halive s hs
    exact re_fwdMap_pos hW hW0 hx hv ⟨hs.1, le_rfl⟩
  have hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < σ → X s + W s ≤ X t + W t := by
    intro s t hs hst ht
    obtain ⟨v, hv⟩ := halive t ⟨hs.trans hst, ht⟩
    have h := re_add_monotoneOn hW hW0 hx (hs.trans hst) hv ⟨hs, hst⟩ ⟨hs.trans hst, le_rfl⟩ hst
    simp only [hXdef]
    rw [fwdMap_eq_of_isForwardSol hW hv ⟨hs, hst⟩,
      fwdMap_eq_of_isForwardSol hW hv ⟨hs.trans hst, le_rfl⟩]
    exact h
  have hsmall : ∀ c > (0 : ℝ), ∀ s₀ < σ, ∃ s ∈ Ico (0 : ℝ) σ, s₀ ≤ s ∧ X s < c := by
    intro c hc s₀ hs₀
    by_contra hcon
    push Not at hcon
    set s₁ := max s₀ 0 with hs₁def
    have hs₁ : s₁ ∈ Ico (0 : ℝ) σ := ⟨le_max_right _ _, max_lt hs₀ hσ⟩
    obtain ⟨v, hv⟩ := halive s₁ hs₁
    obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx hs₁.1 hv
    refine hdead (exists_isForwardSol_of_forall_lt hW hW0 hσ halive (lt_min hc hc₁)
      fun s hs => ?_)
    rcases le_or_gt s₀ s with h | h
    · exact (min_le_left _ _).trans (hcon s hs h)
    · have hs' : s ∈ Icc 0 s₁ := ⟨hs.1, h.le.trans (le_max_left _ _)⟩
      rw [fwdMap_eq_of_isForwardSol hW hv hs']
      exact (min_le_right _ _).trans (hc₁le s hs')
  have hup : ∀ s ∈ Ico (0 : ℝ) σ, X s + W s ≤ W σ := by
    intro s hs
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨δ, hδ, hWδ⟩ := Metric.continuousAt_iff.1 hW.continuousAt (ε / 2) (half_pos hε)
    obtain ⟨s', hs', hs's, hX'⟩ := hsmall (ε / 2) (half_pos hε) (max s (σ - δ / 2))
      (max_lt hs.2 (by linarith))
    have h1 := hmono s s' hs.1 ((le_max_left _ _).trans hs's) hs'.2
    have hd : dist s' σ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_max_right s (σ - δ / 2), hs'.2]
    have h2 := hWδ hd
    rw [Real.dist_eq] at h2
    linarith [(abs_lt.1 h2).2]
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hWδ⟩ := Metric.continuousAt_iff.1 hW.continuousAt ε hε
  refine ⟨min δ σ, lt_min hδ hσ, fun s hs hsd => ?_⟩
  have hs0 : 0 ≤ s := by
    have := hsd.trans_le (min_le_right _ _)
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hsm : s ∈ Ico (0 : ℝ) σ := ⟨hs0, hs⟩
  have hW' := hWδ (hsd.trans_le (min_le_left _ _))
  rw [Real.dist_eq] at hW'
  obtain ⟨v, hv⟩ := halive s hsm
  rw [dist_zero_right, fwdMap_eq_ofReal_re hW hv ⟨hs0, le_rfl⟩, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (hXpos s hsm)]
  linarith [hup s hsm, (abs_lt.1 hW').1]

/-- **Existence of the swallowing time.** If `x > 0` is not alive on `[0, T]`, it is swallowed at
some `σ ∈ (0, T]` (`σ` is the supremum of the times at which `x` is alive; the tamed flow gives
local existence and continuation). -/
theorem exists_realSwallowAt (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : 0 < x)
    (hT : 0 ≤ T) (hdead : ¬ ∃ v, IsForwardSol W (x : ℂ) T v) :
    ∃ σ ∈ Ioc 0 T, RealSwallowAt W x σ := by
  set S : Set ℝ := {s | 0 ≤ s ∧ ∃ v, IsForwardSol W (x : ℂ) s v} with hSdef
  have hSlt : ∀ s ∈ S, s < T := fun s hs => by
    by_contra hle
    push Not at hle
    obtain ⟨v, hv⟩ := hs.2
    exact hdead ⟨v, isForwardSol_restrict hv hT hle⟩
  have hbdd : BddAbove S := ⟨T, fun s hs => (hSlt s hs).le⟩
  have hx2 : 0 < x / 2 := half_pos hx
  have hcont1 : ContinuousOn (realTamed W (x / 2) x) (Icc 0 1) :=
    continuousOn_realTamed hW hx2 zero_le_one x
  have h0val : realTamed W (x / 2) x 0 = x := by
    rw [realTamed, realTamedUnc_zero hW hx2, hW0, sub_zero]
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1
    (hcont1.continuousWithinAt ⟨le_rfl, zero_le_one⟩) (x / 2) hx2
  set ε := min (δ / 2) 1 with hεdef
  have hε : 0 < ε := lt_min (half_pos hδ) one_pos
  have hεS : ε ∈ S := by
    refine ⟨hε.le, _, isForwardSol_realTamed hW hx2 hε.le fun t ht => ?_⟩
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
    have hd : dist t 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      linarith [ht.2, min_le_left (δ / 2) 1]
    have := hδc ht1 hd
    rw [Real.dist_eq, h0val] at this
    linarith [(abs_lt.1 this).1]
  set σ := sSup S with hσdef
  have hσpos : 0 < σ := hε.trans_le (le_csSup hbdd hεS)
  have hσT : σ ≤ T := csSup_le ⟨ε, hεS⟩ fun s hs => (hSlt s hs).le
  have halive : ∀ s ∈ Ico (0 : ℝ) σ, ∃ v, IsForwardSol W (x : ℂ) s v := fun s hs => by
    obtain ⟨s', hs'S, hss'⟩ := exists_lt_of_lt_csSup ⟨ε, hεS⟩ hs.2
    obtain ⟨v, hv⟩ := hs'S.2
    exact ⟨v, isForwardSol_restrict hv hs.1 hss'.le⟩
  refine ⟨σ, ⟨hσpos, hσT⟩, hσpos, halive, fun ⟨v, hv⟩ => ?_⟩
  have hσT' : σ < T := lt_of_le_of_ne hσT fun h => hdead ⟨v, h ▸ hv⟩
  obtain ⟨c, hc, hcle⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx hσpos.le hv
  have hc2 : 0 < c / 2 := half_pos hc
  have hagree := realTamed_eq_re_of_isForwardSol hW hW0 hc2 hv
    (fun t ht => by linarith [hcle t ht])
  have hcontT : ContinuousOn (realTamed W (c / 2) x) (Icc 0 T) :=
    continuousOn_realTamed hW hc2 (hσpos.le.trans hσT) x
  obtain ⟨δ', hδ', hδ'c⟩ := Metric.continuousWithinAt_iff.1
    (hcontT.continuousWithinAt ⟨hσpos.le, hσT⟩) (c / 2) hc2
  set ε' := min (δ' / 2) ((T - σ) / 2) with hε'def
  have hε' : 0 < ε' := lt_min (half_pos hδ') (by linarith)
  have hS' : σ + ε' ∈ S := by
    refine ⟨by linarith, _, isForwardSol_realTamed hW hc2 (by linarith) fun t ht => ?_⟩
    rcases le_or_gt t σ with h | h
    · rw [hagree t ⟨ht.1, h⟩]; linarith [hcle t ⟨ht.1, h⟩]
    · have htT : t ∈ Icc (0 : ℝ) T :=
        ⟨ht.1, by linarith [ht.2, min_le_right (δ' / 2) ((T - σ) / 2)]⟩
      have hd : dist t σ < δ' := by
        rw [Real.dist_eq, abs_of_pos (by linarith)]
        linarith [ht.2, min_le_left (δ' / 2) ((T - σ) / 2)]
      have := hδ'c htT hd
      rw [Real.dist_eq, hagree σ ⟨hσpos.le, le_rfl⟩] at this
      linarith [(abs_lt.1 this).1, hcle σ ⟨hσpos.le, le_rfl⟩]
  have := le_csSup hbdd hS'
  linarith

/-- **The real flow preserves order** of positive starting points: if `0 < x < y` are alive on
`[0, T]`, then `X_t(x) < X_t(y)` there (two solutions of the Loewner ODE that met would agree
backwards to time `0`, by uniqueness for the Lipschitz tamed field). -/
theorem re_lt_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x y T : ℝ} (hx : 0 < x)
    (hxy : x < y) {v w : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v)
    (hw : IsForwardSol W (y : ℂ) T w) : ∀ t ∈ Icc (0 : ℝ) T, (v t).re < (w t).re := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_re_of_isForwardSol hW hW0 hx hT hv
  obtain ⟨c₂, hc₂, hc₂le⟩ := exists_pos_le_re_of_isForwardSol hW hW0 (hx.trans hxy) hT hw
  set c := min c₁ c₂ with hcdef
  have hc : 0 < c := lt_min hc₁ hc₂
  set V1 : ℝ → ℝ := fun s => (w s).re + W s with hV1
  set V2 : ℝ → ℝ := fun s => (v s).re + W s with hV2
  have hd1 : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt V1 (realVf W c s (V1 s)) (Icc 0 T) s :=
    fun s hs => hasDerivWithinAt_re_add_of_isForwardSol hW hw
      (fun r hr => (min_le_right _ _).trans (hc₂le r hr)) hs
  have hd2 : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt V2 (realVf W c s (V2 s)) (Icc 0 T) s :=
    fun s hs => hasDerivWithinAt_re_add_of_isForwardSol hW hv
      (fun r hr => (min_le_left _ _).trans (hc₁le r hr)) hs
  have hV1c : ContinuousOn V1 (Icc 0 T) := fun s hs => (hd1 s hs).continuousWithinAt
  have hV2c : ContinuousOn V2 (Icc 0 T) := fun s hs => (hd2 s hs).continuousWithinAt
  have h10 : V1 0 = y := by
    simp only [hV1]; rw [FwdHolo.sol_zero hw hT, hW0]; simp
  have h20 : V2 0 = x := by
    simp only [hV2]; rw [FwdHolo.sol_zero hv hT, hW0]; simp
  suffices V2 t < V1 t by simp only [hV1, hV2] at this; linarith
  by_contra hcon'
  have hcon := not_lt.1 hcon'
  obtain ⟨t1, ht1, ht1eq⟩ : ∃ t1 ∈ Icc 0 t, (fun s => V1 s - V2 s) t1 = 0 := by
    have := intermediate_value_Icc' ht.1 ((hV1c.sub hV2c).mono (Icc_subset_Icc_right ht.2))
    exact this ⟨by show V1 t - V2 t ≤ 0; linarith, by show 0 ≤ V1 0 - V2 0; linarith⟩
  simp only at ht1eq
  have ht1pos : 0 < t1 := lt_of_le_of_ne ht1.1 (fun h => by rw [← h] at ht1eq; linarith)
  have hsub : Icc 0 t1 ⊆ Icc 0 T := Icc_subset_Icc_right (ht1.2.trans ht.2)
  have hIic : ∀ {f : ℝ → ℝ},
      (∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (realVf W c s (f s)) (Icc 0 T) s) →
      ∀ s ∈ Ioc (0 : ℝ) t1, HasDerivWithinAt f (realVf W c s (f s)) (Iic s) s :=
    fun h s hs => (h s (hsub (Ioc_subset_Icc_self hs))).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsLE hs.1)
        (Icc_subset_Icc_right (hs.2.trans (ht1.2.trans ht.2))))
  have heq := ODE_solution_unique_of_mem_Icc_left (s := fun _ => univ)
    (fun s _ => (lipschitz_realVf hc W s).lipschitzOnWith)
    (hV1c.mono hsub) (hIic hd1) (fun _ _ => mem_univ _)
    (hV2c.mono hsub) (hIic hd2) (fun _ _ => mem_univ _) (by linarith : V1 t1 = V2 t1)
  have := heq ⟨le_rfl, ht1pos.le⟩
  linarith

/-- The swallowing time is unique. -/
theorem RealSwallowAt.eq {x σ σ' : ℝ} (h : RealSwallowAt W x σ) (h' : RealSwallowAt W x σ') :
    σ = σ' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2.2 (h'.2.1 σ ⟨h.1.le, hlt⟩)
  · exact h'.2.2 (h.2.1 σ' ⟨h'.1.le, hlt⟩)

/-- **An interval swallowed at once.** If `0 < x ≤ v ≤ y` and `x`, `y` are swallowed at the same
time `σ`, so is `v` (aliveness is monotone in the starting point,
`QuantumZipper.RS.exists_isForwardSol_of_lt`). -/
theorem realSwallowAt_of_le_of_le (hW : Continuous W) (hW0 : W 0 = 0) {x v y σ : ℝ}
    (hx : 0 < x) (hxv : x ≤ v) (hvy : v ≤ y) (hxs : RealSwallowAt W x σ)
    (hys : RealSwallowAt W y σ) : RealSwallowAt W v σ := by
  refine ⟨hxs.1, fun s hs => ?_, fun ⟨u, hu⟩ => ?_⟩
  · obtain ⟨u, hu⟩ := hxs.2.1 s hs
    rcases hxv.lt_or_eq with h | h
    · exact exists_isForwardSol_of_lt hW hs.1 (by rw [hW0]; exact hx) h hu
    · exact ⟨u, h ▸ hu⟩
  · rcases hvy.lt_or_eq with h | h
    · exact hys.2.2 (exists_isForwardSol_of_lt hW hxs.1.le (by rw [hW0]; linarith) h hu)
    · exact hys.2.2 ⟨u, h ▸ hu⟩

/-- Reflection of real solutions: `W ↦ −W`, `x ↦ −x`. -/
theorem isForwardSol_neg_iff {z : ℂ} {T : ℝ} {u : ℝ → ℂ} :
    IsForwardSol (fun t => -W t) (-z) T (fun t => -u t) ↔ IsForwardSol W z T u := by
  refine ⟨fun h => ?_, isForwardSol_neg⟩
  have h' := isForwardSol_neg h
  simp only [neg_neg] at h'
  exact h'

theorem exists_isForwardSol_neg_iff {x T : ℝ} :
    (∃ v, IsForwardSol (fun t => -W t) ((-x : ℝ) : ℂ) T v) ↔ ∃ v, IsForwardSol W (x : ℂ) T v := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun t => -v t, ?_⟩
    have h := isForwardSol_neg hv
    simp only [neg_neg, Complex.ofReal_neg] at h
    exact h
  · rintro ⟨v, hv⟩
    refine ⟨fun t => -v t, ?_⟩
    have h := isForwardSol_neg hv
    simpa only [Complex.ofReal_neg] using h

theorem realSwallowAt_neg_iff {x σ : ℝ} :
    RealSwallowAt (fun t => -W t) (-x) σ ↔ RealSwallowAt W x σ := by
  simp only [RealSwallowAt, exists_isForwardSol_neg_iff]

theorem fwdMap_neg_real (hW : Continuous W) {x T : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap (fun s => -W s) t ((-x : ℝ) : ℂ) = -fwdMap W t x := by
  have h := isForwardSol_neg hv
  rw [← Complex.ofReal_neg] at h
  rw [fwdMap_eq_of_isForwardSol (W := fun s => -W s) (by fun_prop) h ht,
    fwdMap_eq_of_isForwardSol hW hv ht]

end InteractingSLE
