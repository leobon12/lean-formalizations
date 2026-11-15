/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCDet
import InteractingSLE.Spec.Coupling.MartMeans2Announce

/-!
# The threshold of geometric force points is announced; (Det) without an announcing input

Packet PROVE-FCDET. K2's driving equations (E) (`ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun`)
need an announcing sequence of the continuation's lifetime. For a continuation known only through its chart driver
`W` (a continuous path, not yet known to solve any equation), the lifetime is the threshold of the geometric images
`geomLW W xL`, `geomRW W xR`. PROVE-T11-ANN's construction (`Coupling.exists_isAnnouncingSeq_le_of_adaptedBefore`,
`Coupling.AnnouncePath`) assumes an integrated evolution (`Sec2.IsForcePath`); its proof uses the force equations only
to show that merged force points stay merged. For geometric images this is a deterministic Loewner fact:

* **`gImg_sub_anti`**, **`rightImg_sub_anti`**: the gap between two images is nonincreasing in time (the Loewner
  equation `∂ₜ g = 2/(g − w)` for alive points, then infima over alive points);
* `IsAnnPath`: the pathwise conditions the candidates use, with `gapL_anti`, `gapR_anti` in place of the equations;
  `IsAnnPath.reflect` and copies of PROVE-T11-ANN's deterministic lemmas (`IsAnnPath.exists_bdd_candTime`, …);
* **`exists_isAnnouncingSeq_le_of_isAnnPath`**: the selection argument of PROVE-T11-ANN from `IsAnnPath`, a positive
  lifetime and a threshold limit state at a finite lifetime;
* **`isAnnPath_geom`**, `exists_tendsto_threshold_geom`, **`exists_isAnnouncingSeq_thr`**: the threshold of
  geometric images of a continuous driver is announced in every right-continuous filtration containing the null sets
  in which the driver is adapted, once it is almost surely positive;
* **`ae_codeMatch_of_hasSafeLaw'`**: `FCDet.ae_codeMatch_of_hasSafeLaw` with the announcing sequence supplied.

Provenance: the `IsAnnPath` lemmas and `exists_isAnnouncingSeq_le_of_isAnnPath` are copies of
`Coupling.{eventually_le_hitL, le_sideGap_of_bdd, hitL_eq_of_bdd, exists_bdd_hitL, eventually_le_hitL_of_bdd,
exists_eventually_le_candTime, exists_bdd_candTime, exists_isAnnouncingSeq_le_of_adaptedBefore}` with
`Sec2.IsForcePath` replaced by `IsAnnPath`; `gImg_sub_anti` follows the proof of
`MartChar.RealFlow.cflow_lt_and_sub_le`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCDet

open MartChar.RealFlow in
/-- **The gap between two alive images is nonincreasing in time** (both satisfy the Loewner equation
`∂ₜ g = 2/(g − w)`, and `g(y') > g(y) > w`): `g_{s'}(y') − g_{s'}(y) ≤ g_s(y') − g_s(y)` for `s ≤ s' ≤ t`. -/
theorem gImg_sub_anti {w : ℝ → ℝ} (hw : Continuous w) {y y' t : ℝ} (h : Alive w y t) (hyy : y < y')
    (ht : 0 ≤ t) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s ≤ s') (hs't : s' ≤ t) :
    gImg w y' s' - gImg w y s' ≤ gImg w y' s - gImg w y s := by
  obtain ⟨n, hn⟩ := (alive_iff_regFlow hw ht).1 h
  set ε : ℝ := 1 / ((n : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hlt : ∀ r ∈ Icc 0 t, regFlow w ε y r < regFlow w ε y' r := fun r hr =>
    regFlow_lt_regFlow hw hε0 hyy hr.1
  have hn' : ∀ r ∈ Icc 0 t, ε ≤ regFlow w ε y' r := fun r hr => (hn r hr).trans (hlt r hr).le
  set D : ℝ → ℝ := fun r => regFlow w ε y' r - regFlow w ε y r with hD
  have hDc : ContinuousOn D (Icc 0 t) :=
    ((continuousOn_regFlow hw hε0 y').sub (continuousOn_regFlow hw hε0 y)).mono fun r hr => hr.1
  have hanti : AntitoneOn D (Icc 0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t) hDc
      (f' := fun u => Bessel.regDrift 2 ε (regFlow w ε y' u) - Bessel.regDrift 2 ε (regFlow w ε y u))
      (fun u hu => ?_) (fun u hu => ?_)
    · rw [interior_Icc] at hu
      exact (hasDerivAt_regFlow_sub hw hε0 y y' hu.1).hasDerivWithinAt
    · rw [interior_Icc] at hu
      have hu' : u ∈ Icc 0 t := Ioo_subset_Icc_self hu
      rw [Bessel.regDrift_of_le (hn' u hu'), Bessel.regDrift_of_le (hn u hu')]
      have h1 := hε0.trans_le (hn u hu')
      have h2 := hlt u hu'
      rw [sub_nonpos]
      exact div_le_div_of_nonneg_left zero_le_two h1 h2.le
  have hsI : s ∈ Icc 0 t := ⟨hs, hss'.trans hs't⟩
  have hs'I : s' ∈ Icc 0 t := ⟨hs.trans hss', hs't⟩
  have key := hanti hsI hs'I hss'
  have e : ∀ r ∈ Icc 0 t, gImg w y' r - gImg w y r = D r := fun r hr => by
    simp only [gImg, hD, cflow_eq_regFlow hw hε0 hn hr, cflow_eq_regFlow hw hε0 hn' hr]
    ring
  rw [e s' hs'I, e s hsI]
  exact key

open MartChar.RealFlow in
/-- **The gap between two geometric images is nonincreasing in time**: for `x ≤ x'` and `0 ≤ s ≤ t`,
`V_t(x') − V_t(x) ≤ V_s(x') − V_s(x)` for the right images `V(x) = rightImg w x`. -/
theorem rightImg_sub_anti {w : ℝ → ℝ} (hw : Continuous w) {x x' : ℝ} (hxx : x ≤ x') {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) :
    rightImg w x' t - rightImg w x t ≤ rightImg w x' s - rightImg w x s := by
  have ht : 0 ≤ t := hs.trans hst
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- an alive point `y > x` at time `t` with `g_t(y)` close to `V_t(x)`
  obtain ⟨y, hxy, hy, hyt⟩ := exists_lt_of_rightImg_lt hw ht
    (show rightImg w x t < rightImg w x t + ε / 2 by linarith)
  have hgap_s : 0 ≤ rightImg w x' s - rightImg w x s := sub_nonneg.2 (rightImg_mono_index hw hs hxx)
  rcases lt_or_ge x' y with hx'y | hyx'
  · -- `y > x'`: the gap at time `t` is below `ε/2`
    have h1 : rightImg w x' t ≤ gImg w y t := rightImg_le_gImg hw ht hx'y hy
    linarith
  · -- `y ≤ x'`: compare with an alive point `y' > x'` near `V_s(x')`
    obtain ⟨y', hx'y', hy', hy's⟩ := exists_lt_of_rightImg_lt hw hs
      (show rightImg w x' s < rightImg w x' s + ε / 2 by linarith)
    have hyy' : y < y' := lt_of_le_of_lt hyx' hx'y'
    have hy't : Alive w y' t := hy.of_le hw hyy'.le ht
    have h1 : rightImg w x' t ≤ gImg w y' t := rightImg_le_gImg hw ht hx'y' hy't
    have h2 : rightImg w x s ≤ gImg w y s := rightImg_le_gImg hw hs hxy (hy.mono hst)
    have h3 := gImg_sub_anti hw hy hyy' ht hs hst le_rfl
    linarith

/-! ### The pathwise conditions of the announcing construction -/

section AnnPath

open Coupling

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The pathwise conditions of PROVE-T11-ANN's candidates**: the conditions of `Sec2.IsForcePath` that the
candidates use (continuity, order, no threshold before `ζ`), with the integrated force equations replaced by what
they were used for: the gaps between neighbouring force points are nonincreasing ("merged force points stay
merged"). Geometric images of a continuous driver satisfy them up to their threshold (`isAnnPath_geom`). -/
structure IsAnnPath (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop where
  continuousOn_w : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}
  continuousOn_vL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}
  continuousOn_vR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}
  antitone_vL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → Antitone fun i => vL i t
  vL_le_w : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i, vL i t ≤ w t
  w_le_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i, w t ≤ vR i t
  monotone_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → Monotone fun i => vR i t
  not_threshold : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
    ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun i => vR i t)
  gapL_anti : ∀ (j : Fin nL) {s s' : ℝ≥0}, s ≤ s' → (s' : ℝ≥0∞) < ζ →
    sideGap (fun i => vL i s') j ≤ sideGap (fun i => vL i s) j
  gapR_anti : ∀ (j : Fin nR) {s s' : ℝ≥0}, s ≤ s' → (s' : ℝ≥0∞) < ζ →
    sideGap (fun i => -vR i s') j ≤ sideGap (fun i => -vR i s) j

namespace IsAnnPath

/-- **Reflection**: `(−w, −v^R, −v^L)` with the sides exchanged. -/
theorem reflect (h : IsAnnPath ρL ρR w vL vR ζ) :
    IsAnnPath ρR ρL (-w) (fun i => -vR i) (fun i => -vL i) ζ where
  continuousOn_w := h.continuousOn_w.neg
  continuousOn_vL i := (h.continuousOn_vR i).neg
  continuousOn_vR i := (h.continuousOn_vL i).neg
  antitone_vL ht _ _ hij := neg_le_neg (h.monotone_vR ht hij)
  vL_le_w ht i := neg_le_neg (h.w_le_vR ht i)
  w_le_vR ht i := neg_le_neg (h.vL_le_w ht i)
  monotone_vR ht _ _ hij := neg_le_neg (h.antitone_vL ht hij)
  not_threshold ht hth := h.not_threshold ht (Sec2.thresholdCondition_neg_iff.1 hth)
  gapL_anti j _ _ hss' hs' := h.gapR_anti j hss' hs'
  gapR_anti j _ _ hss' hs' := by
    simp only [Pi.neg_apply, neg_neg]
    exact h.gapL_anti j hss' hs'

theorem continuousOn_sideVal_path (h : IsAnnPath ρL ρR w vL vR ζ) (m : ℕ) (j : Fin nL) :
    ContinuousOn (fun s => sideVal m j (w s) fun i => vL i s) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} :=
  (continuous_sideVal m j).comp_continuousOn
    (h.continuousOn_w.prodMk (continuousOn_pi.2 h.continuousOn_vL))

theorem pos_sideVal (h : IsAnnPath ρL ρR w vL vR ζ) {m : ℕ} {j : Fin nL}
    (hsum : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) :
    0 < sideVal m j (w s) fun i => vL i s :=
  sideVal_pos (h.antitone_vL hs) (h.vL_le_w hs) hsum fun hth => h.not_threshold hs (Or.inl hth)

/-- Every time before `ζ` is eventually below the candidates of a cluster of weight `≤ −2`
(`Coupling.eventually_le_hitL`). -/
theorem eventually_le_hitL (h : IsAnnPath ρL ρR w vL vR ζ) {m : ℕ} {j : Fin nL}
    (hsum : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∀ᶠ k : ℕ in atTop, (t : WithTop ℝ≥0) ≤ hitL ρL w vL ζ j m k := by
  simp only [hitL, hsum, ↓reduceIte]
  exact eventually_le_hitBelow (continuousOn_sideVal_path h m j) (fun s hs => pos_sideVal h hsum hs) ht

/-- Along a bounded candidate the gap stays at least `1/(m+1)` (`Coupling.le_sideGap_of_bdd`). -/
theorem le_sideGap_of_bdd (h : IsAnnPath ρL ρR w vL vR ζ) {j : Fin nL} {m : ℕ}
    (hb : ∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < ζ) : 1 / ((m : ℝ) + 1) ≤ sideGap (fun i => vL i s) j := by
  obtain ⟨hsum, hlt⟩ := hitL_lt_of_bdd hb
  choose t ht htζ using hlt
  have hev : ∀ᶠ k : ℕ in atTop, 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1) ≤ sideGap (fun i => vL i s) j := by
    filter_upwards [eventually_le_hitL h (m := m) hsum hs] with k hk
    rw [ht k] at hk
    have hsk : s ≤ t k := WithTop.coe_le_coe.1 hk
    have hval : sideVal m j (w (t k)) (fun i => vL i (t k)) ≤ 1 / ((k : ℝ) + 1) := by
      have := ht k
      simp only [hitL, hsum, ↓reduceIte] at this
      exact le_of_hitBelow_eq (continuousOn_sideVal_path h m j) this
    have h1 := sub_sideGap_le_sideVal m j (w (t k)) (fun i => vL i (t k))
    have h2 := h.gapL_anti j hsk (htζ k)
    linarith
  have hlim : Tendsto (fun k : ℕ => 1 / ((m : ℝ) + 1) - 1 / ((k : ℝ) + 1)) atTop
      (𝓝 (1 / ((m : ℝ) + 1) - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim hev

/-- A bounded candidate is the hitting sequence of `|w − v^j|` (`Coupling.hitL_eq_of_bdd`). -/
theorem hitL_eq_of_bdd (h : IsAnnPath ρL ρR w vL vR ζ) {j : Fin nL} {m : ℕ}
    (hb : ∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) (k : ℕ) :
    hitL ρL w vL ζ j m k = hitBelow (fun s => |w s - vL j s|) ζ (1 / ((k : ℝ) + 1)) := by
  have hsum := (hitL_lt_of_bdd hb).1
  simp only [hitL, hsum, ↓reduceIte]
  refine hitBelow_congr fun s hs => ?_
  have hg := le_sideGap_of_bdd h hb hs
  simp only [sideVal]
  rw [max_eq_left (by linarith), add_zero]

/-- At a finite lifetime with a threshold limit state, some candidate is bounded (`Coupling.exists_bdd_hitL`). -/
theorem exists_bdd_hitL (h : IsAnnPath ρL ρR w vL vR ζ) {T : ℝ≥0} (hT : 0 < T)
    (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ}
    (hlim : Tendsto (fun s => (w s, fun i => vL i s)) (𝓝[<] T) (𝓝 (w₀, vL₀)))
    (hth : (∑ i ∈ Finset.univ.filter (fun i => vL₀ i = w₀), ρL i) ≤ -2) :
    ∃ (j : Fin nL) (m : ℕ), ∀ k, hitL ρL w vL ζ j m k ≤ (T : WithTop ℝ≥0) := by
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hev_lt : ∀ᶠ s : ℝ≥0 in 𝓝[<] T, (s : ℝ≥0∞) < ζ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← hTζ]
    exact_mod_cast hs
  have hw : Tendsto w (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hlim
  have hv : ∀ i, Tendsto (fun s => vL i s) (𝓝[<] T) (𝓝 (vL₀ i)) := fun i =>
    ((continuous_apply i).tendsto _).comp ((continuous_snd.tendsto _).comp hlim)
  have hanti₀ : Antitone vL₀ := fun i i' hii' =>
    le_of_tendsto_of_tendsto (hv i') (hv i) (hev_lt.mono fun _ hs => h.antitone_vL hs hii')
  have hle₀ : ∀ i, vL₀ i ≤ w₀ := fun i =>
    le_of_tendsto_of_tendsto (hv i) hw (hev_lt.mono fun _ hs => h.vL_le_w hs i)
  set C := Finset.univ.filter (fun i => vL₀ i = w₀) with hC
  have hCne : C.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hth
    norm_num at hth
  set j := C.max' hCne with hj_def
  have hvj : vL₀ j = w₀ := (Finset.mem_filter.1 (C.max'_mem hCne)).2
  have hCeq : C = Finset.Iic j := by
    ext i
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    constructor
    · intro hi
      exact C.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    · intro hij
      exact le_antisymm (hle₀ i) (hvj ▸ hanti₀ hij)
  have hsum : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2 := hCeq ▸ hth
  have hgap : 0 < sideGap vL₀ j := by
    by_cases hj : j.1 + 1 < nL
    · simp only [sideGap, hj, ↓reduceDIte]
      have hnot : (⟨j.1 + 1, hj⟩ : Fin nL) ∉ C := fun hmem => by
        have := Fin.le_def.1 (C.le_max' _ hmem)
        simp only [← hj_def] at this
        omega
      have hne : vL₀ ⟨j.1 + 1, hj⟩ ≠ w₀ := fun he => hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩)
      have hle : vL₀ ⟨j.1 + 1, hj⟩ ≤ vL₀ j := hanti₀ (Fin.le_def.2 (Nat.le_succ _))
      rw [hvj] at hle ⊢
      exact sub_pos.2 (lt_of_le_of_ne hle hne)
    · simp only [sideGap, hj, ↓reduceDIte]
      exact one_pos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hgap
  have hval : sideVal m j w₀ vL₀ = 0 := by
    simp only [sideVal, hvj, sub_self, abs_zero, zero_add]
    exact max_eq_left (by linarith)
  have htend : Tendsto (fun s => sideVal m j (w s) fun i => vL i s) (𝓝[<] T) (𝓝 0) := by
    rw [← hval]
    exact ((continuous_sideVal m j).tendsto _).comp hlim
  refine ⟨j, m, fun k => ?_⟩
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨s, hsT, hsζ, hfs⟩ :=
    (eventually_mem_nhdsWithin.and (hev_lt.and (htend.eventually (gt_mem_nhds hk)))).exists
  simp only [hitL, hsum, ↓reduceIte]
  exact (hitBelow_le hsζ hfs).trans (WithTop.coe_le_coe.2 (le_of_lt hsT))

/-- For one left cluster, all bounded candidates eventually pass a time `t < ζ`, from one index on
(`Coupling.eventually_le_hitL_of_bdd`). -/
theorem eventually_le_hitL_of_bdd (h : IsAnnPath ρL ρR w vL vR ζ) (j : Fin nL) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    ∀ᶠ K : ℕ in atTop, ∀ m, (∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) →
      ∀ k, K ≤ k → (t : WithTop ℝ≥0) ≤ hitL ρL w vL ζ j m k := by
  by_cases hex : ∃ m₀, ∃ M : ℕ, ∀ k, hitL ρL w vL ζ j m₀ k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)
  · obtain ⟨m₀, hb₀⟩ := hex
    obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_le_hitL h (m := m₀) (hitL_lt_of_bdd hb₀).1 ht)
    refine eventually_atTop.2 ⟨K, fun K' hK' m hb k hk => ?_⟩
    rw [hitL_eq_of_bdd h hb k, ← hitL_eq_of_bdd h hb₀ k]
    exact hK k (hK'.trans hk)
  · exact Eventually.of_forall fun K m hb => absurd ⟨m, hb⟩ hex

/-- Uniformity over the bounded candidates (`Coupling.exists_eventually_le_candTime`). -/
theorem exists_eventually_le_candTime (h : IsAnnPath ρL ρR w vL vR ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    ∃ K : ℕ, ∀ p, (∃ M : ℕ, ∀ k, candTime ρL ρR w vL vR ζ p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0)) →
      ∀ k, K ≤ k → (t : WithTop ℝ≥0) ≤ candTime ρL ρR w vL vR ζ p k := by
  have hL := eventually_all.2 fun j => eventually_le_hitL_of_bdd h j ht
  have hR := eventually_all.2 fun j => eventually_le_hitL_of_bdd h.reflect j ht
  obtain ⟨K, hKL, hKR⟩ := (hL.and hR).exists
  refine ⟨K, fun p hp k hk => ?_⟩
  by_cases hc : (Nat.unpair p).1 < nL
  · simp only [candTime, hc, ↓reduceDIte] at hp ⊢
    exact hKL _ _ hp k hk
  by_cases hc' : (Nat.unpair p).1 - nL < nR
  · simp only [candTime, hc, hc', ↓reduceDIte] at hp ⊢
    exact hKR _ _ hp k hk
  · simp only [candTime, hc, hc', ↓reduceDIte]
    exact le_top

/-- At a finite lifetime some candidate is bounded (`Coupling.exists_bdd_candTime`). -/
theorem exists_bdd_candTime (h : IsAnnPath ρL ρR w vL vR ζ) {T : ℝ≥0} (hT : 0 < T)
    (hTζ : (T : ℝ≥0∞) = ζ) {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ}
    (hlim : Tendsto (fun s => (w s, fun i => vL i s, fun i => vR i s)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)))
    (hth : ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    ∃ p, ∃ M : ℕ, ∀ k, candTime ρL ρR w vL vR ζ p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0) := by
  have hTM : (T : WithTop ℝ≥0) ≤ ((⌈T⌉₊ : ℕ) : ℝ≥0) := WithTop.coe_le_coe.2 (Nat.le_ceil T)
  rcases hth with hl | hr
  · have hlim' : Tendsto (fun s => (w s, fun i => vL i s)) (𝓝[<] T) (𝓝 (w₀, vL₀)) :=
      ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).tendsto _).comp hlim
    obtain ⟨j, m, hjm⟩ := exists_bdd_hitL h hT hTζ hlim' hl
    refine ⟨Nat.pair j.1 m, ⌈T⌉₊, fun k => ?_⟩
    have hc : (Nat.unpair (Nat.pair j.1 m)).1 < nL := by rw [Nat.unpair_pair]; exact j.2
    have e : candTime ρL ρR w vL vR ζ (Nat.pair j.1 m) k = hitL ρL w vL ζ j m k := by
      simp only [candTime, hc, ↓reduceDIte]
      congr 1
      · exact Fin.ext (by simp only [Nat.unpair_pair])
      · simp only [Nat.unpair_pair]
    rw [e]
    exact (hjm k).trans hTM
  · have hlim' : Tendsto (fun s => ((-w) s, fun i => (fun i => -vR i) i s)) (𝓝[<] T)
        (𝓝 (-w₀, fun i => -vR₀ i)) :=
      ((continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd).neg).tendsto _).comp hlim
    have hr' : (∑ i ∈ Finset.univ.filter (fun i => (fun i => -vR₀ i) i = -w₀), ρR i) ≤ -2 := by
      simpa only [neg_inj] using hr
    obtain ⟨j, m, hjm⟩ := exists_bdd_hitL h.reflect hT hTζ hlim' hr'
    refine ⟨Nat.pair (nL + j.1) m, ⌈T⌉₊, fun k => ?_⟩
    have hc : ¬ (Nat.unpair (Nat.pair (nL + j.1) m)).1 < nL := by
      rw [Nat.unpair_pair]; omega
    have hc' : (Nat.unpair (Nat.pair (nL + j.1) m)).1 - nL < nR := by
      rw [Nat.unpair_pair]; omega
    have e : candTime ρL ρR w vL vR ζ (Nat.pair (nL + j.1) m) k =
        hitL ρR (-w) (fun i => -vR i) ζ j m k := by
      simp only [candTime, hc, hc', ↓reduceDIte]
      congr 1
      · exact Fin.ext (by simp only [Nat.unpair_pair]; omega)
      · simp only [Nat.unpair_pair]
    rw [e]
    exact (hjm k).trans hTM

end IsAnnPath

end AnnPath

/-! ### The announcing sequence -/

section Announce

open Coupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

open scoped Classical in
/-- **An announcing sequence from the pathwise conditions** (`Coupling.exists_isAnnouncingSeq_le_of_adaptedBefore`
with the integrated evolution replaced by its two uses: the pathwise conditions `IsAnnPath` and a threshold limit
state at a finite lifetime; the positivity of `ζ` replaces the admissible seed). In a right-continuous filtration
containing the measurable null sets, in which the coordinates are adapted before `ζ`, the lifetime has an announcing
sequence `T_n ≤ n`. -/
theorem exists_isAnnouncingSeq_le_of_isAnnPath [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hWa : AdaptedBefore 𝓖 ζ W)
    (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (hae : ∀ᵐ ω ∂P, IsAnnPath ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) ∧
      0 < ζ ω ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq 𝓖 P ζ T ∧ ∀ n ω, T n ω ≤ n := by
  set good : Ω → Prop := fun ω =>
    IsAnnPath ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) ∧
      0 < ζ ω ∧ ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ ω →
        ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
          Tendsto (fun t => (W t ω, fun i => VL i t ω, fun i => VR i t ω)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
          ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ with hgood
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓖 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hF : ∀ ω ∈ G, IsAnnPath ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) :=
    fun ω hω => (hGgood ω hω).1
  have hcont : ∀ ω ∈ G, ContinuousOn (fun s => stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
    fun ω hω => (hF ω hω).continuousOn_w.prodMk ((continuousOn_pi.2 (hF ω hω).continuousOn_vL).prodMk
      (continuousOn_pi.2 (hF ω hω).continuousOn_vR))
  set a : ℕ → ℕ → Ω → WithTop ℝ≥0 := fun p k ω => if ω ∈ G then
    candTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k else ⊤
    with ha_def
  have hatop : ∀ p k, (∀ ω ∈ G, candTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (ζ ω) p k = ⊤) → IsStoppingTime 𝓖 (a p k) := by
    intro p k htop
    have : a p k = fun _ => ⊤ := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [ha_def, hω, ite_true]; exact htop ω hω
      · simp only [ha_def, hω, ite_false]
    rw [this]
    exact isStoppingTime_top'
  have ha : ∀ p k, IsStoppingTime 𝓖 (a p k) := by
    intro p k
    by_cases hc : (Nat.unpair p).1 < nL
    · set j : Fin nL := ⟨(Nat.unpair p).1, hc⟩ with hj
      set m := (Nat.unpair p).2 with hm
      by_cases hs : (∑ i ∈ Finset.Iic j, ρL i) ≤ -2
      · have e : a p k = fun ω => if ω ∈ G then hitBelow (fun s =>
            (fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => sideVal m j x.1 x.2.1) (stateAt W VL VR s ω))
            (ζ ω) (1 / ((k : ℝ) + 1)) else ⊤ := by
          funext ω
          simp only [ha_def, candTime, hc, ↓reduceDIte, hitL, ← hj, ← hm, hs, ↓reduceIte, stateAt]
        rw [e]
        exact isStoppingTime_hitBelow_state hWa hVLa hVRa hG0 hcont
          ((continuous_sideVal m j).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) _
      · exact hatop p k fun ω _ => by
          simp only [candTime, hc, ↓reduceDIte, hitL, ← hj, hs, ↓reduceIte]
    by_cases hc' : (Nat.unpair p).1 - nL < nR
    · set j : Fin nR := ⟨(Nat.unpair p).1 - nL, hc'⟩ with hj
      set m := (Nat.unpair p).2 with hm
      by_cases hs : (∑ i ∈ Finset.Iic j, ρR i) ≤ -2
      · have e : a p k = fun ω => if ω ∈ G then hitBelow (fun s =>
            (fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => sideVal m j (-x.1) (-x.2.2))
              (stateAt W VL VR s ω)) (ζ ω) (1 / ((k : ℝ) + 1)) else ⊤ := by
          funext ω
          simp only [ha_def, candTime, hc, hc', ↓reduceDIte, hitL, ← hj, ← hm, hs, ↓reduceIte, stateAt]
          rfl
        rw [e]
        exact isStoppingTime_hitBelow_state hWa hVLa hVRa hG0 hcont
          ((continuous_sideVal m j).comp
            (continuous_fst.neg.prodMk (continuous_snd.comp continuous_snd).neg)) _
      · exact hatop p k fun ω _ => by
          simp only [candTime, hc, hc', ↓reduceDIte, hitL, ← hj, hs, ↓reduceIte]
    · exact hatop p k fun ω _ => by simp only [candTime, hc, hc', ↓reduceDIte]
  have hmono : ∀ p ω, Monotone fun k => a p k ω := by
    intro p ω
    by_cases hω : ω ∈ G
    · simp only [ha_def, hω, ite_true]
      exact candTime_mono p
    · simp only [ha_def, hω, ite_false]
      exact monotone_const
  have hbdd : ∀ ω ∈ G, ∀ p, BddSeq (a p) ω ↔ ∃ M : ℕ, ∀ k, candTime ρL ρR (fun t => W t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (ζ ω) p k ≤ ((M : ℝ≥0) : WithTop ℝ≥0) := by
    intro ω hω p
    simp only [BddSeq, ha_def, hω, ite_true]
  refine exists_isAnnouncingSeq_le_of_candidates ha hmono ?_ ?_ ?_
  · filter_upwards [hGae] with ω hω p hp k
    have := candTime_lt_of_bdd ((hbdd ω hω p).1 hp) k
    simpa only [ha_def, hω, ite_true] using this
  · filter_upwards [hGae] with ω hω t ht
    obtain ⟨K, hK⟩ := (hF ω hω).exists_eventually_le_candTime ht
    refine ⟨K, fun p hp k hk => ?_⟩
    have := hK p ((hbdd ω hω p).1 hp) k hk
    simpa only [ha_def, hω, ite_true] using this
  · filter_upwards [hGae] with ω hω hζ
    have hTζ : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hζ
    have hT : 0 < (ζ ω).toNNReal := ENNReal.toNNReal_pos (hGgood ω hω).2.1.ne' hζ
    obtain ⟨w₀, vL₀, vR₀, hlim, hth⟩ := (hGgood ω hω).2.2 _ hT hTζ
    obtain ⟨p, hp⟩ := (hF ω hω).exists_bdd_candTime hT hTζ hlim hth
    exact ⟨p, (hbdd ω hω p).2 hp⟩

end Announce

/-! ### Geometric images up to their threshold -/

section Geom

open Coupling Sec7.PocketTraversal MartChar.RealFlow

variable {Ω : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}

/-- **Geometric images satisfy the pathwise conditions up to their threshold.** -/
theorem isAnnPath_geom (hWc : ∀ ω, Continuous fun t => W t ω) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω)) (ω : Ω) :
    IsAnnPath ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω) (fun j t => geomRW W xR j t ω)
      (thr ρL ρR W xL xR ω) where
  continuousOn_w := (hWc ω).continuousOn
  continuousOn_vL i := (isForcePath_geomLW hWc xL ω i).1.continuousOn
  continuousOn_vR j := (isForcePath_geomRW hWc xR ω j).1.continuousOn
  antitone_vL {t} _ := antitone_index_geomLW hWc (hxLa ω) t
  vL_le_w {t} _ i := geomLW_le hWc xL ω t i
  w_le_vR {t} _ j := le_geomRW hWc xR ω t j
  monotone_vR {t} _ := monotone_index_geomRW hWc (hxRm ω) t
  not_threshold {t} ht := MartChar.notMem_thresholdSet_of_lt ht
  gapL_anti j s s' hss' _ := by
    by_cases hj : j.1 + 1 < nL
    · simp only [sideGap, hj, ↓reduceDIte, geomLW]
      have hc : Continuous (Bessel.realPath (fun t ω => -W t ω) ω) :=
        Bessel.continuous_realPath (fun ω => (hWc ω).neg) ω
      have hx : -xL ω j ≤ -xL ω ⟨j.1 + 1, hj⟩ := neg_le_neg (hxLa ω (Fin.le_def.2 (Nat.le_succ _)))
      have := rightImg_sub_anti hc hx s.coe_nonneg (NNReal.coe_le_coe.2 hss')
      linarith
    · simp only [sideGap, hj, ↓reduceDIte, le_refl]
  gapR_anti j s s' hss' _ := by
    by_cases hj : j.1 + 1 < nR
    · simp only [sideGap, hj, ↓reduceDIte, geomRW]
      have hx : xR ω j ≤ xR ω ⟨j.1 + 1, hj⟩ := hxRm ω (Fin.le_def.2 (Nat.le_succ _))
      have := rightImg_sub_anti (Bessel.continuous_realPath hWc ω) hx s.coe_nonneg (NNReal.coe_le_coe.2 hss')
      linarith
    · simp only [sideGap, hj, ↓reduceDIte, le_refl]

/-- **At a finite threshold the state converges to a threshold state** (the coordinates are continuous at the
threshold, which is attained). -/
theorem exists_tendsto_threshold_geom (hWc : ∀ ω, Continuous fun t => W t ω) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (ω : Ω) {T : ℝ≥0} (hT : (T : ℝ≥0∞) = thr ρL ρR W xL xR ω) :
    ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (W t ω, fun i => geomLW W xL i t ω, fun j => geomRW W xR j t ω)) (𝓝[<] T)
        (𝓝 (w₀, vL₀, vR₀)) ∧ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  refine ⟨W T ω, fun i => geomLW W xL i T ω, fun j => geomRW W xR j T ω, ?_, ?_⟩
  · have hc : Continuous fun t => (W t ω, fun i => geomLW W xL i t ω, fun j => geomRW W xR j t ω) :=
      (hWc ω).prodMk ((continuous_pi fun i => (isForcePath_geomLW hWc xL ω i).1).prodMk
        (continuous_pi fun j => (isForcePath_geomRW hWc xR ω j).1))
    exact (hc.tendsto T).mono_left nhdsWithin_le_nhds
  · have := thr_mem_thresholdSet (ρL := ρL) (ρR := ρR) hWc xL xR (ω := ω) hT.symm
    exact this

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The threshold of geometric images has an announcing sequence** in every right-continuous filtration
containing the measurable null sets in which the driver is adapted and the word initial, as soon as the threshold
is almost surely positive. -/
theorem exists_isAnnouncingSeq_thr [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓖 W) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝓖 0] xL)
    (hxR : Measurable[𝓖 0] xR) (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω))
    (hpos : ∀ᵐ ω ∂P, 0 < thr ρL ρR W xL xR ω) :
    ∃ T : ℕ → Ω → ℝ≥0, IsAnnouncingSeq 𝓖 P (thr ρL ρR W xL xR) T ∧ ∀ n ω, T n ω ≤ n := by
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω | thr ρL ρR W xL xR ω ≤ t} :=
    measurableSet_thr_le hWc hWa hxL hxR
  refine exists_isAnnouncingSeq_le_of_isAnnPath (ρL := ρL) (ρR := ρR) hnull
    (MartChar.adaptedBefore_of_stronglyAdapted hζm hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (stronglyAdapted_geomLW hWa hWc hxL i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (stronglyAdapted_geomRW hWa hWc hxR j)) ?_
  filter_upwards [hpos] with ω hω
  exact ⟨isAnnPath_geom hWc hxLa hxRm ω, hω, fun T _ hT => exists_tendsto_threshold_geom hWc xL xR ω hT⟩

end Geom

/-! ### (Det) from (S) and (L), with the announcing sequence supplied -/

section Det

open DomainMarkov.K2 Sec7.PocketTraversal

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **(Det) from (S) and (L)** (`ae_codeMatch_of_hasSafeLaw` with the announcing sequence of the threshold supplied
by `exists_isAnnouncingSeq_thr` in the usual augmentation of `𝓗`). On a standard Borel space in `Type`: a globally
continuous driver `W` from `0`, adapted to `𝓗`, with the geometric images of a sorted `𝒢`-measurable word of flow-line
type almost surely and an admissible seed; the field `X = Hc + θχ` with integrable pairings; K2's inputs (S), (L) up
to the threshold with the live event `univ`; a globally continuous path that is almost surely the generating trace of
`W` up to the threshold. Then almost surely the path is the decoded canonical flow code of `(c, Hc)`. -/
theorem ae_codeMatch_of_hasSafeLaw' {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} (hκ : 0 < κ)
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0) {c : Ω → BoundaryWord} (hc : Measurable[𝒢] c)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) (htype : ∀ᵐ ω ∂P, IsFlowType κ θ (c ω) (xL ω) (xR ω) ρL ρR)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓗 W) {Hc X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    (hX : Measurable X) (hXH : ∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (Hc ω) (X ω))
    (hint : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hseed : ∀ᵐ ω ∂P, ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL ω) (xR ω))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 univ (thr ρL ρR W xL xR) W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 univ (thr ρL ρR W xL xR) W X) {γ : Ω → ℝ≥0 → ℂ}
    (hγ : ∀ t, Measurable fun ω => γ ω t) (hγc : ∀ ω, Continuous (γ ω))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (thr ρL ρR W xL xR ω) (γ ω))
    {F : (BoundaryWord × ℝ) × LQGMetric.DistOn upperHalfPlaneOpens →
      (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F) :
    ∀ᵐ ω ∂P, IsCodeMatch (F ((c ω, 0), Hc ω)) (γ ω) (thr ρL ρR W xL xR ω) := by
  have h0U : 𝒢 ≤ usualAugmentation 𝓗 P 0 := h𝒢.trans (Ito.le_usualAugmentation 𝓗 P 0)
  have hWaU : StronglyAdapted (usualAugmentation 𝓗 P) W := fun t =>
    (hWa t).mono (Ito.le_usualAugmentation 𝓗 P t)
  obtain ⟨T, hT, -⟩ := exists_isAnnouncingSeq_thr (ρL := ρL) (ρR := ρR) (𝓖 := usualAugmentation 𝓗 P)
    (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0) hWc hWaU (hxL.mono h0U le_rfl)
    (hxR.mono h0U le_rfl) hxLa hxRm (hseed.mono fun ω h => thr_pos hW0 hWc hxL0 hxR0 h)
  exact ae_codeMatch_of_hasSafeLaw hκ h𝒢 hc hxL hxR hxL0 hxR0 hxLa hxRm htype hW0 hWc hWa hHc hX hXH hint hseed
    hT hlaw hmem hγ hγc htr hF

end Det

end InteractingSLE.Restart.FCDet
