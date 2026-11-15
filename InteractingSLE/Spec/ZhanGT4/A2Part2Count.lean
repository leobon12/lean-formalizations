/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part2Domain
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Spec.ZhanGT4.DualA15CofinalHull
import InteractingSLE.Spec.Sec7.LocalExtGChart
import InteractingSLE.Spec.Ito.Loewner
import QuantumZipper.Proofs.Loewner.CoreArc3b
import QuantumZipper.Proofs.Loewner.ForwardFlow
import QuantumZipper.Proofs.Zipper.AreaCoordBasic
import QuantumZipper.Proofs.RS.HullBasics

/-!
# A.2, part 2: the countable argument, pathwise

Packet PROVE-ZHAN-A2P2. Source: Astra, *Follow-up proofs and dependency audit*, §A.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L537–L561; R38, R53):

> Its endpoint lies strictly between `W₂` and `g₂(p₂)`, so its crosscut separates the large tip from infinity. This
> shows that the entire large hull lies on the bounded side of `J`. The following countable argument makes the
> conditioning legitimate. If a large-curve point escapes the closed bounded side of `J`, choose a rational polygonal
> crosscut `α` that strictly encloses `J` and `x₂` but excludes that point, and choose a rational protected crosscut
> `γ` bounding an original pre-lifetime localization. Stop the large curve at its first hit of `α ∪ γ`. On the event
> that it hits `α` first while `J` is strictly inside `α`, there is an exterior path from its tip to infinity avoiding
> `J` and the stopped large hull, contrary to the conditional separation just proved. The countable union over `α, γ`
> has probability zero.

This file proves the deterministic content of that paragraph, for one sample.

* `TipSeparated w s J`: **the large tip at time `s` is separated from `∞` by `J`** — some relative neighbourhood of
  the prime end at the tip (the points `z ∉ K_s` with `|f_s(z)| < ε`, `f_s = g_s − W_s`) is cut off from `∞` by
  `K_s ∪ J` (it misses `unbddPart (K_s ∪ J)`).
* `IsFirstHit w L s`: `s` is the first time the hulls meet `L`. For a compact `L ⊆ ℍ` the first hit exists
  (`exists_isFirstHit`).
* `exists_forall_norm_fwdMap_lt_of_fresh`: **a fresh point is at the tip** — if `p` is swallowed exactly at time
  `s`, the points of `ℍ \ K_s` near `p` have `f_s` near `0` (local growth `f_t(p) → 0`, continuity of `f_t` at `p`,
  the flow property and the short-time displacement bound `24 M + 8 √h`).
* `not_tipSeparated_of_isFirstHit`: the contradiction of L559–L560 — at the first hit of `L` by hulls that stay
  off an open, preconnected, unbounded `U ⊆ ℍ` missing `J` with `L ⊆ closure U`, the tip is **not** separated
  (points of `U` near the fresh point are at the tip and reach `∞` inside `U`).
* **`disjoint_lifeHullClosure_of_tipSeparated`**: if the tip is separated at the first hit of every good rational
  chain (`chainClosed F`) inside the strip life, then the large hull before the first force collision misses the
  unbounded side `D` of `J` — the conclusion of A.2, part 2, for one sample.
* `tipSeparated_of_image`: **the pull-back** (L551–L553) — if the centred image `f_s(J₀)` of part of the small curve
  contains a crosscut from a negative to a positive real point, the tip is separated;
  `tipSeparated_of_image_of_continuousOn` is the same for a driver continuous only on `[0, t']`, `s < t'`.

The source's polygon `α` is replaced by the boundary of a finite union of rational balls joined to the far region,
and its protected crosscut by the strip life at the first hit.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2Part2

open QuantumZipper

/-! ### Definitions -/

/-- **The large tip at time `s` is separated from `∞` by `J`** (A.2 L552–L553): for some `ε > 0`, every point of
`ℍ \ K_s` whose centred image `f_s(z) = g_s(z) − W_s` lies within `ε` of `0` is cut off from `∞` by `K_s ∪ J`. -/
def TipSeparated (w : ℝ → ℝ) (s : ℝ) (J : Set ℂ) : Prop :=
  ∃ ε > (0 : ℝ), ∀ z ∈ H \ fwdHull w s, ‖fwdMap w s z‖ < ε → z ∉ unbddPart (fwdHull w s ∪ J)

/-- **`s` is the first time the hulls of `w` meet `L`.** -/
def IsFirstHit (w : ℝ → ℝ) (L : Set ℂ) (s : ℝ) : Prop :=
  0 ≤ s ∧ (fwdHull w s ∩ L).Nonempty ∧ ∀ t, 0 ≤ t → t < s → fwdHull w t ∩ L = ∅

/-! ### Hull facts -/

section Hull

variable {A : ℝ → ℝ}

theorem fwdHull_subset_of_le {W : ℝ → ℝ} {t t' : ℝ} (h : t ≤ t') : fwdHull W t ⊆ fwdHull W t' :=
  fun _ hz => ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal h)⟩

/-- **The first hit of a compact subset of `ℍ` exists** (hulls are right-continuous and the alive set is open). -/
theorem exists_isFirstHit (hA : Continuous A) {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (hhit : (fwdHull A t₀ ∩ L).Nonempty) : ∃ s, IsFirstHit A L s ∧ s ≤ t₀ := by
  set S := {t : ℝ | 0 ≤ t ∧ (fwdHull A t ∩ L).Nonempty} with hS
  have hSne : S.Nonempty := ⟨t₀, ht₀, hhit⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  have hs0 : 0 ≤ sInf S := le_csInf hSne fun t ht => ht.1
  have hst₀ : sInf S ≤ t₀ := csInf_le hSbdd ⟨ht₀, hhit⟩
  have hbefore : ∀ t, 0 ≤ t → t < sInf S → fwdHull A t ∩ L = ∅ := by
    intro t ht0 hts
    by_contra hne
    exact absurd (csInf_le hSbdd ⟨ht0, nonempty_iff_ne_empty.2 hne⟩) (not_le.2 hts)
  refine ⟨sInf S, ⟨hs0, ?_, hbefore⟩, hst₀⟩
  by_contra hempty
  have hseq : ∀ n : ℕ, ∃ t ∈ S, t < sInf S + 1 / ((n : ℝ) + 1) := fun n =>
    exists_lt_of_csInf_lt hSne (by have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := (by positivity); linarith)
  choose t ht hts using hseq
  choose p hp using fun n => (ht n).2
  obtain ⟨q, hqL, φ, hφ, hlim⟩ := hL.tendsto_subseq (fun n => (hp n).2)
  have hqK : q ∉ fwdHull A (sInf S) := fun h => hempty ⟨q, h, hqL⟩
  obtain ⟨-, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff hs0).1 ⟨hLH hqL, hqK⟩
  set T : ℝ := (sInf S + T') / 2 with hT
  have hT0 : 0 ≤ T := by rw [hT]; linarith
  have hqT : q ∈ H \ fwdHull A T := (FwdHolo.mem_compl_fwdHull_iff hT0).2 ⟨hLH hqL, T', by rw [hT]; linarith, u, hu⟩
  have h1 : ∀ᶠ n in atTop, p (φ n) ∈ H \ fwdHull A T :=
    hlim.eventually ((FwdHolo.isOpen_compl_fwdHull hA hT0).mem_nhds hqT)
  have htlim : Tendsto t atTop (𝓝 (sInf S)) := by
    have hup : Tendsto (fun n : ℕ => sInf S + 1 / ((n : ℝ) + 1)) atTop (𝓝 (sInf S)) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (sInf S)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => csInf_le hSbdd (ht n)) (fun n => (hts n).le)
  have h2 : ∀ᶠ n in atTop, t (φ n) < T :=
    (htlim.comp hφ.tendsto_atTop).eventually (eventually_lt_nhds (by rw [hT]; linarith))
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact hn1.2 (fwdHull_subset_of_le hn2.le (hp (φ n)).1)

/-- **A fresh point is at the tip.** If `p` is swallowed exactly at time `s > 0`, then every point of `ℍ \ K_s`
close to `p` has centred image `f_s` close to `0`. -/
theorem exists_forall_norm_fwdMap_lt_of_fresh (hA : Continuous A) {s : ℝ} (hs : 0 < s) {p : ℂ}
    (hp : p ∈ fwdHull A s) (hnot : ∀ t ∈ Ico (0 : ℝ) s, p ∉ fwdHull A t) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > (0 : ℝ), ∀ z ∈ H \ fwdHull A s, ‖z - p‖ < ρ → ‖fwdMap A s z‖ < ε := by
  have hlim := CoreArc.tendsto_fwdMap_nhdsLT_of_mem hA hs hp hnot
  have hev1 : ∀ᶠ t in 𝓝[<] s, ‖fwdMap A t p‖ < ε / 4 := by
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < ε / 4))]
      with t ht
    rwa [dist_zero_right] at ht
  obtain ⟨δ, hδ, hAδ⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := s)) (ε / 200) (by positivity)
  set η := min (min δ s) ((ε / 64) ^ 2) with hη
  have hη0 : 0 < η := by positivity
  have hηδ : η ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hηs : η ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hηe : η ≤ (ε / 64) ^ 2 := min_le_right _ _
  obtain ⟨t, ht1, ht2⟩ := (hev1.and (Ioo_mem_nhdsLT (show s - η < s by linarith))).exists
  have ht0 : 0 ≤ t := by linarith [ht2.1]
  have hpK : p ∈ H \ fwdHull A t := ⟨hp.1, hnot t ⟨ht0, ht2.2⟩⟩
  have hcont : ContinuousAt (fwdMap A t) p :=
    (E6.continuousOn_fwdMap_compl hA ht0).continuousAt ((FwdHolo.isOpen_compl_fwdHull hA ht0).mem_nhds hpK)
  obtain ⟨ρ, hρ, hρc⟩ := Metric.continuousAt_iff.1 hcont (ε / 4) (by positivity)
  refine ⟨ρ, hρ, fun z hz hzp => ?_⟩
  set h := s - t with hh
  have hh0 : 0 < h := by rw [hh]; linarith [ht2.2]
  have hhη : h < η := by rw [hh]; linarith [ht2.1]
  have hts : t + h = s := by rw [hh]; ring
  have hzKt : z ∈ H \ fwdHull A t := ⟨hz.1, fun h' => hz.2 (fwdHull_subset_of_le (by linarith) h')⟩
  obtain ⟨-, T', hT', u, hu⟩ := (FwdHolo.mem_compl_fwdHull_iff hs.le).1 hz
  have hsol : ∃ v, IsForwardSol A z (t + h) v := ⟨u, by rw [hts]; exact isForwardSol_restrict hu hs.le hT'.le⟩
  have hflow := fwdMap_add hA hz.1 ht0 hh0.le hsol
  rw [hts] at hflow
  set At : ℝ → ℝ := fun r => A (t + r) - A t with hAt
  have hAtc : Continuous At := by rw [hAt]; fun_prop
  have hAt0 : At 0 = 0 := by simp [hAt]
  have hζ : fwdMap A t z ∈ H \ fwdHull At h := by
    refine ⟨Ito.im_fwdMap_pos hA ht0 hzKt ⟨ht0, le_rfl⟩, fun hζK => hz.2 ?_⟩
    have hmem : z ∈ fwdHull A (t + h) \ fwdHull A t := by
      rw [fwdHull_add_diff hA ht0 hh0.le]
      exact ⟨hzKt, hζK⟩
    rw [hts] at hmem
    exact hmem.1
  have hM : ∀ r ∈ Icc (0 : ℝ) h, |At r| ≤ ε / 100 := by
    intro r hr
    have h1 := hAδ (x := t + r) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2])
    have h2 := hAδ (x := t) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq] at h1 h2
    calc |At r| = |(A (t + r) - A s) - (A t - A s)| := by rw [hAt]; ring_nf
      _ ≤ |A (t + r) - A s| + |A t - A s| := abs_sub _ _
      _ ≤ ε / 100 := by linarith
  have hdisp := CoreArc.norm_fwdMap_sub_le_uniform hAtc hAt0 hh0 hM hζ
  have hsq : Real.sqrt h < ε / 64 := (Real.sqrt_lt' (by positivity)).2 (by linarith)
  have hzc : ‖fwdMap A t z - fwdMap A t p‖ < ε / 4 := by
    have := hρc (x := z) (by rwa [dist_eq_norm])
    rwa [dist_eq_norm] at this
  rw [hflow]
  calc ‖fwdMap At h (fwdMap A t z)‖
      = ‖(fwdMap At h (fwdMap A t z) - fwdMap A t z) + (fwdMap A t z - fwdMap A t p) + fwdMap A t p‖ := by
        ring_nf
    _ ≤ ‖fwdMap At h (fwdMap A t z) - fwdMap A t z‖ + ‖fwdMap A t z - fwdMap A t p‖ + ‖fwdMap A t p‖ :=
        norm_add₃_le
    _ < ε := by linarith

end Hull

/-! ### The contradiction at the first hit -/

/-- **The tip at the first hit is not separated** (L558–L560: "there is an exterior path from its tip to infinity
avoiding `J` and the stopped large hull"). Let `U ⊆ ℍ` be open, preconnected, unbounded and disjoint from `J`, and
let the hulls stay off `U` strictly before the first hit `s` of a set `L ⊆ closure U`. Then the hull at `s` still
misses `U` (`fwdHull_subset_of_forall_lt`), a point `p ∈ K_s ∩ L` is swallowed exactly at `s`, and the points of `U`
near `p` are at the tip (`exists_forall_norm_fwdMap_lt_of_fresh`) and reach `∞` inside `U`. -/
theorem not_tipSeparated_of_isFirstHit {A : ℝ → ℝ} (hA : Continuous A) (hA0 : A 0 = 0) {L U J : Set ℂ} {s : ℝ}
    (hs : IsFirstHit A L s) (hLU : L ⊆ closure U) (hUH : U ⊆ H) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUb : ¬ IsBounded U) (hUJ : Disjoint U J)
    (hKU : ∀ t, 0 ≤ t → t < s → Disjoint (fwdHull A t) U) : ¬ TipSeparated A s J := by
  rintro ⟨ε, hε, hsep⟩
  obtain ⟨hs0, ⟨p, hpK, hpL⟩, hbefore⟩ := hs
  have hHU : H \ (H \ U) = U := Set.sdiff_sdiff_cancel_left hUH
  have hKs : fwdHull A s ⊆ H \ U :=
    ZhanGT4.fwdHull_subset_of_forall_lt hA hA0 hs0 (by rwa [hHU]) (by rwa [hHU]) (by rwa [hHU])
      fun t ht0 hts z hz => ⟨hz.1, fun hzU => Set.disjoint_left.1 (hKU t ht0 hts) hz hzU⟩
  have hspos : 0 < s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h, RS.fwdHull_zero_eq_empty hA] at hpK
      exact absurd hpK (notMem_empty p)
    · exact h
  have hnot : ∀ t ∈ Ico (0 : ℝ) s, p ∉ fwdHull A t := fun t ht hpt =>
    (Set.eq_empty_iff_forall_notMem.1 (hbefore t ht.1 ht.2)) p ⟨hpt, hpL⟩
  obtain ⟨ρ, hρ, hest⟩ := exists_forall_norm_fwdMap_lt_of_fresh hA hspos hpK hnot hε
  obtain ⟨z, hzU, hzp⟩ := Metric.mem_closure_iff.1 (hLU hpL) ρ hρ
  have hzH : z ∈ H \ fwdHull A s := ⟨hUH hzU, fun h => (hKs h).2 hzU⟩
  refine hsep z hzH (hest z hzH (by rwa [dist_comm, dist_eq_norm] at hzp)) ?_
  refine Set.mem_sUnion.2 ⟨U, ⟨hUc, fun w hw => ⟨hUH hw, fun hw' => ?_⟩, hUb⟩, hzU⟩
  rcases hw' with h | h
  · exact (hKs h).2 hw
  · exact Set.disjoint_left.1 hUJ hw h

/-! ### The countable argument for one sample -/

/-- **A.2, part 2, for one sample** (L537–L561). Let `w` be a driver continuous on `[0, ζ)` with `w 0 = 0`, `v` a
mark, `γ` a crosscut with unbounded side `D`. If at the first hit of every good rational chain inside the strip life
of `(w, v)` the tip is separated from `∞` by `J = γ((0, 1))`, then the closure of the hulls over the strip life misses
`D`. -/
theorem disjoint_lifeHullClosure_of_tipSeparated {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {γ : ℝ → ℂ} {D : Set ℂ}
    (hD : IsCrosscutDomain D γ)
    (hsep : ∀ F : Finset (ℚ × ℚ × ℚ), IsGoodChain H F → ∀ s : ℝ≥0,
      IsFirstHit (Strip.extPath w) (chainClosed F) s → Strip.IsStripLife w v ζ s →
        TipSeparated (Strip.extPath w) s (γ '' Ioo 0 1)) :
    Disjoint (A2X.lifeHullClosure w v ζ) D := by
  rw [Set.disjoint_left]
  intro z hzS hzD
  obtain ⟨z', hz'D, hz'U⟩ := mem_closure_iff.1 hzS D hD.isOpen hzD
  simp only [mem_iUnion] at hz'U
  obtain ⟨t₀, hlife, hz'K⟩ := hz'U
  obtain ⟨t', ht₀t', ht'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlife.1
  have ht₀t'R : (t₀ : ℝ) < t' := by exact_mod_cast ht₀t'
  -- a globally continuous driver agreeing with `w` on `[0, t']`
  set A : ℝ → ℝ := Ito.clampDrv (Strip.extPath w) t' with hAdef
  have hAc : Continuous A := Ito.continuous_clampDrv t'.coe_nonneg (Strip.continuousOn_extPath hw ht'ζ)
  have hA0 : A 0 = 0 := by
    show Strip.extPath w (min (max 0 0) t') = 0
    rw [max_self, min_eq_left t'.coe_nonneg]
    simp [Strip.extPath, hw0]
  have hAeq : EqOn A (Strip.extPath w) (Icc 0 t') := Ito.clampDrv_eqOn
  have hK : ∀ t : ℝ, 0 ≤ t → t < t' → fwdHull A t = fwdHull (Strip.extPath w) t := fun t ht htt' =>
    LocalExt.fwdHull_congr_of_eqOn_of_lt ht htt' hAeq
  have hF : ∀ t : ℝ, t ≤ t' → ∀ z, fwdMap A t z = fwdMap (Strip.extPath w) t z := fun t htt' z =>
    Ito.fwdMap_congr_of_eqOn_of_le hAeq htt'
  have hz'K' : z' ∈ fwdHull A t₀ := by rw [hK t₀ t₀.coe_nonneg ht₀t'R]; exact hz'K
  -- a far radius beyond the hull at `t₀` and beyond `D`'s far radius
  obtain ⟨R₀, hR₀⟩ := (isBounded_fwdHull hAc (t₀ : ℝ)).subset_ball (0 : ℂ)
  obtain ⟨RD, hRD⟩ := hD.far
  set R : ℝ := max (max R₀ RD) 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  have hfarD : farH R ⊆ D := fun z hz =>
    hRD z hz.1 (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hz.2)
  have hKfar : ∀ t : ℝ, t ≤ t₀ → Disjoint (fwdHull A t) (farH R) := fun t htt₀ =>
    Set.disjoint_left.2 fun z hzK hzf => by
      have h1 := hR₀ (fwdHull_subset_of_le htt₀ hzK)
      rw [mem_ball_zero_iff] at h1
      have h2 := (le_max_left R₀ RD).trans (le_max_left _ (0 : ℝ))
      linarith [hzf.2]
  -- the rational chain from `z'` to the far region
  obtain ⟨F, hFD, hFc, hz'F⟩ := exists_chain hD.isOpen hD.isPreconnected hR0 hfarD hz'D
  have hz'L : z' ∈ chainClosed F := by
    rcases hz'F with h | h
    · exact chainOpen_subset_chainClosed F h
    · exact absurd h (Set.disjoint_left.1 (hKfar t₀ le_rfl) hz'K')
  obtain ⟨s, hs, hst₀⟩ := exists_isFirstHit hAc (isCompact_chainClosed F)
    (hFD.chainClosed_subset.trans hD.subset_H) t₀.coe_nonneg ⟨z', hz'K', hz'L⟩
  have hst' : s < t' := lt_of_le_of_lt hst₀ ht₀t'R
  set s' : ℝ≥0 := ⟨s, hs.1⟩ with hs'
  have hlife' : Strip.IsStripLife w v ζ s' := hlife.mono (show s' ≤ t₀ from hst₀)
  have hsfirst : IsFirstHit (Strip.extPath w) (chainClosed F) s := by
    obtain ⟨h0, hne, hb⟩ := hs
    refine ⟨h0, by rwa [← hK s h0 hst'], fun t ht hts => ?_⟩
    rw [← hK t ht (by linarith)]
    exact hb t ht hts
  have hTS := hsep F (hFD.mono hD.subset_H) s' hsfirst hlife'
  have hTSA : TipSeparated A s (γ '' Ioo 0 1) := by
    obtain ⟨ε, hε, h⟩ := hTS
    have h' : ∀ z ∈ H \ fwdHull (Strip.extPath w) s, ‖fwdMap (Strip.extPath w) s z‖ < ε →
        z ∉ unbddPart (fwdHull (Strip.extPath w) s ∪ γ '' Ioo 0 1) := h
    refine ⟨ε, hε, fun z hz hzε => ?_⟩
    have hKs : fwdHull A s = fwdHull (Strip.extPath w) s := hK s hs.1 hst'
    rw [hKs] at hz ⊢
    exact h' z hz (by rwa [← hF s hst'.le z])
  have hUD : chainOpen F ∪ farH R ⊆ D := union_subset
    (fun z hz => hFD.chainClosed_subset (chainOpen_subset_chainClosed F hz)) hfarD
  refine not_tipSeparated_of_isFirstHit hAc hA0 hs
    (hFD.chainClosed_subset_closure.trans (closure_mono subset_union_left)) (hUD.trans hD.subset_H)
    ((isOpen_chainOpen F).union (isOpen_farH R)) hFc
    (fun hb => not_isBounded_farH R (hb.subset subset_union_right))
    (Set.disjoint_left.2 fun z hz hzJ => Set.disjoint_left.1 hD.disjoint_crosscut (hUD hz) hzJ)
    (fun t ht hts => ?_) hTSA
  refine Set.disjoint_left.2 fun z hzK hzU => ?_
  rcases hzU with h | h
  · exact (Set.eq_empty_iff_forall_notMem.1 (hs.2.2 t ht hts)) z ⟨hzK, chainOpen_subset_chainClosed F h⟩
  · exact Set.disjoint_left.1 (hKfar t (by linarith)) hzK h

/-! ### The pull-back of the image crosscut -/

/-- **The pull-back** (L551–L553: "its crosscut separates the large tip from infinity"). If the centred image
`f_s(J₀ \ K_s)` of a part `J₀` of `J` contains the open part of a simple real crosscut `γ'` from a negative to a
positive real point, then the tip at time `s` is separated from `∞` by `J`: a relative half-disc of `0` lies inside
`γ'`, and the `f_s`-image of a connected unbounded subset of `ℍ \ (K_s ∪ J)` is connected, unbounded and misses
`γ'((0, 1))` (`f_s` is injective), so it lies on the unbounded side of `γ'`. -/
theorem tipSeparated_of_image {A : ℝ → ℝ} (hA : Continuous A) (hA0 : A 0 = 0) {s : ℝ} (hs : 0 < s)
    {J₀ J : Set ℂ} (hJ₀J : J₀ ⊆ J) {γ' : ℝ → ℂ} (hγ' : IsRealCrosscut γ') (ha : (γ' 0).re < 0)
    (hb : 0 < (γ' 1).re) (himg : γ' '' Ioo 0 1 ⊆ fwdMap A s '' (J₀ ∩ (H \ fwdHull A s))) :
    TipSeparated A s J := by
  obtain ⟨D', hD'⟩ := exists_isCrosscutDomain hγ' (by linarith)
  obtain ⟨V, hVo, -, hVH, hVD, -, hVfr, -⟩ := hD'.exists_inside
  obtain ⟨δ, hδ, hball⟩ := hD'.exists_ball_inter_H_subset_inside hVo hVH hVfr (x := 0) ⟨ha, hb⟩
  refine ⟨δ, hδ, fun z hz hzδ hzU => ?_⟩
  obtain ⟨C, ⟨hCc, hCsub, hCb⟩, hzC⟩ := Set.mem_sUnion.1 hzU
  have hCK : C ⊆ H \ fwdHull A s := fun c hc => ⟨(hCsub hc).1, fun h => (hCsub hc).2 (Or.inl h)⟩
  have hC'c : IsPreconnected (fwdMap A s '' C) :=
    hCc.image _ ((E6.continuousOn_fwdMap_compl hA hs.le).mono hCK)
  have hC'H : fwdMap A s '' C ⊆ H := by
    rintro _ ⟨c, hc, rfl⟩
    exact Ito.im_fwdMap_pos hA hs.le (hCK hc) ⟨hs.le, le_rfl⟩
  have hC'γ : Disjoint (fwdMap A s '' C) (γ' '' Ioo 0 1) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨c, hc, rfl⟩ hcγ
    obtain ⟨j, ⟨hjJ₀, hjK⟩, hj⟩ := himg hcγ
    have hjc : j = c := FwdHolo.injOn_fwdMap hA hs.le hjK (hCK hc) hj
    exact (hCsub hc).2 (Or.inr (hjc ▸ hJ₀J hjJ₀))
  have hC'b : ¬ IsBounded (fwdMap A s '' C) := by
    intro hbd
    obtain ⟨M, hM⟩ := ZhanGT4.exists_abs_le_of_continuous hA s
    obtain ⟨R, hR⟩ := hbd.subset_ball (0 : ℂ)
    refine hCb ((isBounded_ball (x := (0 : ℂ)) (r := R + (24 * M + 8 * Real.sqrt s))).subset fun c hc => ?_)
    have h1 := CoreArc.norm_fwdMap_sub_le_uniform hA hA0 hs hM (hCK hc)
    have h2 := hR (mem_image_of_mem _ hc)
    rw [mem_ball_zero_iff] at h2 ⊢
    have h3 : ‖c‖ ≤ ‖fwdMap A s c‖ + ‖fwdMap A s c - c‖ := by
      calc ‖c‖ = ‖fwdMap A s c - (fwdMap A s c - c)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖fwdMap A s c‖ + ‖fwdMap A s c - c‖ := norm_sub_le _ _
    linarith
  have hC'D : fwdMap A s '' C ⊆ D' := by
    obtain ⟨R, -, hR⟩ := hD'.exists_far_mem
    obtain ⟨c', hc'C', hc'R⟩ : ∃ c' ∈ fwdMap A s '' C, R < ‖c'‖ := by
      by_contra hcon
      push Not at hcon
      exact hC'b ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun c hc => by
        rw [mem_closedBall_zero_iff]; exact hcon c hc)
    exact hD'.subset_of_isPreconnected hC'c hC'H hC'γ ⟨c', hc'C', hR c' (hC'H hc'C') hc'R⟩
  have hzV : fwdMap A s z ∈ V := hball ⟨by rw [Complex.ofReal_zero, mem_ball_zero_iff]; exact hzδ,
    Ito.im_fwdMap_pos hA hs.le hz ⟨hs.le, le_rfl⟩⟩
  exact Set.disjoint_left.1 hVD hzV (hC'D (mem_image_of_mem _ hzC))

/-- **The pull-back for a driver continuous only on `[0, t']`**, `0 < s < t'` (for instance `W = extPath w` of a
driver continuous before its lifetime): `tipSeparated_of_image` through the clamped driver `Ito.clampDrv W t'`, whose
hull and centred map at time `s` are those of `W`. -/
theorem tipSeparated_of_image_of_continuousOn {W : ℝ → ℝ} {t' : ℝ} (hW : ContinuousOn W (Icc 0 t'))
    (hW0 : W 0 = 0) {s : ℝ} (hs : 0 < s) (hst' : s < t') {J₀ J : Set ℂ} (hJ₀J : J₀ ⊆ J) {γ' : ℝ → ℂ}
    (hγ' : IsRealCrosscut γ') (ha : (γ' 0).re < 0) (hb : 0 < (γ' 1).re)
    (himg : γ' '' Ioo 0 1 ⊆ fwdMap W s '' (J₀ ∩ (H \ fwdHull W s))) : TipSeparated W s J := by
  have ht'0 : 0 ≤ t' := by linarith
  have hAc : Continuous (Ito.clampDrv W t') := Ito.continuous_clampDrv ht'0 hW
  have hAeq : EqOn (Ito.clampDrv W t') W (Icc 0 t') := Ito.clampDrv_eqOn
  have hA0 : Ito.clampDrv W t' 0 = 0 := by rw [hAeq ⟨le_rfl, ht'0⟩, hW0]
  have hK : fwdHull (Ito.clampDrv W t') s = fwdHull W s := LocalExt.fwdHull_congr_of_eqOn_of_lt hs.le hst' hAeq
  have hF : ∀ z, fwdMap (Ito.clampDrv W t') s z = fwdMap W s z := fun z =>
    Ito.fwdMap_congr_of_eqOn_of_le hAeq hst'.le
  have himg' : γ' '' Ioo 0 1 ⊆ fwdMap (Ito.clampDrv W t') s '' (J₀ ∩ (H \ fwdHull (Ito.clampDrv W t') s)) := by
    rw [hK]
    intro z hz
    obtain ⟨j, hj, rfl⟩ := himg hz
    exact ⟨j, hj, hF j⟩
  obtain ⟨ε, hε, h⟩ := tipSeparated_of_image hAc hA0 hs hJ₀J hγ' ha hb himg'
  refine ⟨ε, hε, fun z hz hzε => ?_⟩
  rw [← hK] at hz ⊢
  exact h z hz (by rwa [hF z])

end InteractingSLE.ZhanGT4.A2Part2
