/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma77Sep
import InteractingSLE.Spec.Supplement.G7RestartPath
import InteractingSLE.WangWu.ChamberJordan
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# Lemma 7.6: a forbidden first exit is a chart visit beyond the first tip

Packet PROVE-LEMMA76D, part (b). Specification §7.2, proof of Lemma 7.6 (p. 270): "At a continuous first physical
exit, the first-exit prime-end lemma supplies its endpoint in the half-plane chart. Every exit through the indicated
right side is therefore excluded."

Setting: disjoint prefixes `α([0, a])`, `β([0, b])`, the joint unbounded domain `D = ℍ \ fill(α([0, a]) ∪ β([0, b]))`,
a chart `(φ, ψ)` of `D` with `ψ(0) = β(b)` (G7's `IsRetCont`), and the continuation of `β` read in the chart up to and
including its first new contact (`IsRetainedClock`). A forbidden exit (`IsForbiddenExit … v = a`): `β((b, e)) ⊆ D`,
`β(e) = α(u)` with `u < a`, and the first tip `α(a)` inside the Jordan curve `α([0, u]) ∪ β([0, e]) ∪ L`.

**Main result** (`exists_chartVisit_of_isForbiddenExit`): if moreover the first tip is accessible (`α(a) ∈ closure D`),
the chart path reaches a real point `y` with `ψ(y) = α(u)`, and some real `w` strictly between `0` and `y` has
`ψ(w) = α(a)`: in the chart, the first tip lies between the second tip and the exit point. This is the
deterministic content of "the exit is through the right side of the first prefix"; the heights on that side are a
property of the conditional law (`Lemma76Kernel2`).

**Proof.** The chart path up to the exit is a crosscut `F` of `ℍ` from `0` to `y` (its interior points lie in `ℍ`
because the physical continuation lies in `D`). The unbounded domain `E` of `F` is mapped by `ψ` to a preconnected
unbounded set missing the Jordan curve, hence outside it. Points of `D` near `α(a)` lie inside the curve, so their
chart preimages lie in the bounded part `fill(F)`; by compactness `α(a) = ψ(w)` for some `w ∈ closure (fill F)`,
necessarily real. Real points outside `[0, y]` lie on unbounded rays missing `F`, so `F` is free there and they are
not in `closure (fill F)`; `w ≠ 0, y` because `α(a) ≠ β(b), α(u)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Sec7

namespace Lemma76Exit

/-! ### Elementary facts -/

/-- The points inside a closed set (bounded components of its complement) form an open set. -/
theorem isOpen_jordanIn_of_isClosed {J : Set ℂ} (hJ : IsClosed J) : IsOpen (WangWu.jordanIn J) := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  refine ⟨connectedComponentIn Jᶜ z, fun w hw => ⟨connectedComponentIn_subset _ _ hw, ?_⟩,
    hJ.isOpen_compl.connectedComponentIn, mem_connectedComponentIn hz.1⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

/-- For a closed set, the unbounded part of `ℍ \ K` is the unbounded domain `ℍ \ fill K`. -/
theorem unboundedPart_eq {K : Set ℂ} (hK : IsClosed K) : unboundedPart (H \ K) = H \ fillH K := by
  ext z
  rw [HalfPlaneSep.mem_H_diff_fillH_of_isClosed hK]
  exact Iff.rfl

theorem isClosed_Hbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im

theorem H_subset_Hbar : H ⊆ Hbar := fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz

/-- A point of `ℍ̄` off `ℍ` is real. -/
theorem eq_ofReal_re_of_mem_Hbar {z : ℂ} (hz : z ∈ Hbar) (hzH : z ∉ H) : z = (z.re : ℂ) := by
  have him : z.im = 0 := le_antisymm (not_lt.1 hzH) hz
  exact Complex.ext (by simp) (by simp [him])

/-- A real point on an unbounded ray missing a compact set `F ⊆ ℍ̄` is not adherent to the bounded part
`fill F`. -/
theorem notMem_closure_fillH_of_ray {F X : Set ℂ} (hF : IsCompact F) (hX : IsPreconnected X)
    (hXu : ¬ IsBounded X) (hXF : X ⊆ {w | 0 ≤ w.im} \ F) {z : ℂ} (hz : z ∈ X) :
    z ∉ closure (fillH F) := by
  intro hzc
  obtain ⟨ε, hε, hball⟩ :=
    HalfPlaneSep.isFreeAt_of_not_isBounded hF.isClosed hF.isBounded hX hXu hXF z hz
  obtain ⟨s, hs, hsz⟩ := Metric.mem_closure_iff.1 hzc ε hε
  have hsH : s ∈ H := fillH_subset_H F hs
  have hsb : s ∈ ball z ε := by rw [mem_ball, dist_comm]; exact hsz
  exact (hball ⟨hsb, hsH⟩).2 hs

theorem not_isBounded_ofReal_Iio (m : ℝ) : ¬ IsBounded (((↑) : ℝ → ℂ) '' Iio m) := by
  intro hb
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 hb
  have ht : min m (-|R|) - 1 ∈ Iio m := by
    simp only [mem_Iio]; linarith [min_le_left m (-|R|)]
  have h := hR ⟨_, ht, rfl⟩
  rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h
  have h1 : min m (-|R|) - 1 < -|R| := by linarith [min_le_right m (-|R|)]
  rw [abs_of_neg (by linarith [abs_nonneg R])] at h
  linarith [le_abs_self R]

theorem not_isBounded_ofReal_Ioi (m : ℝ) : ¬ IsBounded (((↑) : ℝ → ℂ) '' Ioi m) := by
  intro hb
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall 0).1 hb
  have ht : max m |R| + 1 ∈ Ioi m := by
    simp only [mem_Ioi]; linarith [le_max_left m |R|]
  have h := hR ⟨_, ht, rfl⟩
  rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h
  have h1 : |R| < max m |R| + 1 := by linarith [le_max_right m |R|]
  rw [abs_of_pos (by linarith [abs_nonneg R])] at h
  linarith [le_abs_self R]

/-! ### The chart visit -/

section Visit

variable {α β Γ : ℝ≥0 → ℂ} {a b e u : ℝ≥0} {ζ U : ℝ≥0∞} {x : ℝ} {φ ψ : ℂ → ℂ} {L : Set ℂ}

/-- **A forbidden first exit is a chart visit beyond the first tip** (first-exit prime-end lemma, p. 270). In the
retained chart of the disjoint prefixes `α([0, a])`, `β([0, b])` at the second tip, let the continuation of `β` be
read in the chart path `Γ` up to and including its first new contact (`IsRetainedClock`), and let `β` exit the joint
unbounded domain at `β(e) = α(u)`, `u < a`, with the accessible first tip `α(a)` inside the Jordan curve
`α([0, u]) ∪ β([0, e]) ∪ L` (`L` closed, below `ℝ`). Then the chart path reaches a real point `y` with
`ψ(y) = α(u)`, and some real `w` strictly between `0` and `y` has `ψ(w) = α(a)`. -/
theorem exists_chartVisit_of_isForbiddenExit
    (hR : Supp7.IsRetCont β ζ x b (α '' Icc 0 a) φ ψ)
    (hclk : Supp7.IsRetainedClock β ζ b (α '' Icc 0 a ∪ β '' Icc 0 b) ψ Γ U)
    (hΓc : ContinuousOn Γ {s | (s : ℝ≥0∞) ≤ U})
    (hαc : ContinuousOn α (Icc 0 a)) (hαi : InjOn α (Icc 0 a))
    (hLc : IsClosed L) (hLH : Disjoint L H)
    (hex : IsForbiddenExit α a β b e u a L) (he : (e : ℝ≥0∞) ≤ ζ)
    (hcl : α a ∈ closure (H \ fillH (α '' Icc 0 a ∪ β '' Icc 0 b))) :
    ∃ s : ℝ≥0, (s : ℝ≥0∞) ≤ U ∧ ∃ y : ℝ, Γ s = y ∧ ψ y = α u ∧
      ∃ w : ℝ, ψ w = α a ∧ (0 < w ∧ w < y ∨ y < w ∧ w < 0) := by
  set K := α '' Icc 0 a ∪ β '' Icc 0 b with hKdef
  have hK : IsClosed K := hR.isClosed_K
  have hch := hR.chart
  obtain ⟨hbe, hua, -, hpath, hβe, hjord⟩ := hex
  rw [unboundedPart_eq hK] at hpath
  obtain ⟨c, σ, hσU, hmono, himg, hrel, hHb⟩ := hclk
  have hDK : ∀ z ∈ H \ fillH K, z ∉ K := fun z hz => (HalfPlaneSep.H_diff_fillH_subset_H_diff hK hz).2
  have hαK : ∀ s ≤ a, α s ∈ K := fun s hs => Or.inl ⟨s, ⟨zero_le, hs⟩, rfl⟩
  have hβK : ∀ t ≤ b, β t ∈ K := fun t ht => Or.inr ⟨t, ⟨zero_le, ht⟩, rfl⟩
  -- times in `[b, e]` are clock times
  have hmemI : ∀ t : ℝ≥0, b ≤ t → t ≤ e → t ∈ c '' {s | (s : ℝ≥0∞) ≤ σ} := by
    intro t hbt hte
    rw [himg]
    exact ⟨hbt, (ENNReal.coe_le_coe.2 hte).trans he,
      fun t' h1 h2 => hDK _ (hpath t' ⟨h1, h2.trans_le hte⟩)⟩
  have hσ0 : (0 : ℝ≥0) ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ σ} := by simp
  have hc0 : c 0 = b := by
    obtain ⟨s₀, hs₀, hcs₀⟩ := hmemI b le_rfl hbe.le
    have h1 : b ≤ c 0 := by
      have h := mem_image_of_mem c hσ0
      rw [himg] at h
      exact h.1
    have h2 : c 0 ≤ c s₀ := hmono.monotoneOn hσ0 hs₀ zero_le
    exact le_antisymm (hcs₀ ▸ h2) h1
  obtain ⟨s_e, hs_e, hcs_e⟩ := hmemI e hbe.le le_rfl
  have hs_eσ : (s_e : ℝ≥0∞) ≤ σ := hs_e
  have hs_eU : (s_e : ℝ≥0∞) ≤ U := hs_eσ.trans hσU
  have hΓ0 : Γ 0 = 0 := by
    have h := hrel 0 hσ0
    rw [hc0] at h
    exact hR.tipUniq _ (hHb 0 hσ0) h.symm
  -- interior clock times are interior chart points
  have hint : ∀ s : ℝ≥0, 0 < s → s < s_e → Γ s ∈ H := by
    intro s hs0 hse
    have hsσ : (s : ℝ≥0∞) ≤ σ := (ENNReal.coe_le_coe.2 hse.le).trans hs_eσ
    have h1 : b < c s := hc0 ▸ hmono hσ0 hsσ hs0
    have h2 : c s < e := hcs_e ▸ hmono hsσ hs_e hse
    have hD : β (c s) ∈ H \ fillH K := hpath (c s) ⟨h1, h2⟩
    by_contra hn
    exact hch.inv_notMem _ hn (by rw [← hrel s hsσ]; exact hD)
  -- every time in `(b, e)` is an interior clock time
  have hinv : ∀ t ∈ Ioo b e, ∃ s : ℝ≥0, 0 < s ∧ s < s_e ∧ (s : ℝ≥0∞) ≤ σ ∧ c s = t := by
    intro t ht
    obtain ⟨s, hs, hcs⟩ := hmemI t ht.1.le ht.2.le
    refine ⟨s, ?_, ?_, hs, hcs⟩
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
      · rw [← h, hc0] at hcs
        exact absurd hcs ht.1.ne
      · exact h
    · by_contra hn
      have h := hmono.monotoneOn hs_e hs (not_lt.1 hn)
      rw [hcs_e, hcs] at h
      exact absurd ht.2 (not_lt.2 h)
  -- the exit point in the chart
  have hψe : ψ (Γ s_e) = α u := by rw [← hrel s_e hs_e, hcs_e, hβe]
  have hΓe : Γ s_e ∉ H := by
    intro hH
    exact hDK _ (hch.bijOn_inv.mapsTo hH) (by rw [hψe]; exact hαK u hua.le)
  have hΓy : Γ s_e = ((Γ s_e).re : ℂ) := eq_ofReal_re_of_mem_Hbar (hHb s_e hs_e) hΓe
  set y : ℝ := (Γ s_e).re with hy
  -- the crosscut
  set F : Set ℂ := Γ '' Icc 0 s_e with hFdef
  have hIcc : Icc 0 s_e ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ U} := fun s hs =>
    (ENNReal.coe_le_coe.2 hs.2).trans hs_eU
  have hFc : IsCompact F := isCompact_Icc.image_of_continuousOn (hΓc.mono hIcc)
  have hFreal : ∀ z ∈ F, z.im = 0 → z = 0 ∨ z = (y : ℂ) := by
    rintro _ ⟨s, hs, rfl⟩ him
    rcases eq_or_lt_of_le hs.1 with h | h
    · left; rw [← h, hΓ0]
    rcases eq_or_lt_of_le hs.2 with h' | h'
    · right; rw [h', ← hΓy]
    · exact absurd him (ne_of_gt (show (0 : ℝ) < (Γ s).im from hint s h h'))
  -- the unbounded domain of the crosscut
  set E := H \ fillH F with hEdef
  have hEpc : IsPreconnected E := HalfPlaneSep.isPreconnected_H_diff_fillH hFc.isClosed hFc.isBounded
  have hEub : ¬ IsBounded E := HalfPlaneSep.not_isBounded_H_diff_fillH hFc.isClosed hFc.isBounded
  have hEF : ∀ w ∈ E, w ∉ F := fun w hw => (HalfPlaneSep.H_diff_fillH_subset_H_diff hFc.isClosed hw).2
  -- the Jordan curve
  set J := α '' Icc 0 u ∪ β '' Icc 0 e ∪ L with hJdef
  have hJc : IsClosed J :=
    ((isCompact_Icc.image_of_continuousOn (hαc.mono (Icc_subset_Icc_right hua.le))).isClosed.union
      (IsPathGood.isCompact_image_Icc hR.path he).isClosed).union hLc
  -- `ψ` maps the unbounded domain of the crosscut outside the curve
  obtain ⟨M, hM⟩ := hch.bdd
  have hEout : ψ '' E ⊆ WangWu.jordanOut J := by
    refine WangWu.subset_jordanOut_of_isPreconnected
      (hEpc.image ψ (hch.differentiableOn_inv.continuousOn.mono sdiff_subset))
      (not_isBounded_image_of_norm_sub_le hEub fun w hw => hM w (H_subset_Hbar hw.1)) ?_
    rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hJ
    have hwD : ψ w ∈ H \ fillH K := hch.bijOn_inv.mapsTo hw.1
    have hwK := hDK _ hwD
    rcases hJ with (hJ | hJ) | hJ
    · obtain ⟨s, hs, hse⟩ := hJ
      exact hwK (by rw [← hse]; exact hαK s (hs.2.trans hua.le))
    · obtain ⟨t, ht, hte⟩ := hJ
      rcases le_or_gt t b with htb | htb
      · exact hwK (by rw [← hte]; exact hβK t htb)
      rcases eq_or_lt_of_le ht.2 with hte' | hte'
      · rw [hte', hβe] at hte
        exact hwK (by rw [← hte]; exact hαK u hua.le)
      obtain ⟨s, hs0, hse, hsσ, hcs⟩ := hinv t ⟨htb, hte'⟩
      have h1 : ψ (Γ s) = ψ w := by rw [← hrel s hsσ, hcs, hte]
      have h2 : Γ s = w := hch.bijOn_inv.injOn (hint s hs0 hse) hw.1 h1
      exact hEF w hw ⟨s, ⟨hs0.le, hse.le⟩, h2⟩
    · exact Set.disjoint_left.1 hLH hJ hwD.1
  -- the bounded part of the crosscut's complement
  have hSb : IsBounded (fillH F) := by
    obtain ⟨R, hR0, hFR⟩ := hFc.isBounded.subset_ball_lt 0 0
    exact isBounded_ball.subset (fillH_subset_ball hR0 (by rw [hFc.isClosed.closure_eq]; exact hFR))
  have hSc : IsCompact (closure (fillH F)) := hSb.isCompact_closure
  have hSH : closure (fillH F) ⊆ Hbar :=
    closure_minimal ((fillH_subset_H F).trans H_subset_Hbar) isClosed_Hbar
  -- `α(a)` is adherent to the image of the bounded part
  have hcl' : α a ∈ closure (ψ '' fillH F) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hN : IsOpen (ball (α a) ε ∩ WangWu.jordanIn J) :=
      isOpen_ball.inter (isOpen_jordanIn_of_isClosed hJc)
    obtain ⟨d, ⟨hdb, hdin⟩, hdD⟩ := mem_closure_iff.1 hcl _ hN ⟨mem_ball_self hε, hjord⟩
    obtain ⟨w, hwH, rfl⟩ := hch.bijOn_inv.surjOn hdD
    have hwS : w ∈ fillH F := by
      by_contra hn
      exact Set.disjoint_left.1 (WangWu.disjoint_jordanIn_jordanOut J) hdin (hEout ⟨w, ⟨hwH, hn⟩, rfl⟩)
    exact ⟨ψ w, ⟨w, hwS, rfl⟩, by rw [dist_comm]; exact hdb⟩
  have hclosed : IsClosed (ψ '' closure (fillH F)) :=
    (hSc.image_of_continuousOn (hch.continuousOn_inv.mono hSH)).isClosed
  obtain ⟨w, hwS, hψw⟩ : α a ∈ ψ '' closure (fillH F) :=
    closure_minimal (image_mono subset_closure) hclosed hcl'
  have hwH : w ∉ H := by
    intro hH
    exact hDK _ (hch.bijOn_inv.mapsTo hH) (by rw [hψw]; exact hαK a le_rfl)
  have hw : w = (w.re : ℂ) := eq_ofReal_re_of_mem_Hbar (hSH hwS) hwH
  set w' := w.re with hw'
  have hw0 : w' ≠ 0 := by
    intro h0
    apply hR.tipO
    refine ⟨a, ⟨zero_le, le_rfl⟩, ?_⟩
    rw [← hψw, hw, h0, Complex.ofReal_zero, hR.tipInv]
  have hwy : w' ≠ y := by
    intro hwy
    have h : α a = α u := by rw [← hψw, hw, hwy, ← hΓy, hψe]
    exact hua.ne' (hαi ⟨zero_le, le_rfl⟩ ⟨zero_le, hua.le⟩ h)
  -- real points outside `[0, y]` lie on rays missing the crosscut
  have hray : ∀ X : Set ℂ, IsPreconnected X → ¬ IsBounded X → (∀ t : ℝ, (t : ℂ) ∈ X → t ≠ 0 ∧ t ≠ y) →
      X ⊆ ((↑) : ℝ → ℂ) '' univ → w ∉ X := by
    intro X hX hXu hXt hXr hwX
    refine notMem_closure_fillH_of_ray hFc hX hXu (fun z hz => ?_) hwX hwS
    obtain ⟨t, -, rfl⟩ := hXr hz
    refine ⟨by simp, fun htF => ?_⟩
    obtain ⟨ht0, hty⟩ := hXt t hz
    rcases hFreal _ htF (by simp) with h | h
    · exact ht0 (by exact_mod_cast h)
    · exact hty (by exact_mod_cast h)
  have hle : min 0 y ≤ w' ∧ w' ≤ max 0 y := by
    constructor
    · by_contra hlt
      push Not at hlt
      refine hray (((↑) : ℝ → ℂ) '' Iio (min 0 y))
        (isPreconnected_Iio.image _ Complex.continuous_ofReal.continuousOn) (not_isBounded_ofReal_Iio _)
        (fun t ht => ?_) (image_mono (subset_univ _)) ⟨w', hlt, hw.symm⟩
      obtain ⟨t', ht', htt'⟩ := ht
      have htt : t' = t := by exact_mod_cast htt'
      rw [htt, mem_Iio] at ht'
      exact ⟨by linarith [min_le_left 0 y], by linarith [min_le_right 0 y]⟩
    · by_contra hlt
      push Not at hlt
      refine hray (((↑) : ℝ → ℂ) '' Ioi (max 0 y))
        (isPreconnected_Ioi.image _ Complex.continuous_ofReal.continuousOn) (not_isBounded_ofReal_Ioi _)
        (fun t ht => ?_) (image_mono (subset_univ _)) ⟨w', hlt, hw.symm⟩
      obtain ⟨t', ht', htt'⟩ := ht
      have htt : t' = t := by exact_mod_cast htt'
      rw [htt, mem_Ioi] at ht'
      exact ⟨by linarith [le_max_left 0 y], by linarith [le_max_right 0 y]⟩
  refine ⟨s_e, hs_eU, y, hΓy, by rw [← hΓy]; exact hψe, w', by rw [← hw]; exact hψw, ?_⟩
  obtain ⟨h1, h2⟩ := hle
  rcases lt_trichotomy 0 y with hy0 | hy0 | hy0
  · left
    rw [min_eq_left hy0.le] at h1
    rw [max_eq_right hy0.le] at h2
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hw0), lt_of_le_of_ne h2 hwy⟩
  · exfalso
    rw [← hy0, min_self] at h1
    rw [← hy0, max_self] at h2
    exact hw0 (le_antisymm h2 h1)
  · right
    rw [min_eq_right hy0.le] at h1
    rw [max_eq_left hy0.le] at h2
    exact ⟨lt_of_le_of_ne h1 (Ne.symm hwy), lt_of_le_of_ne h2 hw0⟩

end Visit

end Lemma76Exit

end Sec7

end InteractingSLE
