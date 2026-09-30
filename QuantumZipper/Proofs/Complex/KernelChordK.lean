import QuantumZipper.Proofs.Complex.KernelChordK1

/-!
# KT2 input K: kernel convergence of the doubled left domains

`leftDoubledKernel : LeftDoubledKernel`. If simple chords `η n → ηi` uniformly on `[0,∞)` in the
chordal metric, the doubled domains `leftDoubled (η n)` converge to `leftDoubled ηi` in the sense
of Carathéodory kernel convergence with respect to `−1` (Pommerenke, *Boundary Behaviour of
Conformal Maps* (1992), §1.4, p. 13):

(i) every point of `leftDoubled ηi` has a neighbourhood lying in `leftDoubled (η n)` for large
`n`: near a negative real point because the chords `η n` eventually miss a fixed disk there;
at a point `w ∈ D₁(ηi)` because a compact set made of a closed disk around `w` and a path in
`D₁(ηi)` from `w` to a point near `−1` has positive distance from `ηi`, hence eventually from
`η n` (`eventually_le_dist_chord`), and so lies in the component `D₁(η n)`; conjugate points by
symmetry;
(ii) every frontier point `w` of the limit domain is a limit of frontier points of
`leftDoubled (η n)`: `w` is a limit chord point `ηi t` (or its conjugate) or a non-negative real,
so it is the limit of points `a n ∉ leftDoubled (η n)` (namely `η n t`, its conjugate, or `w`),
while points of the limit domain near `w` lie in `leftDoubled (η n)` for large `n`; the segment
between them meets the frontier.

Own elementary proof (cost rule of `AGENT_GUIDE.md`); the definition of kernel convergence is
Pommerenke's.
-/

noncomputable section

open Set Metric Filter Topology Complex Function
open QuantumZipper.CA.Uniformizer
open scoped ComplexConjugate

namespace QuantumZipper.CA.Kernel

variable {η : ℕ → ℝ → ℂ} {ηi : ℝ → ℂ}

/-- (i) at a negative real point. -/
theorem eventually_ball_subset_leftDoubled_neg (hηi : IsSimpleChord ηi)
    (hc : SphereUniformConv η ηi) {x : ℝ} (hx : x < 0) :
    ∃ r > 0, ∀ᶠ n in atTop, ball (x : ℂ) r ⊆ leftDoubled (η n) := by
  have hxK : (x : ℂ) ∉ chordSet ηi := fun h => by
    have := eq_zero_of_mem_chordSet_of_im_nonpos hηi h (by simp)
    have : x = 0 := by exact_mod_cast this
    linarith
  have hρ : 0 < infDist (x : ℂ) (chordSet ηi) :=
    ((isClosed_chordSet hηi).notMem_iff_infDist_pos chordSet_nonempty).1 hxK
  set ρ := infDist (x : ℂ) (chordSet ηi)
  refine ⟨min (ρ / 2) (-x), lt_min (by linarith) (by linarith), ?_⟩
  have hev := eventually_le_dist_chord (K := {(x : ℂ)}) hc hρ (norm_nonneg (x : ℂ))
    (fun z hz => by rw [mem_singleton_iff.1 hz]) (fun z hz t ht => by
      rw [mem_singleton_iff.1 hz]; exact infDist_le_dist_of_mem ⟨t, ht, rfl⟩)
  filter_upwards [hev] with n hn
  refine ball_subset_leftDoubled hx (min_le_right _ _) fun t ht hb => ?_
  have h1 := hn x rfl t ht
  rw [mem_ball, dist_comm] at hb
  linarith [min_le_left (ρ / 2) (-x)]

/-- (i) at a point of the left component. -/
theorem eventually_nhds_subset_leftComponent (hη : ∀ n, IsSimpleChord (η n))
    (hηi : IsSimpleChord ηi) (hc : SphereUniformConv η ηi) {w : ℂ}
    (hw : w ∈ leftComponent ηi) :
    ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ leftComponent (η n) := by
  -- a disk around `-1` missing all chords eventually
  have hρ0 := infDist_neg_one_pos hηi
  set ρ₀ := infDist (-1 : ℂ) (chordSet ηi)
  set ρ := min (ρ₀ / 2) 1 with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) one_pos
  have hρρ₀ : ρ ≤ ρ₀ / 2 := min_le_left _ _
  have hm1 : ((-1 : ℝ) : ℂ) = (-1 : ℂ) := by push_cast; rfl
  have hev1 : ∀ᶠ n in atTop, ∀ t ≥ (0 : ℝ), η n t ∉ ball ((-1 : ℝ) : ℂ) ρ := by
    have hev := eventually_le_dist_chord (K := {(-1 : ℂ)}) hc hρ0 (norm_nonneg (-1 : ℂ))
      (fun z hz => by rw [mem_singleton_iff.1 hz]) (fun z hz t ht => by
        rw [mem_singleton_iff.1 hz]; exact infDist_le_dist_of_mem ⟨t, ht, rfl⟩)
    filter_upwards [hev] with n hn t ht hb
    have h1 := hn (-1) rfl t ht
    rw [mem_ball, dist_comm, hm1] at hb
    linarith
  have hi1 : ∀ t ≥ (0 : ℝ), ηi t ∉ ball ((-1 : ℝ) : ℂ) ρ := fun t ht hb => by
    have h1 : ρ₀ ≤ dist (-1 : ℂ) (ηi t) := infDist_le_dist_of_mem ⟨t, ht, rfl⟩
    rw [mem_ball, dist_comm, hm1] at hb
    linarith
  set z₀ : ℂ := ((-1 : ℝ) : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I with hz₀
  have hz₀H : z₀ ∈ H := by show 0 < z₀.im; simp [hz₀, hρ]
  have hz₀B : z₀ ∈ ball ((-1 : ℝ) : ℂ) ρ := by
    rw [mem_ball, dist_eq_norm, hz₀, add_sub_cancel_left, norm_mul, norm_I, mul_one,
      norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hz₀L : z₀ ∈ leftComponent ηi :=
    inter_ball_subset_leftComponent (by norm_num) hi1 ⟨hz₀H, hz₀B⟩
  -- a path in `D₁(ηi)` from `w` to `z₀`
  have hLo := isOpen_leftComponent hηi
  have hpc : IsPathConnected (leftComponent ηi) :=
    (hLo.isConnected_iff_isPathConnected).1
      ⟨leftComponent_nonempty hηi, isPreconnected_leftComponent hηi⟩
  have hj := hpc.joinedIn w hw z₀ hz₀L
  set γ := hj.somePath
  obtain ⟨ε, hε, hεL⟩ := Metric.isOpen_iff.1 hLo w hw
  set r₁ := ε / 2
  have hr₁ : 0 < r₁ := half_pos hε
  set S := closedBall w r₁ ∪ range γ with hSdef
  have hSL : S ⊆ leftComponent ηi := by
    rintro z (hz | ⟨s, rfl⟩)
    · exact hεL (closedBall_subset_ball (half_lt_self hε) hz)
    · exact hj.somePath_mem s
  have hSc : IsCompact S := (isCompact_closedBall w r₁).union (isCompact_range γ.continuous)
  have hwS : w ∈ S := Or.inl (mem_closedBall_self hr₁.le)
  have hz₀S : z₀ ∈ S := Or.inr ⟨1, γ.target⟩
  have hSp : IsPreconnected S :=
    (convex_closedBall w r₁).isPreconnected.union w (mem_closedBall_self hr₁.le)
      (show w ∈ range γ from ⟨0, γ.source⟩) (isPreconnected_range γ.continuous)
  -- positive distance from the limit chord
  obtain ⟨z₁, hz₁S, hmin⟩ := hSc.exists_isMinOn ⟨w, hwS⟩
    (continuous_infDist_pt (chordSet ηi)).continuousOn
  set δ := infDist z₁ (chordSet ηi)
  have hδ : 0 < δ := ((isClosed_chordSet hηi).notMem_iff_infDist_pos chordSet_nonempty).1
    fun h => (hSL hz₁S).1.2 h
  have hδS : ∀ z ∈ S, ∀ t ≥ (0 : ℝ), δ ≤ dist z (ηi t) := fun z hz t ht =>
    (show δ ≤ infDist z (chordSet ηi) from hmin hz).trans
      (infDist_le_dist_of_mem (show ηi t ∈ chordSet ηi from ⟨t, ht, rfl⟩))
  obtain ⟨R, hR⟩ := hSc.isBounded.subset_closedBall 0
  have hev2 := eventually_le_dist_chord hc hδ (le_max_right R 0)
    (fun z hz => (mem_closedBall_zero_iff.1 (hR hz)).trans (le_max_left R 0)) hδS
  refine ⟨ball w r₁, ball_mem_nhds w hr₁, ?_⟩
  filter_upwards [hev1, hev2] with n h1 h2
  have hz₀n : z₀ ∈ leftComponent (η n) :=
    inter_ball_subset_leftComponent (by norm_num) h1 ⟨hz₀H, hz₀B⟩
  have hSn : S ⊆ slitH (η n) := fun z hz => by
    refine ⟨(hSL hz).1.1, ?_⟩
    rintro ⟨t, ht, rfl⟩
    have := h2 _ hz t ht
    rw [dist_self] at this
    linarith
  rw [leftComponent_eq (hη n)] at hz₀n ⊢
  rw [connectedComponentIn_eq hz₀n]
  exact ball_subset_closedBall.trans
    ((subset_union_left).trans (hSp.subset_connectedComponentIn hz₀S hSn))

/-- (i) at every point of the doubled domain. -/
theorem eventually_nhds_subset_leftDoubled (hη : ∀ n, IsSimpleChord (η n))
    (hηi : IsSimpleChord ηi) (hc : SphereUniformConv η ηi) {w : ℂ}
    (hw : w ∈ leftDoubled ηi) :
    ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ leftDoubled (η n) := by
  rcases hw with (hw | ⟨v, hv, rfl⟩) | ⟨h0, hneg⟩
  · obtain ⟨U, hU, hev⟩ := eventually_nhds_subset_leftComponent hη hηi hc hw
    exact ⟨U, hU, hev.mono fun n hn => hn.trans (leftComponent_subset_leftDoubled _)⟩
  · obtain ⟨U, hU, hev⟩ := eventually_nhds_subset_leftComponent hη hηi hc hv
    refine ⟨(starRingEnd ℂ) ⁻¹' U,
      continuous_conj.continuousAt.preimage_mem_nhds (by rwa [conj_conj]), ?_⟩
    filter_upwards [hev] with n hn z hz
    exact Or.inl (Or.inr ⟨conj z, hn hz, conj_conj z⟩)
  · obtain ⟨r, hr, hev⟩ := eventually_ball_subset_leftDoubled_neg hηi hc hneg
    have hw : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h0])
    exact ⟨ball (w.re : ℂ) r, by rw [← hw]; exact ball_mem_nhds _ hr, hev⟩

/-- (ii), abstract form: a closure point that is a limit of non-members `a n ∉ G n`, while each
point of `D` lies in `G n` eventually, is a limit of frontier points of `G n`. -/
theorem exists_frontier_seq {G : ℕ → Set ℂ} (hGo : ∀ n, IsOpen (G n)) {D : Set ℂ} {w : ℂ}
    (hw : w ∈ closure D) (hG : ∀ z ∈ D, ∀ᶠ n in atTop, z ∈ G n) {a : ℕ → ℂ}
    (ha : Tendsto a atTop (𝓝 w)) (haG : ∀ᶠ n in atTop, a n ∉ G n)
    (hne : ∀ n, (frontier (G n)).Nonempty) :
    ∃ u : ℕ → ℂ, (∀ n, u n ∈ frontier (G n)) ∧ Tendsto u atTop (𝓝 w) := by
  have key : ∀ ε > 0, ∀ᶠ n in atTop, infDist w (frontier (G n)) < ε := by
    intro ε hε
    obtain ⟨z, hzD, hz⟩ := Metric.mem_closure_iff.1 hw (ε / 2) (half_pos hε)
    filter_upwards [hG z hzD, haG, (Metric.tendsto_nhds.1 ha) (ε / 2) (half_pos hε)] with
      n hzn han hdn
    have hseg : segment ℝ z (a n) ⊆ ball w (ε / 2) :=
      (convex_ball w (ε / 2)).segment_subset (by rw [mem_ball, dist_comm]; exact hz) hdn
    obtain ⟨u, hu1, hu2⟩ := inter_frontier_nonempty_of_isPreconnected
      (convex_segment z (a n)).isPreconnected (hGo n) (left_mem_segment ℝ _ _) hzn
      (right_mem_segment ℝ _ _) han
    have hu := hseg hu1
    rw [mem_ball, dist_comm] at hu
    exact (infDist_le_dist_of_mem hu2).trans_lt (by linarith)
  have hex : ∀ n : ℕ, ∃ u ∈ frontier (G n),
      dist w u < infDist w (frontier (G n)) + 1 / ((n : ℝ) + 1) := fun n =>
    (infDist_lt_iff (hne n)).1 (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
  choose u hu hud using hex
  refine ⟨u, hu, ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (eventually_lt_nhds (half_pos hε))
  filter_upwards [key (ε / 2) (half_pos hε), h1] with n h2 h3
  rw [dist_comm]
  linarith [hud n]

/-- Frontier points of the doubled domain: chord points, their conjugates, or `[0,∞)`. -/
theorem frontier_leftDoubled_cases (hηi : IsSimpleChord ηi) {w : ℂ}
    (hw : w ∈ frontier (leftDoubled ηi)) :
    (∃ t ≥ (0 : ℝ), w = ηi t) ∨ (∃ t ≥ (0 : ℝ), w = conj (ηi t)) ∨ (w.im = 0 ∧ 0 ≤ w.re) := by
  rw [(isOpen_leftDoubled hηi).frontier_eq] at hw
  obtain ⟨hcl, hnot⟩ := hw
  have hR : closure {z : ℂ | z.im = 0 ∧ z.re < 0} ⊆ {z : ℂ | z.im = 0} :=
    closure_minimal (fun z hz => hz.1) (isClosed_eq continuous_im continuous_const)
  have hC : closure ((starRingEnd ℂ) '' leftComponent ηi) ⊆
      (starRingEnd ℂ) ⁻¹' closure (leftComponent ηi) := by
    rw [conj_image_eq_preimage]; exact continuous_conj.closure_preimage_subset _
  have hL : closure (leftComponent ηi) ⊆ Hbar := closure_subset_Hbar (leftComponent_subset_H ηi)
  unfold leftDoubled at hcl hnot
  rw [closure_union, closure_union] at hcl
  -- a point of `ℍ` in the closure of `D₁` but not in `D₁` is a chord point
  have hchord : ∀ v ∈ closure (leftComponent ηi), v ∈ H → v ∉ leftComponent ηi →
      ∃ t ≥ (0 : ℝ), v = ηi t := fun v hv hvH hvD => by
    by_contra hK
    refine hvD (mem_leftComponent_of_mem_closure hηi hv ⟨hvH, ?_⟩)
    rintro ⟨t, ht, rfl⟩
    exact hK ⟨t, ht, rfl⟩
  rcases lt_trichotomy w.im 0 with him | him | him
  · right; left
    have hwC : w ∈ closure ((starRingEnd ℂ) '' leftComponent ηi) := by
      rcases hcl with (h | h) | h
      · have : 0 ≤ w.im := hL h
        linarith
      · exact h
      · have : w.im = 0 := hR h
        linarith
    have hv := hC hwC
    have hvH : conj w ∈ H := by show 0 < (conj w).im; rw [conj_im]; linarith
    obtain ⟨t, ht, hte⟩ := hchord _ hv hvH fun h => hnot (Or.inl (Or.inr ⟨conj w, h, conj_conj w⟩))
    exact ⟨t, ht, by rw [← hte, conj_conj]⟩
  · right; right
    refine ⟨him, not_lt.1 fun hneg => hnot (Or.inr ⟨him, hneg⟩)⟩
  · left
    have hwL : w ∈ closure (leftComponent ηi) := by
      rcases hcl with (h | h) | h
      · exact h
      · have : 0 ≤ (conj w).im := hL (hC h)
        rw [conj_im] at this
        linarith
      · have : w.im = 0 := hR h
        linarith
    exact hchord w hwL him fun h => hnot (Or.inl (Or.inl h))

/-- **KT2 input K.** Sphere-uniform convergence of simple chords implies kernel convergence of
the doubled left domains with respect to `−1`. -/
theorem leftDoubledKernel : LeftDoubledKernel := by
  intro η ηi hη hηi hc
  have hi := fun w (hw : w ∈ leftDoubled ηi) => eventually_nhds_subset_leftDoubled hη hηi hc hw
  refine ⟨Or.inr ⟨isOpen_leftDoubled hηi, isConnected_leftDoubled hηi, leftDoubled_ne_univ,
    neg_one_mem_leftDoubled ηi, hi⟩, fun w hw => ?_⟩
  have hGev : ∀ z ∈ leftDoubled ηi, ∀ᶠ n in atTop, z ∈ leftDoubled (η n) := fun z hz => by
    obtain ⟨U, hU, hev⟩ := hi z hz
    exact hev.mono fun n hn => hn (mem_of_mem_nhds hU)
  have hcl : w ∈ closure (leftDoubled ηi) := frontier_subset_closure hw
  have hne : ∀ n, (frontier (leftDoubled (η n))).Nonempty :=
    fun n => ⟨0, zero_mem_frontier_leftDoubled (hη n)⟩
  have hGo : ∀ n, IsOpen (leftDoubled (η n)) := fun n => isOpen_leftDoubled (hη n)
  rcases frontier_leftDoubled_cases hηi hw with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨h0, hre⟩
  · exact exists_frontier_seq hGo hcl hGev (tendsto_of_sphereUniformConv hc ht)
      (Eventually.of_forall fun n => (chord_notMem_leftDoubled (hη n) ht).1) hne
  · exact exists_frontier_seq hGo hcl hGev
      ((continuous_conj.tendsto _).comp (tendsto_of_sphereUniformConv hc ht))
      (Eventually.of_forall fun n => (chord_notMem_leftDoubled (hη n) ht).2) hne
  · exact exists_frontier_seq hGo hcl hGev tendsto_const_nhds
      (Eventually.of_forall fun n => nonneg_notMem_leftDoubled _ h0 hre) hne

end QuantumZipper.CA.Kernel
