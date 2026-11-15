import InteractingSLE.Foundations.Loewner.ConformalImage
import InteractingSLE.Foundations.Loewner.ConformalImageLoewner
import InteractingSLE.Foundations.Loewner.HullKernel
import InteractingSLE.Foundations.Loewner.YuanFiber

/-!
# Uniform limits of simple paths generate Loewner chains

Packet PROVE-YUAN-M23: [Yua22, Theorem 1.1, (iii) ⇒ (i)] together with Loewner's theorem for
locally growing hull families, in the compact-interval form of Specification Proposition 6.12
(`source/spec/p193-240.md`, p. 211). Reference for the estimates: G. F. Lawler, *Conformally
invariant processes in the plane* (2005), Proposition 3.76 and §4.1.

Let `η : [0, S] → ℍ̄` be continuous, `η 0 = 0`, with strictly increasing fillings
`K_t = fill(η[0, t])`, and let `γ_n → η` uniformly on `[0, S]`, where each `γ_n` is a simple
path with `γ_n 0 = 0` and `γ_n((0, S]) ⊆ ℍ`.

## The estimate for simple paths

`SimpleCurveLocalGrowth` is [Law05, Proposition 3.76] for simple paths, with a universal
constant `C`: if `γ` is simple, `|γ| ≤ R`, and `γ([s, t]) ⊆ B̄(γ(s), d)` with `d ≤ R`, then
`g_{fill γ[0,s]}(γ((s, t]))` lies in a closed disc of radius `C √(d R)` centred on `ℝ`. It is
proved in `YuanCharacterisationSimple.lean`; here it is an explicit hypothesis.

## Main results

* `kernelConvergesTo_fillH`: `ℍ \ fill(γ_n[0, s]) → ℍ \ fill(η[0, s])` in the kernel sense (no
  simplicity is needed), so the mapping-out functions converge locally uniformly
  (`HullKernel`).
* `exists_ray_mem`: every point `z` of `K_t \ K_s` has a trace point `η(u)`, `u ∈ (s, t]`,
  `η(u) ∉ K_s`, with `g_s(η(u))` on the vertical ray above `g_s(z)`.
* `exists_forall_norm_mapOut_sub_le`: the uniform local growth of `(K_t)`: for `t − s ≤ δ` the
  increment `g_s(K_t \ K_s)` lies in a small disc centred on `ℝ`.
* `exists_loewner_of_tendstoUniformlyOn`: the chain `(K_t)` is a Loewner chain after the capacity
  time change, with a continuous driver (`IsContinuouslyGrowing.loewner`, [Law05] §4.1).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace YuanCharacterisation


/-! ### Fillings of paths -/

section PathHull

variable {ζ : ℝ → ℂ} {s : ℝ}

theorem isCompact_image_Icc (hζ : ContinuousOn ζ (Icc 0 s)) : IsCompact (ζ '' Icc 0 s) :=
  isCompact_Icc.image_of_continuousOn hζ

/-- The filling of a path started on `ℝ` is a compact `ℍ`-hull. -/
theorem isHPHull_fillH_image_of_im (hζ : ContinuousOn ζ (Icc 0 s)) (hs : 0 ≤ s)
    (h0 : (ζ 0).im = 0) : IsHPHull (fillH (ζ '' Icc 0 s)) := by
  refine isHPHull_fillH_of_isPreconnected (isCompact_image_Icc hζ).isBounded ?_
  refine IsPreconnected.union (ζ 0) ⟨0, ⟨le_rfl, hs⟩, rfl⟩ ?_ (isPreconnected_Icc.image _ hζ)
    isPreconnected_lowerHalf
  show (ζ 0).im ≤ 0
  rw [h0]

/-- The filling of a path started at `0` is a compact `ℍ`-hull. -/
theorem isHPHull_fillH_image (hζ : ContinuousOn ζ (Icc 0 s)) (hs : 0 ≤ s) (h0 : ζ 0 = 0) :
    IsHPHull (fillH (ζ '' Icc 0 s)) :=
  isHPHull_fillH_image_of_im hζ hs (by rw [h0, zero_im])

theorem not_isBounded_H : ¬ Bornology.IsBounded H := by
  have : H = {w : ℂ | (0 : ℝ) < w.im} := rfl
  rw [this]
  exact not_isBounded_setOf_lt_im 0

/-- A set in the closed lower half-plane has empty filling. -/
theorem fillH_eq_empty_of_subset {A : Set ℂ} (hA : A ⊆ {z : ℂ | z.im ≤ 0}) : fillH A = ∅ := by
  have hcl : closure A ⊆ {z : ℂ | z.im ≤ 0} := closure_minimal hA isClosed_lowerHalf
  ext z
  simp only [mem_empty_iff_false, iff_false]
  rintro ⟨hz, h | h⟩
  · exact (not_le.2 (show (0 : ℝ) < z.im from hz)) (hcl h)
  · have hHeq : H \ closure A = H := by
      refine sdiff_eq_left.2 (Set.disjoint_left.2 fun w hw hwA => ?_)
      exact (not_le.2 (show (0 : ℝ) < w.im from hw)) (hcl hwA)
    rw [hHeq, convex_H.isPreconnected.connectedComponentIn hz] at h
    exact not_isBounded_H h

theorem fillH_image_Icc_zero (h0 : ζ 0 = 0) : fillH (ζ '' Icc 0 0) = ∅ := by
  refine fillH_eq_empty_of_subset ?_
  rintro _ ⟨u, hu, rfl⟩
  have : u = 0 := le_antisymm hu.2 hu.1
  subst this
  show (ζ 0).im ≤ 0
  rw [h0, zero_im]

theorem mem_fillH_image {u : ℝ} (hu : u ∈ Icc 0 s) (hH : ζ u ∈ H) :
    ζ u ∈ fillH (ζ '' Icc 0 s) :=
  mem_fillH_of_mem_closure hH (subset_closure ⟨u, hu, rfl⟩)

/-- A point of the path is never in the complement of its filling. -/
theorem notMem_H_diff_fillH {u : ℝ} (hu : u ∈ Icc 0 s) : ζ u ∉ H \ fillH (ζ '' Icc 0 s) :=
  fun h => h.2 (mem_fillH_image hu h.1)

/-- `ℍ \ fill(ζ[0, s])` is the component of `(R + 1) i` in `ℍ \ ζ[0, s]`. -/
theorem H_diff_fillH_image {R : ℝ} (hR : 0 < R) (hζ : ContinuousOn ζ (Icc 0 s))
    (hζR : ∀ u ∈ Icc 0 s, ‖ζ u‖ < R) :
    H \ fillH (ζ '' Icc 0 s) =
      connectedComponentIn (H \ ζ '' Icc 0 s) (((R + 1 : ℝ) : ℂ) * I) := by
  have hcl : closure (ζ '' Icc 0 s) = ζ '' Icc 0 s := (isCompact_image_Icc hζ).isClosed.closure_eq
  have hsub : closure (ζ '' Icc 0 s) ⊆ ball 0 R := by
    rw [hcl]
    rintro _ ⟨u, hu, rfl⟩
    exact mem_ball_zero_iff.2 (hζR u hu)
  rw [H_diff_fillH hR hsub, hcl]

/-- Points above height `R` are outside the filling. -/
theorem mem_H_diff_fillH_of_lt_im {R : ℝ} (hR : 0 < R) (hζ : ContinuousOn ζ (Icc 0 s))
    (hζR : ∀ u ∈ Icc 0 s, ‖ζ u‖ < R) {w : ℂ} (hw : R < w.im) : w ∈ H \ fillH (ζ '' Icc 0 s) := by
  rw [H_diff_fillH_image hR hζ hζR]
  refine setOf_lt_im_subset_connectedComponentIn hR ?_ hw
  rintro _ ⟨u, hu, rfl⟩
  exact mem_ball_zero_iff.2 (hζR u hu)

/-- A connected subset of `ℍ` that avoids the path and meets the complement of its filling lies
in that complement. -/
theorem subset_H_diff_fillH_of_isPreconnected {R : ℝ} (hR : 0 < R)
    (hζ : ContinuousOn ζ (Icc 0 s)) (hζR : ∀ u ∈ Icc 0 s, ‖ζ u‖ < R) {Q : Set ℂ}
    (hQ : IsPreconnected Q) (hQH : Q ⊆ H) (hQζ : Disjoint Q (ζ '' Icc 0 s)) {q : ℂ}
    (hqQ : q ∈ Q) (hq : q ∈ H \ fillH (ζ '' Icc 0 s)) : Q ⊆ H \ fillH (ζ '' Icc 0 s) := by
  rw [H_diff_fillH_image hR hζ hζR] at hq ⊢
  rw [connectedComponentIn_eq hq]
  exact hQ.subset_connectedComponentIn hqQ fun w hw => ⟨hQH hw, Set.disjoint_left.1 hQζ hw⟩

end PathHull

/-! ### Kernel convergence of the fillings of uniformly convergent paths -/

section Kernel

variable {η : ℝ → ℂ} {γ : ℕ → ℝ → ℂ} {s R : ℝ}

/-- A compact set avoiding the limit path eventually avoids the approximating paths. -/
theorem eventually_disjoint_image (hη : ContinuousOn η (Icc 0 s))
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 s)) {Q : Set ℂ} (hQ : IsCompact Q)
    (hQη : Disjoint Q (η '' Icc 0 s)) : ∀ᶠ n in atTop, Disjoint Q (γ n '' Icc 0 s) := by
  rcases Q.eq_empty_or_nonempty with hQe | hQne
  · exact Eventually.of_forall fun n => by rw [hQe]; exact empty_disjoint _
  rcases (Icc (0 : ℝ) s).eq_empty_or_nonempty with hIe | hIne
  · exact Eventually.of_forall fun n => by rw [hIe, image_empty]; exact disjoint_empty _
  have hne : (η '' Icc 0 s).Nonempty := hIne.image η
  have hcl : IsClosed (η '' Icc 0 s) := (isCompact_image_Icc hη).isClosed
  obtain ⟨q₀, hq₀, hmin⟩ := hQ.exists_isMinOn hQne
    (continuous_infDist_pt (η '' Icc 0 s)).continuousOn
  have hpos : 0 < infDist q₀ (η '' Icc 0 s) :=
    (hcl.notMem_iff_infDist_pos hne).1 (Set.disjoint_left.1 hQη hq₀)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv _ hpos] with n hn
  refine Set.disjoint_left.2 fun q hq hqγ => ?_
  obtain ⟨u, hu, hqu⟩ := hqγ
  have h1 : infDist q₀ (η '' Icc 0 s) ≤ dist q (η u) :=
    (isMinOn_iff.1 hmin q hq).trans (infDist_le_dist_of_mem ⟨u, hu, rfl⟩)
  have h2 : dist (η u) (γ n u) < infDist q₀ (η '' Icc 0 s) := hn u hu
  rw [← hqu, dist_comm] at h1
  linarith

/-- Condition (i) of kernel convergence: every point of `ℍ \ fill(η[0, s])` has a neighbourhood
eventually contained in `ℍ \ fill(γ_n[0, s])` (join it to `(R + 1) i` by a path; the path keeps a
positive distance from `η([0, s])`). -/
theorem exists_nhds_eventually_subset (hR : 0 < R) (hη : ContinuousOn η (Icc 0 s))
    (hηR : ∀ u ∈ Icc 0 s, ‖η u‖ < R) (hγ : ∀ n, ContinuousOn (γ n) (Icc 0 s))
    (hγR : ∀ n, ∀ u ∈ Icc 0 s, ‖γ n u‖ < R) (hconv : TendstoUniformlyOn γ η atTop (Icc 0 s))
    {w : ℂ} (hw : w ∈ H \ fillH (η '' Icc 0 s)) :
    ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ H \ fillH (γ n '' Icc 0 s) := by
  set D := H \ fillH (η '' Icc 0 s) with hD
  have hDo : IsOpen D := isOpen_H_diff_fillH (isCompact_image_Icc hη).isBounded
  set w₀ : ℂ := ((R + 1 : ℝ) : ℂ) * I with hw₀
  have hw₀im : R < w₀.im := by simp [hw₀]
  have hw₀D : w₀ ∈ D := mem_H_diff_fillH_of_lt_im hR hη hηR hw₀im
  have hDc : IsConnected D := by
    have h1 := hw₀D
    rw [hD, H_diff_fillH_image hR hη hηR] at h1 ⊢
    exact isConnected_connectedComponentIn_iff.2 (connectedComponentIn_subset _ _ h1)
  obtain ⟨p, hp⟩ := ((hDo.isConnected_iff_isPathConnected.1 hDc).joinedIn w hw w₀ hw₀D)
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hDo w hw
  set Q := range p ∪ closedBall w (ε / 2) with hQ
  have hQc : IsCompact Q := (isCompact_range p.continuous).union (isCompact_closedBall w _)
  have hQp : IsPreconnected Q :=
    IsPreconnected.union w ⟨0, p.source⟩ (mem_closedBall_self (by positivity))
      (isPreconnected_range p.continuous) (convex_closedBall w _).isPreconnected
  have hQD : Q ⊆ D := by
    rintro q (⟨t, rfl⟩ | hq)
    · exact hp t
    · exact hεD (closedBall_subset_ball (by linarith) hq)
  have hQH : Q ⊆ H := fun q hq => (hQD hq).1
  have hQη : Disjoint Q (η '' Icc 0 s) := Set.disjoint_left.2 fun q hq ⟨u, hu, hqu⟩ =>
    notMem_H_diff_fillH hu (hqu ▸ hQD hq)
  refine ⟨ball w (ε / 2), ball_mem_nhds w (by positivity), ?_⟩
  filter_upwards [eventually_disjoint_image hη hconv hQc hQη] with n hn
  have hsub := subset_H_diff_fillH_of_isPreconnected hR (hγ n) (hγR n) hQp hQH hn
    (q := w₀) (Or.inl ⟨1, p.target⟩) (mem_H_diff_fillH_of_lt_im hR (hγ n) (hγR n) hw₀im)
  exact fun q hq => hsub (Or.inr (ball_subset_closedBall hq))

/-- **Kernel convergence**: if `γ_n → η` uniformly on `[0, s]` (all paths in `B(0, R)`), then
`ℍ \ fill(γ_n[0, s]) → ℍ \ fill(η[0, s])` in the kernel sense with respect to `(R + 1) i`. -/
theorem kernelConvergesTo_fillH (hR : 0 < R) (hη : ContinuousOn η (Icc 0 s))
    (hηR : ∀ u ∈ Icc 0 s, ‖η u‖ < R) (hγ : ∀ n, ContinuousOn (γ n) (Icc 0 s))
    (hγR : ∀ n, ∀ u ∈ Icc 0 s, ‖γ n u‖ < R) (hconv : TendstoUniformlyOn γ η atTop (Icc 0 s)) :
    QuantumZipper.CA.Kernel.KernelConvergesTo (fun n => H \ fillH (γ n '' Icc 0 s))
      (H \ fillH (η '' Icc 0 s)) (((R + 1 : ℝ) : ℂ) * I) := by
  set D := H \ fillH (η '' Icc 0 s) with hD
  have hDo : IsOpen D := isOpen_H_diff_fillH (isCompact_image_Icc hη).isBounded
  have hw₀im : R < (((R + 1 : ℝ) : ℂ) * I).im := by simp
  have hw₀D : ((R + 1 : ℝ) : ℂ) * I ∈ D := mem_H_diff_fillH_of_lt_im hR hη hηR hw₀im
  have hDc : IsConnected D := by
    have h1 := hw₀D
    rw [hD, H_diff_fillH_image hR hη hηR] at h1 ⊢
    exact isConnected_connectedComponentIn_iff.2 (connectedComponentIn_subset _ _ h1)
  have h0H : (0 : ℂ) ∉ H := fun h => (lt_irrefl (0 : ℝ))
    (by have : (0 : ℝ) < (0 : ℂ).im := h; simp at this)
  refine ⟨Or.inr ⟨hDo, hDc, fun h => h0H ((h ▸ mem_univ (0 : ℂ)) : (0 : ℂ) ∈ D).1, hw₀D,
    fun w hw => exists_nhds_eventually_subset hR hη hηR hγ hγR hconv hw⟩, ?_⟩
  intro w hw
  have hGo : ∀ n, IsOpen (H \ fillH (γ n '' Icc 0 s)) := fun n =>
    isOpen_H_diff_fillH (isCompact_image_Icc (hγ n)).isBounded
  refine exists_tendsto_frontier (fun n => frontier_nonempty_of_isOpen
    ⟨_, mem_H_diff_fillH_of_lt_im hR (hγ n) (hγR n) hw₀im⟩
    (fun h => h0H ((h ▸ mem_univ (0 : ℂ)) : (0 : ℂ) ∈ H \ fillH (γ n '' Icc 0 s)).1)) ?_
  intro ε hε
  have hwcl : w ∈ closure D := hw.1
  have hwD : w ∉ D := by rw [hDo.frontier_eq] at hw; exact hw.2
  obtain ⟨d, hdD, hdw⟩ := Metric.mem_closure_iff.1 hwcl ε hε
  obtain ⟨U, hU, hUev⟩ := exists_nhds_eventually_subset hR hη hηR hγ hγR hconv hdD
  have hev2 : ∀ᶠ n in atTop, ∃ e ∈ ball w ε, e ∉ H \ fillH (γ n '' Icc 0 s) := by
    by_cases hwH : w ∈ H
    · have hfr := frontier_H_diff_fillH_subset (isCompact_image_Icc hη).isBounded hw
      have hwη : w ∈ η '' Icc 0 s := by
        rcases hfr with h | h
        · exact absurd (show w.im = 0 from h) (ne_of_gt hwH)
        · rwa [(isCompact_image_Icc hη).isClosed.closure_eq] at h
      obtain ⟨u, hu, rfl⟩ := hwη
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv ε hε] with n hn
      exact ⟨γ n u, mem_ball.2 (by rw [dist_comm]; exact hn u hu), notMem_H_diff_fillH hu⟩
    · exact Eventually.of_forall fun n => ⟨w, mem_ball_self hε, fun h => hwH h.1⟩
  filter_upwards [hUev, hev2] with n hn hn2
  obtain ⟨e, he, heG⟩ := hn2
  exact ball_inter_frontier_nonempty (hGo n) (mem_ball.2 (by rw [dist_comm]; exact hdw))
    (hn (mem_of_mem_nhds hU)) he heG

end Kernel

/-! ### The estimate for simple paths -/

/-- **[Law05, Proposition 3.76] for simple paths, with constant `C`**: for a simple path `γ` on
`[0, S]` with `γ 0 = 0`, `γ((0, S]) ⊆ ℍ` and `|γ| ≤ R`, and for `0 ≤ s ≤ t ≤ S` with
`γ([s, t]) ⊆ B̄(γ(s), d)`, `0 < d ≤ R`, the image of `γ((s, t])` under the mapping-out function
of `fill(γ[0, s])` lies in a closed disc of radius `C √(d R)` centred on `ℝ`. -/
def SimpleCurveLocalGrowthWith (C : ℝ) : Prop :=
  ∀ (γ : ℝ → ℂ) (S R : ℝ), ContinuousOn γ (Icc 0 S) → InjOn γ (Icc 0 S) → γ 0 = 0 →
    MapsTo γ (Ioc 0 S) H → (∀ u ∈ Icc 0 S, ‖γ u‖ ≤ R) →
    ∀ s t d : ℝ, 0 ≤ s → s ≤ t → t ≤ S → 0 < d → d ≤ R → (∀ u ∈ Icc s t, ‖γ u - γ s‖ ≤ d) →
    ∃ x : ℝ, ∀ u ∈ Ioc s t,
      ‖ConformalImage.mapOut (fillH (γ '' Icc 0 s)) (γ u) - x‖ ≤ C * √(d * R)

/-- **[Law05, Proposition 3.76] for simple paths**: `SimpleCurveLocalGrowthWith C` for some
universal constant `C ≥ 0`. -/
def SimpleCurveLocalGrowth : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ SimpleCurveLocalGrowthWith C

/-! ### Increments of the filled hulls of a path -/

section Ray

variable {η : ℝ → ℂ} {S R : ℝ}

/-- `Im w ≤ Im F(w)` for the inverse `F` of a mapping-out function. -/
theorem im_le_im_symm {A : Set ℂ} {g F : ℂ → ℂ} (hA : IsHPHull A) (hg : IsMapOut A g)
    (hF : ∀ w ∈ H, F w ∈ H \ A ∧ g (F w) = w) {w : ℂ} (hw : w ∈ H) : w.im ≤ (F w).im := by
  have h := hg.im_le hA (hF w hw).1
  rwa [(hF w hw).2] at h

/-- **The ray lemma.** Every point `z` of `K_t \ K_s` (fillings of a path) is reached through a
trace point: there is `u ∈ (s, t]` with `η(u) ∉ K_s` and `g_s(η(u))` on the vertical ray above
`g_s(z)`. (Pull the ray back by `g_s⁻¹`; it joins `z ∈ K_t` to a point above `K_t`, so it meets
`η([0, t])`, and it avoids `η([0, s])`.) -/
theorem exists_ray_mem (hR : 0 < R) (hη : ContinuousOn η (Icc 0 S)) (h0 : η 0 = 0)
    (hηR : ∀ u ∈ Icc 0 S, ‖η u‖ < R) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htS : t ≤ S)
    {z : ℂ} (hz : z ∈ fillH (η '' Icc 0 t) \ fillH (η '' Icc 0 s)) :
    ∃ u ∈ Ioc s t, η u ∈ H \ fillH (η '' Icc 0 s) ∧ ∃ τ : ℝ, 0 ≤ τ ∧
      ConformalImage.mapOut (fillH (η '' Icc 0 s)) (η u) =
        ConformalImage.mapOut (fillH (η '' Icc 0 s)) z + (τ : ℂ) * I := by
  have hηs : ContinuousOn η (Icc 0 s) := hη.mono (Icc_subset_Icc_right (hst.trans htS))
  have hηt : ContinuousOn η (Icc 0 t) := hη.mono (Icc_subset_Icc_right htS)
  have hηRt : ∀ u ∈ Icc 0 t, ‖η u‖ < R := fun u hu => hηR u ⟨hu.1, hu.2.trans htS⟩
  set A := fillH (η '' Icc 0 s) with hAdef
  have hA : IsHPHull A := isHPHull_fillH_image hηs hs h0
  set g := ConformalImage.mapOut A with hgdef
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  obtain ⟨F, hFd, hF1, hF2⟩ := hg.exists_symm hA
  have hzA : z ∈ H \ A := ⟨fillH_subset_H _ hz.1, hz.2⟩
  set w := g z with hw
  have hwH : w ∈ H := hg.1.2.mapsTo hzA
  have hray : ∀ τ : ℝ, 0 ≤ τ → w + (τ : ℂ) * I ∈ H := fun τ hτ => by
    show 0 < (w + (τ : ℂ) * I).im
    have : 0 < w.im := hwH
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith
  by_contra hcon
  push Not at hcon
  set M : ℝ := R + 1 with hM
  set P := (fun τ : ℝ => F (w + (τ : ℂ) * I)) '' Icc 0 M with hP
  have hcont : ContinuousOn (fun τ : ℝ => F (w + (τ : ℂ) * I)) (Icc 0 M) := by
    refine hFd.continuousOn.comp (by fun_prop) fun τ hτ => hray τ hτ.1
  have hPc : IsPreconnected P := isPreconnected_Icc.image _ hcont
  have hPA : P ⊆ H \ A := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact (hF1 _ (hray τ hτ.1)).1
  have hPH : P ⊆ H := fun q hq => (hPA hq).1
  have hPη : Disjoint P (η '' Icc 0 t) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨τ, hτ, rfl⟩ ⟨u, hu, hηu⟩
    have hηu' : η u = F (w + (τ : ℂ) * I) := hηu
    have hmem := (hF1 _ (hray τ hτ.1))
    rw [← hηu'] at hmem
    by_cases hus : u ≤ s
    · exact notMem_H_diff_fillH (ζ := η) (s := s) ⟨hu.1, hus⟩ hmem.1
    · refine hcon u ⟨not_le.1 hus, hu.2⟩ hmem.1 τ hτ.1 ?_
      rw [hmem.2]
  have htop : F (w + (M : ℂ) * I) ∈ H \ fillH (η '' Icc 0 t) := by
    refine mem_H_diff_fillH_of_lt_im hR hηt hηRt ?_
    have h1 := im_le_im_symm hA hg hF1 (hray M (by linarith))
    have h2 : (w + (M : ℂ) * I).im = w.im + M := by simp
    have : 0 < w.im := hwH
    linarith
  have hsub := subset_H_diff_fillH_of_isPreconnected hR hηt hηRt hPc hPH hPη
    ⟨M, ⟨by linarith, le_rfl⟩, rfl⟩ htop
  have hzP : z ∈ P := ⟨0, ⟨le_rfl, by linarith⟩, by simp [hw, hF2 z hzA]⟩
  exact (hsub hzP).2 hz.1

end Ray

/-! ### Locally growing families of hulls: the driving function -/

section Growing

open ConformalImage (inc)

variable {B : ℝ → Set ℂ} {T : ℝ}

theorem isHPHull_inc_of (hB : ∀ t ∈ Icc 0 T, IsHPHull (B t)) (hmono : MonotoneOn B (Icc 0 T))
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) : IsHPHull (inc B s t) :=
  (ConformalImage.isMapOut_mapOut (hB s hs)).isHPHull_image (hB s hs) (hB t ht) (hmono hs ht hst)

theorem inc_mono (hmono : MonotoneOn B (Icc 0 T)) {s t t' : ℝ} (ht : t ∈ Icc 0 T)
    (ht' : t' ∈ Icc 0 T) (htt' : t ≤ t') : inc B s t ⊆ inc B s t' :=
  image_mono fun _ hz => ⟨hmono ht ht' htt' hz.1, hz.2⟩

/-- The candidate set for the driving value at `s`: `⋂_{t ∈ (s, T]} closure g_s(B t \ B s)`. -/
def drvSet (B : ℝ → Set ℂ) (T s : ℝ) : Set ℂ := ⋂ t : Ioc s T, closure (inc B s t)

theorem drvSet_nonempty (hB : ∀ t ∈ Icc 0 T, IsHPHull (B t)) (hmono : StrictMonoOn B (Icc 0 T))
    {s : ℝ} (hs : s ∈ Ico 0 T) : (drvSet B T s).Nonempty := by
  have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
  have hmem : ∀ t : Ioc s T, (t : ℝ) ∈ Icc 0 T := fun t => ⟨hs.1.trans t.2.1.le, t.2.2⟩
  have : Nonempty (Ioc s T) := ⟨⟨T, hs.2, le_rfl⟩⟩
  refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _ ?_ ?_ ?_ ?_
  · intro t₁ t₂
    refine ⟨⟨min t₁ t₂, lt_min t₁.2.1 t₂.2.1, (min_le_left _ _).trans t₁.2.2⟩, ?_, ?_⟩
    · exact closure_mono (inc_mono hmono.monotoneOn
        ⟨hs.1.trans (lt_min t₁.2.1 t₂.2.1).le, (min_le_left _ _).trans t₁.2.2⟩ (hmem t₁)
        (min_le_left _ _))
    · exact closure_mono (inc_mono hmono.monotoneOn
        ⟨hs.1.trans (lt_min t₁.2.1 t₂.2.1).le, (min_le_left _ _).trans t₁.2.2⟩ (hmem t₂)
        (min_le_right _ _))
  · intro t
    obtain ⟨z, hz⟩ := nonempty_of_ssubset (hmono hs' (hmem t) t.2.1)
    exact ⟨_, subset_closure ⟨z, hz, rfl⟩⟩
  · intro t
    exact (isHPHull_inc_of hB hmono.monotoneOn hs' (hmem t) t.2.1.le).2.1.isCompact_closure
  · intro t
    exact isClosed_closure

/-- Under uniform local growth, a point of `drvSet B T s` controls every short increment. -/
theorem inc_subset_closedBall_of_mem_drvSet {s ε δ : ℝ}
    (hδ : ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s ≤ δ →
      ∃ x : ℝ, ∀ z ∈ B t \ B s, ‖ConformalImage.mapOut (B s) z - x‖ ≤ ε)
    (hs : s ∈ Icc 0 T) {ζ : ℂ} (hζ : ζ ∈ drvSet B T s) {t : ℝ} (ht : t ∈ Ioc s T)
    (hts : t - s ≤ δ) : |ζ.im| ≤ ε ∧ inc B s t ⊆ closedBall ζ (2 * ε) := by
  obtain ⟨x, hx⟩ := hδ s t hs ⟨hs.1.trans ht.1.le, ht.2⟩ ht.1.le hts
  have hsub : inc B s t ⊆ closedBall (x : ℂ) ε := by
    rintro _ ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_eq_norm]
    exact hx z hz
  have hζx : ζ ∈ closedBall (x : ℂ) ε :=
    closure_minimal hsub isClosed_closedBall (mem_iInter.1 hζ ⟨t, ht⟩)
  rw [mem_closedBall, dist_eq_norm] at hζx
  refine ⟨?_, fun w hw => ?_⟩
  · have : (ζ - x).im = ζ.im := by simp
    rw [← this]
    exact (abs_im_le_norm _).trans hζx
  · have hw' := hsub hw
    rw [mem_closedBall, dist_eq_norm] at hw' ⊢
    calc ‖w - ζ‖ = ‖(w - x) - (ζ - x)‖ := by ring_nf
      _ ≤ ‖w - x‖ + ‖ζ - x‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith

/-- The points of `drvSet B T s` are real. -/
theorem im_eq_zero_of_mem_drvSet
    (hLG : ∀ ε > 0, ∃ δ > 0, ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s ≤ δ →
      ∃ x : ℝ, ∀ z ∈ B t \ B s, ‖ConformalImage.mapOut (B s) z - x‖ ≤ ε)
    {s : ℝ} (hs : s ∈ Ico 0 T) {ζ : ℂ} (hζ : ζ ∈ drvSet B T s) : ζ.im = 0 := by
  refine abs_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (abs_nonneg _))
  obtain ⟨δ, hδ, hδ'⟩ := hLG ε hε
  have ht : min T (s + δ) ∈ Ioc s T := ⟨lt_min hs.2 (by linarith), min_le_left _ _⟩
  have := (inc_subset_closedBall_of_mem_drvSet hδ' (Ico_subset_Icc_self hs) hζ ht
    (by linarith [min_le_right T (s + δ)])).1
  linarith

/-- The driving value at `s < T`: the real part of a point of `drvSet B T s` (`0` if empty). -/
def drvPoint (B : ℝ → Set ℂ) (T s : ℝ) : ℝ :=
  open scoped Classical in if h : (drvSet B T s).Nonempty then h.some.re else 0

section LG

variable (hB : ∀ t ∈ Icc 0 T, IsHPHull (B t)) (hmono : StrictMonoOn B (Icc 0 T))
  (hLG : ∀ ε > 0, ∃ δ > 0, ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s ≤ δ →
      ∃ x : ℝ, ∀ z ∈ B t \ B s, ‖ConformalImage.mapOut (B s) z - x‖ ≤ ε)
include hB hmono hLG

theorem drvPoint_mem {s : ℝ} (hs : s ∈ Ico 0 T) : (drvPoint B T s : ℂ) ∈ drvSet B T s := by
  have hne := drvSet_nonempty hB hmono hs
  have him := im_eq_zero_of_mem_drvSet hLG hs hne.some_mem
  have : ((hne.some.re : ℝ) : ℂ) = hne.some := Complex.ext (by simp) (by simp [him])
  have hd : drvPoint B T s = hne.some.re := by simp only [drvPoint, hne, ↓reduceDIte]
  rw [hd, this]
  exact hne.some_mem

/-- Short increments lie in small discs about the driving value. -/
theorem inc_subset_closedBall_drvPoint {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ s ∈ Ico 0 T,
    ∀ t ∈ Ioc s T, t - s ≤ δ → inc B s t ⊆ closedBall (drvPoint B T s : ℂ) ε := by
  obtain ⟨δ, hδ, hδ'⟩ := hLG (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs t ht hts => ?_⟩
  have := (inc_subset_closedBall_of_mem_drvSet hδ' (Ico_subset_Icc_self hs)
    (drvPoint_mem hB hmono hLG hs) ht hts).2
  rwa [show 2 * (ε / 2) = ε by ring] at this

/-- The driving value is uniformly continuous on `[0, T)`. -/
theorem abs_drvPoint_sub_le {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ s ∈ Ico 0 T, ∀ s' ∈ Ico 0 T,
    s ≤ s' → s' - s < δ → |drvPoint B T s' - drvPoint B T s| ≤ ε := by
  obtain ⟨δ, hδ, hδ'⟩ := inc_subset_closedBall_drvPoint hB hmono hLG (ε := ε / 6) (by positivity)
  refine ⟨δ, hδ, fun s hs s' hs' hss' hd => ?_⟩
  have hsI : s ∈ Icc 0 T := Ico_subset_Icc_self hs
  have hs'I : s' ∈ Icc 0 T := Ico_subset_Icc_self hs'
  set t := min T (s + δ) with htdef
  have ht' : t ∈ Ioc s' T := ⟨lt_min hs'.2 (by linarith), min_le_left _ _⟩
  have htI : t ∈ Icc 0 T := ⟨hs'.1.trans ht'.1.le, ht'.2⟩
  have ht : t ∈ Ioc s T := ⟨hss'.trans_lt ht'.1, ht'.2⟩
  have hts : t - s ≤ δ := by linarith [min_le_right T (s + δ)]
  set U := drvPoint B T s with hU
  set L := inc B s s' with hL
  have hLh : IsHPHull L := isHPHull_inc_of hB hmono.monotoneOn hsI hs'I hss'
  have hLsub : L ⊆ closedBall (U : ℂ) (ε / 6) := by
    rcases eq_or_lt_of_le hss' with heq | hlt
    · rw [hL, ← heq]
      rintro _ ⟨z, hz, rfl⟩
      exact absurd hz.1 hz.2
    · exact hδ' s hs s' ⟨hlt, hs'I.2⟩ (by linarith)
  have hgs := ConformalImage.isMapOut_mapOut (hB s hsI)
  have hcomp : EqOn (ConformalImage.mapOut (B s'))
      (ConformalImage.mapOut L ∘ ConformalImage.mapOut (B s)) (H \ B s') :=
    (ConformalImage.isMapOut_mapOut (hB s' hs'I)).eqOn (hB s' hs'I)
      (hgs.comp (hB s hsI) (hB s' hs'I) (hmono.monotoneOn hsI hs'I hss')
        (ConformalImage.isMapOut_mapOut hLh))
  have hsub : inc B s' t ⊆ closedBall (U : ℂ) ε := by
    rintro _ ⟨z, hz, rfl⟩
    have hzH : z ∈ H := (hB t htI).1 hz.1
    have hzs : z ∉ B s := fun h => hz.2 (hmono.monotoneOn hsI hs'I hss' h)
    have hgz : ConformalImage.mapOut (B s) z ∈ inc B s t := ⟨z, ⟨hz.1, hzs⟩, rfl⟩
    have hgzL : ConformalImage.mapOut (B s) z ∈ H \ L := by
      refine ⟨hgs.1.2.mapsTo ⟨hzH, hzs⟩, ?_⟩
      rintro ⟨z', hz', hzz'⟩
      have := hgs.1.2.injOn ⟨(hB s' hs'I).1 hz'.1, hz'.2⟩ ⟨hzH, hzs⟩ hzz'
      exact hz.2 (this ▸ hz'.1)
    have h1 := IsMapOut.norm_sub_center_le hLh (ConformalImage.isMapOut_mapOut hLh)
      (by positivity) hLsub hgzL
    have h2 := hδ' s hs t ht hts hgz
    rw [mem_closedBall, dist_eq_norm] at h2 ⊢
    rw [hcomp ⟨hzH, hz.2⟩]
    simp only [Function.comp]
    linarith
  have hmem := closure_minimal hsub isClosed_closedBall
    (mem_iInter.1 (drvPoint_mem hB hmono hLG hs') ⟨t, ht'⟩)
  rw [mem_closedBall, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hmem
  exact hmem

end LG

/-- **Loewner's theorem for locally growing hull families** (the driving function, [Law05]
§4.1): a strictly increasing family of compact `ℍ`-hulls on `[0, T]` with `B 0 = ∅` whose short
increments `g_{B s}(B t \ B s)` lie, uniformly in `s`, in small discs centred on `ℝ` is a
continuously growing family (`IsContinuouslyGrowing`) for a continuous driver `U`; if the hulls
shrink to `0` as `t → 0`, then `U 0 = 0`. -/
theorem exists_isContinuouslyGrowing (hT : 0 < T) (hB : ∀ t ∈ Icc 0 T, IsHPHull (B t))
    (hB0 : B 0 = ∅) (hmono : StrictMonoOn B (Icc 0 T))
    (hLG : ∀ ε > 0, ∃ δ > 0, ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s ≤ t → t - s ≤ δ →
      ∃ x : ℝ, ∀ z ∈ B t \ B s, ‖ConformalImage.mapOut (B s) z - x‖ ≤ ε)
    (hsmall : ∀ ε > 0, ∃ t ∈ Ioc 0 T, B t ⊆ closedBall 0 ε) :
    ∃ U : ℝ → ℝ, ConformalImage.IsContinuouslyGrowing B U T ∧ U 0 = 0 := by
  set U₀ := drvPoint B T with hU₀
  set U := extendFrom (Ico 0 T) U₀ with hU
  have hcl : closure (Ico (0 : ℝ) T) = Icc 0 T := closure_Ico hT.ne
  -- continuity of `U₀` within `[0, T)`
  have hcw : ∀ s ∈ Ico 0 T, Tendsto U₀ (𝓝[Ico 0 T] s) (𝓝 (U₀ s)) := by
    intro s hs
    refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hδ'⟩ := abs_drvPoint_sub_le hB hmono hLG (ε := ε / 2) (by positivity)
    refine ⟨δ, hδ, fun s' hs' hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    rcases le_total s s' with h | h
    · have := hδ' s hs s' hs' h (by rw [abs_lt] at hd; linarith)
      linarith
    · have := hδ' s' hs' s hs h (by rw [abs_lt] at hd; linarith)
      rw [abs_sub_comm]; linarith
  have hUeq : ∀ s ∈ Ico 0 T, U s = U₀ s := fun s hs =>
    extendFrom_eq (subset_closure hs) (hcw s hs)
  -- limits at every point of `[0, T]`
  have hlim : ∀ x ∈ Icc 0 T, ∃ y, Tendsto U₀ (𝓝[Ico 0 T] x) (𝓝 y) := by
    intro x hx
    have : (𝓝[Ico 0 T] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hcl ▸ hx)
    refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨map_neBot, fun ε hε => ?_⟩)
    obtain ⟨δ, hδ, hδ'⟩ := abs_drvPoint_sub_le hB hmono hLG (ε := ε / 2) (by positivity)
    refine ⟨U₀ '' (Ico 0 T ∩ ball x (δ / 2)), ?_, ?_⟩
    · exact mem_map.2 (mem_of_superset (inter_mem_nhdsWithin _ (ball_mem_nhds x (by positivity)))
        (subset_preimage_image _ _))
    · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      have hpq : |p - q| < δ := by
        have h1 := mem_ball.1 hp.2
        have h2 := mem_ball.1 hq.2
        rw [Real.dist_eq] at h1 h2
        rw [abs_lt] at h1 h2 ⊢
        constructor <;> linarith
      rw [Real.dist_eq]
      rcases le_total p q with h | h
      · have := hδ' p hp.1 q hq.1 h (by rw [abs_lt] at hpq; linarith)
        rw [abs_sub_comm]; linarith
      · have := hδ' q hq.1 p hp.1 h (by rw [abs_lt] at hpq; linarith)
        linarith
  have hUc : ContinuousOn U (Icc 0 T) := continuousOn_extendFrom (hcl ▸ subset_rfl) hlim
  refine ⟨U, ⟨hB, hB0, fun s hs t ht hst => hmono.monotoneOn hs ht hst,
    fun s hs t ht hst => nonempty_of_ssubset (hmono hs ht hst), hUc, ?_⟩, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := inc_subset_closedBall_drvPoint hB hmono hLG hε
    refine ⟨δ, hδ, fun s hs t ht hst hts => ?_⟩
    rcases eq_or_lt_of_le hst with heq | hlt
    · subst heq
      rintro _ ⟨z, hz, rfl⟩
      exact absurd hz.1 hz.2
    · have hsT : s ∈ Ico 0 T := ⟨hs.1, hlt.trans_le ht.2⟩
      rw [hUeq s hsT]
      exact hδ' s hsT t ⟨hlt, ht.2⟩ hts
  · have h0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
    rw [hUeq 0 h0]
    have hmem := drvPoint_mem hB hmono hLG h0
    have hid : ∀ t ∈ Icc 0 T, inc B 0 t = B t := by
      intro t ht
      have hg0 := ConformalImage.isMapOut_mapOut (hB 0 ⟨le_rfl, hT.le⟩)
      rw [hB0] at hg0
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [hB0] at hz ⊢
        rw [hg0.eqOn isHPHull_empty isMapOut_empty_id ⟨(hB t ht).1 hz.1, notMem_empty z⟩]
        exact hz.1
      · intro hw
        refine ⟨w, ⟨hw, by rw [hB0]; exact notMem_empty w⟩, ?_⟩
        rw [hB0]
        exact hg0.eqOn isHPHull_empty isMapOut_empty_id ⟨(hB t ht).1 hw, notMem_empty w⟩
    have hnorm : ‖(U₀ 0 : ℂ)‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨t, ht, hBt⟩ := hsmall ε hε
      have := closure_minimal (show inc B 0 t ⊆ closedBall 0 ε by
        rw [hid t ⟨ht.1.le, ht.2⟩]; exact hBt) isClosed_closedBall (mem_iInter.1 hmem ⟨t, ht⟩)
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    have := norm_le_zero_iff.1 hnorm
    exact_mod_cast this

end Growing

/-! ### The local growth of the limit chain -/

section Limit

variable {η : ℝ → ℂ} {γ : ℕ → ℝ → ℂ} {S R : ℝ}

/-- The mapping-out functions of the approximating fillings converge locally uniformly. -/
theorem tendstoLocallyUniformlyOn_mapOut (hR : 0 < R) (hη : ContinuousOn η (Icc 0 S))
    (h0 : η 0 = 0) (hηR : ∀ u ∈ Icc 0 S, ‖η u‖ < R) (hγc : ∀ n, ContinuousOn (γ n) (Icc 0 S))
    (hγ0 : ∀ n, γ n 0 = 0) (hγR : ∀ n, ∀ u ∈ Icc 0 S, ‖γ n u‖ < R)
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 S)) {s : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) :
    TendstoLocallyUniformlyOn (fun n => ConformalImage.mapOut (fillH (γ n '' Icc 0 s)))
      (ConformalImage.mapOut (fillH (η '' Icc 0 s))) atTop (H \ fillH (η '' Icc 0 s)) := by
  have hsub : Icc (0 : ℝ) s ⊆ Icc 0 S := Icc_subset_Icc_right hsS
  have hA : ∀ n, IsHPHull (fillH (γ n '' Icc 0 s)) := fun n =>
    isHPHull_fillH_image ((hγc n).mono hsub) hs (hγ0 n)
  have hB : IsHPHull (fillH (η '' Icc 0 s)) := isHPHull_fillH_image (hη.mono hsub) hs h0
  have hAR : ∀ n, fillH (γ n '' Icc 0 s) ⊆ ball 0 R := fun n => by
    refine fillH_subset_ball hR ?_
    rw [(isCompact_image_Icc ((hγc n).mono hsub)).isClosed.closure_eq]
    rintro _ ⟨u, hu, rfl⟩
    exact mem_ball_zero_iff.2 (hγR n u (hsub hu))
  exact tendstoLocallyUniformlyOn_of_kernelConvergesTo_H hA hB hAR
    (fun n => ConformalImage.isMapOut_mapOut (hA n)) (ConformalImage.isMapOut_mapOut hB)
    (kernelConvergesTo_fillH hR (hη.mono hsub) (fun u hu => hηR u (hsub hu))
      (fun n => (hγc n).mono hsub) (fun n u hu => hγR n u (hsub hu)) (hconv.mono hsub))

/-- `g_s^n(γ_n(u)) → g_s(η(u))` at a trace point `η(u)` outside `K_s`. -/
theorem tendsto_mapOut_apply (hR : 0 < R) (hη : ContinuousOn η (Icc 0 S))
    (h0 : η 0 = 0) (hηR : ∀ u ∈ Icc 0 S, ‖η u‖ < R) (hγc : ∀ n, ContinuousOn (γ n) (Icc 0 S))
    (hγ0 : ∀ n, γ n 0 = 0) (hγR : ∀ n, ∀ u ∈ Icc 0 S, ‖γ n u‖ < R)
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 S)) {s u : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S)
    (hu : u ∈ Icc 0 S) (hηu : η u ∈ H \ fillH (η '' Icc 0 s)) :
    Tendsto (fun n => ConformalImage.mapOut (fillH (γ n '' Icc 0 s)) (γ n u)) atTop
      (𝓝 (ConformalImage.mapOut (fillH (η '' Icc 0 s)) (η u))) := by
  have hB : IsHPHull (fillH (η '' Icc 0 s)) :=
    isHPHull_fillH_image (hη.mono (Icc_subset_Icc_right hsS)) hs h0
  have hlim := tendstoLocallyUniformlyOn_mapOut hR hη h0 hηR hγc hγ0 hγR hconv hs hsS
  refine hlim.tendsto_comp
    ((ConformalImage.isMapOut_mapOut hB).1.1.continuousOn.continuousWithinAt hηu) hηu ?_
  have ht : Tendsto (fun n => γ n u) atTop (𝓝 (η u)) := hconv.tendsto_at hu
  exact tendsto_nhdsWithin_iff.2 ⟨ht, ht.eventually (hB.isOpen.mem_nhds hηu)⟩

/-- **The estimate passes to the limit.** Under `SimpleCurveLocalGrowthWith C`, if
`η([s, t]) ⊆ B(η(s), d)` (strictly), the images under `g_s` of the trace points `η(u)`,
`u ∈ (s, t]`, outside `K_s` lie in a closed disc of radius `3 C √(d R)` centred on `ℝ`. -/
theorem exists_forall_norm_mapOut_trace_sub_le {C : ℝ} (hSC : SimpleCurveLocalGrowthWith C)
    (hR : 0 < R) (hη : ContinuousOn η (Icc 0 S)) (h0 : η 0 = 0)
    (hηR : ∀ u ∈ Icc 0 S, ‖η u‖ < R) (hγc : ∀ n, ContinuousOn (γ n) (Icc 0 S))
    (hγi : ∀ n, InjOn (γ n) (Icc 0 S)) (hγ0 : ∀ n, γ n 0 = 0)
    (hγH : ∀ n, MapsTo (γ n) (Ioc 0 S) H) (hγR : ∀ n, ∀ u ∈ Icc 0 S, ‖γ n u‖ < R)
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 S)) {s t d : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htS : t ≤ S) (hd : 0 < d) (hdR : d ≤ R) (hosc : ∀ u ∈ Icc s t, ‖η u - η s‖ < d) :
    ∃ x : ℝ, ∀ u ∈ Ioc s t, η u ∈ H \ fillH (η '' Icc 0 s) →
      ‖ConformalImage.mapOut (fillH (η '' Icc 0 s)) (η u) - x‖ ≤ 3 * (C * √(d * R)) := by
  set ρ := C * √(d * R) with hρ
  set g := ConformalImage.mapOut (fillH (η '' Icc 0 s)) with hg
  set gn := fun n => ConformalImage.mapOut (fillH (γ n '' Icc 0 s)) with hgn
  have hsS : s ≤ S := hst.trans htS
  -- a margin in the oscillation
  obtain ⟨u₁, hu₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hst)
    ((hη.mono (Icc_subset_Icc hs htS)).sub continuousOn_const).norm
  set d₁ := ‖η u₁ - η s‖ with hd₁
  have hd₁d : d₁ < d := hosc u₁ hu₁
  have hεpos : 0 < (d - d₁) / 2 := by linarith
  -- eventually the approximating paths have oscillation `≤ d` on `[s, t]`
  have hev : ∀ᶠ n in atTop, ∃ x : ℝ, ∀ u ∈ Ioc s t, ‖gn n (γ n u) - x‖ ≤ ρ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hconv _ hεpos] with n hn
    refine hSC (γ n) S R (hγc n) (hγi n) (hγ0 n) (hγH n) (fun u hu => (hγR n u hu).le) s t d hs
      hst htS hd hdR fun u hu => ?_
    have hu' : u ∈ Icc 0 S := ⟨hs.trans hu.1, hu.2.trans htS⟩
    have h1 : dist (η u) (γ n u) < (d - d₁) / 2 := hn u hu'
    have h2 : dist (η s) (γ n s) < (d - d₁) / 2 := hn s ⟨hs, hsS⟩
    have h3 : ‖η u - η s‖ ≤ d₁ := isMaxOn_iff.1 hmax u hu
    rw [dist_eq_norm] at h1 h2
    calc ‖γ n u - γ n s‖ = ‖(η u - η s) - (η u - γ n u) + (η s - γ n s)‖ := by ring_nf
      _ ≤ ‖(η u - η s) - (η u - γ n u)‖ + ‖η s - γ n s‖ := norm_add_le _ _
      _ ≤ ‖η u - η s‖ + ‖η u - γ n u‖ + ‖η s - γ n s‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ d := by linarith
  -- pairwise bound and height bound in the limit
  have hlim : ∀ u ∈ Ioc s t, η u ∈ H \ fillH (η '' Icc 0 s) →
      Tendsto (fun n => gn n (γ n u)) atTop (𝓝 (g (η u))) := fun u hu hηu =>
    tendsto_mapOut_apply hR hη h0 hηR hγc hγ0 hγR hconv hs hsS
      ⟨hs.trans hu.1.le, hu.2.trans htS⟩ hηu
  have hpair : ∀ u ∈ Ioc s t, η u ∈ H \ fillH (η '' Icc 0 s) → ∀ u' ∈ Ioc s t,
      η u' ∈ H \ fillH (η '' Icc 0 s) → ‖g (η u) - g (η u')‖ ≤ 2 * ρ := by
    intro u hu hηu u' hu' hηu'
    refine le_of_tendsto ((hlim u hu hηu).sub (hlim u' hu' hηu')).norm ?_
    filter_upwards [hev] with n ⟨x, hx⟩
    calc ‖gn n (γ n u) - gn n (γ n u')‖ = ‖(gn n (γ n u) - x) - (gn n (γ n u') - x)‖ := by
          ring_nf
      _ ≤ ‖gn n (γ n u) - x‖ + ‖gn n (γ n u') - x‖ := norm_sub_le _ _
      _ ≤ 2 * ρ := by linarith [hx u hu, hx u' hu']
  have him : ∀ u ∈ Ioc s t, η u ∈ H \ fillH (η '' Icc 0 s) → |(g (η u)).im| ≤ ρ := by
    intro u hu hηu
    refine le_of_tendsto ((continuous_abs.comp continuous_im).continuousAt.tendsto.comp
      (hlim u hu hηu)) ?_
    filter_upwards [hev] with n ⟨x, hx⟩
    have : (gn n (γ n u) - x).im = (gn n (γ n u)).im := by simp
    calc |(gn n (γ n u)).im| = |(gn n (γ n u) - x).im| := by rw [this]
      _ ≤ ‖gn n (γ n u) - x‖ := abs_im_le_norm _
      _ ≤ ρ := hx u hu
  by_cases hex : ∃ u₀ ∈ Ioc s t, η u₀ ∈ H \ fillH (η '' Icc 0 s)
  · obtain ⟨u₀, hu₀, hηu₀⟩ := hex
    refine ⟨(g (η u₀)).re, fun u hu hηu => ?_⟩
    have h1 := hpair u hu hηu u₀ hu₀ hηu₀
    have h2 := him u₀ hu₀ hηu₀
    have h3 : ‖g (η u₀) - ((g (η u₀)).re : ℂ)‖ = |(g (η u₀)).im| := by
      have : g (η u₀) - ((g (η u₀)).re : ℂ) = ((g (η u₀)).im : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc ‖g (η u) - ((g (η u₀)).re : ℂ)‖
        = ‖(g (η u) - g (η u₀)) + (g (η u₀) - ((g (η u₀)).re : ℂ))‖ := by ring_nf
      _ ≤ ‖g (η u) - g (η u₀)‖ + ‖g (η u₀) - ((g (η u₀)).re : ℂ)‖ := norm_add_le _ _
      _ ≤ 3 * ρ := by linarith
  · push Not at hex
    exact ⟨0, fun u hu hηu => absurd hηu (hex u hu)⟩

/-- From the trace points to the whole increment: if `g_s(η(u)) ∈ B̄(x, ρ)` (`x ∈ ℝ`) for every
trace point `η(u) ∉ K_s`, `u ∈ (s, t]`, then `g_s(K_t \ K_s) ⊆ B̄(x, 2ρ)` (`exists_ray_mem`). -/
theorem norm_mapOut_sub_le_of_trace (hR : 0 < R) (hη : ContinuousOn η (Icc 0 S)) (h0 : η 0 = 0)
    (hηR : ∀ u ∈ Icc 0 S, ‖η u‖ < R) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htS : t ≤ S)
    {x ρ : ℝ} (htr : ∀ u ∈ Ioc s t, η u ∈ H \ fillH (η '' Icc 0 s) →
      ‖ConformalImage.mapOut (fillH (η '' Icc 0 s)) (η u) - x‖ ≤ ρ)
    {z : ℂ} (hz : z ∈ fillH (η '' Icc 0 t) \ fillH (η '' Icc 0 s)) :
    ‖ConformalImage.mapOut (fillH (η '' Icc 0 s)) z - x‖ ≤ 2 * ρ := by
  obtain ⟨u, hu, hηu, τ, hτ, heq⟩ := exists_ray_mem hR hη h0 hηR hs hst htS hz
  have h1 := htr u hu hηu
  rw [heq] at h1
  set w := ConformalImage.mapOut (fillH (η '' Icc 0 s)) z with hw
  have hA : IsHPHull (fillH (η '' Icc 0 s)) :=
    isHPHull_fillH_image (hη.mono (Icc_subset_Icc_right (hst.trans htS))) hs h0
  have hwH : 0 < w.im :=
    (ConformalImage.isMapOut_mapOut hA).1.2.mapsTo ⟨fillH_subset_H _ hz.1, hz.2⟩
  have hre : |(w - x).re| ≤ ρ := by
    have := abs_re_le_norm (w + (τ : ℂ) * I - x)
    have hr : (w + (τ : ℂ) * I - x).re = (w - x).re := by simp
    rw [hr] at this
    linarith
  have him : |(w - x).im| ≤ ρ := by
    have := abs_im_le_norm (w + (τ : ℂ) * I - x)
    have hi : (w + (τ : ℂ) * I - x).im = w.im + τ := by simp
    have hi' : (w - x).im = w.im := by simp
    rw [hi] at this
    rw [hi', abs_of_pos hwH]
    rw [abs_of_nonneg (by linarith)] at this
    linarith
  calc ‖w - x‖ ≤ |(w - x).re| + |(w - x).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * ρ := by linarith

/-- **Uniform local growth of the limit chain**: for every `ε > 0` there is `δ > 0` such that,
for `0 ≤ s ≤ t ≤ S` with `t − s ≤ δ`, the increment `g_s(K_t \ K_s)` lies in a closed disc of
radius `ε` centred on `ℝ`. -/
theorem exists_forall_norm_mapOut_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hSC : SimpleCurveLocalGrowthWith C) (hR : 0 < R) (hη : ContinuousOn η (Icc 0 S))
    (h0 : η 0 = 0) (hηR : ∀ u ∈ Icc 0 S, ‖η u‖ < R) (hγc : ∀ n, ContinuousOn (γ n) (Icc 0 S))
    (hγi : ∀ n, InjOn (γ n) (Icc 0 S)) (hγ0 : ∀ n, γ n 0 = 0)
    (hγH : ∀ n, MapsTo (γ n) (Ioc 0 S) H) (hγR : ∀ n, ∀ u ∈ Icc 0 S, ‖γ n u‖ < R)
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 S)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ S → t - s ≤ δ → ∃ x : ℝ,
      ∀ z ∈ fillH (η '' Icc 0 t) \ fillH (η '' Icc 0 s),
        ‖ConformalImage.mapOut (fillH (η '' Icc 0 s)) z - x‖ ≤ ε := by
  set d := min R (ε ^ 2 / (36 * (C + 1) ^ 2 * R)) with hd
  have hdpos : 0 < d := lt_min hR (by positivity)
  have hdR : d ≤ R := min_le_left _ _
  have hρ : 6 * (C * √(d * R)) ≤ ε := by
    have h1 : d * R ≤ (ε / (6 * (C + 1))) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (min_le_right R (ε ^ 2 / (36 * (C + 1) ^ 2 * R))) hR.le
      rw [← hd] at this
      calc d * R ≤ ε ^ 2 / (36 * (C + 1) ^ 2 * R) * R := this
        _ = (ε / (6 * (C + 1))) ^ 2 := by field_simp; ring
    have h2 : √(d * R) ≤ ε / (6 * (C + 1)) :=
      Real.sqrt_le_iff.2 ⟨by positivity, h1⟩
    have h3 : C * √(d * R) ≤ C * (ε / (6 * (C + 1))) := mul_le_mul_of_nonneg_left h2 hC0
    have h4 : C * (ε / (6 * (C + 1))) ≤ ε / 6 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hη) d hdpos
  refine ⟨δ / 2, by positivity, fun s t hs hst htS hts => ?_⟩
  have hsS : s ≤ S := hst.trans htS
  obtain ⟨x, hx⟩ := exists_forall_norm_mapOut_trace_sub_le hSC hR hη h0 hηR hγc hγi hγ0 hγH hγR
    hconv hs hst htS hdpos hdR fun u hu => by
      have := hδu u ⟨hs.trans hu.1, hu.2.trans htS⟩ s ⟨hs, hsS⟩ (by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2])
      rwa [dist_eq_norm] at this
  refine ⟨x, fun z hz => ?_⟩
  have := norm_mapOut_sub_le_of_trace hR hη h0 hηR hs hst htS hx hz
  linarith

end Limit

/-! ### Assembly -/

section Assembly

/-- Uniformly convergent sequences of continuous paths are uniformly bounded. -/
theorem exists_forall_norm_lt_of_tendstoUniformlyOn {η : ℝ → ℂ} {γ : ℕ → ℝ → ℂ} {S : ℝ}
    (hη : ContinuousOn η (Icc 0 S)) (hγc : ∀ n, ContinuousOn (γ n) (Icc 0 S))
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 S)) :
    ∃ R > 0, (∀ u ∈ Icc 0 S, ‖η u‖ < R) ∧ ∀ n, ∀ u ∈ Icc 0 S, ‖γ n u‖ < R := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn hη
  have hb : ∀ n, ∃ B : ℝ, ∀ u ∈ Icc 0 S, ‖γ n u‖ ≤ B := fun n =>
    (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn (hγc n)
  choose B hB using hb
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hconv 1 one_pos)
  set R := |M| + 1 + 1 + ∑ n ∈ Finset.range N, |B n| with hR
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, |B n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨R, by positivity, fun u hu => ?_, fun n u hu => ?_⟩
  · linarith [hM u hu, le_abs_self M]
  · rcases lt_or_ge n N with hn | hn
    · have := Finset.single_le_sum (f := fun k => |B k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 hn)
      linarith [hB n u hu, le_abs_self (B n), abs_nonneg M]
    · have h1 := hN n hn u hu
      rw [dist_eq_norm] at h1
      have h2 : ‖γ n u‖ ≤ ‖η u‖ + ‖η u - γ n u‖ := by
        calc ‖γ n u‖ = ‖η u - (η u - γ n u)‖ := by ring_nf
          _ ≤ ‖η u‖ + ‖η u - γ n u‖ := norm_sub_le _ _
      linarith [hM u hu, le_abs_self M]

/-- **Loewner's theorem for the fillings of a path with uniform local growth**: if the fillings
`K_t = fill(η[0, t])` of a continuous path `η` (`η 0 = 0`) are strictly increasing and their short
increments `g_s(K_t \ K_s)` lie, uniformly in `s`, in small discs centred on `ℝ`, then `(K_t)` is a
Loewner chain with a continuous driver `W` (`W 0 = 0`) after the capacity time change `σ`. -/
theorem exists_loewner_of_localGrowth {η : ℝ → ℂ} {S : ℝ} (hS : 0 < S)
    (hη : ContinuousOn η (Icc 0 S)) (h0 : η 0 = 0)
    (hmono : StrictMonoOn (fun t => fillH (η '' Icc 0 t)) (Icc 0 S))
    (hLG : ∀ ε > 0, ∃ δ > 0, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ S → t - s ≤ δ → ∃ x : ℝ,
      ∀ z ∈ fillH (η '' Icc 0 t) \ fillH (η '' Icc 0 s),
        ‖ConformalImage.mapOut (fillH (η '' Icc 0 s)) z - x‖ ≤ ε) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧
      ContinuousOn σ (Icc 0 S) ∧
      ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (σ t) = fillH (η '' Icc 0 t) := by
  set B : ℝ → Set ℂ := fun t => fillH (η '' Icc 0 t) with hBdef
  have hB : ∀ t ∈ Icc 0 S, IsHPHull (B t) := fun t ht =>
    isHPHull_fillH_image (hη.mono (Icc_subset_Icc_right ht.2)) ht.1 h0
  have hLG' : ∀ ε > 0, ∃ δ > 0, ∀ s t : ℝ, s ∈ Icc 0 S → t ∈ Icc 0 S → s ≤ t → t - s ≤ δ →
      ∃ x : ℝ, ∀ z ∈ B t \ B s, ‖ConformalImage.mapOut (B s) z - x‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hLG ε hε
    exact ⟨δ, hδ, fun s t hs ht hst hts => hδ' s t hs.1 hst ht.2 hts⟩
  have hsmall : ∀ ε > 0, ∃ t ∈ Ioc 0 S, B t ⊆ closedBall 0 ε := by
    intro ε hε
    have hc0 := (hη 0 ⟨le_rfl, hS.le⟩)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1 hc0 (ε / 2) (by positivity)
    set t := min S (δ / 2) with ht
    have htpos : 0 < t := lt_min hS (by positivity)
    refine ⟨t, ⟨htpos, min_le_left _ _⟩, ?_⟩
    have hsub : fillH (η '' Icc 0 t) ⊆ ball 0 (ε / 2) := by
      refine fillH_subset_ball (by positivity) ?_
      rw [(isCompact_image_Icc
        (hη.mono (Icc_subset_Icc_right (min_le_left _ _)))).isClosed.closure_eq]
      rintro _ ⟨u, hu, rfl⟩
      have hu' : u ∈ Icc 0 S := ⟨hu.1, hu.2.trans (min_le_left _ _)⟩
      have := hδ' hu' (by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
        linarith [hu.2, min_le_right S (δ / 2)])
      rw [h0, dist_zero_right] at this
      exact mem_ball_zero_iff.2 this
    exact hsub.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  obtain ⟨U, hU, hU0⟩ := exists_isContinuouslyGrowing hS hB
    (by simp only [hBdef]; exact fillH_image_Icc_zero h0) hmono hLG' hsmall
  have hl := fun t ht => hU.loewner hS.le (t := t) ht
  refine ⟨ConformalImage.IsContinuouslyGrowing.drv B U S, hU.continuous_drv hS.le, ?_,
    ConformalImage.cap B,
    hU.cap_zero hS.le, hU.strictMonoOn_cap, hU.continuousOn_cap, fun t ht => (hl t ht).2.1⟩
  have := (hl 0 ⟨le_rfl, hS.le⟩).1
  rw [hU.cap_zero hS.le, hU0] at this
  exact this

/-- **[Yua22, Theorem 1.1, (iii) ⇒ (i)] with Loewner's theorem**, conditional on the estimate
for simple paths (`SimpleCurveLocalGrowth`, proved in `YuanCharacterisationSimple.lean`): a
continuous path `η` on `[0, S]` with `η 0 = 0`, strictly increasing fillings, and a uniform
approximation by simple paths `γ_n` (`γ_n 0 = 0`, `γ_n((0, S]) ⊆ ℍ`) generates a Loewner chain
with a continuous driver `W` (`W 0 = 0`) after the capacity time change `σ`. -/
theorem exists_loewner_of_tendstoUniformlyOn (hSC : SimpleCurveLocalGrowth) {η : ℝ → ℂ}
    {S : ℝ} (hS : 0 < S) (hη : ContinuousOn η (Icc 0 S)) (h0 : η 0 = 0)
    (hmono : StrictMonoOn (fun t => fillH (η '' Icc 0 t)) (Icc 0 S)) {γ : ℕ → ℝ → ℂ}
    (hγ : ∀ n, ContinuousOn (γ n) (Icc 0 S) ∧ InjOn (γ n) (Icc 0 S) ∧ γ n 0 = 0 ∧
      MapsTo (γ n) (Ioc 0 S) H)
    (hconv : TendstoUniformlyOn γ η atTop (Icc 0 S)) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧
      ContinuousOn σ (Icc 0 S) ∧
      ∀ t ∈ Icc 0 S, QuantumZipper.fwdHull W (σ t) = fillH (η '' Icc 0 t) := by
  obtain ⟨C, hC0, hSCw⟩ := hSC
  obtain ⟨R, hR, hηR, hγR⟩ :=
    exists_forall_norm_lt_of_tendstoUniformlyOn hη (fun n => (hγ n).1) hconv
  exact exists_loewner_of_localGrowth hS hη h0 hmono fun ε hε =>
    exists_forall_norm_mapOut_sub_le hC0 hSCw hR hη h0 hηR (fun n => (hγ n).1)
      (fun n => (hγ n).2.1) (fun n => (hγ n).2.2.1) (fun n => (hγ n).2.2.2) hγR hconv hε

end Assembly

end YuanCharacterisation

end InteractingSLE
