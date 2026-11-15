/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB10
import InteractingSLE.Spec.Supplement.GW2ScheduleL25
import InteractingSLE.Spec.Zhan.ConstDriftTraceRs
import InteractingSLE.Foundations.SLE.SpaceFilling

/-!
# Lemma GB10, the deterministic part: a trace interval in a simple arc gives a restart without real contacts

Packet PROVE-T14-GW4S. Lemma GB10 (`source/spec/p529-576.md` L629–L635, p. 555), second paragraph of the proof:

> "Suppose a trace interval were contained in a simple arc. Inverse arc parameter makes it a continuous real-valued
> function. It is strictly monotone: a constant interval adds no hull, and a reversal creates a nontrivial return
> interval inside an already traced subarc, which also adds no hull. Choose a rational time `r` inside the interval.
> Strict capacity growth supplies a later point outside the old range `R_r`. The corresponding open set of times
> contains an interior-tip time by Lemma 2.5; choose its physical neighborhood disjoint from `R_r` and from the
> original real boundary. A rational time `a > r` in that neighborhood has a short future which avoids `R_r` by
> separation and avoids the intervening range by strict monotonicity on the arc. No entry into a filled pocket puts
> this own-mapped future in the open half-plane. This contradicts the simultaneous rational-restart assertion."

The "simultaneous rational-restart assertion" is used here in the form that the probabilistic part supplies
(`GB10Proof.lean`): at a rational restart time `q` with an interior tip, every positive-time hull of the shifted
driver `w(q + ·) − w(q)` contains an upper half-neighbourhood of `0` ([RS05, Lemma 7.3] for ordinary `SLE_k`, `k > 4`,
transferred by local absolute continuity). Its consequence "real contacts arbitrarily soon" is the contrapositive of
`exists_notMem_fillH`: a compact set meeting the closed lower half-plane only at `0` fills no half-neighbourhood.

## Main results

* `exists_notMem_fillH`: a compact set meeting `{Im ≤ 0}` at most at `0` misses points of every half-ball in its fill;
* `continuousOn_invFunOn_image`: the inverse of a continuous injective map on a compact set is continuous;
* `IsLoewnerTraceLT.not_image_Icc_subset` (strict hull growth: a later interval is never inside the old range);
* `IsLoewnerTraceLT.injOn_of_image_subset_arc` (the strict monotonicity on the arc);
* `IsLoewnerTraceLT.notMem_fwdHull_of_connected` ("no entry into a filled pocket");
* **`IsLoewnerTraceLT.exists_restart_of_arc`**: the rational restart `q` with interior tip whose short future lies
  in `ℍ \ K_q`;
* **`IsLoewnerTraceLT.false_of_arc_of_halfBall`** and its frozen form **`noSimpleArcInterval_of_halfBall`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace Theorem14

namespace GB10

/-! ### A compact set touching the real line only at `0` fills no half-ball -/

/-- **A compact set meeting the closed lower half-plane at most at `0` fills no half-neighbourhood of `0`**: for
every `ε > 0` some `z ∈ ℍ` with `‖z‖ < ε` is outside `fillH A`. The thin strip `{ε/4 < Re, 0 < Im < h}` avoids `A`
(the part of `A` with `Re ≥ ε/4` is compact and in `ℍ`, hence at positive height), is connected and unbounded, and
reaches into the ball. -/
theorem exists_notMem_fillH {A : Set ℂ} (hA : IsCompact A) (hAR : ∀ z ∈ A, z.im ≤ 0 → z = 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ z ∈ H, ‖z‖ < ε ∧ z ∉ fillH A := by
  set A' := A ∩ {z : ℂ | ε / 4 ≤ z.re} with hA'
  have hA'c : IsCompact A' := hA.inter_right (isClosed_le continuous_const Complex.continuous_re)
  obtain ⟨m, hm, hmA'⟩ : ∃ m > (0 : ℝ), ∀ z ∈ A', m ≤ z.im := by
    rcases A'.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun z hz => ?_⟩
      rw [he] at hz
      exact absurd hz (notMem_empty z)
    · obtain ⟨z₀, hz₀, hmin⟩ := hA'c.exists_isMinOn hne Complex.continuous_im.continuousOn
      refine ⟨z₀.im, ?_, fun z hz => hmin hz⟩
      by_contra hle
      have h0 := hAR z₀ hz₀.1 (not_lt.1 hle)
      have h1 : ε / 4 ≤ z₀.re := hz₀.2
      rw [h0, Complex.zero_re] at h1
      linarith
  set h : ℝ := min m ε / 2 with hh
  have hmε : 0 < min m ε := lt_min hm hε
  have hh0 : 0 < h := by rw [hh]; linarith
  have hhm : h < m := by rw [hh]; linarith [min_le_left m ε]
  have hhε : h < ε := by rw [hh]; linarith [min_le_right m ε]
  set S : Set ℂ := {w : ℂ | ε / 4 < w.re} ∩ {w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < h} with hS
  have hSconv : Convex ℝ S :=
    ((convex_halfSpace_gt (f := fun z : ℂ => z.re) Complex.reLm.isLinear (ε / 4)).inter
      (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).inter
      (convex_halfSpace_lt (f := fun z : ℂ => z.im) Complex.imLm.isLinear h)
  have hSA : S ⊆ H \ A := by
    rintro w ⟨⟨hw1, hw2⟩, hw3⟩
    refine ⟨hw2, fun hwA => ?_⟩
    have := hmA' w ⟨hwA, show ε / 4 ≤ w.re from le_of_lt hw1⟩
    linarith [show w.im < h from hw3]
  have hSunb : ¬ Bornology.IsBounded S := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    set w : ℂ := ⟨|R| + ε / 4 + 1, h / 2⟩ with hw
    have hwS : w ∈ S := ⟨⟨by show ε / 4 < |R| + ε / 4 + 1; linarith [abs_nonneg R],
      by show (0 : ℝ) < h / 2; linarith⟩, by show h / 2 < h; linarith⟩
    have h1 := hR hwS
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h3 : w.re = |R| + ε / 4 + 1 := rfl
    rw [h3, abs_of_pos (by positivity)] at h2
    linarith [le_abs_self R]
  set z : ℂ := ⟨ε / 2, h / 2⟩ with hz
  have hzS : z ∈ S := ⟨⟨by show ε / 4 < ε / 2; linarith, by show (0 : ℝ) < h / 2; linarith⟩,
    by show h / 2 < h; linarith⟩
  refine ⟨z, (hSA hzS).1, ?_, ?_⟩
  · have h1 := Complex.norm_le_abs_re_add_abs_im z
    have h2 : |z.re| = ε / 2 := abs_of_pos (show (0 : ℝ) < ε / 2 by linarith)
    have h3 : |z.im| = h / 2 := abs_of_pos (show (0 : ℝ) < h / 2 by linarith)
    rw [h2, h3] at h1
    linarith
  · rintro ⟨-, hzA⟩
    rw [hA.isClosed.closure_eq] at hzA
    rcases hzA with hzA | hzA
    · exact (hSA hzS).2 hzA
    · exact hSunb (hzA.subset (hSconv.isPreconnected.subset_connectedComponentIn hzS hSA))

/-! ### The inverse arc parameter -/

/-- **The inverse of a continuous injective map on a compact set is continuous** on the image (a closed subset of
the compact domain has compact, hence closed, image). -/
theorem continuousOn_invFunOn_image {K : Set ℝ} (hK : IsCompact K) {f : ℝ → ℂ} (hf : ContinuousOn f K)
    (hinj : InjOn f K) : ContinuousOn (invFunOn f K) (f '' K) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨f '' (t ∩ K), ((hK.inter_left ht).image_of_continuousOn (hf.mono inter_subset_right)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hyt, x, hx, rfl⟩
    have hgx : invFunOn f K (f x) = x := hinj.leftInvOn_invFunOn hx
    refine ⟨⟨x, ⟨?_, hx⟩, rfl⟩, x, hx, rfl⟩
    rw [mem_preimage, hgx] at hyt
    exact hyt
  · rintro ⟨⟨x, hx, rfl⟩, -⟩
    have hgx : invFunOn f K (f x) = x := hinj.leftInvOn_invFunOn hx.2
    exact ⟨by rw [mem_preimage, hgx]; exact hx.1, x, hx.2, rfl⟩

/-! ### Strict growth, the arc order and filled pockets -/

section Trace

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

/-- **Strict hull growth**: a later time interval is never contained in the old range (otherwise the two ranges, and
hence the two hulls, would coincide, contrary to `fwdHull_ssubset`). -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.not_image_Icc_subset (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') (hs'T : s' < T) :
    ¬ η '' Icc s s' ⊆ η '' Icc 0 s := by
  intro hsub
  have himg : η '' Icc 0 s' = η '' Icc 0 s := by
    refine Subset.antisymm ?_ (image_mono (Icc_subset_Icc_right hss'.le))
    rintro _ ⟨r, hr, rfl⟩
    rcases le_total r s with hrs | hrs
    · exact ⟨r, ⟨hr.1, hrs⟩, rfl⟩
    · exact hsub ⟨r, ⟨hrs, hr.2⟩, rfl⟩
  have hss := QuantumZipper.RS.fwdHull_ssubset hW hW0 hs hss'
  rw [hη.2.2 s hs (hss'.trans hs'T), hη.2.2 s' (hs.trans hss'.le) hs'T, himg] at hss
  exact (ssubset_irrefl _) hss

/-- **The trace is injective on a time interval contained in a simple arc** (GB10's proof: "Inverse arc parameter
makes it a continuous real-valued function. It is strictly monotone: a constant interval adds no hull, and a reversal
creates a nontrivial return interval inside an already traced subarc, which also adds no hull"). If `φ = α⁻¹ ∘ η`
took one value at `s₁ < s₂`, its extreme values on `[s₁, s₂]` are taken before `s₂`, at times `≤ t < s₂`; then
`φ([t, s₂]) ⊆ φ([s₁, t])` by the intermediate value theorem, i.e. `η([t, s₂]) ⊆ η([0, t])`, contrary to strict
growth. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.injOn_of_image_subset_arc (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a' b' : ℝ} (ha' : 0 ≤ a') (hb'T : b' < T) {α : ℝ → ℂ}
    (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1)) (hsub : η '' Icc a' b' ⊆ α '' Icc 0 1) :
    InjOn η (Icc a' b') := by
  set φ : ℝ → ℝ := fun s => invFunOn α (Icc 0 1) (η s) with hφ
  have hηc : ContinuousOn η (Icc a' b') := hη.2.1.mono fun s hs => ⟨ha'.trans hs.1, hs.2.trans_lt hb'T⟩
  have hφc : ContinuousOn φ (Icc a' b') :=
    (continuousOn_invFunOn_image isCompact_Icc hαc hαi).comp hηc fun s hs => hsub ⟨s, hs, rfl⟩
  have hαφ : ∀ s ∈ Icc a' b', α (φ s) = η s := fun s hs => invFunOn_eq (hsub ⟨s, hs, rfl⟩)
  have key : ∀ s₁ ∈ Icc a' b', ∀ s₂ ∈ Icc a' b', s₁ < s₂ → η s₁ = η s₂ → False := by
    intro s₁ hs₁ s₂ hs₂ hlt heq
    have hφeq : φ s₁ = φ s₂ := by simp only [hφ, heq]
    have hJ : Icc s₁ s₂ ⊆ Icc a' b' := Icc_subset_Icc hs₁.1 hs₂.2
    have hne : (Icc s₁ s₂).Nonempty := nonempty_Icc.2 hlt.le
    obtain ⟨sM, hsM, hMax⟩ := isCompact_Icc.exists_isMaxOn hne (hφc.mono hJ)
    obtain ⟨sm, hsm, hMin⟩ := isCompact_Icc.exists_isMinOn hne (hφc.mono hJ)
    -- move an extreme time at `s₂` back to `s₁`
    have hback : ∀ s ∈ Icc s₁ s₂, ∃ s' ∈ Ico s₁ s₂, φ s' = φ s := by
      intro s hs
      rcases eq_or_lt_of_le hs.2 with h | h
      · exact ⟨s₁, ⟨le_rfl, hlt⟩, by rw [h, hφeq]⟩
      · exact ⟨s, ⟨hs.1, h⟩, rfl⟩
    obtain ⟨sM', hsM', hφM⟩ := hback sM hsM
    obtain ⟨sm', hsm', hφm⟩ := hback sm hsm
    set t := max sM' sm' with ht
    have ht1 : s₁ ≤ t := le_trans hsM'.1 (le_max_left _ _)
    have ht2 : t < s₂ := max_lt hsM'.2 hsm'.2
    have hsub2 : η '' Icc t s₂ ⊆ η '' Icc 0 t := by
      rintro _ ⟨s, hs, rfl⟩
      have hsJ : s ∈ Icc s₁ s₂ := ⟨ht1.trans hs.1, hs.2⟩
      have hval : φ s ∈ Icc (φ sm') (φ sM') := by
        rw [hφm, hφM]
        exact ⟨hMin hsJ, hMax hsJ⟩
      have hpre : IsPreconnected (φ '' Icc s₁ t) :=
        isPreconnected_Icc.image φ (hφc.mono (Icc_subset_Icc hs₁.1 (ht2.le.trans hs₂.2)))
      obtain ⟨s'', hs'', hs''eq⟩ := hpre.Icc_subset ⟨sm', ⟨hsm'.1, le_max_right _ _⟩, rfl⟩
        ⟨sM', ⟨hsM'.1, le_max_left _ _⟩, rfl⟩ hval
      refine ⟨s'', ⟨ha'.trans (hs₁.1.trans hs''.1), hs''.2⟩, ?_⟩
      have h1 : s'' ∈ Icc a' b' := ⟨hs₁.1.trans hs''.1, hs''.2.trans (ht2.le.trans hs₂.2)⟩
      rw [← hαφ s'' h1, hs''eq, hαφ s (hJ hsJ)]
    exact hη.not_image_Icc_subset hW hW0 (ha'.trans (hs₁.1.trans ht1)) ht2 (hs₂.2.trans_lt hb'T) hsub2
  intro s₁ hs₁ s₂ hs₂ heq
  rcases lt_trichotomy s₁ s₂ with h | h | h
  · exact (key s₁ hs₁ s₂ hs₂ h heq).elim
  · exact h
  · exact (key s₂ hs₂ s₁ hs₁ h heq.symm).elim

/-- **No entry into a filled pocket**: if after time `q ≥ 0` the trace stays, on `(q, q + δ]`, in `ℍ` and off its old
range `η([0, q])`, then it stays off the hull `K_q`. All these points lie in one component of `ℍ \ η([0, q])`; were
it bounded, the range up to `q + δ` would add nothing to the fill, contrary to strict growth. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.notMem_fwdHull_of_connected (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ) (hqT : q + δ < T)
    (hgood : ∀ u ∈ Ioc (0 : ℝ) δ, η (q + u) ∈ H ∧ η (q + u) ∉ η '' Icc 0 q) :
    ∀ u ∈ Ioc (0 : ℝ) δ, η (q + u) ∉ fwdHull W q := by
  set A := η '' Icc 0 q with hAdef
  set S := η '' Ioc q (q + δ) with hSdef
  have hAc : IsCompact A := hη.isCompact_image (by linarith)
  have hSA : S ⊆ H \ A := by
    rintro _ ⟨s, hs, rfl⟩
    have h := hgood (s - q) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [add_sub_cancel] at h
    exact h
  have hSc : IsPreconnected S :=
    isPreconnected_Ioc.image η (hη.2.1.mono fun s hs => ⟨hq.trans hs.1.le, hs.2.trans_lt hqT⟩)
  intro u₀ hu₀ hmem
  have hz₀S : η (q + u₀) ∈ S := ⟨q + u₀, ⟨by linarith [hu₀.1], by linarith [hu₀.2]⟩, rfl⟩
  rw [hη.2.2 q hq (by linarith)] at hmem
  change η (q + u₀) ∈ fillH A at hmem
  have hbdd : Bornology.IsBounded (connectedComponentIn (H \ closure A) (η (q + u₀))) := by
    rcases hmem.2 with h | h
    · rw [hAc.isClosed.closure_eq] at h
      exact absurd h (hSA hz₀S).2
    · exact h
  rw [hAc.isClosed.closure_eq] at hbdd
  have hSC := hSc.subset_connectedComponentIn hz₀S hSA
  -- the fill does not grow
  have hfill : fwdHull W (q + δ) ⊆ fwdHull W q := by
    have hAS : η '' Icc 0 (q + δ) = A ∪ S := by
      rw [hAdef, hSdef, ← image_union, Icc_union_Ioc_eq_Icc hq (by linarith)]
    have hASc : IsCompact (A ∪ S) := by rw [← hAS]; exact hη.isCompact_image hqT
    rw [hη.2.2 (q + δ) (by linarith) hqT, hη.2.2 q hq (by linarith), hAS]
    intro z hz
    by_contra hzA
    have hzH : z ∈ H := hz.1
    have hzA' : z ∉ A := fun h => hzA ⟨hzH, Or.inl (subset_closure h)⟩
    have hunb : ¬ Bornology.IsBounded (connectedComponentIn (H \ A) z) := by
      intro hb
      exact hzA ⟨hzH, Or.inr (by rw [hAc.isClosed.closure_eq]; exact hb)⟩
    set Cz := connectedComponentIn (H \ A) z with hCz
    have hCzS : Disjoint Cz S := by
      rw [Set.disjoint_left]
      intro w hwC hwS
      apply hunb
      rw [hCz, connectedComponentIn_eq hwC, ← connectedComponentIn_eq (hSC hwS)]
      exact hbdd
    have hCzsub : Cz ⊆ H \ closure (A ∪ S) := by
      rw [hASc.isClosed.closure_eq]
      intro w hw
      have hw' := connectedComponentIn_subset (H \ A) z hw
      exact ⟨hw'.1, fun h => h.elim hw'.2 (Set.disjoint_left.1 hCzS hw)⟩
    have hzC : z ∈ Cz := mem_connectedComponentIn ⟨hzH, hzA'⟩
    rcases hz.2 with h | h
    · exact (hCzsub hzC).2 h
    · exact hunb (h.subset (isPreconnected_connectedComponentIn.subset_connectedComponentIn hzC hCzsub))
  exact (ssubset_irrefl _) ((QuantumZipper.RS.fwdHull_ssubset hW hW0 hq (by linarith)).trans_subset hfill)

/-- **The rational restart** (GB10's proof): if `η([a', b'])` lies in a simple arc, `0 ≤ a' < b' < T`, there are a
rational `q ∈ (a', b')` with interior tip `η(q) ∈ ℍ` and `δ > 0` such that `η(q + u) ∈ ℍ \ K_q` for `u ∈ (0, δ]`.
With `r = (a' + b')/2`: strict growth gives `s₀ ∈ (r, b']` off `η([0, r])`; times just before `s₀` stay off it, and
by Lemma 2.5 one of them, `s₁`, has `η(s₁) ∈ ℍ`; a rational `q` just before `s₁` then has a short future in `ℍ`, off
`η([0, r])` (separation), off `η([r, q])` (injectivity on the arc), hence off `K_q` (no filled pocket). -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.exists_restart_of_arc (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a' b' : ℝ} (ha' : 0 ≤ a') (hab : a' < b') (hbT : b' < T)
    {α : ℝ → ℂ} (hαc : ContinuousOn α (Icc 0 1)) (hαi : InjOn α (Icc 0 1))
    (hsub : η '' Icc a' b' ⊆ α '' Icc 0 1) :
    ∃ q : ℚ, a' < q ∧ (q : ℝ) < b' ∧ η q ∈ H ∧ ∃ δ > (0 : ℝ), (q : ℝ) + δ < T ∧
      ∀ u ∈ Ioc (0 : ℝ) δ, η (q + u) ∈ H \ fwdHull W q := by
  set r := (a' + b') / 2 with hr
  have hr1 : a' < r := by rw [hr]; linarith
  have hr2 : r < b' := by rw [hr]; linarith
  have hr0 : 0 ≤ r := by linarith
  have hcont : ∀ s, 0 < s → s < T → ContinuousAt η s := fun s hs hsT =>
    hη.2.1.continuousAt (Ico_mem_nhds hs hsT)
  have hKr : IsCompact (η '' Icc 0 r) := hη.isCompact_image (hr2.trans hbT)
  -- a later point off the old range
  obtain ⟨s₀, hs₀, hs₀n⟩ : ∃ s₀ ∈ Icc r b', η s₀ ∉ η '' Icc 0 r := by
    by_contra hcon
    push Not at hcon
    exact hη.not_image_Icc_subset hW hW0 hr0 hr2 hbT (by rintro _ ⟨s, hs, rfl⟩; exact hcon s hs)
  have hs₀r : r < s₀ := lt_of_le_of_ne hs₀.1 fun h => hs₀n ⟨r, ⟨hr0, le_rfl⟩, by rw [h]⟩
  have hO1 : (η '' Icc 0 r)ᶜ ∈ 𝓝 (η s₀) := hKr.isClosed.isOpen_compl.mem_nhds hs₀n
  obtain ⟨θ, hθ, hθ'⟩ := Metric.eventually_nhds_iff.1
    ((hcont s₀ (by linarith) (hs₀.2.trans_lt hbT)).eventually hO1)
  set c := max r (s₀ - θ) with hc
  have hcs₀ : c < s₀ := max_lt hs₀r (by linarith)
  -- Lemma 2.5: an interior tip just before `s₀`
  obtain ⟨s₁, hs₁, hs₁H⟩ : ∃ s₁ ∈ Ioo c s₀, η s₁ ∈ H := by
    by_contra hcon
    push Not at hcon
    have hnull := hη.volume_setOf_notMem_H hW hW0
    have hsub' : Ioo c s₀ ⊆ {t | t ∈ Ico 0 T ∧ η t ∉ H} := fun s hs =>
      ⟨⟨by linarith [le_max_left r (s₀ - θ), hs.1], by linarith [hs.2, hs₀.2]⟩, hcon s hs⟩
    have h0 := measure_mono_null hsub' hnull
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
    linarith
  have hs₁r : r < s₁ := lt_of_le_of_lt (le_max_left _ _) hs₁.1
  have hs₁n : η s₁ ∉ η '' Icc 0 r := by
    refine hθ' ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right r (s₀ - θ), hs₁.1, hs₁.2]
  have hs₁T : s₁ < T := by linarith [hs₁.2, hs₀.2]
  have hO2 : (η '' Icc 0 r)ᶜ ∩ H ∈ 𝓝 (η s₁) :=
    Filter.inter_mem (hKr.isClosed.isOpen_compl.mem_nhds hs₁n) (QuantumZipper.isOpen_H.mem_nhds hs₁H)
  obtain ⟨θ₁, hθ₁, hθ₁'⟩ := Metric.eventually_nhds_iff.1
    ((hcont s₁ (by linarith) hs₁T).eventually hO2)
  -- the rational restart
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max r (s₁ - θ₁) < s₁ from max_lt hs₁r (by linarith))
  have hqr : r < q := lt_of_le_of_lt (le_max_left _ _) hq1
  have hs₁b : s₁ < b' := by linarith [hs₁.2, hs₀.2]
  set e := min (s₁ + θ₁) b' with he
  have hqe : (q : ℝ) < e := lt_min (by linarith) (hq2.trans hs₁b)
  set δ := (e - q) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hqδe : (q : ℝ) + δ < e := by rw [hδ]; linarith
  have hqδb : (q : ℝ) + δ < b' := lt_of_lt_of_le hqδe (min_le_right _ _)
  have hqδs : (q : ℝ) + δ < s₁ + θ₁ := lt_of_lt_of_le hqδe (min_le_left _ _)
  have hinj := hη.injOn_of_image_subset_arc hW hW0 ha' hbT hαc hαi hsub
  have hnear : ∀ s, (q : ℝ) ≤ s → s ≤ q + δ → η s ∈ (η '' Icc 0 r)ᶜ ∩ H := by
    intro s hs1 hs2
    refine hθ₁' ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right r (s₁ - θ₁)]
  have hgood : ∀ u ∈ Ioc (0 : ℝ) δ, η (q + u) ∈ H ∧ η (q + u) ∉ η '' Icc 0 q := by
    intro u hu
    have hn := hnear (q + u) (by linarith [hu.1]) (by linarith [hu.2])
    refine ⟨hn.2, ?_⟩
    rintro ⟨s, hs, hseq⟩
    rcases le_total s r with hsr | hsr
    · exact hn.1 ⟨s, ⟨hs.1, hsr⟩, hseq⟩
    · have h1 : s ∈ Icc a' b' := ⟨by linarith, by linarith [hs.2]⟩
      have h2 : (q : ℝ) + u ∈ Icc a' b' := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have := hinj h1 h2 hseq
      linarith [hs.2, hu.1]
  have hq0 : (0 : ℝ) ≤ q := by linarith
  have hnot := hη.notMem_fwdHull_of_connected hW hW0 hq0 hδ0 (hqδb.trans hbT) hgood
  refine ⟨q, by linarith, by linarith, (hnear q le_rfl (by linarith)).2, δ, hδ0, hqδb.trans hbT,
    fun u hu => ⟨(hgood u hu).1, hnot u hu⟩⟩

/-- **GB10's contradiction** (deterministic): a trace interval `η([a', b'])`, `0 ≤ a' < b' < T`, cannot lie in a
compact simple arc if at every rational restart `q ∈ (a', b')` with interior tip every positive-time hull of the
shifted driver contains a half-neighbourhood of `0` (before the horizon). At the restart of `exists_restart_of_arc`
the shifted tips `γ_q(u)`, `u ∈ (0, δ]`, are in `ℍ`: `F̄_q(γ_q(u)) = η(q + u) ∈ ℍ \ K_q`, while `F̄_q` maps real
points outside `ℍ \ K_q` (`IsLoewnerTraceLT.exists_extension`). So the shifted trace touches `{Im ≤ 0}` only at `0`
on `[0, δ]` and its fill contains no half-ball (`exists_notMem_fillH`). -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.false_of_arc_of_halfBall (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a' b' : ℝ} (ha' : 0 ≤ a') (hab : a' < b') (hbT : b' < T)
    {A : Set ℂ} (hA : IsSimpleArc A) (hsub : η '' Icc a' b' ⊆ A)
    (hhalf : ∀ q : ℚ, a' < q → (q : ℝ) < b' → η q ∈ H → ∀ t : ℝ, 0 < t → (q : ℝ) + t < T →
      HullContainsHalfBall (shiftDrive W q) t) : False := by
  obtain ⟨α, hαc, hαi, rfl⟩ := hA
  obtain ⟨q, hq1, hq2, hqH, δ, hδ, hqδT, hgood⟩ := hη.exists_restart_of_arc hW hW0 ha' hab hbT hαc hαi hsub
  have hq0 : (0 : ℝ) ≤ q := by linarith
  obtain ⟨hsh, hfib⟩ := hη.isLoewnerTraceLT_shift hW hW0 hq0
  have hV := QuantumZipper.RS.continuous_shiftDrive hW (q : ℝ)
  have hV0 : shiftDrive W q 0 = 0 := QuantumZipper.RS.shiftDrive_zero W q
  have hδT : δ < T - q := by linarith
  obtain ⟨F, hFeq, hFc, hFreal⟩ := hη.exists_extension hW hW0 hq0 (by linarith)
  set γ := loewnerTip (shiftDrive W q) with hγ
  have hγH : ∀ u ∈ Ioc (0 : ℝ) δ, γ u ∈ H := by
    intro u hu
    have huT : u < T - q := lt_of_le_of_lt hu.2 hδT
    have him : 0 ≤ (γ u).im := hsh.im_nonneg hV hV0 hu.1.le huT
    rcases lt_or_eq_of_le him with h | h
    · exact h
    · exfalso
      have hbar : γ u ∈ Hbar := him
      have hlim : Tendsto (fwdMapInv W q) (𝓝[H] (γ u)) (𝓝 (F (γ u))) :=
        ((hFc (γ u) hbar).mono H_subset_Hbar).congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)
      have hext : extendFrom H (fwdMapInv W q) (γ u) = F (γ u) :=
        extendFrom_eq (by rw [closure_H]; exact hbar) hlim
      have h1 := hfib u hu.1.le huT
      rw [hext] at h1
      exact hFreal (γ u) h.symm (h1 ▸ hgood u hu)
  have hAc : IsCompact (γ '' Icc 0 δ) := hsh.isCompact_image hδT
  have hAR : ∀ z ∈ γ '' Icc 0 δ, z.im ≤ 0 → z = 0 := by
    rintro _ ⟨u, hu, rfl⟩ hz
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; exact hsh.1
    · exact absurd (hγH u ⟨h, hu.2⟩) (not_lt.2 hz)
  obtain ⟨ε, hε, hball⟩ := hhalf q hq1 hq2 hqH δ hδ hqδT
  obtain ⟨z, hzH, hzε, hzn⟩ := exists_notMem_fillH hAc hAR hε
  have hK := hsh.2.2 δ hδ.le hδT
  exact hzn (hK ▸ hball z hzH hzε)

end Trace

/-! ### The frozen form -/

/-- **GB10's pathwise conclusion from the rational-restart half-ball property** (deterministic, frozen form). Let `γ`
be a generating trace of `w` before `ζ` (`w` continuous before `ζ`, `w 0 = 0`). Suppose that at every positive
rational time `q < ζ` with interior tip `γ(q) ∈ ℍ`, the shifted driver `w(q + ·) − w(q)` has hulls containing a
half-neighbourhood of `0` at all small positive times. Then no nontrivial time interval before `ζ` is mapped into a
compact simple arc. -/
theorem noSimpleArcInterval_of_halfBall {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ζ γ) (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (hhalf : ∀ q : ℚ, 0 < (q : ℝ) → (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ → γ (q : ℝ).toNNReal ∈ H →
      ∃ t₁ > (0 : ℝ), ∀ t ∈ Ioo (0 : ℝ) t₁,
        HullContainsHalfBall (fun r : ℝ => Sec7.shiftNN w (q : ℝ).toNNReal r.toNNReal) t) :
    NoSimpleArcInterval γ ζ := by
  intro a b hab hbζ A hA hsub
  obtain ⟨t₂, hbt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hbζ
  have hη := hγ.isLoewnerTraceLT ht₂ζ
  have hW := continuous_frozenDrive_of_lt hwc ht₂ζ
  have ht₂0 : (0 : ℝ) ≤ t₂ := le_trans b.coe_nonneg hbt₂.le
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  refine hη.false_of_arc_of_halfBall hW hW0 a.coe_nonneg hab' hbt₂ hA ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    refine hsub ⟨s.toNNReal, ⟨?_, ?_⟩, rfl⟩
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (a.coe_nonneg.trans hs.1)]; exact hs.1
    · exact Real.toNNReal_le_iff_le_coe.2 hs.2
  · intro q hq1 hq2 hqH t ht hqt
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt a.coe_nonneg hq1
    have hqζ : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hbζ
      exact Real.toNNReal_le_iff_le_coe.2 hq2.le
    obtain ⟨t₁, ht₁, hball⟩ := hhalf q hq0 hqζ hqH
    set t' := min t (t₁ / 2) with ht'
    have ht'0 : 0 < t' := lt_min ht (by linarith)
    have ht't : t' ≤ t := min_le_left _ _
    have ht't₁ : t' < t₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hqN : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0.le
    have hK : fwdHull (fun r : ℝ => Sec7.shiftNN w (q : ℝ).toNNReal r.toNNReal) t' =
        fwdHull (shiftDrive (frozenDrive w t₂) q) t' := by
      refine fwdHull_eq_of_eqOn ht'0.le (t₂ := t₂ - q) (by linarith) fun r hr => ?_
      have hr' : r ∈ Icc (0 : ℝ) (t₂ - (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) := by rw [hqN]; exact hr
      have h := Zhan.shiftDrive_frozenDrive_eq (w := w) hr'
      rw [hqN] at h
      exact h.symm
    have h1 := hball t' ⟨ht'0, ht't₁⟩
    obtain ⟨ε, hε, hε'⟩ := h1
    exact HullContainsHalfBall.mono ⟨ε, hε, fun z hz hzε => hK ▸ hε' z hz hzε⟩ ht't

end GB10

end Theorem14

end InteractingSLE
