/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideReflect

/-!
# Aux. lemma 37's side germ: the unswallowed collar band and the boundary extension on it

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L118–L127, p. 199:
"The compact arc `J = αᵢ([v₁, v₂])` is disjoint from `R_r`, is contained in `R_{T_v}`, and never loses its incident
`C`-side collar to new range, because the new range avoids `C`").

* `rect a b δ`: the open rectangle `{a < Re < b, 0 < Im < δ}` in a chart, with its closure facts;
* **`exists_band_cf`**: at a rational witness, the chart band over the arc values `f([u(s)/2, v₂])` of small height
  maps under the chart inverse off the counterflow hull at `s` and off the walls (the collar argument of
  `Aux37Frame.collar_of_band`, keeping the band itself);
* **`exists_ext_rect`**: on a rectangle of that band whose bottom edge lands at arc points visited by a time `t ≤ s`,
  the counterflow map `g_t ∘ m ∘ ℓ` extends continuously and injectively to the closed rectangle's landing image
  (`exists_ext`), and is conformal with real boundary values on every upper half-disc of the rectangle
  (`isRealBoundaryConformal_ext`).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.WangWu (negInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O Aux37Frame

/-! ### Rectangles in a chart -/

section Rect

/-- The open rectangle `{a < Re < b, 0 < Im < δ}`. -/
def rect (a b δ : ℝ) : Set ℂ := {w : ℂ | 0 < w.im ∧ w.im < δ ∧ w.re ∈ Ioo a b}

variable {a b δ : ℝ}

theorem rect_subset_H : rect a b δ ⊆ H := fun _ hw => hw.1

theorem convex_rect : Convex ℝ (rect a b δ) := by
  have h1 : Convex ℝ {w : ℂ | 0 < w.im} := convex_halfSpace_gt (f := Complex.im) Complex.imLm.isLinear 0
  have h2 : Convex ℝ {w : ℂ | w.im < δ} := convex_halfSpace_lt (f := Complex.im) Complex.imLm.isLinear δ
  have h3 : Convex ℝ {w : ℂ | w.re ∈ Ioo a b} :=
    (convex_Ioo a b).is_linear_preimage Complex.reLm.isLinear
  exact h1.inter (h2.inter h3)

/-- The closed rectangle containing the closure. -/
def crect (a b δ : ℝ) : Set ℂ := {w : ℂ | 0 ≤ w.im ∧ w.im ≤ δ ∧ w.re ∈ Icc a b}

theorem isClosed_crect : IsClosed (crect a b δ) :=
  (isClosed_le continuous_const Complex.continuous_im).inter
    ((isClosed_le Complex.continuous_im continuous_const).inter (isClosed_Icc.preimage Complex.continuous_re))

theorem closure_rect_subset : closure (rect a b δ) ⊆ crect a b δ :=
  isClosed_crect.closure_subset_iff.2 fun _ hw => ⟨hw.1.le, hw.2.1.le, Ioo_subset_Icc_self hw.2.2⟩

theorem crect_subset_Hbar : crect a b δ ⊆ Hbar := fun _ hw => hw.1

theorem isCompact_closure_rect : IsCompact (closure (rect a b δ)) := by
  refine (Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_)
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2 ⟨|a| + |b| + |δ|, ?_⟩
  intro w hw
  have hw' := closure_rect_subset hw
  rw [mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
  have h1 : |w.re| ≤ |a| + |b| := by
    rw [abs_le]; constructor <;> linarith [hw'.2.2.1, hw'.2.2.2, abs_nonneg a, abs_nonneg b, neg_abs_le a,
      le_abs_self b]
  have h2 : |w.im| ≤ |δ| := by
    rw [abs_of_nonneg hw'.1]; exact hw'.2.1.trans (le_abs_self δ)
  linarith

/-- The upper half-disc around a bottom point of the rectangle lies in it, and its closure in the closure. -/
theorem ball_subset_rect {ξ ρ : ℝ} (hρa : ρ ≤ ξ - a) (hρb : ρ ≤ b - ξ) (hρδ : ρ ≤ δ) :
    H ∩ ball (ξ : ℂ) ρ ⊆ rect a b δ ∧ Hbar ∩ ball (ξ : ℂ) ρ ⊆ closure (rect a b δ) := by
  have key : ∀ w ∈ ball (ξ : ℂ) ρ, w.re ∈ Ioo a b ∧ w.im < δ := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have h1 := (Complex.abs_re_le_norm (w - ξ)).trans_lt hw
    have h2 := (Complex.abs_im_le_norm (w - ξ)).trans_lt hw
    rw [sub_re, ofReal_re, abs_lt] at h1
    rw [sub_im, ofReal_im, sub_zero, abs_lt] at h2
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨fun w hw => ⟨hw.1, (key w hw.2).2, (key w hw.2).1⟩, fun w hw => ?_⟩
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ w.im from hw.1) with h0 | hpos
  · -- a bottom point: the limit of `w + i t`
    have hb : ball (ξ : ℂ) ρ ∈ 𝓝 w := isOpen_ball.mem_nhds hw.2
    have ht : Tendsto (fun t : ℝ => w + (t : ℂ) * I) (𝓝[>] 0) (𝓝 w) := by
      have : Tendsto (fun t : ℝ => w + (t : ℂ) * I) (𝓝 0) (𝓝 (w + ((0 : ℝ) : ℂ) * I)) :=
        (continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [ht hb, self_mem_nhdsWithin] with t htb ht0
    have hk := key _ htb
    refine ⟨?_, hk.2, hk.1⟩
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero, ← h0, zero_add]
    exact ht0
  · exact subset_closure ⟨hpos, (key w hw.2).2, (key w hw.2).1⟩

/-- A bottom-edge point lies in the closure of the rectangle. -/
theorem ofReal_mem_closure_rect (hab : a < b) (hδ : 0 < δ) {q : ℝ} (hq : q ∈ Icc a b) :
    (q : ℂ) ∈ closure (rect a b δ) := by
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  -- move slightly inside, then down
  set m : ℝ := (a + b) / 2 with hmdef
  have ht : Tendsto (fun s : ℝ => ((q + s * (m - q) : ℝ) : ℂ) + ((s * δ / 2 : ℝ) : ℂ) * I) (𝓝[>] 0)
      (𝓝 (q : ℂ)) := by
    have hc : Continuous fun s : ℝ => ((q + s * (m - q) : ℝ) : ℂ) + ((s * δ / 2 : ℝ) : ℂ) * I := by fun_prop
    have := hc.tendsto 0
    simp only [zero_mul, add_zero, zero_div, Complex.ofReal_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with s hs
  refine ⟨?_, ?_, ?_⟩
  · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add]
    have := hs.1; positivity
  · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add]
    have := hs.2; nlinarith
  · simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero, zero_mul, add_zero]
    have h1 := hs.1; have h2 := hs.2
    constructor
    · rcases eq_or_lt_of_le hq.1 with he | hlt
      · rw [← he]; nlinarith [hm.1]
      · nlinarith [hm.1, hm.2, hq.2]
    · rcases eq_or_lt_of_le hq.2 with he | hlt
      · rw [he]; nlinarith [hm.2]
      · nlinarith [hm.1, hm.2, hq.1]

/-- A closed rectangle whose base avoids `0` avoids `0`. -/
theorem ne_zero_of_mem_closure_rect (h : 0 < a ∨ b < 0) {q : ℂ} (hq : q ∈ closure (rect a b δ)) : q ≠ 0 := by
  intro h0
  have hq' : q.re ∈ Icc a b := (closure_rect_subset hq).2.2
  rw [h0, zero_re] at hq'
  rcases h with h | h
  · linarith [hq'.1]
  · linarith [hq'.2]

end Rect

/-! ### The visit data of an arc at a witness, and the collar band -/

section Band

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β A : ℝ → ℂ} {τ σ : ℝ}

/-- **The visit data of an arc at a witness** (pocket-shape free): the counterflow is a continuous Loewner trace from
`0` avoiding `C` on `[r₀, s₀]` (`0 ≤ r₀ < s₀`); for arc parameters `0 < a₀ < v < v₂ < 1` the arc points over
`[a₀, v₂]` are unvisited at `r₀` (in `D_{r₀}`), `A(a₀)` is unvisited at `s₀`, the points over `[v, v₂]` are visited at
`s₀`, and visits on `[a₀, v₂]` are in reverse order (a visited point makes every later point visited). -/
structure IsArcVisit (W : ℝ → ℝ) (η : ℝ → ℂ) (C : Set ℂ) (A : ℝ → ℂ) (r₀ s₀ a₀ v v₂ : ℝ) : Prop where
  trace : IsLoewnerTrace W η
  continuous_W : Continuous W
  W_zero : W 0 = 0
  nonneg : 0 ≤ r₀
  lt : r₀ < s₀
  avoid : ∀ t ∈ Icc r₀ s₀, η t ∉ C
  pos : 0 < a₀
  a₀_lt : a₀ < v
  v_lt : v < v₂
  lt_one : v₂ < 1
  unvis_r : ∀ u ∈ Icc a₀ v₂, A u ∈ H \ fwdHull W r₀
  unvis_s : A a₀ ∈ H \ fwdHull W s₀
  vis_s : ∀ u ∈ Icc v v₂, A u ∈ η '' Icc 0 s₀
  rev : ∀ t : ℝ, ∀ u ∈ Icc a₀ v₂, ∀ u' ∈ Icc a₀ v₂, u ≤ u' → A u ∈ η '' Icc 0 t → A u' ∈ η '' Icc 0 t

/-- **The visit data at a witness of a reverse-contained pocket** (`a₀ = u(s₀)/2`). -/
theorem isArcVisit_of_witness (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (hA : A = α₁ ∨ A = α₂)
    {r₀ s₀ v v₁ v₂ : ℝ} (hw : Aux37Attach.IsAttachWitness η C A τ σ r₀ s₀ v v₁ v₂) :
    IsArcVisit W η C A r₀ s₀ (Sec6.firstVisit (fun t => η '' Icc 0 t) A s₀ / 2) v v₂ ∧ v < v₁ ∧ v₁ < v₂ := by
  obtain ⟨hτr, hrs, hsσ, havoid, hus, hvv₁, hv₁v₂, hv₂r⟩ := hw
  obtain ⟨hur, hur1, hDr, -, -⟩ := hP.chart hτr (hrs.trans hsσ) hA
  obtain ⟨hus0, hus1, hDs, hVs, -⟩ := hP.chart (hτr.trans hrs.le) hsσ hA
  obtain ⟨-, -, -, -, -, hrev⟩ := hP.arm hA
  set us := Sec6.firstVisit (fun t => η '' Icc 0 t) A s₀ with husdef
  refine ⟨⟨hP.trace, hP.continuous_W, hP.W_zero, hP.nonneg.trans hτr, hrs, havoid, by linarith, by linarith,
    by linarith, hv₂r.trans_le hur1, fun u hu => hDr u ⟨by linarith [hu.1], hu.2.trans_lt hv₂r⟩,
    hDs _ ⟨by linarith, by linarith⟩, fun u hu => hVs u ⟨by linarith [hu.1], by linarith [hu.2, hv₂r.trans_le hur1]⟩,
    fun t u hu u' hu' huu' h => hrev t u ⟨by linarith [hu.1], by linarith [hu.2, hv₂r.trans_le hur1]⟩ u'
      ⟨by linarith [hu'.1], by linarith [hu'.2, hv₂r.trans_le hur1]⟩ huu' h⟩, hvv₁, hv₁v₂⟩

/-- **The unswallowed collar band** at a witness (generic in the pocket, through its visit data): the chart band over
the arc values `f([a₀, v₂])` of some height `δ > 0` maps under the chart inverse off `m(K_{s₀})` and off the walls (the
collar argument of `Aux37Frame.collar_of_band`, keeping the band itself). -/
theorem exists_band_cf {r₀ s₀ a₀ v v₂ : ℝ} (hV : IsArcVisit W η C A r₀ s₀ a₀ v v₂) {P : Set ℂ}
    (hCP : C = negInv '' P) (hPH : P ⊆ H) {X : ℝ≥0 → ℂ} {Wu : Set ℂ} (hPW : Disjoint P Wu) {lo hi : ℝ}
    (hAX : ∀ u ∈ Ioo (0 : ℝ) 1, negInv (A u) = X (arcTime (lo + u * (hi - lo))).toNNReal)
    {c : Chart} (hc : c.IsConformal) (hcP : MapsTo c.2.1 H P) {f : ℝ → ℝ} (hfc : ContinuousOn f (Ioo 0 1))
    (hlim : ∀ u ∈ Ioo (0 : ℝ) 1, Tendsto c.2.1 (𝓝[H] (f u : ℂ)) (𝓝 (X (arcTime (lo + u * (hi - lo))).toNNReal))) :
    ∃ δ > 0, ∀ w ∈ H, w.re ∈ uIcc (f a₀) (f v₂) → w.im < δ → c.2.1 w ∈ H \ (negInv '' fwdHull W s₀ ∪ Wu) := by
  have hη := hV.trace
  have hW := hV.continuous_W
  have hr₀ : 0 ≤ r₀ := hV.nonneg
  have hs₀ : 0 ≤ s₀ := hr₀.trans hV.lt.le
  have hdom : ∀ {t : ℝ}, ∀ u, A u ∈ H \ fwdHull W t → negInv (A u) ∈ H \ negInv '' fwdHull W t := fun u hu =>
    ⟨negInv_mem_H hu.1, fun hK => hu.2 (by rw [mem_negInv_image, negInv_negInv] at hK; exact hK)⟩
  have h12 : a₀ ≤ v₂ := (hV.a₀_lt.trans hV.v_lt).le
  have hIcc : Icc a₀ v₂ ⊆ Ioo (0 : ℝ) 1 := fun u hu => ⟨hV.pos.trans_le hu.1, hu.2.trans_lt hV.lt_one⟩
  have hK : uIcc (f a₀) (f v₂) ⊆ f '' Icc a₀ v₂ := by
    have := intermediate_value_uIcc (hfc.mono (by rw [uIcc_of_le h12]; exact hIcc))
    rwa [uIcc_of_le h12] at this
  obtain ⟨δ, hδ, hband⟩ := exists_band (c := c) isCompact_uIcc (WangWu.isOpen_H_diff_negInv_fwdHull hW hr₀)
    fun q hq => by
      obtain ⟨u, hu, rfl⟩ := hK hq
      refine ⟨_, ?_, hlim u (hIcc hu)⟩
      rw [← hAX u (hIcc hu)]
      exact hdom u (hV.unvis_r u hu)
  set a := f a₀ ⊓ f v₂ with ha
  set b := f a₀ ⊔ f v₂ with hb
  set S : Set ℂ := {w : ℂ | w ∈ H ∧ w.re ∈ Icc a b ∧ w.im < δ} with hS
  set B : Set ℂ := c.2.1 '' S with hB
  have hcont : ContinuousOn c.2.1 H := hc.1.continuousOn
  have hBpc : IsPreconnected B := ((convex_band a b δ).isPreconnected).image _ (hcont.mono fun w hw => hw.1)
  have hBr : B ⊆ P \ negInv '' fwdHull W r₀ := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hcP hw.1, (hband w hw.1 hw.2.1 hw.2.2).2⟩
  have hBH : B ⊆ H := by rintro _ ⟨w, hw, rfl⟩; exact hc.2.1 hw.1
  have hBs : (B \ negInv '' fwdHull W s₀).Nonempty := by
    have hσ₁ : a₀ ∈ Ioo (0 : ℝ) 1 := hIcc ⟨le_rfl, h12⟩
    have hps : X (arcTime (lo + a₀ * (hi - lo))).toNNReal ∈ H \ negInv '' fwdHull W s₀ := by
      rw [← hAX _ hσ₁]
      exact hdom _ hV.unvis_s
    have hm : c.2.1 ⁻¹' (H \ negInv '' fwdHull W s₀) ∈ 𝓝[H] (f a₀ : ℂ) :=
      hlim _ hσ₁ ((WangWu.isOpen_H_diff_negInv_fwdHull hW hs₀).mem_nhds hps)
    obtain ⟨ρ, hρ, hρs⟩ := Metric.mem_nhdsWithin_iff.1 hm
    set t : ℝ := min ρ δ / 2 with ht
    have ht0 : 0 < t := by positivity
    have htρ : t < ρ := by have := min_le_left ρ δ; linarith
    have htδ : t < δ := by have := min_le_right ρ δ; linarith
    set w : ℂ := (f a₀ : ℂ) + (t : ℂ) * I with hw
    have hwre : w.re = f a₀ := by simp [hw]
    have hwim : w.im = t := by simp [hw]
    have hwH : w ∈ H := show (0 : ℝ) < w.im by rw [hwim]; exact ht0
    have hwball : w ∈ ball (f a₀ : ℂ) ρ := by
      rw [mem_ball, dist_eq, show w - (f a₀ : ℂ) = (t : ℂ) * I by rw [hw]; ring, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact htρ
    exact ⟨c.2.1 w, ⟨w, ⟨hwH, by rw [hwre]; exact ⟨inf_le_left, le_sup_left⟩, by rw [hwim]; exact htδ⟩, rfl⟩,
      (hρs ⟨hwball, hwH⟩).2⟩
  have hBdis : Disjoint B (negInv '' fwdHull W s₀) :=
    disjoint_of_avoid hη hr₀ hV.lt.le hPH (fun t ht => by rw [← hCP]; exact hV.avoid t ht) hBpc hBr hBs
  refine ⟨δ, hδ, fun w hwH hwre hwim => ?_⟩
  have hwS : w ∈ S := ⟨hwH, hwre, hwim⟩
  have hz : c.2.1 w ∈ B := ⟨w, hwS, rfl⟩
  exact ⟨hBH hz, fun h => h.elim (fun h' => Set.disjoint_left.1 hBdis hz h')
    (fun h' => Set.disjoint_left.1 hPW (hBr hz).1 h')⟩

end Band

/-! ### The counterflow map on a rectangle of the band -/

section ExtRect

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {c : Chart} {κ : ℂ → ℂ} {t s₀ a b δ a' b' δ' : ℝ} {Wu : Set ℂ}

/-- **The counterflow map `g_t ∘ m ∘ ℓ` on a rectangle of the band** (see the module docstring): the extension and the
real-boundary conformality of the transition on every upper half-disc of the rectangle. -/
theorem exists_ext_rect (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hts : t ≤ s₀) (hc : c.IsConformal) (hℓc : ContinuousOn (land c) Hbar) (hℓH : ∀ w ∈ H, land c w = c.2.1 w)
    (hκ : ∀ q ∈ Hbar, κ (land c q) = q) (hκc : ∀ q ∈ Hbar, ContinuousWithinAt κ (land c '' Hbar) (land c q))
    (hℓ0 : ∀ q ∈ closure (rect a' b' δ'), land c q ≠ 0)
    (hband : ∀ w ∈ H, w.re ∈ Icc a b → w.im < δ → c.2.1 w ∈ H \ (negInv '' fwdHull W s₀ ∪ Wu))
    (haa : a ≤ a') (hbb : b' ≤ b) (hδδ : δ' < δ)
    (hvis : ∀ q : ℝ, q ∈ Icc a' b' → negInv (land c q) ∉ H \ fwdHull W t) :
    ∃ G : ℂ → ℂ, ContinuousOn G (negInv '' (land c '' closure (rect a' b' δ'))) ∧
      InjOn G (negInv '' (land c '' closure (rect a' b' δ'))) ∧
      MapsTo G (negInv '' (land c '' closure (rect a' b' δ'))) Hbar ∧
      (∀ z ∈ negInv '' (land c '' closure (rect a' b' δ')), trMap W 0 t (G z) = z) ∧
      (∀ z ∈ negInv '' (land c '' closure (rect a' b' δ')), z ∈ H \ fwdHull W t → G z = fwdMap W t z) ∧
      (∀ z ∈ negInv '' (land c '' closure (rect a' b' δ')), z ∉ H \ fwdHull W t → (G z).im = 0) ∧
      (∀ q ∈ closure (rect a' b' δ'), q ∈ H → negInv (land c q) ∈ H \ fwdHull W s₀) ∧
      ∀ ξ ρ : ℝ, ρ ≤ ξ - a' → ρ ≤ b' - ξ → ρ ≤ δ' →
        R16.IsRealBoundaryConformal (fun w => G (negInv (land c w))) ξ ρ := by
  set S := rect a' b' δ' with hSdef
  have hKH : closure S ⊆ Hbar := closure_rect_subset.trans crect_subset_Hbar
  have hMc : ContinuousOn negInv (land c '' closure S) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (WangWu.continuousAt_negInv (hℓ0 q hq)).continuousWithinAt
  have hM' : ∀ z ∈ land c '' closure S, negInv (negInv z) = z := fun z _ => WangWu.negInv_negInv z
  have hM'c : ∀ z ∈ land c '' closure S, ContinuousAt negInv (negInv z) := by
    rintro _ ⟨q, hq, rfl⟩
    refine WangWu.continuousAt_negInv ?_
    intro h0
    have := WangWu.negInv_negInv (land c q)
    rw [h0] at this
    exact hℓ0 q hq (by rw [← this]; simp [WangWu.negInv])
  have hDs : ∀ q ∈ closure S, q ∈ H → negInv (land c q) ∈ H \ fwdHull W s₀ := by
    intro q hq hqH
    have hq' := closure_rect_subset hq
    have hb := hband q hqH ⟨haa.trans hq'.2.2.1, hq'.2.2.2.trans hbb⟩ (hq'.2.1.trans_lt hδδ)
    rw [hℓH q hqH]
    refine ⟨WangWu.negInv_mem_H hb.1, fun hK => hb.2 (Or.inl ?_)⟩
    rw [mem_negInv_image]
    exact hK
  have hD : ∀ q ∈ closure S, q ∈ H → negInv (land c q) ∈ H \ fwdHull W t := fun q hq hqH =>
    ⟨(hDs q hq hqH).1, fun hK => (hDs q hq hqH).2 (WangWu.fwdHull_mono hts hK)⟩
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ := exists_ext hη hW hW0 ht convex_rect rect_subset_H isCompact_closure_rect hKH
    hℓc hκ hκc hMc hM' hM'c hD
  refine ⟨G, h1, h2, h3, h4, h5, h6, hDs, fun ξ ρ hρa hρb hρδ => ?_⟩
  obtain ⟨-, hball⟩ := ball_subset_rect (a := a') (b := b') (δ := δ') hρa hρb hρδ
  refine isRealBoundaryConformal_ext hW ht hKH hℓc hκ hMc hM' hD h1 h2 h5 h6 hball ?_ ?_
  · intro q hq hqH
    have hq' := closure_rect_subset hq
    have him : q.im = 0 := le_antisymm (not_lt.1 hqH) hq'.1
    have hqr : q = ((q.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hqr]
    exact hvis q.re hq'.2.2
  · intro w hw
    have hwH : w ∈ H := hw.1
    have h0 : c.2.1 w ≠ 0 := by rw [← hℓH w hwH]; exact hℓ0 w (hball ⟨QuantumZipper.H_subset_Hbar hwH, hw.2⟩)
    have hd : DifferentiableAt ℂ (fun w => -(c.2.1 w)⁻¹) w :=
      ((hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hwH)).inv h0).neg
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hwH] with w' hw'
    simp only [WangWu.negInv, hℓH w' hw']

end ExtRect

end InteractingSLE.Sec7.Aux37Side
