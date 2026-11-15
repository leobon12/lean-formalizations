/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FrameCollar

/-!
# Aux. lemma 37's witness frame at one witness: the counterflow-chart inputs of the collar

Packet PROVE-STRIPSYS40. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L104–L120,
pp. 198–199). For the change pocket `C = m(P)` of the walls `R`, `L` (`P = changePocket R L r` in the flow chart,
`m(z) = −1/z`), a counterflow `η` (a Loewner trace of `W`) and a witness interval `[r₀, s₀]` on which `η` avoids `C`:

* `mem_negInv_image`: `z ∈ m(X) ↔ m(z) ∈ X`;
* **`disjoint_of_avoid`**: every preconnected subset of `P ∖ m(K_{r₀})` meeting `ℍ ∖ m(K_{s₀})` misses `m(K_{s₀})`
  (the new range avoids `C`; a connected set off the old range meeting the domain stays in it);
* **`component_subset_pocket`**: components of `ℍ ∖ (A ∪ walls)` through a point of `P` stay in `P` (the frontier of
  `C` is made of wall points and possibly `0`);
* **`exists_ball_range`**: near a point `R(t₀)` of a simple proper curve, the curve only passes at times near `t₀`.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex Bornology
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Frame

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry

/-! ### `m(z) = −1/z` -/

section NegInv

theorem mem_negInv_image {X : Set ℂ} {z : ℂ} : z ∈ negInv '' X ↔ negInv z ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩; rwa [negInv_negInv]
  · intro h; exact ⟨negInv z, h, negInv_negInv z⟩

theorem negInv_image_negInv_image (X : Set ℂ) : negInv '' (negInv '' X) = X := by
  ext z; simp only [mem_negInv_image, negInv_negInv]

theorem negInv_image_subset_H {X : Set ℂ} (hX : X ⊆ H) : negInv '' X ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩; exact negInv_mem_H (hX hz)

theorem isPreconnected_negInv_image {S : Set ℂ} (hS : IsPreconnected S) (hSH : S ⊆ H) :
    IsPreconnected (negInv '' S) :=
  hS.image _ fun _ hz => (WangWu.continuousAt_negInv (Aux37Assembly.ne_zero_of_mem_H (hSH hz))).continuousWithinAt

end NegInv

/-! ### No new hull in the avoided pocket -/

section Avoid

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **No new hull in the avoided pocket** (flow chart): if `η([r₀, s₀]) ∩ C = ∅` for `C = m(P)`, every preconnected
subset of `P ∖ m(K_{r₀})` that meets `ℍ ∖ m(K_{s₀})` misses `m(K_{s₀})`. -/
theorem disjoint_of_avoid (hη : IsLoewnerTrace W η) {r₀ s₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrs : r₀ ≤ s₀) {P : Set ℂ}
    (hPH : P ⊆ H) (havoid : ∀ t ∈ Icc r₀ s₀, η t ∉ negInv '' P) {S : Set ℂ} (hS : IsPreconnected S)
    (hSP : S ⊆ P \ negInv '' fwdHull W r₀) (hSs : (S \ negInv '' fwdHull W s₀).Nonempty) :
    Disjoint S (negInv '' fwdHull W s₀) := by
  have hSH : S ⊆ H := fun z hz => hPH (hSP hz).1
  have hS' := isPreconnected_negInv_image hS hSH
  have hS'H := negInv_image_subset_H hSH
  have hS'R : Disjoint (negInv '' S) (η '' Icc 0 s₀) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨t, ht, hte⟩
    rcases le_or_gt t r₀ with htr | htr
    · refine Sec6.notMem_domain_of_mem_trace hη hr₀ ⟨t, ⟨ht.1, htr⟩, hte⟩ ⟨negInv_mem_H (hSH hz), ?_⟩
      intro hK
      exact (hSP hz).2 (mem_negInv_image.2 hK)
    · exact havoid t ⟨htr.le, ht.2⟩ (hte ▸ mem_negInv_image.2 (by rw [negInv_negInv]; exact (hSP hz).1))
  obtain ⟨z, hzS, hzs⟩ := hSs
  have hsub := Sec6.subset_domain_of_isPreconnected hη (hr₀.trans hrs) hS' hS'H hS'R ⟨z, hzS, rfl⟩
    ⟨negInv_mem_H (hSH hzS), fun hK => hzs (mem_negInv_image.2 hK)⟩
  refine Set.disjoint_left.2 fun y hy hyK => (hsub ⟨y, hy, rfl⟩).2 (mem_negInv_image.1 hyK)

end Avoid

/-! ### Components stay in the pocket -/

section Component

/-- **Components through the pocket stay in the pocket** (flow chart): if every frontier point of `C = m(P)` in `ℍ` is
the `m`-image of a point of `W`, then the component of `ℍ ∖ (A ∪ W)` through a point of `P` lies in `P`. -/
theorem component_subset_pocket {P A Wu : Set ℂ} (hCo : IsOpen (negInv '' P))
    (hfr : ∀ y ∈ frontier (negInv '' P), y ∈ H → negInv y ∈ Wu) {z : ℂ} (hz : z ∈ P) :
    connectedComponentIn (H \ (A ∪ Wu)) z ⊆ P := by
  by_cases hzE : z ∉ H \ (A ∪ Wu)
  · rw [connectedComponentIn_eq_empty hzE]; exact empty_subset _
  rw [not_not] at hzE
  set Q := connectedComponentIn (H \ (A ∪ Wu)) z with hQ
  have hQsub : Q ⊆ H \ (A ∪ Wu) := connectedComponentIn_subset _ _
  have hQH : Q ⊆ H := fun y hy => (hQsub hy).1
  have hQ' := isPreconnected_negInv_image isPreconnected_connectedComponentIn hQH
  have hzQ : z ∈ Q := mem_connectedComponentIn hzE
  have hne : (negInv '' Q ∩ negInv '' P).Nonempty := ⟨negInv z, ⟨z, hzQ, rfl⟩, ⟨z, hz, rfl⟩⟩
  have hdis : Disjoint (negInv '' Q) (frontier (negInv '' P)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨q, hq, rfl⟩ hfq
    have := hfr _ hfq (negInv_mem_H (hQH hq))
    rw [negInv_negInv] at this
    exact (hQsub hq).2 (Or.inr this)
  have hsub := Sec6.subset_of_isPreconnected_of_disjoint_frontier hQ' hCo hne hdis
  intro q hq
  have := hsub ⟨q, hq, rfl⟩
  rwa [mem_negInv_image, negInv_negInv] at this

end Component

/-! ### A simple proper curve near one of its points -/

section Embed

/-- **Near `R(t₀)` the simple proper curve `R` passes only at times near `t₀`.** -/
theorem exists_ball_range {R : ℝ≥0 → ℂ} (hR : IsSimpleProper R) (t₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ t : ℝ≥0, R t ∈ ball (R t₀) ε → dist t t₀ < δ := by
  set M : ℝ := ‖R t₀‖ + 1 with hM
  obtain ⟨T, hT⟩ := (hR.2.2.2.2.eventually (eventually_gt_atTop M)).exists_forall_of_atTop
  set K : Set ℝ≥0 := {t | δ ≤ dist t t₀ ∧ ‖R t‖ ≤ M} with hK
  have hKc : IsClosed K :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_norm.comp hR.1) continuous_const)
  have hKT : K ⊆ Icc 0 T := fun t ht => ⟨bot_le, not_lt.1 fun hlt => by
    have := hT t hlt.le; linarith [ht.2]⟩
  have hKcpt : IsCompact K := (isCompact_Icc).of_isClosed_subset hKc hKT
  have hRK : IsCompact (R '' K) := hKcpt.image hR.1
  have hnot : R t₀ ∉ R '' K := by
    rintro ⟨t, ht, he⟩
    have h1 : δ ≤ dist t t₀ := ht.1
    rw [hR.2.1 he, dist_self] at h1
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hRK.isClosed.isOpen_compl _ hnot
  refine ⟨min ε 1, lt_min hε one_pos, fun t ht => not_le.1 fun hle => ?_⟩
  have hd : dist (R t) (R t₀) < min ε 1 := ht
  have hn : ‖R t‖ ≤ M := by
    have := norm_le_norm_add_norm_sub' (R t) (R t₀)
    rw [← dist_eq_norm] at this
    linarith [min_le_right ε 1]
  exact hball (mem_ball.2 (hd.trans_le (min_le_left _ _))) ⟨t, ⟨hle, hn⟩, rfl⟩

end Embed

/-! ### The frame fields at one witness (either arc) -/

section Fields

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β A : ℝ → ℂ} {τ σ : ℝ}

/-- An affine parameter in `(0, 1)` gives a disc parameter in `(lo, hi)`. -/
theorem affine_mem_Ioo {lo hi u : ℝ} (hlh : lo < hi) (hu : u ∈ Ioo (0 : ℝ) 1) :
    lo + u * (hi - lo) ∈ Ioo lo hi := by
  have h := sub_pos.2 hlh
  constructor
  · have := mul_pos hu.1 h; linarith
  · have := mul_lt_mul_of_pos_right hu.2 h; linarith

/-- **The frame fields (F2), (F3), (F4) at a witness point** (generic in the arc). In the counterflow chart, `C = m(P)`
is a reverse-contained pocket and `A` one of its arcs, read through the wall `X` (`m(A u) = X(arcTime(lo + u(hi − lo)))`
on `(0, 1)`), with a conformal chart `c` of `P` whose inverse lands at the wall points at the real values `f u`
(continuous, injective). For a witness `(r₀, s₀, v, v₁, v₂)` on `A` and `x ∈ [v, v₂)`, put `z₀ = m(A x)` and
`A_t = m(K_t)`. Then: a ball around `z₀` misses `A_{r₀}`; `z₀ ∈ A_{s₀}`, and near `z₀` the walls `Wu` (contained in the
ranges of `X` and `Y`, the latter off `z₀`) lie in `A_{s₀}`; the chart approach at `f x` comes from `P` and from
`ℍ ∖ (A_{s₀} ∪ Wu)`, inside one component of it that is also a component of `ℍ ∖ (A_{r₀} ∪ Wu)`. -/
theorem witness_fields (hP : Sec6.IsReversePocket W η C α₁ α₂ β τ σ) (hA : A = α₁ ∨ A = α₂) {P : Set ℂ}
    (hCP : C = negInv '' P) (hPH : P ⊆ H) {X Y : ℝ≥0 → ℂ} (hX : IsSimpleProper X) (hY : IsSimpleProper Y)
    {Wu : Set ℂ} (hWu : Wu ⊆ range X ∪ range Y) (hPW : Disjoint P Wu)
    (hfr : ∀ y ∈ frontier C, y ∈ H → negInv y ∈ Wu) {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo < hi) (hhi : hi ≤ 1)
    (hAX : ∀ u ∈ Ioo (0 : ℝ) 1, negInv (A u) = X (arcTime (lo + u * (hi - lo))).toNNReal)
    {c : Chart} (hc : c.IsConformal) (hcP : MapsTo c.2.1 H P) {f : ℝ → ℝ}
    (hfc : ContinuousOn f (Ioo 0 1)) (hfi : InjOn f (Ioo 0 1))
    (hlim : ∀ u ∈ Ioo (0 : ℝ) 1, Tendsto c.2.1 (𝓝[H] (f u : ℂ)) (𝓝 (X (arcTime (lo + u * (hi - lo))).toNNReal)))
    {r₀ s₀ v v₁ v₂ x : ℝ} (hw : Aux37Attach.IsAttachWitness η C A τ σ r₀ s₀ v v₁ v₂) (hx : x ∈ Ico v v₂)
    (hY₀ : negInv (A x) ∉ range Y) :
    (∃ ε > 0, negInv '' fwdHull W r₀ ∩ ball (negInv (A x)) ε = ∅) ∧ negInv (A x) ∈ negInv '' fwdHull W s₀ ∧
      (∃ ε > 0, Wu ∩ ball (negInv (A x)) ε ⊆ negInv '' fwdHull W s₀) ∧
      (map c.2.1 (𝓝[H] (f x : ℂ))).NeBot ∧ map c.2.1 (𝓝[H] (f x : ℂ)) ≤ 𝓝[P] (negInv (A x)) ∧
      map c.2.1 (𝓝[H] (f x : ℂ)) ≤ 𝓝[H \ (negInv '' fwdHull W s₀ ∪ Wu)] (negInv (A x)) ∧
      ∃ z ∈ H \ (negInv '' fwdHull W s₀ ∪ Wu),
        connectedComponentIn (H \ (negInv '' fwdHull W s₀ ∪ Wu)) z =
          connectedComponentIn (H \ (negInv '' fwdHull W r₀ ∪ Wu)) z ∧
        ∀ᶠ w in map c.2.1 (𝓝[H] (f x : ℂ)), w ∈ connectedComponentIn (H \ (negInv '' fwdHull W s₀ ∪ Wu)) z := by
  have hη := hP.trace
  have hW := hP.continuous_W
  obtain ⟨hτr, hrs, hsσ, havoid, hus, hvv₁, hv₁v₂, hv₂r⟩ := hw
  have hr₀ : 0 ≤ r₀ := hP.nonneg.trans hτr
  have hs₀ : 0 ≤ s₀ := hr₀.trans hrs.le
  obtain ⟨hur, hur1, hDr, -, -⟩ := hP.chart hτr (hrs.trans hsσ) hA
  obtain ⟨hus0, hus1, hDs, hVs, -⟩ := hP.chart (hτr.trans hrs.le) hsσ hA
  set ur := Sec6.firstVisit (fun t => η '' Icc 0 t) A r₀ with hurdef
  set us := Sec6.firstVisit (fun t => η '' Icc 0 t) A s₀ with husdef
  have hx0 : 0 < x := hus0.trans (hus.trans_le hx.1)
  have hx1 : x < 1 := hx.2.trans (hv₂r.trans_le hur1)
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx1⟩
  -- the cf-chart point and its flow-chart image
  have hAxr : A x ∈ H \ fwdHull W r₀ := hDr x ⟨hx0.le, hx.2.trans hv₂r⟩
  have hAxH : A x ∈ H := hAxr.1
  have hAxs : A x ∈ η '' Icc 0 s₀ := hVs x ⟨hus.le.trans hx.1, hx1.le⟩
  have hhull_s : ∀ u ∈ Icc us 1, A u ∈ H → negInv (A u) ∈ negInv '' fwdHull W s₀ := fun u hu huH => by
    refine mem_negInv_image.2 ?_
    rw [negInv_negInv]
    by_contra hK
    exact Sec6.notMem_domain_of_mem_trace hη hs₀ (hVs u hu) ⟨huH, hK⟩
  have hdom : ∀ {t : ℝ}, ∀ u, A u ∈ H \ fwdHull W t → negInv (A u) ∈ H \ negInv '' fwdHull W t := fun u hu =>
    ⟨negInv_mem_H hu.1, fun hK => hu.2 (by rw [mem_negInv_image, negInv_negInv] at hK; exact hK)⟩
  -- (F2), (F3a)
  have hF2 : ∃ ε > 0, negInv '' fwdHull W r₀ ∩ ball (negInv (A x)) ε = ∅ := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (WangWu.isOpen_H_diff_negInv_fwdHull hW hr₀) _ (hdom x hAxr)
    exact ⟨ε, hε, eq_empty_of_forall_notMem fun z hz => (hball hz.2).2 hz.1⟩
  have hF3a := hhull_s x ⟨hus.le.trans hx.1, hx1.le⟩ hAxH
  -- (F3b): the walls near `z₀`
  have hF3b : ∃ ε > 0, Wu ∩ ball (negInv (A x)) ε ⊆ negInv '' fwdHull W s₀ := by
    set σx := lo + x * (hi - lo) with hσx
    have hσxI := affine_mem_Ioo hlh hxI
    have hσx1 : σx < 1 := hσxI.2.trans_le hhi
    set t₀ : ℝ≥0 := (arcTime σx).toNNReal with ht₀
    have ht₀r : (t₀ : ℝ) = arcTime σx := Real.coe_toNNReal _ (arcTime_nonneg ⟨(hlo.trans hσxI.1).le, hσx1⟩)
    have hz₀ : negInv (A x) = X t₀ := hAX x hxI
    -- the disc parameters of `(us, v₂)` around `σx`
    have hlo' : lo + us * (hi - lo) < σx := by
      have := mul_lt_mul_of_pos_right (hus.trans_le hx.1) (sub_pos.2 hlh); linarith
    have hhi' : σx < lo + v₂ * (hi - lo) := by
      have := mul_lt_mul_of_pos_right hx.2 (sub_pos.2 hlh); linarith
    have hdc : ContinuousAt WangWu.discTime (t₀ : ℝ) := by
      have h1 : (1 : ℝ) + t₀ ≠ 0 := by positivity
      exact continuousAt_id.div (continuousAt_const.add continuousAt_id) h1
    have hdt₀ : WangWu.discTime (t₀ : ℝ) = σx := by rw [ht₀r, WangWu.discTime_arcTime hσx1]
    have hnb : Ioo (lo + us * (hi - lo)) (lo + v₂ * (hi - lo)) ∈ 𝓝 (WangWu.discTime (t₀ : ℝ)) := by
      rw [hdt₀]; exact Ioo_mem_nhds hlo' hhi'
    obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 (hdc hnb)
    obtain ⟨ε₂, hε₂, hR⟩ := exists_ball_range hX t₀ hδ
    obtain ⟨ε₁, hε₁, hYb⟩ := Metric.isOpen_iff.1 (Lemma71Pin.IsSimpleProper.isClosed_range hY).isOpen_compl _ hY₀
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z ⟨hzW, hzb⟩ => ?_⟩
    rcases hWu hzW with ⟨t, rfl⟩ | hzY
    · have htd : dist t t₀ < δ := hR t (by rw [← hz₀]; exact ball_subset_ball (min_le_right _ _) hzb)
      have hσ := hδb (show (t : ℝ) ∈ ball (t₀ : ℝ) δ from htd)
      set u := (WangWu.discTime t - lo) / (hi - lo) with hu
      have hul : lo + u * (hi - lo) = WangWu.discTime t := by
        rw [hu]; field_simp [(sub_pos.2 hlh).ne']; ring
      have hus' : us < u := by
        rw [hu, lt_div_iff₀ (sub_pos.2 hlh)]; linarith [hσ.1]
      have huv : u < v₂ := by
        rw [hu, div_lt_iff₀ (sub_pos.2 hlh)]; linarith [hσ.2]
      have huI : u ∈ Ioo (0 : ℝ) 1 := ⟨hus0.trans hus', huv.trans (hv₂r.trans_le hur1)⟩
      have hXt : X t = negInv (A u) := by
        rw [hAX u huI, hul, WangWu.arcTime_discTime t.coe_nonneg, Real.toNNReal_coe]
      have hAuH : A u ∈ H := (hP.arm hA).2.2.2.2.1 u ⟨huI.1.le, huI.2⟩
      rw [hXt]
      exact hhull_s u ⟨hus'.le, huI.2.le⟩ hAuH
    · exact absurd hzY (hYb (ball_subset_ball (min_le_left _ _) hzb))
  -- (F4): the collar
  have hIcc : Icc (us / 2) v₂ ⊆ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨by linarith [hu.1, hus0], hu.2.trans_lt (hv₂r.trans_le hur1)⟩
  have h10 : us / 2 < x := by linarith [hus0, hus, hx.1]
  obtain ⟨hev, z, hzE, hcomp, hevc⟩ := collar_of_band (σ₁ := us / 2) (σ₀ := x) (σ₂ := v₂) hc hcP hPW
    (image_mono (WangWu.fwdHull_mono hrs.le)) (WangWu.isOpen_H_diff_negInv_fwdHull hW hr₀)
    (WangWu.isOpen_H_diff_negInv_fwdHull hW hs₀)
    (fun z hz => component_subset_pocket (by rw [← hCP]; exact hP.isOpen) (by rw [← hCP]; exact hfr) hz)
    (fun S hS hSP hSs => disjoint_of_avoid hη hr₀ hrs.le hPH (fun t ht => by rw [← hCP]; exact havoid t ht) hS hSP
      hSs)
    h10 hx.2 (hfc.mono hIcc) (hfi.mono hIcc) (p := fun u => X (arcTime (lo + u * (hi - lo))).toNNReal)
    (fun u hu => hlim u (hIcc hu))
    (fun u hu => by
      have huI : u ∈ Ioo (0 : ℝ) 1 := hIcc hu
      show X (arcTime (lo + u * (hi - lo))).toNNReal ∈ _
      rw [← hAX u huI]
      exact hdom u (hDr u ⟨huI.1.le, hu.2.trans_lt hv₂r⟩))
    (by
      have huI : us / 2 ∈ Ioo (0 : ℝ) 1 := hIcc ⟨le_rfl, by linarith [hv₁v₂, hvv₁, hus, hus0]⟩
      show X (arcTime (lo + us / 2 * (hi - lo))).toNNReal ∈ _
      rw [← hAX _ huI]
      exact hdom _ (hDs _ ⟨huI.1.le, by linarith⟩))
  have hxl := hlim x hxI
  rw [← hAX x hxI] at hxl
  have hne : (𝓝[H] (f x : ℂ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    show (0 : ℝ) ≤ ((f x : ℝ) : ℂ).im
    simp
  refine ⟨hF2, hF3a, hF3b, Filter.map_neBot, le_inf hxl (tendsto_principal.2
    (eventually_nhdsWithin_of_forall fun w hw => hcP hw)), le_inf hxl (tendsto_principal.2 hev), z, hzE, hcomp,
    hevc⟩

end Fields

end InteractingSLE.Sec7.Aux37Frame
