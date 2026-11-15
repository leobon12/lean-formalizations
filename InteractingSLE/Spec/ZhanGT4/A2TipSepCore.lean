/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2TipSepGeom

/-!
# A.2, part 2, step 1: the pathwise separation from the image endpoint alternative

Packet PROVE-ZHAN-A2TIPSEP. Source: Astra, *Follow-up proofs*, §A.2 L548–L553 (R38, R53).

Fix one sample: a large driver `A` (continuous, `A 0 = 0`) stopped at `τ > 0`, with the small source `y` alive (not in
the closed large hull `K = K_τ`), the small crosscut `γ` from `y` (`IsSmallCrosscut`), and the image chain of the small
curve under `g_τ` up to its first contact with `K` (`IsImageChainUpTo`). The source's conditional separation is:

* `exists_contact_point` ("this conditional image is maximal at first contact", the physical side): the small hulls
  before contact accumulate at a point `q ≠ y` of the closed large hull or of `ℝ` (the first contact point, or the
  crosscut's end point when there is no contact);
* `not_premature`: hence the image curve was not stopped prematurely — its image points accumulate at a real point
  (the inverse map is continuous on `ℍ` and `q` is not in `ℍ \ K`), which is not the image source (points near the
  source come from the early small hulls, which shrink to `y`);
* `tipSeparated_of_endpoint`: so the crosscut alternative of `ImageEndpointAlt` holds, the image crosscut runs from the
  image source `< W_τ` to a point `> W_τ`, and its pull-back (the small hulls before contact, inside `J`) separates the
  large tip from `∞` (`A2Part2.tipSeparated_of_image`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A2TipSep

open QuantumZipper A2X A2Part2

/-- A strict upper bound of a bounded infimum is witnessed by one admissible index. -/
theorem exists_of_iInf₂_lt {p : ℝ≥0 → Prop} {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ⨅ (s : ℝ≥0) (_ : p s), f s < a) : ∃ s, p s ∧ f s < a := by
  obtain ⟨s, hs⟩ := iInf_lt_iff.1 h
  by_cases hp : p s
  · rw [iInf_pos hp] at hs; exact ⟨s, hp, hs⟩
  · rw [iInf_neg hp] at hs; exact absurd hs not_top_lt

/-- The small hulls before the time `c`. -/
def preHulls (y : ℝ) (w : ℝ → ℝ) (c : ℝ≥0∞) : Set ℂ := ⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < c), physHull y w s

theorem physHull_subset_H (x : ℝ) (w : ℝ → ℝ) (s : ℝ) : physHull x w s ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  have : 0 < z.im := hz.1
  show 0 < (z + x).im
  simpa using this

theorem closure_fwdHull_inter_H_subset {A : ℝ → ℝ} (hA : Continuous A) {τ : ℝ} (hτ : 0 ≤ τ) {z : ℂ}
    (hz : z ∈ closure (fwdHull A τ)) (hzH : z ∈ H) : z ∈ fwdHull A τ := by
  by_contra hzK
  have hopen := FwdHolo.isOpen_compl_fwdHull hA hτ
  obtain ⟨w, hw, hwK⟩ := mem_closure_iff.1 hz _ hopen ⟨hzH, hzK⟩
  exact hw.2 hwK

/-- Before contact, the closed small hulls miss the closed large hull. -/
theorem disjoint_closure_of_lt_contactTime {y : ℝ} {w₁ : ℝ → ℝ} {ζ₁ : ℝ≥0∞} {A : ℝ → ℝ} {τ : ℝ} {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < contactTime y w₁ ζ₁ 0 A τ) :
    Disjoint (closure (physHull y w₁ s)) (closure (physHull 0 A τ)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hne
  have h1 : contactTime y w₁ ζ₁ 0 A τ ≤ (s : ℝ≥0∞) :=
    (min_le_right _ _).trans (iInf₂_le s (Set.nonempty_iff_ne_empty.2 hne))
  exact absurd hs (not_lt.2 h1)

section Small

variable {y : ℝ} {w₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞} {γ : ℝ → ℂ} {η : ℝ≥0 → ℂ}

/-- A small hull before `ζ₁`, translated, lies in the translated trace up to its time. -/
theorem physHull_subset_trace (hγ : IsRealCrosscut γ) (hγ0 : (γ 0).re = y) (hlt : y < (γ 1).re)
    (hη : IsGeneratingTrace w₁ ζ₁ η)
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ₁}))
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₁) :
    physHull y (Strip.extPath w₁) s ⊆ (fun z : ℂ => z + y) '' (η '' Icc 0 s) :=
  image_mono (fwdHull_subset_trace hγ hγ0 hlt hη himg hs)

/-- The trace at a time `0 < r < ζ₁`, translated, lies in the crosscut, hence in `ℍ`. -/
theorem trace_add_mem_crosscut
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ₁}))
    {r : ℝ≥0} (hr : 0 < r) (hrζ : (r : ℝ≥0∞) < ζ₁) : η r + y ∈ γ '' Ioo 0 1 := by
  rw [himg]; exact ⟨η r, ⟨r, ⟨hr, hrζ⟩, rfl⟩, rfl⟩

theorem trace_mem_H (hγ : IsRealCrosscut γ)
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ₁}))
    {r : ℝ≥0} (hr : 0 < r) (hrζ : (r : ℝ≥0∞) < ζ₁) : η r ∈ H := by
  have h := hγ.2.2.1 (trace_add_mem_crosscut himg hr hrζ)
  have : 0 < (η r + y).im := h
  show 0 < (η r).im
  simpa using this

/-- The translated trace point at `0 < r < ζ₁` lies in the small hull at `r`. -/
theorem trace_add_mem_physHull (hγ : IsRealCrosscut γ) (hη : IsGeneratingTrace w₁ ζ₁ η)
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ₁}))
    {r : ℝ≥0} (hr : 0 < r) (hrζ : (r : ℝ≥0∞) < ζ₁) : η r + y ∈ physHull y (Strip.extPath w₁) r :=
  ⟨η r, trace_mem_fwdHull hη hrζ (trace_mem_H hγ himg hr hrζ), rfl⟩

/-- **The small hulls before contact lie in the small crosscut.** -/
theorem preHulls_subset_crosscut (hγ : IsRealCrosscut γ) (hγ0 : (γ 0).re = y) (hlt : y < (γ 1).re)
    (hη : IsGeneratingTrace w₁ ζ₁ η)
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ₁}))
    {c : ℝ≥0∞} (hc : c ≤ ζ₁) : preHulls y (Strip.extPath w₁) c ⊆ γ '' Ioo 0 1 := by
  intro z hz
  simp only [preHulls, mem_iUnion] at hz
  obtain ⟨s, hs, hzs⟩ := hz
  have hsζ : (s : ℝ≥0∞) < ζ₁ := hs.trans_le hc
  obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := physHull_subset_trace hγ hγ0 hlt hη himg hsζ hzs
  have hzH := physHull_subset_H y _ s hzs
  have hr0 : 0 < r := by
    rcases eq_or_lt_of_le (zero_le (a := r)) with h | h
    · exfalso; rw [← h, hη.1] at hzH
      have : (0 : ℝ) < ((0 : ℂ) + y).im := hzH
      simp at this
    · exact h
  exact trace_add_mem_crosscut himg hr0 ((ENNReal.coe_le_coe.2 hr.2).trans_lt hsζ)


/-- **The contact point** (L548–L551, the physical side of "maximal at first contact"): the small hulls before the
first contact with the closed large hull `K` accumulate at a point `q ≠ y` that lies in `K̄` (the first contact point)
or on `ℝ` (the crosscut's end point, when there is no contact before `ζ₁`). -/
theorem exists_contact_point {A : ℝ → ℝ} {τ : ℝ} (hy : (y : ℂ) ∉ closure (fwdHull A τ))
    (hγ : IsRealCrosscut γ) (hγ0 : (γ 0).re = y) (hlt : y < (γ 1).re) (hη : IsGeneratingTrace w₁ ζ₁ η)
    (himg : γ '' Ioo 0 1 = (fun z : ℂ => z + y) '' (η '' {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < ζ₁})) :
    ∃ q : ℂ, q ∈ closure (preHulls y (Strip.extPath w₁) (contactTime y (Strip.extPath w₁) ζ₁ 0 A τ)) ∧
      (q ∈ closure (fwdHull A τ) ∨ q.im = 0) ∧ q ≠ y := by
  set c := contactTime y (Strip.extPath w₁) ζ₁ 0 A τ with hc
  set M := ⨅ (s : ℝ≥0) (_ : (closure (physHull y (Strip.extPath w₁) s) ∩ closure (physHull 0 A τ)).Nonempty),
    (s : ℝ≥0∞) with hM
  have hcM : c = min ζ₁ M := rfl
  have h0 : γ 0 = (y : ℂ) := Complex.ext (by simp [hγ0]) (by simp [hγ.2.2.2.1])
  by_cases hζM : ζ₁ ≤ M
  · -- no contact before the end of the small curve: its end point
    have hcζ : c = ζ₁ := by rw [hcM, min_eq_left hζM]
    refine ⟨γ 1, ?_, Or.inr hγ.2.2.2.2, ?_⟩
    · have h1 : γ 1 ∈ closure (γ '' Ioo 0 1) := by
        have hcw : ContinuousWithinAt γ (Ioo 0 1) 1 :=
          (hγ.1 1 ⟨zero_le_one, le_rfl⟩).mono Ioo_subset_Icc_self
        have hmem : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
          rw [closure_Ioo zero_ne_one]; exact right_mem_Icc.2 zero_le_one
        exact hcw.mem_closure_image hmem
      refine closure_mono ?_ h1
      intro z hz
      rw [himg] at hz
      obtain ⟨_, ⟨r, ⟨hr0, hrζ⟩, rfl⟩, rfl⟩ := hz
      simp only [preHulls, mem_iUnion]
      exact ⟨r, hcζ ▸ hrζ, trace_add_mem_physHull hγ hη himg hr0 hrζ⟩
    · intro h1
      rw [← h0] at h1
      exact one_ne_zero (hγ.2.1 (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one) h1)
  · -- the first contact point
    push Not at hζM
    have hcM' : c = M := by rw [hcM, min_eq_right hζM.le]
    obtain ⟨s₀, hmeet₀, hs₀⟩ := exists_of_iInf₂_lt hζM
    have hphys0 : physHull 0 A τ = fwdHull A τ := A2X.P3.physHull_zero A τ
    have hsub : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ →
        closure (physHull y (Strip.extPath w₁) s) ⊆ (fun z : ℂ => z + y) '' (η '' Icc 0 s) := by
      intro s hs
      have hcpt : IsCompact ((fun z : ℂ => z + y) '' (η '' Icc 0 s)) :=
        (isCompact_Icc.image_of_continuousOn
          (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hs.le)).image (continuous_id.add continuous_const)
      exact closure_minimal (physHull_subset_trace hγ hγ0 hlt hη himg hs) hcpt.isClosed
    set T := Icc 0 s₀ ∩ (fun r => η r + y) ⁻¹' closure (fwdHull A τ) with hT
    have hTc : IsCompact T := by
      refine isCompact_Icc.of_isClosed_subset ?_ inter_subset_left
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_Icc isClosed_closure
      exact (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hs₀.le).add continuousOn_const
    have hTne : T.Nonempty := by
      obtain ⟨p, hp1, hp2⟩ := hmeet₀
      obtain ⟨_, ⟨r, hr, rfl⟩, rfl⟩ := hsub s₀ hs₀ hp1
      exact ⟨r, hr, by rw [hphys0] at hp2; exact hp2⟩
    set rs := sInf T with hrs
    have hrsT : rs ∈ T := hTc.sInf_mem hTne
    refine ⟨η rs + y, ?_, Or.inl hrsT.2, fun h => hy (h ▸ hrsT.2)⟩
    have hbefore : ∀ r : ℝ≥0, r < rs → (r : ℝ≥0∞) < c := by
      intro r hr
      rw [hcM']
      by_contra hcon
      push Not at hcon
      have hlt' : M < (rs : ℝ≥0∞) := hcon.trans_lt (ENNReal.coe_lt_coe.2 hr)
      obtain ⟨s, hmeet, hsr⟩ := exists_of_iInf₂_lt hlt'
      have hsrs : s < rs := ENNReal.coe_lt_coe.1 hsr
      have hss₀ : s ≤ s₀ := hsrs.le.trans hrsT.1.2
      have hsζ : (s : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.2 hss₀).trans_lt hs₀
      obtain ⟨p, hp1, hp2⟩ := hmeet
      obtain ⟨_, ⟨r', hr', rfl⟩, rfl⟩ := hsub s hsζ hp1
      have hr'T : r' ∈ T := ⟨⟨hr'.1, hr'.2.trans hss₀⟩, by rw [hphys0] at hp2; exact hp2⟩
      exact absurd (csInf_le hTc.bddBelow hr'T) (not_le.2 (lt_of_le_of_lt hr'.2 hsrs))
    have hrs0 : 0 < rs := by
      rcases eq_or_lt_of_le (zero_le (a := rs)) with h | h
      · exfalso; apply hy; have := hrsT.2; rw [← h] at this; simp only [mem_preimage, hη.1, zero_add] at this
        exact this
      · exact h
    have hcw : ContinuousWithinAt (fun r => η r + y) (Ioo 0 rs) rs :=
      ((hη.2.1 rs ((ENNReal.coe_le_coe.2 hrsT.1.2).trans hs₀.le)).mono fun r hr =>
        (ENNReal.coe_le_coe.2 (hr.2.le.trans hrsT.1.2)).trans hs₀.le).add continuousWithinAt_const
    have hmem : rs ∈ closure (Ioo 0 rs) := by rw [closure_Ioo hrs0.ne]; exact right_mem_Icc.2 hrs0.le
    refine closure_mono ?_ (hcw.mem_closure_image hmem)
    rintro _ ⟨r, hr, rfl⟩
    simp only [preHulls, mem_iUnion]
    have hrζ : (r : ℝ≥0∞) < ζ₁ := (ENNReal.coe_le_coe.2 (hr.2.le.trans hrsT.1.2)).trans_lt hs₀
    exact ⟨r, hbefore r hr.2, trace_add_mem_physHull hγ hη himg hr.1 hrζ⟩


/-- **The pathwise separation** (L548–L553, one sample). The large driver `A` is continuous with `A 0 = 0` and stopped
at `τ > 0`; the small source `y < 0` is not in the closed large hull; the image source `src` lies left of the large
tip `A τ`; `γ` is the small crosscut; the small curve's image under `g_τ` up to contact is the image chain of
`(w', clk, ζ')`, and the image curve satisfies the endpoint alternative. Then the large tip is separated from `∞` by
the small crosscut. -/
theorem tipSeparated_of_endpoint {A : ℝ → ℝ} (hA : Continuous A) (hA0 : A 0 = 0) {τ : ℝ} (hτ : 0 < τ)
    (hy0 : y < 0) (hy : (y : ℂ) ∉ closure (fwdHull A τ)) {src : ℝ} (hsrc : src < A τ)
    (hγ : IsSmallCrosscut y w₁ ζ₁ γ) {w' : ℝ → ℝ} {clk : ℝ → ℝ} {ζ' : ℝ≥0∞}
    (hch : IsImageChainUpTo y (Strip.extPath w₁) ζ₁ 0 A τ src w' clk ζ')
    (hend : ImageEndpointAlt w' ζ' (A τ - src)) : TipSeparated A τ (γ '' Ioo 0 1) := by
  obtain ⟨hγc, hγ0, hγ1, η, hη, himg⟩ := hγ
  have hlt : y < (γ 1).re := by linarith
  set c := contactTime y (Strip.extPath w₁) ζ₁ 0 A τ with hc
  have hcζ : c ≤ ζ₁ := min_le_left _ _
  set P₁ := preHulls y (Strip.extPath w₁) c with hP₁
  have hphys : ∀ z, physMap 0 A τ z = A τ + fwdMap A τ z := fun z => by simp [physMap]
  have hU : (fun z : ℂ => z + src) '' imgU w' ζ' = physMap 0 A τ '' P₁ := by
    rw [hP₁, preHulls, ← A2X.P3.iUnion_physHull_eq_of_imageChain hch, imgU, image_iUnion₂]
    rfl
  have hP₁K : P₁ ⊆ H \ fwdHull A τ := by
    intro z hz
    simp only [hP₁, preHulls, mem_iUnion] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    refine ⟨physHull_subset_H y _ s hzs, fun hzK => ?_⟩
    have hd := disjoint_closure_of_lt_contactTime hs
    rw [A2X.P3.physHull_zero] at hd
    exact Set.disjoint_left.1 hd (subset_closure hzs) (subset_closure hzK)
  have hP₁J : P₁ ⊆ γ '' Ioo 0 1 := preHulls_subset_crosscut hγc hγ0 hlt hη himg hcζ
  rcases hend with ⟨γ'', hγ''c, hγ''0, hb, hγ''U⟩ | ⟨hbdd, hreal, hearly⟩
  · -- the crosscut alternative: pull the image crosscut back
    set γ' : ℝ → ℂ := fun r => γ'' r - ((A τ - src : ℝ) : ℂ) with hγ'
    have hγ'c : IsRealCrosscut γ' := isRealCrosscut_sub hγ''c (A τ - src)
    refine tipSeparated_of_image hA hA0 hτ hP₁J hγ'c ?_ ?_ ?_
    · simp only [hγ', hγ''0, sub_re, zero_re, ofReal_re]; linarith
    · simp only [hγ', sub_re, ofReal_re]; linarith
    · rintro _ ⟨r, hr, rfl⟩
      have hmem : γ'' r + src ∈ physMap 0 A τ '' P₁ := by
        rw [← hU]; exact ⟨γ'' r, by rw [← hγ''U]; exact ⟨r, hr, rfl⟩, rfl⟩
      obtain ⟨z, hz, hzeq⟩ := hmem
      refine ⟨z, ⟨hz, hP₁K hz⟩, ?_⟩
      rw [hphys] at hzeq
      simp only [hγ']
      push_cast
      linear_combination hzeq
  · -- the premature alternative is impossible
    exfalso
    obtain ⟨q, hqcl, hqK, hqy⟩ := exists_contact_point hy hγc hγ0 hlt hη himg
    obtain ⟨z, hzP, hzq⟩ := mem_closure_iff_seq_limit.1 hqcl
    set u : ℕ → ℂ := fun n => (A τ : ℂ) + fwdMap A τ (z n) - src with hu
    have huU : ∀ n, u n ∈ imgU w' ζ' := by
      intro n
      have : physMap 0 A τ (z n) ∈ (fun z : ℂ => z + src) '' imgU w' ζ' := by rw [hU]; exact ⟨z n, hzP n, rfl⟩
      obtain ⟨v, hv, hveq⟩ := this
      rw [hphys] at hveq
      have : u n = v := by simp only [hu]; rw [← hveq]; ring
      rw [this]; exact hv
    obtain ⟨a, ha, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd huU
    have hUH : imgU w' ζ' ⊆ H := iUnion₂_subset fun t _ => fun z hz => hz.1
    have ha0 : 0 ≤ a.im :=
      closure_minimal (fun z hz => (hUH hz).le) (isClosed_le continuous_const continuous_im) ha
    have hzφ : Tendsto (z ∘ φ) atTop (𝓝 q) := hzq.comp hφ.tendsto_atTop
    have haim : a.im = 0 := by
      rcases ha0.lt_or_eq with hpos | h
      · exfalso
        set ω' : ℂ := a + src - A τ with hω'
        have hω'H : ω' ∈ H := by show 0 < ω'.im; simpa [hω'] using hpos
        have hf : Tendsto (fun n => fwdMap A τ (z (φ n))) atTop (𝓝 ω') := by
          have e : (fun n => fwdMap A τ (z (φ n))) = fun n => (u ∘ φ) n + src - A τ := by
            funext n; simp only [hu, Function.comp]; ring
          rw [e]; exact (hlim.add tendsto_const_nhds).sub tendsto_const_nhds
        have hF := ((RS.continuousAt_fwdMapInv hA hA0 hτ.le hω'H).tendsto).comp hf
        have heq : (fwdMapInv A τ ∘ fun n => fwdMap A τ (z (φ n))) = z ∘ φ := by
          funext n; exact RS.fwdMapInv_fwdMap hA hA0 hτ.le (hP₁K (hzP (φ n)))
        rw [heq] at hF
        have hq : q = fwdMapInv A τ ω' := tendsto_nhds_unique hzφ hF
        have hqH := RS.fwdMapInv_mem_compl_fwdHull hA hA0 hτ.le hω'H
        rw [← hq] at hqH
        rcases hqK with hqK | hqK
        · exact hqH.2 (closure_fwdHull_inter_H_subset hA hτ.le hqK hqH.1)
        · have : (0 : ℝ) < q.im := hqH.1
          linarith
      · exact h.symm
    have ha_eq : a = 0 := by
      have hare : a = ((a.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [haim])
      have hmem : ((a.re : ℝ) : ℂ) ∈ closure (imgU w' ζ') := by rw [← hare]; exact ha
      rw [hare, hreal a.re hmem]; simp
    rw [ha_eq] at hlim
    -- a positive time before contact
    obtain ⟨s₁, hs₁c, hs₁pos⟩ : ∃ s : ℝ≥0, (s : ℝ≥0∞) < c ∧ 0 < s := by
      have h0 := hzP 0
      simp only [preHulls, mem_iUnion] at h0
      obtain ⟨s, hs, hzs⟩ := h0
      refine ⟨s, hs, ?_⟩
      rcases eq_or_lt_of_le (zero_le (a := s)) with h | h
      · exfalso
        have hzH := physHull_subset_H y _ s hzs
        obtain ⟨_, ⟨r, hr, rfl⟩, he⟩ := physHull_subset_trace hγc hγ0 hlt hη himg (hs.trans_le hcζ) hzs
        have hr0 : r = 0 := le_antisymm (h ▸ hr.2) (zero_le (a := r))
        rw [← he, hr0, hη.1] at hzH
        have : (0 : ℝ) < ((0 : ℂ) + y).im := hzH
        simp at this
      · exact h
    -- `q` lies in the translated trace up to every small positive time before contact
    have hqs : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < c → q ∈ (fun z : ℂ => z + y) '' (η '' Icc 0 s) := by
      intro s hs0 hsc
      have hsζ : (s : ℝ≥0∞) < ζ₁ := hsc.trans_le hcζ
      have hclk0 : 0 < clk s := by
        have h0mem : (0 : ℝ) ∈ {r : ℝ | 0 ≤ r ∧ ENNReal.ofReal r < c} :=
          ⟨le_rfl, by rw [ENNReal.ofReal_zero]; exact (zero_le (a := (s : ℝ≥0∞))).trans_lt hsc⟩
        have hsmem : (s : ℝ) ∈ {r : ℝ | 0 ≤ r ∧ ENNReal.ofReal r < c} :=
          ⟨s.2, by rw [ENNReal.ofReal_coe_nnreal]; exact hsc⟩
        have := hch.2.2.1 h0mem hsmem (by exact_mod_cast hs0)
        rwa [hch.1] at this
      obtain ⟨δ, hδ, hδsub⟩ := hearly (clk s) hclk0
      have hev : ∀ᶠ n in atTop, z (φ n) ∈ physHull y (Strip.extPath w₁) s := by
        filter_upwards [hlim.eventually (ball_mem_nhds 0 hδ)] with n hn
        have hK' : u (φ n) ∈ fwdHull w' (clk s) := hδsub ⟨huU _, hn⟩
        have hmem : u (φ n) + src ∈ physMap 0 A τ '' physHull y (Strip.extPath w₁) s := by
          rw [hch.2.2.2.2 s hsc]; exact ⟨u (φ n), hK', rfl⟩
        obtain ⟨z', hz', hz'eq⟩ := hmem
        have hz'P : z' ∈ P₁ := by simp only [hP₁, preHulls, mem_iUnion]; exact ⟨s, hsc, hz'⟩
        have hff : fwdMap A τ z' = fwdMap A τ (z (φ n)) := by
          rw [hphys] at hz'eq; simp only [hu] at hz'eq; linear_combination hz'eq
        rw [← FwdHolo.injOn_fwdMap hA hτ.le (hP₁K hz'P) (hP₁K (hzP (φ n))) hff]
        exact hz'
      have hcl : IsClosed ((fun z : ℂ => z + y) '' (η '' Icc 0 s)) :=
        ((isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun r hr =>
          (ENNReal.coe_le_coe.2 hr.2).trans hsζ.le)).image (continuous_id.add continuous_const)).isClosed
      exact hcl.mem_of_tendsto hzφ
        (hev.mono fun n hn => physHull_subset_trace hγc hγ0 hlt hη himg hsζ hn)
    -- the early small hulls shrink to `y`
    apply hqy
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨δ, hδ, hδη⟩ := Metric.continuousWithinAt_iff.1
      (hη.2.1 0 (by show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₁; simp)) ε hε
    set s : ℝ≥0 := min s₁ ⟨δ / 2, by positivity⟩ with hs
    have hs0 : 0 < s := lt_min hs₁pos (by show (0 : ℝ) < δ / 2; positivity)
    have hsc : (s : ℝ≥0∞) < c := (ENNReal.coe_le_coe.2 (min_le_left _ _)).trans_lt hs₁c
    obtain ⟨_, ⟨r, hr, rfl⟩, he⟩ := hqs s hs0 hsc
    have hrδ : dist r 0 < δ := by
      have hrd : dist r 0 = (r : ℝ) := by simp [NNReal.dist_eq]
      rw [hrd]
      have : (r : ℝ) ≤ δ / 2 := (NNReal.coe_le_coe.2 (hr.2.trans (min_le_right _ _))).trans_eq rfl
      linarith
    have hrdom : r ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ₁} :=
      (ENNReal.coe_le_coe.2 hr.2).trans (hsc.trans_le hcζ).le
    have := hδη hrdom hrδ
    rw [hη.1, dist_zero_right] at this
    rw [← he, dist_eq_norm, add_sub_cancel_right]
    exact this.le

end Small

end InteractingSLE.ZhanGT4.A2TipSep
