import QuantumZipper.Blueprint.ComplexAnalysis
import QuantumZipper.Analysis.Holder
import QuantumZipper.Proofs.Loewner.ReverseHolo
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# JS-CHART (task R13): the two half-plane charts of the doubled hull

Blueprint `blueprint/EXT_JS_BLUEPRINT.md` §3 (the `IsChart` node, the C0/C1/D inputs) and
DECISIONS D6 (the Option B adapter `ae_removable_doubledHull`).

`IsChart K R F` records that `F` is a chart for `K` on the box `[-2R,2R] × [0,4R]`: continuous
there, holomorphic and injective on `ℍ = H`, and `F '' H ⊆ Kᶜ`. For a Carathéodory extension `F`
of the reverse Loewner map `revMap W T` we prove that `F` and its Schwarz reflection
`reflChart F` (`z ↦ conj (F (−conj z))`) are charts for the doubled hull
`Kd = closure K ∪ conj '' closure K` with `K = revHull W T`, and that `Kd` is covered by the
images of the real interval `[-R,R]` under the two charts, for all large enough `R`. The
reflection `reflChart` also preserves `IsHolderOn` on the closed box.

## Main statements

* `JS.IsChart` (structure), `JS.reflChart` (definition);
* `JS.charts_of_caratheodoryRevExt`;
* `JS.isHolderOn_reflChart`.

## Sources

* Schwarz reflection in the imaginary axis: `z ↦ conj (F (−conj z)) = (conj ∘ F ∘ conj) ∘ neg` is
  holomorphic where `F` is, since conjugation is an antiholomorphic involution
  (mathlib `DifferentiableAt.conj_conj`, `Mathlib/Analysis/Calculus/Deriv/Star.lean`);
  Ahlfors, *Complex Analysis*, 3rd ed., §4.6.5.
* The Carathéodory boundary correspondence of `Blueprint.IsCaratheodoryRevExt` (Pommerenke,
  *Boundary Behaviour of Conformal Maps*, Thm 2.1, Prop. 2.5) supplies the covering argument of
  EXT-JS §2/§3: `K ⊆ F '' (0₋,0₊)` because a point of the hull is hit by the (surjective)
  extension and cannot be hit from `ℍ`, and `closure K ⊆ F '' [0₋,0₊]` because the image of the
  compact interval is closed. Seeing that `F '' ℍ` misses `closure K` uses `IsSimpleCurveHull`;
  note `K` itself is **not** closed in general (it is an arc without its endpoint, e.g.
  `γ''Ioc 0 1`), and only `closure K ⊆ γ''Icc 0 1` is used.

**Deviation (statement).** `TASKS.md` R13 states `charts_of_caratheodoryRevExt` without any
continuity hypothesis on the driving function `W`; but holomorphy of `F` on `ℍ` can only come
from `F = revMap W T` on `ℍ`, and the repository's `differentiableOn_revMap`
(`Proofs/Loewner/ReverseHolo.lean:229`) requires `Continuous W`. We therefore add the hypothesis
`(hW : Continuous W)` and keep everything else verbatim. The consumers hold it a.s.
(`Blueprint.RevMapCaratheodory` takes `Continuous W` as a hypothesis).
-/

noncomputable section

open Set Metric
open scoped ComplexConjugate

namespace QuantumZipper
namespace JS

/-- A *chart* for a compact set `K` on the box `[-2R,2R] × [0,4R]`: a function continuous on
that box, holomorphic and injective on the upper half-plane, taking `ℍ` into the complement
of `K`. This is the notion of EXT-JS §2 ("a chart for `K` is `F : ℂ → ℂ`, continuous on
`B_R := [-2R,2R] ×ℂ [0,4R]`, holomorphic and injective on `ℍ`, with `F '' ℍ ⊆ Kᶜ`"). -/
structure IsChart (K : Set ℂ) (R : ℝ) (F : ℂ → ℂ) : Prop where
  pos : 0 < R
  cont : ContinuousOn F (Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R))
  holo : DifferentiableOn ℂ F H
  inj : InjOn F H
  mapsTo : MapsTo F H Kᶜ

/-- The Schwarz reflection of a chart `F` in the imaginary axis: `z ↦ conj (F (−conj z))`. Where
`F` is a conformal map of `ℍ`, this is the conformal map of the doubled domain obtained by
reflecting in `iℝ` and conjugating (EXT-JS §2, DECISIONS D6: the second chart of the pair
"`F` and `z ↦ conj (F (−conj z))`"). -/
def reflChart (F : ℂ → ℂ) : ℂ → ℂ := fun z => starRingEnd ℂ (F (-(starRingEnd ℂ) z))

/-! ### Conjugation and the reflection `z ↦ -conj z` -/

/-- Defining equation of `reflChart`, written with the `conj` notation. -/
theorem reflChart_apply (F : ℂ → ℂ) (z : ℂ) : reflChart F z = conj (F (-(conj z))) := by
  simp only [reflChart]

/-- The reflection `z ↦ -conj z` maps `ℍ` to itself. -/
theorem neg_conj_mem_H {z : ℂ} (hz : z ∈ H) : -(conj z) ∈ H := by
  simpa [H] using hz

/-- The reflection `z ↦ -conj z` maps `s ×ℂ [L,M]` to itself when `s` is stable under `t ↦ -t`
(it negates the real part and preserves the imaginary part). -/
theorem neg_conj_mem_reProdIm {s : Set ℝ} {L M : ℝ} {z : ℂ} (hs : ∀ t ∈ s, -t ∈ s)
    (hz : z ∈ s ×ℂ Icc L M) : -(conj z) ∈ s ×ℂ Icc L M := by
  rw [Complex.mem_reProdIm] at hz ⊢
  refine ⟨?_, ?_⟩
  · simpa using hs z.re hz.1
  · simpa using hz.2

/-- Conjugation permutes the doubled hull `A ∪ conj '' A`. -/
theorem conj_image_doubled (A : Set ℂ) :
    conj '' (A ∪ conj '' A) = A ∪ conj '' A := by
  ext w
  constructor
  · rintro ⟨z, hz | hz, rfl⟩
    · exact Or.inr ⟨z, hz, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := hz
      exact Or.inl (by simpa using hy)
  · rintro (hw | hw)
    · exact ⟨conj w, Or.inr ⟨w, hw, rfl⟩, by simp⟩
    · obtain ⟨y, hy, rfl⟩ := hw
      exact ⟨y, Or.inl hy, rfl⟩

/-! ### The reflection of a chart -/

/-- `reflChart F` is continuous wherever `F` is continuous on a set stable under `z ↦ -conj z`. -/
theorem continuousOn_reflChart {F : ℂ → ℂ} {s : Set ℂ} (hF : ContinuousOn F s)
    (hs : ∀ z ∈ s, -(conj z) ∈ s) : ContinuousOn (reflChart F) s := by
  have hg : ContinuousOn (fun z : ℂ => -(conj z)) s :=
    (continuous_neg.comp Complex.continuous_conj).continuousOn
  have h1 : ContinuousOn (fun z : ℂ => F (-(conj z))) s := hF.comp hg hs
  have h2 : ContinuousOn (fun z : ℂ => conj (F (-(conj z)))) s :=
    Complex.continuous_conj.comp_continuousOn h1
  exact h2.congr fun z _ => (reflChart_apply F z).symm

/-- **Schwarz reflection** (the analytic core of `reflChart`): if `F` is holomorphic on `ℍ`, so is
`reflChart F`. Indeed `reflChart F = (conj ∘ F ∘ conj) ∘ neg` and `conj ∘ F ∘ conj` is
holomorphic on `-ℍ` (`DifferentiableAt.conj_conj`). -/
theorem differentiableOn_reflChart {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F H) :
    DifferentiableOn ℂ (reflChart F) H := by
  intro z hz
  have hz' : -(conj z) ∈ H := neg_conj_mem_H hz
  have hd : DifferentiableAt ℂ (conj ∘ F ∘ conj) (-z) := by
    have h := (hF.differentiableAt (isOpen_H.mem_nhds hz')).conj_conj
    rwa [show conj (-(conj z)) = -z by simp] at h
  have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) z :=
    (differentiable_neg (𝕜 := ℂ)).differentiableAt
  have h2 : DifferentiableAt ℂ ((conj ∘ F ∘ conj) ∘ fun z : ℂ => -z) z :=
    (hd.hasFDerivAt.comp z hneg.hasFDerivAt).differentiableAt
  have heq : ((conj ∘ F ∘ conj) ∘ fun z : ℂ => -z) = reflChart F := by
    funext w
    simp [Function.comp_def, reflChart_apply]
  exact (heq ▸ h2).differentiableWithinAt

/-- `reflChart` preserves injectivity on `ℍ`. -/
theorem injOn_reflChart {F : ℂ → ℂ} (h : InjOn F H) : InjOn (reflChart F) H := by
  intro z hz w hw hzw
  have hz' : -(conj z) ∈ H := neg_conj_mem_H hz
  have hw' : -(conj w) ∈ H := neg_conj_mem_H hw
  have h3 : -(conj z) = -(conj w) := by
    refine h hz' hw' ?_
    have := congrArg conj hzw
    simpa [reflChart_apply] using this
  have h4 : conj z = conj w := by simpa using congrArg Neg.neg h3
  simpa using congrArg conj h4

/-- `reflChart` maps `ℍ` into the complement of a set `K` invariant under conjugation whenever
`F` does. -/
theorem mapsTo_reflChart {K : Set ℂ} {F : ℂ → ℂ} (h : MapsTo F H Kᶜ) (hK : conj '' K ⊆ K) :
    MapsTo (reflChart F) H Kᶜ := by
  intro z hz
  rw [mem_compl_iff]
  intro hc
  have h1 : F (-(conj z)) ∉ K := h (neg_conj_mem_H hz)
  exact h1 (by simpa [reflChart_apply] using hK ⟨reflChart F z, hc, rfl⟩)

/-! ### Properties of a Carathéodory extension -/

/-- A Carathéodory extension of `revMap W T` is injective on `ℍ`: the only identifications made
by `F` are the welding ones, and these only relate real points. -/
theorem injOn_of_caratheodoryRevExt {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ}
    (h : Blueprint.IsCaratheodoryRevExt W T F) : InjOn F H := by
  intro z hz w hw hzw
  rcases (h.2.2.2.2.2.2 z (show z ∈ Hbar from H_subset_Hbar hz)
    w (show w ∈ Hbar from H_subset_Hbar hw)).1 hzw with h1 | h1
  · exact h1
  · simp only [Blueprint.WeldingRel] at h1
    obtain ⟨s, -, h1 | h1⟩ := h1
    · exact absurd (h1.1 ▸ hz) (by simp [H])
    · exact absurd (h1.2 ▸ hw) (by simp [H])

/-- A Carathéodory extension of the reverse Loewner map is holomorphic on `ℍ` (it agrees there
with `revMap W T`). -/
theorem differentiableOn_of_caratheodoryRevExt {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ} (hW : Continuous W)
    (hT : 0 ≤ T) (h : Blueprint.IsCaratheodoryRevExt W T F) : DifferentiableOn ℂ F H :=
  (differentiableOn_revMap W hW hT).congr fun _ hz => (h.1 hz)

/-! ### The charts of the doubled hull -/

/-- **R13 (JS-CHART), the D6 adapter.** A Carathéodory extension `F` of the reverse Loewner map
at time `T` and its Schwarz reflection `reflChart F` are charts for the doubled hull
`Kd = closure K ∪ conj '' closure K`, `K = revHull W T`, covering `Kd` by the images of the real
interval `[-R,R]`, for every `R ≥ R₀ = max |0₋| |0₊| + 1`.

The covering uses the Carathéodory boundary correspondence: every point of the hull is the image
of a point of the real interval `(0₋, 0₊)` (EXT-JS §3), so `closure K ⊆ F '' [0₋,0₊] ⊆ F '' [-R,R]`;
reflecting gives the second half of the cover.

**Deviation (statement).** The hypothesis `(hW : Continuous W)` is not in the `TASKS.md` R13
statement; it is needed for holomorphy of `F = revMap W T` on `ℍ`
(`differentiableOn_revMap`, `Proofs/Loewner/ReverseHolo.lean:229`). -/
theorem charts_of_caratheodoryRevExt {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W) (hT : 0 < T)
    (hK : IsSimpleCurveHull (revHull W T)) {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt W T F) :
    let Kd := closure (revHull W T) ∪ starRingEnd ℂ '' closure (revHull W T)
    ∃ R₀ > 0, ∀ R ≥ R₀, IsChart Kd R F ∧ IsChart Kd R (reflChart F) ∧
      Kd ⊆ F '' ((↑) '' Set.Icc (-R) R) ∪ reflChart F '' ((↑) '' Set.Icc (-R) R) := by
  obtain ⟨γ, hγc, -, hγ0, hγH, hγK⟩ := hK
  have hFcar := hF
  obtain ⟨hFeq, hFcont, hFsurj, -, -, hFreal, hFinj⟩ := hF
  set a := zeroMinus W T with ha
  set b := zeroPlus W T with hb
  -- the arc `γ '' [0,1]` is closed, contains the hull, and lies in the closed upper half-plane
  have hclγ : IsClosed (γ '' Icc (0 : ℝ) 1) := (isCompact_Icc.image_of_continuousOn hγc).isClosed
  have hcl_sub : closure (revHull W T) ⊆ γ '' Icc (0 : ℝ) 1 := by
    rw [hγK]
    exact closure_minimal (image_mono Ioc_subset_Icc_self) hclγ
  have hHbar_sub : γ '' Icc (0 : ℝ) 1 ⊆ Hbar := by
    rintro z ⟨t, ht, rfl⟩
    rcases lt_or_eq_of_le ht.1 with ht0 | ht0
    · have hpos : (0 : ℝ) < (γ t).im := hγH t ⟨ht0, ht.2⟩
      exact hpos.le
    · rw [← ht0]
      exact le_of_eq hγ0.symm
  -- the hull is the image of the open interval `(0₋, 0₊)` under `F`
  have hKsub : revHull W T ⊆ F '' ((↑) '' Ioo a b) := by
    intro x hx
    have hxH : x ∈ H := by
      have h := hx
      rw [revHull, mem_sdiff] at h
      exact h.1
    have hxnot : x ∉ revMap W T '' H := by
      have h := hx
      rw [revHull, mem_sdiff] at h
      exact h.2
    obtain ⟨y, hyHbar, hyF⟩ := hFsurj (H_subset_Hbar hxH)
    have hynotH : y ∉ H := fun hyy => hxnot ⟨y, hyy, by rw [← hFeq hyy]; exact hyF⟩
    have hyreal : y.im = 0 := le_antisymm (not_lt.1 hynotH) hyHbar
    have hy_eq : ((y.re : ℝ) : ℂ) = y := Complex.ext rfl (by simp [hyreal])
    have hnotle : ¬ (y.re ≤ a ∨ b ≤ y.re) := by
      rintro (h | h)
      · have h1 : x.im = 0 := by
          have := (hFreal y.re).2 (Or.inl (ha ▸ h))
          rwa [hy_eq, hyF] at this
        exact absurd h1 (ne_of_gt hxH)
      · have h1 : x.im = 0 := by
          have := (hFreal y.re).2 (Or.inr (hb ▸ h))
          rwa [hy_eq, hyF] at this
        exact absurd h1 (ne_of_gt hxH)
    exact ⟨((y.re : ℝ) : ℂ),
      ⟨y.re, mem_Ioo.mpr ⟨lt_of_not_ge fun h => hnotle (Or.inl h),
        lt_of_not_ge fun h => hnotle (Or.inr h)⟩, rfl⟩,
      by rw [hy_eq, hyF]⟩
  -- the two structural facts about `F` that do not involve `R`
  have hFholo : DifferentiableOn ℂ F H := differentiableOn_of_caratheodoryRevExt hW hT.le hFcar
  have hFinjOn : InjOn F H := injOn_of_caratheodoryRevExt hFcar
  dsimp only
  set Kd := closure (revHull W T) ∪ starRingEnd ℂ '' closure (revHull W T) with hKd
  refine ⟨max (|a|) (|b|) + 1, by positivity, fun R hR => ?_⟩
  have hRpos : 0 < R := by
    have : (0 : ℝ) < max (|a|) (|b|) + 1 := by positivity
    linarith
  have haR : |a| ≤ R := by linarith [le_max_left (|a|) (|b|), hR]
  have hbR : |b| ≤ R := by linarith [le_max_right (|a|) (|b|), hR]
  -- image of the real interval `[-R,R]` and its conjugate
  have hSsub : ((↑) '' Icc (-R) R : Set ℂ) ⊆ Hbar := by
    rintro z ⟨t, ht, rfl⟩
    simp [Hbar]
  have hclS : IsClosed (F '' ((↑) '' Icc (-R) R : Set ℂ)) :=
    ((isCompact_Icc.image_of_continuousOn Complex.continuous_ofReal.continuousOn).image_of_continuousOn
      (hFcont.mono hSsub)).isClosed
  have hIoo_sub : ((↑) '' Ioo a b : Set ℂ) ⊆ ((↑) '' Icc (-R) R : Set ℂ) := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, ⟨by linarith [(abs_le.1 haR).1, ht.1], by linarith [(abs_le.1 hbR).2, ht.2]⟩, rfl⟩
  have hclHull : closure (revHull W T) ⊆ F '' ((↑) '' Icc (-R) R : Set ℂ) :=
    closure_minimal (hKsub.trans (image_mono hIoo_sub)) hclS
  have hreflImg : reflChart F '' ((↑) '' Icc (-R) R : Set ℂ)
      = (starRingEnd ℂ) '' (F '' ((↑) '' Icc (-R) R : Set ℂ)) := by
    have hA : (fun z : ℂ => -(conj z)) '' ((↑) '' Icc (-R) R : Set ℂ)
        = ((↑) '' Icc (-R) R : Set ℂ) := by
      ext w
      constructor
      · rintro ⟨s, ⟨t, ht, rfl⟩, hs⟩
        rw [← hs]
        exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp⟩
      · rintro ⟨t, ht, rfl⟩
        refine ⟨((-t : ℝ) : ℂ), ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩, ?_⟩
        simp
    have hcomp : reflChart F = (conj ∘ F) ∘ (fun z : ℂ => -(conj z)) := by
      funext w
      simp [Function.comp_def, reflChart_apply]
    calc reflChart F '' ((↑) '' Icc (-R) R : Set ℂ)
        = ((conj ∘ F) ∘ fun z : ℂ => -(conj z)) '' ((↑) '' Icc (-R) R : Set ℂ) := by
          rw [hcomp]
      _ = (conj ∘ F) '' ((fun z : ℂ => -(conj z)) '' ((↑) '' Icc (-R) R : Set ℂ)) :=
          Set.image_comp (conj ∘ F) (fun z : ℂ => -(conj z)) _
      _ = (conj ∘ F) '' ((↑) '' Icc (-R) R : Set ℂ) := by rw [hA]
      _ = conj '' (F '' ((↑) '' Icc (-R) R : Set ℂ)) := Set.image_comp conj F _
  have hconjHull : (starRingEnd ℂ) '' closure (revHull W T)
      ⊆ reflChart F '' ((↑) '' Icc (-R) R : Set ℂ) := by
    rw [hreflImg]
    exact image_mono hclHull
  have hcover : Kd ⊆ F '' ((↑) '' Icc (-R) R : Set ℂ)
      ∪ reflChart F '' ((↑) '' Icc (-R) R : Set ℂ) := by
    rw [hKd]
    exact union_subset (hclHull.trans subset_union_left) (hconjHull.trans subset_union_right)
  -- the `IsChart` fields
  have hbox : Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) ⊆ Hbar := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    exact hz.2.1
  have hboxinv : ∀ z ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R),
      -(conj z) ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := fun _ hz =>
    neg_conj_mem_reProdIm (s := Icc (-2 * R) (2 * R)) (L := 0) (M := 4 * R)
      (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩) hz
  have hKdconj : (starRingEnd ℂ) '' Kd ⊆ Kd := by
    rw [hKd, conj_image_doubled]
  have hMapsToF : MapsTo F H Kdᶜ := by
    intro z hz
    rw [mem_compl_iff]
    have hzH : 0 < (F z).im := by
      have h := im_le_im_revMap W hW z hz hT.le
      rw [← hFeq hz] at h
      exact lt_of_lt_of_le hz h
    have hnotRev : F z ∉ revHull W T := by
      rw [revHull]
      exact fun h => h.2 ⟨z, hz, (hFeq hz).symm⟩
    have hnotCl : F z ∉ closure (revHull W T) := by
      intro hc
      obtain ⟨t, ht, htz⟩ := hcl_sub hc
      rcases lt_or_eq_of_le ht.1 with ht0 | ht0
      · exact hnotRev (by rw [hγK]; exact ⟨t, ⟨ht0, ht.2⟩, htz⟩)
      · exact absurd (show (F z).im = 0 by rw [← htz, ← ht0]; exact hγ0) (ne_of_gt hzH)
    have hnotConj : F z ∉ (starRingEnd ℂ) '' closure (revHull W T) := by
      rintro ⟨w, hw, hwz⟩
      have hwHbar : w ∈ Hbar := hHbar_sub (hcl_sub hw)
      have hle : (F z).im ≤ 0 := by
        rw [← hwz]
        simpa [Hbar] using hwHbar
      linarith
    rw [hKd]
    exact fun hc => hc.elim hnotCl hnotConj
  refine ⟨⟨hRpos, hFcont.mono hbox, hFholo, hFinjOn, hMapsToF⟩,
    ⟨hRpos, continuousOn_reflChart (hFcont.mono hbox) hboxinv, differentiableOn_reflChart hFholo,
      injOn_reflChart hFinjOn, mapsTo_reflChart hMapsToF hKdconj⟩, hcover⟩

/-! ### Hölder continuity is preserved by the reflection -/

/-- `IsHolderOn` is preserved by the reflection `reflChart` on a box symmetric in the imaginary
axis: `z ↦ -conj z` is an isometry of the box and conjugation is isometric. -/
theorem isHolderOn_reflChart {F : ℂ → ℂ} {R : ℝ} (h : IsHolderOn F (Set.Icc (-R) R ×ℂ Set.Icc 0 R)) :
    IsHolderOn (reflChart F) (Set.Icc (-R) R ×ℂ Set.Icc 0 R) := by
  obtain ⟨α, C, hα, hC⟩ := h
  refine ⟨α, C, hα, fun z hz w hw => ?_⟩
  have hneg : ∀ t ∈ Icc (-R) R, -t ∈ Icc (-R) R :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hz' : -(conj z) ∈ Icc (-R) R ×ℂ Icc 0 R :=
    neg_conj_mem_reProdIm (s := Icc (-R) R) (L := 0) (M := R) hneg hz
  have hw' : -(conj w) ∈ Icc (-R) R ×ℂ Icc 0 R :=
    neg_conj_mem_reProdIm (s := Icc (-R) R) (L := 0) (M := R) hneg hw
  have hb := hC _ hz' _ hw'
  calc ‖reflChart F z - reflChart F w‖
      = ‖F (-(conj z)) - F (-(conj w))‖ := by
        rw [reflChart_apply, reflChart_apply, ← map_sub, Complex.norm_conj]
    _ ≤ C * ‖-(conj z) - -(conj w)‖ ^ α := hb
    _ = C * ‖z - w‖ ^ α := by
        have hkey : -(conj z) - -(conj w) = -(conj (z - w)) := by
          rw [map_sub]
          ring
        rw [hkey, norm_neg, Complex.norm_conj]

end JS
end QuantumZipper
