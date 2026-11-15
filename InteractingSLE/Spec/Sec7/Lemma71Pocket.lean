import InteractingSLE.Spec.Sec6.DrivingSimple

/-!
# Lemma 7.1: the mapped pocket segment is a simple path from `0` to `∞` (Remark 6.14, geometric part)

Packet PROVE-LEMMA71. Specification Remark 6.14 (`source/spec/p193-240.md` L478–L493, pp. 217–218) and the proof
of Lemma 7.1 (L580–L606, pp. 223–225).

Remark 6.14: "Let `ψ : C → ℍ` send `x₀` to zero and `y₀` to infinity. Its Jordan boundary homeomorphism makes
`ψ(η_C)` a continuous simple path from zero to infinity. … each closed set of times when the middle curve lies on
one outer curve is nowhere dense. Their union is nowhere dense on every compact interval. Consequently the mapped
segment does not spend a nontrivial interval on `ℝ`."

The segment `η_C = η|_{[σ_C, τ_C]}` lives on a time interval `[σ_C, τ_C)` (`τ_C` may be the terminal time at
`∞`). We read it on `[0, ∞)` through a continuous strictly increasing clock `φ` from `0` onto `[σ_C, τ_C)` and
transport it by a continuous injective `Ψ` (the boundary extension of `ψ`) on a set `E ⊇ η_C`, which maps `E` into
`ℍ̄`, the open pocket `C` into `ℍ`, the first endpoint `η(σ_C) = x₀` to `0`, and points near `y₀` near `∞`.

## Main results

* `interior_setOf_comp_mem_eq_empty`: a continuous strictly increasing clock pulls a set of times with empty
  interior back to a set with empty interior.
* **`mappedSegment_props`**: the mapped segment `u ↦ Ψ(η(φ(u)))` is continuous and injective on `[0, ∞)`, lies
  in `ℍ̄`, starts at `0`, tends to `∞`, and its real-boundary times have empty interior: exactly the geometric clause
  of `Lemma71MappedSegmentStatement` (`Lemma71Reduce.lean`).
* `interior_setOf_not_mem_eq_empty_of_contacts`: Remark 6.14's "each closed set of times when the middle curve
  lies on one outer curve is nowhere dense. Their union is nowhere dense": if the contact times with the two outer
  curves have empty interior, so do the times after `σ_C` at which the segment is outside the open pocket.
* The clocks: `segClock a b` (from `0` onto `[a, b)`, `b < ∞`) and `fun u => a + u` (onto `[a, ∞)`), with
  `mappedSegment_props_finite` (the segment ends at a finite time at `y₀`) and `mappedSegment_props_infinite`
  (`τ_C = ∞`: the segment ends at `∞`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.Lemma71

/-- A continuous strictly increasing clock on `[0, ∞)` pulls back a set of times `X` with empty interior to a set of
positive times with empty interior. -/
theorem interior_setOf_comp_mem_eq_empty {φ : ℝ → ℝ} {X : Set ℝ} (hφc : ContinuousOn φ (Ici 0))
    (hφm : StrictMonoOn φ (Ici 0)) (hX : interior X = ∅) :
    interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ φ u ∈ X} = ∅ := by
  by_contra hne
  obtain ⟨u, hu⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u hu
  have hu0 : 0 < u := (interior_subset hu).2.1
  set d := u + ε / 2 with hd
  have hud : u < d := by linarith
  have hsub : Icc u d ⊆ Ici 0 := fun v hv => le_trans hu0.le hv.1
  have hφud : φ u < φ d := hφm (show u ∈ Ici (0 : ℝ) from hu0.le) (hsub ⟨hud.le, le_rfl⟩) hud
  have hIoo : Ioo (φ u) (φ d) ⊆ X := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := intermediate_value_Icc hud.le (hφc.mono hsub) (Ioo_subset_Icc_self hy)
    have hvu : v ≠ u := by rintro rfl; exact lt_irrefl _ hy.1
    have hvd : v ≠ d := by rintro rfl; exact lt_irrefl _ hy.2
    have hvball : v ∈ ball u ε := by
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hv.1, hv.2]
    exact (interior_subset (hball hvball)).2.2
  have := interior_maximal hIoo isOpen_Ioo
  rw [hX, subset_empty_iff] at this
  exact (nonempty_Ioo.2 hφud).ne_empty this

/-- **The mapped pocket segment** (Remark 6.14, geometric part). Let `φ` be a continuous strictly increasing clock
on `[0, ∞)`, let the middle curve `η` be continuous and injective on the time interval `J = φ([0, ∞))` with values in
`E`, and let `Ψ` be continuous and injective on `E` with values in `ℍ̄`, mapping the open pocket `C` into `ℍ` and the
first endpoint `η(φ 0)` to `0`. If `η(φ u)` converges along `L` as `u → ∞` and `Ψ` sends `L`-neighbourhoods (within
`E`) to neighbourhoods of `∞` (`ψ(y₀) = ∞`), and the times after `φ 0` at which `η` is outside `C` have empty
interior, then `γ = Ψ ∘ η ∘ φ` is a continuous simple path in `ℍ̄` from `0` tending to `∞` whose real-boundary times
have empty interior. -/
theorem mappedSegment_props {η : ℝ → ℂ} {Ψ : ℂ → ℂ} {E C : Set ℂ} {φ : ℝ → ℝ} {L : Filter ℂ}
    (hφc : ContinuousOn φ (Ici 0)) (hφm : StrictMonoOn φ (Ici 0))
    (hc : ContinuousOn η (φ '' Ici 0)) (hinj : InjOn η (φ '' Ici 0))
    (hηE : MapsTo η (φ '' Ici 0) E) (hΨc : ContinuousOn Ψ E) (hΨi : InjOn Ψ E)
    (hΨE : MapsTo Ψ E Hbar) (hΨC : MapsTo Ψ C H) (h0 : Ψ (η (φ 0)) = 0)
    (hlim : Tendsto (fun u => η (φ u)) atTop L)
    (hΨL : Tendsto Ψ (L ⊓ 𝓟 E) (Bornology.cobounded ℂ))
    (hC : interior {t ∈ φ '' Ici 0 | φ 0 < t ∧ η t ∉ C} = ∅) :
    ContinuousOn (fun u => Ψ (η (φ u))) (Ici 0) ∧ InjOn (fun u => Ψ (η (φ u))) (Ici 0) ∧
      MapsTo (fun u => Ψ (η (φ u))) (Ici 0) Hbar ∧ Ψ (η (φ 0)) = 0 ∧
      Tendsto (fun u => ‖Ψ (η (φ u))‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Ψ (η (φ u))).im = 0} = ∅ := by
  have hφJ : MapsTo φ (Ici 0) (φ '' Ici 0) := mapsTo_image φ (Ici 0)
  have hηφ : ContinuousOn (fun u => η (φ u)) (Ici 0) := hc.comp hφc hφJ
  have hηφE : MapsTo (fun u => η (φ u)) (Ici 0) E := hηE.comp hφJ
  refine ⟨hΨc.comp hηφ hηφE, (hΨi.comp (hinj.comp hφm.injOn hφJ) hηφE), hΨE.comp hηφE, h0, ?_, ?_⟩
  · have hev : ∀ᶠ u in atTop, η (φ u) ∈ E :=
      (eventually_ge_atTop (0 : ℝ)).mono fun u hu => hηφE (show u ∈ Ici (0 : ℝ) from hu)
    have hcob : Tendsto (fun u => Ψ (η (φ u))) atTop (Bornology.cobounded ℂ) :=
      hΨL.comp (tendsto_inf.2 ⟨hlim, tendsto_principal.2 hev⟩)
    exact tendsto_norm_cobounded_atTop.comp hcob
  · have hsub : {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Ψ (η (φ u))).im = 0} ⊆
        {u ∈ Ici (0 : ℝ) | 0 < u ∧ φ u ∈ {t ∈ φ '' Ici 0 | φ 0 < t ∧ η t ∉ C}} := by
      rintro u ⟨hu, hu0, him⟩
      refine ⟨hu, hu0, ⟨u, hu, rfl⟩, hφm self_mem_Ici hu hu0, fun hC' => ?_⟩
      exact (show (0 : ℝ) < (Ψ (η (φ u))).im from hΨC hC').ne' him
    exact subset_empty_iff.1 ((interior_mono hsub).trans
      (interior_setOf_comp_mem_eq_empty hφc hφm hC).subset)

/-! ### The clocks -/

/-- The clock `u ↦ a + (b − a) u/(1 + u)` from `[0, ∞)` onto `[a, b)`. -/
def segClock (a b u : ℝ) : ℝ := a + (b - a) * (u / (1 + u))

theorem segClock_zero (a b : ℝ) : segClock a b 0 = a := by simp [segClock]

theorem continuousOn_segClock (a b : ℝ) : ContinuousOn (segClock a b) (Ici 0) := by
  refine continuousOn_const.add (continuousOn_const.mul (continuousOn_id.div
    (continuousOn_const.add continuousOn_id) fun u hu => ?_))
  have : (0 : ℝ) ≤ u := hu
  positivity

theorem strictMonoOn_segClock {a b : ℝ} (hab : a < b) : StrictMonoOn (segClock a b) (Ici 0) := by
  intro u hu v hv huv
  have hu' : (0 : ℝ) ≤ u := hu
  have hv' : (0 : ℝ) ≤ v := hv
  simp only [segClock]
  have h1 : u / (1 + u) < v / (1 + v) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : 0 < b - a := sub_pos.2 hab
  nlinarith

theorem segClock_lt {a b : ℝ} (hab : a < b) {u : ℝ} (hu : 0 ≤ u) : segClock a b u < b := by
  simp only [segClock]
  have h1 : u / (1 + u) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have h2 : 0 < b - a := sub_pos.2 hab
  nlinarith

theorem image_segClock {a b : ℝ} (hab : a < b) : segClock a b '' Ici 0 = Ico a b := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : (0 : ℝ) ≤ u := hu
    refine ⟨?_, segClock_lt hab hu'⟩
    simp only [segClock]
    have : 0 ≤ (b - a) * (u / (1 + u)) := mul_nonneg (sub_pos.2 hab).le (by positivity)
    linarith
  · rintro ⟨hat, htb⟩
    -- `u = (t − a)/(b − t)`
    have hbt : 0 < b - t := sub_pos.2 htb
    refine ⟨(t - a) / (b - t), div_nonneg (sub_nonneg.2 hat) hbt.le, ?_⟩
    simp only [segClock]
    have h1 : 1 + (t - a) / (b - t) = (b - a) / (b - t) := by field_simp; ring
    rw [h1, div_div_div_cancel_right₀ hbt.ne']
    field_simp [(sub_pos.2 hab).ne']
    ring

theorem tendsto_segClock {a b : ℝ} (hab : a < b) :
    Tendsto (segClock a b) atTop (𝓝[<] b) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, (eventually_ge_atTop 0).mono fun u hu => segClock_lt hab hu⟩
  have h : Tendsto (fun u : ℝ => u / (1 + u)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun u : ℝ => 1 - 1 / (1 + u)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_id))
    rw [sub_zero] at h2
    refine h2.congr' ((eventually_ge_atTop 0).mono fun u hu => ?_)
    have : (1 : ℝ) + u ≠ 0 := by positivity
    field_simp
    ring
  have := (tendsto_const_nhds (x := a)).add ((tendsto_const_nhds (x := b - a)).mul h)
  simp only [mul_one, add_sub_cancel] at this
  exact this

/-- **The mapped segment of a pocket traversed in finite time** (Remark 6.14; the segment `η|_{[σ, τ]}` ends at the
second endpoint `y₀ = η(τ)` at a finite time `τ`). Its clock is `segClock σ τ`, from `[0, ∞)` onto `[σ, τ)`. -/
theorem mappedSegment_props_finite {η : ℝ → ℂ} {Ψ : ℂ → ℂ} {E C : Set ℂ} {σ τ : ℝ} {y₀ : ℂ}
    (hστ : σ < τ) (hc : ContinuousOn η (Ico σ τ)) (hinj : InjOn η (Ico σ τ))
    (hηE : MapsTo η (Ico σ τ) E) (hΨc : ContinuousOn Ψ E) (hΨi : InjOn Ψ E)
    (hΨE : MapsTo Ψ E Hbar) (hΨC : MapsTo Ψ C H) (h0 : Ψ (η σ) = 0)
    (hlim : Tendsto η (𝓝[<] τ) (𝓝 y₀)) (hΨL : Tendsto Ψ (𝓝 y₀ ⊓ 𝓟 E) (Bornology.cobounded ℂ))
    (hC : interior {t ∈ Ico σ τ | σ < t ∧ η t ∉ C} = ∅) :
    ContinuousOn (fun u => Ψ (η (segClock σ τ u))) (Ici 0) ∧
      InjOn (fun u => Ψ (η (segClock σ τ u))) (Ici 0) ∧
      MapsTo (fun u => Ψ (η (segClock σ τ u))) (Ici 0) Hbar ∧ Ψ (η (segClock σ τ 0)) = 0 ∧
      Tendsto (fun u => ‖Ψ (η (segClock σ τ u))‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Ψ (η (segClock σ τ u))).im = 0} = ∅ := by
  have himg := image_segClock hστ
  have h0' : segClock σ τ 0 = σ := segClock_zero σ τ
  refine mappedSegment_props (continuousOn_segClock σ τ) (strictMonoOn_segClock hστ)
    (himg ▸ hc) (himg ▸ hinj) (himg ▸ hηE) hΨc hΨi hΨE hΨC (by rw [h0']; exact h0)
    (hlim.comp (tendsto_segClock hστ)) hΨL (by rw [himg, h0']; exact hC)

/-- **The mapped segment of a pocket whose second endpoint is `∞`** (Remark 6.14: "`τ_C` may be the terminal time
at infinity"). Its clock is `u ↦ σ + u`, from `[0, ∞)` onto `[σ, ∞)`, and the boundary map sends neighbourhoods of
`∞` in `E` to neighbourhoods of `∞`. -/
theorem mappedSegment_props_infinite {η : ℝ → ℂ} {Ψ : ℂ → ℂ} {E C : Set ℂ} {σ : ℝ}
    (hc : ContinuousOn η (Ici σ)) (hinj : InjOn η (Ici σ)) (hηE : MapsTo η (Ici σ) E)
    (hΨc : ContinuousOn Ψ E) (hΨi : InjOn Ψ E) (hΨE : MapsTo Ψ E Hbar) (hΨC : MapsTo Ψ C H)
    (h0 : Ψ (η σ) = 0) (hlim : Tendsto η atTop (Bornology.cobounded ℂ))
    (hΨL : Tendsto Ψ (Bornology.cobounded ℂ ⊓ 𝓟 E) (Bornology.cobounded ℂ))
    (hC : interior {t ∈ Ici σ | σ < t ∧ η t ∉ C} = ∅) :
    ContinuousOn (fun u => Ψ (η (σ + u))) (Ici 0) ∧ InjOn (fun u => Ψ (η (σ + u))) (Ici 0) ∧
      MapsTo (fun u => Ψ (η (σ + u))) (Ici 0) Hbar ∧ Ψ (η (σ + 0)) = 0 ∧
      Tendsto (fun u => ‖Ψ (η (σ + u))‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (Ψ (η (σ + u))).im = 0} = ∅ := by
  have himg : (fun u => σ + u) '' Ici 0 = Ici σ := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_Ici.2 (le_add_of_nonneg_right (mem_Ici.1 hu))
    · intro ht
      exact ⟨t - σ, mem_Ici.2 (sub_nonneg.2 (mem_Ici.1 ht)), by ring⟩
  have h0' : σ + 0 = σ := add_zero σ
  refine mappedSegment_props (φ := fun u => σ + u) (continuousOn_const.add continuousOn_id)
    (fun u _ v _ huv => by simpa using huv) (himg ▸ hc) (himg ▸ hinj) (himg ▸ hηE) hΨc hΨi hΨE hΨC
    (by rw [h0']; exact h0) (hlim.comp (tendsto_atTop_add_const_left _ σ tendsto_id)) hΨL
    (by rw [himg, h0']; exact hC)

/-! ### The times outside the pocket -/

/-- **Remark 6.14, the contact times** (p. 217: "each closed set of times when the middle curve lies on one outer curve
is nowhere dense. Their union is nowhere dense on every compact interval"). Let the segment `η` (continuous on the
time interval `J`) stay in the closure of the open pocket `C`, lie in `ℍ` after its first time `σ`, and let the
frontier of `C` lie on the outer curves `K₁ ∪ K₂` and the real line. If the contact times with `K₁` (closed) and with
`K₂` have empty interior, then so do the times after `σ` at which `η` is outside `C`: the last hypothesis of
`mappedSegment_props`. -/
theorem interior_setOf_not_mem_eq_empty_of_contacts {η : ℝ → ℂ} {C K₁ K₂ : Set ℂ} {J : Set ℝ} {σ : ℝ}
    (hc : ContinuousOn η J) (hCo : IsOpen C) (hK₁ : IsClosed K₁) (hηC : MapsTo η J (closure C))
    (hηH : ∀ t ∈ J, σ < t → η t ∈ H) (hfr : frontier C ⊆ (K₁ ∪ K₂) ∪ {z : ℂ | z.im = 0})
    (h₁ : interior {t ∈ J | η t ∈ K₁} = ∅) (h₂ : interior {t ∈ J | η t ∈ K₂} = ∅) :
    interior {t ∈ J | σ < t ∧ η t ∉ C} = ∅ := by
  have hsub : {t ∈ J | σ < t ∧ η t ∉ C} ⊆ {t ∈ J | η t ∈ K₁ ∪ K₂} := by
    rintro t ⟨ht, hσt, hC⟩
    refine ⟨ht, ?_⟩
    have hfrt : η t ∈ frontier C := ⟨hηC ht, by rwa [hCo.interior_eq]⟩
    rcases hfr hfrt with h | h
    · exact h
    · exact absurd h (show (0 : ℝ) < (η t).im from hηH t ht hσt).ne'
  exact subset_empty_iff.1 ((interior_mono hsub).trans
    (Sec6.interior_setOf_mem_union_eq_empty hc hK₁ h₁ h₂).subset)

end InteractingSLE.Sec7.Lemma71
