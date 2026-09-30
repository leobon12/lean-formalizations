import QuantumZipper.Proofs.Zipper.E6Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E6 without Palm-side measurability (1): the fixed-`ω` comparison for arbitrary integrands

Theorem 1.3, node E6 (Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.4, proof of Thm 1.8, pp. 70–72; the paper does not discuss measurability). Task E6-AEMEAS.

`E6Omega.lean` compares, for one boundary measure `μ`, the Palm integrals
`∫_{[−δ,0]} 1_hit X dμ` and `∫_{[−δ,0]} 1_hit Y dμ` of *measurable* `X`, `Y`. Here the same
comparison is proved for **arbitrary** (possibly non-measurable) `X`, `Y` bounded by `1`, with
`∫⁻` mathlib's (lower) Lebesgue integral, and without measurability of the collided set `hitS`:

* `e6_shf_le_nm`, `e6_le_shf_nm`: A6 (`e6_shf_both`) for arbitrary `g ≤ 1`. The direction
  `∫ g ≤ ∫ g ∘ shf + 2ℓ` uses a measurable minorant of `g` with the same integral
  (`exists_measurable_le_lintegral_eq`); the direction `∫ g ∘ shf ≤ ∫ g + 2ℓ` uses in addition
  that `shf` is injective on `[−δ, 0]` (it cuts exact length `ℓ` there, `shfM_len`) and has the
  monotone, hence measurable, left inverse `shfInv` (own elementary argument);
* `e6_omega_b_nm`, `e6_omega_a_nm`: `e6_omega_b`, `e6_omega_a` with the locality error merged into
  the integrand (no splitting of Palm integrals is needed).

Own elementary argument (no published source discusses this measurability point).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace QuantumZipper.E6

open PalmShift

variable {μ : Measure ℝ} {δ : ℝ}

/-- A monotone left inverse of `shf` on `[−δ, 0]`. -/
def shfInv (μ : Measure ℝ) (δ : ℝ) (ℓ : ℝ≥0) (y : ℝ) : ℝ :=
  sSup (insert (-δ) {x | x ∈ Icc (-δ) 0 ∧ shf μ δ ℓ x ≤ y})

section

variable (hδ : 0 < δ) (hatom : ∀ x, μ {x} = 0) (hpos : ∀ x y, x < y → 0 < μ (Ioo x y))
  (hfin : ∀ u v, μ (Icc u v) ≠ ∞) (ℓ : ℝ≥0)

include hatom hpos in
lemma shfM_mono : Monotone (shf μ δ ℓ) := by
  have : NullSingletonClass (padM μ δ) := padM_singleton hatom
  have hpos' := padM_pos (δ := δ) hpos
  have hℓ : (ℓ : ℝ≥0∞) ≤ padM μ δ (Iic (-δ - 1)) := padM_Iic _ ℓ
  intro u u' huu
  have hu : -δ - 1 < max u (-δ) := by linarith [le_max_right u (-δ)]
  have hu' : -δ - 1 < max u' (-δ) := by linarith [le_max_right u' (-δ)]
  have hm : max u (-δ) ≤ max u' (-δ) := max_le_max huu le_rfl
  refine (ps_le_iff hpos' hℓ hu _).mpr ?_
  refine le_trans (measure_mono (Icc_subset_Icc_right hm)) ?_
  exact (ps_le_iff hpos' hℓ hu' _).mp le_rfl

include hatom hpos hfin in
/-- On `[−δ, 0]` the shift cuts exactly `ℓ` of the padded measure. -/
lemma shfM_len {x : ℝ} (hx : x ∈ Icc (-δ) 0) :
    padM μ δ (Icc (shf μ δ ℓ x) x) = ℓ := by
  have : NullSingletonClass (padM μ δ) := padM_singleton hatom
  have hpos' := padM_pos (δ := δ) hpos
  have hℓ : (ℓ : ℝ≥0∞) ≤ padM μ δ (Iic (-δ - 1)) := padM_Iic _ ℓ
  have hx' : -δ - 1 < x := by linarith [hx.1]
  have hiff := ps_le_iff hpos' hℓ hx'
  rw [shf_eq hx ℓ]
  set t := palmShiftLeft (padM μ δ) ℓ x
  refine le_antisymm ((hiff t).mp le_rfl) ?_
  refine ps_le_Icc_left (a := t - 1) (by linarith) (padM_Icc_ne_top hfin _ _) fun y _ hyt => ?_
  exact lt_of_not_ge fun h => absurd ((hiff y).mpr h) (not_le.mpr hyt)

include hatom hpos hfin in
/-- `shf` is strictly monotone on `[−δ, 0]`. -/
lemma shfM_le_imp {x x₀ : ℝ} (hx : x ∈ Icc (-δ) 0) (hx₀ : x₀ ∈ Icc (-δ) 0)
    (h : shf μ δ ℓ x ≤ shf μ δ ℓ x₀) : x ≤ x₀ := by
  by_contra hlt
  push Not at hlt
  have heq : shf μ δ ℓ x = shf μ δ ℓ x₀ := le_antisymm h (shfM_mono hatom hpos ℓ hlt.le)
  have h1 := shfM_len hatom hpos hfin ℓ hx
  have h2 := shfM_len hatom hpos hfin ℓ hx₀
  rw [heq] at h1
  have ht : shf μ δ ℓ x₀ ≤ x₀ := shf_le hatom hpos ℓ hx₀
  have hdisj : Disjoint (Icc (shf μ δ ℓ x₀) x₀) (Ioo x₀ x) :=
    disjoint_left.mpr fun y hy1 hy2 => absurd hy1.2 (not_le.mpr hy2.1)
  have hsub : Icc (shf μ δ ℓ x₀) x₀ ∪ Ioo x₀ x ⊆ Icc (shf μ δ ℓ x₀) x := by
    intro y hy
    rcases hy with hy | hy
    · exact ⟨hy.1, hy.2.trans hlt.le⟩
    · exact ⟨ht.trans hy.1.le, hy.2.le⟩
  have hm := measure_mono (μ := padM μ δ) hsub
  rw [measure_union hdisj measurableSet_Ioo, h1, h2] at hm
  have hp : 0 < padM μ δ (Ioo x₀ x) := padM_pos hpos x₀ x hlt
  exact absurd hm (not_le.mpr (ENNReal.lt_add_right ENNReal.coe_ne_top hp.ne'))

include hδ in
lemma shfInv_mono : Monotone (shfInv μ δ ℓ) := by
  intro y y' hyy
  refine csSup_le_csSup ⟨0, ?_⟩ (insert_nonempty _ _)
    (insert_subset_insert fun x hx => ⟨hx.1, hx.2.trans hyy⟩)
  rintro x (rfl | hx)
  · linarith
  · exact hx.1.2

include hδ hatom hpos hfin in
lemma shfInv_shf {x : ℝ} (hx : x ∈ Icc (-δ) 0) : shfInv μ δ ℓ (shf μ δ ℓ x) = x := by
  refine le_antisymm (csSup_le (insert_nonempty _ _) ?_)
    (le_csSup ⟨0, ?_⟩ (mem_insert_of_mem _ ⟨hx, le_rfl⟩))
  · rintro y (rfl | hy)
    · exact hx.1
    · exact shfM_le_imp hatom hpos hfin ℓ hy.1 hx hy.2
  · rintro y (rfl | hy)
    · linarith
    · exact hy.1.2

include hδ hatom hpos hfin in
/-- **A6 for an arbitrary integrand**, direction `∫ g ∘ shf ≤ ∫ g + 2ℓ`. -/
lemma e6_shf_le_nm {g : ℝ → ℝ≥0∞} (hg1 : ∀ x, g x ≤ 1) :
    ∫⁻ x in Icc (-δ) 0, g (shf μ δ ℓ x) ∂μ ≤
      ∫⁻ x in Icc (-δ) 0, g x ∂μ + ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) := by
  obtain ⟨h, hhm, hle, heq⟩ :=
    exists_measurable_le_lintegral_eq (μ.restrict (Icc (-δ) 0)) (fun x => g (shf μ δ ℓ x))
  have hr : Measurable (shfInv μ δ ℓ) := (shfInv_mono hδ ℓ).measurable
  have hs := measurable_shf hδ hatom hpos ℓ
  set S : Set ℝ := {y | y = shf μ δ ℓ (shfInv μ δ ℓ y)} ∩ shfInv μ δ ℓ ⁻¹' Icc (-δ) 0 with hS
  have hSm : MeasurableSet S :=
    (measurableSet_eq_fun measurable_id (hs.comp hr)).inter (hr measurableSet_Icc)
  set k : ℝ → ℝ≥0∞ := S.indicator (fun y => min (h (shfInv μ δ ℓ y)) 1) with hk
  have hkm : Measurable k := ((hhm.comp hr).min measurable_const).indicator hSm
  have hkg : ∀ y, k y ≤ g y := by
    intro y
    by_cases hy : y ∈ S
    · rw [hk, indicator_of_mem hy]
      refine (min_le_left _ _).trans ((hle _).trans ?_)
      have e : shf μ δ ℓ (shfInv μ δ ℓ y) = y := hy.1.symm
      simp only [e, le_refl]
    · rw [hk, indicator_of_notMem hy]; exact zero_le
  have hk1 : ∀ y, k y ≤ ((1 : ℝ≥0) : ℝ≥0∞) := by
    intro y
    simp only [hk, indicator]
    split_ifs
    · simp
    · exact zero_le
  have hks : ∀ x ∈ Icc (-δ) 0, h x ≤ k (shf μ δ ℓ x) := by
    intro x hx
    have hrx : shfInv μ δ ℓ (shf μ δ ℓ x) = x := shfInv_shf hδ hatom hpos hfin ℓ hx
    have hmem : shf μ δ ℓ x ∈ S := ⟨by simp only [mem_ofPred_eq, hrx], by
      simp only [mem_preimage, hrx]; exact hx⟩
    rw [hk, indicator_of_mem hmem, hrx]
    exact le_min le_rfl ((hle x).trans (hg1 _))
  calc ∫⁻ x in Icc (-δ) 0, g (shf μ δ ℓ x) ∂μ = ∫⁻ x in Icc (-δ) 0, h x ∂μ := heq
    _ ≤ ∫⁻ x in Icc (-δ) 0, k (shf μ δ ℓ x) ∂μ := setLIntegral_mono' measurableSet_Icc hks
    _ ≤ ∫⁻ x in Icc (-δ) 0, k x ∂μ + ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) :=
        (e6_shf_both hδ hatom hpos hfin ℓ hkm hk1).1
    _ ≤ _ := add_le_add (lintegral_mono hkg) le_rfl

include hδ hatom hpos hfin in
/-- **A6 for an arbitrary integrand**, direction `∫ g ≤ ∫ g ∘ shf + 2ℓ`. -/
lemma e6_le_shf_nm {g : ℝ → ℝ≥0∞} (hg1 : ∀ x, g x ≤ 1) :
    ∫⁻ x in Icc (-δ) 0, g x ∂μ ≤
      ∫⁻ x in Icc (-δ) 0, g (shf μ δ ℓ x) ∂μ + ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) := by
  obtain ⟨h, hhm, hle, heq⟩ := exists_measurable_le_lintegral_eq (μ.restrict (Icc (-δ) 0)) g
  set k : ℝ → ℝ≥0∞ := fun x => min (h x) 1 with hk
  have hkm : Measurable k := hhm.min measurable_const
  have hkg : ∀ x, k x ≤ g x := fun x => (min_le_left _ _).trans (hle x)
  have hk1 : ∀ x, k x ≤ ((1 : ℝ≥0) : ℝ≥0∞) := fun x => by rw [ENNReal.coe_one]; exact min_le_right _ _
  calc ∫⁻ x in Icc (-δ) 0, g x ∂μ = ∫⁻ x in Icc (-δ) 0, h x ∂μ := heq
    _ = ∫⁻ x in Icc (-δ) 0, k x ∂μ :=
        lintegral_congr fun x => (min_eq_left ((hle x).trans (hg1 x))).symm
    _ ≤ ∫⁻ x in Icc (-δ) 0, k (shf μ δ ℓ x) ∂μ + ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) :=
        (e6_shf_both hδ hatom hpos hfin ℓ hkm hk1).2
    _ ≤ _ := add_le_add (lintegral_mono fun x => hkg _) le_rfl

lemma indicator_le_one' {s : Set ℝ} {F : ℝ → ℝ≥0∞} (hF : ∀ x, F x ≤ 1) (x : ℝ) :
    s.indicator F x ≤ 1 := by
  simp only [indicator]; split_ifs
  · exact hF x
  · exact zero_le

include hδ hatom hpos hfin in
/-- **`e6_omega_b` for arbitrary integrands**: if `X x ≤ Y y` whenever `y` is a collided point
left of `x` at `μ`-distance `ℓ`, then `∫ 1_hit X ≤ ∫ 1_hit Y + 2ℓ + badB`. -/
lemma e6_omega_b_nm (hitS : Set ℝ) (z : ℝ) (hhit : ∀ x ≤ 0, x ∈ hitS ↔ z < x)
    {X Y : ℝ → ℝ≥0∞} (hX1 : ∀ x, X x ≤ 1) (hY1 : ∀ x, Y x ≤ 1)
    (hkey : ∀ x ∈ Icc (-δ) 0, ∀ y, y ∈ hitS → -δ - 1 < y → y ≤ x → μ (Icc y x) = ℓ →
      X x ≤ Y y) :
    ∫⁻ x in Icc (-δ) 0, hitS.indicator X x ∂μ ≤
      ∫⁻ x in Icc (-δ) 0, hitS.indicator Y x ∂μ + ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) +
        badB μ δ ℓ := by
  set g := hitS.indicator Y with hgdef
  have hpt : ∀ x ∈ Icc (-δ) 0,
      hitS.indicator X x ≤ g (shf μ δ ℓ x) + (badSet μ δ ℓ z).indicator 1 x := by
    intro x hx
    by_cases hxh : x ∈ hitS
    · by_cases hb : x ∈ badSet μ δ ℓ z
      · rw [indicator_of_mem hxh, indicator_of_mem hb]
        exact (hX1 x).trans (le_add_left (by simp))
      · obtain ⟨h1, h2, h3, h4⟩ := e6_good_pt hatom hpos hfin ℓ hitS z hhit hx hb hxh
        rw [indicator_of_mem hxh, hgdef, indicator_of_mem h1]
        exact (hkey x hx _ h1 h2 h3 h4).trans le_self_add
    · rw [indicator_of_notMem hxh]; exact zero_le
  have hbm := measurableSet_badSet hδ hatom hpos ℓ z
  calc ∫⁻ x in Icc (-δ) 0, hitS.indicator X x ∂μ
      ≤ ∫⁻ x in Icc (-δ) 0, (g (shf μ δ ℓ x) + (badSet μ δ ℓ z).indicator 1 x) ∂μ :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ∫⁻ x in Icc (-δ) 0, g (shf μ δ ℓ x) ∂μ +
          ∫⁻ x in Icc (-δ) 0, (badSet μ δ ℓ z).indicator 1 x ∂μ :=
        lintegral_add_right _ (measurable_one.indicator hbm)
    _ ≤ _ := add_le_add (e6_shf_le_nm hδ hatom hpos hfin ℓ (indicator_le_one' hY1))
        (e6_bad_int hδ hatom hpos ℓ z)

include hδ hatom hpos hfin in
/-- **`e6_omega_a` for arbitrary integrands**: if `X y ≤ Y x` whenever `y` is a collided point
left of `x` at `μ`-distance `ℓ`, then `∫ 1_hit X ≤ ∫ 1_hit Y + 2ℓ + badB`. -/
lemma e6_omega_a_nm (hitS : Set ℝ) (z : ℝ) (hhit : ∀ x ≤ 0, x ∈ hitS ↔ z < x)
    {X Y : ℝ → ℝ≥0∞} (hX1 : ∀ x, X x ≤ 1)
    (hkey : ∀ x ∈ Icc (-δ) 0, ∀ y, y ∈ hitS → -δ - 1 < y → y ≤ x → μ (Icc y x) = ℓ →
      X y ≤ Y x) :
    ∫⁻ x in Icc (-δ) 0, hitS.indicator X x ∂μ ≤
      ∫⁻ x in Icc (-δ) 0, hitS.indicator Y x ∂μ + ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) +
        badB μ δ ℓ := by
  have hpt : ∀ x ∈ Icc (-δ) 0, hitS.indicator X (shf μ δ ℓ x) ≤
      hitS.indicator Y x + (badSet μ δ ℓ z).indicator 1 x := by
    intro x hx
    by_cases hxh : x ∈ hitS
    · by_cases hb : x ∈ badSet μ δ ℓ z
      · rw [indicator_of_mem hb]
        exact ((indicator_le_one' hX1 _).trans (by simp)).trans le_add_self
      · obtain ⟨h1, h2, h3, h4⟩ := e6_good_pt hatom hpos hfin ℓ hitS z hhit hx hb hxh
        rw [indicator_of_mem h1, indicator_of_mem hxh]
        exact (hkey x hx _ h1 h2 h3 h4).trans le_self_add
    · have hy : shf μ δ ℓ x ∉ hitS := by
        intro hy
        have hyx := shf_le hatom hpos ℓ hx
        have := (hhit _ (hyx.trans hx.2)).mp hy
        exact hxh ((hhit x hx.2).mpr (this.trans_le hyx))
      rw [indicator_of_notMem hy]; exact zero_le
  have hbm := measurableSet_badSet hδ hatom hpos ℓ z
  calc ∫⁻ x in Icc (-δ) 0, hitS.indicator X x ∂μ
      ≤ ∫⁻ x in Icc (-δ) 0, hitS.indicator X (shf μ δ ℓ x) ∂μ +
          ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) :=
        e6_le_shf_nm hδ hatom hpos hfin ℓ (indicator_le_one' hX1)
    _ ≤ (∫⁻ x in Icc (-δ) 0, hitS.indicator Y x ∂μ +
          ∫⁻ x in Icc (-δ) 0, (badSet μ δ ℓ z).indicator 1 x ∂μ) +
          ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) := by
        refine add_le_add ((setLIntegral_mono' measurableSet_Icc hpt).trans_eq ?_) le_rfl
        exact lintegral_add_right _ (measurable_one.indicator hbm)
    _ ≤ (∫⁻ x in Icc (-δ) 0, hitS.indicator Y x ∂μ + badB μ δ ℓ) +
          ENNReal.ofReal (2 * ℓ * (1 : ℝ≥0)) :=
        add_le_add (add_le_add le_rfl (e6_bad_int hδ hatom hpos ℓ z)) le_rfl
    _ = _ := by ring

end

end QuantumZipper.E6
