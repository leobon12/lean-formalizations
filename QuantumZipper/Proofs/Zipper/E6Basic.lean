import QuantumZipper.Proofs.Abstract.PalmShift
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# E6 (length stationarity of `P_*`): deterministic Palm-shift inputs

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §E6. Paper: Sheffield, *Conformal weldings of random
surfaces: SLE and the quantum gravity zipper*, arXiv:1012.4797, proof of Theorem 1.8
(PDF p. 70: "Since x was sampled uniformly from quantum measure ... the SLE_κ decorated
(γ − 2/γ) quantum wedge must be invariant under the operation of unzipping by a fixed quantity
of quantum boundary length"). The paper gives no details; the ε-argument below is the
blueprint's (own argument, built on the in-project A6 `PalmShift.ps_det_left`).

For a measure `μ` on `ℝ` (the boundary measure `ν_ω`) we use the padded measure
`μ̃ := μ + Leb|_{(−∞, −δ−1]}` (blueprint: `ν̃ := ν + Leb|_{(−∞,−δ−1]}`), so that the left Palm
shift `x_ℓ` is always well defined, and prove, for fixed `ω`:
* `e6_shift_le`, `e6_le_shift`: the `ℝ≥0∞` form of A6 on `[−δ, 0]`;
* `e6_shift_len`: `μ[x_ℓ, x] = ℓ` when `x_ℓ > −δ − 1`;
* `e6_bad_le`: the `μ`-mass of the collided points `x ∈ (z, 0] ∩ [−δ, 0]` whose shift is not
  collided or leaves the padding-free zone is `≤ ℓ + 1{μ[−δ−1, −δ] ≤ ℓ} μ[−δ, 0]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace QuantumZipper.E6

open PalmShift

/-- The padded measure `μ̃ = μ + Leb|_{(−∞, −δ−1]}`. -/
def padM (μ : Measure ℝ) (δ : ℝ) : Measure ℝ := μ + volume.restrict (Iic (-δ - 1))

section Det

variable {μ : Measure ℝ} {δ : ℝ}

lemma padM_singleton (hatom : ∀ x, μ {x} = 0) : NullSingletonClass (padM μ δ) :=
  ⟨fun x => by simp [padM, hatom x]⟩

lemma padM_pos (hpos : ∀ x y, x < y → 0 < μ (Ioo x y)) :
    ∀ x y, x < y → 0 < padM μ δ (Ioo x y) := fun x y h =>
  (hpos x y h).trans_le (by simp [padM])

lemma padM_Iic (a : ℝ) (ℓ : ℝ≥0) : (ℓ : ℝ≥0∞) ≤ padM μ δ (Iic a) := by
  have : volume (Iic a ∩ Iic (-δ - 1)) = ∞ := by
    rw [Iic_inter_Iic]; exact Real.volume_Iic
  calc (ℓ : ℝ≥0∞) ≤ ∞ := le_top
    _ = volume.restrict (Iic (-δ - 1)) (Iic a) := by
        rw [Measure.restrict_apply measurableSet_Iic, this]
    _ ≤ padM μ δ (Iic a) := by simp [padM]

lemma padM_Icc_of_lt {y x : ℝ} (hy : -δ - 1 < y) : padM μ δ (Icc y x) = μ (Icc y x) := by
  have : Icc y x ∩ Iic (-δ - 1) = ∅ := by
    ext t; simp only [mem_inter_iff, mem_Icc, mem_Iic, mem_empty_iff_false, iff_false]
    intro h; linarith [h.1.1, h.2]
  simp [padM, Measure.restrict_apply measurableSet_Icc, this]

lemma padM_restrict (hδ : 0 < δ) :
    (padM μ δ).restrict (Icc (-δ) 0) = μ.restrict (Icc (-δ) 0) := by
  have : Icc (-δ) 0 ∩ Iic (-δ - 1) = ∅ := by
    ext t; simp only [mem_inter_iff, mem_Icc, mem_Iic, mem_empty_iff_false, iff_false]
    intro h; linarith [h.1.1, h.2]
  rw [padM, Measure.restrict_add, Measure.restrict_restrict measurableSet_Icc, this]
  simp

lemma padM_Icc_ne_top (hfin : ∀ u v, μ (Icc u v) ≠ ∞) (u v : ℝ) : padM μ δ (Icc u v) ≠ ∞ := by
  have h2 : volume.restrict (Iic (-δ - 1)) (Icc u v) ≠ ∞ := by
    rw [Measure.restrict_apply measurableSet_Icc]
    exact ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_left)
  simp only [padM, Measure.coe_add, Pi.add_apply]
  exact ENNReal.add_ne_top.mpr ⟨hfin u v, h2⟩

lemma le_padM (s : Set ℝ) : μ s ≤ padM μ δ s := by simp [padM]

/-- `ℝ≥0∞` bookkeeping: `|A − B| ≤ c` in `ℝ` gives `A ≤ B + c`. -/
lemma e6_le_of_abs {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞) {c : ℝ}
    (h : |A.toReal - B.toReal| ≤ c) : A ≤ B + ENNReal.ofReal c := by
  have h1 : A.toReal ≤ B.toReal + c := by linarith [(abs_le.mp h).2]
  calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
    _ ≤ ENNReal.ofReal (B.toReal + c) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal B.toReal + ENNReal.ofReal c := ENNReal.ofReal_add_le
    _ = B + ENNReal.ofReal c := by rw [ENNReal.ofReal_toReal hB]

/-- The `ℝ≥0∞` form of A6 on `[−δ, 0]` for one measure (both directions). -/
lemma e6_shift_both (hδ : 0 < δ) (hatom : ∀ x, μ {x} = 0)
    (hpos : ∀ x y, x < y → 0 < μ (Ioo x y)) (hfin : ∀ u v, μ (Icc u v) ≠ ∞) (ℓ : ℝ≥0)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {M : ℝ≥0} (hgM : ∀ x, g x ≤ M) :
    (∫⁻ x in Icc (-δ) 0, g (palmShiftLeft (padM μ δ) ℓ x) ∂μ ≤
        ∫⁻ x in Icc (-δ) 0, g x ∂μ + ENNReal.ofReal (2 * ℓ * M)) ∧
      (∫⁻ x in Icc (-δ) 0, g x ∂μ ≤
        ∫⁻ x in Icc (-δ) 0, g (palmShiftLeft (padM μ δ) ℓ x) ∂μ + ENNReal.ofReal (2 * ℓ * M)) := by
  set μ' := padM μ δ with hμ'
  haveI : NullSingletonClass μ' := padM_singleton hatom
  have hpos' := padM_pos (δ := δ) hpos
  have hℓ : (ℓ : ℝ≥0∞) ≤ μ' (Iic (-δ)) := padM_Iic _ ℓ
  set T₁ : ℝ → ℝ := fun x => ⨅ q : ℚ, if μ' (Icc (q : ℝ) x) ≤ ℓ then (q : ℝ) else x with hT₁d
  have hT₁ : Measurable T₁ := by
    refine Measurable.iInf fun q => Measurable.ite ?_ measurable_const measurable_id
    have hmono : Monotone fun x : ℝ => μ' (Icc (q : ℝ) x) := fun x y h =>
      measure_mono (Icc_subset_Icc_right h)
    exact measurableSet_le hmono.measurable measurable_const
  have hT : ∀ x, -δ < x → T₁ x = palmShiftLeft μ' ℓ x := fun x hx => ps_hat_eq hpos' hℓ hx
  have hG : Measurable fun x => (g x).toReal := hg.ennreal_toReal
  have hGM : ∀ x, |(g x).toReal| ≤ (M : ℝ) := fun x => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal M.2 (by simpa using hgM x)
  have hdet := ps_det_left (μ := μ') hpos' hℓ (padM_Icc_ne_top hfin (-δ) 0) hT₁ hT hG hGM
  have hR := padM_restrict (μ := μ) hδ
  -- rewrite the real integrals as lintegrals
  have hfinI : μ' (Icc (-δ) 0) ≠ ∞ := padM_Icc_ne_top hfin _ _
  have hlt : ∀ f : ℝ → ℝ≥0∞, (∀ x, f x ≤ M) → ∫⁻ x in Icc (-δ) 0, f x ∂μ' ≠ ∞ := by
    intro f hf
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := M)) hfinI) ?_
    calc ∫⁻ x in Icc (-δ) 0, f x ∂μ' ≤ ∫⁻ _ in Icc (-δ) 0, (M : ℝ≥0∞) ∂μ' := lintegral_mono hf
      _ = M * μ' (Icc (-δ) 0) := by rw [setLIntegral_const]
  have hconv : ∀ f : ℝ → ℝ≥0∞, Measurable f → (∀ x, f x ≤ M) →
      ∫ x in Icc (-δ) 0, (f x).toReal ∂μ' = (∫⁻ x in Icc (-δ) 0, f x ∂μ').toReal := by
    intro f hf hfM
    rw [integral_toReal hf.aemeasurable
      (ae_of_all _ fun x => (hfM x).trans_lt ENNReal.coe_lt_top)]
  have hA := hconv (fun x => g (T₁ x)) (hg.comp hT₁) (fun x => hgM _)
  have hB := hconv g hg hgM
  rw [hA, hB] at hdet
  have hne1 := hlt (fun x => g (T₁ x)) (fun x => hgM _)
  have hne2 := hlt g hgM
  -- `T₁ = x_ℓ` a.e. on `[−δ, 0]`
  have hae : ∫⁻ x in Icc (-δ) 0, g (T₁ x) ∂μ' =
      ∫⁻ x in Icc (-δ) 0, g (palmShiftLeft μ' ℓ x) ∂μ' := by
    refine lintegral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    have hne : ∀ᵐ x ∂μ', x ≠ -δ := by
      rw [ae_iff]; simp
    filter_upwards [hne] with x hx hxI
    rw [hT x (lt_of_le_of_ne hxI.1 (Ne.symm hx))]
  have e1 : ∀ f : ℝ → ℝ≥0∞, ∫⁻ x in Icc (-δ) 0, f x ∂μ' = ∫⁻ x in Icc (-δ) 0, f x ∂μ := by
    intro f; rw [hR]
  rw [hae, e1, e1] at hdet
  rw [hae, e1] at hne1
  rw [e1] at hne2
  refine ⟨e6_le_of_abs hne1 hne2 hdet, e6_le_of_abs hne2 hne1 ?_⟩
  rwa [abs_sub_comm]

/-- The Palm shift of `x ∈ (−δ−1, ∞)` lies to the left of `x`, and cuts length exactly `ℓ` when
it stays in `(−δ − 1, ∞)`. -/
lemma e6_shift_len (hatom : ∀ x, μ {x} = 0) (hpos : ∀ x y, x < y → 0 < μ (Ioo x y))
    (hfin : ∀ u v, μ (Icc u v) ≠ ∞) (ℓ : ℝ≥0) {x : ℝ} (hx : -δ - 1 < x)
    (hs : -δ - 1 < palmShiftLeft (padM μ δ) ℓ x) :
    palmShiftLeft (padM μ δ) ℓ x ≤ x ∧ μ (Icc (palmShiftLeft (padM μ δ) ℓ x) x) = ℓ := by
  set μ' := padM μ δ
  haveI : NullSingletonClass μ' := padM_singleton hatom
  have hpos' := padM_pos (δ := δ) hpos
  have hℓ : (ℓ : ℝ≥0∞) ≤ μ' (Iic (-δ - 1)) := padM_Iic _ ℓ
  set t := palmShiftLeft μ' ℓ x
  have hiff := ps_le_iff hpos' hℓ hx
  have htx : t ≤ x := (hiff x).mpr (by rw [ps_Icc_of_le le_rfl]; exact zero_le)
  refine ⟨htx, ?_⟩
  rw [← padM_Icc_of_lt (μ := μ) hs]
  refine le_antisymm ((hiff t).mp le_rfl) ?_
  refine ps_le_Icc_left (a := t - 1) (by linarith) (padM_Icc_ne_top hfin _ _) fun y _ hyt => ?_
  exact lt_of_not_ge fun h => absurd ((hiff y).mpr h) (not_le.mpr hyt)

/-- Bad points: collided points of `[−δ, 0]` whose shift is not collided, or leaves the
padding-free zone `(−δ−1, ∞)`. -/
lemma e6_bad_le (hatom : ∀ x, μ {x} = 0) (hpos : ∀ x y, x < y → 0 < μ (Ioo x y))
    (ℓ : ℝ≥0) (z : ℝ) :
    μ {x | x ∈ Icc (-δ) 0 ∧ z < x ∧
        ¬ (z < palmShiftLeft (padM μ δ) ℓ x ∧ -δ - 1 < palmShiftLeft (padM μ δ) ℓ x)} ≤
      ℓ + {m : ℝ≥0∞ | m ≤ ℓ}.indicator (fun _ => μ (Icc (-δ) 0)) (μ (Icc (-δ - 1) (-δ))) := by
  set μ' := padM μ δ
  haveI : NullSingletonClass μ' := padM_singleton hatom
  have hpos' := padM_pos (δ := δ) hpos
  have hℓ : (ℓ : ℝ≥0∞) ≤ μ' (Iic (-δ - 1)) := padM_Iic _ ℓ
  set S1 := {x | x ∈ Ioc z 0 ∧ μ' (Icc z x) ≤ ℓ}
  set S2 : Set ℝ := if μ (Icc (-δ - 1) (-δ)) ≤ ℓ then Icc (-δ) 0 else ∅
  have hsub : {x | x ∈ Icc (-δ) 0 ∧ z < x ∧
      ¬ (z < palmShiftLeft μ' ℓ x ∧ -δ - 1 < palmShiftLeft μ' ℓ x)} ⊆ S1 ∪ S2 := by
    rintro x ⟨hxI, hzx, hbad⟩
    have hx : -δ - 1 < x := by linarith [hxI.1]
    have hiff := ps_le_iff hpos' hℓ hx
    rcases not_and_or.mp hbad with h | h
    · exact Or.inl ⟨⟨hzx, hxI.2⟩, (hiff z).mp (not_lt.mp h)⟩
    · have h2 : μ' (Icc (-δ - 1) x) ≤ ℓ := (hiff _).mp (not_lt.mp h)
      have h3 : μ (Icc (-δ - 1) (-δ)) ≤ ℓ :=
        ((le_padM _).trans (measure_mono (Icc_subset_Icc_right hxI.1))).trans h2
      right; simp only [S2, if_pos h3]; exact hxI
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
  · exact (le_padM _).trans (ps_window (μ := μ') (c := z) (b := 0)).1
  · simp only [S2, indicator, mem_setOf_eq]
    split_ifs <;> simp

end Det

end QuantumZipper.E6
