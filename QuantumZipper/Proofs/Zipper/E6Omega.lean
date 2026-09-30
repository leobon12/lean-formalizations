import QuantumZipper.Proofs.Zipper.E6Basic

/-!
# E6: the fixed-`ω` comparison of the Palm integrals

For one boundary measure `μ = ν_ω` (atomless, positive on intervals, locally finite), the set of
collided points `hitS` (`x ≤ 0` is collided iff `z < x`, `z = zeroMinus V T`), and the shift
`x ↦ x_ℓ` of the padded measure (`E6Basic`), we compare
`∫_{[−δ,0]} 1_{hit} X dμ` with `∫_{[−δ,0]} 1_{hit} Y dμ` when `X` at `x` is controlled by `Y`
(and a locality error `I`) at `x_ℓ` or conversely (`e6_omega_b`, `e6_omega_a`). The errors are
two A6 costs `2ℓ` and the bad mass `ℓ + 1{μ[−δ−1,−δ] ≤ ℓ} μ[−δ,0]` of `e6_bad_le`.
Blueprint §E6 (own formalization of the blueprint's argument).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace QuantumZipper.E6

open PalmShift

variable {μ : Measure ℝ} {δ : ℝ}

/-- The shift, frozen to the left of `−δ` (it agrees with `x_ℓ` on `[−δ, ∞)` and is monotone). -/
def shf (μ : Measure ℝ) (δ : ℝ) (ℓ : ℝ≥0) (x : ℝ) : ℝ := palmShiftLeft (padM μ δ) ℓ (max x (-δ))

/-- The error term `ℓ + 1{μ[−δ−1,−δ] ≤ ℓ} μ[−δ,0]`. -/
def badB (μ : Measure ℝ) (δ : ℝ) (ℓ : ℝ≥0) : ℝ≥0∞ :=
  ℓ + {m : ℝ≥0∞ | m ≤ ℓ}.indicator (fun _ => μ (Icc (-δ) 0)) (μ (Icc (-δ - 1) (-δ)))

section

variable (hδ : 0 < δ) (hatom : ∀ x, μ {x} = 0) (hpos : ∀ x y, x < y → 0 < μ (Ioo x y))
  (hfin : ∀ u v, μ (Icc u v) ≠ ∞) (ℓ : ℝ≥0)

include hδ hatom hpos in
lemma measurable_shf : Measurable (shf μ δ ℓ) := by
  haveI : NullSingletonClass (padM μ δ) := padM_singleton hatom
  have hpos' := padM_pos (δ := δ) hpos
  have hℓ : (ℓ : ℝ≥0∞) ≤ padM μ δ (Iic (-δ - 1)) := padM_Iic _ ℓ
  refine Monotone.measurable fun u u' huu => ?_
  have hu : -δ - 1 < max u (-δ) := by linarith [le_max_right u (-δ)]
  have hu' : -δ - 1 < max u' (-δ) := by linarith [le_max_right u' (-δ)]
  have hm : max u (-δ) ≤ max u' (-δ) := max_le_max huu le_rfl
  refine (ps_le_iff hpos' hℓ hu _).mpr ?_
  refine le_trans (measure_mono (Icc_subset_Icc_right hm)) ?_
  exact (ps_le_iff hpos' hℓ hu' _).mp le_rfl

lemma shf_eq {x : ℝ} (hx : x ∈ Icc (-δ) 0) (ℓ : ℝ≥0) :
    shf μ δ ℓ x = palmShiftLeft (padM μ δ) ℓ x := by
  rw [shf, max_eq_left hx.1]

include hδ hatom hpos hfin in
/-- A6 in `ℝ≥0∞` form for `shf` (both directions). -/
lemma e6_shf_both {g : ℝ → ℝ≥0∞} (hg : Measurable g) {M : ℝ≥0} (hgM : ∀ x, g x ≤ M) :
    (∫⁻ x in Icc (-δ) 0, g (shf μ δ ℓ x) ∂μ ≤
        ∫⁻ x in Icc (-δ) 0, g x ∂μ + ENNReal.ofReal (2 * ℓ * M)) ∧
      (∫⁻ x in Icc (-δ) 0, g x ∂μ ≤
        ∫⁻ x in Icc (-δ) 0, g (shf μ δ ℓ x) ∂μ + ENNReal.ofReal (2 * ℓ * M)) := by
  have he : ∫⁻ x in Icc (-δ) 0, g (shf μ δ ℓ x) ∂μ =
      ∫⁻ x in Icc (-δ) 0, g (palmShiftLeft (padM μ δ) ℓ x) ∂μ :=
    setLIntegral_congr_fun measurableSet_Icc fun x hx => by rw [shf_eq hx]
  rw [he]
  exact e6_shift_both hδ hatom hpos hfin ℓ hg hgM

/-- Bad points and their mass. -/
def badSet (μ : Measure ℝ) (δ : ℝ) (ℓ : ℝ≥0) (z : ℝ) : Set ℝ :=
  {x | x ∈ Icc (-δ) 0 ∧ z < x ∧ ¬ (z < shf μ δ ℓ x ∧ -δ - 1 < shf μ δ ℓ x)}

include hδ hatom hpos in
lemma measurableSet_badSet (z : ℝ) : MeasurableSet (badSet μ δ ℓ z) := by
  have hs := measurable_shf hδ hatom hpos ℓ
  refine measurableSet_Icc.inter ((measurableSet_lt measurable_const measurable_id).inter ?_)
  exact ((measurableSet_lt measurable_const hs).inter (measurableSet_lt measurable_const hs)).compl

include hδ hatom hpos in
lemma e6_bad_int (z : ℝ) :
    ∫⁻ x in Icc (-δ) 0, (badSet μ δ ℓ z).indicator 1 x ∂μ ≤ badB μ δ ℓ := by
  rw [lintegral_indicator_one (measurableSet_badSet hδ hatom hpos ℓ z)]
  refine (Measure.restrict_apply_le _ _).trans ?_
  refine le_trans (measure_mono fun x hx => ?_) (e6_bad_le hatom hpos ℓ z)
  obtain ⟨hxI, hzx, hb⟩ := hx
  exact ⟨hxI, hzx, by rwa [← shf_eq hxI]⟩

include hatom hpos in
lemma shf_le {x : ℝ} (hx : x ∈ Icc (-δ) 0) : shf μ δ ℓ x ≤ x := by
  haveI : NullSingletonClass (padM μ δ) := padM_singleton hatom
  have hℓ : (ℓ : ℝ≥0∞) ≤ padM μ δ (Iic (-δ - 1)) := padM_Iic _ ℓ
  rw [shf_eq hx]
  exact (ps_le_iff (padM_pos hpos) hℓ (by linarith [hx.1]) x).mpr
    (by rw [ps_Icc_of_le le_rfl]; exact zero_le)

include hatom hpos hfin in
/-- The pointwise facts at a good point: `y = x_ℓ` is collided, left of `x`, and cuts `ℓ`. -/
lemma e6_good_pt (hitS : Set ℝ) (z : ℝ) (hhit : ∀ x ≤ 0, x ∈ hitS ↔ z < x) {x : ℝ}
    (hx : x ∈ Icc (-δ) 0) (hbad : x ∉ badSet μ δ ℓ z) (hxh : x ∈ hitS) :
    shf μ δ ℓ x ∈ hitS ∧ -δ - 1 < shf μ δ ℓ x ∧ shf μ δ ℓ x ≤ x ∧
      μ (Icc (shf μ δ ℓ x) x) = ℓ := by
  have hzx := (hhit x hx.2).mp hxh
  have hg : z < shf μ δ ℓ x ∧ -δ - 1 < shf μ δ ℓ x := by
    by_contra h; exact hbad ⟨hx, hzx, h⟩
  have hxx : -δ - 1 < x := by linarith [hx.1]
  rw [shf_eq hx] at hg ⊢
  obtain ⟨h1, h2⟩ := e6_shift_len hatom hpos hfin ℓ hxx hg.2
  exact ⟨(hhit _ (h1.trans hx.2)).mpr hg.1, hg.2, h1, h2⟩

end

end QuantumZipper.E6
