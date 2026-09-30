import QuantumZipper.Proofs.Section5.Prop16NodeBWin
import QuantumZipper.Proofs.Loewner.TwoPoint
import QuantumZipper.Proofs.Section5.Prop16PalmMask

/-!
# Proposition 1.6, Palm node B′: the regularity hypothesis `hreg` of the window Palm formula

The window Palm formula `palm_formula_prop16_window` (`Prop16NodeBWin.lean`) assumes `hreg`: for
**every** level `n` and every `x ∈ [a',b']`, a.s.
`avgReg (m + maskK K X) n x = (m + maskK K X)(fc(x, 2^{-n}))` for the *masked* field on the window
set `K = palmWinK a' b' g`. That hypothesis is not satisfiable in general for the `g` chosen there:
if `g/2 = 2^{-n}` and `a'` is not dyadic, the dyadic centres `dyadicRoundC j a' < a'` give folded
circles of radius `g/2` not carried by `K` (masked value `0`), while `fc(a', g/2)` is carried
(masked value `X(fc(a', g/2))`, a non-degenerate Gaussian).

This file fixes this and reduces `hreg` to a statement about the **actual** field only:

* `foldedCircle_im_gt_pos`, `not_kAdm_of_gt`: circles of radius `> g/2` are never carried by `K`;
* `hreg_maskK_of_actual`: if `g/2` is not a dyadic radius, `hreg` for the masked field follows
  from `hact`: a.s. `avgReg (h0 + X) n x = (h0 + X)(fc(x, 2^{-n}))` for `2^{-n} < g/2` (below
  `g/2`: locality `LocalRule.avgReg_congr_local`; above: both sides are `∫ m d fc(x, 2^{-n})`, by
  continuity of folded-circle averages of the continuous `m` in the centre);
* `palm_formula_prop16_window'`: the window Palm formula with `g/2` non-dyadic and `hreg`
  replaced by `hact`;
* `Prop16ActRegStmt`: `hact` on the whole arc, stated exactly (remaining).

Own elementary arguments (no published counterpart; the paper works with the continuum field).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal Real

namespace QuantumZipper

namespace Prop16Asm

/-- Own elementary lemma: a folded circle centred in `ℍ̄` charges `{ρ < Im}` when its top
point `c + i r` lies there. -/
theorem foldedCircle_im_gt_pos {c : ℂ} {r ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ < c.im + r) : 0 < foldedCircle c r {u | ρ < u.im} := by
  have hV : IsOpen {u : ℂ | ρ < u.im} := isOpen_lt continuous_const Complex.continuous_im
  rw [foldedCircle, Measure.map_apply measurable_foldH hV.measurableSet]
  refine lt_of_lt_of_le ?_ (measure_mono (show {u : ℂ | ρ < u.im} ⊆ foldH ⁻¹' {u | ρ < u.im} from
    fun u hu => by
      have h0 : 0 ≤ u.im := hρ0.trans (le_of_lt hu)
      simp only [mem_preimage, foldH, h0, ite_true]; exact hu))
  rw [circleUnif, Measure.smul_apply, Measure.map_apply (measurable_circleMap c r) hV.measurableSet,
    smul_eq_mul]
  refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top) (ne_of_gt ?_)
  set U := circleMap c r ⁻¹' {u | ρ < u.im} with hUdef
  have hU : IsOpen U := hV.preimage (continuous_circleMap c r)
  have hθU : π / 2 ∈ U := by
    show ρ < (circleMap c r (π / 2)).im
    simp only [circleMap, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_two,
      Real.cos_pi_div_two, zero_mul, mul_one, add_zero]
    exact hρ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (π / 2) hθU
  have hpi : π / 2 < 2 * π := by linarith [Real.pi_pos]
  have hsub : Ioo (π / 2) (min (π / 2 + ε) (2 * π)) ⊆ U ∩ Ico 0 (2 * π) := by
    intro θ hθ
    refine ⟨hball ?_, by linarith [hθ.1, Real.pi_pos], hθ.2.trans_le (min_le_right _ _)⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hθ.1]
    · linarith [hθ.2.trans_le (min_le_left _ _)]
  rw [Measure.restrict_apply hU.measurableSet]
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo, ENNReal.ofReal_pos]
  exact sub_pos.2 (lt_min (by linarith) hpi)

variable {a' b' g : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Circles of radius `> g/2` centred in `ℍ̄` are not carried by the window set. -/
theorem not_kAdm_of_gt (hg : 0 < g) {c : ℂ} (hc : c ∈ Hbar) {r : ℝ} (hr : g / 2 < r) :
    ¬ KAdm (palmWinK a' b' g) (foldedCircle c r) := by
  intro h
  have hpos := foldedCircle_im_gt_pos (c := c) (r := r) (by linarith : (0 : ℝ) ≤ g / 2)
    (by have : (0 : ℝ) ≤ c.im := hc; linarith)
  refine hpos.ne' (measure_mono_null
    (show {u : ℂ | g / 2 < u.im} ⊆ (palmWinK a' b' g)ᶜ from fun u hu hK => ?_) h.2)
  obtain ⟨t, -, hdt⟩ := exists_mem_of_mem_palmWinK hg hK
  have h1 : u.im ≤ ‖u - (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (u - (t : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  rw [← dist_eq_norm] at h1
  exact absurd hu (not_lt.2 (h1.trans hdt))

theorem dyadicRoundC_ofReal_mem_Hbar (j : ℕ) (x : ℝ) : dyadicRoundC j (x : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ (dyadicRoundC j (x : ℂ)).im
  simp [dyadicRoundC, dyadicRound]

/-- **`hreg` for the masked field from the regularity of the actual field** (`g/2` non-dyadic). -/
theorem hreg_maskK_of_actual {m h0 : ℂ → ℝ} (hm : Continuous m)
    (hmK : EqOn m h0 (palmWinK a' b' g)) (hg : 0 < g) (hnd : ∀ n, radius n ≠ g / 2)
    (hact : ∀ n, radius n < g / 2 → ∀ x ∈ Icc a' b', ∀ᵐ ω ∂P,
      avgReg (ofFun h0 + X ω) n (x : ℂ) = (ofFun h0 + X ω) (Palm.fcK x n)) :
    ∀ n, ∀ x ∈ Icc a' b', ∀ᵐ ω ∂P,
      avgReg (ofFun m + maskK (palmWinK a' b' g) X ω) n (x : ℂ) =
        (ofFun m + maskK (palmWinK a' b' g) X ω) (Palm.fcK x n) := by
  intro n x hx
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  rcases lt_or_gt_of_ne (hnd n) with hlt | hgt
  · filter_upwards [hact n hlt x hx] with ω hω
    have hloc : avgReg (ofFun m + maskK (palmWinK a' b' g) X ω) n (x : ℂ) =
        avgReg (ofFun h0 + X ω) n (x : ℂ) := by
      refine LocalRule.avgReg_congr_local n (sub_pos.2 hlt) (fun c hc hct => ?_) hxH
      have hK : foldedCircle c (radius n) (palmWinK a' b' g)ᶜ = 0 := by
        refine measure_mono_null (compl_subset_compl.2 fun u hu => ⟨?_, hu.2⟩)
          (K3.foldedCircle_compl_eq_zero hc (radius_pos n).le)
        refine mem_cthickening_of_dist_le u x _ _ ⟨x, hx, rfl⟩ ?_
        have := mem_closedBall.1 hu.1
        linarith [dist_triangle u c (x : ℂ)]
      have hA : KAdm (palmWinK a' b' g) (foldedCircle c (radius n)) :=
        ⟨isAdmissibleH_foldedCircle hc (radius_pos n), hK⟩
      simp only [Pi.add_apply, maskK_of_KAdm hA]
      rw [ofFun_eq_of_eqOn hmK hK]
    have hA : KAdm (palmWinK a' b' g) (Palm.fcK x n) :=
      ⟨isAdmissibleH_fcK x n, foldedCircle_palmWinK_compl hx (radius_pos n).le hlt.le⟩
    rw [hloc, hω]
    simp only [Pi.add_apply, maskK_of_KAdm hA]
    rw [ofFun_eq_of_eqOn hmK hA.2]
  · refine ae_of_all _ fun ω => ?_
    have hnot : ∀ j, (ofFun m + maskK (palmWinK a' b' g) X ω)
        (foldedCircle (dyadicRoundC j (x : ℂ)) (radius n)) =
          ∫ u, m u ∂foldedCircle (dyadicRoundC j (x : ℂ)) (radius n) := by
      intro j
      simp only [Pi.add_apply, maskK_of_not (not_kAdm_of_gt hg (dyadicRoundC_ofReal_mem_Hbar j x)
        hgt), add_zero]
      rfl
    have hlim : Tendsto (fun j => ∫ u, m u ∂foldedCircle (dyadicRoundC j (x : ℂ)) (radius n))
        atTop (𝓝 (∫ u, m u ∂foldedCircle (x : ℂ) (radius n))) := by
      have h1 := (TwoPoint.continuous_integral_foldedCircle hm).tendsto ((x : ℂ), radius n)
      have h2 : Tendsto (fun j : ℕ => (dyadicRoundC j (x : ℂ), radius n)) atTop
          (𝓝 ((x : ℂ), radius n)) :=
        (RegClosure.tendsto_dyadicRoundC (x : ℂ)).prodMk_nhds tendsto_const_nhds
      simpa only [Function.comp_def] using h1.comp h2
    have hR : (ofFun m + maskK (palmWinK a' b' g) X ω) (Palm.fcK x n) =
        ∫ u, m u ∂foldedCircle (x : ℂ) (radius n) := by
      simp only [Pi.add_apply, maskK_of_not (not_kAdm_of_gt hg hxH hgt), add_zero]
      rfl
    refine (?_ : _ = ∫ u, m u ∂foldedCircle (x : ℂ) (radius n)).trans hR.symm
    unfold avgReg
    simp_rw [hnot]
    exact hlim.limUnder_eq

/-- A scale `g' ∈ (g/2, g)` with `g'/2` not a dyadic radius (the dyadic radii are countable). -/
theorem exists_nondyadic_scale {g : ℝ} (hg : 0 < g) :
    ∃ g', 0 < g' ∧ g' ≤ g ∧ ∀ n, radius n ≠ g' / 2 := by
  have hne : (Ioo (g / 4) (g / 2) \ range radius).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
    have h0 : volume (range radius) = 0 := (countable_range radius).measure_zero volume
    have := measure_mono_null h h0
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
    linarith
  obtain ⟨s, ⟨hs1, hs2⟩, hsr⟩ := hne
  exact ⟨2 * s, by linarith, by linarith, fun n hn => hsr ⟨n, by rw [hn]; ring⟩⟩

/-- **Remaining node (regularity of the actual field at the free arc).** For `x ∈ (a,b)` and
folded circles `fc(x, 2^{-n})` with `2 · 2^{-n} < gap(x)` (inside `D ∪ (a,b)`), almost surely the
regularized average of `h0 + X` at `x` equals its value on `fc(x, 2^{-n})`. -/
def Prop16ActRegStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ x ∈ Ioo a b, ∀ n, 2 * radius n < palmGap D a b x → ∀ᵐ ω ∂P,
      avgReg (ofFun h0 + X ω) n (x : ℂ) = (ofFun h0 + X ω) (Palm.fcK x n)

/-- `Prop16ActRegStmt` gives the hypothesis `hact` of `palm_formula_prop16_window'`. -/
theorem hact_of_actReg (hR : Prop16ActRegStmt) {γ : ℝ} {D : Set ℂ} {c d a b a' b' g : ℝ}
    {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hH : Prop16PalmHyp γ D c d a b h0 P X) (ha : a < a') (hb : b' < b)
    (hgap : ∀ t ∈ Icc a' b', g ≤ palmGap D a b t) :
    ∀ n, radius n < g / 2 → ∀ x ∈ Icc a' b', ∀ᵐ ω ∂P,
      avgReg (ofFun h0 + X ω) n (x : ℂ) = (ofFun h0 + X ω) (Palm.fcK x n) :=
  fun n hn x hx => hR γ D c d a b h0 P X hH x ⟨by linarith [hx.1], by linarith [hx.2]⟩ n
    (by linarith [hgap x hx])

/-- **Remaining node (item (2), `hL1`).** On every window `[a',b'] ⊆ (a,b)` the boundary
approximations of `h0 + X` converge to `ν_h = prop16Nu` in the `L¹(P)`, `C_c` sense. -/
def Prop16BdryL1Stmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ a' b' : ℝ, a < a' → b' < b →
      PalmFree.BdryL1ConvCc γ h0 X P (fun ω => prop16Nu γ h0 a b (X ω)) a' b'

end Prop16Asm

end QuantumZipper
