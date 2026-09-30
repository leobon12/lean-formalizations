import QuantumZipper.Proofs.Zipper.Cor15RezipRegDist
import QuantumZipper.Proofs.Zipper.Cor15RezipRegStrip
import QuantumZipper.Proofs.Loewner.CoreArc1
import QuantumZipper.Proofs.Zipper.RegContEnergy
import QuantumZipper.Proofs.GFF.FrostmanReg
import QuantumZipper.Proofs.GFF.CoordRegEnergy
import QuantumZipper.Proofs.GFF.CoordRegLog

/-!
# Corollary 1.5, input R: the pushed folded circles are tame (deterministic part)

Task COR15-R. For a continuous driver `V` with `V 0 = 0`, `t > 0`, a folded circle
`σ = fc(w₀, r₀)` (`r₀ > 0`) not charging the hull `ℍ \ D` (`D = revMap V t '' ℍ`), a Hölder
bound on `F = revMap V t` and a polynomial bound `σ{dist(·, S) ≤ ε} ≤ c ε^{1/8}` for a set
`S ⊇ ℍ \ D` (the SLE trace, `Cor15RezipRegHull.lean`), the pushed measure
`ν = σ.map (revMapInv V t)` has every property that the general RC3 theorem
`CoordReg.ae_evalReg_coordChange_revMap_gen` asks of it:

* carried by `ℍ` (`ae_mem_H_map_revMapInv`) and by a bounded part of `Hbar`
  (`map_revMapInv_compl_closedBall_Hbar`; the displacement bound `‖F u − u‖ ≤ 12 M + 8√t`,
  `CoreArc.norm_revMap_sub_le`, gives `‖f z‖ ≤ ‖z‖ + 12 M + 8 √t`);
* Frostman with exponent `β` (`isFrostman_map_revMapInv_fc`);
* polynomial strip masses (`map_revMapInv_fc_im_lt_le`), hence `StripBound` (`stripBound_of_pow`)
  and integrable `|log Im|` (`integrable_abs_log_im_of_pow`);
* `ν.map F = σ` (`map_revMap_map_revMapInv`), Frostman with exponent `1` (`isFrostman_fc`).

**Own elementary arguments** throughout (bookkeeping around the Hölder bound, Rohde–Schramm
2005, Thm 5.2, and the one-point estimate, Beffara 2008, Prop. 4).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

variable {V : ℝ → ℝ} {t : ℝ}

theorem ae_mem_revMap_image_fc {w₀ : ℂ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hK : foldedCircle w₀ r₀ (H \ revMap V t '' H) = 0) :
    ∀ᵐ z ∂foldedCircle w₀ r₀, z ∈ revMap V t '' H := by
  have h2 : ∀ᵐ z ∂foldedCircle w₀ r₀, z ∉ H \ revMap V t '' H :=
    ae_iff.2 (by simp only [not_not, setOf_mem_eq]; exact hK)
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H w₀ hr₀, h2] with z hz h
  by_contra hc
  exact h ⟨hz, hc⟩

/-- Bounded preimages: `‖f z‖ ≤ ‖z‖ + 12 M + 8 √t`. -/
theorem norm_revMapInv_le (hV : Continuous V) (hV0 : V 0 = 0) (ht : 0 < t) {M : ℝ}
    (hM : ∀ r ∈ Icc (0 : ℝ) t, |V r| ≤ M) {z : ℂ} (hz : z ∈ revMap V t '' H) :
    ‖revMapInv V t z‖ ≤ ‖z‖ + (12 * M + 8 * Real.sqrt t) := by
  obtain ⟨hfH, hFf⟩ := revMapInv_mem_H hV ht.le hz
  have h := CoreArc.norm_revMap_sub_le hV hV0 ht hM hfH
  rw [hFf, norm_sub_rev] at h
  have := norm_sub_norm_le (revMapInv V t z) z
  linarith

theorem ae_mem_H_map_revMapInv (hV : Continuous V) (ht : 0 ≤ t) {σ : Measure ℂ}
    (hσD : ∀ᵐ z ∂σ, z ∈ revMap V t '' H) : ∀ᵐ w ∂σ.map (revMapInv V t), w ∈ H :=
  (ae_map_iff (measurable_revMapInv hV ht).aemeasurable isOpen_H.measurableSet).2
    (hσD.mono fun z hz => (revMapInv_mem_H hV ht hz).1)

theorem map_revMapInv_compl_closedBall_Hbar (hV : Continuous V) (ht : 0 ≤ t) {σ : Measure ℂ}
    {ρ : ℝ} (hσD : ∀ᵐ z ∂σ, z ∈ revMap V t '' H) (hσρ : ∀ᵐ z ∂σ, ‖revMapInv V t z‖ ≤ ρ) :
    σ.map (revMapInv V t) (closedBall 0 ρ ∩ Hbar)ᶜ = 0 := by
  have hm : MeasurableSet (closedBall (0 : ℂ) ρ ∩ Hbar) :=
    (isClosed_closedBall.inter isClosed_Hbar).measurableSet
  have h : ∀ᵐ w ∂σ.map (revMapInv V t), w ∈ closedBall (0 : ℂ) ρ ∩ Hbar := by
    refine (ae_map_iff (measurable_revMapInv hV ht).aemeasurable hm).2 ?_
    filter_upwards [hσD, hσρ] with z hz hzρ
    refine ⟨by rw [mem_closedBall, dist_zero_right]; exact hzρ, ?_⟩
    have h1 : 0 < (revMapInv V t z).im := (revMapInv_mem_H hV ht hz).1
    exact h1.le
  exact ae_iff.1 h

theorem isFrostman_fc (w₀ : ℂ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    IsFrostman (foldedCircle w₀ r₀) 1 (6 / r₀) := by
  intro p s hs
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity)
    (RegCont.foldedCircle_closedBall_le_arc w₀ p hr₀ hs.le)).trans (le_of_eq ?_)
  rw [Real.rpow_one]
  ring

/-- **Frostman bound for the pushed folded circle.** -/
theorem isFrostman_map_revMapInv_fc (hV : Continuous V) (ht : 0 ≤ t) {w₀ : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) {ρ C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    (hσD : ∀ᵐ z ∂foldedCircle w₀ r₀, z ∈ revMap V t '' H)
    (hσρ : ∀ᵐ z ∂foldedCircle w₀ r₀, ‖revMapInv V t z‖ ≤ ρ) :
    IsFrostman ((foldedCircle w₀ r₀).map (revMapInv V t)) β (6 * C * 2 ^ β / r₀) := by
  intro p s hs
  obtain ⟨z₀, hz₀⟩ := map_revMapInv_closedBall_le hV ht hC hβ hHol hσD hσρ p s
  have h2 := RegCont.foldedCircle_closedBall_le_arc w₀ z₀ hr₀
    (by positivity : (0 : ℝ) ≤ C * (2 * s) ^ β)
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (hz₀.trans h2)).trans (le_of_eq ?_)
  rw [Real.mul_rpow (by norm_num) hs.le]
  ring

/-- `ν.map F = σ` when `σ` is carried by `D`. -/
theorem map_revMap_map_revMapInv (hV : Continuous V) (ht : 0 ≤ t) {σ : Measure ℂ}
    (hσD : ∀ᵐ z ∂σ, z ∈ revMap V t '' H) :
    (σ.map (revMapInv V t)).map (revMap V t) = σ := by
  rw [Measure.map_map (TwoPoint.measurable_revMap hV ht) (measurable_revMapInv hV ht)]
  have h : (revMap V t ∘ revMapInv V t) =ᵐ[σ] id :=
    hσD.mono fun z hz => (revMapInv_mem_H hV ht hz).2
  rw [Measure.map_congr h, Measure.map_id]

/-- `|log Im|` is integrable under polynomial strip masses and bounded `Im`. -/
theorem integrable_abs_log_im_of_pow {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hνH : ∀ᵐ z ∂ν, z ∈ H) {R : ℝ} (hR : ∀ᵐ z ∂ν, z.im ≤ R) {A a : ℝ} (hA : 0 ≤ A)
    (ha : 0 < a) (h : ∀ τ : ℝ, 0 < τ → ν {z | z.im < τ} ≤ ENNReal.ofReal (A * τ ^ a)) :
    Integrable (fun z : ℂ => |Real.log z.im|) ν := by
  have hgl := lintegral_logRatio_le_of_pow hνH hA ha one_pos h
  set gf : ℂ → ℝ := fun u => max (Real.log (1 / |u.im|)) 0 with hgf
  have hgm : Measurable gf :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
  have hg0 : ∀ u, 0 ≤ gf u := fun u => le_max_right _ _
  have hgi : Integrable gf ν :=
    ⟨hgm.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
      exact lt_of_le_of_lt hgl ENNReal.ofReal_lt_top⟩
  refine (hgi.add (integrable_const |Real.log (max R 1)|)).mono'
    (continuous_abs.measurable.comp
      (Real.measurable_log.comp Complex.measurable_im)).aestronglyMeasurable ?_
  filter_upwards [hνH, hR] with z hz hzR
  rw [Real.norm_eq_abs, abs_abs]
  have hy : 0 < z.im := hz
  rcases le_or_gt z.im 1 with h1 | h1
  · have e : |Real.log z.im| = Real.log (1 / |z.im|) := by
      rw [abs_of_pos hy, one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos hy.le h1)]
    rw [e]
    exact le_add_of_le_of_nonneg (le_max_left _ _) (abs_nonneg _)
  · have hlog : |Real.log z.im| ≤ |Real.log (max R 1)| := by
      rw [abs_of_pos (Real.log_pos h1), abs_of_nonneg (Real.log_nonneg (le_max_right _ _))]
      exact Real.log_le_log hy (hzR.trans (le_max_left _ _))
    exact hlog.trans (le_add_of_nonneg_left (hg0 z))

/-- **Polynomial strip masses of the pushed folded circle.** -/
theorem map_revMapInv_fc_im_lt_le (hV : Continuous V) (ht : 0 ≤ t) {w₀ : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) {S : Set ℂ} (hS : H \ revMap V t '' H ⊆ S) {ρ C β : ℝ} (hC : 0 < C)
    (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    (hσD : ∀ᵐ z ∂foldedCircle w₀ r₀, z ∈ revMap V t '' H)
    (hσρ : ∀ᵐ z ∂foldedCircle w₀ r₀, ‖revMapInv V t z‖ ≤ ρ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      foldedCircle w₀ r₀ {z | infDist z S ≤ ε} ≤ ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ)))
    (τ : ℝ) (hτ : 0 < τ) :
    (foldedCircle w₀ r₀).map (revMapInv V t) {z | z.im < τ} ≤
      ENNReal.ofReal ((18 * Real.sqrt (2 / r₀) + c + 1) * C ^ (1 / 8 : ℝ) * τ ^ (β / 8)) := by
  set σ := foldedCircle w₀ r₀ with hσ
  set x := C * τ ^ β with hx
  have hx0 : 0 < x := by positivity
  set K := 18 * Real.sqrt (2 / r₀) + c + 1 with hK
  have hK1 : 1 ≤ K := by have := Real.sqrt_nonneg (2 / r₀); linarith
  have hxe : C ^ (1 / 8 : ℝ) * τ ^ (β / 8) = x ^ (1 / 8 : ℝ) := by
    rw [hx, Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hτ.le]
    congr 2
    ring
  rw [mul_assoc, hxe]
  by_cases hx1 : x ≤ 1
  · have hmono : (σ.map (revMapInv V t)) {z | z.im < τ} ≤
        (σ.map (revMapInv V t)) {z | z.im ≤ τ} :=
      measure_mono fun z (hz : z.im < τ) => (le_of_lt hz : z.im ≤ τ)
    refine hmono.trans ((map_revMapInv_im_le hV ht hS hC.le hβ hHol hσD hσρ τ).trans ?_)
    have h1 : σ {z | z.im ≤ x} ≤ ENNReal.ofReal (18 * Real.sqrt (2 * x / r₀)) := by
      refine (measure_mono_ae ?_).trans
        (TwoPoint.foldedCircle_strip_le w₀ hr₀ (by positivity : (0 : ℝ) < 2 * x))
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H w₀ hr₀] with z hz hzx
      have hz0 : 0 < z.im := hz
      change z.im ≤ x at hzx
      show |z.im| < 2 * x
      rw [abs_of_pos hz0]
      linarith
    have h2 := hc x hx0 hx1
    refine (add_le_add h1 h2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs : Real.sqrt (2 * x / r₀) = Real.sqrt (2 / r₀) * Real.sqrt x := by
      rw [show 2 * x / r₀ = 2 / r₀ * x by ring, Real.sqrt_mul (by positivity)]
    have hsx : Real.sqrt x ≤ x ^ (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hx0 hx1 (by norm_num)
    have hx8 : 0 ≤ x ^ (1 / 8 : ℝ) := by positivity
    have hs0 := Real.sqrt_nonneg (2 / r₀)
    rw [hs]
    nlinarith
  · push Not at hx1
    have hP : IsProbabilityMeasure (σ.map (revMapInv V t)) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_revMapInv hV ht).aemeasurable).2
        inferInstance
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 1 ≤ x ^ (1 / 8 : ℝ) := Real.one_le_rpow hx1.le (by norm_num)
    nlinarith

section RC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **(R) for a fixed good driver.** For a deterministic driver `V` with the Hölder bound and
the hull-neighbourhood bound, a.s. in the free field `X` the pulled-back field
`coordChange (𝔥₀ + X) F Q` is regular at the pushed folded circle `σ.map f`. RC3 for general
measures (`CoordReg.ae_evalReg_coordChange_revMap_gen`; Duplantier–Sheffield 2011, Prop. 3.1)
applied to `ν = σ.map f`, whose hypotheses are checked above. -/
theorem ae_evalReg_coordChange_pushed_fc (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P]
    (κ Q : ℝ) (hV : Continuous V) (hV0 : V 0 = 0) (ht : 0 < t) {w₀ : ℂ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hK : foldedCircle w₀ r₀ (H \ revMap V t '' H) = 0) {S : Set ℂ}
    (hS : H \ revMap V t '' H ⊆ S) {M : ℝ} (hM : ∀ r ∈ Icc (0 : ℝ) t, |V r| ≤ M) {C β : ℝ}
    (hC : 0 < C) (hβ : 0 < β)
    (hHol : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
      ‖w‖ ≤ ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) →
      ‖revMap V t z - revMap V t w‖ ≤ C * ‖z - w‖ ^ β)
    {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      foldedCircle w₀ r₀ {z | infDist z S ≤ ε} ≤ ENNReal.ofReal (c * ε ^ (1 / 8 : ℝ))) :
    ∀ᵐ ω ∂P,
      evalReg (coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q)
          ((foldedCircle w₀ r₀).map (revMapInv V t)) =
        coordChange (ofFun (h0rev κ) + X ω) (revMap V t) Q
          ((foldedCircle w₀ r₀).map (revMapInv V t)) := by
  set ρ := ‖w₀‖ + r₀ + (12 * M + 8 * Real.sqrt t) with hρ
  set σ := foldedCircle w₀ r₀ with hσ
  have hσD := ae_mem_revMap_image_fc hr₀ hK
  have hσρ : ∀ᵐ z ∂σ, ‖revMapInv V t z‖ ≤ ρ := by
    filter_upwards [hσD, TwoPoint.foldedCircle_ae_norm_le w₀ hr₀.le] with z hz hzn
    exact (norm_revMapInv_le hV hV0 ht hM hz).trans (by rw [hρ]; linarith)
  set ν := σ.map (revMapInv V t) with hν
  have hνP : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_revMapInv hV ht.le).aemeasurable).2
      inferInstance
  have hsupp := map_revMapInv_compl_closedBall_Hbar hV ht.le hσD hσρ
  have hνH := ae_mem_H_map_revMapInv hV ht.le hσD
  have hF := isFrostman_map_revMapInv_fc hV ht.le hr₀ hC.le hβ hHol hσD hσρ
  have hpow := map_revMapInv_fc_im_lt_le hV ht.le hr₀ hS hC hβ hHol hσD hσρ hc0 hc
  have hA0 : 0 ≤ (18 * Real.sqrt (2 / r₀) + c + 1) * C ^ (1 / 8 : ℝ) := by positivity
  have hβ8 : 0 < β / 8 := by positivity
  have hSt := stripBound_of_pow hνH hA0 hβ8 hpow
  have hR : ∀ᵐ z ∂ν, z.im ≤ ρ := by
    filter_upwards [(mem_ae_iff.2 hsupp : ∀ᵐ z ∂ν, z ∈ closedBall (0 : ℂ) ρ ∩ Hbar)] with z hz
    have h1 := hz.1
    rw [mem_closedBall, dist_zero_right] at h1
    exact (Complex.im_le_norm z).trans h1
  have hlν := integrable_abs_log_im_of_pow hνH hR hA0 hβ8 hpow
  have hFf : IsFrostman (ν.map (revMap V t)) 1 (6 / r₀) := by
    rw [hν, map_revMap_map_revMapInv hV ht.le hσD]
    exact isFrostman_fc w₀ hr₀
  have hB := CoordReg.ae_evalReg_coordChange_revMap_gen hV ht.le hX (P := P)
    (2 / Real.sqrt κ) (g₁ := fun _ => 0) continuous_const Q hsupp hνH hF hβ hlν hSt
    (by positivity) hFf one_pos
  rw [← CoordReg.h0rev_eq_logAdd κ] at hB
  filter_upwards [hB] with ω h
  rw [h]
  rfl

end RC

end Cor15Group
end QuantumZipper
