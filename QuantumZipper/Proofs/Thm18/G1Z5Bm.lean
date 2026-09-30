import QuantumZipper.Proofs.Thm18.G1Z5Ident
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z5 (D58, S1): a path-measurable boundary map, and measurability tools

* `bm m left t`: on the side half-line, the limit of `Re m(t + i/(n+1))`; off it, `t`. For a
  side map with reflection data (`SideReflGood left m Φ`) it equals `Φ` on the half-line
  (`bm_eq_of_refl`), so the glued test functions agree: `glue left G ∘ Φ = glue left G ∘ bm`
  (`glue_bm`). It is jointly measurable when the map family is (`measurable_bm`).
* `measurable_integral_bdryR_param`: `p ↦ ∫ G p t d(bdryR γ (Y p) r)` is measurable.
* `measurableSet_tendsto_fun`: `{p | a_k(p) → L(p)}` is measurable.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z5

open GoodSample GoodMeas

/-- The approach points `t + i/(n+1)`. -/
def appr (t : ℝ) (n : ℕ) : ℂ := (t : ℂ) + Complex.I * ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

theorem appr_mem_H (t : ℝ) (n : ℕ) : appr t n ∈ H := by
  show 0 < (appr t n).im
  simp only [appr, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
  positivity

theorem tendsto_appr (t : ℝ) : Tendsto (appr t) atTop (𝓝 (t : ℂ)) := by
  have h := ((Complex.continuous_ofReal.tendsto 0).comp
    tendsto_one_div_add_atTop_nhds_zero_nat).const_mul Complex.I
  simp only [Complex.ofReal_zero, mul_zero] at h
  have h2 := (tendsto_const_nhds (x := (t : ℂ))).add h
  simp only [add_zero] at h2
  exact h2

open Classical in
/-- The path-measurable boundary map. -/
def bm (m : ℂ → ℂ) (left : Bool) (t : ℝ) : ℝ :=
  if t ∈ g1SideHalf left then limUnder atTop (fun n : ℕ => (m (appr t n)).re) else t

theorem bm_eq_of_refl {m : ℂ → ℂ} {left : Bool} {Φ : ℝ ≃o ℝ} (hR : SideReflGood left m Φ)
    {t : ℝ} (ht : t ∈ g1SideHalf left) : bm m left t = Φ t := by
  obtain ⟨p, q, hpq, hS, htpq⟩ := exists_side_window left (isCompact_singleton (x := t))
    (singleton_subset_iff.2 ht)
  obtain ⟨U, Ψ', hU, hJU, hΨd, hΨΦ, -, hEq⟩ := hR.2 p q hpq hS
  have htI : t ∈ Icc p q := Ioo_subset_Icc_self (htpq (mem_singleton t))
  have hc : ContinuousAt Ψ' t :=
    (hΨd.differentiableAt (hU.mem_nhds (hJU t htI))).continuousAt
  have h3 : Tendsto (fun n => Ψ' (appr t n)) atTop (𝓝 (Ψ' t)) := hc.tendsto.comp (tendsto_appr t)
  rw [hΨΦ t htI] at h3
  have h4 := (Complex.continuous_re.tendsto _).comp h3
  simp only [Complex.ofReal_re] at h4
  have h5 : Tendsto (fun n : ℕ => (m (appr t n)).re) atTop (𝓝 (Φ t)) :=
    h4.congr fun n => by simp only [Function.comp]; rw [← hEq (appr_mem_H t n)]
  unfold bm
  rw [if_pos ht]
  exact h5.limUnder_eq

theorem glue_bm {m : ℂ → ℂ} {left : Bool} {Φ : ℝ ≃o ℝ} (hR : SideReflGood left m Φ)
    (G : ℝ → ℝ) (t : ℝ) : glue left G (Φ t) = glue left G (bm m left t) := by
  by_cases ht : t ∈ g1SideHalf left
  · rw [bm_eq_of_refl hR ht]
  · have h1 : Φ t ∉ g1SideHalf left := by
      intro h
      have hI := image_g1SideHalf hR.1 left
      rw [← hI] at h
      exact ht (Φ.injective.mem_set_image.1 h)
    have h2 : bm m left t = t := by unfold bm; rw [if_neg ht]
    rw [h2]
    simp only [glue, indicator_of_notMem h1, indicator_of_notMem ht]

theorem measurable_bm {Z : Type*} [MeasurableSpace Z] {M : Z → ℂ → ℂ}
    (hM : Measurable fun q : Z × ℂ => M q.1 q.2) (left : Bool) :
    Measurable fun q : Z × ℝ => bm (M q.1) left q.2 := by
  unfold bm
  refine Measurable.ite (measurable_snd (g1z2_isOpen_sideHalf left).measurableSet) ?_
    measurable_snd
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine (Complex.measurable_re.comp (hM.comp (measurable_fst.prodMk ?_))).stronglyMeasurable
  exact (Complex.measurable_ofReal.comp measurable_snd).add_const _

theorem bdryR_congr_avg {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    bdryR γ x = bdryR γ x' := by
  funext r; unfold bdryR bdryDens evalReg; rw [h]

theorem measurable_integral_bdryR_param {Z : Type*} [MeasurableSpace Z] {Y : Z → FieldSample}
    (hY : Measurable Y) {G : Z → ℝ → ℝ} (hG : Measurable fun q : Z × ℝ => G q.1 q.2) (γ : ℝ)
    {r : ℝ} (hr : 0 < r) : Measurable fun p => ∫ t, G p t ∂bdryR γ (Y p) r := by
  let D : Z × ℝ → ℝ := fun q => bdryDens γ (Y q.1) r q.2
  have hDm : Measurable D :=
    (Real.measurable_exp.comp (((measurable_evalReg_fc_joint r).comp ((hY.comp measurable_fst).prodMk
      (Complex.continuous_ofReal.measurable.comp measurable_snd))).const_mul (γ / 2))).const_mul _
  have hD0 : ∀ q, 0 ≤ D q := fun q => GoodSample.bdryDens_nonneg γ _ hr q.2
  have heq : ∀ p, ∫ t, G p t ∂bdryR γ (Y p) r = ∫ t, D (p, t) * G p t := fun p =>
    GoodSample.integral_withDensity_ofReal (hDm.comp (measurable_const.prodMk measurable_id))
      (fun t => hD0 _) (G p)
  simp_rw [heq]
  exact (StronglyMeasurable.integral_prod_right' (f := fun q : Z × ℝ => D q * G q.1 q.2)
    (hDm.mul hG).stronglyMeasurable).measurable

theorem measurableSet_tendsto_fun {Z : Type*} [MeasurableSpace Z] {a : ℕ → Z → ℝ} {L : Z → ℝ}
    (ha : ∀ k, Measurable (a k)) (hL : Measurable L) :
    MeasurableSet {p | Tendsto (fun k => a k p) atTop (𝓝 (L p))} := by
  have e : {p | Tendsto (fun k => a k p) atTop (𝓝 (L p))} =
      {p | ∃ l, Tendsto (fun k => a k p) atTop (𝓝 l)} ∩
        {p | limUnder atTop (fun k => a k p) = L p} := by
    ext p
    simp only [mem_setOf_eq, mem_inter_iff]
    constructor
    · intro h; exact ⟨⟨_, h⟩, h.limUnder_eq⟩
    · rintro ⟨⟨l, hl⟩, he⟩
      rw [← he, hl.limUnder_eq]; exact hl
  rw [e]
  exact (StronglyMeasurable.measurableSet_exists_tendsto
    (f := fun k p => a k p) fun k => (ha k).stronglyMeasurable).inter
    (measurableSet_eq_fun (StronglyMeasurable.limUnder fun k => (ha k).stronglyMeasurable).measurable
      hL)

end G1Z5
end Thm18Asm
end QuantumZipper
