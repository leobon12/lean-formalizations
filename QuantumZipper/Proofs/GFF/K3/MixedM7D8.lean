import QuantumZipper.Proofs.GFF.K3.MixedM7D7
import QuantumZipper.Proofs.GFF.K3.MixedM7B4

/-!
# K3-mixed M7-a3, half-disc covariance, step D8: the Green identity and `HalfDiscMixedCovStmt`

`halfDiscGreenId_holds`: for local admissible `μ, ν` (carried by `closedBall t r'`, `r' < r`),

  `∫_B ∫_B G_ℍ(φ x, φ y) dν̃ dμ̃ = 2 · kernelCov (halfDiscGreen t r) μ ν`,

by expanding `μ̃ ⊗ ν̃` into the four reflected copies of `μ ⊗ ν` and using, off the null sets
`{x = y}`, `{x = ȳ}` (admissible measures have no atoms), `G_ℍ(φ x, φ y) = G_B(x, y)` (D7),
`G_B(x̄, ȳ) = G_B(x, y)` and `halfDiscGreen = G_B(x, y) + G_B(x, ȳ)` (D7). Integrability comes from
the admissibility of the Cayley pushforwards (D6) and `integrable_greenH_prod`.

Consequently `HalfDiscMixedCovStmt t r r'` holds for all `t r r'` (`halfDiscMixedCov_holds`), and
hence M7-a (`MixedHalfDiscMarkovCovStmt`) holds unconditionally (`mixedHalfDiscMarkovCov_holds`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Real Topology ComplexConjugate ENNReal

namespace QuantumZipper.K3

theorem restrict_sym_eq_m7d {t r r' : ℝ} (hr'r : r' < r) {ρ : Measure ℂ}
    (hρK : ρ (closedBall (t : ℂ) r')ᶜ = 0) :
    (ρ + ρ.map conj).restrict (ball (t : ℂ) r) = ρ + ρ.map conj := by
  have hconjm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hKB : closedBall (t : ℂ) r' ⊆ ball (t : ℂ) r := closedBall_subset_ball hr'r
  refine Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff (s := ball (t : ℂ) r)).2 ?_)
  rw [Measure.add_apply, Measure.map_apply hconjm isOpen_ball.measurableSet.compl]
  have h1 : ρ (ball (t : ℂ) r)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 hKB) hρK
  have h2 : conj ⁻¹' (ball (t : ℂ) r)ᶜ = (ball (t : ℂ) r)ᶜ := by
    ext z; simp [mem_ball, dist_eq_norm, norm_conj_sub_ofReal_k3]
  rw [h2, h1, add_zero]

/-- A.e. on `μ ⊗ ν`: `x, y ∈ closedBall t r'`, `x ≠ y`, `x ≠ ȳ`. -/
theorem ae_prod_good_m7d {t r' : ℝ} {μ ν : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hν : IsAdmissibleH ν) (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0)
    (hνK : ν (closedBall (t : ℂ) r')ᶜ = 0) :
    ∀ᵐ p ∂(μ.prod ν), p.1 ∈ closedBall (t : ℂ) r' ∧ p.2 ∈ closedBall (t : ℂ) r' ∧
      p.1 ≠ p.2 ∧ p.1 ≠ conj p.2 := by
  have := hμ.1; have := hν.1
  have hatom := noAtoms_of_isAdmissibleH hν
  have hconjm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have h1 : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ closedBall (t : ℂ) r' := by
    rw [ae_iff]
    have : {p : ℂ × ℂ | ¬ p.1 ∈ closedBall (t : ℂ) r'} = (closedBall (t : ℂ) r')ᶜ ×ˢ univ := by
      ext p; simp
    rw [this, Measure.prod_prod, hμK, zero_mul]
  have h2 : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ closedBall (t : ℂ) r' := by
    rw [ae_iff]
    have : {p : ℂ × ℂ | ¬ p.2 ∈ closedBall (t : ℂ) r'} = univ ×ˢ (closedBall (t : ℂ) r')ᶜ := by
      ext p; simp
    rw [this, Measure.prod_prod, hνK, mul_zero]
  have h3 : ∀ᵐ p ∂(μ.prod ν), p.1 ≠ p.2 := by
    rw [ae_iff]; simp only [ne_eq, not_not]
    have hmd : MeasurableSet {p : ℂ × ℂ | p.1 = p.2} := measurableSet_diagonal
    rw [Measure.prod_apply hmd]
    have : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = p.2} = {x} := fun x => by
      ext y; simp [eq_comm]
    simp [this, hatom]
  have h4 : ∀ᵐ p ∂(μ.prod ν), p.1 ≠ conj p.2 := by
    rw [ae_iff]; simp only [ne_eq, not_not]
    have hm : MeasurableSet {p : ℂ × ℂ | p.1 = conj p.2} :=
      measurableSet_eq_fun measurable_fst (hconjm.comp measurable_snd)
    rw [Measure.prod_apply hm]
    have : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 = conj p.2} = {conj x} := fun x => by
      ext y; simp only [mem_preimage, mem_setOf_eq, mem_singleton_iff]
      constructor
      · intro h; rw [h, Complex.conj_conj]
      · intro h; rw [h, Complex.conj_conj]
    simp [this, hatom]
  filter_upwards [h1, h2, h3, h4] with p a b c d using ⟨a, b, c, d⟩

/-- The pointwise four-term identity. -/
theorem four_term_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r) {x y : ℂ}
    (hx : x ∈ closedBall (t : ℂ) r') (hy : y ∈ closedBall (t : ℂ) r') (hxy : x ≠ y)
    (hxy' : x ≠ conj y) :
    greenH (discMap t r x) (discMap t r y) + greenH (discMap t r x) (discMap t r (conj y)) +
      greenH (discMap t r (conj x)) (discMap t r y) +
      greenH (discMap t r (conj x)) (discMap t r (conj y)) = 2 * halfDiscGreen t r x y := by
  have hr : 0 < r := hr'.trans hr'r
  have hKB : closedBall (t : ℂ) r' ⊆ ball (t : ℂ) r := closedBall_subset_ball hr'r
  have hcK : ∀ z ∈ closedBall (t : ℂ) r', conj z ∈ closedBall (t : ℂ) r' := fun z hz => by
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm, norm_conj_sub_ofReal_k3]; exact hz
  have hcx : conj x ≠ y := fun h => hxy' (by rw [← h, Complex.conj_conj])
  have hcc : conj x ≠ conj y := fun h => hxy (by simpa using congrArg conj h)
  rw [greenH_discMap_m7d hr (hKB hx) (hKB hy) hxy,
    greenH_discMap_m7d hr (hKB hx) (hKB (hcK y hy)) hxy',
    greenH_discMap_m7d hr (hKB (hcK x hx)) (hKB hy) hcx,
    greenH_discMap_m7d hr (hKB (hcK x hx)) (hKB (hcK y hy)) hcc,
    halfDiscGreen_eq_discG_m7d hr' hr'r (hKB hx) hy, discG_conj_conj_m7d]
  have : discG t r (conj x) y = discG t r x (conj y) := by
    conv_lhs => rw [← Complex.conj_conj y]
    exact discG_conj_conj_m7d t r x (conj y)
  rw [this]; ring

/-- **The explicit Green identity (D8).** -/
theorem halfDiscGreenId_holds (t r r' : ℝ) : HalfDiscGreenIdStmt t r r' := by
  intro hr' hr'r μ ν hμ hμK hν hνK
  have := hμ.1; have := hν.1
  have hconjm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hφm := measurable_discMap_m7d t r
  set Φ : ℂ × ℂ → ℝ := fun p => greenH (discMap t r p.1) (discMap t r p.2) with hΦ
  have hΦm : Measurable Φ := measurable_greenH.comp (hφm.prodMap hφm)
  have hμA := isAdmissibleH_map_sym_m7d hr' hr'r hμ hμK
  have hνA := isAdmissibleH_map_sym_m7d hr' hr'r hν hνK
  rw [restrict_sym_eq_m7d hr'r hμK] at hμA ⊢
  rw [restrict_sym_eq_m7d hr'r hνK] at hνA ⊢
  set μc := μ.map conj with hμc
  set νc := ν.map conj with hνc
  have hint : Integrable Φ ((μ + μc).prod (ν + νc)) := by
    have hA := integrable_greenH_prod hμA hνA
    rw [Measure.map_prod_map _ _ hφm hφm] at hA
    exact (integrable_map_measure measurable_greenH.aestronglyMeasurable
      (hφm.prodMap hφm).aemeasurable).1 hA
  have hiter : ∫ x, ∫ y, greenH (discMap t r x) (discMap t r y) ∂(ν + νc) ∂(μ + μc) =
      ∫ p, Φ p ∂((μ + μc).prod (ν + νc)) := (integral_prod Φ hint).symm
  rw [hiter]
  set P := μ.prod ν with hP
  have hsplit : (μ + μc).prod (ν + νc) = (μ.prod ν + μ.prod νc) + (μc.prod ν + μc.prod νc) := by
    rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  rw [hsplit] at hint ⊢
  obtain ⟨h12, h34⟩ := integrable_add_measure.1 hint
  obtain ⟨h1, h2⟩ := integrable_add_measure.1 h12
  obtain ⟨h3, h4⟩ := integrable_add_measure.1 h34
  have e2 : μ.prod νc = P.map (Prod.map id conj) := by
    rw [hP, ← Measure.map_prod_map _ _ measurable_id hconjm, Measure.map_id]
  have e3 : μc.prod ν = P.map (Prod.map conj id) := by
    rw [hP, ← Measure.map_prod_map _ _ hconjm measurable_id, Measure.map_id]
  have e4 : μc.prod νc = P.map (Prod.map conj conj) := by
    rw [hP, ← Measure.map_prod_map _ _ hconjm hconjm]
  have h2' := h2; have h3' := h3; have h4' := h4
  rw [e2] at h2'; rw [e3] at h3'; rw [e4] at h4'
  have i2 := (integrable_map_measure hΦm.aestronglyMeasurable
    (measurable_id.prodMap hconjm).aemeasurable).1 h2'
  have i3 := (integrable_map_measure hΦm.aestronglyMeasurable
    (hconjm.prodMap measurable_id).aemeasurable).1 h3'
  have i4 := (integrable_map_measure hΦm.aestronglyMeasurable
    (hconjm.prodMap hconjm).aemeasurable).1 h4'
  rw [integral_add_measure h12 h34, integral_add_measure h1 h2, integral_add_measure h3 h4,
    e2, e3, e4, integral_map (measurable_id.prodMap hconjm).aemeasurable hΦm.aestronglyMeasurable,
    integral_map (hconjm.prodMap measurable_id).aemeasurable hΦm.aestronglyMeasurable,
    integral_map (hconjm.prodMap hconjm).aemeasurable hΦm.aestronglyMeasurable]
  set S : ℂ × ℂ → ℝ := fun p => Φ p + Φ (Prod.map id conj p) +
    (Φ (Prod.map conj id p) + Φ (Prod.map conj conj p)) with hS
  have hsumint : ∫ p, S p ∂P = ∫ p, Φ p ∂P + ∫ p, Φ (Prod.map id conj p) ∂P +
      (∫ p, Φ (Prod.map conj id p) ∂P + ∫ p, Φ (Prod.map conj conj p) ∂P) := by
    have ha : ∫ p, (Φ p + Φ (Prod.map id conj p)) ∂P =
        ∫ p, Φ p ∂P + ∫ p, Φ (Prod.map id conj p) ∂P := integral_add h1 i2
    have hb : ∫ p, (Φ (Prod.map conj id p) + Φ (Prod.map conj conj p)) ∂P =
        ∫ p, Φ (Prod.map conj id p) ∂P + ∫ p, Φ (Prod.map conj conj p) ∂P := integral_add i3 i4
    have hc : ∫ p, S p ∂P = ∫ p, (Φ p + Φ (Prod.map id conj p)) ∂P +
        ∫ p, (Φ (Prod.map conj id p) + Φ (Prod.map conj conj p)) ∂P :=
      integral_add (h1.add i2) (i3.add i4)
    rw [hc, ha, hb]
  have hae : S =ᵐ[P] fun p => 2 * halfDiscGreen t r p.1 p.2 := by
    filter_upwards [ae_prod_good_m7d hμ hν hμK hνK] with p hp
    have := four_term_m7d hr' hr'r hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
    simp only [hS, hΦ, Prod.map_fst, Prod.map_snd, id]
    linarith
  have hsum : Integrable S P := (h1.add i2).add (i3.add i4)
  have hI : Integrable (fun p : ℂ × ℂ => halfDiscGreen t r p.1 p.2) P := by
    have := (hsum.congr hae).div_const 2
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only; ring
  have hfinal : ∫ p, S p ∂P = 2 * kernelCov (halfDiscGreen t r) μ ν := by
    rw [integral_congr_ae hae, integral_const_mul, hP, integral_prod _ hI]
    rfl
  exact hsumint.symm.trans hfinal

/-- **The explicit half-disc covariance holds.** -/
theorem halfDiscMixedCov_holds (t r r' : ℝ) : HalfDiscMixedCovStmt t r r' :=
  halfDiscMixedCov_of_greenId (halfDiscGreenId_holds t r r')

/-- **M7-a holds** (from M7-a2′, proved for every domain, and the half-disc covariance). -/
theorem mixedHalfDiscMarkovCov_holds (D : Set ℂ) (c d t r r' : ℝ) :
    MixedHalfDiscMarkovCovStmt D c d t r r' :=
  mixedHalfDiscMarkovCov_of_pairing_halfDiscCov (mixedHarmonicPairing_holds D c d t r r')
    (mixedHarmonicPairing_holds _ _ _ t r r') (halfDiscMixedCov_holds t r r')

end QuantumZipper.K3
