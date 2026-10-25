import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51GProb
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.Family




 














set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology
open LQGMetric.Blueprint
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC addConst)

theorem gScale_pos {b : ℝ} (hb : 0 < b) (m k : ℕ) : 0 < 4 * b * (1 / 4 : ℝ) ^ (m + k) :=
  mul_pos (mul_pos (by norm_num) hb) (pow_pos (by norm_num) _)

 
def gScale (b : ℝ) (hb : 0 < b) (m k : ℕ) : Ioi (0 : ℝ) :=
  ⟨4 * b * (1 / 4 : ℝ) ^ (m + k), gScale_pos hb m k⟩

 
def goodCount (ξ Q lam R : ℝ) (D : DistC → LSCMetric) (b : ℝ) (hb : 0 < b) (m : ℕ) (w : ℂ)
    (g : DistC) : ℕ :=
  countOcc (fun k => {g | GEv ξ Q lam R D w (gScale b hb m k) g}) (m + 1) g

theorem gCarrier_subset_iterAnn (w : ℂ) {s : ℝ} (hs : 0 < s) :
    gCarrier w s ⊆ (annulus w ((1 / 4 : ℝ) * ((3 / 2) * s)) ((3 / 4 : ℝ) * ((3 / 2) * s)) :
      Set ℂ) := by
  intro x hx
  have h1 : dist x w ≤ s := mem_closedBall.mp hx.1
  have h2 : ¬ dist x w < s / 2 := fun h => hx.2 (mem_ball.mpr h)
  change (1 / 4 : ℝ) * ((3 / 2) * s) < ‖x - w‖ ∧ ‖x - w‖ < (3 / 4 : ℝ) * ((3 / 2) * s)
  rw [← dist_eq_norm]
  constructor <;> linarith

 
theorem goodCount_tail {pLM cLM : ℝ}
    (hLM : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsWholePlaneGFF h P →
        ∀ (z : ℂ) (r : ℕ → ℝ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ 1 / 4) →
          (∀ k, AEEventIn P
            (fieldSigma (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) z))
              (annulus z (1 / 4 * r k) (3 / 4 * r k))) (E k)) →
          (∀ k, ENNReal.ofReal pLM ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < 3 / 4 * K} ≤
            ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * K)))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (lam R : ℝ) (hmarg : ∀ (w : ℂ) (s : Ioi (0 : ℝ)),
      ENNReal.ofReal pLM ≤ μ {g | GEv ξ Q lam R D w s g})
    (b : ℝ) (hb : 0 < b) (m : ℕ) (w : ℂ) :
    μ {g | (goodCount ξ Q lam R D b hb m w g : ℝ) < 3 / 4 * ((m + 1 : ℕ) : ℝ)} ≤
      ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) := by
  let E : ℕ → Set DistC := fun k => {g | GEv ξ Q lam R D w (gScale b hb m k) g}
  let r : ℕ → ℝ := fun k => (3 / 2) * (gScale b hb m k : ℝ)
  have hr : ∀ k, 0 < r k := fun k => mul_pos (by norm_num) (gScale_pos hb m k)
  have hanti : Antitone r := by
    intro i j hij
    change (3 / 2 : ℝ) * (4 * b * (1 / 4 : ℝ) ^ (m + j)) ≤ (3 / 2) * (4 * b * (1 / 4 : ℝ) ^ (m + i))
    have : (1 / 4 : ℝ) ^ (m + j) ≤ (1 / 4 : ℝ) ^ (m + i) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hb4 : 0 ≤ 4 * b := by positivity
    nlinarith
  have hratio : ∀ k, r (k + 1) / r k ≤ 1 / 4 := by
    intro k
    have hk := hr k
    rw [div_le_iff₀ hk]
    change (3 / 2 : ℝ) * (4 * b * (1 / 4 : ℝ) ^ (m + (k + 1))) ≤
      1 / 4 * ((3 / 2) * (4 * b * (1 / 4 : ℝ) ^ (m + k)))
    rw [show m + (k + 1) = (m + k) + 1 by omega, pow_succ]
    nlinarith [pow_pos (show (0 : ℝ) < 1 / 4 by norm_num) (m + k)]
  have hloc : ∀ k, AEEventIn μ
      (fieldSigma (fun g => addConst (id g) (-LQGMetric.circleAvg (id g) (r k) w))
        (annulus w (1 / 4 * r k) (3 / 4 * r k))) (E k) := by
    intro k
    obtain ⟨F, hFm, hEF⟩ := aeEventIn_GEv μ hμ ξ Q D hD lam R w (gScale b hb m k)
    exact ⟨F, (Toolkit.AnnulusIteration.fieldSigmaClosed0_le_centered_open id
      (fun g => -LQGMetric.circleAvg g (r k) w) (gCarrier w (gScale b hb m k))
      (annulus w (1 / 4 * r k) (3 / 4 * r k))
      (isCompact_annK _ _ _) (gCarrier_subset_iterAnn w (gScale_pos hb m k))) F hFm, hEF⟩
  have hprob : ∀ k, ENNReal.ofReal pLM ≤ μ (E k) := fun k => hmarg w (gScale b hb m k)
  exact hLM μ id hμ.1 w r E hr hanti hratio hloc hprob (m + 1)

 
def gridCentres (b α δ : ℝ) : Finset ℂ :=
  (orientations ×ˢ gridAngles δ).image (fun x => (b : ℂ) * x.1 * Objects.CorrectedEvent.polar α x.2) ∪
    (orientations ×ˢ gridAngles δ).image (fun x => (b : ℂ) * x.1 * Objects.CorrectedEvent.polar 1 x.2)

theorem orientations_card_le : orientations.card ≤ 4 := by
  unfold orientations
  have h1 := Finset.card_insert_le (1 : ℂ) {Complex.I, -1, -Complex.I}
  have h2 := Finset.card_insert_le Complex.I ({-1, -Complex.I} : Finset ℂ)
  have h3 := Finset.card_insert_le (-1 : ℂ) ({-Complex.I} : Finset ℂ)
  have h4 : ({-Complex.I} : Finset ℂ).card = 1 := Finset.card_singleton _
  omega

theorem gridAngles_card_le (δ : ℝ) : (gridAngles δ).card ≤ 2 * gridHalf δ + 1 := by
  unfold gridAngles
  refine Finset.card_image_le.trans ?_
  rw [Int.card_Icc]
  omega

theorem gridCentres_card_le (b α δ : ℝ) :
    (gridCentres b α δ).card ≤ 8 * (2 * gridHalf δ + 1) := by
  unfold gridCentres
  refine (Finset.card_union_le _ _).trans ?_
  have hp : (orientations ×ˢ gridAngles δ).card ≤ 4 * (2 * gridHalf δ + 1) := by
    rw [Finset.card_product]
    exact Nat.mul_le_mul orientations_card_le (gridAngles_card_le δ)
  have h1 := (Finset.card_image_le (s := orientations ×ˢ gridAngles δ)
    (f := fun x => (b : ℂ) * x.1 * Objects.CorrectedEvent.polar α x.2))
  have h2 := (Finset.card_image_le (s := orientations ×ˢ gridAngles δ)
    (f := fun x => (b : ℂ) * x.1 * Objects.CorrectedEvent.polar 1 x.2))
  omega

 
def UEv (ξ Q lam R : ℝ) (D : DistC → LSCMetric) (b : ℝ) (hb : 0 < b) (α δ : ℝ) (m : ℕ)
    (g : DistC) : Prop :=
  ∀ w ∈ gridCentres b α δ, 3 / 4 * ((m + 1 : ℕ) : ℝ) ≤ goodCount ξ Q lam R D b hb m w g

 
theorem measure_not_UEv_le {pLM cLM : ℝ}
    (hLM : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsWholePlaneGFF h P →
        ∀ (z : ℂ) (r : ℕ → ℝ) (E : ℕ → Set Ω),
          (∀ k, 0 < r k) → Antitone r →
          (∀ k, r (k + 1) / r k ≤ 1 / 4) →
          (∀ k, AEEventIn P
            (fieldSigma (fun ω => addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) z))
              (annulus z (1 / 4 * r k) (3 / 4 * r k))) (E k)) →
          (∀ k, ENNReal.ofReal pLM ≤ P (E k)) →
          ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < 3 / 4 * K} ≤
            ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * K)))
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (lam R : ℝ) (hmarg : ∀ (w : ℂ) (s : Ioi (0 : ℝ)),
      ENNReal.ofReal pLM ≤ μ {g | GEv ξ Q lam R D w s g})
    (b : ℝ) (hb : 0 < b) (α δ : ℝ) (m : ℕ) :
    μ {g | ¬ UEv ξ Q lam R D b hb α δ m g} ≤
      ((8 * (2 * gridHalf δ + 1) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) := by
  have hsub : {g | ¬ UEv ξ Q lam R D b hb α δ m g} ⊆
      ⋃ w ∈ gridCentres b α δ,
        {g | (goodCount ξ Q lam R D b hb m w g : ℝ) < 3 / 4 * ((m + 1 : ℕ) : ℝ)} := by
    intro g hg
    simp only [UEv, mem_ofPred_eq, not_forall, not_le] at hg
    obtain ⟨w, hw, hlt⟩ := hg
    exact mem_biUnion hw hlt
  calc μ {g | ¬ UEv ξ Q lam R D b hb α δ m g}
      ≤ μ (⋃ w ∈ gridCentres b α δ,
          {g | (goodCount ξ Q lam R D b hb m w g : ℝ) < 3 / 4 * ((m + 1 : ℕ) : ℝ)}) :=
        measure_mono hsub
    _ ≤ ∑ w ∈ gridCentres b α δ,
          μ {g | (goodCount ξ Q lam R D b hb m w g : ℝ) < 3 / 4 * ((m + 1 : ℕ) : ℝ)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ gridCentres b α δ,
          ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun w _ => goodCount_tail hLM μ hμ ξ Q D hD lam R hmarg b hb m w
    _ = ((gridCentres b α δ).card : ℝ≥0∞) *
          ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((8 * (2 * gridHalf δ + 1) : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (cLM * Real.exp (-(2 * Real.log 16) * ((m + 1 : ℕ) : ℝ))) := by
        gcongr
        exact_mod_cast gridCentres_card_le b α δ

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
