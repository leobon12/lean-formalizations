import HigherDimLQGMetric.Events.TightCore
import HigherDimLQGMetric.LGF.Normalized
import HigherDimLQGMetric.LGF.Exists
import HigherDimLQGMetric.Sphere.Scaling
import HigherDimLQGMetric.Metric.WeylAxioms

/-!
# Centred normalized metric laws

The dimension `d` port of the law step in `LQGMetric.Papers.GM.S2.TightLaw`.
The centered metric observable uses a fixed real scale and spatial center.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The normalized metric observable centered at `z`. -/
def scaledField (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (r : ℝ) (z : Rd d) (g : DistRd d) : C(Rd d × Rd d, ℝ) :=
  ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z)) •
    (D g).1.comp ⟨fun p : Rd d × Rd d => (r • p.1 + z, r • p.2 + z), by fun_prop⟩

@[simp] theorem scaledField_apply (ξ : ℝ) (D : DistRd d → ContMetric d)
    (c : ℝ → ℝ) (r : ℝ) (z : Rd d) (g : DistRd d) (p : Rd d × Rd d) :
    scaledField ξ D c r z g p =
      ((c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z)) *
        (D g).1 (r • p.1 + z, r • p.2 + z) := rfl

/-- At center zero the observable is the frozen Axiom V normalization. -/
theorem scaledField_zero (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (r : ℝ) (g : DistRd d) :
    scaledField ξ D c r 0 g = normalizedAtScale ξ D c g r := by
  ext p
  simp only [scaledField_apply, normalizedAtScale, ContinuousMap.smul_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul, add_zero]

/-- The centered normalized metric is Borel in the field. -/
theorem measurable_scaledField {ξ : ℝ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (c : ℝ → ℝ) (r : ℝ) (z : Rd d) :
    Measurable (scaledField ξ D c r z) := by
  have h1 : Measurable fun g : DistRd d =>
      (D g).1.comp ⟨fun p : Rd d × Rd d =>
        (r • p.1 + z, r • p.2 + z), by fun_prop⟩ :=
    (ContinuousMap.continuous_precomp _).measurable.comp
      (measurable_subtype_coe.comp hD)
  have h2 : Measurable fun g : DistRd d =>
      (c r)⁻¹ * Real.exp (-ξ * sphereAvg g r z) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left r z)))
  exact h2.smul h1

/-- Convergence of the sphere-average sequence persists under a constant shift. -/
private theorem mem_convSet_addConst (hd : 1 ≤ d) {g : DistRd d}
    (hg : g ∈ convSet d) (c : ℝ) : addConst g c ∈ convSet d := by
  obtain ⟨a, ha⟩ := hg
  refine ⟨a + c, ?_⟩
  have he : sphereAvgSeq (addConst g c) 1 0 = fun n => sphereAvgSeq g 1 0 n + c :=
    funext fun n => sphereAvgSeq_addConst hd g c 1 0 n
  rw [he]
  exact ha.add_const c

/-- The normalized LGF law is independent of the sample space and additive constant. -/
theorem map_normalizedLGF_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P') :
    P.map (fun ω => addConst (h ω) (-sphereAvg (h ω) 1 0)) =
      P'.map (fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0)) := by
  have hd1 : 1 ≤ d := by omega
  have hc : ∀ᵐ ω ∂P, h ω ∈ convSet d :=
    hh.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  have hc' : ∀ᵐ ω ∂P', h' ω ∈ convSet d :=
    hh'.ae_exists_tendsto_sphereAvgSeq hd one_pos 0
  have hN := hh.isNormalizedLGF_normalize hd1 hc
  have hN' := hh'.isNormalizedLGF_normalize hd1 hc'
  have hcN : ∀ᵐ ω ∂P, addConst (h ω) (-sphereAvg (h ω) 1 0) ∈ convSet d := by
    filter_upwards [hc] with ω hω
    exact mem_convSet_addConst hd1 hω _
  have hcN' : ∀ᵐ ω ∂P', addConst (h' ω) (-sphereAvg (h' ω) 1 0) ∈ convSet d := by
    filter_upwards [hc'] with ω hω
    exact mem_convSet_addConst hd1 hω _
  exact hN.map_eq hd1 hN' hcN hcN'

/-- Translation covariance and the a.s. sphere-average identity move the center to zero. -/
theorem IsWeakExpMetric.ae_scaledField_translate {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ∀ᵐ ω ∂P, scaledField ξ D c r z (h ω) =
      scaledField ξ D c r 0 (affineComp 1 z (h ω)) := by
  filter_upwards [hD.translation P h hh.isLGFPlusCont z,
    hh.ae_sphereAvg_affineComp hd one_pos z hr 0] with ω ht hs
  ext p
  rw [scaledField_apply, scaledField_apply]
  simp only [one_mul, smul_zero, zero_add] at hs ⊢
  rw [hs, ht]
  simp only [add_zero]

/-- Recentring the field by `h_1(0)` does not alter a normalized metric. -/
theorem IsWeakExpMetric.ae_scaledField_normalize {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, scaledField ξ D c r 0 (h ω) =
      scaledField ξ D c r 0 (addConst (h ω) (-sphereAvg (h ω) 1 0)) := by
  have hd1 : 1 ≤ d := by omega
  filter_upwards [hD.ae_apply_addFun_const hh.isLGFPlusCont,
    hh.ae_exists_tendsto_sphereAvgSeq hd hr 0] with ω hw hc
  obtain ⟨_, hc⟩ := hc
  ext p
  rw [scaledField_apply, scaledField_apply,
    sphereAvg_addConst_of_tendsto hd1 hc (-sphereAvg (h ω) 1 0)]
  have hD_eq := hw (-sphereAvg (h ω) 1 0) (r • p.1 + 0) (r • p.2 + 0)
  simp only [addFun_const] at hD_eq
  rw [hD_eq]
  simp only [add_zero]
  have he : Real.exp (-ξ * (sphereAvg (h ω) r 0 + -sphereAvg (h ω) 1 0)) =
      Real.exp (-ξ * sphereAvg (h ω) r 0) *
        Real.exp (ξ * sphereAvg (h ω) 1 0) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [he]
  have hcancel : Real.exp (ξ * sphereAvg (h ω) 1 0) *
      Real.exp (ξ * -sphereAvg (h ω) 1 0) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  calc
    (c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r 0) *
        (D (h ω)).1 (r • p.1, r • p.2) =
      (c r)⁻¹ * Real.exp (-ξ * sphereAvg (h ω) r 0) *
        (Real.exp (ξ * sphereAvg (h ω) 1 0) *
          Real.exp (ξ * -sphereAvg (h ω) 1 0)) *
        (D (h ω)).1 (r • p.1, r • p.2) := by rw [hcancel]; ring
    _ = _ := by ring

/-- Centered normalized metric laws agree for all whole-space LGFs. -/
theorem IsWeakExpMetric.map_scaledField_eq {Ω Ω' : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {h : Ω → DistRd d} {h' : Ω' → DistRd d}
    {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    (hh : IsWholeSpaceLGF h P) (hh' : IsWholeSpaceLGF h' P')
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    P.map (fun ω => scaledField ξ D c r z (h ω)) =
      P'.map (fun ω => scaledField ξ D c r 0 (h' ω)) := by
  have hz := hh.affineComp one_pos z
  have hF := measurable_scaledField (ξ := ξ) hD.measurable c r 0
  rw [Measure.map_congr (hD.ae_scaledField_translate hd hh hr z),
    Measure.map_congr (hD.ae_scaledField_normalize hd hz hr),
    Measure.map_congr (hD.ae_scaledField_normalize hd hh' hr)]
  have hN := measurable_sphereAvg_left (d := d) 1 0
  have hm1 : Measurable fun ω => addConst (affineComp 1 z (h ω))
      (-sphereAvg (affineComp 1 z (h ω)) 1 0) :=
    (hz.addConst (hN.comp hz.measurable).neg).measurable
  have hm2 : Measurable fun ω => addConst (h' ω) (-sphereAvg (h' ω) 1 0) :=
    (hh'.addConst (hN.comp hh'.measurable).neg).measurable
  have e1 := Measure.map_map (μ := P) hF hm1
  have e2 := Measure.map_map (μ := P') hF hm2
  simp only [Function.comp_def] at e1 e2
  rw [← e1, ← e2, map_normalizedLGF_eq hd hz hh']

/-- The master uniform compact-set estimate behind Lemma R and D-SF5. -/
theorem IsWeakExpMetric.tightMapsTo {ξ : ℝ} {D : DistRd d → ContMetric d}
    {c : ℝ → ℝ} (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {A : ℕ → Set (Rd d × Rd d)} (hA : ∀ n, IsCompact (A n))
    (hAa : Antitone A) {U : ℕ → Set ℝ} (hU : ∀ n, IsOpen (U n))
    (hUm : Monotone U)
    (hmet : ∀ f : C(Rd d × Rd d, ℝ), IsContinuousMetric f →
      ∀ x ∈ ⋂ n, A n, ∃ n, f x ∈ U n)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        P {ω | ¬ MapsTo (scaledField ξ D c r z (h ω)) (A n) (U n)} < ε := by
  obtain ⟨Ω₀, _, P₀, h₀, hP₀, hh₀⟩ := exists_isWholeSpaceLGF (by omega : 1 ≤ d)
  have hT := hD.tight_bdd P₀ h₀ hh₀.isLGFPlusBddCont
  obtain ⟨n, hn⟩ := tightMapsTo_of_tightOver hT hA hAa hU hUm hmet hε
  refine ⟨n, fun P _ h hh r hr z => ?_⟩
  have hfm : Measurable (fun ω => scaledField ξ D c r z (h ω)) :=
    (measurable_scaledField hD.measurable c r z).comp hh.measurable
  have hclosed : MeasurableSet
      {f : C(Rd d × Rd d, ℝ) | ¬ MapsTo f (A n) (U n)} :=
    (LQGMetric.GM.Tight.isClosed_setOf_not_mapsTo (hA n) (hU n)).measurableSet
  rw [show P {ω | ¬ MapsTo (scaledField ξ D c r z (h ω)) (A n) (U n)} =
      (P.map fun ω => scaledField ξ D c r z (h ω))
        {f | ¬ MapsTo f (A n) (U n)} by
      rw [Measure.map_apply_of_aemeasurable hfm.aemeasurable hclosed]; rfl]
  rw [hD.map_scaledField_eq hd hh hh₀ hr z]
  have he : (P₀.map fun ω => scaledField ξ D c r 0 (h₀ ω)) =
      P₀.map (fun ω => normalizedAtScale ξ D c (h₀ ω) r) := by
    congr 1
    funext ω
    exact scaledField_zero ξ D c r (h₀ ω)
  rw [he, Measure.map_apply_of_aemeasurable (hT.1 r hr) hclosed]
  exact hn r hr

/-- S2.4a for centered normalized metrics: a uniform positive lower bound away
from the Euclidean diagonal. -/
theorem IsWeakExpMetric.scaledLowerOffDiag {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {K : Set (Rd d × Rd d)} (hK : IsCompact K)
    (hKd : ∀ p ∈ K, p.1 ≠ p.2)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ r : ℝ, 0 < r → ∀ z : Rd d,
          P {ω | ¬ ∀ p ∈ K, a < scaledField ξ D c r z (h ω) p} < ε := by
  have hanti : Antitone (fun _ : ℕ => K) := fun _ _ _ => le_rfl
  have hmono : Monotone (fun n : ℕ => Ioi ((1 : ℝ) / (n + 1))) := by
    intro m n hmn
    exact Ioi_subset_Ioi
      (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.succ_le_succ hmn))
  obtain ⟨n, hn⟩ := hD.tightMapsTo hd (A := fun _ => K) (fun _ => hK) hanti
    (U := fun n => Ioi ((1 : ℝ) / (n + 1))) (fun _ => isOpen_Ioi) hmono
    (by
      intro f hf p hp
      have hpK : p ∈ K := mem_iInter.1 hp 0
      have hnonneg : 0 ≤ f p := by
        have ht := hf.triangle p.1 p.2 p.1
        rw [hf.self_eq_zero, hf.symm p.2 p.1] at ht
        linarith
      have hpos : 0 < f p := lt_of_le_of_ne hnonneg
        (fun h0 => hKd p hpK (hf.eq_of_eq_zero p.1 p.2 h0.symm))
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact ⟨m, hm⟩) hε
  exact ⟨1 / (n + 1), by positivity, fun P _ h hh r hr z => hn P h hh r hr z⟩

/-- S2.4b for centered normalized metrics: a uniform near-diagonal modulus. -/
theorem IsWeakExpMetric.scaledModulus {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {K : Set (Rd d)} (hK : IsCompact K) {a : ℝ} (ha : 0 < a)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ r : ℝ, 0 < r → ∀ z : Rd d,
          P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ b →
            scaledField ξ D c r z (h ω) (u, v) < a} < ε := by
  have hcomp (b : ℝ) : IsCompact
      {p : Rd d × Rd d | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ b} :=
    (hK.prod hK).inter_right
      (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const)
  obtain ⟨n, hn⟩ := hD.tightMapsTo hd
    (A := fun n => {p : Rd d × Rd d | p ∈ K ×ˢ K ∧
      ‖p.1 - p.2‖ ≤ 1 / (n + 1)})
    (fun n => hcomp _) (fun m n hmn p hp => ⟨hp.1,
      hp.2.trans (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.succ_le_succ hmn))⟩)
    (U := fun _ => Iio a) (fun _ => isOpen_Iio) (fun _ _ _ => le_rfl)
    (by
      intro f hf p hp
      have h0 : ‖p.1 - p.2‖ ≤ 0 := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
        exact ((mem_iInter.1 hp m).2.trans hm.le).trans (by linarith)
      have heq : p.1 = p.2 := sub_eq_zero.1 (norm_le_zero_iff.1 h0)
      refine ⟨0, ?_⟩
      show f p < a
      rcases p with ⟨u, v⟩
      simp only at heq
      subst v
      rw [hf.self_eq_zero]
      exact ha) hε
  refine ⟨1 / (n + 1), by positivity, fun P _ h hh r hr z => ?_⟩
  refine lt_of_le_of_lt (measure_mono ?_) (hn P h hh r hr z)
  intro ω hω hmaps
  exact hω (fun u hu v hv huv => hmaps ⟨⟨hu, hv⟩, huv⟩)

/-- S2.4b′ for centered normalized metrics: uniform compact diameter bounds. -/
theorem IsWeakExpMetric.scaledDiameter {ξ : ℝ}
    {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d)
    {K : Set (Rd d)} (hK : IsCompact K)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ r : ℝ, 0 < r → ∀ z : Rd d,
          P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K,
            scaledField ξ D c r z (h ω) (u, v) < A} < ε := by
  obtain ⟨n, hn⟩ := hD.tightMapsTo hd
    (A := fun _ => K ×ˢ K) (fun _ => hK.prod hK) (fun _ _ _ => le_rfl)
    (U := fun n => Iio ((n : ℝ) + 1)) (fun _ => isOpen_Iio)
    (fun m n hmn => Iio_subset_Iio (by exact_mod_cast Nat.succ_le_succ hmn))
    (fun f _ p _ => by
      obtain ⟨m, hm⟩ := exists_nat_gt (f p)
      exact ⟨m, show f p < (m : ℝ) + 1 by linarith⟩) hε
  refine ⟨n + 1, by positivity, fun P _ h hh r hr z => ?_⟩
  refine lt_of_le_of_lt (measure_mono ?_) (hn P h hh r hr z)
  intro ω hω hmaps
  exact hω (fun u hu v hv => hmaps ⟨hu, hv⟩)

/-- The sharp normalizer is exactly the inverse coefficient of `scaledField`. -/
theorem scaledField_sharp_apply (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (r : ℝ) (z : Rd d) (g : DistRd d) (p : Rd d × Rd d) :
    scaledField ξ D (fun t => t ^ (ξ * Q)) r z g p =
      (sNorm ξ Q g r z)⁻¹ * (D g).1 (r • p.1 + z, r • p.2 + z) := by
  rw [scaledField_apply, sNorm]
  have he : Real.exp (-ξ * sphereAvg g r z) =
      (Real.exp (ξ * sphereAvg g r z))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring_nf
  rw [he, mul_inv_rev]
  ring

end HigherDimLQGMetric
