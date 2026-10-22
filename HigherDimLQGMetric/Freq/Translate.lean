import HigherDimLQGMetric.Freq.ConstLaw
import HigherDimLQGMetric.Amplify.LengthScale

/-! Translation of the Section 5 events. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set MeasureTheory Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A centered field's metric agrees with the affine pullback at a fixed shift. -/
theorem IsSharpWeakExpMetric.ae_metric_translate
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (z : Rd d) :
    ∀ᵐ ω ∂P, D (affineComp 1 z (h ω)) = (D (h ω)).affine 1 (by norm_num) z := by
  filter_upwards [hD.translation P h hh.isLGFPlusCont z] with ω ht
  apply Subtype.ext
  ext p
  simpa only [ContMetric.affine_apply, one_smul] using ht p.1 p.2

private theorem s4c_image_ann_one (z : Rd d) (a b : ℝ) :
    (fun x : Rd d => x + z) '' ann 0 a b = ann z a b := by
  simpa only [one_smul, one_mul] using image_ann_affine (r := 1) one_pos z a b

private theorem s4c_image_annCl_one (z : Rd d) (a b : ℝ) :
    (fun x : Rd d => x + z) '' annCl 0 a b = annCl z a b := by
  simpa only [one_smul, one_mul] using image_annCl_affine (r := 1) one_pos z a b

private theorem s4c_image_sphere_one (z : Rd d) (a : ℝ) :
    (fun x : Rd d => x + z) '' sphere 0 a = sphere z a := by
  simpa only [one_smul, one_mul] using image_sphere_affine (r := 1) one_pos z a

private theorem s4c_ann_translate_iff (z u : Rd d) (a b : ℝ) :
    u ∈ ann 0 a b ↔ u + z ∈ ann z a b := by
  simp only [ann, mem_ofPred_eq, sub_zero]
  simp

private theorem s4c_annCl_translate_iff (z u : Rd d) (a b : ℝ) :
    u ∈ annCl 0 a b ↔ u + z ∈ annCl z a b := by
  simp only [annCl, mem_ofPred_eq, sub_zero]
  simp

private theorem s4c_setDist_translate (D : ContMetric d) (z : Rd d) (r : ℝ) :
    setDistG (D.affine 1 (by norm_num) z) (sphere 0 r) (sphere 0 (2 * r)) =
      setDistG D (sphere z r) (sphere z (2 * r)) := by
  simpa only [setDistG, acrossDist, one_mul] using
    (acrossDist_affine (r := 1) one_pos z D r (2 * r))

private theorem s4c_diam_translate (D : ContMetric d) (z : Rd d) (r : ℝ) :
    diamIn (D.affine 1 (by norm_num) z)
      (ann 0 (3 * r / 4) (3 * r)) (annCl 0 r (2 * r)) =
    diamIn D (ann z (3 * r / 4) (3 * r)) (annCl z r (2 * r)) := by
  rw [diamIn_affine]
  simp only [one_smul, s4c_image_ann_one, s4c_image_annCl_one]

private theorem s4c_setDistIn_translate (D : ContMetric d) (z : Rd d)
    (r ρ : ℝ) :
    setDistIn (D.affine 1 (by norm_num) z)
      (ann 0 (r / 2) (5 * r)) (annCl 0 r (2 * r)) (sphere 0 ρ) =
    setDistIn D (ann z (r / 2) (5 * r)) (annCl z r (2 * r)) (sphere z ρ) := by
  rw [setDistIn_affine]
  simp only [one_smul, s4c_image_ann_one, s4c_image_annCl_one,
    s4c_image_sphere_one]

/-- The regular shell event is equivariant under translations. -/
theorem s4c_regEvent_translate (A B : DistRd d → ContMetric d)
    (ξ Q U a A₀ ℓ β₀ r : ℝ) (z : Rd d) (g gt : DistRd d)
    (hA : A gt = (A g).affine 1 (by norm_num) z)
    (hB : B gt = (B g).affine 1 (by norm_num) z)
    (hs : sNorm ξ Q gt r 0 = sNorm ξ Q g r z) :
    gt ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r 0 ↔
      g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z := by
  have hcross : setDistG (A gt) (sphere 0 r) (sphere 0 (2 * r)) =
      setDistG (A g) (sphere z r) (sphere z (2 * r)) := by
    rw [hA]
    exact s4c_setDist_translate (A g) z r
  have hdiam : diamIn (A gt) (ann 0 (3 * r / 4) (3 * r)) (annCl 0 r (2 * r)) =
      diamIn (A g) (ann z (3 * r / 4) (3 * r)) (annCl z r (2 * r)) := by
    rw [hA]
    exact s4c_diam_translate (A g) z r
  have hcollA : ∀ ρ : ℝ,
      setDistIn (A gt) (ann 0 (r / 2) (5 * r)) (annCl 0 r (2 * r)) (sphere 0 ρ) =
      setDistIn (A g) (ann z (r / 2) (5 * r)) (annCl z r (2 * r)) (sphere z ρ) := by
    intro ρ
    rw [hA]
    exact s4c_setDistIn_translate (A g) z r ρ
  have hcollB : ∀ ρ : ℝ,
      setDistIn (B gt) (ann 0 (r / 2) (5 * r)) (annCl 0 r (2 * r)) (sphere 0 ρ) =
      setDistIn (B g) (ann z (r / 2) (5 * r)) (annCl z r (2 * r)) (sphere z ρ) := by
    intro ρ
    rw [hB]
    exact s4c_setDistIn_translate (B g) z r ρ
  have hmod :
      (∀ u ∈ annCl 0 r (2 * r), ∀ v ∈ annCl 0 r (2 * r),
        ‖u - v‖ ≤ β₀ * r →
          (A gt).internal (ann 0 (3 * r / 4) (3 * r)) u v <
            ENNReal.ofReal (ℓ / 4 * sNorm ξ Q gt r 0)) ↔
      (∀ u ∈ annCl z r (2 * r), ∀ v ∈ annCl z r (2 * r),
        ‖u - v‖ ≤ β₀ * r →
          (A g).internal (ann z (3 * r / 4) (3 * r)) u v <
            ENNReal.ofReal (ℓ / 4 * sNorm ξ Q g r z)) := by
    rw [← s4c_image_annCl_one z r (2 * r)]
    simp only [forall_mem_image, hA, hs, ContMetric.internal_affine,
      one_smul, s4c_image_ann_one]
    simp only [add_sub_add_right_eq_sub]
  simp only [RegEvent, mem_ofPred_eq, hcross, hdiam, hcollA, hcollB]
  rw [hmod, hs]

/-- The path-witness event is equivariant under translations of the field and
both metrics. -/
theorem s4c_witEvent_translate (A B : DistRd d → ContMetric d)
    (ξ Q U a A₀ ℓ β₀ t r : ℝ) (z : Rd d) (g gt : DistRd d)
    (hA : A gt = (A g).affine 1 (by norm_num) z)
    (hB : B gt = (B g).affine 1 (by norm_num) z)
    (hs : sNorm ξ Q gt r 0 = sNorm ξ Q g r z) :
    gt ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0 ↔
      g ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z := by
  let O0 := ann (0 : Rd d) (3 * r / 4) (3 * r)
  let Oz := ann z (3 * r / 4) (3 * r)
  let K0 := annCl (0 : Rd d) r (2 * r)
  let Kz := annCl z r (2 * r)
  have hreg := s4c_regEvent_translate A B ξ Q U a A₀ ℓ β₀ r z g gt hA hB hs
  have hlen (P : ℝ → Rd d) :
      (A gt).len P 0 1 = (A g).len (fun s => P s + z) 0 1 := by
    rw [hA, amplify_len_affine]
    simp only [one_smul]
  have hintA (P : ℝ → Rd d) :
      (A gt).internal O0 (P 0) (P 1) =
        (A g).internal Oz (P 0 + z) (P 1 + z) := by
    rw [hA, ContMetric.internal_affine]
    simp only [one_smul]
    change (A g).internal ((fun a => a + z) '' ann 0 (3 * r / 4) (3 * r))
        (P 0 + z) (P 1 + z) = _
    rw [s4c_image_ann_one]
  have hintB (P : ℝ → Rd d) :
      (B gt).internal O0 (P 0) (P 1) =
        (B g).internal Oz (P 0 + z) (P 1 + z) := by
    rw [hB, ContMetric.internal_affine]
    simp only [one_smul]
    change (B g).internal ((fun a => a + z) '' ann 0 (3 * r / 4) (3 * r))
        (P 0 + z) (P 1 + z) = _
    rw [s4c_image_ann_one]
  have hgeo (P : ℝ → Rd d) :
      IsGeodIn (A gt) O0 P ↔
        IsGeodIn (A g) Oz (fun s => P s + z) := by
    constructor
    · rintro ⟨hc, hO, he⟩
      refine ⟨hc.add continuousOn_const, ?_, ?_⟩
      · intro s hsI
        exact (s4c_ann_translate_iff z (P s) _ _).mp (hO s hsI)
      · rw [← hlen, ← hintA]
        exact he
    · rintro ⟨hc, hO, he⟩
      refine ⟨?_, ?_, ?_⟩
      · have heq : ((fun s => P s + z) - fun _ : ℝ => z) = P := by
          funext s
          simp
        rw [← heq]
        exact hc.sub (continuousOn_const : ContinuousOn (fun _ : ℝ => z) (Icc 0 1))
      · intro s hsI
        exact (s4c_ann_translate_iff z (P s) _ _).mpr (hO s hsI)
      · rw [hlen, hintA]
        exact he
  have hcore (P : ℝ → Rd d) :
      (∀ s ∈ Icc (0 : ℝ) 1, P s ∈ K0) ↔
        (∀ s ∈ Icc (0 : ℝ) 1, P s + z ∈ Kz) := by
    exact forall_congr' fun s => imp_congr_right fun _ =>
      s4c_annCl_translate_iff z (P s) r (2 * r)
  have hpath (P : ℝ → Rd d) :
      ((∀ s ∈ Icc (0 : ℝ) 1, P s ∈ K0) ∧
        IsGeodIn (A gt) O0 P ∧
        ENNReal.ofReal (ℓ / 2 * sNorm ξ Q gt r 0) ≤ (A gt).len P 0 1 ∧
        (A gt).len P 0 1 ≤ ENNReal.ofReal (ℓ * sNorm ξ Q gt r 0) ∧
        ENNReal.ofReal t * (A gt).len P 0 1 < (B gt).internal O0 (P 0) (P 1)) ↔
      ((∀ s ∈ Icc (0 : ℝ) 1, P s + z ∈ Kz) ∧
        IsGeodIn (A g) Oz (fun s => P s + z) ∧
        ENNReal.ofReal (ℓ / 2 * sNorm ξ Q g r z) ≤
          (A g).len (fun s => P s + z) 0 1 ∧
        (A g).len (fun s => P s + z) 0 1 ≤
          ENNReal.ofReal (ℓ * sNorm ξ Q g r z) ∧
        ENNReal.ofReal t * (A g).len (fun s => P s + z) 0 1 <
          (B g).internal Oz (P 0 + z) (P 1 + z)) := by
    rw [hcore, hgeo, hs, hlen, hintB]
  constructor
  · rintro ⟨hR, P, hP⟩
    refine ⟨hreg.mp hR, (fun s => P s + z), ?_⟩
    simpa only using (hpath P).mp hP
  · rintro ⟨hR, W, hW⟩
    let P : ℝ → Rd d := fun s => W s - z
    refine ⟨hreg.mpr hR, P, ?_⟩
    have hQ' : (∀ s ∈ Icc (0 : ℝ) 1, P s + z ∈ Kz) ∧
        IsGeodIn (A g) Oz (fun s => P s + z) ∧
        ENNReal.ofReal (ℓ / 2 * sNorm ξ Q g r z) ≤
          (A g).len (fun s => P s + z) 0 1 ∧
        (A g).len (fun s => P s + z) 0 1 ≤
          ENNReal.ofReal (ℓ * sNorm ξ Q g r z) ∧
        ENNReal.ofReal t * (A g).len (fun s => P s + z) 0 1 <
          (B g).internal Oz (P 0 + z) (P 1 + z) := by
      simpa only [P, sub_add_cancel] using hW
    exact (hpath P).mpr hQ'

/-- Translation stationarity of witness probabilities. The fixed-center law
transfer supplies the second equality after translating the field. -/
theorem s4c_witEvent_law_center
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B) (hd : 2 ≤ d)
    (U a A₀ ℓ β₀ t : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) =
      P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0) := by
  let ht : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  have hht : IsWholeSpaceLGF ht P := hh.affineComp one_pos z
  have hmove : ∀ᵐ ω ∂P,
      ht ω ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0 ↔
        h ω ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z := by
    filter_upwards [hA.ae_metric_translate P h hh z,
      hB.ae_metric_translate P h hh z,
      hh.ae_sphereAvg_affineComp hd one_pos z hr 0]
      with ω hmA hmB hsph
    have hs : sNorm ξ Q (ht ω) r 0 = sNorm ξ Q (h ω) r z := by
      simp only [ht, sNorm]
      simpa only [one_mul, smul_zero, zero_add] using congrArg
        (fun v : ℝ => r ^ (ξ * Q) * Real.exp (ξ * v)) hsph
    exact s4c_witEvent_translate A B ξ Q U a A₀ ℓ β₀ t r z (h ω) (ht ω)
      hmA hmB hs
  have hsets : h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z =ᵐ[P]
      ht ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0 := by
    filter_upwards [hmove] with ω hw
    exact propext hw.symm
  calc
    P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) =
        P (ht ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0) := measure_congr hsets
    _ = P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0) :=
      s4c_witEvent_law_eq P P ht h hht hh hA hB hd U a A₀ ℓ β₀ t hr 0

end HigherDimLQGMetric
