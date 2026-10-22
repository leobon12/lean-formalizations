import HigherDimLQGMetric.Events.EventLocal

/-! Regular-event invariance under equality of normalized shell data. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem scale_ofReal (s t : ℝ) (hs : 0 < s) :
    ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) = ENNReal.ofReal t := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ s⁻¹)]
  congr 1
  field_simp

private theorem scale_lower_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    ENNReal.ofReal (t * s) ≤ x ↔
      ENNReal.ofReal t ≤ ENNReal.ofReal s⁻¹ * x := by
  constructor
  · intro h
    calc
      ENNReal.ofReal t = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) :=
        (scale_ofReal s t hs).symm
      _ ≤ ENNReal.ofReal s⁻¹ * x := by gcongr
  · exact unscale_lower hs

private theorem scale_upper_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    x ≤ ENNReal.ofReal (t * s) ↔
      ENNReal.ofReal s⁻¹ * x ≤ ENNReal.ofReal t := by
  constructor
  · intro h
    calc
      ENNReal.ofReal s⁻¹ * x ≤ ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) :=
        by gcongr
      _ = ENNReal.ofReal t := scale_ofReal s t hs
  · exact unscale_le hs

private theorem scale_lower_strict_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    ENNReal.ofReal (t * s) < x ↔
      ENNReal.ofReal t < ENNReal.ofReal s⁻¹ * x := by
  constructor
  · intro h
    have hpos : ENNReal.ofReal s⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hs)).ne'
    have hfin : ENNReal.ofReal s⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal t = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) :=
        (scale_ofReal s t hs).symm
      _ < ENNReal.ofReal s⁻¹ * x := by
        simpa only [mul_comm] using ENNReal.mul_lt_mul_left hpos hfin h
  · exact unscale_lower_strict hs

private theorem scale_upper_strict_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    x < ENNReal.ofReal (t * s) ↔
      ENNReal.ofReal s⁻¹ * x < ENNReal.ofReal t := by
  constructor
  · intro h
    have hpos : ENNReal.ofReal s⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hs)).ne'
    have hfin : ENNReal.ofReal s⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal s⁻¹ * x < ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) :=
        by simpa only [mul_comm] using ENNReal.mul_lt_mul_left hpos hfin h
      _ = ENNReal.ofReal t := scale_ofReal s t hs
  · exact unscale_lt hs

private def normSetDist (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (r : ℝ) (z : Rd d) (V K L : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ u ∈ K, ⨅ v ∈ L, normInt ξ Q D g r z V u v

private def normDiam (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (r : ℝ) (z : Rd d) (V K : Set (Rd d)) : ℝ≥0∞ :=
  ⨆ u ∈ K, ⨆ v ∈ K, normInt ξ Q D g r z V u v

private theorem normSetDist_eq (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (r : ℝ) (hr : 0 < r) (z : Rd d) (V K L : Set (Rd d)) :
    normSetDist ξ Q D g r z V K L =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) * setDistIn (D g) V K L := by
  unfold normSetDist normInt setDistIn
  simp only [ENNReal.mul_iInf_of_ne
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sNorm_pos ξ Q g hr z))).ne'
    ENNReal.ofReal_ne_top]

private theorem normDiam_eq (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (r : ℝ) (z : Rd d) (V K : Set (Rd d)) :
    normDiam ξ Q D g r z V K =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) * diamIn (D g) V K := by
  unfold normDiam normInt diamIn
  simp only [ENNReal.mul_iSup]

private def NormReg (A B : DistRd d → ContMetric d)
    (ξ Q U a A₀ ℓ β₀ r : ℝ) (z : Rd d) (g : DistRd d) : Prop :=
  let J := ann z (r / 2) (5 * r)
  let O := ann z (3 * r / 4) (3 * r)
  let K := annCl z r (2 * r)
  ENNReal.ofReal a ≤ normSetDist ξ Q A g r z J (sphere z r) (sphere z (2 * r)) ∧
  normDiam ξ Q A g r z O K ≤ ENNReal.ofReal A₀ ∧
  (∀ ρ ∈ ({3 * r / 4, 3 * r} : Set ℝ),
    ENNReal.ofReal (4 * max 1 U * ℓ) < normSetDist ξ Q A g r z J K (sphere z ρ) ∧
    ENNReal.ofReal (4 * max 1 U * ℓ) < normSetDist ξ Q B g r z J K (sphere z ρ)) ∧
  (∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ β₀ * r →
    normInt ξ Q A g r z O u v < ENNReal.ofReal (ℓ / 4))

private theorem core_subset_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    annCl z r (2 * r) ⊆ ann z (r / 2) (5 * r) := by
  intro x hx
  dsimp [ann, annCl] at hx ⊢
  constructor <;> linarith

private theorem regEvent_iff_normReg
    (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ : ℝ)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (g : DistRd d)
    (hA : (A g).IsLength) :
    g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z ↔
      NormReg A B ξ Q U a A₀ ℓ β₀ r z g := by
  let s := sNorm ξ Q g r z
  have hs : 0 < s := sNorm_pos ξ Q g hr z
  let J := ann z (r / 2) (5 * r)
  let O := ann z (3 * r / 4) (3 * r)
  let K := annCl z r (2 * r)
  have hcross : setDistG (A g) (sphere z r) (sphere z (2 * r)) =
      setDistIn (A g) J (sphere z r) (sphere z (2 * r)) := by
    have hsub : annCl z r (2 * r) ⊆ J := core_subset_outer hr z
    have hc := acrossDist_eq_setDistIn (A g) hA (isOpen_ann _ _ _)
      (show r < 2 * r by linarith) hsub
    exact hc
  have hnJ (D : DistRd d → ContMetric d) (K L : Set (Rd d)) :
      normSetDist ξ Q D g r z J K L =
        ENNReal.ofReal s⁻¹ * setDistIn (D g) J K L :=
    normSetDist_eq ξ Q D g r hr z J K L
  have hnO : normDiam ξ Q A g r z O K =
      ENNReal.ofReal s⁻¹ * diamIn (A g) O K :=
    normDiam_eq ξ Q A g r z O K
  change
    (ENNReal.ofReal (a * s) ≤ setDistG (A g) (sphere z r) (sphere z (2 * r)) ∧
      diamIn (A g) O K ≤ ENNReal.ofReal (A₀ * s) ∧
      (∀ ρ ∈ ({3 * r / 4, 3 * r} : Set ℝ),
        ENNReal.ofReal (4 * max 1 U * ℓ * s) < setDistIn (A g) J K (sphere z ρ) ∧
        ENNReal.ofReal (4 * max 1 U * ℓ * s) < setDistIn (B g) J K (sphere z ρ)) ∧
      (∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ β₀ * r →
        (A g).internal O u v < ENNReal.ofReal (ℓ / 4 * s))) ↔
    (ENNReal.ofReal a ≤ normSetDist ξ Q A g r z J (sphere z r) (sphere z (2 * r)) ∧
      normDiam ξ Q A g r z O K ≤ ENNReal.ofReal A₀ ∧
      (∀ ρ ∈ ({3 * r / 4, 3 * r} : Set ℝ),
        ENNReal.ofReal (4 * max 1 U * ℓ) < normSetDist ξ Q A g r z J K (sphere z ρ) ∧
        ENNReal.ofReal (4 * max 1 U * ℓ) < normSetDist ξ Q B g r z J K (sphere z ρ)) ∧
      (∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ β₀ * r →
        normInt ξ Q A g r z O u v < ENNReal.ofReal (ℓ / 4)))
  rw [hcross, hnJ A, hnO]
  simp_rw [hnJ A, hnJ B, normInt]
  simp only [scale_lower_iff hs, scale_upper_iff hs,
    scale_lower_strict_iff hs, scale_upper_strict_iff hs]
  simp only [s]

/-- Normalized internal metrics agree everywhere once they agree on the domain. -/
theorem normInt_eq_all_of_eq_on
    (D : DistRd d → ContMetric d) (ξ Q : ℝ)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (V : Set (Rd d))
    (g₁ g₂ : DistRd d)
    (he : ∀ u ∈ V, ∀ v ∈ V,
      normInt ξ Q D g₁ r z V u v = normInt ξ Q D g₂ r z V u v) :
    normInt ξ Q D g₁ r z V = normInt ξ Q D g₂ r z V := by
  funext u v
  by_cases hu : u ∈ V
  · by_cases hv : v ∈ V
    · exact he u hu v hv
    · have hf1 : ENNReal.ofReal ((sNorm ξ Q g₁ r z)⁻¹) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sNorm_pos ξ Q g₁ hr z))).ne'
      have hf2 : ENNReal.ofReal ((sNorm ξ Q g₂ r z)⁻¹) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sNorm_pos ξ Q g₂ hr z))).ne'
      simp [normInt, (D g₁).internal_eq_top_of_notMem_right hv,
        (D g₂).internal_eq_top_of_notMem_right hv, ENNReal.mul_top, hf1, hf2]
  · have hf1 : ENNReal.ofReal ((sNorm ξ Q g₁ r z)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sNorm_pos ξ Q g₁ hr z))).ne'
    have hf2 : ENNReal.ofReal ((sNorm ξ Q g₂ r z)⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr (sNorm_pos ξ Q g₂ hr z))).ne'
    simp [normInt, (D g₁).internal_eq_top_of_notMem_left hu,
      (D g₂).internal_eq_top_of_notMem_left hu, ENNReal.mul_top, hf1, hf2]

/-- The regular event depends only on the normalized internal metrics of the
outer shell and the smaller annulus. -/
theorem regEvent_iff_of_normInternal_eq
    (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ : ℝ)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (g₁ g₂ : DistRd d)
    (hA₁ : (A g₁).IsLength) (hA₂ : (A g₂).IsLength)
    (hAJ : ∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
      normInt ξ Q A g₁ r z (ann z (r / 2) (5 * r)) u v =
        normInt ξ Q A g₂ r z (ann z (r / 2) (5 * r)) u v)
    (hBJ : ∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
      normInt ξ Q B g₁ r z (ann z (r / 2) (5 * r)) u v =
        normInt ξ Q B g₂ r z (ann z (r / 2) (5 * r)) u v)
    (hAO : ∀ u ∈ ann z (3 * r / 4) (3 * r), ∀ v ∈ ann z (3 * r / 4) (3 * r),
      normInt ξ Q A g₁ r z (ann z (3 * r / 4) (3 * r)) u v =
        normInt ξ Q A g₂ r z (ann z (3 * r / 4) (3 * r)) u v) :
    g₁ ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z ↔
      g₂ ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z := by
  rw [regEvent_iff_normReg A B ξ Q U a A₀ ℓ β₀ hr z g₁ hA₁,
    regEvent_iff_normReg A B ξ Q U a A₀ ℓ β₀ hr z g₂ hA₂]
  have eAJ := normInt_eq_all_of_eq_on A ξ Q hr z
    (ann z (r / 2) (5 * r)) g₁ g₂ hAJ
  have eBJ := normInt_eq_all_of_eq_on B ξ Q hr z
    (ann z (r / 2) (5 * r)) g₁ g₂ hBJ
  have eAO := normInt_eq_all_of_eq_on A ξ Q hr z
    (ann z (3 * r / 4) (3 * r)) g₁ g₂ hAO
  unfold NormReg normSetDist normDiam
  simp only [eAJ, eBJ, eAO]

/-- D-LOC for the regular event in the sharp weak class. -/
theorem IsSharpWeakExpMetric.aeEventIn_regEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (U a A₀ ℓ β₀ : ℝ) (z : Rd d)
    {r : ℝ} (hr : 0 < r) :
    AEEventIn P (fieldSigma0 h (ann z (r / 2) (5 * r)))
      (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z) := by
  have hmap := hh.map_id
  have hE : NullMeasurableSet (RegEvent A B ξ Q U a A₀ ℓ β₀ r z) (P.map h) :=
    nullMeasurableSet_RegEvent (P.map h) id measurable_id hA.measurable hB.measurable
      ξ Q U a A₀ ℓ β₀ r z
      (hA.length (P.map h) id hmap.isLGFPlusCont)
      (hB.length (P.map h) id hmap.isLGFPlusCont)
  refine aeEventIn_of_normInternal_shell P h hh hA hB hd z hr
    (RegEvent A B ξ Q U a A₀ ℓ β₀ r z) hE ?_
  intro g₁ g₂ hlA₁ _ hlA₂ _ hAJ hBJ hAO _ hmem
  exact (regEvent_iff_of_normInternal_eq A B ξ Q U a A₀ ℓ β₀ hr z g₁ g₂
    hlA₁ hlA₂ hAJ hBJ hAO).mp hmem

theorem IsSharpWeakExpMetric.isShellLocal_regEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (U a A₀ ℓ β₀ : ℝ) :
    IsShellLocal P h (fun z r => h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z) :=
  fun z _ hr => hA.aeEventIn_regEvent P h hh hB hd U a A₀ ℓ β₀ z hr

private theorem scale_factor_cancel {s : ℝ} (hs : 0 < s) (x : ℝ≥0∞) :
    ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * x) = x := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hs.le,
    mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one, one_mul]

private theorem scale_injective {s : ℝ} (hs : 0 < s) {x y : ℝ≥0∞}
    (he : ENNReal.ofReal s⁻¹ * x = ENNReal.ofReal s⁻¹ * y) : x = y := by
  calc
    x = ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * x) :=
      (scale_factor_cancel hs x).symm
    _ = ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * y) := by rw [he]
    _ = y := scale_factor_cancel hs y

private theorem scale_lt_iff {s : ℝ} (hs : 0 < s) {x y : ℝ≥0∞} :
    x < y ↔ ENNReal.ofReal s⁻¹ * x < ENNReal.ofReal s⁻¹ * y := by
  have hf0 : ENNReal.ofReal s⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hs)).ne'
  have hfT : ENNReal.ofReal s⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · intro h
    simpa only [mul_comm] using ENNReal.mul_lt_mul_left hf0 hfT h
  · intro h
    have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
    have hsT : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
    have hh := ENNReal.mul_lt_mul_left hs0 hsT h
    calc
      x = ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * x) :=
        (scale_factor_cancel hs x).symm
      _ < ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * y) := by
        simpa only [mul_comm] using hh
      _ = y := scale_factor_cancel hs y

private theorem normInt_curveLength (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (g : DistRd d) (r : ℝ) (z : Rd d) (O : Set (Rd d))
    (P : ℝ → Rd d) (hPc : ContinuousOn P (Icc 0 1))
    (hPO : MapsTo P (Icc 0 1) O) :
    curveLengthWith (normInt ξ Q D g r z O) P 0 1 =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) * (D g).len P 0 1 := by
  unfold normInt
  rw [curveLengthWith_const_mul, (D g).curveLengthWith_internal hPc hPO]

/-- A path witness is determined by the normalized internal metrics of the
outer shell and the smaller annulus. -/
theorem witEvent_of_normInternal_eq
    (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ t : ℝ)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (g₁ g₂ : DistRd d)
    (hA₁ : (A g₁).IsLength) (hA₂ : (A g₂).IsLength)
    (hAJ : ∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
      normInt ξ Q A g₁ r z (ann z (r / 2) (5 * r)) u v =
        normInt ξ Q A g₂ r z (ann z (r / 2) (5 * r)) u v)
    (hBJ : ∀ u ∈ ann z (r / 2) (5 * r), ∀ v ∈ ann z (r / 2) (5 * r),
      normInt ξ Q B g₁ r z (ann z (r / 2) (5 * r)) u v =
        normInt ξ Q B g₂ r z (ann z (r / 2) (5 * r)) u v)
    (hAO : ∀ u ∈ ann z (3 * r / 4) (3 * r), ∀ v ∈ ann z (3 * r / 4) (3 * r),
      normInt ξ Q A g₁ r z (ann z (3 * r / 4) (3 * r)) u v =
        normInt ξ Q A g₂ r z (ann z (3 * r / 4) (3 * r)) u v)
    (hBO : ∀ u ∈ ann z (3 * r / 4) (3 * r), ∀ v ∈ ann z (3 * r / 4) (3 * r),
      normInt ξ Q B g₁ r z (ann z (3 * r / 4) (3 * r)) u v =
        normInt ξ Q B g₂ r z (ann z (3 * r / 4) (3 * r)) u v)
    (hWit : g₁ ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) :
    g₂ ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z := by
  let O := ann z (3 * r / 4) (3 * r)
  let K := annCl z r (2 * r)
  let s₁ := sNorm ξ Q g₁ r z
  let s₂ := sNorm ξ Q g₂ r z
  have hs₁ : 0 < s₁ := sNorm_pos ξ Q g₁ hr z
  have hs₂ : 0 < s₂ := sNorm_pos ξ Q g₂ hr z
  have hKO : K ⊆ O := by
    intro x hx
    dsimp [K, O, ann, annCl] at hx ⊢
    constructor <;> linarith
  rcases hWit with ⟨hReg, P, hPK, ⟨hPc, hPO, hGeo⟩, hLow, hHigh, hRatio⟩
  have hReg₂ : g₂ ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z :=
    (regEvent_iff_of_normInternal_eq A B ξ Q U a A₀ ℓ β₀ hr z g₁ g₂
      hA₁ hA₂ hAJ hBJ hAO).mp hReg
  have hAOall := normInt_eq_all_of_eq_on A ξ Q hr z O g₁ g₂ hAO
  have hBOall := normInt_eq_all_of_eq_on B ξ Q hr z O g₁ g₂ hBO
  have hLenEq : ENNReal.ofReal s₁⁻¹ * (A g₁).len P 0 1 =
      ENNReal.ofReal s₂⁻¹ * (A g₂).len P 0 1 := by
    calc
      ENNReal.ofReal s₁⁻¹ * (A g₁).len P 0 1 =
          curveLengthWith (normInt ξ Q A g₁ r z O) P 0 1 := by
            rw [normInt_curveLength ξ Q A g₁ r z O P hPc hPO]
      _ = curveLengthWith (normInt ξ Q A g₂ r z O) P 0 1 := by rw [hAOall]
      _ = ENNReal.ofReal s₂⁻¹ * (A g₂).len P 0 1 :=
        normInt_curveLength ξ Q A g₂ r z O P hPc hPO
  have hGeo₂ : (A g₂).len P 0 1 = (A g₂).internal O (P 0) (P 1) := by
    apply scale_injective hs₂
    calc
      ENNReal.ofReal s₂⁻¹ * (A g₂).len P 0 1 =
          ENNReal.ofReal s₁⁻¹ * (A g₁).len P 0 1 := hLenEq.symm
      _ = normInt ξ Q A g₁ r z O (P 0) (P 1) := by rw [hGeo]; rfl
      _ = normInt ξ Q A g₂ r z O (P 0) (P 1) := by rw [hAOall]
      _ = ENNReal.ofReal s₂⁻¹ * (A g₂).internal O (P 0) (P 1) := rfl
  have hLow₂ : ENNReal.ofReal (ℓ / 2 * s₂) ≤ (A g₂).len P 0 1 := by
    apply (scale_lower_iff hs₂).2
    rw [← hLenEq]
    exact (scale_lower_iff hs₁).1 hLow
  have hHigh₂ : (A g₂).len P 0 1 ≤ ENNReal.ofReal (ℓ * s₂) := by
    apply (scale_upper_iff hs₂).2
    rw [← hLenEq]
    exact (scale_upper_iff hs₁).1 hHigh
  have hRatio₂ : ENNReal.ofReal t * (A g₂).len P 0 1 <
      (B g₂).internal O (P 0) (P 1) := by
    apply (scale_lt_iff hs₂).2
    have hr₁ := (scale_lt_iff hs₁).1 hRatio
    calc
      ENNReal.ofReal s₂⁻¹ * (ENNReal.ofReal t * (A g₂).len P 0 1) =
          ENNReal.ofReal t * (ENNReal.ofReal s₁⁻¹ * (A g₁).len P 0 1) := by
            rw [mul_left_comm, ← hLenEq]
      _ < normInt ξ Q B g₁ r z O (P 0) (P 1) := by
        simpa only [normInt, mul_left_comm] using hr₁
      _ = normInt ξ Q B g₂ r z O (P 0) (P 1) := by rw [hBOall]
      _ = ENNReal.ofReal s₂⁻¹ * (B g₂).internal O (P 0) (P 1) := rfl
  exact ⟨hReg₂, P, hPK, ⟨hPc, hPO, hGeo₂⟩, hLow₂, hHigh₂, hRatio₂⟩

/-- D-LOC for the existential witness event. -/
theorem IsSharpWeakExpMetric.aeEventIn_witEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (U a A₀ ℓ β₀ t : ℝ) (z : Rd d)
    {r : ℝ} (hr : 0 < r) :
    AEEventIn P (fieldSigma0 h (ann z (r / 2) (5 * r)))
      (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) := by
  have hmap := hh.map_id
  have hE : NullMeasurableSet (WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) (P.map h) :=
    hA.nullMeasurableSet_witEvent (P.map h) id hmap hB U a A₀ ℓ β₀ t hr z
  refine aeEventIn_of_normInternal_shell P h hh hA hB hd z hr
    (WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) hE ?_
  intro g₁ g₂ hlA₁ _ hlA₂ _ hAJ hBJ hAO hBO hmem
  exact witEvent_of_normInternal_eq A B ξ Q U a A₀ ℓ β₀ t hr z g₁ g₂
    hlA₁ hlA₂ hAJ hBJ hAO hBO hmem

theorem IsSharpWeakExpMetric.isShellLocal_witEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (U a A₀ ℓ β₀ t : ℝ) :
    IsShellLocal P h (fun z r => h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) :=
  fun z _ hr => hA.aeEventIn_witEvent P h hh hB hd U a A₀ ℓ β₀ t z hr

/-- The shell event used by Lemma 5.2, regularity without a witness. -/
theorem IsSharpWeakExpMetric.aeEventIn_regDiffWit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (U a A₀ ℓ β₀ t : ℝ) (z : Rd d)
    {r : ℝ} (hr : 0 < r) :
    AEEventIn P (fieldSigma0 h (ann z (r / 2) (5 * r)))
      (h ⁻¹' (RegEvent A B ξ Q U a A₀ ℓ β₀ r z \
        WitEvent A B ξ Q U a A₀ ℓ β₀ t r z)) := by
  obtain ⟨F, hFm, hFe⟩ := hA.aeEventIn_regEvent P h hh hB hd U a A₀ ℓ β₀ z hr
  obtain ⟨G, hGm, hGe⟩ := hA.aeEventIn_witEvent P h hh hB hd U a A₀ ℓ β₀ t z hr
  refine ⟨F \ G, hFm.diff hGm, ?_⟩
  simpa only [preimage_sdiff] using hFe.diff hGe

theorem IsSharpWeakExpMetric.isShellLocal_regDiffWit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (hd : 2 ≤ d) (U a A₀ ℓ β₀ t : ℝ) :
    IsShellLocal P h (fun z r => h ⁻¹'
      (RegEvent A B ξ Q U a A₀ ℓ β₀ r z \
        WitEvent A B ξ Q U a A₀ ℓ β₀ t r z)) :=
  fun z _ hr => hA.aeEventIn_regDiffWit P h hh hB hd U a A₀ ℓ β₀ t z hr

end HigherDimLQGMetric
