import HigherDimLQGMetric.Events.AnalyticQuant
import HigherDimLQGMetric.Events.RegularProof

/-! Universal measurability of the source regular event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem measurable_sNorm (ξ Q r : ℝ) (z : Rd d) :
    Measurable fun g : DistRd d => sNorm ξ Q g r z :=
  measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul (measurable_sphereAvg_left r z)))

private theorem measurable_setDistG (K L : Set (Rd d)) :
    Measurable fun D : ContMetric d => setDistG D K L := by
  have he : (fun D : ContMetric d => setDistG D K L) =
      fun D => ⨅ p ∈ K ×ˢ L, ENNReal.ofReal (D.1 p) := by
    funext D
    unfold setDistG
    rw [biInf_prod]
  rw [he]
  refine LQGMetric.measurable_biInf_of_continuous
    (f := fun (D : ContMetric d) (p : Rd d × Rd d) => ENNReal.ofReal (D.1 p))
    (fun D => ENNReal.continuous_ofReal.comp D.1.continuous) (fun p => ?_) _
  exact (ENNReal.continuous_ofReal.comp
    (continuous_contMetric_apply_select.comp
      (continuous_id.prodMk continuous_const))).measurable

private def chainSetDist (D : ContMetric d) (V K L : Set (Rd d)) : ℝ≥0∞ :=
  ⨅ u ∈ K, ⨅ v ∈ L, D.chainInf V u v

private def chainDiam (D : ContMetric d) (V K : Set (Rd d)) : ℝ≥0∞ :=
  ⨆ u ∈ K, ⨆ v ∈ K, D.chainInf V u v

private def RegEventChain (A B : DistRd d → ContMetric d)
    (ξ Q U a A₀ ℓ β₀ r : ℝ) (z : Rd d) : Set (DistRd d) :=
  {g |
    ENNReal.ofReal (a * sNorm ξ Q g r z) ≤
      setDistG (A g) (sphere z r) (sphere z (2 * r)) ∧
    chainDiam (A g) (ann z (3 * r / 4) (3 * r)) (annCl z r (2 * r)) ≤
      ENNReal.ofReal (A₀ * sNorm ξ Q g r z) ∧
    (∀ ρ ∈ ({3 * r / 4, 3 * r} : Set ℝ),
      ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z) <
        chainSetDist (A g) (ann z (r / 2) (5 * r))
          (annCl z r (2 * r)) (sphere z ρ) ∧
      ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z) <
        chainSetDist (B g) (ann z (r / 2) (5 * r))
          (annCl z r (2 * r)) (sphere z ρ)) ∧
    (∀ u ∈ annCl z r (2 * r), ∀ v ∈ annCl z r (2 * r), ‖u - v‖ ≤ β₀ * r →
      (A g).chainInf (ann z (3 * r / 4) (3 * r)) u v <
        ENNReal.ofReal (ℓ / 4 * sNorm ξ Q g r z))}

private theorem measurable_chainKernel {D : DistRd d → ContMetric d}
    (hD : Measurable D) (V : Set (Rd d)) :
    Measurable fun p : DistRd d × (Rd d × Rd d) =>
      (D p.1).chainInf V p.2.1 p.2.2 :=
  (ContMetric.measurable_chainInf V).comp
    ((hD.comp measurable_fst).prodMk measurable_snd)

private theorem measurableSet_pairCore (z : Rd d) (r : ℝ) :
    MeasurableSet (annCl z r (2 * r) ×ˢ annCl z r (2 * r)) :=
  (isClosed_annCl z r (2 * r)).measurableSet.prod
    (isClosed_annCl z r (2 * r)).measurableSet

private theorem uMeasurableSet_RegEventChain
    {A B : DistRd d → ContMetric d} (hA : Measurable A) (hB : Measurable B)
    (ξ Q U a A₀ ℓ β₀ r : ℝ) (z : Rd d) :
    UMeasurableSet (RegEventChain A B ξ Q U a A₀ ℓ β₀ r z) := by
  let K := annCl z r (2 * r)
  let O := ann z (3 * r / 4) (3 * r)
  let J := ann z (r / 2) (5 * r)
  have hs : Measurable fun g : DistRd d => sNorm ξ Q g r z :=
    measurable_sNorm ξ Q r z
  have hcross : UMeasurableSet {g : DistRd d |
      ENNReal.ofReal (a * sNorm ξ Q g r z) ≤
        setDistG (A g) (sphere z r) (sphere z (2 * r))} :=
    UMeasurableSet.of_measurableSet (measurableSet_le
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hs))
      ((measurable_setDistG _ _).comp hA))
  have hpair : MeasurableSet (K ×ˢ K) := measurableSet_pairCore z r
  have hdiam : UMeasurableSet {g : DistRd d |
      chainDiam (A g) O K ≤ ENNReal.ofReal (A₀ * sNorm ξ Q g r z)} := by
    have hm := uMeasurableSet_iSup_le (K ×ˢ K) hpair
      (measurable_chainKernel hA O)
      (c := fun g => ENNReal.ofReal (A₀ * sNorm ξ Q g r z))
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hs))
    convert hm using 1
    ext g
    simp only [chainDiam, biSup_prod]
  have hcoll (D : DistRd d → ContMetric d) (hD : Measurable D) (ρ : ℝ) :
      UMeasurableSet {g : DistRd d |
        ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z) <
          chainSetDist (D g) J K (sphere z ρ)} := by
    have hKρ : MeasurableSet (K ×ˢ sphere z ρ) :=
      (isClosed_annCl z r (2 * r)).measurableSet.prod (isClosed_sphere).measurableSet
    have hm := uMeasurableSet_lt_iInf (K ×ˢ sphere z ρ) hKρ
      (measurable_chainKernel hD J)
      (c := fun g => ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z))
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hs))
    convert hm using 1
    ext g
    simp only [chainSetDist, biInf_prod]
  have hcollBoth (ρ : ℝ) : UMeasurableSet {g : DistRd d |
      ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z) <
        chainSetDist (A g) J K (sphere z ρ) ∧
      ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z) <
        chainSetDist (B g) J K (sphere z ρ)} :=
    (hcoll A hA ρ).inter (hcoll B hB ρ)
  have hcollAll : UMeasurableSet {g : DistRd d |
      ∀ ρ ∈ ({3 * r / 4, 3 * r} : Set ℝ),
        ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z) <
          chainSetDist (A g) J K (sphere z ρ) ∧
        ENNReal.ofReal (4 * max 1 U * ℓ * sNorm ξ Q g r z) <
          chainSetDist (B g) J K (sphere z ρ)} := by
    convert (hcollBoth (3 * r / 4)).inter (hcollBoth (3 * r)) using 1
    ext g
    simp [mem_insert_iff]
  have hmod : UMeasurableSet {g : DistRd d |
      ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ β₀ * r →
        (A g).chainInf O u v < ENNReal.ofReal (ℓ / 4 * sNorm ξ Q g r z)} := by
    let L : Set (Rd d × Rd d) :=
      {p | p ∈ K ×ˢ K ∧ ‖p.1 - p.2‖ ≤ β₀ * r}
    have hL : MeasurableSet L := hpair.inter
      (isClosed_le (continuous_fst.sub continuous_snd).norm continuous_const).measurableSet
    have hRel : MeasurableSet {p : DistRd d × (Rd d × Rd d) |
        (A p.1).chainInf O p.2.1 p.2.2 <
          ENNReal.ofReal (ℓ / 4 * sNorm ξ Q p.1 r z)} :=
      measurableSet_lt (measurable_chainKernel hA O)
        ((ENNReal.measurable_ofReal.comp (measurable_const.mul hs)).comp measurable_fst)
    have hm := uMeasurableSet_forall_mem L hL hRel
    convert hm using 1
    ext g
    constructor
    · intro hg b hb
      exact hg b.1 hb.1.1 b.2 hb.1.2 hb.2
    · intro hg u hu v hv huv
      exact hg (u, v) ⟨⟨hu, hv⟩, huv⟩
  exact hcross.inter (hdiam.inter (hcollAll.inter hmod))

private theorem regEvent_iff_chain (A B : DistRd d → ContMetric d)
    (ξ Q U a A₀ ℓ β₀ r : ℝ) (z : Rd d)
    (g : DistRd d) (hA : (A g).IsLength) (hB : (B g).IsLength) :
    g ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z ↔
      g ∈ RegEventChain A B ξ Q U a A₀ ℓ β₀ r z := by
  let J := ann z (r / 2) (5 * r)
  let O := ann z (3 * r / 4) (3 * r)
  have hAJ : (A g).internal J = (A g).chainInf J := by
    funext u v
    exact (A g).internal_eq_chainInf hA (isOpen_ann _ _ _) u v
  have hAO : (A g).internal O = (A g).chainInf O := by
    funext u v
    exact (A g).internal_eq_chainInf hA (isOpen_ann _ _ _) u v
  have hBJ : (B g).internal J = (B g).chainInf J := by
    funext u v
    exact (B g).internal_eq_chainInf hB (isOpen_ann _ _ _) u v
  dsimp only [J, O] at hAJ hAO hBJ
  simp only [RegEvent, RegEventChain, mem_ofPred_eq, setDistIn, diamIn,
    chainSetDist, chainDiam, hAJ, hAO, hBJ]

/-- The regular event is measurable in the completion of every LGF law.
The quantified internal distances are replaced a.s. by rational-chain
formulas, whose bad sets are analytic projections. -/
theorem nullMeasurableSet_RegEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : Measurable h)
    {A B : DistRd d → ContMetric d} (hA : Measurable A) (hB : Measurable B)
    (ξ Q U a A₀ ℓ β₀ r : ℝ) (z : Rd d)
    (hLenA : ∀ᵐ ω ∂P, (A (h ω)).IsLength)
    (hLenB : ∀ᵐ ω ∂P, (B (h ω)).IsLength) :
    NullMeasurableSet (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z) P := by
  have hC : NullMeasurableSet
      (h ⁻¹' RegEventChain A B ξ Q U a A₀ ℓ β₀ r z) P :=
    (uMeasurableSet_RegEventChain hA hB ξ Q U a A₀ ℓ β₀ r z).nullMeasurableSet_preimage
      hh.aemeasurable
  have he : h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z =ᵐ[P]
      h ⁻¹' RegEventChain A B ξ Q U a A₀ ℓ β₀ r z := by
    filter_upwards [hLenA, hLenB] with ω hlA hlB
    exact propext (regEvent_iff_chain A B ξ Q U a A₀ ℓ β₀ r z (h ω) hlA hlB)
  exact hC.congr he.symm

/-- D-MEAS for the regular event under the sharp weak metric axioms. -/
theorem IsSharpWeakExpMetric.nullMeasurableSet_regEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (U a A₀ ℓ β₀ r : ℝ) (z : Rd d) :
    NullMeasurableSet (h ⁻¹' RegEvent A B ξ Q U a A₀ ℓ β₀ r z) P :=
  nullMeasurableSet_RegEvent P h hh.measurable hA.measurable hB.measurable
    ξ Q U a A₀ ℓ β₀ r z (hA.length P h hh.isLGFPlusCont)
      (hB.length P h hh.isLGFPlusCont)

/-- D-MEAS for the path-witness event under the sharp weak metric axioms. -/
theorem IsSharpWeakExpMetric.nullMeasurableSet_witEvent
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} {A B : DistRd d → ContMetric d}
    (hA : IsSharpWeakExpMetric d ξ Q A)
    (hB : IsSharpWeakExpMetric d ξ Q B)
    (U a A₀ ℓ β₀ t : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    NullMeasurableSet (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t r z) P := by
  exact nullMeasurableSet_witEvent_of_regular P h hh.measurable
    hA.measurable hB.measurable ξ Q U a A₀ ℓ β₀ t hr z
    (hA.length P h hh.isLGFPlusCont) (hB.length P h hh.isLGFPlusCont)
    (hA.nullMeasurableSet_regEvent P h hh hB U a A₀ ℓ β₀ r z)

end HigherDimLQGMetric
