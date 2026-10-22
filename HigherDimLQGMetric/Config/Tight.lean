import HigherDimLQGMetric.Config.TightGeometry
import HigherDimLQGMetric.Config.Measurable
import HigherDimLQGMetric.Events.TightLaw
import HigherDimLQGMetric.Core.Interfaces
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative ingredients for D-SF5. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Topology Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Any compact subset of an open Euclidean annulus fits inside a compact
connected closed annulus in the same domain. -/
theorem config_exists_connected_compact_superset
    (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {L : Set (Rd d)} (hL : IsCompact L) (hLU : L ⊆ ann 0 a b) :
    ∃ K : Set (Rd d), IsCompact K ∧ IsConnected K ∧
      L ⊆ K ∧ K ⊆ ann 0 a b := by
  by_cases hne : L.Nonempty
  · obtain ⟨u, hu, hmin⟩ := hL.exists_isMinOn hne continuous_norm.continuousOn
    obtain ⟨v, hv, hmax⟩ := hL.exists_isMaxOn hne continuous_norm.continuousOn
    let a' : ℝ := (a + ‖u‖) / 2
    let b' : ℝ := (b + ‖v‖) / 2
    have hua : a < ‖u‖ := by simpa only [ann, mem_ofPred_eq, sub_zero] using (hLU hu).1
    have hvb : ‖v‖ < b := by simpa only [ann, mem_ofPred_eq, sub_zero] using (hLU hv).2
    have huv : ‖u‖ ≤ ‖v‖ := hmin hv
    have ha' : 0 < a' := by dsimp [a']; linarith
    have hab' : a' ≤ b' := by dsimp [a', b']; linarith
    refine ⟨annCl 0 a' b', ?_, isConnected_annCl hd 0 ha' hab', ?_, ?_⟩
    · refine isCompact_of_isClosed_isBounded (isClosed_annCl _ _ _) ?_
      apply (isBounded_closedBall : Bornology.IsBounded
        (Metric.closedBall (0 : Rd d) b')).subset
      intro x hx
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx.2
    · intro x hx
      have hxl : ‖u‖ ≤ ‖x‖ := hmin hx
      have hxu : ‖x‖ ≤ ‖v‖ := hmax hx
      change a' ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ b'
      simp only [sub_zero]
      constructor <;> dsimp [a', b'] <;> linarith
    · intro x hx
      change a < ‖x - 0‖ ∧ ‖x - 0‖ < b
      change a' ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ b' at hx
      constructor <;> dsimp [a', b'] at * <;> linarith
  · let a' : ℝ := (2 * a + b) / 3
    let b' : ℝ := (a + 2 * b) / 3
    have ha' : 0 < a' := by dsimp [a']; linarith
    have hab' : a' ≤ b' := by dsimp [a', b']; linarith
    refine ⟨annCl 0 a' b', ?_, isConnected_annCl hd 0 ha' hab', ?_, ?_⟩
    · refine isCompact_of_isClosed_isBounded (isClosed_annCl _ _ _) ?_
      apply (isBounded_closedBall : Bornology.IsBounded
        (Metric.closedBall (0 : Rd d) b')).subset
      intro x hx
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx.2
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      exact empty_subset _
    · intro x hx
      change a < ‖x - 0‖ ∧ ‖x - 0‖ < b
      change a' ≤ ‖x - 0‖ ∧ ‖x - 0‖ ≤ b' at hx
      constructor <;> dsimp [a', b'] at * <;> linarith

/-- Pairs from a compact annular set separated in Euclidean distance. -/
def configOffDiagSet {U : Set (Rd d)} (L : Set U) (η : ℝ) :
    Set (Rd d × Rd d) :=
  {p | p.1 ∈ Subtype.val '' L ∧ p.2 ∈ Subtype.val '' L ∧ η ≤ dist p.1 p.2}

theorem configOffDiagSet_isCompact {U : Set (Rd d)} {L : Set U}
    (hL : IsCompact L) (η : ℝ) :
    IsCompact (configOffDiagSet L η) := by
  have hLi : IsCompact (Subtype.val '' L) := hL.image continuous_subtype_val
  have hc : IsCompact (((Subtype.val '' L) ×ˢ (Subtype.val '' L)) ∩
      {p : Rd d × Rd d | η ≤ dist p.1 p.2}) :=
    (hLi.prod hLi).inter_right
      (isClosed_le continuous_const ((continuous_fst).dist continuous_snd))
  convert hc using 1
  ext p
  simp only [configOffDiagSet, mem_ofPred_eq, mem_inter_iff, mem_prod, and_assoc]

theorem configOffDiagSet_ne {U : Set (Rd d)} {L : Set U}
    {η : ℝ} (hη : 0 < η) (p : Rd d × Rd d)
    (hp : p ∈ configOffDiagSet L η) : p.1 ≠ p.2 := by
  intro heq
  have hsep := hp.2.2
  rw [heq, dist_self] at hsep
  exact (not_le_of_gt hη) hsep

theorem configScaledMetric_apply_sharp (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (g : DistRd d)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (p : Rd d × Rd d) :
    (configScaledMetric (D g) (sNorm_pos ξ Q g hr z) hr z).1 p =
      scaledField ξ D (fun t => t ^ (ξ * Q)) r z g p := by
  rw [scaledField_sharp_apply]
  rfl

theorem config_internalC_lower_of_ambient
    (D : ContMetric d) (hD : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (u v : U) :
    D.1 (u.1, v.1) ≤ internalC D hD hU hUc (u, v) := by
  have hfin := D.internal_ne_top_of_isPreconnected hD hU hUc u.2 v.2
  have h := ENNReal.toReal_mono hfin (D.ofReal_le_internal U u.1 v.1)
  change D.1 (u.1, v.1) ≤ (D.internal U u.1 v.1).toReal
  simpa only [ENNReal.toReal_ofReal (D.nonneg u.1 v.1)] using h

/-- S4a's uniform off-diagonal estimate transfers directly to the real
internal coordinate, since internal distance dominates ambient distance. -/
theorem IsWeakExpMetric.configScaledLowerOffDiag
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {L : Set U} (hL : IsCompact L) {η : ℝ} (hη : 0 < η)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
            ∀ u ∈ L, ∀ v ∈ L, η ≤ dist u.1 v.1 →
              a < internalC
                (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
                (configScaledMetric_isLength (D (h ω)) hl
                  (sNorm_pos ξ Q (h ω) hr z) hr z)
                hU hUc (u, v)} < ε := by
  let K := configOffDiagSet L η
  obtain ⟨a, ha, htail⟩ := (show IsWeakExpMetric d ξ D
      (fun r => r ^ (ξ * Q)) from hD).scaledLowerOffDiag hd
    (configOffDiagSet_isCompact hL η)
    (configOffDiagSet_ne hη) hε
  refine ⟨a, ha, ?_⟩
  intro Ω _ P _ h hh r hr z
  have hbad := htail P h hh r hr z
  refine lt_of_le_of_lt (measure_mono ?_) hbad
  intro ω hω hgood
  apply hω
  intro hl u hu v hv huv
  have hp : (u.1, v.1) ∈ K := by
    exact ⟨⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, huv⟩
  have hlow := hgood (u.1, v.1) hp
  rw [← configScaledMetric_apply_sharp ξ Q D (h ω) hr z] at hlow
  exact lt_of_lt_of_le hlow
    (config_internalC_lower_of_ambient _
      (configScaledMetric_isLength (D (h ω)) hl
        (sNorm_pos ξ Q (h ω) hr z) hr z)
      hU hUc u v)

/-- A uniform collar converts S4a's ambient near-diagonal modulus into a
modulus for the internal metric on a compact set. -/
theorem IsWeakExpMetric.configScaledInternalModulus
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d)
    {U O K : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hO : IsOpen O) (hOcl : IsCompact (closure O))
    (hK : IsCompact K) (hKO : K ⊆ O) (hOU : O ⊆ U)
    {θ : ℝ} (hθ : 0 < θ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
            ∀ p q : U × U, p.1.1 ∈ K → p.2.1 ∈ K →
              q.1.1 ∈ K → q.2.1 ∈ K → dist p q ≤ η →
              dist
                (internalC
                  (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
                  (configScaledMetric_isLength (D (h ω)) hl
                    (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc p)
                (internalC
                  (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
                  (configScaledMetric_isLength (D (h ω)) hl
                    (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc q) ≤ θ} < ε := by
  have hfront : IsCompact (frontier O) :=
    hOcl.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hdiag : ∀ p ∈ K ×ˢ frontier O, p.1 ≠ p.2 := by
    intro p hp heq
    have hpO : p.2 ∈ O := heq ▸ hKO hp.1
    exact (hO.frontier_eq ▸ hp.2).2 hpO
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨a, ha, Hsep⟩ := (show IsWeakExpMetric d ξ D
      (fun r => r ^ (ξ * Q)) from hD).scaledLowerOffDiag hd
    (hK.prod hfront) hdiag hε2
  let t : ℝ := min (a / 2) (θ / 2)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have hta : t < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htθ : 2 * t ≤ θ := by dsimp [t]; linarith [min_le_right (a / 2) (θ / 2)]
  obtain ⟨η, hη, Hmod⟩ := (show IsWeakExpMetric d ξ D
      (fun r => r ^ (ξ * Q)) from hD).scaledModulus hd hK ht hε2
  refine ⟨η, hη, ?_⟩
  intro Ω _ P _ h hh r hr z
  have hbad : P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
      ∀ p q : U × U, p.1.1 ∈ K → p.2.1 ∈ K →
        q.1.1 ∈ K → q.2.1 ∈ K → dist p q ≤ η →
        dist
          (internalC
            (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
            (configScaledMetric_isLength (D (h ω)) hl
              (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc p)
          (internalC
            (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
            (configScaledMetric_isLength (D (h ω)) hl
              (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc q) ≤ θ} ≤
      P ({ω | ¬ ∀ s ∈ K ×ˢ frontier O,
        a < scaledField ξ D (fun r => r ^ (ξ * Q)) r z (h ω) s} ∪
        {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ η →
          scaledField ξ D (fun r => r ^ (ξ * Q)) r z (h ω) (u, v) < t}) := by
    refine measure_mono_ae ?_
    filter_upwards [hD.length P h hh.isLGFPlusCont] with ω hl hω
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
    apply hω
    intro hl' p q hp₁ hp₂ hq₁ hq₂ hpq
    let M := configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z
    have hsep : ∀ u ∈ K, ∀ v ∈ frontier O, a ≤ M.1 (u, v) := by
      intro u hu v hv
      exact le_of_lt (configScaledMetric_apply_sharp ξ Q D (h ω) hr z (u,v) ▸
        hnot.1 (u,v) ⟨hu,hv⟩)
    have hsmall : ∀ u ∈ K, ∀ v ∈ K, dist u v ≤ η → M.1 (u,v) ≤ t := by
      intro u hu v hv huv
      exact le_of_lt (configScaledMetric_apply_sharp ξ Q D (h ω) hr z (u,v) ▸
        hnot.2 u hu v hv (by simpa only [dist_eq_norm] using huv))
    have hnear : dist p.1.1 q.1.1 ≤ η ∧ dist p.2.1 q.2.1 ≤ η := by
      rw [Prod.dist_eq] at hpq
      constructor
      · exact (le_max_left _ _).trans hpq
      · exact (le_max_right _ _).trans hpq
    exact (config_internalC_upper_modulus_of_collar M
      (configScaledMetric_isLength (D (h ω)) hl'
        (sNorm_pos ξ Q (h ω) hr z) hr z)
      hU hUc hO hKO hOU ha hta hsep hsmall p q hp₁ hp₂ hq₁ hq₂ hnear).trans htθ
  calc
    P _ ≤ P _ := hbad
    _ ≤ P {ω | ¬ ∀ s ∈ K ×ˢ frontier O,
        a < scaledField ξ D (fun r => r ^ (ξ * Q)) r z (h ω) s} +
        P {ω | ¬ ∀ u ∈ K, ∀ v ∈ K, ‖u - v‖ ≤ η →
          scaledField ξ D (fun r => r ^ (ξ * Q)) r z (h ω) (u, v) < t} :=
      measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add (Hsep P h hh r hr z) (Hmod P h hh r hr z)
    _ = ε := ENNReal.add_halves ε

/-- The E5 normalizer is the diameter of the scaled metric on the unit-scale
sets, for arbitrary open region and compact set. -/
theorem configScaledMetric_diamIn_eq_normDiam
    (ξ Q : ℝ) (D : DistRd d → ContMetric d) (g : DistRd d)
    (U K : Set (Rd d)) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    diamIn (configScaledMetric (D g) (sNorm_pos ξ Q g hr z) hr z) U K =
      normDiam ξ Q D g U K r z := by
  unfold configScaledMetric
  rw [diamIn_smul, diamIn_affine hr.ne' z]
  unfold normDiam affineSet
  have himage (S : Set (Rd d)) :
      (fun u => r • u + z) '' S = (fun u => z + r • u) '' S := by
    congr 1
    funext u
    exact add_comm _ _
  rw [himage U, himage K]
  have he : -(ξ * sphereAvg g r z) = -ξ * sphereAvg g r z := by ring
  rw [he]
  rw [sharpScaledCoeff ξ Q g r z]
  rfl

theorem measurable_diamIn_of_length
    {Ω : Type*} [MeasurableSpace Ω] (F : Ω → ContMetric d)
    (hF : Measurable F) (hLen : ∀ ω, (F ω).IsLength)
    {U K : Set (Rd d)} (hU : IsOpen U) (hKU : K ⊆ U) :
    Measurable (fun ω => diamIn (F ω) U K) := by
  obtain ⟨G, hG, hGeq⟩ := measurable_internal_ambient hU
  let g : K × K → Ω → ℝ≥0∞ := fun p ω => (F ω).internal U p.1.1 p.2.1
  have hm (p : K × K) : Measurable (g p) := by
    have harg : Measurable (fun ω => ((F ω).1, p.1.1, p.2.1)) :=
      (measurable_subtype_coe.comp hF).prodMk
        (measurable_const.prodMk measurable_const)
    convert hG.comp harg using 1
    funext ω
    exact hGeq (F ω) (hLen ω) p.1.1 p.2.1
  have hc (ω : Ω) : Continuous (fun p : K × K => g p ω) := by
    have hpair : Continuous (fun p : K × K =>
        ((p.1 : Rd d), (p.2 : Rd d))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact ((F ω).continuousOn_internal (hLen ω) hU).comp_continuous hpair
      (fun p => ⟨hKU p.1.2, hKU p.2.2⟩)
  have hsup0 := measurable_iSup_of_lowerSemicontinuous hm
    (fun ω => (hc ω).lowerSemicontinuous)
  have hsup : Measurable (fun ω => ⨆ p : K × K, g p ω) := by
    convert hsup0 using 1
    funext ω
    rw [iSup_apply]
  convert hsup using 1
  funext ω
  unfold diamIn
  rw [iSup_prod]
  simp only [iSup_subtype]
  rfl

/-- A countable dense set of endpoint pairs makes internal diameter measurable
up to the almost-sure length-metric event. -/
theorem aemeasurable_diamIn_of_ae_length
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Ω → ContMetric d) (hF : Measurable F)
    (hLen : ∀ᵐ ω ∂P, (F ω).IsLength)
    {U K : Set (Rd d)} (hU : IsOpen U) (hKU : K ⊆ U) :
    AEMeasurable (fun ω => diamIn (F ω) U K) P := by
  obtain ⟨G, hG, hGeq⟩ := measurable_internal_ambient hU
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (K × K)
  let g : K × K → Ω → ℝ≥0∞ := fun p ω => G ((F ω).1, p.1.1, p.2.1)
  have hm (p : K × K) : Measurable (g p) := by
    exact hG.comp ((measurable_subtype_coe.comp hF).prodMk
      (measurable_const.prodMk measurable_const))
  have hcount : Measurable (fun ω => ⨆ p : S, g p.1 ω) := by
    let : Countable S := hSc.to_subtype
    exact Measurable.iSup fun p => hm p.1
  have heq (ω : Ω) (hl : (F ω).IsLength) :
      (⨆ p : S, g p.1 ω) = diamIn (F ω) U K := by
    have hpair : Continuous (fun p : K × K =>
        ((p.1 : Rd d), (p.2 : Rd d))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have hc : Continuous (fun p : K × K =>
        (F ω).internal U p.1.1 p.2.1) :=
      ((F ω).continuousOn_internal hl hU).comp_continuous hpair
        (fun p => ⟨hKU p.1.2, hKU p.2.2⟩)
    have hgs (p : K × K) : g p ω = (F ω).internal U p.1.1 p.2.1 :=
      (hGeq (F ω) hl p.1.1 p.2.1).symm
    simp_rw [hgs]
    rw [hSd.ciSup' hc]
    unfold diamIn
    rw [iSup_prod]
    simp only [iSup_subtype]
  exact hcount.aemeasurable.congr (Filter.Eventually.mono hLen
    (fun ω hl => heq ω hl))

theorem measurable_normDiam_of_length
    {Ω : Type*} [MeasurableSpace Ω] (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (hD : Measurable D)
    (h : Ω → DistRd d) (hh : Measurable h)
    (hLen : ∀ ω, (D (h ω)).IsLength)
    {U K : Set (Rd d)} (hU : IsOpen U) (hKU : K ⊆ U)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    Measurable (fun ω => normDiam ξ Q D (h ω) U K r z) := by
  have hsm : Measurable (fun ω => sNorm ξ Q (h ω) r z) := by
    unfold sNorm
    exact measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_sphereAvg_left r z).comp hh)))
  let F : Ω → ContMetric d := fun ω =>
    configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z
  have hFm : Measurable F := measurable_configScaledMetric_var
    (fun ω => D (h ω)) (hD.comp hh)
    (fun ω => sNorm ξ Q (h ω) r z) hsm
    (fun ω => sNorm_pos ξ Q (h ω) hr z) hr z
  have hFl (ω : Ω) : (F ω).IsLength :=
    configScaledMetric_isLength (D (h ω)) (hLen ω)
      (sNorm_pos ξ Q (h ω) hr z) hr z
  have hm := measurable_diamIn_of_length F hFm hFl hU hKU
  convert hm using 1
  funext ω
  exact (configScaledMetric_diamIn_eq_normDiam ξ Q D (h ω) U K hr z).symm

theorem aemeasurable_normDiam_of_ae_length
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (hD : Measurable D)
    (h : Ω → DistRd d) (hh : Measurable h)
    (hLen : ∀ᵐ ω ∂P, (D (h ω)).IsLength)
    {U K : Set (Rd d)} (hU : IsOpen U) (hKU : K ⊆ U)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    AEMeasurable (fun ω => normDiam ξ Q D (h ω) U K r z) P := by
  have hsm : Measurable (fun ω => sNorm ξ Q (h ω) r z) := by
    unfold sNorm
    exact measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_sphereAvg_left r z).comp hh)))
  let F : Ω → ContMetric d := fun ω =>
    configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z
  have hFm : Measurable F := measurable_configScaledMetric_var
    (fun ω => D (h ω)) (hD.comp hh)
    (fun ω => sNorm ξ Q (h ω) r z) hsm
    (fun ω => sNorm_pos ξ Q (h ω) hr z) hr z
  have hFl : ∀ᵐ ω ∂P, (F ω).IsLength :=
    hLen.mono fun ω hl => configScaledMetric_isLength (D (h ω)) hl
      (sNorm_pos ξ Q (h ω) hr z) hr z
  have hm := aemeasurable_diamIn_of_ae_length P F hFm hFl hU hKU
  convert hm using 1
  funext ω
  exact (configScaledMetric_diamIn_eq_normDiam ξ Q D (h ω) U K hr z).symm

/-- A direct Markov consequence of (E5), with one deterministic threshold for
all LGF realizations, centers, and scales. -/
theorem configE5_diameter_power_tail
    (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (hD : Measurable D) (hE5 : E5SharpMoment d ξ Q D)
    {U K : Set (Rd d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsConnected K) (hKU : K ⊆ U)
    {p : ℝ} (hp : 0 < p)
    (hpmax : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (_hh : IsWholeSpaceLGF h P)
        (_hLen : ∀ᵐ ω ∂P, (D (h ω)).IsLength)
        (r : ℝ) (_hr : 0 < r) (z : Rd d),
        P {ω | (N : ℝ≥0∞) ≤ (normDiam ξ Q D (h ω) U K r z) ^ p} < ε := by
  obtain ⟨M, hM⟩ := hE5 hU hK hKc hKU hp hpmax
  let ε₀ := min ε 1
  have hε₀ : 0 < ε₀ := lt_min hε (by norm_num)
  have hε₀fin : ε₀ ≠ ∞ := by simp [ε₀]
  obtain ⟨N, hN, hbig⟩ := ENNReal.exists_nat_pos_mul_gt
    hε₀.ne' ENNReal.ofReal_ne_top (a := ε₀) (b := ENNReal.ofReal M)
  refine ⟨N, hN, ?_⟩
  intro Ω _ P _ h hh hLen r hr z
  have hm : AEMeasurable (fun ω => (normDiam ξ Q D (h ω) U K r z) ^ p) P :=
    (aemeasurable_normDiam_of_ae_length P ξ Q D hD h hh.measurable hLen hU hKU hr z).pow_const p
  have hmark := meas_ge_le_lintegral_div (μ := P) hm
    (by exact_mod_cast hN.ne') (by simp : (N : ℝ≥0∞) ≠ ∞)
  have hquot : ENNReal.ofReal M / (N : ℝ≥0∞) < ε₀ := by
    apply (ENNReal.div_lt_iff (Or.inl (by exact_mod_cast hN.ne'))
      (Or.inl (by simp : (N : ℝ≥0∞) ≠ ∞))).2
    simpa only [mul_comm] using hbig
  have hdiv : (∫⁻ ω, normDiam ξ Q D (h ω) U K r z ^ p ∂P) /
      (N : ℝ≥0∞) ≤ ENNReal.ofReal M / (N : ℝ≥0∞) := by
    gcongr
    exact hM P h hh r hr z
  exact (hmark.trans_lt (hdiv.trans_lt hquot)).trans_le (min_le_left _ _)

/-- The moment estimate also yields an ordinary uniform upper tail for the
normalized internal diameter. -/
theorem configE5_diameter_tail
    (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (hD : Measurable D) (hE5 : E5SharpMoment d ξ Q D)
    {U K : Set (Rd d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKc : IsConnected K) (hKU : K ⊆ U)
    {p : ℝ} (hp : 0 < p)
    (hpmax : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (_hh : IsWholeSpaceLGF h P)
        (_hLen : ∀ᵐ ω ∂P, (D (h ω)).IsLength)
        (r : ℝ) (_hr : 0 < r) (z : Rd d),
        P {ω | ENNReal.ofReal A ≤ normDiam ξ Q D (h ω) U K r z} < ε := by
  obtain ⟨N, hN, htail⟩ := configE5_diameter_power_tail ξ Q D hD hE5
    hU hK hKc hKU hp hpmax hε
  have hT : Tendsto (fun x : ℝ => x ^ p) atTop atTop := tendsto_rpow_atTop hp
  obtain ⟨A, hA, hApow⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and
      (hT.eventually (eventually_gt_atTop (N : ℝ)))).exists
  have hpow : (N : ℝ≥0∞) < (ENNReal.ofReal A) ^ p := by
    rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_pos hA]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < A ^ p)).2 hApow
  refine ⟨A, hA, ?_⟩
  intro Ω _ P _ h hh hLen r hr z
  exact (measure_mono (fun ω hω =>
    hpow.le.trans (ENNReal.rpow_le_rpow hω hp.le))) |>.trans_lt
      (htail P h hh hLen r hr z)

/-- (E5) controls the two-endpoint internal coordinate on every compact
subset of either configuration annulus. -/
theorem configE5_internal_upper_on_compact
    (hd : 2 ≤ d) (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (hD : IsSharpWeakExpMetric d ξ Q D) (hE5 : E5SharpMoment d ξ Q D)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hshape : U = ann 0 a b)
    {L : Set U} (hL : IsCompact L)
    {p : ℝ} (hp : 0 < p)
    (hpmax : p < (Q + Real.sqrt (Q ^ 2 - 2 * d)) / ξ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d)
        (_hh : IsWholeSpaceLGF h P)
        (r : ℝ) (hr : 0 < r) (z : Rd d),
        P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
          ∀ u ∈ L, ∀ v ∈ L,
            internalC
              (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
              (configScaledMetric_isLength (D (h ω)) hl
                (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc (u,v) < A} < ε := by
  let L₀ : Set (Rd d) := Subtype.val '' L
  have hL₀ : IsCompact L₀ := hL.image continuous_subtype_val
  have hL₀U : L₀ ⊆ U := by rintro x ⟨u, _, rfl⟩; exact u.2
  obtain ⟨K, hK, hKc, hL₀K, hKU⟩ :=
    config_exists_connected_compact_superset hd ha hab hL₀ (hshape ▸ hL₀U)
  have hKU' : K ⊆ U := hshape ▸ hKU
  obtain ⟨A, hA, htail⟩ := configE5_diameter_tail ξ Q D hD.measurable hE5
    hU hK hKc hKU' hp hpmax hε
  refine ⟨A, hA, ?_⟩
  intro Ω _ P _ h hh r hr z
  have hbad : P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
        ∀ u ∈ L, ∀ v ∈ L,
          internalC
            (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
            (configScaledMetric_isLength (D (h ω)) hl
              (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc (u,v) < A} ≤
      P {ω | ENNReal.ofReal A ≤ normDiam ξ Q D (h ω) U K r z} := by
    refine measure_mono_ae ?_
    filter_upwards [hD.length P h hh.isLGFPlusCont] with ω hl hω
    by_contra hgood
    apply hω
    intro hl' u hu v hv
    let M := configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z
    have hdiam : M.internal U u.1 v.1 ≤ diamIn M U K := by
      unfold diamIn
      exact le_iSup_of_le u.1 (le_iSup_of_le (hL₀K ⟨u,hu,rfl⟩)
        (le_iSup_of_le v.1 (le_iSup_of_le (hL₀K ⟨v,hv,rfl⟩) le_rfl)))
    have hlt : M.internal U u.1 v.1 < ENNReal.ofReal A := by
      rw [configScaledMetric_diamIn_eq_normDiam ξ Q D (h ω) U K hr z] at hdiam
      exact lt_of_le_of_lt hdiam (lt_of_not_ge hgood)
    have hfin : M.internal U u.1 v.1 ≠ ∞ :=
      M.internal_ne_top_of_isPreconnected
        (configScaledMetric_isLength (D (h ω)) hl'
          (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc u.2 v.2
    change (M.internal U u.1 v.1).toReal < A
    have ht := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).2 hlt
    simpa [ENNReal.toReal_ofReal hA.le] using ht
  exact hbad.trans_lt (htail P h hh
    (hD.length P h hh.isLGFPlusCont) r hr z)

/-- The compact collar can be selected around any exhaustion set. -/
theorem IsWeakExpMetric.configScaledInternalModulusOnCompact
    {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hd : 2 ≤ d)
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    {L : Set U} (hL : IsCompact L)
    {θ : ℝ} (hθ : 0 < θ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ (r : ℝ) (hr : 0 < r) (z : Rd d),
          P {ω | ¬ ∀ hl : (D (h ω)).IsLength,
            ∀ p q : U × U,
              p.1 ∈ L → p.2 ∈ L → q.1 ∈ L → q.2 ∈ L → dist p q ≤ η →
              dist
                (internalC
                  (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
                  (configScaledMetric_isLength (D (h ω)) hl
                    (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc p)
                (internalC
                  (configScaledMetric (D (h ω)) (sNorm_pos ξ Q (h ω) hr z) hr z)
                  (configScaledMetric_isLength (D (h ω)) hl
                    (sNorm_pos ξ Q (h ω) hr z) hr z) hU hUc q) ≤ θ} < ε := by
  let K : Set (Rd d) := Subtype.val '' L
  have hK : IsCompact K := hL.image continuous_subtype_val
  have hKU : K ⊆ U := by rintro x ⟨u, _, rfl⟩; exact u.2
  obtain ⟨O, hO, hKO, hOUcl, hOcl⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  have hOU : O ⊆ U := (subset_closure).trans hOUcl
  obtain ⟨η, hη, htail⟩ := IsWeakExpMetric.configScaledInternalModulus hD hd hU hUc
    hO hOcl hK hKO hOU hθ hε
  refine ⟨η, hη, ?_⟩
  intro Ω _ P _ h hh r hr z
  refine lt_of_le_of_lt (measure_mono ?_) (htail P h hh r hr z)
  intro ω hω hgood
  apply hω
  intro hl p q hp₁ hp₂ hq₁ hq₂ hpq
  exact hgood hl p q ⟨p.1,hp₁,rfl⟩ ⟨p.2,hp₂,rfl⟩
    ⟨q.1,hq₁,rfl⟩ ⟨q.2,hq₂,rfl⟩ hpq

end HigherDimLQGMetric
