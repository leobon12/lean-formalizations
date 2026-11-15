/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetZoneHist
import InteractingSLE.Spec.Supplement.RetChartClear
import InteractingSLE.Spec.Supplement.WalkStageLocalAE
import InteractingSLE.Spec.Sec7.Lemma76FMark
import InteractingSLE.Spec.Sec7.Lemma76FStop
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Restart.ChartMeasRandom
import InteractingSLE.Spec.Restart.RetPlumbProofFilled
import InteractingSLE.Spec.Coupling.WholeField8Trace
import InteractingSLE.Spec.Coupling.WholeField9Entr

/-!
# Aux. lemma 82: the union mean at cleared prime ends (`RLC.RetCollarMeanStatement`)

Packet PROVE-T15-RET6. Specification supplement, Aux. lemma 82 (pp. 296–297), for the two retained flow-line prefixes
of Theorem 1.5's retained pair: along every approach within the active domain on which the first path's individual
chart `physF W₁ u x₁` tends to a real point whose chart ball misses the chart image of the transition hull
`fill(α[0,u] ∪ β[0,r]) ∖ fill(α[0,u])` (the prime-end clearance (OM2) of Aux. lemma 83), the union mean minus the
first range's mean tends to `0`; symmetrically for the second path.

**Proof.** Proposition 3.8 in the individual chart (`RetZone.ae_tendsto_zero_of_history`) for the nested
history-marked local sets `A₂ = α[0,u] ∩ ℍ ⊆ A = (α[0,u] ∪ β[0,r]) ∩ ℍ`:
* the marks are the killed histories of good capped versions (`Restart.exists_capped_version`, the retained range
  entrance property `WholeField.retainedRangeEntranceStatement`, `Sec7.Lemma76F.isHistoryAvoidanceLocal_cstUnion`; the
  single range is the stopped union of the first path with itself), transferred to the given versions
  (`Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae`);
* the chart is the mapping-out function of the filled first range, measurable in its history (dyadic hits,
  `Restart.measurable_indicator_mapOut`); on the ordinary event it is `physF W₁ u x₁ + κ` (uniqueness of mapping-out
  functions, `ReverseArc.exists_physChart`);
* the cleared ball of the statement is a cleared chart ball, the active domain lies in the complement of the filled
  first range, and the harmonic representatives agree with the one of the theorem (`Sec6.eqOn_of_integral_mul_eq`).

Main results: **`ae_tendsto_sub_of_side`** (one path) and **`retCollarMeanStatement : RetCollarMeanStatement`**.
For Theorem 1.5; uses Lemma 7.5 (field determination) only (R43/R48: no Theorem 1.2/1.3 input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

namespace RetZone

open Sec7 Sec7.Lemma76F Sec7.Lemma76G Restart LocalSets

/-! ### Deterministic facts -/

/-- The active domain of two closed prefixes lies in the complement of the filled first prefix. -/
theorem activeDomain_subset_H_diff_fillH {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} (hK : IsClosed (prefixSet α a β b)) :
    activeDomain α a β b ⊆ H \ fillH (α '' Icc 0 a) := by
  rw [activeDomain_eq hK]
  exact fun z hz => ⟨hz.1, fun h => hz.2 (fillH_mono subset_union_left h)⟩

/-- A capped version agrees with the path before a cutoff strictly inside the lifetime and the cap. -/
theorem eqOn_of_capped {η ηc : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {m s : ℝ≥0} (hag : ∀ t, ηc t = η (capTime m ζ t))
    (hs : (s : ℝ≥0∞) < ζ) (hsm : s < m) : ∀ t ≤ s, ηc t = η t := fun t ht => by
  rw [hag t, capTime_eq_of_lt hs hsm ht]


/-- The stopped union of two continuous paths is relatively closed in `ℍ`. -/
theorem cstUnion_relClosed {Ω : Type*} {ηa ηb : Ω → ℝ≥0 → ℂ} (ha : ∀ ω, Continuous (ηa ω))
    (hb : ∀ ω, Continuous (ηb ω)) (s s' : ℝ≥0) (ω : Ω) :
    cstUnion ηa ηb s s' ω ⊆ H ∧ IsOpen (H \ cstUnion ηa ηb s s' ω) := by
  refine ⟨fun z hz => by rw [cstUnion_eq] at hz; exact hz.2, ?_⟩
  have hK : IsCompact (ηa ω '' Icc 0 s ∪ ηb ω '' Icc 0 s') :=
    (isCompact_Icc.image (ha ω)).union (isCompact_Icc.image (hb ω))
  have e : H \ cstUnion ηa ηb s s' ω = H \ (ηa ω '' Icc 0 s ∪ ηb ω '' Icc 0 s') := by
    rw [cstUnion_eq]
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, not_and]
    exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hu => hn hu hz⟩, fun ⟨hz, hn⟩ => ⟨hz, fun hu _ => hn hu⟩⟩
  rw [e]
  exact QuantumZipper.isOpen_H.sdiff hK.isClosed

/-! ### One side -/

/-- The history marks of a stopped pair: the σ-algebra of the two killed histories. -/
@[instance_reducible]
def sideMark {Ω : Type*} (ηa ηb : Ω → ℝ≥0 → ℂ) (ζa ζb : Ω → ℝ≥0∞) (s s' : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (cstHist ηa ηb ζa ζb s s') inferInstance

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x x' θ θ' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η η' : Ω → ℝ≥0 → ℂ}
  {ζ ζ' : Ω → ℝ≥0∞}

/-- **Aux. lemma 82 for one path** (the first path `η` of a retained pair with the other path `η'`, cutoffs `s`, `s'`
below a common cap `m`): almost surely on `{s < ζ, s' < ζ'}`, for all harmonic representatives `v` of the union mean
and `vA` of the first range's mean, `v − vA → 0` along every approach within the active domain on which the first
path's individual chart tends to a real point whose ball misses the chart image of the transition hull. -/
theorem ae_tendsto_sub_of_side (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη : IsFlowLine κ b jumps x θ P h η ζ) (hη' : IsFlowLine κ b jumps x' θ' P h η' ζ')
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {s s' m : ℝ≥0} (hsm : s < m) (hs'm : s' < m)
    {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x) ∧
      ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0)
    {ηc ηc' : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (ηc ω)) (hc' : ∀ ω, Continuous (ηc' ω))
    (hm : ∀ t, Measurable fun ω => ηc ω t) (hm' : ∀ t, Measurable fun ω => ηc' ω t)
    (hag : ∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (capTime m (ζ ω) t))
    (hag' : ∀ᵐ ω ∂P, ∀ t, ηc' ω t = η' ω (capTime m (ζ' ω) t))
    {g G : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (cstUnion ηc ηc' s s') (WholeField.centredField h u₀) P g)
    (hG : IsLocalSetMean (fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s} ∩ H) (WholeField.centredField h u₀) P G) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ ω → (s' : ℝ≥0∞) < ζ' ω → ∀ v vA : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ cstUnion ηc ηc' s s' ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηc ηc' s s' ω → g ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vA (H \ (ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s} ∩ H) →
        G ω φ = ∫ z, vA z * φ z) →
      ∀ y ρ : ℝ, 0 < ρ → Disjoint (ball (y : ℂ) ρ) (physF (fun t => W t ω) s x ''
          (fillH (prefixSet (η ω) s (η' ω) s') \ fillH (η ω '' Icc 0 s))) →
        ∀ F : Filter ℂ, F ≤ 𝓟 (activeDomain (η ω) s (η' ω) s') →
          Tendsto (physF (fun t => W t ω) s x) F (𝓝 (y : ℂ)) → Tendsto (fun z => v z - vA z) F (𝓝 0) := by
  classical
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hhm := hh0.measurable
  -- good capped versions, their killed histories and their marked locality
  obtain ⟨ηg, hcg, hmg, h0g, -, hagg, hdetg, hdetζg⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη u₀ m
  obtain ⟨ηg', hcg', hmg', h0g', -, hagg', hdetg', hdetζg'⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη' u₀ m
  have hloc := WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x θ P h hh η ζ hη u₀ hu₀ m ηg hcg
    hmg hagg
  have hloc' := WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x' θ' P h hh η' ζ' hη' u₀ hu₀ m ηg'
    hcg' hmg' hagg'
  have hζlm : Measurable fun ω => cutLife (ζ ω) m := (measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη)
  have hζlm' : Measurable fun ω => cutLife (ζ' ω) m :=
    (measurable_cutLife _).comp (measurable_lifetime_of_isFlowLine hη')
  have hlocA' := isHistoryAvoidanceLocal_cstUnion (u := s) (r := s') hhm hcg hcg' h0g h0g' hmg hmg' hζlm hζlm'
    hdetg hdetg' hdetζg hdetζg' hloc hloc'
  have hlocA₂' := isHistoryAvoidanceLocal_cstUnion (u := s) (r := s) hhm hcg hcg h0g h0g hmg hmg hζlm hζlm
    hdetg hdetg hdetζg hdetζg hloc hloc
  -- the two sets and their almost sure agreement with the good versions
  set A : Ω → Set ℂ := cstUnion ηc ηc' s s' with hAdef
  set A₂ : Ω → Set ℂ := fun ω => ηc ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s} ∩ H with hA₂def
  have hIcc : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s} = Icc 0 s := by
    ext t; simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and, ENNReal.coe_le_coe]
  have hA₂eq : A₂ = cstUnion ηc ηc s s := by
    funext ω; rw [cstUnion_eq, union_self, hA₂def, hIcc]
  have hAm : Measurable[mΩ, hittingSigma] A := measurable_cstUnion hc hc' hm hm' s s'
  have hA₂m : Measurable[mΩ, hittingSigma] A₂ := hA₂eq ▸ measurable_cstUnion hc hc hm hm s s
  have hvers : ∀ᵐ ω ∂P, ∀ t, ηc ω t = ηg ω t := by
    filter_upwards [hag, hagg] with ω h1 h2 t; rw [h1, h2]
  have hvers' : ∀ᵐ ω ∂P, ∀ t, ηc' ω t = ηg' ω t := by
    filter_upwards [hag', hagg'] with ω h1 h2 t; rw [h1, h2]
  have hAae : ∀ᵐ ω ∂P, cstUnion ηg ηg' s s' ω = A ω := by
    filter_upwards [hvers, hvers'] with ω h1 h2
    have e1 : ηg ω = ηc ω := funext fun t => (h1 t).symm
    have e2 : ηg' ω = ηc' ω := funext fun t => (h2 t).symm
    simp only [hAdef, cstUnion_eq, e1, e2]
  have hA₂ae : ∀ᵐ ω ∂P, cstUnion ηg ηg s s ω = A₂ ω := by
    filter_upwards [hvers] with ω h1
    have e1 : ηg ω = ηc ω := funext fun t => (h1 t).symm
    rw [hA₂eq]; simp only [cstUnion_eq, e1]
  have hlocA := Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae hAae hlocA'
  have hlocA₂ := Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae hA₂ae hlocA₂'
  -- the marks
  have hℋ : sideMark ηg ηg' (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ' ω) m) s s' ≤ mΩ :=
    (measurable_cstHist hmg hmg' hζlm hζlm' s s').comap_le
  have hℋ₁ : sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s ≤
      sideMark ηg ηg' (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ' ω) m) s s' := by
    have e : cstHist ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s =
        (fun p => (p.1, p.1)) ∘ cstHist ηg ηg' (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ' ω) m) s s' := rfl
    unfold sideMark
    rw [e, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_fst.prodMk measurable_fst).comap_le
  -- the first path before `s` is recorded by its history
  have hrec : ∀ t ≤ s, Measurable[sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s]
      fun ω => ηg ω t := by
    intro t ht
    have e : (fun ω => ηg ω t) = fun ω => Restart.recon
        (cstHist ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s ω).1.1 t := by
      funext ω
      exact (Restart.recon_histOf (T' := ⊤) (by simpa using hcg ω) le_top
        (ENNReal.coe_le_coe.2 ht)).symm
    rw [e]
    exact (Restart.measurable_recon t).comp (measurable_fst.comp (measurable_fst.comp (comap_measurable _)))
  -- the single range is recorded by the history of the first path
  have hA₂ℋ : MeasurableSpace.comap A₂ hittingSigma ≤ aeSigma (MeasurableSpace.comap A hittingSigma ⊔
      sideMark ηg ηg' (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ' ω) m) s s') P := by
    set ηs : Ω → ℝ≥0 → ℂ := fun ω t => ηg ω (min t s) with hηs
    have hcs : ∀ ω, Continuous (ηs ω) := fun ω => (hcg ω).comp (continuous_id.min continuous_const)
    have hms : ∀ t, Measurable[sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s]
        fun ω => ηs ω t := fun t => hrec (min t s) (min_le_right _ _)
    have hBm := @measurable_cstUnion Ω
      (sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s) ηs ηs hcs hcs hms hms s s
    have hBeq : ∀ ω, cstUnion ηs ηs s s ω = cstUnion ηg ηg s s ω := fun ω => by
      have e : ηs ω '' Icc 0 s = ηg ω '' Icc 0 s :=
        image_congr fun t ht => by simp only [hηs, min_eq_left ht.2]
      rw [cstUnion_eq, cstUnion_eq, e]
    have hae : A₂ =ᵐ[P] cstUnion ηs ηs s s := by
      filter_upwards [hA₂ae] with ω hω
      rw [hBeq, hω]
    have h1 := (@WholeField.measurable_aeSigma_of_ae_eq' Ω mΩ P (Set ℂ) hittingSigma _ A₂ _ hBm hae).comap_le
    exact h1.trans (Sec7.FlatClockProof.aeSigma_mono (hℋ₁.trans le_sup_right))
  have hA₂A : ∀ ω, A₂ ω ⊆ A ω := fun ω => by
    rw [hA₂eq, hAdef, cstUnion_eq, cstUnion_eq]
    exact inter_subset_inter_left _ (union_subset subset_union_left subset_union_left)
  have hclosed : ∀ᵐ ω ∂P, (A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧ (A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧ A₂ ω ⊆ A ω := by
    refine Eventually.of_forall fun ω => ⟨cstUnion_relClosed hc hc' s s' ω, ?_, hA₂A ω⟩
    rw [hA₂eq]; exact cstUnion_relClosed hc hc s s ω
  -- the chart: the mapping-out function of the filled first range
  have hKc : ∀ ω, IsCompact (ηg ω '' Icc 0 s) := fun ω => isCompact_Icc.image (hcg ω)
  have hKp : ∀ ω, IsPreconnected (ηg ω '' Icc 0 s ∪ Restart.lowerHalf) := fun ω =>
    (isPreconnected_Icc.image _ (hcg ω).continuousOn).union (ηg ω 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩
      (by show (ηg ω 0).im ≤ 0; rw [h0g ω]; simp) InteractingSLE.isPreconnected_lowerHalf
  have hHull : ∀ ω, IsHPHull (fillH (ηg ω '' Icc 0 s)) := fun ω =>
    isHPHull_fillH_of_isPreconnected (hKc ω).isBounded (hKp ω)
  have hKdy := @Restart.RetAux79.isDyadicHitMeasurable_prefix Ω
    (sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s) ηg s hcg hrec
  have hchart : ∀ᵐ ω ∂P, IsChartSetting (H \ fillH (ηg ω '' Icc 0 s)) (H \ A₂ ω)
      (ConformalImage.mapOut (fillH (ηg ω '' Icc 0 s))) ∧ ∃ M : ℝ, ∀ z ∈ H \ fillH (ηg ω '' Icc 0 s),
        ‖ConformalImage.mapOut (fillH (ηg ω '' Icc 0 s)) z - z‖ ≤ M := by
    filter_upwards [hA₂ae] with ω hω
    have hO : H \ A₂ ω = H \ ηg ω '' Icc 0 s := by
      rw [← hω, cstUnion_eq, union_self]
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, not_and]
      exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hu => hn hu hz⟩, fun ⟨hz, hn⟩ => ⟨hz, fun hu _ => hn hu⟩⟩
    have hMO := ConformalImage.isMapOut_mapOut (hHull ω)
    rw [hO]
    exact ⟨{ isOpen_D := isOpen_H_diff_fillH (hKc ω).isBounded
             isOpen_O := QuantumZipper.isOpen_H.sdiff (hKc ω).isClosed
             subset_O := HalfPlaneSep.H_diff_fillH_subset_H_diff (hKc ω).isClosed
             O_subset := sdiff_subset
             comp := fun z hz => HalfPlaneSep.connectedComponentIn_subset_H_diff_fillH (hKc ω).isClosed hz
             conf := hMO.1 }, IsMapOut.exists_norm_sub_le (hHull ω) hMO⟩
  have key := ae_tendsto_zero_of_history
    (ℋ := sideMark ηg ηg' (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ' ω) m) s s')
    (ℋ₁ := sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s)
    (D := fun ω => H \ fillH (ηg ω '' Icc 0 s)) (G := fun ω => ConformalImage.mapOut (fillH (ηg ω '' Icc 0 s)))
    hh0 hAm hA₂m hℋ hℋ₁ hlocA hlocA₂ hA₂ℋ hclosed hg hG hchart
    (fun q => @Restart.measurableSet_mem_H_diff_fillH Ω
      (sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s) _ hKdy hKc q)
    (fun q => @Restart.measurable_indicator_mapOut Ω
      (sideMark ηg ηg (fun ω => cutLife (ζ ω) m) (fun ω => cutLife (ζ ω) m) s s) _ hKdy hKc hKp q)
  filter_upwards [key, hW, hag, hag', hvers] with ω ⟨uh, huh, hur, hdec⟩ ⟨hgt, hWc, hW0⟩ hagω hagω' hversω
  intro hs hs' v vA hv hvr hvA hvAr y ρ hρ hdisj F hF hT
  have e₁ : ∀ t ≤ s, ηc ω t = η ω t := eqOn_of_capped hagω hs hsm
  have e₁' : ∀ t ≤ s', ηc' ω t = η' ω t := eqOn_of_capped hagω' hs' hs'm
  have hηimg : ηc ω '' Icc 0 s = η ω '' Icc 0 s := image_congr fun t ht => e₁ t ht.2
  have hη'img : ηc' ω '' Icc 0 s' = η' ω '' Icc 0 s' := image_congr fun t ht => e₁' t ht.2
  have hKη : ηg ω '' Icc 0 s = η ω '' Icc 0 s := image_congr fun t ht => by rw [← hversω t, e₁ t ht.2]
  have hAω : A ω = (η ω '' Icc 0 s ∪ η' ω '' Icc 0 s') ∩ H := by rw [hAdef, cstUnion_eq, hηimg, hη'img]
  -- the physical chart is the mapping-out function up to a real constant
  obtain ⟨κc, -, hMOp, -⟩ := ReverseArc.exists_physChart hgt hWc hW0 hs
  have hHullη : IsHPHull (fillH (η ω '' Icc 0 s)) := hKη ▸ hHull ω
  have hGeq : ∀ z ∈ H \ fillH (ηg ω '' Icc 0 s),
      ConformalImage.mapOut (fillH (ηg ω '' Icc 0 s)) z = physF (fun t => W t ω) s x z + κc := by
    intro z hz
    rw [hKη] at hz ⊢
    exact IsMapOut.eqOn hHullη (ConformalImage.isMapOut_mapOut hHullη) hMOp hz
  -- the active domain lies in the chart domain and off the union
  have hKcl : IsClosed (prefixSet (η ω) s (η' ω) s') := by
    rw [prefixSet, ← hηimg, ← hη'img]
    exact ((isCompact_Icc.image (hc ω)).union (isCompact_Icc.image (hc' ω))).isClosed
  have hADsub : activeDomain (η ω) s (η' ω) s' ⊆ H \ fillH (ηg ω '' Icc 0 s) := by
    rw [hKη]; exact activeDomain_subset_H_diff_fillH hKcl
  have hFD : F ≤ 𝓟 (H \ fillH (ηg ω '' Icc 0 s)) := hF.trans (principal_mono.2 hADsub)
  have hTG : Tendsto (ConformalImage.mapOut (fillH (ηg ω '' Icc 0 s))) F (𝓝 (((y + κc : ℝ)) : ℂ)) := by
    have h1 : Tendsto (fun z => physF (fun t => W t ω) s x z + κc) F (𝓝 ((y : ℂ) + κc)) := hT.add_const _
    rw [ofReal_add]
    exact h1.congr' (Filter.eventually_of_mem (le_principal_iff.1 hFD) fun z hz => (hGeq z hz).symm)
  -- the cleared ball is a cleared chart ball
  have hclr : ∀ z ∈ H \ fillH (ηg ω '' Icc 0 s),
      ConformalImage.mapOut (fillH (ηg ω '' Icc 0 s)) z ∈ ball (((y + κc : ℝ)) : ℂ) ρ → z ∉ A ω := by
    intro z hzD hzb hzA
    rw [hAω] at hzA
    have hzfill : z ∈ fillH (prefixSet (η ω) s (η' ω) s') :=
      mem_fillH_of_mem_closure hzA.2 (subset_closure hzA.1)
    have hzD' : z ∉ fillH (η ω '' Icc 0 s) := by rw [← hKη]; exact hzD.2
    have hball : physF (fun t => W t ω) s x z ∈ ball (y : ℂ) ρ := by
      rw [hGeq z hzD, mem_ball, dist_eq_norm] at hzb
      rw [mem_ball, dist_eq_norm]
      have e : physF (fun t => W t ω) s x z + κc - ((y + κc : ℝ) : ℂ) = physF (fun t => W t ω) s x z - y := by
        push_cast; ring
      rwa [e] at hzb
    exact Set.disjoint_left.1 hdisj hball ⟨z, ⟨hzfill, hzD'⟩, rfl⟩
  have hlim := hdec (y + κc) ρ hρ hclr F hFD hTG
  -- the harmonic representatives agree with `uh` off the union
  have hAo : IsOpen (H \ A ω) := (cstUnion_relClosed hc hc' s s' ω).2
  have hsubA : H \ A ω ⊆ H \ A₂ ω := fun z hz => ⟨hz.1, fun h' => hz.2 (hA₂A ω h')⟩
  have hvA' : InnerProductSpace.HarmonicOnNhd vA (H \ A ω) := fun z hz => hvA z (hsubA hz)
  have hcont : ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ A ω) → ContinuousOn w (H \ A ω) :=
    fun w hw z hz => (hw z hz).1.continuousAt.continuousWithinAt
  have heq : EqOn (fun z => v z - vA z) uh (H \ A ω) := by
    refine Sec6.eqOn_of_integral_mul_eq hAo sdiff_subset (hv.sub hvA') huh fun φ hφ => ?_
    have hi1 := LocalSets.integrable_mul_test hAo (hcont v hv) φ hφ
    have hi2 := LocalSets.integrable_mul_test hAo (hcont vA hvA') φ hφ
    have e : (fun z => (v z - vA z) * φ z) = fun z => v z * φ z - vA z * φ z := by funext z; ring
    rw [e, integral_sub hi1 hi2, ← hvr φ hφ, ← hvAr φ (hφ.trans hsubA), hur φ hφ]
  have hFA : ∀ᶠ z in F, z ∈ H \ A ω := by
    refine Filter.eventually_of_mem (le_principal_iff.1 hF) fun z hz => ?_
    refine ⟨hz.1.1, fun hzA => hz.1.2 ?_⟩
    rw [hAω] at hzA
    exact hzA.1
  exact hlim.congr' (hFA.mono fun z hz => (heq hz).symm)

end RetZone

/-! ### The statement and the reduction of leaf 2 -/

open RetZone Sec7.Lemma76F Restart LocalSets in
/-- **Aux. lemma 82 for the retained pair (`RetCollarMeanStatement`)**, from Lemma 7.5. -/
theorem retCollarMeanStatement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u}) : RetCollarMeanStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ _ _ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r u₀ hu₀ W₁ W₂ hW₁ hW₂
    ηc₁ ηc₂ g G₁ G₂ hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg hG₁ hG₂
  have hswap : cstUnion ηc₂ ηc₁ r u = cstUnion ηc₁ ηc₂ u r :=
    funext fun ω => by rw [cstUnion_eq, cstUnion_eq, union_comm]
  have hg' : IsLocalSetMean (cstUnion ηc₂ ηc₁ r u) (WholeField.centredField h u₀) P g := by rw [hswap]; exact hg
  have h1 := ae_tendsto_sub_of_side hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ (lt_capR_left u r) (lt_capR_right u r) hW₁
    hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg hG₁
  have h2 := ae_tendsto_sub_of_side hL75 hκ hκ4 hb hh hη₂ hη₁ hu₀ (lt_capR_right u r) (lt_capR_left u r) hW₂
    hc₂ hc₁ hm₂ hm₁ hag₂ hag₁ hg' hG₂
  filter_upwards [h1, h2] with ω h1 h2 hord _ v vA₁ vA₂ hv hvr hvA₁ hvA₁r hvA₂ hvA₂r
  refine ⟨h1 hord.1 hord.2.1 v vA₁ hv hvr hvA₁ hvA₁r, ?_⟩
  have hpre : prefixSet (η₂ ω) r (η₁ ω) u = prefixSet (η₁ ω) u (η₂ ω) r := union_comm _ _
  have had : activeDomain (η₂ ω) r (η₁ ω) u = activeDomain (η₁ ω) u (η₂ ω) r := by
    simp only [activeDomain, union_comm]
  have hv' : InnerProductSpace.HarmonicOnNhd v (H \ cstUnion ηc₂ ηc₁ r u ω) := by rw [hswap]; exact hv
  have hvr' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηc₂ ηc₁ r u ω →
      g ω φ = ∫ z, v z * φ z := by rw [hswap]; exact hvr
  intro y ρ hρ hdisj F hF hT
  exact h2 hord.2.1 hord.1 v vA₂ hv' hvr' hvA₂ hvA₂r y ρ hρ (by rw [hpre]; exact hdisj) F
    (by rw [had]; exact hF) hT

/-- **Leaf 2 of Theorem 1.5's retained continuation reduced to Aux. lemma 85**: the touching-pair chart boundary values
from Lemma 7.5 and `RetTouchZonesStatement` alone (Aux. lemmas 82 and 83 and the side functions are now proved). -/
theorem retTouchChartBoundaryStatement_of_zones (hL75 : Theorem15.Lemma75Statement.{u})
    (hZ : RetTouchZonesStatement) : RetTouchChartBoundaryStatement.{u} :=
  retTouchChartBoundaryStatement_of_parts hL75 hZ RetChart.retTouchSidesStatement RetChart.retTouchClearStatement
    (retCollarMeanStatement_of_lemma75 hL75)

/-- **The touching mean word from Lemma 7.5 and Aux. lemma 85.** -/
theorem retTouchMeanWordStatement_of_zones (hL75 : Theorem15.Lemma75Statement.{u})
    (hZ : RetTouchZonesStatement) : RetTouchMeanWordStatement.{u} :=
  retTouchMeanWordStatement_of_chartBoundary hL75 (retTouchChartBoundaryStatement_of_zones hL75 hZ)

end RLC

end InteractingSLE
