import HigherDimLQGMetric.Thm13.GoodWeyl
import HigherDimLQGMetric.Determ.LawTransfer
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LQGMetric.Papers.DFGPS.L2_17Core3D

/-! Transfer the almost-sure LFPP subsequence limit through the canonical
normalized LGF law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_ae_tendsto_lfppSeq_transfer
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (G : DistRd d → C(Rd d × Rd d, ℝ)) (hG : Measurable G)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : Ω → DistRd d) (h' : Ω' → DistRd d)
    (hh : IsNormalizedLGF h P) (hh' : IsNormalizedLGF h' P')
    (hae : ∀ᵐ ω ∂P,
      Tendsto (fun n => lfppSeq κ ξ εs (h ω) n) atTop (𝓝 (G (h ω)))) :
    ∀ᵐ ω ∂P',
      Tendsto (fun n => lfppSeq κ ξ εs (h' ω) n) atTop (𝓝 (G (h' ω))) := by
  have hcanon : P.map h = P'.map h' :=
    ((normLGFLaw_spec_holds d hd).2.2 (P.map h) inferInstance hh.map_id).trans
      ((normLGFLaw_spec_holds d hd).2.2 (P'.map h') inferInstance hh'.map_id).symm
  letI : IsProbabilityMeasure (P.map h) :=
    (Measure.isProbabilityMeasure_map_iff hh.1.measurable.aemeasurable).2 inferInstance
  have hXm (n : ℕ) : AEMeasurable
      (fun g : DistRd d => lfppSeq κ ξ εs g n) (P.map h) :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n)
      (P.map h) id hh.map_id.1.isLGFPlusBddCont
  let X : ℕ → DistRd d → C(Rd d × Rd d, ℝ) :=
    fun n => (hXm n).mk _
  have hS : MeasurableSet
      {g : DistRd d | Tendsto (fun n => X n g) atTop (𝓝 (G g))} :=
    measurableSet_tendsto_fun (fun n => (hXm n).measurable_mk) hG
  have hX : ∀ᵐ g ∂(P.map h), ∀ n,
      X n g = lfppSeq κ ξ εs g n :=
    ae_all_iff.2 fun n => (hXm n).ae_eq_mk.symm
  have hPS : ∀ᵐ ω ∂P,
      h ω ∈ {g : DistRd d | Tendsto (fun n => X n g) atTop (𝓝 (G g))} := by
    filter_upwards [hae, ae_of_ae_map hh.1.measurable.aemeasurable hX]
      with ω ht hω
    simpa only [Set.mem_ofPred_eq, hω] using ht
  have hmap := (ae_map_iff hh.1.measurable.aemeasurable hS).2 hPS
  rw [hcanon] at hmap hX
  filter_upwards [ae_of_ae_map hh'.1.measurable.aemeasurable hmap,
    ae_of_ae_map hh'.1.measurable.aemeasurable hX] with ω ht hω
  simpa only [Set.mem_ofPred_eq, hω] using ht

/-- Every normalized LGF has the same almost-sure metric limit as the
fixed-marginal coupling, after identifying that limit with the patch. -/
theorem l8_normalized_good_of_coupling
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (Dh : Ω → ContMetric d) (hh : IsNormalizedLGF h P)
    (hae : ∀ᵐ ω ∂P,
      Tendsto (fun n => lfppSeq κ ξ εs (h ω) n) atTop (𝓝 (Dh ω).1))
    (hW : ∀ᵐ ω ∂P, ∃ hD : (Dh ω).IsLength,
      ∀ f : C(Rd d, ℝ),
        l8_patch hd hκ ξ εs hεs (addFun (h ω) f) =
          weylMetric ξ f (Dh ω) hD) :
    ∀ {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (h' : Ω' → DistRd d),
      IsNormalizedLGF h' P' →
      (∀ᵐ ω ∂P', (l8_patch hd hκ ξ εs hεs (h' ω)).IsLength) ∧
      (∀ᵐ ω ∂P', Tendsto (fun n => lfppSeq κ ξ εs (h' ω) n)
        atTop (𝓝 (l8_patch hd hκ ξ εs hεs (h' ω)).1)) := by
  let D : DistRd d → ContMetric d := l8_patch hd hκ ξ εs hεs
  have hDm : Measurable D := l8_measurable_patch hd hκ ξ εs hεs
  have hsrc : ∀ᵐ ω ∂P, D (h ω) = Dh ω :=
    hW.mono fun ω ⟨hD, hω⟩ => l8_patch_eq_of_weyl_event hd hκ ξ εs hεs
      (h ω) (Dh ω) hD hω
  have hsrcLen : ∀ᵐ ω ∂P, (D (h ω)).IsLength := by
    filter_upwards [hW, hsrc] with ω hω heq
    rw [heq]
    exact hω.choose
  have hsrcConv : ∀ᵐ ω ∂P,
      Tendsto (fun n => lfppSeq κ ξ εs (h ω) n) atTop
        (𝓝 (D (h ω)).1) := by
    filter_upwards [hae, hsrc] with ω ht heq
    simpa only [heq] using ht
  intro Ω' _ P' _ h' hh'
  have hcanon : P.map h = P'.map h' :=
    ((normLGFLaw_spec_holds d hd).2.2 (P.map h) inferInstance hh.map_id).trans
      ((normLGFLaw_spec_holds d hd).2.2 (P'.map h') inferInstance hh'.map_id).symm
  have hDlaw : P.map (D ∘ h) = P'.map (D ∘ h') := by
    rw [← Measure.map_map hDm hh.1.measurable,
      ← Measure.map_map hDm hh'.1.measurable, hcanon]
  have hlen := determ_length_law_transfer P P' (D ∘ h) (D ∘ h')
    (hDm.comp hh.1.measurable) (hDm.comp hh'.1.measurable)
    hDlaw hsrcLen
  have hconv := l8_ae_tendsto_lfppSeq_transfer hd κ hκ ξ εs hεs
    (fun g => (D g).1) (measurable_subtype_coe.comp hDm)
    P P' h h' hh hh' hsrcConv
  exact ⟨hlen, hconv⟩

private noncomputable instance (d : ℕ) :
    PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _

/-- Almost-sure convergence of continuous-map-valued random variables gives
weak convergence of their laws, including when the prelimit maps are only
almost surely measurable. -/
theorem l8_tendsto_law_of_ae
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : Measurable Y)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (β := ProbabilityMeasure C(Rd d × Rd d, ℝ))
      (fun n => (⟨P.map (X n),
      (Measure.isProbabilityMeasure_map_iff (hX n)).2 inferInstance⟩ :
        ProbabilityMeasure C(Rd d × Rd d, ℝ))) atTop
      (𝓝 (⟨P.map Y,
        (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance⟩ :
          ProbabilityMeasure C(Rd d × Rd d, ℝ))) := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable C(Rd d × Rd d, ℝ)
  let X' : ℕ → Ω → C(Rd d × Rd d, ℝ) := fun n => (hX n).mk _
  have hXm (n : ℕ) : Measurable (X' n) := (hX n).measurable_mk
  have hXe : ∀ᵐ ω ∂P, ∀ n, X' n ω = X n ω :=
    ae_all_iff.2 fun n => (hX n).ae_eq_mk.symm
  have hcv : ∀ᵐ ω ∂P, Tendsto (fun n => X' n ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [hae, hXe] with ω ht he
    simpa only [he] using ht
  have hS : MeasurableSet
      {ω : Ω | Tendsto (fun n => X' n ω) atTop (𝓝 (Y ω))} :=
    measurableSet_tendsto_fun hXm hY
  classical
  let Z : ℕ → Ω → C(Rd d × Rd d, ℝ) :=
    fun n ω => if ω ∈ {ω : Ω | Tendsto (fun n => X' n ω) atTop (𝓝 (Y ω))}
      then X' n ω else Y ω
  have hZm (n : ℕ) : Measurable (Z n) := (hXm n).piecewise hS hY
  have hZeq (n : ℕ) : Z n =ᵐ[P] X n := by
    filter_upwards [hcv, hXe] with ω hω he
    simp [Z, hω, he n]
  have hZt (ω : Ω) : Tendsto (fun n => Z n ω) atTop (𝓝 (Y ω)) := by
    by_cases hω : ω ∈ {ω : Ω | Tendsto (fun n => X' n ω) atTop (𝓝 (Y ω))}
    · have hω' : Tendsto (fun n => X' n ω) atTop (𝓝 (Y ω)) := hω
      have hz : (fun n => Z n ω) = (fun n => X' n ω) := by
        funext n
        simp only [Z, hω, ↓reduceIte]
      rw [hz]
      exact hω'
    · have hω' : ¬Tendsto (fun n => X' n ω) atTop (𝓝 (Y ω)) := hω
      have hz : (fun n => Z n ω) = fun _ => Y ω := by
        funext n
        simp only [Z, hω, ↓reduceIte]
      rw [hz]
      exact tendsto_const_nhds
  have ht := LQGMetric.DFGPS.L217.tendsto_map_of_forall_tendsto
    (P := P) hZm hY hZt
  refine ht.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact Subtype.ext (Measure.map_congr (hZeq n))

/-- A subsequential almost-sure LFPP limit has the properness at infinity
supplied by the L6a support statement. -/
theorem l8_ae_proper_of_ae_lfpp_limit
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    {d : ℕ} (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsNormalizedLGF h P)
    (D : DistRd d → ContMetric d) (hD : Measurable D)
    (hae : ∀ᵐ ω ∂P,
      Tendsto (fun n => lfppSeq κ ξ εs (h ω) n) atTop
        (𝓝 (D (h ω)).1)) :
    ∀ᵐ ω ∂P, IsProperFn (D (h ω)).1 := by
  let Y : Ω → C(Rd d × Rd d, ℝ) := fun ω => (D (h ω)).1
  have hYm : Measurable Y := measurable_subtype_coe.comp (hD.comp hh.1.measurable)
  let X : ℕ → Ω → C(Rd d × Rd d, ℝ) :=
    fun n ω => lfppSeq κ ξ εs (h ω) n
  have hXm (n : ℕ) : AEMeasurable (X n) P :=
    l6a_aemeasurable_normalized_lfpp hd κ hκ ξ (hεs n) P h
      hh.1.isLGFPlusBddCont
  let ν : ℕ → ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    fun n => ⟨P.map (X n), (Measure.isProbabilityMeasure_map_iff (hXm n)).2 inferInstance⟩
  let μ : ProbabilityMeasure C(Rd d × Rd d, ℝ) :=
    ⟨P.map Y, (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).2 inferInstance⟩
  have hLaw : Tendsto ν atTop (𝓝 μ) :=
    l8_tendsto_law_of_ae P X Y hXm hYm hae
  have hεsmall : ∀ᶠ n in atTop, εs n < 1 :=
    hεt.eventually (gt_mem_nhds one_pos)
  have hmem : ∀ᶠ n in atTop,
      ν n ∈ {ρ : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
        ∃ ε ∈ Ioo (0 : ℝ) 1,
          (ρ : Measure C(Rd d × Rd d, ℝ)) =
            P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ •
              lfppDist κ ξ ε (h ω)))} := by
    filter_upwards [hεsmall] with n hn
    exact ⟨εs n, ⟨hεs n, hn⟩, rfl⟩
  have hcl := mem_closure_of_tendsto hLaw hmem
  have hsup := (hL6a d ξ κ) hB2 P h hh.1.isLGFPlusBddCont
  have hμ := hsup.2.2.2 μ hcl
  exact (ae_of_ae_map hYm.aemeasurable hμ).mono fun ω hω => hω.2

end HigherDimLQGMetric
