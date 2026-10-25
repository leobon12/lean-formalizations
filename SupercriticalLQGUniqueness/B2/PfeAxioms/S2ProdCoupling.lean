import SupercriticalLQGUniqueness.B2.PfeAxioms.A4DG20Inputs
import SupercriticalLQGUniqueness.B2.PfeAxioms.RealAxiomVSkC
import SupercriticalLQGUniqueness.B2.PfeAxioms.NormalizedCanonicalModel
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionBdd
import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeOfInputs
import SupercriticalLQGUniqueness.B2.DG20Lim.CanonicalFiniteLFPP
import SupercriticalLQGUniqueness.B2.PfeWeyl.S3Bridge
import SupercriticalLQGUniqueness.B2.PfeWeyl.S1Transfer
import SupercriticalLQGUniqueness.B2.PfeAxioms.NonDiracGFF

 




















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem canonicalHeatVersion_isHeatSmoothing' (δ : Ioi (0 : ℝ)) :
    IsHeatSmoothing normGFFLaw (id : DistC → DistC) δ
      (B2.DG20Lim.canonicalHeatVersion δ) := by
  have _ : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  have hh : LQGMetric.IsGFFPlusBddCont (id : DistC → DistC) normGFFLaw :=
    LQGMetric.DFGPS.isGFFPlusBddCont_of_wp normalized_canonical_model.2.1
  obtain ⟨X, hXe, hX⟩ := exists_heatVersion_bdd hh δ
  intro z
  have hHe := B2.DG20Lim.canonicalHeatVersion_ae δ
  filter_upwards [hXe, hX z, hHe] with g hg hXg hHg
  dsimp only [id] at hg hXg ⊢
  simpa only [hg z, (congrFun hHg z)] using hXg

 


def IdentifiedDG20Coupling (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (e : ℕ → Ioi (0 : ℝ)) (V : Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric) : Prop :=
  IsNormalizedWholePlaneGFF h' P' ∧ (∀ n, Measurable (hN n)) ∧
    (∀ n, P'.map (hN n) = normGFFLaw) ∧
    (∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω))) ∧ Measurable L ∧
    (∀ᵐ ω ∂P', Tendsto (fun n =>
      PfeWeyl.normalizedLFPPMetric (ξ : ℝ) (m (e n)) (V (e n) (hN n ω))) atTop (𝓝 (L ω))) ∧
    (∀ᵐ ω ∂P', ∀ u v : ℂ, IsRationalPoint u → IsRationalPoint v →
      Tendsto (fun n => rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)) (u, v)) atTop
        (𝓝 ((L ω).toLSCFun.1 (u, v)))) ∧
    (∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
      (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
      (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
        ∃ (γ : ℝ → ℂ) (a b : ℝ),
          (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧ (L ω).len γ a b = (L ω).1 (u, v)))

 
theorem exists_normalizer_identified_coupling
    (hS4 : DG20Section4) (hPerc : DG20PercEstimate') (hRatio : DG20QuantileRatio)
    (hRel : DG20ExponentRelation) (hPos : DG20ExponentPositive)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ₁ : ℕ → ℕ, StrictMono φ₁ ∧
      ∃ c : Ioi (0 : ℝ) → Ioi (0 : ℝ),
        (∀ r : ℚ, ∀ hr : 0 < r,
          Tendsto (fun n => (r : ℝ) *
            (m ⟨(ε (φ₁ n) : ℝ) / (r : ℝ),
              Set.mem_Ioi.mpr (div_pos (ε (φ₁ n)).property (Rat.cast_pos.mpr hr))⟩ : ℝ) /
            (m (ε (φ₁ n)) : ℝ)) atTop
            (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
        (∃ Λ : ℝ, 1 < Λ ∧
          ∀ δ : Ioo (0 : ℝ) 1, ∀ r : ℚ, ∀ hr : 0 < r,
            Λ⁻¹ * (δ : ℝ) ^ Λ ≤
              (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ∧
            (c ⟨(δ : ℝ) * (r : ℝ), Set.mem_Ioi.mpr
                (mul_pos δ.property.1 (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ) ≤
              Λ * (δ : ℝ) ^ (-Λ)) ∧
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω')
          (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
          IdentifiedDG20Coupling ξ m (ε ∘ φ₁) B2.DG20Lim.canonicalHeatVersion P' h' hN L := by
  letI : IsProbabilityMeasure normGFFLaw := normalized_canonical_model.1
  
  obtain ⟨φV, hφV, c, hc, Λ, hΛ, hV17⟩ := exists_real_axiomV_of_DG20LimitSkC hS4
    (dg20LimitSkC_of_dg20Inputs hS4 hPerc hRatio hRel hPos) ξ Q hQ m hm ε hε
  have hεV : Tendsto (fun n => (ε (φV n) : ℝ)) atTop (𝓝 0) := hε.comp hφV.tendsto_atTop
  
  obtain ⟨φS, hφS, -, -, hCouple⟩ := B2.DG20Lim.dg20LimitSkSB_of_inputs hS4 hPerc hRatio hRel
    hPos B2.LscTop.iface_lscTop ξ Q hQ m hm (fun n => ε (φV n)) hεV
  set V := B2.DG20Lim.canonicalHeatVersion with hVdef
  obtain ⟨Ω', M', SB', P', hP', h', hN, F, L, hLm, hh', hLaw, hField, hFc, hLsc, hRat, hGeom⟩ :=
    hCouple normGFFLaw id normalized_canonical_model.2 V canonicalHeatVersion_isHeatSmoothing'
  letI : MeasurableSpace Ω' := M'
  letI : IsProbabilityMeasure P' := hP'
  set e : ℕ → Ioi (0 : ℝ) := fun n => ε (φV (φS n)) with he
  have hRm : ∀ n, Measurable fun g : DistC =>
      (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g)) := fun n =>
    measurable_id.prodMk (Measurable.of_eval fun p =>
      PfeWeyl.measurable_rescaledLFPP_comp (ξ : ℝ) (m (e n))
        (B2.DG20Lim.canonicalHeatVersion_measurable (e n)) p)
  
  have hLaw' : ∀ n, P'.map (fun ω => (hN n ω, F n ω)) =
      normGFFLaw.map (fun g : DistC => (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g))) :=
    fun n => hLaw n
  have hpairAE : ∀ n, AEMeasurable (fun ω => (hN n ω, F n ω)) P' := by
    intro n
    by_contra hnot
    have h0 := Measure.map_of_not_aemeasurable_of_ne_zero hnot (IsProbabilityMeasure.ne_zero P')
    rw [hLaw' n] at h0
    have h1 := congrArg (Measure.map Prod.fst) h0
    rw [Measure.map_map measurable_fst (hRm n), Measure.map_dirac' measurable_fst] at h1
    have h2 : (Prod.fst ∘ fun g : DistC => (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g))) =
        id := rfl
    rw [h2] at h1
    exact wholePlaneGFF_map_ne_dirac normGFFLaw id normalized_canonical_model.2.1 _ h1
  have hNae : ∀ n, AEMeasurable (hN n) P' := fun n => (hpairAE n).fst
  set hN' : ℕ → Ω' → DistC := fun n => (hNae n).mk (hN n) with hN'def
  have hN'm : ∀ n, Measurable (hN' n) := fun n => (hNae n).measurable_mk
  have hN'eq : ∀ᵐ ω ∂P', ∀ n, hN n ω = hN' n ω :=
    ae_all_iff.2 fun n => (hNae n).ae_eq_mk
  
  have hid : ∀ n, ∀ᵐ ω ∂P', F n ω = rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)) :=
    fun n => PfeWeyl.ae_eq_rescaledLFPP_of_joint_law (ξ : ℝ) (m (e n))
      (B2.DG20Lim.canonicalHeatVersion_measurable (e n)) P' (hN n) (F n) (hFc n) (hLaw n)
  have hidAll := ae_all_iff.2 hid
  
  have hNlaw : ∀ n, P'.map (hN' n) = normGFFLaw := by
    intro n
    rw [Measure.map_congr (hNae n).ae_eq_mk.symm]
    have h1 : (P'.map fun ω => (hN n ω, F n ω)).map Prod.fst = P'.map (hN n) :=
      AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hpairAE n)
    rw [← h1, hLaw' n, Measure.map_map measurable_fst (hRm n)]
    have h2 : (Prod.fst ∘ fun g : DistC => (g, rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) g))) =
        id := rfl
    rw [h2, Measure.map_id]
  refine ⟨φV ∘ φS, hφV.comp hφS, c, fun r hr => (hc r hr).comp hφS.tendsto_atTop,
    ⟨Λ, hΛ, hV17⟩, Ω', M', SB', P', hP', h', hN', L, ⟨hh', hN'm, hNlaw, ?_, hLm, ?_, ?_, hGeom⟩⟩
  · filter_upwards [hField, hN'eq] with ω hω heq
    simpa only [heq] using hω
  · filter_upwards [hLsc, hidAll, hN'eq] with ω hω hidω heq
    apply (PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto (ξ : ℝ) (fun n => m (e n))
      (fun n => V (e n) (hN' n ω)) (L ω)).2
    have hfun : (fun n => F n ω) = fun n => rescaledLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN' n ω)) :=
      funext fun n => by rw [hidω n, heq n]
    rw [← hfun]
    exact hω
  · filter_upwards [hRat, hidAll, hN'eq] with ω hω hidω heq
    intro u v hu hv
    exact (hω u v hu hv).congr fun n => by rw [hidω n, heq n]; rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
