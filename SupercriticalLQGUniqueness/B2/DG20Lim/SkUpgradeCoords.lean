import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeOfInputs

 























set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

open SupercriticalLQGUniqueness.B2.Iface

 

def DG20LimitSkSBR : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
            (∀ r : ℚ, ∀ hr : 0 < r,
              Tendsto (fun n => (r : ℝ) *
                (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                  Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                    (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (m (ε (φ n)) : ℝ)) atTop
                (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
            ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
              ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
                (∀ δ, IsHeatSmoothing P h δ (X δ)) →
              ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω')
                (P' : Measure Ω') (_ : IsProbabilityMeasure P') (h' : Ω' → DistC)
                (hN : ℕ → Ω' → DistC)
                (F : ℕ → Ω' → ℂ × ℂ → EReal) (L : Ω' → LSCMetric)
                (Z : ℕ → Ω' → RatCoords) (Zlim : Ω' → RatCoords),
                Measurable L ∧ IsNormalizedWholePlaneGFF h' P' ∧
                (∀ n, P'.map (fun ω => (hN n ω, F n ω)) =
                  P.map (fun ω => (h ω,
                    rescaledLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)))) ∧
                (∀ᵐ ω ∂P', Tendsto (fun n => hN n ω) atTop (𝓝 (h' ω))) ∧
                (∀ n, ∀ᵐ ω ∂P', Continuous (F n ω)) ∧
                (∀ᵐ ω ∂P', LSCTendsto (fun n => F n ω) (L ω).toLSCFun.1) ∧
                (∀ᵐ ω ∂P', ∀ u v : ℂ, IsRationalPoint u → IsRationalPoint v →
                  Tendsto (fun n => F n ω (u, v)) atTop
                    (𝓝 ((L ω).toLSCFun.1 (u, v)))) ∧
                (∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
                  (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
                    ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
                  (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
                    ∃ (γ : ℝ → ℂ) (a b : ℝ),
                      (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
                        (L ω).len γ a b = (L ω).1 (u, v))) ∧
                
                (∀ n, Measurable (Z n)) ∧ Measurable Zlim ∧
                (∀ n, P'.map (fun ω => (hN n ω, Z n ω)) =
                  P.map (fun ω => (h ω, finiteRatCoords
                    (normalizedContLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω))))) ∧
                (∀ n ω, F n ω = finiteMetricE (circleCoordsInv (Z n ω).1)) ∧
                (∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω))) ∧
                (∀ᵐ ω ∂P', ∃ R : RData,
                  R.across = (fun O O' => (Zlim ω).1 (O, O')) ∧
                  R.around = (Zlim ω).2 ∧
                  (L ω).toLSCFun.1 = R.toLSCFun.1)

 
theorem lscTendsto_unique {α : Type*} [TopologicalSpace α]
    {F : ℕ → α × α → EReal} {f g : α × α → EReal}
    (hf : LSCTendsto F f) (hg : LSCTendsto F g) : f = g := by
  have key : ∀ {f g : α × α → EReal}, LSCTendsto F f → LSCTendsto F g →
      ∀ q, f q ≤ g q := by
    intro f g hf hg q
    obtain ⟨p, hp, hpg⟩ := hg.2 q
    exact (hf.1 p q hp).trans_eq hpg.liminf_eq
  funext q
  exact le_antisymm (key hf hg q) (key hg hf q)

 

theorem field_coord_law_of_pairJ_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω')
    (h : Ω → DistC) (hh : Measurable h) (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω))) :
    P'.map (fun ω => (pairJInv ⊤ (Y ω).1, (Y ω).2)) =
      P.map (fun ω => (h ω, finiteRatCoords (D ω))) := by
  have hq : Measurable (fun y : (CoordJ → ℝ) × RatCoords => (pairJInv ⊤ y.1, y.2)) :=
    ((measurable_pairJInv ⊤).comp measurable_fst).prodMk measurable_snd
  have hV : Measurable (measurableRatCoordsVersion D hD) :=
    measurable_measurableRatCoordsVersion D hD
  have hpv : Measurable (fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) :=
    ((measurable_pairJ ⊤).comp hh).prodMk hV
  calc P'.map (fun ω => (pairJInv ⊤ (Y ω).1, (Y ω).2))
      = (P'.map Y).map (fun y : (CoordJ → ℝ) × RatCoords => (pairJInv ⊤ y.1, y.2)) :=
        (Measure.map_map hq hY).symm
    _ = (P.map (fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω))).map
          (fun y : (CoordJ → ℝ) × RatCoords => (pairJInv ⊤ y.1, y.2)) := by rw [hLaw]
    _ = P.map (fun ω => (h ω, measurableRatCoordsVersion D hD ω)) := by
        rw [Measure.map_map hq hpv]
        congr 1
        funext ω
        simp only [Function.comp_apply, pairJInv_pairJ]
    _ = P.map (fun ω => (h ω, finiteRatCoords (D ω))) := by
        refine Measure.map_congr ?_
        filter_upwards [(aemeasurable_finiteRatCoords D hD).ae_eq_mk] with ω hω
        simp only [measurableRatCoordsVersion, ← hω]

 
theorem dg20LimitSkSBR_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (_hRatio : B2.Iface.DG20QuantileRatio)
    (_hRelation : B2.Iface.DG20ExponentRelation)
    (hPositive : B2.Iface.DG20ExponentPositive)
    (_hTop : B2.Iface.LscTop) : DG20LimitSkSBR := by
  intro ξ Q hQ m hm ε hε
  obtain ⟨φ, hφ, c, hc, ρ, hlim, hmarg⟩ :=
    exists_scale_canonical_field_limit hS4 ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω mΩ P hP h hh X hX
  obtain ⟨Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, hCoordLaw, hNorm, hPairLaw, hCont, hConv, hFieldTop⟩ :=
    exists_lfpp_joint_field_skorokhod_of_canonical_limit (ξ : ℝ) m
      (fun n => ε (φ n)) ρ hlim hmarg P h hh X hX
  letI : MeasurableSpace Ω' := mΩ'
  letI : StandardBorelSpace Ω' := sbΩ'
  letI : IsProbabilityMeasure P' := hP'
  let ε' : ℕ → Ioi (0 : ℝ) := fun n => ε (φ n)
  have hε' : Tendsto (fun n => (ε' n : ℝ)) atTop (𝓝 0) :=
    hε.comp hφ.tendsto_atTop
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP (ξ : ℝ) (m (ε' n)) (X (ε' n) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε' n) (m (ε' n)) (ξ : ℝ) (X (ε' n)) (hX (ε' n))
  have hLen : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength := by
    intro n
    exact ae_of_all P (fun ω => isLength_normalizedContLFPP
      (ξ : ℝ) (m (ε' n)) (X (ε' n) ω))
  have hChain := ae_all_finiteCircle_chain_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm hCoordLaw
  have hAround := ae_all_finiteAround_bounds_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm hCoordLaw
  have hRData0 := ae_rdata_of_section51_coupling
    hPerc ξ m hm ε hε φ hφ P P' h hh X hX
    Y Ylim hYm hCoordLaw hConv hChain hAround
  have hLSC := ae_lscTendsto_of_joint_coord_laws P P' h hh.1.measurable
    D hD hLen Y Ylim hYm hCoordLaw hConv hRData0
  have hLaw' : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion
        (fun ω => normalizedContLFPP (ξ : ℝ) (m (ε' n)) (X (ε' n) ω))
        (aemeasurable_normalizedContLFPP_heat_version P h hh
          (ε' n) (m (ε' n)) (ξ : ℝ) (X (ε' n)) (hX (ε' n))) ω)) := by
    intro n
    exact hCoordLaw n
  have hConvAE : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) :=
    ae_of_all P' hConv
  have hRData : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O Q => (Ylim ω).2.1 (O, Q)) ∧
      R.around = (Ylim ω).2.2 :=
    hLSC.mono fun _ hω => by
      obtain ⟨R, ha, hb, _⟩ := hω
      exact ⟨R, ha, hb⟩
  have hTri := ae_triangle_on_coupled_limit_of_inputs
    hS4 hPerc ξ Q hQ m hm P P' h hh X hX ε' hε'
    Y Ylim hYm hLaw' hConvAE hRData
  have hAgree := ae_rational_agreement_on_coupled_limit_of_inputs
    hS4 hPerc hPositive ξ Q hQ m hm P P' h hh X hX ε' hε'
    Y Ylim hYm hLaw' hConvAE hRData
  have hGeom := ae_geometry_on_coupled_limit_of_inputs
    hS4 hPerc hPositive ξ Q hQ m hm P P' h hh X hX ε' hε'
    Y Ylim hYm hLaw' hConvAE hTri
  have hFinite := ae_finite_length_and_range_of_joint_coord_laws
    P P' h hh.1.measurable D hD hLen Y hYm
    (by simpa only [D] using hLaw')
  have hRange : ∀ᵐ ω ∂P', ∀ n,
      finiteCircleCoords (circleCoordsInv (Y n ω).2.1) = (Y n ω).2.1 :=
    hFinite.mono fun _ hω n => (hω n).1
  obtain ⟨L, hLm, hLsc, hRat, hGeometry⟩ :=
    exists_measurable_coupled_limit_metric
      P' Y Ylim hYm hConvAE hRange hLSC hAgree hGeom
  let h' : Ω' → DistC := fun ω => pairJInv ⊤ (Ylim ω).1
  let hN : ℕ → Ω' → DistC := fun n ω => pairJInv ⊤ (Y n ω).1
  let F : ℕ → Ω' → ℂ × ℂ → EReal := fun n ω =>
    finiteMetricE (circleCoordsInv (Y n ω).2.1)
  let Z : ℕ → Ω' → RatCoords := fun n ω => (Y n ω).2
  let Zlim : Ω' → RatCoords := fun ω => (Ylim ω).2
  have hZlaw : ∀ n, P'.map (fun ω => (hN n ω, Z n ω)) =
      P.map (fun ω => (h ω, finiteRatCoords
        (normalizedContLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)))) := fun n =>
    field_coord_law_of_pairJ_law P P' h hh.1.measurable (D n) (hD n) (Y n) (hYm n)
      (hCoordLaw n)
  have hLink : ∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O O' => (Zlim ω).1 (O, O')) ∧ R.around = (Zlim ω).2 ∧
      (L ω).toLSCFun.1 = R.toLSCFun.1 := by
    filter_upwards [hLSC, hLsc] with ω hR hL
    obtain ⟨R, ha, hb, hRt⟩ := hR
    exact ⟨R, ha, hb, lscTendsto_unique hL hRt⟩
  exact ⟨Ω', mΩ', sbΩ', P', hP', h', hN, F, L, Z, Zlim,
    hLm, hNorm, hPairLaw, hFieldTop, fun n => ae_of_all P' (hCont n),
    hLsc, hRat, hGeometry,
    fun n => measurable_snd.comp (hYm n), measurable_snd.comp hYlimm, hZlaw,
    fun _ _ => rfl,
    fun ω => ((continuous_snd.tendsto (Ylim ω)).comp (hConv ω)), hLink⟩

 
theorem dg20LimitSkSB_of_SkSBR (hR : DG20LimitSkSBR) :
    B2.PfeAxioms.Inputs.DG20LimitSkSB := by
  intro ξ Q hQ m hm ε hε
  obtain ⟨φ, hφ, c, hc, hCouple⟩ := hR ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω _ P _ h hh X hX
  obtain ⟨Ω', M', SB', P', hP', h', hN, F, L, -, -,
    hLm, hh', hLaw, hField, hFc, hLsc, hRat, hGeom, -⟩ := hCouple P h hh X hX
  exact ⟨Ω', M', SB', P', hP', h', hN, F, L,
    hLm, hh', hLaw, hField, hFc, hLsc, hRat, hGeom⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
