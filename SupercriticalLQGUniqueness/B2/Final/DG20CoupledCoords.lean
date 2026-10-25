import SupercriticalLQGUniqueness.B2.Final.CouplingGlue
import SupercriticalLQGUniqueness.B2.DG20Lim.SkUpgradeCoords

 


















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.DG20Lim (RatCoords RData finiteRatCoords normalizedContLFPP)

namespace SupercriticalLQGUniqueness.B2.Final

 
def CoupledRatCoords (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (hN : ℕ → Ω' → DistC)
    (L : Ω' → LSCMetric) : Prop :=
  ∃ (Z : ℕ → Ω' → RatCoords) (Zlim : Ω' → RatCoords),
    (∀ n, Measurable (Z n)) ∧ Measurable Zlim ∧
    (∀ᵐ ω ∂P', ∀ n, Z n ω =
      finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (e n)) (V (e n) (hN n ω)))) ∧
    (∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω))) ∧
    (∀ᵐ ω ∂P', ∃ R : RData,
      R.across = (fun O O' => (Zlim ω).1 (O, O')) ∧ R.around = (Zlim ω).2 ∧
      (L ω).toLSCFun.1 = R.toLSCFun.1)

 

theorem ae_eq_comp_of_joint_law {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α]
    {P' : Measure Ω'} {μ : Measure α} {X : Ω' → α} {Z : Ω' → RatCoords}
    (hX : Measurable X) (hZ : Measurable Z) (hXlaw : P'.map X = μ)
    {f : α → RatCoords} (hf : AEMeasurable f μ)
    (hlaw : P'.map (fun ω => (X ω, Z ω)) = μ.map (fun g => (g, f g))) :
    ∀ᵐ ω ∂P', Z ω = f (X ω) := by
  let g : α → RatCoords := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  have hS : MeasurableSet {p : α × RatCoords | p.2 = g p.1} :=
    measurableSet_eq_fun measurable_snd (hg.comp measurable_fst)
  have hgraph : Measurable (fun a => (a, g a)) := measurable_id.prodMk hg
  have hlaw' : P'.map (fun ω => (X ω, Z ω)) = μ.map (fun a => (a, g a)) := by
    rw [hlaw]
    exact Measure.map_congr (hf.ae_eq_mk.mono fun a ha => by simp only [g, ha])
  have h1 : ∀ᵐ p ∂(P'.map (fun ω => (X ω, Z ω))), p.2 = g p.1 := by
    rw [hlaw']
    exact (ae_map_iff (p := fun p : α × RatCoords => p.2 = g p.1)
      hgraph.aemeasurable hS).2 (ae_of_all _ fun a => rfl)
  have h2 : ∀ᵐ ω ∂P', Z ω = g (X ω) :=
    ae_of_ae_map (hX.prodMk hZ).aemeasurable h1
  have h3 : ∀ᵐ ω ∂P', g (X ω) = f (X ω) := by
    have : ∀ᵐ a ∂(P'.map X), g a = f a := by
      rw [hXlaw]
      exact hf.ae_eq_mk.mono fun a ha => ha.symm
    exact ae_of_ae_map hX.aemeasurable this
  filter_upwards [h2, h3] with ω h2ω h3ω
  rw [h2ω, h3ω]

 

theorem exists_dg20CouplingData_coords (hSBR : DG20Lim.DG20LimitSkSBR) (hS4 : DG20Section4)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) :
    ∃ φ₁ : ℕ → ℕ, StrictMono φ₁ ∧ ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      ∃ V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ),
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P') (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC)
        (L : Ω' → LSCMetric),
        DG20CouplingData ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L ∧
        CoupledRatCoords ξ m (fun n => ε (φ₁ n)) V P' hN L := by
  obtain ⟨φ₁, hφ₁, c₀, hc₀, hCouple⟩ := hSBR ξ Q hQ m hm ε hε
  have he : Tendsto (fun n => (ε (φ₁ n) : ℝ)) atTop (𝓝 0) := hε.comp hφ₁.tendsto_atTop
  obtain ⟨c, hc, hΛ⟩ :=
    exists_pfeNormalizer_of_limits hS4 ξ Q hQ m hm (fun n => ε (φ₁ n)) he c₀ hc₀
  obtain ⟨V, hVm, hV⟩ := exists_canonical_heat_versions
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  have := hprob
  obtain ⟨Ω', M', SB', P', hP', h', hN, F, L, Z, Zlim, hLm, hh', hLaw, hField, hFc, hLsc,
    hRat, hGeom, hZm, hZlimm, hZlaw, -, hZconv, hLink⟩ :=
    hCouple normGFFLaw id hcan V (PfeLocal.l1_isHeatSmoothing_canonical V hV)
  let _ : MeasurableSpace Ω' := M'
  have : StandardBorelSpace Ω' := SB'
  have : IsProbabilityMeasure P' := hP'
  have hsrc : ∀ n, Measurable fun g : DistC =>
      (g, rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g)) := fun n =>
    measurable_id.prodMk (Measurable.of_eval fun p =>
      PfeWeyl.measurable_rescaledLFPP_comp (ξ : ℝ) (m (ε (φ₁ n))) (hVm (ε (φ₁ n))) p)
  have hLaw' : ∀ n, P'.map (fun ω => (hN n ω, F n ω)) =
      normGFFLaw.map (fun g : DistC =>
        (g, rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g))) := fun n => hLaw n
  have hJ : ∀ n, AEMeasurable (fun ω => (hN n ω, F n ω)) P' := fun n =>
    PfeAxioms.aemeasurable_of_map_eq_nondirac normGFFLaw P' _ _ (hsrc n).aemeasurable
      (fun x => PfeAxioms.gff_joint_law_ne_dirac normGFFLaw id hcan.1
        (fun g => rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g))
        (Measurable.of_eval fun p => PfeWeyl.measurable_rescaledLFPP_comp (ξ : ℝ)
          (m (ε (φ₁ n))) (hVm (ε (φ₁ n))) p).aemeasurable x)
      (hLaw' n)
  have hNa0 : ∀ n, AEMeasurable (hN n) P' := fun n => measurable_fst.comp_aemeasurable (hJ n)
  have hNa : ∀ n, ∃ g : Ω' → DistC, Measurable g ∧ hN n =ᵐ[P'] g := fun n =>
    ⟨(hNa0 n).mk _, (hNa0 n).measurable_mk, (hNa0 n).ae_eq_mk⟩
  choose hN' hN'm hN'eq using hNa
  have hid : ∀ n, ∀ᵐ ω ∂P',
      F n ω = rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω)) := fun n =>
    PfeWeyl.ae_eq_rescaledLFPP_of_joint_law (ξ : ℝ) (m (ε (φ₁ n))) (hVm _) P'
      (hN n) (F n) (hFc n) (hLaw' n)
  have hlawN : ∀ n, P'.map (hN' n) = normGFFLaw := by
    intro n
    rw [← Measure.map_congr (hN'eq n)]
    have h1 : P'.map (hN n) = (P'.map (fun ω => (hN n ω, F n ω))).map Prod.fst := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hJ n)]
      rfl
    rw [h1, hLaw' n, Measure.map_map measurable_fst (hsrc n)]
    exact Measure.map_id
  have hall : ∀ᵐ ω ∂P', ∀ n, hN n ω = hN' n ω := ae_all_iff.2 hN'eq
  have hidall : ∀ᵐ ω ∂P', ∀ n,
      F n ω = rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN n ω)) := ae_all_iff.2 hid
  
  have hZid : ∀ n, ∀ᵐ ω ∂P', Z n ω = finiteRatCoords
      (normalizedContLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN' n ω))) := by
    intro n
    have hDm : Measurable fun g : DistC =>
        normalizedContLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g) :=
      (DG20Lim.measurable_normalizedContLFPP (ξ : ℝ) (m (ε (φ₁ n)))).comp (hVm _)
    have hf : AEMeasurable (fun g : DistC => finiteRatCoords
        (normalizedContLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g))) normGFFLaw :=
      DG20Lim.aemeasurable_finiteRatCoords _ hDm.aemeasurable
    have hlaw2 : P'.map (fun ω => (hN' n ω, Z n ω)) = normGFFLaw.map (fun g => (g,
        finiteRatCoords (normalizedContLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) g)))) := by
      exact (Measure.map_congr ((hN'eq n).mono fun ω hω => by simp only [hω])).trans
        (hZlaw n)
    exact ae_eq_comp_of_joint_law (hN'm n) (hZm n) (hlawN n) hf hlaw2
  refine ⟨φ₁, hφ₁, c, V, Ω', M', SB', P', hP', h', hN', L, ?_, ?_⟩
  · refine
      { exponent := hQ
        normalizer := hm
        scale_tendsto := he
        ratio := hc
        ratio_bound := hΛ
        heat_measurable := hVm
        heat_ae := hV
        limit_field := hh'
        field_measurable := hN'm
        field_law := hlawN
        field_tendsto := ?_
        limit_measurable := hLm
        metric_tendsto := ?_
        rational_tendsto := ?_
        geometry := hGeom }
    · filter_upwards [hField, hall] with ω hω heq
      have hfun : (fun n => hN' n ω) = fun n => hN n ω := funext fun n => (heq n).symm
      rw [hfun]
      exact hω
    · filter_upwards [hLsc, hidall, hall] with ω hl hidω heq
      rw [PfeWeyl.tendsto_normalizedLFPP_iff_lscTendsto]
      have hfun : (fun n => rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN' n ω))) =
          fun n => F n ω := funext fun n => by rw [hidω n, heq n]
      rw [hfun]
      exact hl
    · filter_upwards [hRat, hidall, hall] with ω hr hidω heq u v hu hv
      have hfun : (fun n => rescaledLFPP (ξ : ℝ) (m (ε (φ₁ n))) (V (ε (φ₁ n)) (hN' n ω))
          (u, v)) = fun n => F n ω (u, v) := funext fun n => by rw [hidω n, heq n]
      rw [hfun]
      exact hr u v hu hv
  · exact ⟨Z, Zlim, hZm, hZlimm, ae_all_iff.2 hZid, hZconv, hLink⟩

end SupercriticalLQGUniqueness.B2.Final
