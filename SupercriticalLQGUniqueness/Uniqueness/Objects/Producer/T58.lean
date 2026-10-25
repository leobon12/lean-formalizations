import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T57f
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.Geom
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.SourceStatementsV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.QPosBridgeV2




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

open LQGMetric (DistC TestC addFun testCont)

 

 
def circleFamily (z : ℂ) (r : Set.Ioi (0 : ℝ)) : Set (Set.Ioi (0 : ℝ) × ℂ) := {(oneR, z), (r, z)}

theorem circleFamily_countable (z : ℂ) (r : Set.Ioi (0 : ℝ)) : (circleFamily z r).Countable :=
  (Set.countable_singleton _).insert _

theorem oneR_mem_circleFamily (z : ℂ) (r : Set.Ioi (0 : ℝ)) : (oneR, z) ∈ circleFamily z r :=
  Set.mem_insert _ _

theorem r_mem_circleFamily (z : ℂ) (r : Set.Ioi (0 : ℝ)) : (r, z) ∈ circleFamily z r :=
  Set.mem_insert_of_mem _ rfl

 

 
def BoundsAt (D : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (par : EndSaving.Interfaces.Parameters ξ) (z : ℂ)
    (r : Set.Ioi (0 : ℝ)) (U V : TopologicalSpace.Opens ℂ) (u : DistC) : Prop :=
  ∀ c : ℝ, IsCircleAverage u r z c →
    let N : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c))
    OptimalConstants.Ratios.setDist (D u) (V : Set ℂ)
      (Metric.sphere z r ∪ Metric.sphere z (3 * (r : ℝ))) ≥
        ENNReal.ofReal par.Cacross * N ∧
    (∃ A : EuclideanAnnulus,
      A.center = z ∧ A.innerRadius = 3 * (r : ℝ) ∧
      A.outerRadius = 4 * (r : ℝ) ∧
      aroundDist (D u) A ≤ ENNReal.ofReal par.Caround * N) ∧
    EndSaving.Interfaces.HasTubeSeparator (D u) z r U (ENNReal.ofReal par.Ctube * N)

 

 

structure ObjectInputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (par : EndSaving.Interfaces.Parameters ξ)
    (pbar : Set.Ioo (0 : ℝ) 1) (z : ℂ) (r : Set.Ioi (0 : ℝ)) where
   
  U : TopologicalSpace.Opens ℂ
   
  V : TopologicalSpace.Opens ℂ
   
  f : TestC
  U_annular : EndSaving.InterfaceV2.IsOpenAnnularTubeV2 z r U
  V_annular : EndSaving.InterfaceV2.IsOpenAnnularTubeV2 z r V
  closure_U_V : closure (U : Set ℂ) ⊆ (V : Set ℂ)
  closure_V_annulus : closure (V : Set ℂ) ⊆
    {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)}
  f_nonneg : ∀ x : ℂ, 0 ≤ f x
  f_le : ∀ x : ℂ, f x ≤ par.Cmax
  f_on_U : ∀ x ∈ (U : Set ℂ), f x = par.Cmax
  f_off_V : ∀ x ∉ (V : Set ℂ), f x = 0
   
  Target : Set DistC
   
  L : Set DistC
  L_local : @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC)
    {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) L
  L_null : (P.map h) (L \ centreTarget Target z) = 0
   
  L_prob : ENNReal.ofReal (pbar : ℝ) ≤ (P.map h) L
   
  bounds : ∀ u, LocalGood (ξ : ℝ) D D' {z} (circleFamily z r) u → normTranslate z u ∈ Target →
    BoundsAt D ξ Q par z r U V u
   
  rn : ∀ u, LocalGood (ξ : ℝ) D D' {z} (circleFamily z r) u → normTranslate z u ∈ Target →
    par.Crn⁻¹ ≤ LQGMetric.cmDensity f (LQGMetric.pair0 u) ∧
      LQGMetric.cmDensity f (LQGMetric.pair0 u) ≤ par.Crn
   
  shortcut : ∀ u, LocalGood (ξ : ℝ) D D' {z} (circleFamily z r) u → normTranslate z u ∈ Target →
    ShortcutAt D D' (ξ : ℝ) Q par.Ctime par.Cinc cMid z r V (testCont f) u

namespace ObjectInputs

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
  {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ} {pbar : Set.Ioo (0 : ℝ) 1} {z : ℂ}
  {r : Set.Ioi (0 : ℝ)}

 
def event (I : ObjectInputs P h D D' ξ Q cMid par pbar z r) : Set DistC :=
  sectionFiveEvent P h (ξ : ℝ) D D' {z} (circleFamily z r) I.Target z I.L

 
theorem event_spec [IsProbabilityMeasure P] (I : ObjectInputs P h D D' ξ Q cMid par pbar z r)
    (hh : IsNormalizedWholePlaneGFF h P) (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D') :
    MeasurableSet I.event ∧
      (∀ u c, u ∈ I.event ↔ LQGMetric.addConst u c ∈ I.event) ∧
      (∃ E₀ : Set DistC,
        @MeasurableSet DistC (LQGMetric.Blueprint.fieldSigmaClosed0 (id : DistC → DistC)
          {x : ℂ | r ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}) E₀ ∧
        I.event =ᵐ[P.map h] E₀) ∧
      ENNReal.ofReal (pbar : ℝ) ≤ P (h ⁻¹' I.event) ∧
      I.event ⊆ centreTarget I.Target z ∧
      (∀ u ∈ I.event, LocalGood (ξ : ℝ) D D' {z} (circleFamily z r) u) :=
  sectionFiveEvent_v2 hh hD hD' (EndSaving.InterfaceV2.q_pos_of_weak_metric ξ Q D hD) (Set.countable_singleton z)
    (circleFamily_countable z r) (oneR_mem_circleFamily z r) I.Target I.L_local I.L_null
    (pbar : ℝ) I.L_prob

 
def toObjectAtV2 [IsProbabilityMeasure P] (I : ObjectInputs P h D D' ξ Q cMid par pbar z r)
    (hh : IsNormalizedWholePlaneGFF h P) (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D') : EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar z r where
  U := I.U
  V := I.V
  f := I.f
  E := I.event
  U_annular := I.U_annular
  V_annular := I.V_annular
  closure_U_V := I.closure_U_V
  closure_V_annulus := I.closure_V_annulus
  f_nonneg := I.f_nonneg
  f_le := I.f_le
  f_on_U := I.f_on_U
  f_off_V := I.f_off_V
  E_measurable := (I.event_spec hh hD hD').1
  E_constant := (I.event_spec hh hD hD').2.1
  E_local := (I.event_spec hh hD hD').2.2.1
  E_probability := (I.event_spec hh hD hD').2.2.2.1
  E_circle := fun u hu =>
    ((I.event_spec hh hD hD').2.2.2.2.2 u hu).2.2.2 (r, z) (r_mem_circleFamily z r)
  E_bounds := fun u hu =>
    I.bounds u ((I.event_spec hh hD hD').2.2.2.2.2 u hu) ((I.event_spec hh hD hD').2.2.2.2.1 hu)
  E_rn := fun u hu =>
    I.rn u ((I.event_spec hh hD hD').2.2.2.2.2 u hu) ((I.event_spec hh hD hD').2.2.2.2.1 hu)
  E_shortcut := fun u hu =>
    I.shortcut u ((I.event_spec hh hD hD').2.2.2.2.2 u hu) ((I.event_spec hh hD hD').2.2.2.2.1 hu)

end ObjectInputs

 

 

structure T58Inputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (cMinus cPlus : ℝ≥0∞)
    (pbar : Set.Ioo (0 : ℝ) 1) where
   
  cMid' : ℝ
  cMid'_lower : cMinus.toReal < cMid'
  cMid'_upper : cMid' < EndSaving.Interfaces.midpoint cMinus cPlus
   
  radii : EndSaving.Interfaces.AdmissibleRadii
  params : EndSaving.Interfaces.Parameters ξ
   
  density : ∀ κ : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ j : ℕ,
      let b : Set.Ioi (0 : ℝ) := EndSaving.Interfaces.dyadicRadius j
      ENNReal.ofReal (κ : ℝ) ≤
        P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ
          ⟨cMid', lt_of_le_of_lt ENNReal.toReal_nonneg cMid'_lower⟩) →
      ∃ F : Finset ℝ,
        (F : Set ℝ) = radii.radii ∩ Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) ∧
        (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ F.card
   
  objects : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ radii.radii →
    ObjectInputs P h D D' ξ Q (EndSaving.Interfaces.midpoint cMinus cPlus) params pbar z r

 
def T58Inputs.toObjectsExistV2 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} {D D' : DistC → LSCMetric} {ξ : Set.Ioi (0 : ℝ)}
    {Q : ℝ} {cMinus cPlus : ℝ≥0∞} {pbar : Set.Ioo (0 : ℝ) 1}
    (I : T58Inputs P h D D' ξ Q cMinus cPlus pbar) (hh : IsNormalizedWholePlaneGFF h P)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D') :
    EndSaving.InterfaceV2.ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar :=
  ⟨I.cMid', I.cMid'_lower, I.cMid'_upper, I.radii, I.params,
    fun z r hr => (I.objects z r hr).toObjectAtV2 hh hD hD', I.density⟩

 

theorem t58_of_inputs {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (hInputs : ∀ pbar : Set.Ioo (0 : ℝ) 1, Nonempty (T58Inputs P h D D' ξ Q cMinus cPlus pbar)) :
    EndSaving.InterfaceV2.T58Statement P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict :=
  fun pbar => (hInputs pbar).map fun I => I.toObjectsExistV2 hGFF hD hD'

 

 






structure T57Inputs (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (r : Set.Ioi (0 : ℝ)) (U₀ V₀ : TopologicalSpace.Opens ℂ)
    (g₀ : C(ℂ, ℝ)) (Target : Set DistC) where
   
  C : Objects.CorrectedEvent.Constants
   
  T : Objects.CorrectedEvent.TubeData
  hData : Objects.CorrectedEvent.DataMatch C T
  F : ℂ → DistC → Prop
  ξ_eq : C.ξ = ξ
  Q_eq : C.Q = Q
  r_eq : C.r = r
  max_eq : C.A_max = par.Cmax
  inc_eq : cInc C = par.Cinc
   
  event : ∀ g ∈ Target, Objects.CorrectedEvent.correctedEvent C T hData F D D' g
   
  Cp : ℝ
  Cp_pos : 0 < Cp
  comp : ∀ g ∈ Target, ∀ x y : ℂ, D' g (x, y) ≤ ENNReal.ofReal Cp * D g (x, y)
   
  Cmid0 : ℝ
  Cmid0_nonneg : 0 ≤ Cmid0
  cMid_nonneg : 0 ≤ cMid
  ratio : (1 + 10 * Cp * C.lamConst) * Cmid0 ≤ cMid * (1 - 10 * Cp * C.lamConst)
   
  K_nonneg : 0 ≤ C.K_ann
  endpt_le : C.A_endpt ≤ 1
  lam_le : C.lamConst ≤ 1 / 48
  count : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < C.A_nar →
    21 * (((k : ℝ) + 3) * (C.ξ * (C.Q + 3)) + Real.logb 2 (2 * C.A_around) + 2) ≤
      cSel * (T.blockRadius / C.r) * (2 : ℝ) ^ ((k : ℝ) / 4)
   
  tube_sub : Objects.CorrectedEvent.tubeSet T ⊆ (U₀ : Set ℂ)
   
  sep_small : 2 * Real.sqrt C.A_endpt * C.ρ + 2 * C.A_sup + 3 * C.A_nar ≤ C.ρ * (1 - C.K_ann)
   
  witness : ∀ g ∈ Target, ∀ c : ℝ, IsCircleAverage g (radius C) 0 c →
    ∀ (P : ℝ → ℂ) (L τ' τ σ σ' : ℝ),
      EndSaving.Interfaces.BumpedGeodesic (D (addFun g (-g₀))) P L →
      P 0 ∉ ball (0 : ℂ) (4 * C.r) → P L ∉ ball (0 : ℂ) (4 * C.r) →
      EndSaving.Interfaces.Excursion P L (ball (0 : ℂ) (4 * C.r)) V₀ τ' τ σ σ' →
      ∀ (hτ : P τ ∈ ball (0 : ℂ) (4 * C.r)) (hσ : P σ ∈ ball (0 : ℂ) (4 * C.r)),
        ENNReal.ofReal par.Ctime * ENNReal.ofReal (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) ≤
          (D g).internal (ball (0 : ℂ) (4 * C.r)) (⟨P τ, hτ⟩, ⟨P σ, hσ⟩) →
        Nonempty (T57Witness C T hData endpt_le (D g) (D' g) (D (addFun g (-g₀)))
          (D' (addFun g (-g₀))) (V₀ : Set ℂ) (C.r ^ (C.ξ * C.Q) * Real.exp (C.ξ * c)) Cmid0 P L
          τ' τ σ σ')

 

theorem T57Inputs.shortcut {D D' : DistC → LSCMetric} {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ}
    {par : EndSaving.Interfaces.Parameters ξ} {r : Set.Ioi (0 : ℝ)} {U₀ V₀ : TopologicalSpace.Opens ℂ}
    {g₀ : C(ℂ, ℝ)} {Target : Set DistC} (I : T57Inputs D D' ξ Q cMid par r U₀ V₀ g₀ Target)
    {z : ℂ} {U V : TopologicalSpace.Opens ℂ} {f : TestC}
    (hU : ∀ w : ℂ, w ∈ (U₀ : Set ℂ) ↔ w + z ∈ (U : Set ℂ))
    (hV : ∀ w : ℂ, w ∈ (V₀ : Set ℂ) ↔ w + z ∈ (V : Set ℂ)) (hg : ∀ x, g₀ x = f (x + z))
    (hfnn : ∀ x : ℂ, 0 ≤ f x) (hfle : ∀ x : ℂ, f x ≤ par.Cmax)
    (hfU : ∀ x ∈ (U : Set ℂ), f x = par.Cmax) (hfV : ∀ x ∉ (V : Set ℂ), f x = 0)
    (hVann : closure (V : Set ℂ) ⊆ {x : ℂ | r < dist x z ∧ dist x z < 3 * (r : ℝ)}) :
    ∀ u, LocalGood (ξ : ℝ) D D' {z} (circleFamily z r) u → normTranslate z u ∈ Target →
      ShortcutAt D D' (ξ : ℝ) Q par.Ctime par.Cinc cMid z r V (testCont f) u := by
  intro u hgood hT
  have hr := I.C.rPos
  have hgood' : LocalGood I.C.ξ D D' {z} (circleFamily z r) u := by rw [I.ξ_eq]; exact hgood
  have hρ := rho_lt_of_constants I.C I.lam_le
  have hmid := mid_small_of_constants I.C I.K_nonneg I.lam_le I.endpt_le hρ
  have hf : ∀ x : ℂ, 0 ≤ g₀ x ∧ g₀ x ≤ I.C.A_max := fun x => by
    rw [hg]; exact ⟨hfnn _, I.max_eq ▸ hfle _⟩
  have hfV' : ∀ x ∉ (V₀ : Set ℂ), g₀ x = 0 := fun x hx => by
    rw [hg]; exact hfV _ (fun h => hx ((hV x).2 h))
  have hVW : closure (V₀ : Set ℂ) ⊆ ball (0 : ℂ) (4 * I.C.r) := by
    have hV₀ : (V₀ : Set ℂ) = (Homeomorph.addRight z) ⁻¹' (V : Set ℂ) := Set.ext fun w => hV w
    intro x hx
    rw [hV₀, ← Homeomorph.preimage_closure] at hx
    have h1 := (hVann hx).2
    change dist (x + z) z < 3 * (r : ℝ) at h1
    rw [mem_ball, dist_zero_right, I.r_eq]
    rw [dist_eq_norm, add_sub_cancel_right] at h1
    linarith only [h1, r.2.out]
  have hfB : ∀ c : ℂ, ball c I.T.blockRadius ⊆ Objects.CorrectedEvent.tubeSet I.T →
      ∀ x ∈ closedBall c I.T.blockRadius, g₀ x = I.C.A_max := by
    intro c hc x hx
    have hR0 : 0 < I.T.blockRadius := (blockRadius_bounds I.C I.T I.hData I.endpt_le).1
    have hclosed : IsClosed {y : ℂ | g₀ y = I.C.A_max} := isClosed_eq g₀.continuous continuous_const
    have hsub : ball c I.T.blockRadius ⊆ {y : ℂ | g₀ y = I.C.A_max} := fun y hy => by
      show g₀ y = I.C.A_max
      rw [hg, hfU _ ((hU y).1 (I.tube_sub (hc hy))), I.max_eq]
    have hcl := closure_minimal hsub hclosed
    rw [closure_ball c hR0.ne'] at hcl
    exact hcl hx
  have key := shortcutAt_of_t57 I.C I.T I.hData I.F D D' hgood' (Set.mem_singleton z)
    (I.event _ hT) I.Cp_pos I.Cmid0_nonneg I.cMid_nonneg (I.comp _ hT) I.ratio I.K_nonneg
    I.endpt_le hρ I.lam_le (nar_lt_one I.C) (sup_le_blockRadius I.C I.T I.hData I.K_nonneg I.lam_le)
    (nar_le_blockRadius I.C I.T I.hData I.K_nonneg I.lam_le) I.count (V := V) (V₀ := V₀) hV
    (g := testCont f) (g₀ := g₀) hg hf hfV' hVW (fun k => hfB _ (ball_subset_tubeSet I.T k).1)
    (fun k => hfB _ (ball_subset_tubeSet I.T k).2)
    (fun k => (blockNbhd_subset_midAnn I.C I.T I.hData I.K_nonneg I.endpt_le hmid k).1)
    (fun k => (blockNbhd_subset_midAnn I.C I.T I.hData I.K_nonneg I.endpt_le hmid k).2)
    (fun k => (blockBall_subset_ann I.C I.T I.hData I.K_nonneg I.endpt_le hρ k).1)
    (fun k => (blockBall_subset_ann I.C I.T I.hData I.K_nonneg I.endpt_le hρ k).2)
    (blockNbhd_sep I.C I.T I.hData I.K_nonneg I.sep_small) (I.witness _ hT)
  rw [I.ξ_eq, I.Q_eq, I.inc_eq, show radius I.C = r from Subtype.ext I.r_eq] at key
  exact key

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
