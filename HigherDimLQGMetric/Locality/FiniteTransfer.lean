import HigherDimLQGMetric.Locality.LawCI

/-! Transfer of one finite-domain conditional-independence statement from
the second coupling to the original normalized field and metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.GM.Bilip
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_finite_locality_of_coupling
    {d : ℕ} (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (Dh : Ω → ContMetric d)
    (hh : Measurable h) (hDh : Measurable Dh)
    (hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength)
    (V : TopologicalSpace.Opens (Rd d)) (z₀ : Rd d) (ρ : ℝ)
    (F : Ω → C(Rd d, ℝ))
    (Ψ : (CoordJ → ℝ) → ℝ × C(Rd d, ℝ)) (hΨ : Measurable Ψ)
    (hΨeq : ∀ ω, Ψ (pairJ ⊤ (h ω)) =
      (sphereAvg (h ω) ρ z₀, F ω))
    (R : Ω → DistOn (extOpen V))
    (Φ : (CoordJ → ℝ) → C(Rd d, ℝ) × DistOn (extOpen V))
    (hΦ : Measurable Φ)
    (hΦeq : (fun ω => (F ω, R ω)) = Φ ∘ (fun ω => pairJ ⊤ (h ω)))
    (hFm : Measurable[fieldSigmaRd
      (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)) V] F)
    (raw : Ω → DistOn (extOpen V)) (hRae : raw =ᵐ[P] R)
    (hdet : LQGMetric.AEDeterminedBy
      (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀))
      (fun ω => (restrictTo V
        (addConst (h ω) (-sphereAvg (h ω) ρ z₀)), raw ω)) P)
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    {E : Type} [MeasurableSpace E] [StandardBorelSpace E]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (Y : E → L7aMarkedBase d) (hY : Measurable Y)
    (J₁ : E → L7aFiniteArray S W) (hJ₁ : Measurable J₁)
    (J₂ : E → L7aFiniteArray T W') (hJ₂ : Measurable J₂)
    (hlaw : Q.map Y = P.map (fun ω =>
      ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))), (Dh ω).1)))
    (hgood : ∀ᵐ e ∂Q,
      (l7a_metricLift (Y e).2).IsLength ∧
      (l7a_normalizedMarkedMetric ξ (Y e)).IsLength ∧
      (∀ i : S, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun (J₁ e i),
        ∀ u v : (W i.1 : Set (Rd d)),
          (l7a_normalizedMarkedMetric ξ (Y e)).internal
            (W i.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e i) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e i) hJ v)) ∧
      (∀ j : T, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun (J₂ e j),
        ∀ u v : (W' j.1 : Set (Rd d)),
          (l7a_perturbedMarkedMetric ξ (Y e)).internal
            (W' j.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e j) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e j) hJ v)))
    (hind : Indep
      (fieldSigmaRd (fun e => l7a_markedField₁ (Y e)) V ⊔
        MeasurableSpace.comap J₁ inferInstance)
      (MeasurableSpace.comap (fun e => (Φ (Y e).1.1).2) inferInstance ⊔
        MeasurableSpace.comap J₂ inferInstance) Q) :
    LQGMetric.CondIndepEv
      (fieldSigmaRd (fun ω => addConst (h ω)
        (-sphereAvg (h ω) ρ z₀)) V)
      (⨆ i ∈ S, famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W i))
      (fullSigmaRd (fun ω => addConst (h ω)
        (-sphereAvg (h ω) ρ z₀)) ⊔
        ⨆ j ∈ T, famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W' j)) P := by
  let X : Ω → L7aMarkedBase d := fun ω =>
    ((pairJ ⊤ (h ω), Ψ (pairJ ⊤ (h ω))), (Dh ω).1)
  have hX : Measurable X :=
    (((measurable_pairJ ⊤).comp hh).prodMk
      (hΨ.comp ((measurable_pairJ ⊤).comp hh))).prodMk
      (measurable_subtype_coe.comp hDh)
  let g' : L7aMarkedBase d → DistRd d := l7a_markedField₁
  let F' : L7aMarkedBase d → C(Rd d, ℝ) := fun q => q.1.2.2
  let R' : L7aMarkedBase d → DistOn (extOpen V) := fun q => (Φ q.1.1).2
  have hg' : Measurable g' := l7a_measurable_markedField₁
  have hF' : Measurable F' :=
    (measurable_snd.comp measurable_snd).comp measurable_fst
  have hR' : Measurable R' :=
    measurable_snd.comp (hΦ.comp (measurable_fst.comp measurable_fst))
  have hgX : (fun ω => addConst (h ω)
      (-sphereAvg (h ω) ρ z₀)) = g' ∘ X := by
    funext ω
    simp only [Function.comp_def, g', X, l7a_markedField₁,
      pairJInv_pairJ, (congrArg Prod.fst (hΨeq ω))]
  have hFX : F = F' ∘ X := by
    funext ω
    exact (congrArg Prod.snd (hΨeq ω)).symm
  have hRX : R = R' ∘ X := by
    funext ω
    have he := congrFun hΦeq ω
    exact (congrArg Prod.snd he).trans rfl
  let Ymark : E → (CoordJ → ℝ) × (ℝ × C(Rd d, ℝ)) :=
    fun e => (Y e).1
  let Xmark : Ω → (CoordJ → ℝ) × (ℝ × C(Rd d, ℝ)) :=
    fun ω => (X ω).1
  have hYmark : Measurable Ymark := measurable_fst.comp hY
  have hXmark : Measurable Xmark := measurable_fst.comp hX
  have hlawmark : Q.map Ymark = P.map Xmark := by
    calc
      Q.map Ymark = (Q.map Y).map Prod.fst :=
        (Measure.map_map measurable_fst hY).symm
      _ = (P.map X).map Prod.fst := by
        simpa only [X] using
          (congrArg (fun μ : Measure (L7aMarkedBase d) => μ.map Prod.fst) hlaw)
      _ = P.map Xmark := Measure.map_map measurable_fst hX
  have hfield := l7a_field_from_mark_law P Q Xmark Ymark
    hXmark hYmark hlawmark V
    (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀))
    (fun q => addConst (pairJInv ⊤ q.1) (-q.2.1))
    (measurable_addConst.comp
      (((measurable_pairJInv ⊤).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd).neg))
    (by
      funext ω
      change addConst (h ω) (-sphereAvg (h ω) ρ z₀) =
        addConst (pairJInv ⊤ (pairJ ⊤ (h ω)))
          (-(Ψ (pairJ ⊤ (h ω))).1)
      rw [pairJInv_pairJ, congrArg Prod.fst (hΨeq ω)])
    F (fun q => q.2.2) (measurable_snd.comp measurable_snd)
    (by funext ω; exact (congrArg Prod.snd (hΨeq ω)).symm)
    hFm R (fun q => (Φ q.1).2)
    (measurable_snd.comp (hΦ.comp measurable_fst))
    (by funext ω; exact (congrArg Prod.snd (congrFun hΦeq ω)).trans rfl)
    raw hRae hdet
  have hQgood : ∀ᵐ e ∂Q,
      (l7a_normalizedMarkedMetric ξ (Y e)).IsLength ∧
      (∀ i : S, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun (J₁ e i),
        ∀ u v : (W i.1 : Set (Rd d)),
          (l7a_normalizedMarkedMetric ξ (Y e)).internal
            (W i.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e i) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e i) hJ v)) ∧
      (∀ j : T, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun (J₂ e j),
        ∀ u v : (W' j.1 : Set (Rd d)),
          (l7a_perturbedMarkedMetric ξ (Y e)).internal
            (W' j.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e j) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e j) hJ v)) ∧
      (∀ u v : Rd d,
        ENNReal.ofReal ((l7a_normalizedMarkedMetric ξ (Y e)).1 (u,v)) =
          weylScale ξ (Y e).1.2.2 (l7a_perturbedMarkedMetric ξ (Y e)) u v) := by
    filter_upwards [hgood] with e he
    exact ⟨he.2.1, he.2.2.1, he.2.2.2,
      l7a_markedWeyl_relation ξ (Y e) he.1⟩
  have hCIQ := l7a_limit_finite_ci ξ S T W W' Q
    (fun e => l7a_normalizedMarkedMetric ξ (Y e))
    (fun e => l7a_perturbedMarkedMetric ξ (Y e))
    (l7a_measurable_normalizedMarkedMetric ξ |>.comp hY)
    (fun e => (Y e).1.2.2) (hF'.comp hY)
    J₁ hJ₁ J₂ hJ₂
    (fieldSigmaRd (fun e => l7a_markedField₁ (Y e)) V)
    (MeasurableSpace.comap (fun e => (Φ (Y e).1.1).2) inferInstance)
    ((measurable_restrictTo V).comp (hg'.comp hY)).comap_le
    (hR'.comp hY).comap_le hfield.1 hQgood hind
    (fullSigmaRd (fun e => l7a_markedField₁ (Y e)))
    hfield.2
  -- The remaining transfer only changes the representation of the same marked law.
  let mBase : MeasurableSpace (L7aMarkedBase d) := inferInstance
  let G₀ : MeasurableSpace (L7aMarkedBase d) :=
    MeasurableSpace.comap (fun q => restrictTo V (g' q)) inferInstance
  let A₀ : MeasurableSpace (L7aMarkedBase d) :=
    ⨆ i ∈ S, MeasurableSpace.comap
      (fun q => (l7a_normalizedMarkedMetric ξ q).chainInf (W i : Set (Rd d)))
      inferInstance
  let B₀ : MeasurableSpace (L7aMarkedBase d) :=
    MeasurableSpace.comap g' inferInstance ⊔
      ⨆ j ∈ T, MeasurableSpace.comap
        (fun q => (l7a_normalizedMarkedMetric ξ q).chainInf (W' j : Set (Rd d)))
        inferInstance
  letI : MeasurableSpace (L7aMarkedBase d) := mBase
  have hchain (U : Set (Rd d)) : Measurable
      (fun q : L7aMarkedBase d =>
        (l7a_normalizedMarkedMetric ξ q).chainInf U) := by
    apply measurable_pi_iff.mpr
    intro u
    apply measurable_pi_iff.mpr
    intro v
    exact (ContMetric.measurable_chainInf U).comp
      ((l7a_measurable_normalizedMarkedMetric ξ).prodMk
        (measurable_const.prodMk measurable_const))
  have hG₀ : G₀ ≤ (inferInstance : MeasurableSpace (L7aMarkedBase d)) :=
    ((measurable_restrictTo V).comp hg').comap_le
  have hA₀ : A₀ ≤ (inferInstance : MeasurableSpace (L7aMarkedBase d)) := by
    refine iSup₂_le fun i _ => ?_
    exact (hchain (W i : Set (Rd d))).comap_le
  have hB₀ : B₀ ≤ (inferInstance : MeasurableSpace (L7aMarkedBase d)) := by
    apply sup_le hg'.comap_le
    refine iSup₂_le fun j _ => ?_
    exact (hchain (W' j : Set (Rd d))).comap_le
  have hCIQ' : LQGMetric.CondIndepEv (G₀.comap Y) (A₀.comap Y)
      (B₀.comap Y) Q := by
    simpa only [G₀, A₀, B₀, MeasurableSpace.comap_sup,
      MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, fieldSigmaRd, fullSigmaRd] using hCIQ
  have hCIP := l7a_condIndepEv_of_equal_laws P Q X Y hX hY hlaw
    G₀ A₀ B₀ hG₀ hA₀ hB₀ hCIQ'
  have hA : (⨆ i ∈ S, famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W i)) ≤
      aeClosure P (A₀.comap X) := by
    refine iSup₂_le fun i hi => ?_
    have heq : (fun ω => l7b_chainFam ξ h Dh ρ z₀ ω (W i)) =ᵐ[P]
        (fun ω => (l7a_normalizedMarkedMetric ξ (X ω)).chainInf
          (W i : Set (Rd d))) := by
      filter_upwards [hlen] with ω hω
      funext u v
      dsimp only [X]
      rw [hΨeq ω]
      exact (l7a_normalizedMarked_chain_original ξ (h ω) (Dh ω) ρ z₀
        (F ω) hω (W i) u v).symm
    have hsource : Measurable[A₀.comap X]
        (fun ω => (l7a_normalizedMarkedMetric ξ (X ω)).chainInf
          (W i : Set (Rd d))) := by
      have hf : Measurable[A₀]
          (fun q : L7aMarkedBase d =>
            (l7a_normalizedMarkedMetric ξ q).chainInf (W i : Set (Rd d))) :=
        measurable_iff_comap_le.mpr (le_iSup₂_of_le i hi le_rfl)
      exact hf.comp (comap_measurable X)
    exact l7a_comap_le_aeClosure_of_ae_eq P hsource heq
  have hB : (fullSigmaRd (fun ω => addConst (h ω)
      (-sphereAvg (h ω) ρ z₀)) ⊔
      ⨆ j ∈ T, famSigmaRd (l7b_chainFam ξ h Dh ρ z₀) (W' j)) ≤
      aeClosure P (B₀.comap X) := by
    apply sup_le
    · have hsmall : MeasurableSpace.comap (g' ∘ X) inferInstance ≤
          B₀.comap X := by
        simpa only [MeasurableSpace.comap_comp] using
          (MeasurableSpace.comap_mono
            (le_sup_left : MeasurableSpace.comap g' inferInstance ≤ B₀))
      rw [← hgX] at hsmall
      exact hsmall.trans (le_aeClosure _)
    · refine iSup₂_le fun j hj => ?_
      have heq : (fun ω => l7b_chainFam ξ h Dh ρ z₀ ω (W' j)) =ᵐ[P]
          (fun ω => (l7a_normalizedMarkedMetric ξ (X ω)).chainInf
            (W' j : Set (Rd d))) := by
        filter_upwards [hlen] with ω hω
        funext u v
        dsimp only [X]
        rw [hΨeq ω]
        exact (l7a_normalizedMarked_chain_original ξ (h ω) (Dh ω) ρ z₀
          (F ω) hω (W' j) u v).symm
      have hsource : Measurable[B₀.comap X]
          (fun ω => (l7a_normalizedMarkedMetric ξ (X ω)).chainInf
            (W' j : Set (Rd d))) := by
        have hf : Measurable[B₀]
            (fun q : L7aMarkedBase d =>
              (l7a_normalizedMarkedMetric ξ q).chainInf (W' j : Set (Rd d))) :=
          measurable_iff_comap_le.mpr (by
            have hσ : MeasurableSpace.comap
                (fun q : L7aMarkedBase d =>
                  (l7a_normalizedMarkedMetric ξ q).chainInf (W' j : Set (Rd d)))
                inferInstance ≤
                (⨆ k ∈ T, MeasurableSpace.comap
                  (fun q : L7aMarkedBase d =>
                    (l7a_normalizedMarkedMetric ξ q).chainInf (W' k : Set (Rd d)))
                  inferInstance) := le_iSup₂_of_le j hj le_rfl
            exact hσ.trans le_sup_right)
        exact hf.comp (comap_measurable X)
      exact l7a_comap_le_aeClosure_of_ae_eq P hsource heq
  have hG : G₀.comap X = fieldSigmaRd
      (fun ω => addConst (h ω) (-sphereAvg (h ω) ρ z₀)) V := by
    have heq : (fun ω => restrictTo V (g' (X ω))) =
        fun ω => restrictTo V (addConst (h ω) (-sphereAvg (h ω) ρ z₀)) := by
      funext ω
      have hge : addConst (h ω) (-sphereAvg (h ω) ρ z₀) = g' (X ω) := by
        simpa only [Function.comp_def] using congrFun hgX ω
      rw [← hge]
    simpa only [G₀, fieldSigmaRd, MeasurableSpace.comap_comp,
      Function.comp_def] using
      congrArg (fun f => MeasurableSpace.comap f inferInstance) heq
  rw [hG] at hCIP
  exact LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure hCIP hA hB

end HigherDimLQGMetric
