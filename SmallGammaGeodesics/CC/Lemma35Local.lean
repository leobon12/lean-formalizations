import SmallGammaGeodesics.CC.Lemma35
import SmallGammaGeodesics.CC.LocalityConf
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas
import LQGMetric.Papers.GM.S2.SpatialIndepCirc

/-!
# The event `E^{LM}_r(w)` of [3] Lemma 3.5 is annulus-local (track CC, packet CC8)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D13** ("the good event
`E^{LM}_r(w)` lies a.s. in `σ((h − h_{4r}(w))|_{A_{r/4,2r}(w)})`; the `D^ϕ` part is D4, the `D_h`
part is `GM.setDist_spheres_eq_internal`").

* `mem_of_forall_rat`, `iInf_spheres_eq_iInf_rat`, `forall_sphere_iff_rat`: a closed condition on a
  function continuous on pairs of points of circles holds iff it holds at rational angles.
* `confLMGood_iff_rat` (deterministic): if `e·D^ϕ(·,·;A_{r/2,2r}) = J₁` and
  `e·D_h(·,·;A_{r/4,2r}) = J₂` on the annuli (`e ∈ (0,∞)`), then `ConfLMGood` is the countable
  condition `J₁(u_q, v_q) ≤ C · inf_q J₂(x_q, y_q)` at rational points of the circles.
* `aeEventIn_confLMGood`: `{ω | ConfLMGood …}` is a.s. an event of
  `σ((h − h_{4r}(w))|_{A_{r/4,2r}(w)})` when `B̄_{2r}(w) ⊆ V`. The locality functionals are CC2's
  `exists_confMetric_eq_restrict_addConst` and `exists_internal_eq_restrict_addConst` with
  `c = −h_{4r}(w)`.
* `confLMEvent`, `isAnnulusLocal_confLMEvent`: the event family for `CoverLemma`
  (`c₀ = 4`, `s₁ = 1/16`, `s₂ = 1/2`): `E^{LM}_r(w)` where an activation predicate `act w r` holds
  (`act w r → B̄_{2r}(w) ⊆ V`), the sure event elsewhere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## 1. Rational points of circles -/

/-- a closed condition on a continuous function of `ℝ × ℝ` that holds at all rational pairs
holds everywhere -/
lemma mem_of_forall_rat {F : ℝ × ℝ → ℝ≥0∞} (hF : Continuous F) {T : Set ℝ≥0∞} (hT : IsClosed T)
    (h : ∀ q₁ q₂ : ℚ, F ((q₁ : ℝ), (q₂ : ℝ)) ∈ T) (p : ℝ × ℝ) : F p ∈ T := by
  have hd : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  exact hd.induction_on (p := fun x => F x ∈ T) p (hT.preimage hF) fun q => h q.1 q.2

/-- a function continuous on pairs of points of two circles is continuous in the angles -/
lemma continuous_circlePair {K : ℂ → ℂ → ℝ≥0∞} {U : Set (ℂ × ℂ)} {w : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) U)
    (hU : sphere w a ×ˢ sphere w b ⊆ U) :
    Continuous fun t : ℝ × ℝ => K (circleMap w a t.1) (circleMap w b t.2) :=
  hK.comp_continuous (((continuous_circleMap w a).comp continuous_fst).prodMk
    ((continuous_circleMap w b).comp continuous_snd))
    fun _ => hU ⟨circleMap_mem_sphere w ha _, circleMap_mem_sphere w hb _⟩

/-- the infimum over two circles of a continuous function is the infimum over rational angles -/
lemma iInf_spheres_eq_iInf_rat {K : ℂ → ℂ → ℝ≥0∞} {U : Set (ℂ × ℂ)} {w : ℂ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) U)
    (hU : sphere w a ×ˢ sphere w b ⊆ U) :
    ⨅ x ∈ sphere w a, ⨅ y ∈ sphere w b, K x y =
      ⨅ (q₁ : ℚ) (q₂ : ℚ), K (circleMap w a q₁) (circleMap w b q₂) := by
  refine le_antisymm (le_iInf₂ fun q₁ q₂ => ?_) (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  · exact iInf₂_le_of_le _ (circleMap_mem_sphere w ha _)
      (iInf₂_le _ (circleMap_mem_sphere w hb _))
  · have := mem_of_forall_rat (continuous_circlePair ha hb hK hU)
      (T := Ici (⨅ (q₁ : ℚ) (q₂ : ℚ), K (circleMap w a q₁) (circleMap w b q₂))) isClosed_Ici
      (fun q₁ q₂ => mem_Ici.2 (iInf₂_le (f := fun (q₁ q₂ : ℚ) =>
        K (circleMap w a q₁) (circleMap w b q₂)) q₁ q₂)) (Complex.arg (x - w), Complex.arg (y - w))
    simpa only [mem_Ici, circleMap_arg hx, circleMap_arg hy] using this

/-- a bound over a circle, for a continuous function, holds iff it holds at rational angles -/
lemma forall_sphere_iff_rat {J : ℂ → ℂ → ℝ≥0∞} {U : Set (ℂ × ℂ)} {w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hJ : ContinuousOn (fun p : ℂ × ℂ => J p.1 p.2) U) (hU : sphere w r ×ˢ sphere w r ⊆ U)
    (c : ℝ≥0∞) :
    (∀ u ∈ sphere w r, ∀ v ∈ sphere w r, J u v ≤ c) ↔
      ∀ q₁ q₂ : ℚ, J (circleMap w r q₁) (circleMap w r q₂) ≤ c := by
  refine ⟨fun H q₁ q₂ => H _ (circleMap_mem_sphere w hr _) _ (circleMap_mem_sphere w hr _),
    fun H u hu v hv => ?_⟩
  have := mem_of_forall_rat (continuous_circlePair hr hr hJ hU) (T := Iic c) isClosed_Iic H
    (Complex.arg (u - w), Complex.arg (v - w))
  simpa only [mem_Iic, circleMap_arg hu, circleMap_arg hv] using this

/-! ## 2. The deterministic reduction to countably many values -/

lemma sphere_subset_annulus {w : ℂ} {r a b : ℝ} (ha : a < r) (hb : r < b) :
    sphere w r ⊆ (annulus w a b : Set ℂ) := fun y hy => by
  show a < ‖y - w‖ ∧ ‖y - w‖ < b
  rw [mem_sphere_iff_norm.1 hy]
  exact ⟨ha, hb⟩

/-- **`E^{LM}_r(w)` through countably many values** (deterministic): if `e · D^ϕ(·,·;A) = J₁` on
`A = A_{r/2,2r}(w)` and `e · D_h(·,·;A') = J₂` on `A' = A_{r/4,2r}(w)` for some `e ∈ (0,∞)`, then
`ConfLMGood` holds iff `J₁(u, v) ≤ C · inf J₂(x, y)` for the points `u, v` of `∂B_r(w)` and `x` of
`∂B_{r/2}(w)`, `y` of `∂B_r(w)` at rational angles. Uses continuity of both internal metrics
(`continuousOn_confMetric`, `ContMetric.continuousOn_internal`) and
`GM.setDist_spheres_eq_internal`. -/
theorem confLMGood_iff_rat {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ}
    (hϕ : IsConfNbhd ϕ W V) {h hbar : DistC} {f : C(ℂ, ℝ)} (hL : (D h).IsLength)
    (hL' : (D (addFun hbar f)).IsLength) {C : ℝ} {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hV : closedBall w (2 * r) ⊆ V) {e : ℝ≥0∞} (he0 : e ≠ 0) (het : e ≠ ⊤)
    {J₁ J₂ : ℂ → ℂ → ℝ≥0∞}
    (h1 : ∀ u ∈ annulus w (r / 2) (2 * r), ∀ v ∈ annulus w (r / 2) (2 * r),
      e * confMetric D ϕ (annulus w (r / 2) (2 * r)) hbar f u v = J₁ u v)
    (h2 : ∀ x ∈ annulus w (r / 4) (2 * r), ∀ y ∈ annulus w (r / 4) (2 * r),
      e * (D h).internal (annulus w (r / 4) (2 * r)) x y = J₂ x y) :
    ConfLMGood D ϕ h hbar f C w r ↔
      ∀ q₁ q₂ : ℚ, J₁ (circleMap w r q₁) (circleMap w r q₂) ≤
        ENNReal.ofReal C * ⨅ (q₃ : ℚ) (q₄ : ℚ), J₂ (circleMap w (r / 2) q₃) (circleMap w r q₄) := by
  set A : Set ℂ := (annulus w (r / 2) (2 * r) : Set ℂ) with hAdef
  set A' : Set ℂ := (annulus w (r / 4) (2 * r) : Set ℂ) with hA'def
  have hAo : IsOpen A := (annulus w (r / 2) (2 * r)).isOpen
  have hA'o : IsOpen A' := (annulus w (r / 4) (2 * r)).isOpen
  have hAV : A ⊆ V := fun y hy => hV (mem_closedBall_iff_norm.2 (le_of_lt hy.2))
  have hSA : sphere w r ⊆ A := sphere_subset_annulus (by linarith) (by linarith)
  have hS1 : sphere w r ⊆ A' := sphere_subset_annulus (by linarith) (by linarith)
  have hS2 : sphere w (r / 2) ⊆ A' := sphere_subset_annulus (by linarith) (by linarith)
  -- continuity of `J₁` and `J₂`
  have hJ₁ : ContinuousOn (fun p : ℂ × ℂ => J₁ p.1 p.2) (A ×ˢ A) := by
    have hc := (ENNReal.continuous_const_mul het).comp_continuousOn
      (continuousOn_confMetric (hϕ.mono hAo hAV) hL')
    exact hc.congr fun p hp => (h1 p.1 hp.1 p.2 hp.2).symm
  have hJ₂ : ContinuousOn (fun p : ℂ × ℂ => J₂ p.1 p.2) (A' ×ˢ A') := by
    have hc := (ENNReal.continuous_const_mul het).comp_continuousOn
      ((D h).continuousOn_internal hL hA'o)
    exact hc.congr fun p hp => (h2 p.1 hp.1 p.2 hp.2).symm
  -- the set distance through `J₂`
  have hsub : ∀ y : ℂ, r / 2 ≤ ‖y - w‖ → ‖y - w‖ ≤ r → y ∈ A' := fun y h₁ h₂ =>
    show r / 4 < ‖y - w‖ ∧ ‖y - w‖ < 2 * r from ⟨by linarith, by linarith⟩
  have hsd : e * setDist (D h) (sphere w (r / 2)) (sphere w r) =
      ⨅ x ∈ sphere w (r / 2), ⨅ y ∈ sphere w r, J₂ x y := by
    rw [GM.setDist_spheres_eq_internal (D h) hL (V := A') (by linarith) hsub]
    simp only [ENNReal.mul_iInf_of_ne he0 het]
    exact iInf_congr fun x => iInf_congr fun hx => iInf_congr fun y => iInf_congr fun hy =>
      h2 x (hS2 hx) y (hS1 hy)
  have key : ∀ u ∈ sphere w r, ∀ v ∈ sphere w r,
      (confMetric D ϕ A hbar f u v ≤ ENNReal.ofReal C * setDist (D h) (sphere w (r / 2))
          (sphere w r) ↔
        J₁ u v ≤ ENNReal.ofReal C * ⨅ x ∈ sphere w (r / 2), ⨅ y ∈ sphere w r, J₂ x y) := by
    intro u hu v hv
    rw [← ENNReal.mul_le_mul_iff_right he0 het, h1 u (hSA hu) v (hSA hv), mul_left_comm, hsd]
  unfold ConfLMGood
  rw [← iInf_spheres_eq_iInf_rat (by linarith) hr.le hJ₂ (prod_mono hS2 hS1)]
  exact (forall₂_congr fun u hu => forall₂_congr fun v hv => key u hu v hv).trans
    (forall_sphere_iff_rat hr.le hJ₁ (prod_mono hSA hSA) _)

/-! ## 3. Annulus locality -/

/-- **`E^{LM}_r(w)` is annulus-local** (CC0 D13): if `B̄_{2r}(w) ⊆ V`, the event
`{ω | ConfLMGood …}` is a.s. an event of `σ((h − h_{4r}(w))|_{A_{r/4,2r}(w)})`, written with the
radii `s₁c₀r`, `s₂c₀r` of `IsAnnulusLocal` (`c₀ = 4`, `s₁ = 1/16`, `s₂ = 1/2`). -/
theorem aeEventIn_confLMGood {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    {ϕ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V) (C : ℝ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} (hh : IsWholePlaneGFF h P)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f)
    (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hV : closedBall w (2 * r) ⊆ V) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (4 * r) w))
      (annulus w (1 / 16 * (4 * r)) (1 / 2 * (4 * r))))
      {ω | ConfLMGood D ϕ (h ω) (hbar ω) (f ω) C w r} := by
  have hA'eq : annulus w (1 / 16 * (4 * r)) (1 / 2 * (4 * r)) = annulus w (r / 4) (2 * r) := by
    congr 1 <;> ring
  rw [hA'eq]
  set c : Ω → ℝ := fun ω => -circleAvg (h ω) (4 * r) w with hcdef
  have hcm : Measurable c := ((measurable_circleAvg_left (4 * r) w).comp hh.measurable).neg
  set g : Ω → DistC := fun ω => addConst (h ω) (c ω) with hgdef
  set A : TopologicalSpace.Opens ℂ := annulus w (r / 2) (2 * r) with hAdef
  set A' : TopologicalSpace.Opens ℂ := annulus w (r / 4) (2 * r) with hA'def
  have hAV : (A : Set ℂ) ⊆ V := fun y hy => hV (mem_closedBall_iff_norm.2 (le_of_lt hy.2))
  have hAA' : A ≤ A' := fun y hy =>
    show r / 4 < ‖y - w‖ ∧ ‖y - w‖ < 2 * r from ⟨by linarith [hy.1], hy.2⟩
  obtain ⟨G₁, hG₁, hG₁ae⟩ := exists_confMetric_eq_restrict_addConst hD hϕ A hAV hhb hf hc hcm
  obtain ⟨G₂, hG₂, hG₂ae⟩ := exists_internal_eq_restrict_addConst hD A' hh hcm
  refine ⟨{ω | ∀ q₁ q₂ : ℚ,
      G₁ (restrictTo A (g ω)) (circleMap w r q₁) (circleMap w r q₂) ≤
        ENNReal.ofReal C * ⨅ (q₃ : ℚ) (q₄ : ℚ),
          G₂ (restrictTo A' (g ω)) (circleMap w (r / 2) q₃) (circleMap w r q₄)}, ?_, ?_⟩
  · -- measurability in `σ((h − h_{4r}(w))|_{A'})`
    have hY' : Measurable[fieldSigma g A'] fun ω => restrictTo A' (g ω) :=
      fun s hs => ⟨s, hs, rfl⟩
    have hY : Measurable[fieldSigma g A'] fun ω => restrictTo A (g ω) :=
      Measurable.mono (show Measurable[fieldSigma g A] fun ω => restrictTo A (g ω) from
        fun s hs => ⟨s, hs, rfl⟩) (GM.fieldSigma_mono g hAA') le_rfl
    have hm1 : ∀ q₁ q₂ : ℚ, Measurable[fieldSigma g A'] fun ω =>
        G₁ (restrictTo A (g ω)) (circleMap w r q₁) (circleMap w r q₂) :=
      fun q₁ q₂ => (hG₁.eval.eval).comp hY
    have hm2 : Measurable[fieldSigma g A'] fun ω => ENNReal.ofReal C * ⨅ (q₃ : ℚ) (q₄ : ℚ),
        G₂ (restrictTo A' (g ω)) (circleMap w (r / 2) q₃) (circleMap w r q₄) :=
      (Measurable.iInf fun q₃ => Measurable.iInf fun q₄ =>
        (hG₂.eval.eval).comp hY').const_mul _
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun q₁ => MeasurableSet.iInter fun q₂ =>
      measurableSet_le (hm1 q₁ q₂) hm2
  · -- a.s. equality
    filter_upwards [hG₁ae, hG₂ae, hD.length P h (isGFFPlusCont_of_wp hh),
      ae_isLength_addFun hD hhb hf] with ω h1 h2 hL hL'
    have he0 : ENNReal.ofReal (Real.exp (xiGamma γ * c ω)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    exact propext (confLMGood_iff_rat hϕ hL hL' hr hV he0 ENNReal.ofReal_ne_top h1 h2)

/-- **The event family of `E^{LM}` for the covering lemma**: `E^{LM}_r(w)` where `act w r` holds,
the sure event elsewhere. -/
def confLMEvent (D : DistC → ContMetric) (ϕ : ℂ → ℂ) (C : ℝ) (act : ℂ → ℝ → Prop) {Ω : Type}
    (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)) (w : ℂ) (r : ℝ) : Set Ω :=
  {ω | act w r → ConfLMGood D ϕ (h ω) (hbar ω) (f ω) C w r}

lemma confLMEvent_of_act {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {C : ℝ} {act : ℂ → ℝ → Prop}
    {Ω : Type} {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} {w : ℂ} {r : ℝ} (ha : act w r) :
    confLMEvent D ϕ C act h hbar f w r = {ω | ConfLMGood D ϕ (h ω) (hbar ω) (f ω) C w r} := by
  ext ω
  simp only [confLMEvent, mem_ofPred_eq, ha, true_imp_iff]

lemma confLMEvent_of_not_act {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {C : ℝ} {act : ℂ → ℝ → Prop}
    {Ω : Type} {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} {w : ℂ} {r : ℝ} (ha : ¬ act w r) :
    confLMEvent D ϕ C act h hbar f w r = univ := by
  ext ω
  simp only [confLMEvent, mem_ofPred_eq, ha, false_imp_iff, mem_univ]

/-- **Annulus locality of the `E^{LM}` family** (CC0 D13): with `c₀ = 4`, `s₁ = 1/16`,
`s₂ = 1/2`, as `CoverLemma` requires, provided `act w r → B̄_{2r}(w) ⊆ V`. -/
theorem isAnnulusLocal_confLMEvent {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    {ϕ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V) (C : ℝ) {act : ℂ → ℝ → Prop}
    (hact : ∀ w r, act w r → closedBall w (2 * r) ⊆ V)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} (hh : IsWholePlaneGFF h P)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f)
    (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) :
    IsAnnulusLocal P h (confLMEvent D ϕ C act h hbar f) 4 (1 / 16) (1 / 2) := by
  intro w r hr
  by_cases ha : act w r
  · rw [confLMEvent_of_act ha]
    exact aeEventIn_confLMGood hD hϕ C hh hhb hf hc hr (hact w r ha)
  · rw [confLMEvent_of_not_act ha]
    exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩

end SmallGammaGeodesics.CC
