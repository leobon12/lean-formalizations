import SmallGammaGeodesics.CC.Prop21Det
import SmallGammaGeodesics.CC.LocalityConf
import LQGMetric.Field.CircleAvgLaw

/-!
# [3] Prop 2.1: transfer of the localized event between couplings (packet CC6b; CC0 D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10**: "by D3/D4 and
scale invariance, `P[F_r(z)]` equals the probability of the same `σ₀`-measurable functional for a
fresh GFF". We make this exact for the **localized** event `LocBad` (`CC/Prop21Det.lean`) of two
couplings of the same conformal neighbourhood `(ϕ, W, V)` on possibly different probability spaces,
whose domain fields are **normalized** whole-plane GFFs (`IsNormalizedWPGFF`, `h_1(0) = 0`):

`prob_locBad_le`: `P₁[LocBad₁] ≤ P₂[LocBad₂]`, where `LocBad_i` is the localized event for the
global metric `D_{x_i}`, the internal metric `D_{x_i}(·,·;A_d)` (`A_d` open) and the transported
metric `D^ϕ_i = confMetric D ϕ V h̄_i f_i`.

Proof.
1. One locality functional `G` for both transported metrics (`exists_confMetric_eq_restrict_two`,
   universal locality of CC2 with index `Bool`): a.s. `D^ϕ_i = G(x_i|_V)` on `V × V`.
2. The internal metric of a length metric equals the measurable chain formula `chainInf`
   (`ContMetric.internal_eq_chainInf`, `ContMetric.measurable_chainInf`), and `x ↦ D_x(u, v)` is
   measurable (Axiom: `D` is measurable).
3. With countable dense witness sets `Q₁ ⊆ B_1`, `Q₂ ⊆ T`, the set
   `S = {x | LocBadQ δ Q₁ Q₂ (D_x) (chainInf_x) (G(x|_V))}` is measurable; a.s.
   `LocBad₁ ⊆ {x₁ ∈ S}` (continuity of the three metrics, `locBadQ_of_locBad`) and
   `{x₂ ∈ S} ⊆ LocBad₂` (`locBad_of_locBadQ`).
4. `x₁` and `x₂` have the same law (`CircleAvg.map_eq_of_isNormalizedWPGFF`).

No measurability of the events themselves is needed (outer measures, `measure_mono_ae`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

variable {γ : ℝ} {D : DistC → ContMetric}

/-- **One locality functional for two couplings** of the same conformal neighbourhood on possibly
different probability spaces (universal locality, `exists_universal_confMetric_eq_restrict`, with
index `Bool`). -/
theorem exists_confMetric_eq_restrict_two {ϕ : ℂ → ℂ} {W V : Set ℂ}
    (hD : IsStrongLQGMetric γ D) (hϕ : IsConfNbhd ϕ W V)
    (A : TopologicalSpace.Opens ℂ) (hAV : (A : Set ℂ) ⊆ V)
    {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {x₁ hb₁ : Ω₁ → DistC} {f₁ : Ω₁ → C(ℂ, ℝ)}
    (hhb₁ : IsWholePlaneGFF hb₁ P₁) (hf₁ : Measurable f₁)
    (hc₁ : ∀ᵐ ω ∂P₁, IsConfCoupling γ ϕ W V (x₁ ω) (hb₁ ω) (f₁ ω))
    {Ω₂ : Type} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {x₂ hb₂ : Ω₂ → DistC} {f₂ : Ω₂ → C(ℂ, ℝ)}
    (hhb₂ : IsWholePlaneGFF hb₂ P₂) (hf₂ : Measurable f₂)
    (hc₂ : ∀ᵐ ω ∂P₂, IsConfCoupling γ ϕ W V (x₂ ω) (hb₂ ω) (f₂ ω)) :
    ∃ G : DistOn A → ℂ → ℂ → ℝ≥0∞, Measurable G ∧
      (∀ᵐ ω ∂P₁, ∀ z ∈ A, ∀ w ∈ A,
        confMetric D ϕ A (hb₁ ω) (f₁ ω) z w = G (restrictTo A (x₁ ω)) z w) ∧
      (∀ᵐ ω ∂P₂, ∀ z ∈ A, ∀ w ∈ A,
        confMetric D ϕ A (hb₂ ω) (f₂ ω) z w = G (restrictTo A (x₂ ω)) z w) := by
  let Ωi : Bool → Type := fun b => Bool.rec Ω₂ Ω₁ b
  let mi : ∀ b, MeasurableSpace (Ωi b) := fun b =>
    Bool.rec (motive := fun b => MeasurableSpace (Ωi b)) ‹MeasurableSpace Ω₂›
      ‹MeasurableSpace Ω₁› b
  let Pi : ∀ b, @Measure (Ωi b) (mi b) := fun b =>
    Bool.rec (motive := fun b => @Measure (Ωi b) (mi b)) P₂ P₁ b
  have hPi : ∀ b, @IsProbabilityMeasure (Ωi b) (mi b) (Pi b) := fun b => by
    cases b
    · exact ‹IsProbabilityMeasure P₂›
    · exact ‹IsProbabilityMeasure P₁›
  let xi : ∀ b, Ωi b → DistC := fun b => Bool.rec (motive := fun b => Ωi b → DistC) x₂ x₁ b
  let hbi : ∀ b, Ωi b → DistC := fun b => Bool.rec (motive := fun b => Ωi b → DistC) hb₂ hb₁ b
  let fi : ∀ b, Ωi b → C(ℂ, ℝ) :=
    fun b => Bool.rec (motive := fun b => Ωi b → C(ℂ, ℝ)) f₂ f₁ b
  obtain ⟨G, hGm, hG⟩ := @exists_universal_confMetric_eq_restrict γ D ϕ W V hD hϕ A hAV Bool _ Ωi
    mi Pi hPi xi hbi fi (fun b => by cases b; exacts [hhb₂, hhb₁])
    (fun b => by cases b; exacts [hf₂, hf₁]) (fun b => by cases b; exacts [hc₂, hc₁])
  exact ⟨G, hGm, hG true, hG false⟩

/-- **Transfer of the localized event** (D10): for two couplings of the same conformal
neighbourhood `(ϕ, W, V)` whose domain fields are normalized whole-plane GFFs, the probability of
the localized bad event of the first is at most that of the second (and by symmetry they are
equal). Here `B_1 ⊆ V`, `T ⊆ V` and `A_d ⊇ B_1` is open. -/
theorem prob_locBad_le (hD : IsStrongLQGMetric γ D) {ϕ : ℂ → ℂ} {W V : Set ℂ}
    (hϕ : IsConfNbhd ϕ W V) (hB1 : ball (0 : ℂ) 1 ⊆ V) {T : Set ℂ} (hT : T ⊆ V)
    {Ad : Set ℂ} (hAd : IsOpen Ad) (hB1Ad : ball (0 : ℂ) 1 ⊆ Ad) (δ : ℝ)
    {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {x₁ hb₁ : Ω₁ → DistC} {f₁ : Ω₁ → C(ℂ, ℝ)} (hx₁ : IsNormalizedWPGFF x₁ P₁)
    (hhb₁ : IsWholePlaneGFF hb₁ P₁) (hf₁ : Measurable f₁)
    (hc₁ : ∀ᵐ ω ∂P₁, IsConfCoupling γ ϕ W V (x₁ ω) (hb₁ ω) (f₁ ω))
    {Ω₂ : Type} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {x₂ hb₂ : Ω₂ → DistC} {f₂ : Ω₂ → C(ℂ, ℝ)} (hx₂ : IsNormalizedWPGFF x₂ P₂)
    (hhb₂ : IsWholePlaneGFF hb₂ P₂) (hf₂ : Measurable f₂)
    (hc₂ : ∀ᵐ ω ∂P₂, IsConfCoupling γ ϕ W V (x₂ ω) (hb₂ ω) (f₂ ω)) :
    P₁ {ω | LocBad δ T (fun u v => ENNReal.ofReal ((D (x₁ ω)).1 (u, v)))
        ((D (x₁ ω)).internal Ad) (confMetric D ϕ V (hb₁ ω) (f₁ ω))} ≤
      P₂ {ω | LocBad δ T (fun u v => ENNReal.ofReal ((D (x₂ ω)).1 (u, v)))
        ((D (x₂ ω)).internal Ad) (confMetric D ϕ V (hb₂ ω) (f₂ ω))} := by
  obtain ⟨Q₁, hQ₁, hQ₁c, hQ₁d⟩ := exists_countable_dense_subset_complex (ball (0 : ℂ) 1)
  obtain ⟨Q₂, hQ₂, hQ₂c, hQ₂d⟩ := exists_countable_dense_subset_complex T
  set A : TopologicalSpace.Opens ℂ := ⟨V, hϕ.isOpen_V⟩ with hA
  have hAV : (A : Set ℂ) = V := rfl
  obtain ⟨G, hGm, hG₁, hG₂⟩ :=
    exists_confMetric_eq_restrict_two hD hϕ A hAV.le hhb₁ hf₁ hc₁ hhb₂ hf₂ hc₂
  -- the three functionals of the field
  set dgF : DistC → ℂ → ℂ → ℝ≥0∞ := fun x u v => ENNReal.ofReal ((D x).1 (u, v)) with hdgFdef
  set dlF : DistC → ℂ → ℂ → ℝ≥0∞ := fun x u v => (D x).chainInf Ad u v with hdlFdef
  set nF : DistC → ℂ → ℂ → ℝ≥0∞ := fun x u v => G (restrictTo A x) u v with hnFdef
  have hdgF : ∀ u v, Measurable fun x => dgF x u v := fun u v =>
    ENNReal.measurable_ofReal.comp ((ContinuousMap.measurable_eval (u, v)).comp
      (measurable_subtype_coe.comp hD.measurable))
  have hdlF : ∀ u v, Measurable fun x => dlF x u v := fun u v =>
    (ContMetric.measurable_chainInf Ad).comp (hD.measurable.prodMk
      (measurable_const : Measurable fun _ : DistC => ((u, v) : ℂ × ℂ)))
  have hnF : ∀ u v, Measurable fun x => nF x u v := fun u v =>
    (measurable_pi_apply v).comp ((measurable_pi_apply u).comp
      (hGm.comp (measurable_restrictTo A)))
  set S : Set DistC := {x | LocBadQ δ Q₁ Q₂ (dgF x) (dlF x) (nF x)} with hSdef
  have hS : MeasurableSet S := by
    have e : S = ⋃ u ∈ Q₁, ⋃ v ∈ Q₁, ({x | dgF x u v < dlF x u v} ∪
        (⋃ w ∈ Q₂, {x | nF x u w < nF x u v}) ∪
        {x | dlF x u v + ENNReal.ofReal δ < nF x u v} ∪
        {x | nF x u v + ENNReal.ofReal δ < dlF x u v}) := by
      ext x
      simp only [hSdef, LocBadQ, mem_ofPred_eq, mem_iUnion, mem_union, exists_prop, or_assoc]
    rw [e]
    refine MeasurableSet.biUnion hQ₁c fun u _ => MeasurableSet.biUnion hQ₁c fun v _ => ?_
    refine (((measurableSet_lt (hdgF u v) (hdlF u v)).union
      (MeasurableSet.biUnion hQ₂c fun w _ => measurableSet_lt (hnF u w) (hnF u v))).union
      (measurableSet_lt ((hdlF u v).add_const _) (hnF u v))).union
      (measurableSet_lt ((hnF u v).add_const _) (hdlF u v))
  have hQ₁V : Q₁ ⊆ V := hQ₁.trans hB1
  have hQV : ∀ v ∈ Q₁ ∪ Q₂, v ∈ V := fun v hv => hv.elim (fun h => hQ₁V h) fun h => hT (hQ₂ h)
  -- side 1: the localized event lies a.s. in `{x₁ ∈ S}`
  have h1 : {ω | LocBad δ T (fun u v => ENNReal.ofReal ((D (x₁ ω)).1 (u, v)))
      ((D (x₁ ω)).internal Ad) (confMetric D ϕ V (hb₁ ω) (f₁ ω))} ≤ᵐ[P₁] x₁ ⁻¹' S := by
    filter_upwards [hG₁, hD.length P₁ x₁ (isGFFPlusCont_of_wp hx₁.1),
      ae_isLength_addFun hD hhb₁ hf₁] with ω hGω hlen hlen' hbad
    have hdg : ContinuousOn (fun p : ℂ × ℂ => ENNReal.ofReal ((D (x₁ ω)).1 (p.1, p.2)))
        (ball 0 1 ×ˢ ball 0 1) :=
      (ENNReal.continuous_ofReal.comp (D (x₁ ω)).1.continuous).continuousOn
    have hdl : ContinuousOn (fun p : ℂ × ℂ => (D (x₁ ω)).internal Ad p.1 p.2)
        (ball 0 1 ×ˢ ball 0 1) :=
      ((D (x₁ ω)).continuousOn_internal hlen hAd).mono (prod_mono hB1Ad hB1Ad)
    have hn : ContinuousOn (fun p : ℂ × ℂ => confMetric D ϕ V (hb₁ ω) (f₁ ω) p.1 p.2) (V ×ˢ V) :=
      continuousOn_confMetric hϕ hlen'
    have hQ := locBadQ_of_locBad hQ₁ hQ₁d hQ₂ hQ₂d hB1 hT hdg hdl hn hbad
    show LocBadQ δ Q₁ Q₂ (dgF (x₁ ω)) (dlF (x₁ ω)) (nF (x₁ ω))
    refine hQ.congr (fun _ _ _ _ => rfl) (fun u _ v _ => ?_) (fun u hu v hv => ?_)
    · exact (D (x₁ ω)).internal_eq_chainInf hlen hAd u v
    · exact hGω u (hQ₁V hu) v (hQV v hv)
  -- side 2: `{x₂ ∈ S}` lies a.s. in the localized event
  have h2 : x₂ ⁻¹' S ≤ᵐ[P₂] {ω | LocBad δ T (fun u v => ENNReal.ofReal ((D (x₂ ω)).1 (u, v)))
      ((D (x₂ ω)).internal Ad) (confMetric D ϕ V (hb₂ ω) (f₂ ω))} := by
    filter_upwards [hG₂, hD.length P₂ x₂ (isGFFPlusCont_of_wp hx₂.1)] with ω hGω hlen hSω
    refine locBad_of_locBadQ hQ₁ hQ₂ ((show LocBadQ δ Q₁ Q₂ (dgF (x₂ ω)) (dlF (x₂ ω))
      (nF (x₂ ω)) from hSω).congr (fun _ _ _ _ => rfl) (fun u _ v _ => ?_) (fun u hu v hv => ?_))
    · exact ((D (x₂ ω)).internal_eq_chainInf hlen hAd u v).symm
    · exact (hGω u (hQ₁V hu) v (hQV v hv)).symm
  have hlaw : P₁.map x₁ = P₂.map x₂ := CircleAvg.map_eq_of_isNormalizedWPGFF hx₁ hx₂
  calc P₁ {ω | LocBad δ T (fun u v => ENNReal.ofReal ((D (x₁ ω)).1 (u, v)))
          ((D (x₁ ω)).internal Ad) (confMetric D ϕ V (hb₁ ω) (f₁ ω))}
      ≤ P₁ (x₁ ⁻¹' S) := measure_mono_ae h1
    _ = P₁.map x₁ S := (Measure.map_apply hx₁.1.measurable hS).symm
    _ = P₂.map x₂ S := by rw [hlaw]
    _ = P₂ (x₂ ⁻¹' S) := Measure.map_apply hx₂.1.measurable hS
    _ ≤ _ := measure_mono_ae h2

end SmallGammaGeodesics.CC
